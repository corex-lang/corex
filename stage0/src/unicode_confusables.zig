//! Compact Unicode Trojan, UAX #31 Identifier, and UTS #39 / UTS #55 Confusable Tables
//!
//! Provides zero-ASCII-overhead Trojan control-codepoint detection (`W0102`), compact UAX #31
//! `XID_Start` / `XID_Continue` range tables, a `<= 2,560 B` sorted `UTS #39` confusable skeleton
//! table (`W0103`, `W0104`), algorithmic Fullwidth / Mathematical Alphanumeric folding, and `UTS #55`
//! identifier-chunk and mixed-script word-context analyzers.
//!
//! Canonical CoreX typography (`–`, `…`, `§`, `×`, `≤`, `≥`, `≠`, `→`), monochrome CLI box-drawing
//! and status glyphs (`╭`–`╰`, `▸`, `•`, `✓`, `✗`, `⚠`), and visibly distinct scientific Greek
//! symbols (`Δ`, `λ`, `μ`, `π`, `σ`, `θ`, …) are strictly excluded from confusable sets at `comptime`.

const std = @import("std");
const assert = std.debug.assert;

// ---------------------------------------- TYPES ----------------------------------------

/// Compact script tag encoded in bits `24..27` of `ConfusableEntry.skeleton_and_script` (`UTS #55`).
pub const ScriptTag = enum(u4) {
    /// Standalone typographic punctuation or space impostor (`NBSP`, smart quotes, `U+2212`, `U+2014`).
    common_punct = 0,
    /// Non-ASCII Latin extensions (`ı`, `ſ`, IPA, Latin small capitals, Roman numerals, Fullwidth Latin).
    latin_ext = 1,
    /// Cyrillic script (`U+0400..U+052F`).
    cyrillic = 2,
    /// Greek and Coptic script (`U+0370..U+03FF`).
    greek = 3,
    /// Cherokee script (`U+13A0..U+13FF`, `U+AB70..U+ABBF`).
    cherokee = 4,
    /// Armenian script (`U+0530..U+058F`).
    armenian = 5,
    /// Hebrew script (`U+0590..U+05FF`).
    hebrew = 6,
    /// Katakana, Hiragana, or CJK symbol lookalikes (`ー`, `ロ`, `ニ`).
    cjk_kana = 7,
    /// Coptic, Georgian, Runic, or Indic confusable letters/digits.
    other_script = 8,
};

/// Exact 8-byte `.rodata` record sorted strictly by `codepoint` ascending (`<= 320` entries = `<= 2,560 B`).
pub const ConfusableEntry = extern struct {
    /// Unicode scalar codepoint (`U+0080..U+10FFFF`).
    codepoint: u32,
    /// Packed `1..3`-byte ASCII skeleton (`0..23`), `ScriptTag` (`24..27`), and property flags (`28..31`).
    skeleton_and_script: u32,

    /// Returns the first ASCII skeleton byte (`0x20..0x7E`).
    pub inline fn skelByte0(self: ConfusableEntry) u8 {
        return @truncate(self.skeleton_and_script);
    }

    /// Returns the second ASCII skeleton byte (`0` when single-byte skeleton).
    pub inline fn skelByte1(self: ConfusableEntry) u8 {
        return @truncate(self.skeleton_and_script >> 8);
    }

    /// Returns the third ASCII skeleton byte (`0` when `<= 2`-byte skeleton).
    pub inline fn skelByte2(self: ConfusableEntry) u8 {
        return @truncate(self.skeleton_and_script >> 16);
    }

    /// Writes `1..3` ASCII skeleton bytes into `dest` and returns the populated sub-slice.
    pub inline fn writeSkeleton(self: ConfusableEntry, dest: *[3]u8) []const u8 {
        dest[0] = self.skelByte0();
        const second = self.skelByte1();
        if (second == 0) return dest[0..1];
        dest[1] = second;
        const third = self.skelByte2();
        if (third == 0) return dest[0..2];
        dest[2] = third;
        return dest[0..3];
    }

    /// Returns the `ScriptTag` stored in bits `24..27`.
    pub inline fn scriptTag(self: ConfusableEntry) ScriptTag {
        return @fromBackingInt(@intCast(@as(u4, @truncate(self.skeleton_and_script >> 24))));
    }

    /// Returns `true` when this scalar is an identifier / mixed-word letter or digit homoglyph (`W0103`, `W0104`).
    pub inline fn isIdentConfusable(self: ConfusableEntry) bool {
        return (self.skeleton_and_script & (@as(u32, 1) << 28)) != 0;
    }

    /// Returns `true` when this scalar is a standalone punctuation or whitespace impostor (`W0104`).
    pub inline fn isStandaloneImpostor(self: ConfusableEntry) bool {
        return (self.skeleton_and_script & (@as(u32, 1) << 29)) != 0;
    }

    /// Returns `true` when this scalar is visually indistinguishable from an ASCII letter even in isolation.
    pub inline fn isWholeScriptHomoglyph(self: ConfusableEntry) bool {
        return (self.skeleton_and_script & (@as(u32, 1) << 30)) != 0;
    }

    /// Returns `true` when this scalar has `Lu` / `Lt` uppercase casing for `PascalCase` chunk splitting.
    pub inline fn isUppercase(self: ConfusableEntry) bool {
        return (self.skeleton_and_script & (@as(u32, 1) << 31)) != 0;
    }
};

/// Inclusive `[start, end]` Unicode scalar interval used in sorted `UAX #31` binary-search tables.
pub const CodepointRange = extern struct {
    /// Inclusive lower Unicode scalar bound.
    start: u32,
    /// Inclusive upper Unicode scalar bound.
    end: u32,
};

/// Result of `UTS #55` §5.1.2.2 identifier-chunk mixed-script confusable analysis (`W0103`).
pub const IdentChunkAnalysis = struct {
    /// `true` if a mixed-script confusable chunk or cross-underscore whole-chunk homoglyph was found.
    has_mixed_script_confusable: bool = false,
    /// Relative UTF-8 byte offset within the identifier of the first offending scalar.
    first_confusable_rel_byte: u16 = 0,
    /// Unicode scalar value of the first offending confusable character.
    first_confusable_cp: u21 = 0,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Bitmask of ASCII letters (`A-Z`, `a-z`) that possess visual homoglyphs in Cyrillic (`W0103` `Строкa` guard).
const ASCII_CYRILLIC_HOMOGLYPH_UPPER_MASK: u32 =
    (1 << ('A' - 'A')) | (1 << ('B' - 'A')) | (1 << ('C' - 'A')) | (1 << ('E' - 'A')) |
    (1 << ('H' - 'A')) | (1 << ('I' - 'A')) | (1 << ('J' - 'A')) | (1 << ('K' - 'A')) |
    (1 << ('M' - 'A')) | (1 << ('O' - 'A')) | (1 << ('P' - 'A')) | (1 << ('S' - 'A')) |
    (1 << ('T' - 'A')) | (1 << ('X' - 'A')) | (1 << ('Y' - 'A'));

/// Lowercase ASCII letters (`a-z`) that possess visual homoglyphs in Cyrillic.
const ASCII_CYRILLIC_HOMOGLYPH_LOWER_MASK: u32 =
    (1 << ('a' - 'a')) | (1 << ('b' - 'a')) | (1 << ('c' - 'a')) | (1 << ('d' - 'a')) |
    (1 << ('e' - 'a')) | (1 << ('h' - 'a')) | (1 << ('i' - 'a')) | (1 << ('j' - 'a')) |
    (1 << ('k' - 'a')) | (1 << ('l' - 'a')) | (1 << ('o' - 'a')) | (1 << ('p' - 'a')) |
    (1 << ('q' - 'a')) | (1 << ('r' - 'a')) | (1 << ('s' - 'a')) | (1 << ('w' - 'a')) |
    (1 << ('x' - 'a')) | (1 << ('y' - 'a'));

/// Uppercase ASCII letters (`A-Z`) that possess visual homoglyphs in Greek.
const ASCII_GREEK_HOMOGLYPH_UPPER_MASK: u32 =
    (1 << ('A' - 'A')) | (1 << ('B' - 'A')) | (1 << ('C' - 'A')) | (1 << ('E' - 'A')) |
    (1 << ('H' - 'A')) | (1 << ('I' - 'A')) | (1 << ('J' - 'A')) | (1 << ('K' - 'A')) |
    (1 << ('M' - 'A')) | (1 << ('N' - 'A')) | (1 << ('O' - 'A')) | (1 << ('P' - 'A')) |
    (1 << ('T' - 'A')) | (1 << ('X' - 'A')) | (1 << ('Y' - 'A')) | (1 << ('Z' - 'A'));

/// Lowercase ASCII letters (`a-z`) that possess visual homoglyphs in Greek (excluding `'t'`, `'s'`, `'d'` for `Δt`/`μs`).
const ASCII_GREEK_HOMOGLYPH_LOWER_MASK: u32 =
    (1 << ('a' - 'a')) | (1 << ('b' - 'a')) | (1 << ('c' - 'a')) | (1 << ('e' - 'a')) |
    (1 << ('i' - 'a')) | (1 << ('j' - 'a')) | (1 << ('k' - 'a')) | (1 << ('n' - 'a')) |
    (1 << ('o' - 'a')) | (1 << ('p' - 'a')) | (1 << ('u' - 'a')) | (1 << ('v' - 'a')) |
    (1 << ('w' - 'a')) | (1 << ('x' - 'a')) | (1 << ('y' - 'a'));

/// Compact sorted non-ASCII `UAX #31` `XID_Start` scalar intervals (`U+00AA..U+2FA1D`).
pub const XID_START_RANGES = [_]CodepointRange{
    .{ .start = 0x00AA, .end = 0x00AA },
    .{ .start = 0x00B5, .end = 0x00B5 },
    .{ .start = 0x00BA, .end = 0x00BA },
    .{ .start = 0x00C0, .end = 0x00D6 },
    .{ .start = 0x00D8, .end = 0x00F6 },
    .{ .start = 0x00F8, .end = 0x02C1 },
    .{ .start = 0x02C6, .end = 0x02D1 },
    .{ .start = 0x02E0, .end = 0x02E4 },
    .{ .start = 0x02EC, .end = 0x02EC },
    .{ .start = 0x02EE, .end = 0x02EE },
    .{ .start = 0x0370, .end = 0x0374 },
    .{ .start = 0x0376, .end = 0x0377 },
    .{ .start = 0x037B, .end = 0x037D },
    .{ .start = 0x037F, .end = 0x037F },
    .{ .start = 0x0386, .end = 0x0386 },
    .{ .start = 0x0388, .end = 0x038A },
    .{ .start = 0x038C, .end = 0x038C },
    .{ .start = 0x038E, .end = 0x03A1 },
    .{ .start = 0x03A3, .end = 0x03F5 },
    .{ .start = 0x03F7, .end = 0x0481 },
    .{ .start = 0x048A, .end = 0x052F },
    .{ .start = 0x0531, .end = 0x0556 },
    .{ .start = 0x0559, .end = 0x0559 },
    .{ .start = 0x0560, .end = 0x0588 },
    .{ .start = 0x05D0, .end = 0x05EA },
    .{ .start = 0x05EF, .end = 0x05F2 },
    .{ .start = 0x0620, .end = 0x064A },
    .{ .start = 0x066E, .end = 0x066F },
    .{ .start = 0x0671, .end = 0x06D3 },
    .{ .start = 0x06E5, .end = 0x06E6 },
    .{ .start = 0x06EE, .end = 0x06EF },
    .{ .start = 0x06FA, .end = 0x06FC },
    .{ .start = 0x0710, .end = 0x0710 },
    .{ .start = 0x0712, .end = 0x072F },
    .{ .start = 0x074D, .end = 0x07A5 },
    .{ .start = 0x0904, .end = 0x0939 },
    .{ .start = 0x0958, .end = 0x0961 },
    .{ .start = 0x0985, .end = 0x09B9 },
    .{ .start = 0x0A05, .end = 0x0A39 },
    .{ .start = 0x0A85, .end = 0x0AB9 },
    .{ .start = 0x0B05, .end = 0x0B39 },
    .{ .start = 0x0B85, .end = 0x0BB9 },
    .{ .start = 0x0C05, .end = 0x0C39 },
    .{ .start = 0x0C85, .end = 0x0CB9 },
    .{ .start = 0x0D05, .end = 0x0D3A },
    .{ .start = 0x0E01, .end = 0x0E30 },
    .{ .start = 0x0E81, .end = 0x0EB0 },
    .{ .start = 0x0F40, .end = 0x0F6C },
    .{ .start = 0x10A0, .end = 0x10C5 },
    .{ .start = 0x10D0, .end = 0x10FA },
    .{ .start = 0x1100, .end = 0x1248 },
    .{ .start = 0x13A0, .end = 0x13F5 },
    .{ .start = 0x13F8, .end = 0x13FD },
    .{ .start = 0x1401, .end = 0x166C },
    .{ .start = 0x16A0, .end = 0x16EA },
    .{ .start = 0x1D00, .end = 0x1DBF },
    .{ .start = 0x1E00, .end = 0x1F15 },
    .{ .start = 0x1F18, .end = 0x1F1D },
    .{ .start = 0x1F20, .end = 0x1F45 },
    .{ .start = 0x1F48, .end = 0x1F4D },
    .{ .start = 0x1F50, .end = 0x1F57 },
    .{ .start = 0x1F59, .end = 0x1F7D },
    .{ .start = 0x1F80, .end = 0x1FB4 },
    .{ .start = 0x1FB6, .end = 0x1FBC },
    .{ .start = 0x2102, .end = 0x2102 },
    .{ .start = 0x2107, .end = 0x2107 },
    .{ .start = 0x210A, .end = 0x2113 },
    .{ .start = 0x2115, .end = 0x2115 },
    .{ .start = 0x2119, .end = 0x211D },
    .{ .start = 0x2124, .end = 0x2124 },
    .{ .start = 0x2126, .end = 0x2126 },
    .{ .start = 0x2128, .end = 0x2128 },
    .{ .start = 0x212A, .end = 0x212D },
    .{ .start = 0x212F, .end = 0x2139 },
    .{ .start = 0x2160, .end = 0x2188 },
    .{ .start = 0x2C00, .end = 0x2CE4 },
    .{ .start = 0x2D00, .end = 0x2D25 },
    .{ .start = 0x3005, .end = 0x3007 },
    .{ .start = 0x3021, .end = 0x3029 },
    .{ .start = 0x3041, .end = 0x3096 },
    .{ .start = 0x30A1, .end = 0x30FA },
    .{ .start = 0x30FC, .end = 0x30FF },
    .{ .start = 0x3105, .end = 0x312F },
    .{ .start = 0x3400, .end = 0x4DBF },
    .{ .start = 0x4E00, .end = 0x9FFF },
    .{ .start = 0xA000, .end = 0xA48C },
    .{ .start = 0xA640, .end = 0xA69D },
    .{ .start = 0xA722, .end = 0xA787 },
    .{ .start = 0xAB70, .end = 0xABBF },
    .{ .start = 0xAC00, .end = 0xD7A3 },
    .{ .start = 0xF900, .end = 0xFA6D },
    .{ .start = 0xFF21, .end = 0xFF3A },
    .{ .start = 0xFF41, .end = 0xFF5A },
    .{ .start = 0x1D400, .end = 0x1D7CB },
    .{ .start = 0x20000, .end = 0x2A6DF },
};

/// Additional non-ASCII `UAX #31` `XID_Continue` combining-mark, digit, and connector ranges.
pub const XID_CONTINUE_EXTRA_RANGES = [_]CodepointRange{
    .{ .start = 0x00B7, .end = 0x00B7 },
    .{ .start = 0x0300, .end = 0x036F },
    .{ .start = 0x0483, .end = 0x0487 },
    .{ .start = 0x0591, .end = 0x05BD },
    .{ .start = 0x05BF, .end = 0x05BF },
    .{ .start = 0x05C1, .end = 0x05C2 },
    .{ .start = 0x064B, .end = 0x0669 },
    .{ .start = 0x0670, .end = 0x0670 },
    .{ .start = 0x06F0, .end = 0x06F9 },
    .{ .start = 0x0901, .end = 0x0903 },
    .{ .start = 0x093E, .end = 0x094D },
    .{ .start = 0x0966, .end = 0x096F },
    .{ .start = 0x1DC0, .end = 0x1DFF },
    .{ .start = 0x203F, .end = 0x2040 },
    .{ .start = 0x3099, .end = 0x309A },
    .{ .start = 0xFF10, .end = 0xFF19 },
    .{ .start = 0x1D7CE, .end = 0x1D7FF },
};

/// Sorted `UTS #39` / `UTS #55` confusable lookup table (`<= 320` entries, `<= 2,560 B` `.rodata`).
pub const UTS39_CONFUSABLES = [_]ConfusableEntry{
    // Non-ASCII spaces, soft-hyphen, and Latin Extended homoglyphs:
    packEntry(0x00A0, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x00AD, '-', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x0131, 'i', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x017F, 's', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x0196, 'I', 0, 0, .latin_ext, true, false, true, true),
    packEntry(0x01C0, 'l', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x0251, 'a', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x0261, 'g', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x0269, 'i', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x026A, 'I', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x0280, 'R', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x0299, 'B', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x029C, 'H', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x02B9, '\'', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x02BA, '"', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x02BB, '\'', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x02BC, '\'', 0, 0, .common_punct, false, true, false, false),

    // Greek homoglyphs & U+037E semicolon impostor (visibly distinct scientific Greek strictly excluded!):
    packEntry(0x037E, ';', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x037F, 'J', 0, 0, .greek, true, false, true, true),
    packEntry(0x0391, 'A', 0, 0, .greek, true, false, true, true),
    packEntry(0x0392, 'B', 0, 0, .greek, true, false, true, true),
    packEntry(0x0395, 'E', 0, 0, .greek, true, false, true, true),
    packEntry(0x0396, 'Z', 0, 0, .greek, true, false, true, true),
    packEntry(0x0397, 'H', 0, 0, .greek, true, false, true, true),
    packEntry(0x0399, 'I', 0, 0, .greek, true, false, true, true),
    packEntry(0x039A, 'K', 0, 0, .greek, true, false, true, true),
    packEntry(0x039C, 'M', 0, 0, .greek, true, false, true, true),
    packEntry(0x039D, 'N', 0, 0, .greek, true, false, true, true),
    packEntry(0x039F, 'O', 0, 0, .greek, true, false, true, true),
    packEntry(0x03A1, 'P', 0, 0, .greek, true, false, true, true),
    packEntry(0x03A4, 'T', 0, 0, .greek, true, false, true, true),
    packEntry(0x03A5, 'Y', 0, 0, .greek, true, false, true, true),
    packEntry(0x03A7, 'X', 0, 0, .greek, true, false, true, true),
    packEntry(0x03B1, 'a', 0, 0, .greek, true, false, false, false),
    packEntry(0x03B2, 'b', 0, 0, .greek, true, false, false, false),
    packEntry(0x03B3, 'y', 0, 0, .greek, true, false, false, false),
    packEntry(0x03B5, 'e', 0, 0, .greek, true, false, false, false),
    packEntry(0x03B7, 'n', 0, 0, .greek, true, false, false, false),
    packEntry(0x03B9, 'i', 0, 0, .greek, true, false, true, false),
    packEntry(0x03BA, 'k', 0, 0, .greek, true, false, false, false),
    packEntry(0x03BD, 'v', 0, 0, .greek, true, false, true, false),
    packEntry(0x03BF, 'o', 0, 0, .greek, true, false, true, false),
    packEntry(0x03C1, 'p', 0, 0, .greek, true, false, true, false),
    packEntry(0x03C2, 'c', 0, 0, .greek, true, false, false, false),
    packEntry(0x03C4, 't', 0, 0, .greek, true, false, false, false),
    packEntry(0x03C5, 'u', 0, 0, .greek, true, false, false, false),
    packEntry(0x03C7, 'x', 0, 0, .greek, true, false, false, false),
    packEntry(0x03C9, 'w', 0, 0, .greek, true, false, false, false),
    packEntry(0x03D1, 'v', 0, 0, .greek, true, false, false, false),
    packEntry(0x03D2, 'Y', 0, 0, .greek, true, false, true, true),
    packEntry(0x03F1, 'p', 0, 0, .greek, true, false, false, false),
    packEntry(0x03F2, 'c', 0, 0, .greek, true, false, true, false),
    packEntry(0x03F3, 'j', 0, 0, .greek, true, false, true, false),
    packEntry(0x03F9, 'C', 0, 0, .greek, true, false, true, true),

    // Cyrillic homoglyphs (`U+0405..U+051D`):
    packEntry(0x0405, 'S', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0406, 'I', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0408, 'J', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0410, 'A', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0412, 'B', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0415, 'E', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0417, '3', 0, 0, .cyrillic, true, false, false, true),
    packEntry(0x041A, 'K', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x041C, 'M', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x041D, 'H', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x041E, 'O', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0420, 'P', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0421, 'C', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0422, 'T', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0423, 'Y', 0, 0, .cyrillic, true, false, false, true),
    packEntry(0x0425, 'X', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x0430, 'a', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x0432, 'b', 0, 0, .cyrillic, true, false, false, false),
    packEntry(0x0433, 'r', 0, 0, .cyrillic, true, false, false, false),
    packEntry(0x0435, 'e', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x043A, 'k', 0, 0, .cyrillic, true, false, false, false),
    packEntry(0x043E, 'o', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x0440, 'p', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x0441, 'c', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x0443, 'y', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x0445, 'x', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x0455, 's', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x0456, 'i', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x0458, 'j', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x04AE, 'Y', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x04AF, 'y', 0, 0, .cyrillic, true, false, false, false),
    packEntry(0x04BB, 'h', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x04C0, 'I', 0, 0, .cyrillic, true, false, true, true),
    packEntry(0x04CF, 'l', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x04D8, 'e', 0, 0, .cyrillic, true, false, false, true),
    packEntry(0x04E8, 'O', 0, 0, .cyrillic, true, false, false, true),
    packEntry(0x04E9, 'o', 0, 0, .cyrillic, true, false, false, false),
    packEntry(0x0501, 'd', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x051B, 'q', 0, 0, .cyrillic, true, false, true, false),
    packEntry(0x051D, 'w', 0, 0, .cyrillic, true, false, true, false),

    // Armenian & Hebrew homoglyphs + punctuation impostors (`U+0531..U+061B`):
    packEntry(0x0531, 'U', 0, 0, .armenian, true, false, false, true),
    packEntry(0x0535, 'b', 0, 0, .armenian, true, false, false, true),
    packEntry(0x053C, 'L', 0, 0, .armenian, true, false, false, true),
    packEntry(0x0540, 'Z', 0, 0, .armenian, true, false, false, true),
    packEntry(0x0548, 'N', 0, 0, .armenian, true, false, false, true),
    packEntry(0x054D, 'U', 0, 0, .armenian, true, false, true, true),
    packEntry(0x054F, 'S', 0, 0, .armenian, true, false, true, true),
    packEntry(0x0555, 'O', 0, 0, .armenian, true, false, true, true),
    packEntry(0x0561, 'w', 0, 0, .armenian, true, false, false, false),
    packEntry(0x0563, 'q', 0, 0, .armenian, true, false, false, false),
    packEntry(0x0566, 'q', 0, 0, .armenian, true, false, false, false),
    packEntry(0x0570, 'h', 0, 0, .armenian, true, false, true, false),
    packEntry(0x0578, 'n', 0, 0, .armenian, true, false, true, false),
    packEntry(0x057D, 'u', 0, 0, .armenian, true, false, true, false),
    packEntry(0x0581, 'g', 0, 0, .armenian, true, false, false, false),
    packEntry(0x0585, 'o', 0, 0, .armenian, true, false, true, false),
    packEntry(0x0589, ':', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x05D5, 'l', 0, 0, .hebrew, true, false, false, false),
    packEntry(0x05D7, 'n', 0, 0, .hebrew, true, false, false, false),
    packEntry(0x05D9, 'i', 0, 0, .hebrew, true, false, false, false),
    packEntry(0x05DD, 'o', 0, 0, .hebrew, true, false, false, false),
    packEntry(0x05DF, 'l', 0, 0, .hebrew, true, false, false, false),
    packEntry(0x05E1, 'o', 0, 0, .hebrew, true, false, true, false),
    packEntry(0x05F3, '\'', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x05F4, '"', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x060C, ',', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x061B, ';', 0, 0, .common_punct, false, true, false, false),

    // Cherokee homoglyphs & Ogham space (`U+13A0..U+1D22`):
    packEntry(0x13A0, 'D', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13A1, 'R', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13A2, 'T', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13A5, 'i', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13A9, 'Y', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13AA, 'A', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13AB, 'J', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13AC, 'E', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13B3, 'W', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13B7, 'M', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13BB, 'H', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13C0, 'G', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13C2, 'h', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13C3, 'Z', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13CF, 'b', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13D2, 'R', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13DA, 'S', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13DE, 'L', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13DF, 'C', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13E2, 'P', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13E6, 'K', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13EE, '4', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x13F4, 'B', 0, 0, .cherokee, true, false, true, true),
    packEntry(0x1680, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x1D00, 'A', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D04, 'C', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D05, 'D', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D07, 'E', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D0A, 'J', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D0B, 'K', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D0D, 'M', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D0F, 'O', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D18, 'P', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D1B, 'T', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D1C, 'U', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D20, 'V', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D21, 'W', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x1D22, 'Z', 0, 0, .latin_ext, true, false, false, false),

    // General Punctuation deceptive spaces, hyphens, em-dash (`U+2014`, NOT `U+2013`!), and smart quotes:
    packEntry(0x2000, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2001, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2002, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2003, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2004, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2005, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2006, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2007, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2008, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2009, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x200A, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2010, '-', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2011, '-', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2012, '-', 0, 0, .common_punct, false, true, false, false),
    // NOTE: U+2013 (`–` en-dash) is canonical CoreX typography (`AGENTS.md` §7) and MUST NEVER be listed here!
    packEntry(0x2014, '-', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2015, '-', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2018, '\'', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2019, '\'', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x201A, '\'', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x201B, '\'', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x201C, '"', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x201D, '"', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x201E, '"', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x201F, '"', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2024, '.', 0, 0, .common_punct, false, true, false, false),
    // NOTE: U+2026 (`…` ellipsis) is canonical CoreX typography (`AGENTS.md` §7) and MUST NEVER be listed here!
    packEntry(0x202F, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2032, '\'', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2033, '"', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2035, '\'', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2036, '"', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2043, '-', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2044, '/', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x205F, ' ', 0, 0, .common_punct, false, true, false, false),

    // Letterlike symbols, Roman numerals, and mathematical operator impostors (`U+2113..U+30FC`):
    packEntry(0x2113, 'l', 0, 0, .latin_ext, true, false, false, false),
    packEntry(0x212A, 'K', 0, 0, .latin_ext, true, false, true, true),
    packEntry(0x212B, 'A', 0, 0, .latin_ext, true, false, false, true),
    packEntry(0x2160, 'I', 0, 0, .latin_ext, true, false, true, true),
    packEntry(0x2161, 'I', 'I', 0, .latin_ext, true, false, true, true),
    packEntry(0x2162, 'I', 'I', 'I', .latin_ext, true, false, true, true),
    packEntry(0x2163, 'I', 'V', 0, .latin_ext, true, false, true, true),
    packEntry(0x2164, 'V', 0, 0, .latin_ext, true, false, true, true),
    packEntry(0x2165, 'V', 'I', 0, .latin_ext, true, false, true, true),
    packEntry(0x2166, 'V', 'I', 'I', .latin_ext, true, false, true, true),
    packEntry(0x2168, 'I', 'X', 0, .latin_ext, true, false, true, true),
    packEntry(0x2169, 'X', 0, 0, .latin_ext, true, false, true, true),
    packEntry(0x216C, 'L', 0, 0, .latin_ext, true, false, true, true),
    packEntry(0x216D, 'C', 0, 0, .latin_ext, true, false, true, true),
    packEntry(0x216E, 'D', 0, 0, .latin_ext, true, false, true, true),
    packEntry(0x216F, 'M', 0, 0, .latin_ext, true, false, true, true),
    packEntry(0x2170, 'i', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x2171, 'i', 'i', 0, .latin_ext, true, false, true, false),
    packEntry(0x2172, 'i', 'i', 'i', .latin_ext, true, false, true, false),
    packEntry(0x2173, 'i', 'v', 0, .latin_ext, true, false, true, false),
    packEntry(0x2174, 'v', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x2175, 'v', 'i', 0, .latin_ext, true, false, true, false),
    packEntry(0x2178, 'i', 'x', 0, .latin_ext, true, false, true, false),
    packEntry(0x2179, 'x', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x217C, 'l', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x217D, 'c', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x217E, 'd', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x217F, 'm', 0, 0, .latin_ext, true, false, true, false),
    packEntry(0x2212, '-', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2215, '/', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2223, '|', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2236, ':', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x27E8, '<', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x27E9, '>', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x2C80, 'A', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2C82, 'B', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2C88, 'E', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2C8E, 'H', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2C92, 'I', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2C94, 'K', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2C98, 'M', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2C9A, 'N', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2C9E, 'O', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2CA2, 'P', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2CA4, 'C', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2CA6, 'T', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2CA8, 'Y', 0, 0, .other_script, true, false, true, true),
    packEntry(0x2CAC, 'X', 0, 0, .other_script, true, false, true, true),
    packEntry(0x3000, ' ', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x3001, ',', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x3002, '.', 0, 0, .common_punct, false, true, false, false),
    packEntry(0x30CB, '=', 0, 0, .cjk_kana, false, true, false, false),
    packEntry(0x30ED, 'O', 0, 0, .cjk_kana, true, false, false, false),
    packEntry(0x30FC, '-', 0, 0, .cjk_kana, false, true, false, false),

    // Lowercase Cherokee supplement & small hyphen variants (`U+AB70..U+FE63`):
    packEntry(0xAB70, 'd', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xAB75, 'i', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xAB7A, 'a', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xAB7C, 'e', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xAB81, 'r', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xAB83, 'w', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xAB87, 'm', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xAB8B, 'h', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xAB93, 'z', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xABAA, 's', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xABAE, 'l', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xABAF, 'c', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xABB2, 'p', 0, 0, .cherokee, true, false, true, false),
    packEntry(0xFE58, '-', 0, 0, .common_punct, false, true, false, false),
    packEntry(0xFE63, '-', 0, 0, .common_punct, false, true, false, false),
};

// -------------------------------------- INTERNALS --------------------------------------

/// Packs an 8-byte `ConfusableEntry` at compile time or in algorithmic pre-folding.
inline fn packEntry(
    codepoint: u32,
    b0: u8,
    b1: u8,
    b2: u8,
    script: ScriptTag,
    is_ident: bool,
    is_standalone: bool,
    is_whole_script: bool,
    is_upper: bool,
) ConfusableEntry {
    return .{
        .codepoint = codepoint,
        .skeleton_and_script = @as(u32, b0) |
            (@as(u32, b1) << 8) |
            (@as(u32, b2) << 16) |
            (@as(u32, @backingInt(script)) << 24) |
            (if (is_ident) @as(u32, 1) << 28 else 0) |
            (if (is_standalone) @as(u32, 1) << 29 else 0) |
            (if (is_whole_script) @as(u32, 1) << 30 else 0) |
            (if (is_upper) @as(u32, 1) << 31 else 0),
    };
}

/// Binary searches a sorted `CodepointRange` table in $O(\log R)$ time.
fn containsCodepointInRanges(ranges: []const CodepointRange, codepoint: u21) bool {
    if (ranges.len == 0 or codepoint < ranges[0].start or codepoint > ranges[ranges.len - 1].end) {
        return false;
    }
    var low: usize = 0;
    var high: usize = ranges.len;
    while (low + 1 < high) {
        const mid = low + (high - low) / 2;
        if (ranges[mid].start <= codepoint) {
            low = mid;
        } else {
            high = mid;
        }
    }
    return codepoint <= ranges[low].end;
}

/// Binary searches `UTS39_CONFUSABLES` by `codepoint` in `<= 9` comparisons.
fn binarySearchConfusableTable(codepoint: u21) ?ConfusableEntry {
    if (UTS39_CONFUSABLES.len == 0 or
        codepoint < UTS39_CONFUSABLES[0].codepoint or
        codepoint > UTS39_CONFUSABLES[UTS39_CONFUSABLES.len - 1].codepoint)
    {
        return null;
    }
    var low: usize = 0;
    var high: usize = UTS39_CONFUSABLES.len;
    while (low + 1 < high) {
        const mid = low + (high - low) / 2;
        if (UTS39_CONFUSABLES[mid].codepoint <= codepoint) {
            low = mid;
        } else {
            high = mid;
        }
    }
    return if (UTS39_CONFUSABLES[low].codepoint == codepoint) UTS39_CONFUSABLES[low] else null;
}

/// Maps Mathematical Alphanumeric Greek (`U+1D6A8..U+1D7CB`) to its base Greek `U+0391..U+03C9` scalar.
fn mapMathGreekOffsetToBase(offset_in_run: u32) ?u21 {
    // Runs of 58 scalars: 25 uppercase (Alpha..Omega + Nabla) + 33 lowercase/variant forms:
    if (offset_in_run < 17) return @intCast(0x0391 + offset_in_run); // Α..Ρ
    if (offset_in_run == 17) return 0x03F4; // ϴ
    if (offset_in_run >= 18 and offset_in_run <= 24) return @intCast(0x03A3 + (offset_in_run - 18)); // Σ..Ω
    if (offset_in_run == 25) return null; // ∇
    if (offset_in_run >= 26 and offset_in_run <= 50) return @intCast(0x03B1 + (offset_in_run - 26)); // α..ω
    return null;
}

/// Returns `true` when ASCII letter `ascii_byte` has a visual homoglyph in `script_mask` (`cyrillic` / `greek`).
fn hasCrossScriptAsciiHomoglyph(ascii_byte: u8, chunk_script_mask: u16) bool {
    const has_cyrillic_or_cherokee = (chunk_script_mask &
        ((@as(u16, 1) << @backingInt(ScriptTag.cyrillic)) |
            (@as(u16, 1) << @backingInt(ScriptTag.cherokee)) |
            (@as(u16, 1) << @backingInt(ScriptTag.armenian)))) != 0;
    const has_greek = (chunk_script_mask & (@as(u16, 1) << @backingInt(ScriptTag.greek))) != 0;

    if (ascii_byte >= 'A' and ascii_byte <= 'Z') {
        const bit = @as(u32, 1) << @intCast(ascii_byte - 'A');
        if (has_cyrillic_or_cherokee and (ASCII_CYRILLIC_HOMOGLYPH_UPPER_MASK & bit) != 0) return true;
        if (has_greek and (ASCII_GREEK_HOMOGLYPH_UPPER_MASK & bit) != 0) return true;
    } else if (ascii_byte >= 'a' and ascii_byte <= 'z') {
        const bit = @as(u32, 1) << @intCast(ascii_byte - 'a');
        if (has_cyrillic_or_cherokee and (ASCII_CYRILLIC_HOMOGLYPH_LOWER_MASK & bit) != 0) return true;
        if (has_greek and (ASCII_GREEK_HOMOGLYPH_LOWER_MASK & bit) != 0) return true;
    }
    return false;
}

/// Returns `true` if `codepoint` is a word letter/digit for `W0104` mixed-script word boundary scanning.
inline fn isWordCodepoint(codepoint: u21) bool {
    if (codepoint < 0x80) {
        return std.ascii.isAlphanumeric(@intCast(codepoint));
    }
    return isUnicodeXidContinue(codepoint);
}

comptime {
    @setEvalBranchQuota(50_000);
    assert(@sizeOf(ConfusableEntry) == 8);
    assert(UTS39_CONFUSABLES.len <= 320);
    assert(@sizeOf(@TypeOf(UTS39_CONFUSABLES)) <= 2_560);

    // [1] Enforce strict ascending codepoint order across all static range and confusable tables:
    for (1..XID_START_RANGES.len) |i| {
        assert(XID_START_RANGES[i - 1].start <= XID_START_RANGES[i - 1].end);
        assert(XID_START_RANGES[i - 1].end < XID_START_RANGES[i].start);
    }
    for (1..XID_CONTINUE_EXTRA_RANGES.len) |i| {
        assert(XID_CONTINUE_EXTRA_RANGES[i - 1].start <= XID_CONTINUE_EXTRA_RANGES[i - 1].end);
        assert(XID_CONTINUE_EXTRA_RANGES[i - 1].end < XID_CONTINUE_EXTRA_RANGES[i].start);
    }
    for (1..UTS39_CONFUSABLES.len) |i| {
        assert(UTS39_CONFUSABLES[i - 1].codepoint < UTS39_CONFUSABLES[i].codepoint);
        const item = UTS39_CONFUSABLES[i];
        assert(item.isIdentConfusable() or item.isStandaloneImpostor());
    }

    // [2] Enforce zero false-positive flagging on canonical CoreX typography, monochrome CLI glyphs, and scientific Greek:
    const canonical_exempt_scalars = [_]u21{
        0x00A7, // §
        0x00B1, // ±
        0x00D7, // ×
        0x2013, // – (en-dash)
        0x2022, // •
        0x2026, // … (ellipsis)
        0x2192, // →
        0x221E, // ∞
        0x2248, // ≈
        0x2260, // ≠
        0x2264, // ≤
        0x2265, // ≥
        0x25B8, // ▸
        0x26A0, // ⚠
        0x2713, // ✓
        0x2717, // ✗
        // Visibly distinct scientific Greek (`DR-25` §2.1):
        0x0393, // Γ
        0x0394, // Δ
        0x0398, // Θ
        0x039B, // Λ
        0x039E, // Ξ
        0x03A0, // Π
        0x03A3, // Σ
        0x03A6, // Φ
        0x03A8, // Ψ
        0x03A9, // Ω
        0x03B4, // δ
        0x03B6, // ζ
        0x03B8, // θ
        0x03BB, // λ
        0x03BC, // μ
        0x03BE, // ξ
        0x03C0, // π
        0x03C3, // σ
        0x03C6, // φ
        0x03C8, // ψ
    };
    for (canonical_exempt_scalars) |exempt_cp| {
        if (lookupConfusable(exempt_cp)) |found| {
            assert(!found.isIdentConfusable());
            assert(!found.isStandaloneImpostor());
        }
    }
    var box_cp: u21 = 0x2500;
    while (box_cp <= 0x257F) : (box_cp += 1) {
        assert(lookupConfusable(box_cp) == null);
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Returns `true` if `codepoint` is a Trojan Source bidi control or zero-width spoofing scalar (`W0102`).
pub inline fn isTrojanControlCodepoint(codepoint: u21, byte_offset: usize) bool {
    if (codepoint < 0x200B or (codepoint > 0x2069 and codepoint < 0xFE00) or codepoint > 0xFEFF) {
        return false;
    }
    return switch (codepoint) {
        0x202A...0x202E,
        0x2066...0x2069,
        0x200B,
        0x2060,
        0xFE00...0xFE0F,
        => true,
        0xFEFF => byte_offset > 0,
        else => false,
    };
}

/// Returns `true` if `codepoint` (`>= 0x80` or ASCII) is a valid `UAX #31` `XID_Start` identifier starter.
pub fn isUnicodeXidStart(codepoint: u21) bool {
    if (codepoint < 0x80) {
        const byte_val: u8 = @intCast(codepoint);
        return std.ascii.isAlphabetic(byte_val) or byte_val == '_';
    }
    return containsCodepointInRanges(&XID_START_RANGES, codepoint);
}

/// Returns `true` if `codepoint` is a valid `UAX #31` `XID_Continue` identifier continuation scalar.
pub fn isUnicodeXidContinue(codepoint: u21) bool {
    if (codepoint < 0x80) {
        const byte_val: u8 = @intCast(codepoint);
        return std.ascii.isAlphanumeric(byte_val) or byte_val == '_';
    }
    return containsCodepointInRanges(&XID_START_RANGES, codepoint) or
        containsCodepointInRanges(&XID_CONTINUE_EXTRA_RANGES, codepoint);
}

/// Returns `true` when `codepoint` has uppercase (`Lu` / `Lt`) casing for identifier chunking.
pub fn isUnicodeUppercase(codepoint: u21) bool {
    if (codepoint < 0x80) {
        return codepoint >= 'A' and codepoint <= 'Z';
    }
    if (lookupConfusable(codepoint)) |entry| {
        if (entry.isUppercase()) return true;
    }
    return (codepoint >= 0x00C0 and codepoint <= 0x00DE and codepoint != 0x00D7) or
        (codepoint >= 0x0391 and codepoint <= 0x03AB and codepoint != 0x03A2) or
        (codepoint >= 0x0410 and codepoint <= 0x042F) or
        (codepoint >= 0x0531 and codepoint <= 0x0556) or
        (codepoint >= 0x10A0 and codepoint <= 0x10C5) or
        (codepoint >= 0xFF21 and codepoint <= 0xFF3A);
}

/// Folds Fullwidth ASCII (`U+FF01..U+FF5E`) and Mathematical Alphanumeric (`U+1D400..U+1D7FF`) in $O(1)$ arithmetic.
pub fn foldAlgorithmicConfusable(codepoint: u21) ?ConfusableEntry {
    // [1] Fullwidth ASCII block (`U+FF01..U+FF5E` -> `0x21..0x7E`):
    if (codepoint >= 0xFF01 and codepoint <= 0xFF5E) {
        const ascii_byte: u8 = @intCast(codepoint - 0xFEE0);
        const is_alpha = std.ascii.isAlphabetic(ascii_byte);
        const is_digit = std.ascii.isDigit(ascii_byte);
        const is_upper = std.ascii.isUpper(ascii_byte);
        if (is_alpha) {
            return packEntry(codepoint, ascii_byte, 0, 0, .latin_ext, true, false, true, is_upper);
        }
        return packEntry(codepoint, ascii_byte, 0, 0, .common_punct, is_digit, true, is_digit, false);
    }

    // [2] Mathematical Alphanumeric Symbols (`U+1D400..U+1D7FF`):
    if (codepoint >= 0x1D400 and codepoint <= 0x1D6A5) {
        if (codepoint == 0x1D6A4) return packEntry(codepoint, 'i', 0, 0, .latin_ext, true, false, false, false);
        if (codepoint == 0x1D6A5) return packEntry(codepoint, 'j', 0, 0, .latin_ext, true, false, false, false);
        const rel = codepoint - 0x1D400;
        const idx_in_52 = rel % 52;
        if (idx_in_52 < 26) {
            const upper_ch: u8 = @intCast('A' + idx_in_52);
            return packEntry(codepoint, upper_ch, 0, 0, .latin_ext, true, false, true, true);
        }
        const lower_ch: u8 = @intCast('a' + (idx_in_52 - 26));
        return packEntry(codepoint, lower_ch, 0, 0, .latin_ext, true, false, true, false);
    }
    if (codepoint >= 0x1D6A8 and codepoint <= 0x1D7CB) {
        const greek_rel = (codepoint - 0x1D6A8) % 58;
        if (mapMathGreekOffsetToBase(greek_rel)) |base_greek_cp| {
            if (binarySearchConfusableTable(base_greek_cp)) |greek_entry| {
                return .{
                    .codepoint = codepoint,
                    .skeleton_and_script = greek_entry.skeleton_and_script,
                };
            }
        }
        return null;
    }
    if (codepoint >= 0x1D7CE and codepoint <= 0x1D7FF) {
        const digit_ch: u8 = @intCast('0' + ((codepoint - 0x1D7CE) % 10));
        return packEntry(codepoint, digit_ch, 0, 0, .latin_ext, true, true, true, false);
    }
    return null;
}

/// Resolves `codepoint` via $O(1)$ algorithmic folding followed by `<= 9`-step `.rodata` binary search.
pub fn lookupConfusable(codepoint: u21) ?ConfusableEntry {
    if (codepoint < 0x80) return null;
    if (foldAlgorithmicConfusable(codepoint)) |folded| return folded;
    return binarySearchConfusableTable(codepoint);
}

/// Computes the script bit (`0` = ASCII Latin, `1..8` = `ScriptTag`, `0` = neutral digit/`_`) for `codepoint`.
pub fn classifyLetterScriptBit(codepoint: u21) u16 {
    if (codepoint < 0x80) {
        const byte_val: u8 = @intCast(codepoint);
        if (std.ascii.isAlphabetic(byte_val)) return 1 << 0;
        return 0;
    }
    if (lookupConfusable(codepoint)) |entry| {
        const tag = entry.scriptTag();
        if (tag != .common_punct) {
            return @as(u16, 1) << @backingInt(tag);
        }
    }
    if ((codepoint >= 0x00C0 and codepoint <= 0x024F) or (codepoint >= 0x1E00 and codepoint <= 0x1EFF)) {
        return @as(u16, 1) << @backingInt(ScriptTag.latin_ext);
    }
    if ((codepoint >= 0x0370 and codepoint <= 0x03FF) or (codepoint >= 0x1F00 and codepoint <= 0x1FFF)) {
        return @as(u16, 1) << @backingInt(ScriptTag.greek);
    }
    if (codepoint >= 0x0400 and codepoint <= 0x052F) {
        return @as(u16, 1) << @backingInt(ScriptTag.cyrillic);
    }
    if (codepoint >= 0x0530 and codepoint <= 0x058F) {
        return @as(u16, 1) << @backingInt(ScriptTag.armenian);
    }
    if (codepoint >= 0x0590 and codepoint <= 0x05FF) {
        return @as(u16, 1) << @backingInt(ScriptTag.hebrew);
    }
    if ((codepoint >= 0x13A0 and codepoint <= 0x13FF) or (codepoint >= 0xAB70 and codepoint <= 0xABBF)) {
        return @as(u16, 1) << @backingInt(ScriptTag.cherokee);
    }
    if (codepoint >= 0x3040 and codepoint <= 0x9FFF) {
        return @as(u16, 1) << @backingInt(ScriptTag.cjk_kana);
    }
    return @as(u16, 1) << @backingInt(ScriptTag.other_script);
}

/// Materializes the `UTS #39` skeleton of `ident_text` into `out_buf` (`0` heap allocations).
pub fn computeUts39Skeleton(ident_text: []const u8, out_buf: []u8) []const u8 {
    var cursor: usize = 0;
    var write_pos: usize = 0;
    while (cursor < ident_text.len and write_pos < out_buf.len) {
        const first_byte = ident_text[cursor];
        if (first_byte < 0x80) {
            // Map ASCII `'I'` / `'1'`? No: UTS #39 keeps distinct ASCII identifiers distinct so `user1` != `userl`!
            out_buf[write_pos] = first_byte;
            write_pos += 1;
            cursor += 1;
            continue;
        }
        const seq_len = std.unicode.utf8ByteSequenceLength(first_byte) catch {
            out_buf[write_pos] = first_byte;
            write_pos += 1;
            cursor += 1;
            continue;
        };
        if (cursor + seq_len > ident_text.len) break;
        const decoded_cp = std.unicode.utf8Decode(ident_text[cursor .. cursor + seq_len]) catch {
            out_buf[write_pos] = first_byte;
            write_pos += 1;
            cursor += 1;
            continue;
        };
        if (lookupConfusable(decoded_cp)) |entry| {
            var skel_bytes: [3]u8 = undefined;
            const skel_slice = entry.writeSkeleton(&skel_bytes);
            const copy_len = @min(skel_slice.len, out_buf.len - write_pos);
            @memcpy(out_buf[write_pos .. write_pos + copy_len], skel_slice[0..copy_len]);
            write_pos += copy_len;
        } else {
            const copy_len = @min(seq_len, out_buf.len - write_pos);
            @memcpy(out_buf[write_pos .. write_pos + copy_len], ident_text[cursor .. cursor + copy_len]);
            write_pos += copy_len;
        }
        cursor += seq_len;
    }
    return out_buf[0..write_pos];
}

/// Evaluates `UTS #55` §5.1.2.2 identifier-chunk mixed-script confusable rules (`W0103`).
pub fn analyzeUts55IdentifierChunks(ident_text: []const u8) IdentChunkAnalysis {
    // Fast ASCII exit (`0` work when all bytes `< 0x80`):
    var has_non_ascii = false;
    for (ident_text) |byte_val| {
        if (byte_val >= 0x80) {
            has_non_ascii = true;
            break;
        }
    }
    if (!has_non_ascii) return .{};

    // Decode up to 128 scalars on stack for chunk boundary splitting (`_` and `PascalCase`):
    const DecodedScalar = struct {
        cp: u21,
        byte_off: u16,
        is_upper: bool,
        is_confusable: bool,
        script_bit: u16,
    };
    var scalars: [128]DecodedScalar = undefined;
    var scalar_count: usize = 0;
    var cursor: usize = 0;
    var ident_has_ascii_latin = false;

    while (cursor < ident_text.len and scalar_count < scalars.len) {
        const start_off = cursor;
        const first_byte = ident_text[cursor];
        if (first_byte < 0x80) {
            if (std.ascii.isAlphabetic(first_byte)) ident_has_ascii_latin = true;
            scalars[scalar_count] = .{
                .cp = first_byte,
                .byte_off = @intCast(@min(start_off, std.math.maxInt(u16))),
                .is_upper = std.ascii.isUpper(first_byte),
                .is_confusable = false,
                .script_bit = classifyLetterScriptBit(first_byte),
            };
            scalar_count += 1;
            cursor += 1;
            continue;
        }
        const seq_len = std.unicode.utf8ByteSequenceLength(first_byte) catch {
            cursor += 1;
            continue;
        };
        if (cursor + seq_len > ident_text.len) break;
        const decoded_cp = std.unicode.utf8Decode(ident_text[cursor .. cursor + seq_len]) catch {
            cursor += seq_len;
            continue;
        };
        const opt_conf = lookupConfusable(decoded_cp);
        scalars[scalar_count] = .{
            .cp = decoded_cp,
            .byte_off = @intCast(@min(start_off, std.math.maxInt(u16))),
            .is_upper = isUnicodeUppercase(decoded_cp),
            .is_confusable = if (opt_conf) |conf| conf.isIdentConfusable() else false,
            .script_bit = classifyLetterScriptBit(decoded_cp),
        };
        scalar_count += 1;
        cursor += seq_len;
    }

    var idx: usize = 0;
    while (idx < scalar_count) {
        if (scalars[idx].cp == '_') {
            idx += 1;
            continue;
        }
        const chunk_start = idx;
        idx += 1;
        while (idx < scalar_count and scalars[idx].cp != '_') {
            const prev = scalars[idx - 1];
            const curr = scalars[idx];
            // Split on `lower -> Upper` (`userId` -> `user` | `Id`) or `Upper -> Upper+lower` (`HTTPServer` -> `HTTP` | `Server`):
            // Keep 2-letter scientific `Δt` (`Upper` Greek + single lowercase ASCII) together in one chunk so `Δt` is evaluated cleanly:
            const is_lower_to_upper = !prev.is_upper and prev.script_bit != 0 and curr.is_upper;
            const is_acronym_split = prev.is_upper and curr.is_upper and
                (idx + 1 < scalar_count and scalars[idx + 1].cp != '_' and
                    !scalars[idx + 1].is_upper and scalars[idx + 1].script_bit != 0);
            if (is_lower_to_upper or is_acronym_split) break;
            idx += 1;
        }
        const chunk = scalars[chunk_start..idx];

        var chunk_script_mask: u16 = 0;
        var first_conf_idx: ?usize = null;
        var first_non_ascii_idx: ?usize = null;
        var all_non_ascii_confusable = true;
        var non_ascii_letter_count: usize = 0;

        for (chunk, 0..) |item, rel_i| {
            chunk_script_mask |= item.script_bit;
            if (item.cp >= 0x80 and item.script_bit != 0) {
                non_ascii_letter_count += 1;
                if (first_non_ascii_idx == null) first_non_ascii_idx = rel_i;
                if (item.is_confusable) {
                    if (first_conf_idx == null) first_conf_idx = rel_i;
                } else {
                    all_non_ascii_confusable = false;
                }
            }
        }

        if (@popCount(chunk_script_mask) >= 2) {
            if (first_conf_idx) |conf_i| {
                return .{
                    .has_mixed_script_confusable = true,
                    .first_confusable_rel_byte = chunk[conf_i].byte_off,
                    .first_confusable_cp = chunk[conf_i].cp,
                };
            }
            // Check whether any ASCII letter in this mixed-script chunk has a cross-script homoglyph (`Строкa` / `Бжa` guard):
            for (chunk) |item| {
                if (item.cp < 0x80 and hasCrossScriptAsciiHomoglyph(@intCast(item.cp), chunk_script_mask)) {
                    const report_item = chunk[first_non_ascii_idx orelse 0];
                    return .{
                        .has_mixed_script_confusable = true,
                        .first_confusable_rel_byte = report_item.byte_off,
                        .first_confusable_cp = report_item.cp,
                    };
                }
            }
        } else if (ident_has_ascii_latin and non_ascii_letter_count > 0 and all_non_ascii_confusable) {
            // Cross-`_` guard (`pay_р` where `_р` is 100% confusable alongside Latin `pay_`; `Δ_t` stays permitted!):
            const report_item = chunk[first_conf_idx.?];
            return .{
                .has_mixed_script_confusable = true,
                .first_confusable_rel_byte = report_item.byte_off,
                .first_confusable_cp = report_item.cp,
            };
        }
    }
    return .{};
}

/// Checks whether the alphanumeric word enclosing `[cp_start .. cp_end)` mixes ASCII Latin with non-ASCII letters (`W0104`).
pub fn isMixedScriptWordAt(
    text: []const u8,
    cp_start: usize,
    cp_end: usize,
    word_end_out: *usize,
) bool {
    // [1] Walk backward from `cp_start` to find `word_start`:
    var word_start = cp_start;
    while (word_start > 0) {
        const prev_byte = text[word_start - 1];
        if (prev_byte < 0x80) {
            if (!std.ascii.isAlphanumeric(prev_byte)) break;
            word_start -= 1;
        } else {
            var char_start = word_start - 1;
            while (char_start > 0 and (text[char_start] & 0xC0) == 0x80) : (char_start -= 1) {}
            const decoded_cp = std.unicode.utf8Decode(text[char_start..word_start]) catch break;
            if (!isWordCodepoint(decoded_cp)) break;
            word_start = char_start;
        }
    }

    // [2] Walk forward from `cp_end` to find `word_end`:
    var word_end = cp_end;
    while (word_end < text.len) {
        const cur_byte = text[word_end];
        if (cur_byte < 0x80) {
            if (!std.ascii.isAlphanumeric(cur_byte)) break;
            word_end += 1;
        } else {
            const seq_len = std.unicode.utf8ByteSequenceLength(cur_byte) catch break;
            if (word_end + seq_len > text.len) break;
            const decoded_cp = std.unicode.utf8Decode(text[word_end .. word_end + seq_len]) catch break;
            if (!isWordCodepoint(decoded_cp)) break;
            word_end += seq_len;
        }
    }
    word_end_out.* = word_end;

    // [3] Scan `[word_start .. word_end)` for coexistence of ASCII `[A-Za-z]` and non-ASCII letters:
    var has_ascii_latin = false;
    var has_non_ascii_letter = false;
    var scan_pos = word_start;
    while (scan_pos < word_end) {
        const byte_val = text[scan_pos];
        if (byte_val < 0x80) {
            if (std.ascii.isAlphabetic(byte_val)) has_ascii_latin = true;
            scan_pos += 1;
        } else {
            const seq_len = std.unicode.utf8ByteSequenceLength(byte_val) catch {
                scan_pos += 1;
                continue;
            };
            if (scan_pos + seq_len > word_end) break;
            const decoded_cp = std.unicode.utf8Decode(text[scan_pos .. scan_pos + seq_len]) catch {
                scan_pos += seq_len;
                continue;
            };
            if (isUnicodeXidStart(decoded_cp)) has_non_ascii_letter = true;
            scan_pos += seq_len;
        }
        if (has_ascii_latin and has_non_ascii_letter) return true;
    }
    return false;
}

// ---------------------------------------- TESTS ----------------------------------------

test "test_unicode_confusables_rodata_bounds_and_canonical_allowlist" {
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(ConfusableEntry));
    try std.testing.expect(UTS39_CONFUSABLES.len <= 320);
    try std.testing.expect(@sizeOf(@TypeOf(UTS39_CONFUSABLES)) <= 2_560);

    // Trojan controls (`W0102`):
    try std.testing.expect(isTrojanControlCodepoint(0x202E, 10)); // RLO
    try std.testing.expect(isTrojanControlCodepoint(0x2066, 0)); // LRI
    try std.testing.expect(isTrojanControlCodepoint(0x200B, 5)); // ZWSP
    try std.testing.expect(isTrojanControlCodepoint(0xFE0F, 5)); // VS16 colored-emoji selector
    try std.testing.expect(!isTrojanControlCodepoint(0xFEFF, 0)); // File-initial BOM allowed
    try std.testing.expect(isTrojanControlCodepoint(0xFEFF, 3)); // Mid-file ZWNBSP flagged

    // Canonical CoreX symbols and scientific Greek MUST NEVER be flagged:
    const safe_scalars = [_]u21{
        0x2013, 0x2026, 0x00A7, 0x00D7, 0x2264, 0x2265, 0x2260, 0x2192,
        0x2500, 0x256D, 0x2570, 0x2502, 0x251C, 0x25B8, 0x2022, 0x2713,
        0x2717, 0x26A0, 0x0394, 0x0393, 0x0398, 0x039B, 0x03A0, 0x03A3,
        0x03A6, 0x03A8, 0x03A9, 0x03B4, 0x03B8, 0x03BB, 0x03BC, 0x03C0,
        0x03C3, 0x03C6, 0x03C8,
    };
    for (safe_scalars) |safe_cp| {
        try std.testing.expect(lookupConfusable(safe_cp) == null);
    }

    // Algorithmic folding for Fullwidth and Mathematical Alphanumeric symbols:
    const fullwidth_a = lookupConfusable(0xFF21).?;
    try std.testing.expectEqual(@as(u8, 'A'), fullwidth_a.skelByte0());
    try std.testing.expect(fullwidth_a.isIdentConfusable());

    const math_bold_x = lookupConfusable(0x1D431).?;
    try std.testing.expectEqual(@as(u8, 'x'), math_bold_x.skelByte0());
    try std.testing.expect(math_bold_x.isIdentConfusable());
}

test "test_unicode_uts55_identifier_chunks_and_uts39_skeletons" {
    // Mixed-script spoofing chunks flagged (`pаypal` with Cyrillic `а` U+0430, `Строкa` with ASCII `a`, `HttpSеrver`):
    const paypal_spoof = analyzeUts55IdentifierChunks("p\u{0430}ypal");
    try std.testing.expect(paypal_spoof.has_mixed_script_confusable);
    try std.testing.expectEqual(@as(u21, 0x0430), paypal_spoof.first_confusable_cp);

    const stroka_spoof = analyzeUts55IdentifierChunks("\u{0421}\u{0442}\u{0440}\u{043E}\u{043A}a");
    try std.testing.expect(stroka_spoof.has_mixed_script_confusable);

    const cross_underscore_spoof = analyzeUts55IdentifierChunks("pay_\u{0440}");
    try std.testing.expect(cross_underscore_spoof.has_mixed_script_confusable);

    // Pure non-Latin and scientific Greek mixed chunks permitted (`Строка`, `Δt`, `μs`, `λ_max`, `θ_rad`):
    try std.testing.expect(!analyzeUts55IdentifierChunks("\u{0421}\u{0442}\u{0440}\u{043E}\u{043A}\u{0430}").has_mixed_script_confusable);
    try std.testing.expect(!analyzeUts55IdentifierChunks("\u{0394}t").has_mixed_script_confusable);
    try std.testing.expect(!analyzeUts55IdentifierChunks("\u{03BC}s").has_mixed_script_confusable);
    try std.testing.expect(!analyzeUts55IdentifierChunks("\u{03BB}_max").has_mixed_script_confusable);
    try std.testing.expect(!analyzeUts55IdentifierChunks("\u{03B8}_rad").has_mixed_script_confusable);

    // UTS #39 skeleton collision (`scope` vs `scоpe` with Cyrillic `о` U+043E):
    var skel_a: [64]u8 = undefined;
    var skel_b: [64]u8 = undefined;
    try std.testing.expectEqualStrings(
        computeUts39Skeleton("scope", &skel_a),
        computeUts39Skeleton("sc\u{043E}pe", &skel_b),
    );

    // Word-context check (`Ruff #4859` guard: `"Сache"` flagged, pure `"Привет"` NOT flagged):
    var word_end: usize = 0;
    try std.testing.expect(isMixedScriptWordAt("\"\u{0421}ache\"", 1, 3, &word_end));
    try std.testing.expect(!isMixedScriptWordAt("\"\u{041F}\u{0440}\u{0438}\u{0432}\u{0435}\u{0442}\"", 1, 3, &word_end));
}

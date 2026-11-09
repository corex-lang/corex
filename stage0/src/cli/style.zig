//! CLI Monochrome Glyph Registry & ANSI Styling Engine
//!
//! Defines the canonical monochrome Unicode box-drawing and status glyph vocabulary, terminal `ColorMode`
//! resolution (`NO_COLOR`, `TERM=dumb`, and TTY detection), and ANSI SGR escape formatting primitives.
//!
//! All terminal output across the CoreX toolchain routes through this module to guarantee zero colored
//! emojis and deterministic width calculation across ANSI-enabled and plain-text streams.

const std = @import("std");

// ---------------------------------------- TYPES ----------------------------------------

/// Terminal ANSI color activation policy for CLI and diagnostic output.
pub const ColorMode = enum(u8) {
    /// Automatically enable ANSI colors when writing to a capable TTY without `NO_COLOR`.
    auto = 0,
    /// Unconditionally emit ANSI SGR escape sequences.
    always = 1,
    /// Never emit ANSI SGR escape sequences (pure monochrome Unicode).
    never = 2,

    /// Parses a CLI `--color=<when>` value into a `ColorMode`.
    pub fn parse(raw_value: []const u8) ?ColorMode {
        if (std.mem.eql(u8, raw_value, "auto")) {
            return .auto;
        } else if (std.mem.eql(u8, raw_value, "always")) {
            return .always;
        } else if (std.mem.eql(u8, raw_value, "never")) {
            return .never;
        }
        return null;
    }

    /// Returns the canonical lowercase CLI string representation of this `ColorMode`.
    pub fn asStr(self: ColorMode) []const u8 {
        return switch (self) {
            .auto => "auto",
            .always => "always",
            .never => "never",
        };
    }
};

/// Semantic terminal styling roles mapped to canonical ANSI SGR escape sequences.
pub const StyleRole = enum(u8) {
    /// Unstyled plain text.
    plain = 0,
    /// High-intensity bold text (`\x1b[1m`).
    bold = 1,
    /// Low-intensity dim text for box borders and gutters (`\x1b[2m`).
    dim = 2,
    /// Underlined text (`\x1b[4m`).
    underline = 3,
    /// Bold red status for fatal errors and primary carets (`\x1b[1;31m`).
    err = 4,
    /// Bold yellow status for compiler warnings (`\x1b[1;33m`).
    warning = 5,
    /// Bold cyan status for diagnostic notes and secondary spans (`\x1b[1;36m`).
    note = 6,
    /// Bold blue status for actionable help suggestions (`\x1b[1;34m`).
    help = 7,
    /// Bold green status for passed checks and diff insertions (`\x1b[1;32m`).
    success = 8,
    /// Red foreground for diff deletion lines (`\x1b[31m`).
    diff_remove = 9,
    /// Green foreground for diff addition lines (`\x1b[32m`).
    diff_add = 10,

    /// Returns the opening ANSI SGR escape sequence for this `StyleRole`.
    pub fn asAnsiPrefix(self: StyleRole) []const u8 {
        return switch (self) {
            .plain => "",
            .bold => Sgr.BOLD,
            .dim => Sgr.DIM,
            .underline => Sgr.UNDERLINE,
            .err => Sgr.BOLD_RED,
            .warning => Sgr.BOLD_YELLOW,
            .note => Sgr.BOLD_CYAN,
            .help => Sgr.BOLD_BLUE,
            .success => Sgr.BOLD_GREEN,
            .diff_remove => Sgr.FG_RED,
            .diff_add => Sgr.FG_GREEN,
        };
    }
};

/// Resolved styling configuration passed to terminal renderers.
pub const StyleConfig = struct {
    /// Whether ANSI SGR escape sequences should be emitted to the target stream.
    is_color_enabled: bool = false,

    /// Default plain monochrome configuration with ANSI colors disabled.
    pub const MONOCHROME: StyleConfig = .{ .is_color_enabled = false };
    /// Configuration with ANSI SGR sequences unconditionally enabled.
    pub const COLORED: StyleConfig = .{ .is_color_enabled = true };

    /// Writes `text` wrapped in `role` ANSI SGR sequences when `is_color_enabled` is true.
    pub fn writeStyled(
        self: StyleConfig,
        writer: *std.Io.Writer,
        role: StyleRole,
        text: []const u8,
    ) std.Io.Writer.Error!void {
        if (!self.is_color_enabled or role == .plain or text.len == 0) {
            try writer.writeAll(text);
            return;
        }
        try writer.writeAll(role.asAnsiPrefix());
        try writer.writeAll(text);
        try writer.writeAll(Sgr.RESET);
    }

    /// Writes a repeated monochrome glyph or string `count` times with optional `role` styling.
    pub fn writeRepeated(
        self: StyleConfig,
        writer: *std.Io.Writer,
        role: StyleRole,
        glyph: []const u8,
        n: usize,
    ) std.Io.Writer.Error!void {
        if (n == 0 or glyph.len == 0) return;
        const should_color = self.is_color_enabled and role != .plain;
        if (should_color) {
            try writer.writeAll(role.asAnsiPrefix());
        }
        var i: usize = 0;
        while (i < n) : (i += 1) {
            try writer.writeAll(glyph);
        }
        if (should_color) {
            try writer.writeAll(Sgr.RESET);
        }
    }

    /// Writes a canonical status header (`<glyph> <label>: <message>`) with semantic styling.
    pub fn writeStatusHeader(
        self: StyleConfig,
        writer: *std.Io.Writer,
        role: StyleRole,
        status_glyph: []const u8,
        label_text: []const u8,
        message_text: []const u8,
    ) std.Io.Writer.Error!void {
        if (self.is_color_enabled and role != .plain) {
            try writer.writeAll(role.asAnsiPrefix());
            try writer.writeAll(status_glyph);
            try writer.writeByte(' ');
            try writer.writeAll(label_text);
            try writer.writeAll(Sgr.RESET);
            try writer.writeAll(Sgr.BOLD);
            try writer.writeAll(": ");
            try writer.writeAll(message_text);
            try writer.writeAll(Sgr.RESET);
        } else {
            try writer.writeAll(status_glyph);
            try writer.writeByte(' ');
            try writer.writeAll(label_text);
            try writer.writeAll(": ");
            try writer.writeAll(message_text);
        }
    }
};

/// Canonical monochrome Unicode glyph vocabulary (`DR-15` Section 2.1).
pub const Glyphs = struct {
    // Box corners and border glyphs:
    /// Rounded top-left corner (`U+256D`).
    pub const TOP_LEFT: []const u8 = "╭";
    /// Rounded top-right corner (`U+256E`).
    pub const TOP_RIGHT: []const u8 = "╮";
    /// Rounded bottom-left corner (`U+2570`).
    pub const BOTTOM_LEFT: []const u8 = "╰";
    /// Rounded bottom-right corner (`U+256F`).
    pub const BOTTOM_RIGHT: []const u8 = "╯";
    /// Horizontal box border (`U+2500`).
    pub const HORIZONTAL: []const u8 = "─";
    /// Short left horizontal stub (`U+2574`).
    pub const HORIZONTAL_LEFT: []const u8 = "╴";
    /// Vertical box border (`U+2502`).
    pub const VERTICAL: []const u8 = "│";
    /// Left T-junction (`U+251C`).
    pub const T_RIGHT: []const u8 = "├";
    /// Right T-junction (`U+2524`).
    pub const T_LEFT: []const u8 = "┤";
    /// Top T-junction (`U+252C`).
    pub const T_DOWN: []const u8 = "┬";
    /// Bottom T-junction (`U+2534`).
    pub const T_UP: []const u8 = "┴";
    /// Four-way interior cross junction (`U+253C`).
    pub const CROSS: []const u8 = "┼";
    /// Dotted vertical line for elided source gaps (`U+2506`).
    pub const DOTTED_VERTICAL: []const u8 = "┆";

    // Pointers and bullets:
    /// Solid right-pointing triangle pointer (`U+25B8`).
    pub const POINTER_SOLID: []const u8 = "▸";
    /// Outline right-pointing triangle pointer (`U+25B9`).
    pub const POINTER_OUTLINE: []const u8 = "▹";
    /// Solid circular bullet (`U+2022`).
    pub const BULLET: []const u8 = "•";
    /// Primary diagnostic span underline caret (`U+005E`).
    pub const CARET: []const u8 = "^";
    /// Secondary tilde underline glyph (`U+007E`).
    pub const TILDE: []const u8 = "~";
    /// Single-character horizontal ellipsis (`U+2026`).
    pub const ELLIPSIS: []const u8 = "…";

    // Strictly monochrome status glyphs:
    /// Monochrome checkmark status indicator (`U+2713`).
    pub const SUCCESS: []const u8 = "✓";
    /// Monochrome ballot cross failure indicator (`U+2717`).
    pub const FAILURE: []const u8 = "✗";
    /// Monochrome warning sign (`U+26A0` + Variation Selector-15 `U+FE0E` forcing text presentation).
    pub const WARNING: []const u8 = "⚠\u{FE0E}";

    // High-resolution progress and UI glyphs:
    /// Sub-character 1/8th-width horizontal bar blocks (`U+258F`–`U+2588`).
    pub const BLOCKS_EIGHTH: [8][]const u8 = .{ "▏", "▎", "▍", "▌", "▋", "▊", "▉", "█" };
    /// Monochrome Braille activity spinner frames (`U+280B`–`U+280F`).
    pub const SPINNER_FRAMES: [10][]const u8 = .{ "⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏" };
};

/// Canonical ANSI Select Graphic Rendition (SGR) escape sequences.
pub const Sgr = struct {
    /// Reset all SGR attributes (`\x1b[0m`).
    pub const RESET: []const u8 = "\x1b[0m";
    /// Bold / increased intensity (`\x1b[1m`).
    pub const BOLD: []const u8 = "\x1b[1m";
    /// Dim / decreased intensity (`\x1b[2m`).
    pub const DIM: []const u8 = "\x1b[2m";
    /// Underline text (`\x1b[4m`).
    pub const UNDERLINE: []const u8 = "\x1b[4m";
    /// Standard red foreground (`\x1b[31m`).
    pub const FG_RED: []const u8 = "\x1b[31m";
    /// Standard green foreground (`\x1b[32m`).
    pub const FG_GREEN: []const u8 = "\x1b[32m";
    /// Standard yellow foreground (`\x1b[33m`).
    pub const FG_YELLOW: []const u8 = "\x1b[33m";
    /// Standard blue foreground (`\x1b[34m`).
    pub const FG_BLUE: []const u8 = "\x1b[34m";
    /// Standard magenta foreground (`\x1b[35m`).
    pub const FG_MAGENTA: []const u8 = "\x1b[35m";
    /// Standard cyan foreground (`\x1b[36m`).
    pub const FG_CYAN: []const u8 = "\x1b[36m";
    /// Standard white foreground (`\x1b[37m`).
    pub const FG_WHITE: []const u8 = "\x1b[37m";
    /// Bright black (dark gray) foreground (`\x1b[90m`).
    pub const FG_BRIGHT_BLACK: []const u8 = "\x1b[90m";
    /// Bold red foreground (`\x1b[1;31m`).
    pub const BOLD_RED: []const u8 = "\x1b[1;31m";
    /// Bold green foreground (`\x1b[1;32m`).
    pub const BOLD_GREEN: []const u8 = "\x1b[1;32m";
    /// Bold yellow foreground (`\x1b[1;33m`).
    pub const BOLD_YELLOW: []const u8 = "\x1b[1;33m";
    /// Bold blue foreground (`\x1b[1;34m`).
    pub const BOLD_BLUE: []const u8 = "\x1b[1;34m";
    /// Bold cyan foreground (`\x1b[1;36m`).
    pub const BOLD_CYAN: []const u8 = "\x1b[1;36m";
};

// ------------------------------------- PUBLIC API --------------------------------------

/// Determines whether ANSI color sequences should be emitted for `mode`, `file`, and `environ_map`.
pub fn isColorEnabled(
    mode: ColorMode,
    io: std.Io,
    file: std.Io.File,
    environ_map: ?*const std.process.Environ.Map,
) bool {
    switch (mode) {
        .never => return false,
        .always => return true,
        .auto => {
            if (environ_map) |env_map| {
                if (env_map.get("NO_COLOR")) |no_color_val| {
                    if (no_color_val.len > 0) return false;
                }
                if (env_map.get("TERM")) |term_val| {
                    if (std.mem.eql(u8, term_val, "dumb")) return false;
                }
            }
            if (file.supportsAnsiEscapeCodes(io) catch false) return true;
            if (file.isTty(io) catch false) {
                file.enableAnsiEscapeCodes(io) catch {};
                return file.supportsAnsiEscapeCodes(io) catch false;
            }
            return false;
        },
    }
}

/// Alias for `isColorEnabled` matching specification terminology.
pub const resolveColorEnabled = isColorEnabled;

/// Returns `true` if `codepoint` is a banned colored emoji or emoji variation selector (`U+FE0F`).
pub fn isBannedEmojiCodepoint(codepoint: u21) bool {
    // Check Variation Selector-16 (`U+FE0F`, colored emoji presentation) and dingbat colored emojis:
    if (codepoint == 0xFE0F or codepoint == 0x2705 or codepoint == 0x274C or codepoint == 0x274E) {
        return true;
    }
    // Check supplemental pictographic and colored emoji blocks (`U+1F300`–`U+1FAF8`):
    if (codepoint >= 0x1F300 and codepoint <= 0x1FAF8) {
        return true;
    }
    // Check miscellaneous colored symbols (`U+2614`, `U+2615`, `U+26A1`, `U+26D4`, `U+2728`):
    if (codepoint == 0x2614 or codepoint == 0x2615 or codepoint == 0x26A1 or codepoint == 0x26D4 or codepoint == 0x2728) {
        return true;
    }
    return false;
}

/// Scans a UTF-8 slice and returns `true` if any banned colored emoji sequence is present.
pub fn hasBannedEmoji(text: []const u8) bool {
    var byte_index: usize = 0;
    while (byte_index < text.len) {
        const seq_len = std.unicode.utf8ByteSequenceLength(text[byte_index]) catch {
            byte_index += 1;
            continue;
        };
        if (byte_index + seq_len > text.len) break;
        const codepoint = std.unicode.utf8Decode(text[byte_index .. byte_index + seq_len]) catch {
            byte_index += 1;
            continue;
        };
        if (isBannedEmojiCodepoint(codepoint)) return true;
        byte_index += seq_len;
    }
    return false;
}

/// Measures the visible terminal column width of `text`, ignoring ANSI CSI sequences and zero-width selectors.
pub fn measureVisibleWidth(text: []const u8) usize {
    var visible_cols: usize = 0;
    var byte_index: usize = 0;
    while (byte_index < text.len) {
        // [1] Skip ANSI CSI escape sequences (`\x1b[…<final_byte>`):
        if (text[byte_index] == 0x1B and byte_index + 1 < text.len and text[byte_index + 1] == '[') {
            byte_index += 2;
            while (byte_index < text.len) : (byte_index += 1) {
                const csi_byte = text[byte_index];
                if (csi_byte >= 0x40 and csi_byte <= 0x7E) {
                    byte_index += 1;
                    break;
                }
            }
            continue;
        }
        // [2] Decode UTF-8 codepoint and advance visible width for non-variation-selector glyphs:
        const seq_len = std.unicode.utf8ByteSequenceLength(text[byte_index]) catch {
            visible_cols += 1;
            byte_index += 1;
            continue;
        };
        if (byte_index + seq_len > text.len) {
            visible_cols += 1;
            break;
        }
        const codepoint = std.unicode.utf8Decode(text[byte_index .. byte_index + seq_len]) catch {
            visible_cols += 1;
            byte_index += 1;
            continue;
        };
        if (codepoint != 0xFE0E and codepoint != 0xFE0F and codepoint != 0x200B) {
            visible_cols += 1;
        }
        byte_index += seq_len;
    }
    return visible_cols;
}

comptime {
    // Statically verify that no glyph in `Glyphs` contains a banned colored emoji:
    @setEvalBranchQuota(10_000);
    std.debug.assert(!hasBannedEmoji(Glyphs.TOP_LEFT));
    std.debug.assert(!hasBannedEmoji(Glyphs.TOP_RIGHT));
    std.debug.assert(!hasBannedEmoji(Glyphs.BOTTOM_LEFT));
    std.debug.assert(!hasBannedEmoji(Glyphs.BOTTOM_RIGHT));
    std.debug.assert(!hasBannedEmoji(Glyphs.HORIZONTAL));
    std.debug.assert(!hasBannedEmoji(Glyphs.VERTICAL));
    std.debug.assert(!hasBannedEmoji(Glyphs.POINTER_SOLID));
    std.debug.assert(!hasBannedEmoji(Glyphs.BULLET));
    std.debug.assert(!hasBannedEmoji(Glyphs.SUCCESS));
    std.debug.assert(!hasBannedEmoji(Glyphs.FAILURE));
    std.debug.assert(!hasBannedEmoji(Glyphs.WARNING));
}

test "test_style_glyphs_contain_zero_colored_emojis" {
    try std.testing.expect(!hasBannedEmoji(Glyphs.SUCCESS));
    try std.testing.expect(!hasBannedEmoji(Glyphs.FAILURE));
    try std.testing.expect(!hasBannedEmoji(Glyphs.WARNING));
    try std.testing.expectEqual(@as(usize, 1), measureVisibleWidth(Glyphs.WARNING));
    try std.testing.expect(hasBannedEmoji("\u{1F680}"));
    try std.testing.expect(hasBannedEmoji("\u{2705}"));
    try std.testing.expect(hasBannedEmoji("\u{274C}"));
    try std.testing.expect(hasBannedEmoji("\u{26A0}\u{FE0F}"));
}

test "test_style_measure_visible_width_strips_ansi" {
    var buffer: [128]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buffer);
    try StyleConfig.COLORED.writeStyled(&writer, .err, "✗ error[E0302]");
    const rendered = writer.buffered();
    try std.testing.expect(rendered.len > "✗ error[E0302]".len);
    try std.testing.expectEqual(@as(usize, 14), measureVisibleWidth(rendered));
}

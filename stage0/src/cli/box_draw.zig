//! CLI Monochrome Box-Drawing & Table Layout Engine
//!
//! Provides `CardRenderer`, `TableRenderer`, and high-resolution 1/8th-block progress bar primitives
//! built over the monochrome Unicode glyph vocabulary in `style.zig`.
//!
//! All column and card width calculations operate on visible Unicode codepoint counts with ANSI CSI
//! sequences stripped, guaranteeing aligned box borders whether colors are enabled or disabled.

const std = @import("std");
const style = @import("style.zig");

const Glyphs = style.Glyphs;
const StyleConfig = style.StyleConfig;

// ---------------------------------------- TYPES ----------------------------------------

/// Horizontal alignment mode for cells within a `TableRenderer` column.
pub const ColumnAlign = enum(u8) {
    /// Left-align cell text and pad trailing spaces on the right.
    left = 0,
    /// Right-align cell text and pad leading spaces on the left.
    right = 1,
};

/// Alias for `ColumnAlign` used by table layout callers.
pub const Alignment = ColumnAlign;

/// Column descriptor specifying header text and cell alignment for `TableRenderer`.
pub const TableColumn = struct {
    /// Header label rendered in the top table row.
    header: []const u8,
    /// Horizontal alignment applied to data cells in this column.
    alignment: ColumnAlign = .left,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum number of columns supported in a fixed stack-allocated `TableRenderer` layout.
pub const MAX_TABLE_COLUMNS: usize = 16;

// -------------------------------------- INTERNALS --------------------------------------

/// Writes a horizontal table border rule using `left_corner`, `junction`, and `right_corner`.
fn writeHorizontalBorder(
    style_config: StyleConfig,
    writer: *std.Io.Writer,
    col_widths: []const usize,
    left_corner: []const u8,
    junction: []const u8,
    right_corner: []const u8,
) std.Io.Writer.Error!void {
    try style_config.writeStyled(writer, .dim, left_corner);
    for (col_widths, 0..) |col_width, i| {
        if (i > 0) {
            try style_config.writeStyled(writer, .dim, junction);
        }
        try style_config.writeRepeated(writer, .dim, Glyphs.HORIZONTAL, col_width + 2);
    }
    try style_config.writeStyled(writer, .dim, right_corner);
    try writer.writeByte('\n');
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Rounded monochrome Unicode card renderer (`╭─ Title ─╮` … `╰─────────╯`).
pub const CardRenderer = struct {
    /// Active terminal styling configuration.
    style_config: StyleConfig = StyleConfig.MONOCHROME,

    /// Initializes a `CardRenderer` with the given `style_config`.
    pub fn init(style_config: StyleConfig) CardRenderer {
        return .{ .style_config = style_config };
    }

    /// Renders a rounded card with an optional `title` and body `lines` into `writer`.
    pub fn renderCard(
        self: CardRenderer,
        writer: *std.Io.Writer,
        title: []const u8,
        lines: []const []const u8,
    ) std.Io.Writer.Error!void {
        // [1] Compute the maximum visible inner width across title and body lines:
        const title_width = style.measureVisibleWidth(title);
        var inner_width: usize = if (title_width > 0) title_width + 2 else 0;
        for (lines) |line_text| {
            const line_width = style.measureVisibleWidth(line_text);
            if (line_width > inner_width) {
                inner_width = line_width;
            }
        }

        // [2] Emit top rounded border (`╭─ Title ───╮` or `╭───────────╮`):
        try self.style_config.writeStyled(writer, .dim, Glyphs.TOP_LEFT);
        try self.style_config.writeStyled(writer, .dim, Glyphs.HORIZONTAL);
        if (title_width > 0) {
            try writer.writeByte(' ');
            try self.style_config.writeStyled(writer, .bold, title);
            try writer.writeByte(' ');
            try self.style_config.writeRepeated(
                writer,
                .dim,
                Glyphs.HORIZONTAL,
                (inner_width -| (title_width + 2)) + 1,
            );
        } else {
            try self.style_config.writeRepeated(writer, .dim, Glyphs.HORIZONTAL, inner_width + 1);
        }
        try self.style_config.writeStyled(writer, .dim, Glyphs.TOP_RIGHT);
        try writer.writeByte('\n');

        // [3] Emit padded content rows (`│ line_text   │`):
        for (lines) |line_text| {
            try self.style_config.writeStyled(writer, .dim, Glyphs.VERTICAL);
            try writer.writeByte(' ');
            try writer.writeAll(line_text);
            try writer.splatByteAll(' ', (inner_width -| style.measureVisibleWidth(line_text)) + 1);
            try self.style_config.writeStyled(writer, .dim, Glyphs.VERTICAL);
            try writer.writeByte('\n');
        }

        // [4] Emit bottom rounded border (`╰───────────╯`):
        try self.style_config.writeStyled(writer, .dim, Glyphs.BOTTOM_LEFT);
        try self.style_config.writeRepeated(writer, .dim, Glyphs.HORIZONTAL, inner_width + 2);
        try self.style_config.writeStyled(writer, .dim, Glyphs.BOTTOM_RIGHT);
        try writer.writeByte('\n');
    }
};

/// Multi-column monochrome Unicode table renderer (`╭─┬─╮`, `├─┼─┤`, `╰─┴─╯`).
pub const TableRenderer = struct {
    /// Active terminal styling configuration.
    style_config: StyleConfig = StyleConfig.MONOCHROME,

    /// Initializes a `TableRenderer` with the given `style_config`.
    pub fn init(style_config: StyleConfig) TableRenderer {
        return .{ .style_config = style_config };
    }

    /// Renders an aligned table with `columns` and `rows` into `writer`.
    pub fn renderTable(
        self: TableRenderer,
        writer: *std.Io.Writer,
        columns: []const TableColumn,
        rows: []const []const []const u8,
    ) std.Io.Writer.Error!void {
        if (columns.len == 0 or columns.len > MAX_TABLE_COLUMNS) return;

        // [1] Pre-pass to measure maximum visible width per column:
        var col_widths: [MAX_TABLE_COLUMNS]usize = @splat(0);
        for (columns, 0..) |column_spec, i| {
            col_widths[i] = style.measureVisibleWidth(column_spec.header);
        }
        for (rows) |row_cells| {
            for (row_cells[0..@min(row_cells.len, columns.len)], 0..) |cell_text, i| {
                const cell_width = style.measureVisibleWidth(cell_text);
                if (cell_width > col_widths[i]) {
                    col_widths[i] = cell_width;
                }
            }
        }

        // [2] Emit top border (`╭───┬───╮`):
        try writeHorizontalBorder(
            self.style_config,
            writer,
            col_widths[0..columns.len],
            Glyphs.TOP_LEFT,
            Glyphs.T_DOWN,
            Glyphs.TOP_RIGHT,
        );

        // [3] Emit header row (`│ Col1 │ Col2 │`):
        try self.style_config.writeStyled(writer, .dim, Glyphs.VERTICAL);
        for (columns, 0..) |column_spec, i| {
            const pad_spaces = col_widths[i] -| style.measureVisibleWidth(column_spec.header);
            try writer.writeByte(' ');
            if (column_spec.alignment == .right) {
                try writer.splatByteAll(' ', pad_spaces);
                try self.style_config.writeStyled(writer, .bold, column_spec.header);
            } else {
                try self.style_config.writeStyled(writer, .bold, column_spec.header);
                try writer.splatByteAll(' ', pad_spaces);
            }
            try writer.writeByte(' ');
            try self.style_config.writeStyled(writer, .dim, Glyphs.VERTICAL);
        }
        try writer.writeByte('\n');

        // [4] Emit header separator (`├───┼───┤`):
        try writeHorizontalBorder(
            self.style_config,
            writer,
            col_widths[0..columns.len],
            Glyphs.T_RIGHT,
            Glyphs.CROSS,
            Glyphs.T_LEFT,
        );

        // [5] Emit data rows (`│ val1 │ val2 │`):
        for (rows) |row_cells| {
            try self.style_config.writeStyled(writer, .dim, Glyphs.VERTICAL);
            for (columns, 0..) |column_spec, i| {
                const cell_text = if (i < row_cells.len) row_cells[i] else "";
                const pad_spaces = col_widths[i] -| style.measureVisibleWidth(cell_text);
                try writer.writeByte(' ');
                if (column_spec.alignment == .right) {
                    try writer.splatByteAll(' ', pad_spaces);
                    try writer.writeAll(cell_text);
                } else {
                    try writer.writeAll(cell_text);
                    try writer.splatByteAll(' ', pad_spaces);
                }
                try writer.writeByte(' ');
                try self.style_config.writeStyled(writer, .dim, Glyphs.VERTICAL);
            }
            try writer.writeByte('\n');
        }

        // [6] Emit bottom border (`╰───┴───╯`):
        try writeHorizontalBorder(
            self.style_config,
            writer,
            col_widths[0..columns.len],
            Glyphs.BOTTOM_LEFT,
            Glyphs.T_UP,
            Glyphs.BOTTOM_RIGHT,
        );
    }
};

/// Renders a high-resolution 1/8th-cell monochrome progress bar of `width_cells` columns for `ratio` in `[0.0, 1.0]`.
pub fn renderProgressBar(
    style_config: StyleConfig,
    writer: *std.Io.Writer,
    width_cells: usize,
    ratio: f64,
) std.Io.Writer.Error!void {
    if (width_cells == 0) return;
    const total_eighths: usize = @intFromFloat(
        @round(@max(0.0, @min(1.0, ratio)) * @as(f64, @floatFromInt(width_cells * 8))),
    );
    const full_cells = total_eighths / 8;
    const remainder_eighths = total_eighths % 8;

    try style_config.writeRepeated(writer, .bold, Glyphs.BLOCKS_EIGHTH[7], full_cells);
    var used_cells = full_cells;
    if (remainder_eighths > 0 and used_cells < width_cells) {
        try style_config.writeStyled(writer, .bold, Glyphs.BLOCKS_EIGHTH[remainder_eighths - 1]);
        used_cells += 1;
    }
    if (used_cells < width_cells) {
        try writer.splatByteAll(' ', width_cells - used_cells);
    }
}

test "test_box_draw_card_and_table_alignment" {
    var buffer: [1024]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buffer);

    try CardRenderer.init(StyleConfig.MONOCHROME).renderCard(
        &writer,
        "CoreX Status",
        &.{ "Phase 0 ready", "All arenas verified" },
    );
    const card_out = writer.buffered();
    try std.testing.expect(std.mem.indexOf(u8, card_out, "╭─ CoreX Status ") != null);
    try std.testing.expect(std.mem.indexOf(u8, card_out, "│ All arenas verified │") != null);

    var table_buf: [1024]u8 = undefined;
    var table_writer = std.Io.Writer.fixed(&table_buf);
    const columns = [_]TableColumn{
        .{ .header = "Name", .alignment = .left },
        .{ .header = "Time", .alignment = .right },
    };
    try TableRenderer.init(StyleConfig.MONOCHROME).renderTable(
        &table_writer,
        &columns,
        &.{&.{ "BumpArena", "12ns" }},
    );
    try std.testing.expect(std.mem.indexOf(u8, table_writer.buffered(), "│ BumpArena │ 12ns │") != null);
}

//! Monochrome Unicode & ANSI Diagnostic Snippet Renderer
//!
//! Renders single-line, multi-line, and cross-file compiler diagnostics with gutter-aligned line numbers,
//! primary (`^`) and secondary (`─`) span underlines, inline `SuggestedFix` diff previews, and help notes.
//!
//! Implements the exact visual specification defined in `.agents/skills/docs/SKILL.md` Section 4 and
//! `DR-15` Section 2.1.2, normalizing file path separators to `/` for cross-platform snapshot parity.

const std = @import("std");
const mem = @import("../mem_foundation.zig");
const vfs = @import("../vfs_sourcemap.zig");
const style = @import("../cli/style.zig");
const diag = @import("diagnostic.zig");

const FileId = mem.FileId;
const Span = mem.Span;
const StringInterner = mem.StringInterner;
const LineCol = vfs.LineCol;
const LineIndex = vfs.LineIndex;
const VfsSourceMap = vfs.VfsSourceMap;
const Glyphs = style.Glyphs;
const StyleConfig = style.StyleConfig;
const StyleRole = style.StyleRole;
const Diagnostic = diag.Diagnostic;
const DiagnosticSink = diag.DiagnosticSink;
const LabeledSpan = diag.LabeledSpan;
const LabelStyle = diag.LabelStyle;
const SuggestedFix = diag.SuggestedFix;
const TextEdit = diag.TextEdit;

// ---------------------------------------- TYPES ----------------------------------------

/// Internal resolved span pairing a `LabeledSpan` with its 1-based start and end `LineCol`.
const ResolvedLabel = struct {
    /// Original byte span.
    span: Span,
    /// Label message text.
    label: []const u8,
    /// Primary or secondary underline style.
    style: LabelStyle,
    /// Resolved 1-based start line and column.
    start_loc: LineCol,
    /// Resolved 1-based end line and column.
    end_loc: LineCol,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum number of labeled spans rendered per diagnostic to bound stack usage.
pub const MAX_RENDERED_LABELS: usize = 32;

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `labels` already contains a `.primary` entry matching `primary_span`.
fn hasExplicitPrimaryLabel(labels: []const LabeledSpan, primary_span: Span) bool {
    for (labels) |label_item| {
        if (label_item.style == .primary and
            label_item.span.file_id == primary_span.file_id and
            label_item.span.start_byte == primary_span.start_byte and
            label_item.span.end_byte == primary_span.end_byte)
        {
            return true;
        }
    }
    return false;
}

/// Returns `true` if `file_slice` contains `target_id`.
fn hasFileId(file_slice: []const FileId, target_id: FileId) bool {
    for (file_slice) |existing_id| {
        if (existing_id == target_id) return true;
    }
    return false;
}

/// Comparator sorting `ResolvedLabel` items by `(start_loc.line ASC, start_loc.col_utf8 ASC)`.
fn compareResolvedLabels(_: void, first_label: ResolvedLabel, second_label: ResolvedLabel) bool {
    if (first_label.start_loc.line != second_label.start_loc.line) {
        return first_label.start_loc.line < second_label.start_loc.line;
    }
    return first_label.start_loc.col_utf8 < second_label.start_loc.col_utf8;
}

/// Counts base-10 digits in a positive integer `value`.
fn countDigitsBase10(value: u32) usize {
    var remaining = value;
    var digits: usize = 1;
    while (remaining >= 10) : (remaining /= 10) {
        digits += 1;
    }
    return digits;
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Terminal diagnostic renderer backed by `VfsSourceMap` and `StringInterner`.
pub const DiagnosticRenderer = struct {
    /// Virtual file system and source map providing file buffers and lazy `LineIndex` tables.
    source_map: *VfsSourceMap,
    /// String interner resolving `TextEdit.replacement_id` handles in diff previews.
    interner: *const StringInterner,
    /// Active terminal styling configuration (`MONOCHROME` or `COLORED`).
    style_config: StyleConfig = StyleConfig.MONOCHROME,

    /// Initializes a `DiagnosticRenderer` bound to `source_map`, `interner`, and `style_config`.
    pub fn init(
        source_map: *VfsSourceMap,
        interner: *const StringInterner,
        style_config: StyleConfig,
    ) DiagnosticRenderer {
        return .{
            .source_map = source_map,
            .interner = interner,
            .style_config = style_config,
        };
    }

    /// Renders a single `Diagnostic` (header, source snippets, diff previews, and notes) into `writer`.
    pub fn renderDiagnostic(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        diagnostic: Diagnostic,
    ) !void {
        // [1] Emit diagnostic headline (`✗ error[E0302]: <message>`):
        try self.writeHeaderLine(writer, diagnostic);

        // [2] Collect and resolve all source spans attached to the diagnostic:
        var resolved_labels: [MAX_RENDERED_LABELS]ResolvedLabel = undefined;
        var resolved_count: usize = 0;

        const has_primary_file = self.source_map.getFileEntry(diagnostic.primary_span.file_id) != null;
        if (has_primary_file and !hasExplicitPrimaryLabel(diagnostic.labels, diagnostic.primary_span)) {
            if (try self.resolveSpan(diagnostic.primary_span, "", .primary)) |primary_resolved| {
                resolved_labels[resolved_count] = primary_resolved;
                resolved_count += 1;
            }
        }
        for (diagnostic.labels) |label_item| {
            if (resolved_count >= MAX_RENDERED_LABELS) break;
            if (try self.resolveSpan(label_item.span, label_item.label, label_item.style)) |resolved_item| {
                resolved_labels[resolved_count] = resolved_item;
                resolved_count += 1;
            }
        }

        // [3] Handle file-less CLI/global diagnostics by emitting footer notes directly:
        if (resolved_count == 0) {
            try self.renderStandaloneNotes(writer, 2, diagnostic.suggestions, diagnostic.notes);
            return;
        }

        // [4] Compute gutter digit width across all resolved spans and diff edits:
        var max_line_num: u32 = 1;
        for (resolved_labels[0..resolved_count]) |resolved_item| {
            if (resolved_item.end_loc.line > max_line_num) {
                max_line_num = resolved_item.end_loc.line;
            }
        }
        for (diagnostic.suggestions) |fix_item| {
            for (fix_item.edits) |edit_item| {
                if (try self.resolveEditLine(edit_item)) |edit_line| {
                    if (edit_line > max_line_num) {
                        max_line_num = edit_line;
                    }
                }
            }
        }
        const gutter_width = countDigitsBase10(max_line_num);

        // [5] Determine primary file and header coordinates:
        const primary_file_id = if (has_primary_file)
            diagnostic.primary_span.file_id
        else
            resolved_labels[0].span.file_id;
        const primary_header_loc = try self.resolveHeaderLocation(
            primary_file_id,
            diagnostic.primary_span,
            resolved_labels[0..resolved_count],
        );

        // [6] Render primary file location header (`╭─▸ path/file.cx:line:col`) and spans:
        try writer.splatByteAll(' ', gutter_width + 1);
        try self.style_config.writeStyled(writer, .dim, "╭─▸ ");
        try self.writeNormalizedFileLocation(
            writer,
            self.source_map.getFilePath(primary_file_id),
            primary_header_loc.line,
            primary_header_loc.col_utf8,
        );
        try writer.writeByte('\n');

        try self.renderFileSpans(
            writer,
            primary_file_id,
            gutter_width,
            diagnostic.severity.asStyleRole(),
            resolved_labels[0..resolved_count],
        );

        // [7] Render stitched cross-file secondary snippet blocks (`├─▸ other/file.cx:line:col`):
        var seen_files: [MAX_RENDERED_LABELS]FileId = undefined;
        var seen_file_count: usize = 1;
        seen_files[0] = primary_file_id;

        for (resolved_labels[0..resolved_count]) |resolved_item| {
            const candidate_file_id = resolved_item.span.file_id;
            if (hasFileId(seen_files[0..seen_file_count], candidate_file_id)) continue;
            seen_files[seen_file_count] = candidate_file_id;
            seen_file_count += 1;

            try self.writeGutterBarLine(writer, gutter_width);
            try writer.splatByteAll(' ', gutter_width + 1);
            try self.style_config.writeStyled(writer, .dim, "├─▸ ");
            try self.writeNormalizedFileLocation(
                writer,
                self.source_map.getFilePath(candidate_file_id),
                resolved_item.start_loc.line,
                resolved_item.start_loc.col_utf8,
            );
            try writer.writeByte('\n');

            try self.renderFileSpans(
                writer,
                candidate_file_id,
                gutter_width,
                diagnostic.severity.asStyleRole(),
                resolved_labels[0..resolved_count],
            );
        }

        // [8] Render trailing gutter bar, inline `SuggestedFix` diffs, and `help:`/`note:` footers:
        try self.writeGutterBarLine(writer, gutter_width);
        try self.renderBoxFooter(writer, gutter_width, diagnostic.suggestions, diagnostic.notes);
    }

    /// Renders all diagnostics in `sink`, appending the error-limit summary notice if capped.
    pub fn renderAll(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        sink: *const DiagnosticSink,
    ) !void {
        for (sink.asSlice(), 0..) |diagnostic, i| {
            if (i > 0) {
                try writer.writeByte('\n');
            }
            try self.renderDiagnostic(writer, diagnostic);
        }
        if (sink.has_reached_limit) {
            if (sink.countDiagnostics() > 0) {
                try writer.writeByte('\n');
            }
            try self.style_config.writeStyled(writer, .warning, "warning");
            try writer.print(
                ": aborting due to {d} previous errors (maximum error limit reached)\n",
                .{sink.max_errors},
            );
        }
    }

    // Internal rendering helpers:

    /// Writes the top-level `<glyph> <severity>[<code>]: <message>` line.
    fn writeHeaderLine(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        diagnostic: Diagnostic,
    ) std.Io.Writer.Error!void {
        if (self.style_config.is_color_enabled) {
            try writer.writeAll(diagnostic.severity.asStyleRole().asAnsiPrefix());
            try writer.writeAll(diagnostic.severity.asStatusGlyph());
            try writer.writeByte(' ');
            try writer.writeAll(diagnostic.severity.asLabel());
            try writer.writeByte('[');
            try writer.writeAll(diagnostic.code.asCodeStr());
            try writer.writeByte(']');
            try writer.writeAll(style.Sgr.RESET);
            try writer.writeAll(style.Sgr.BOLD);
            try writer.writeAll(": ");
            try writer.writeAll(diagnostic.message);
            try writer.writeAll(style.Sgr.RESET);
            try writer.writeByte('\n');
        } else {
            try writer.print("{s} {s}[{s}]: {s}\n", .{
                diagnostic.severity.asStatusGlyph(),
                diagnostic.severity.asLabel(),
                diagnostic.code.asCodeStr(),
                diagnostic.message,
            });
        }
    }

    /// Resolves a `Span` into 1-based `start_loc` and `end_loc` coordinates.
    fn resolveSpan(
        self: DiagnosticRenderer,
        span: Span,
        label_text: []const u8,
        label_style: LabelStyle,
    ) !?ResolvedLabel {
        if (span.file_id.isNone()) return null;
        const source = self.source_map.getFileSource(span.file_id) orelse return null;
        const line_index = try self.source_map.getLineIndex(span.file_id);
        return .{
            .span = span,
            .label = label_text,
            .style = label_style,
            .start_loc = line_index.resolveLineCol(source, span.start_byte),
            .end_loc = line_index.resolveLineCol(source, span.end_byte),
        };
    }

    /// Resolves the 1-based line number of a `TextEdit` for gutter width calculation.
    fn resolveEditLine(self: DiagnosticRenderer, edit_item: TextEdit) !?u32 {
        if (edit_item.file_id.isNone()) return null;
        return (try self.source_map.getLineIndex(edit_item.file_id)).resolveLineCol(
            self.source_map.getFileSource(edit_item.file_id) orelse return null,
            edit_item.start_byte,
        ).line;
    }

    /// Resolves the header `LineCol` for `primary_file_id` from `primary_span` or the first label.
    fn resolveHeaderLocation(
        self: DiagnosticRenderer,
        primary_file_id: FileId,
        primary_span: Span,
        resolved_labels: []const ResolvedLabel,
    ) !LineCol {
        if (primary_span.file_id == primary_file_id) {
            if (self.source_map.getFileSource(primary_file_id)) |source| {
                return (try self.source_map.getLineIndex(primary_file_id)).resolveLineCol(source, primary_span.start_byte);
            }
        }
        return resolved_labels[0].start_loc;
    }

    /// Writes `file_path:line:col` normalizing Windows `\` separators to `/`.
    fn writeNormalizedFileLocation(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        file_path: []const u8,
        line_num: u32,
        col_num: u32,
    ) std.Io.Writer.Error!void {
        _ = self;
        for (file_path) |path_byte| {
            try writer.writeByte(if (path_byte == '\\') '/' else path_byte);
        }
        try writer.print(":{d}:{d}", .{ line_num, col_num });
    }

    /// Renders all sorted spans belonging to `target_file_id` with context lines and gap elision.
    fn renderFileSpans(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        target_file_id: FileId,
        gutter_width: usize,
        primary_role: StyleRole,
        all_labels: []const ResolvedLabel,
    ) !void {
        const source = self.source_map.getFileSource(target_file_id) orelse return;
        const line_index = try self.source_map.getLineIndex(target_file_id);

        // [1] Filter and sort spans targeting `target_file_id` by `(start_line ASC, start_col ASC)`:
        var file_labels: [MAX_RENDERED_LABELS]ResolvedLabel = undefined;
        var file_label_count: usize = 0;
        for (all_labels) |resolved_item| {
            if (resolved_item.span.file_id == target_file_id) {
                file_labels[file_label_count] = resolved_item;
                file_label_count += 1;
            }
        }
        std.mem.sort(ResolvedLabel, file_labels[0..file_label_count], {}, compareResolvedLabels);

        try self.writeGutterBarLine(writer, gutter_width);

        // [2] Render each span in line order, inserting context lines or `┆` gap markers:
        var last_rendered_line: u32 = 0;
        for (file_labels[0..file_label_count]) |label_item| {
            const start_line = label_item.start_loc.line;
            const end_line = label_item.end_loc.line;

            if (last_rendered_line > 0 and start_line > last_rendered_line + 1) {
                if (start_line <= last_rendered_line + 3) {
                    var ctx_line = last_rendered_line + 1;
                    while (ctx_line < start_line) : (ctx_line += 1) {
                        try self.writeSourceLine(writer, gutter_width, ctx_line, null, line_index.getLineSlice(source, ctx_line));
                    }
                } else {
                    try writer.splatByteAll(' ', gutter_width + 1);
                    try self.style_config.writeStyled(writer, .dim, Glyphs.DOTTED_VERTICAL);
                    try writer.writeByte('\n');
                }
            }

            const underline_role: StyleRole = if (label_item.style == .primary) primary_role else .note;
            const underline_glyph = if (label_item.style == .primary) Glyphs.CARET else Glyphs.HORIZONTAL;

            if (start_line == end_line) {
                if (start_line != last_rendered_line) {
                    try self.writeSourceLine(writer, gutter_width, start_line, null, line_index.getLineSlice(source, start_line));
                    last_rendered_line = start_line;
                }
                try writer.splatByteAll(' ', gutter_width + 1);
                try self.style_config.writeStyled(writer, .dim, Glyphs.VERTICAL);
                try writer.splatByteAll(' ', (label_item.start_loc.col_utf8 -| 1) + 1);
                try self.style_config.writeRepeated(
                    writer,
                    underline_role,
                    underline_glyph,
                    @max(@as(usize, 1), label_item.end_loc.col_utf8 -| label_item.start_loc.col_utf8),
                );
                if (label_item.label.len > 0) {
                    try writer.writeByte(' ');
                    try self.style_config.writeStyled(writer, underline_role, label_item.label);
                }
                try writer.writeByte('\n');
            } else {
                // Multi-line span with left-gutter vertical connector (`╭─▸` … `│` … `╰─^`):
                try self.writeSourceLine(writer, gutter_width, start_line, "╭─▸ ", line_index.getLineSlice(source, start_line));
                if (end_line > start_line + 1) {
                    if (end_line - start_line <= 5) {
                        var mid_line = start_line + 1;
                        while (mid_line < end_line) : (mid_line += 1) {
                            try self.writeSourceLine(writer, gutter_width, mid_line, "│   ", line_index.getLineSlice(source, mid_line));
                        }
                    } else {
                        try self.writeSourceLine(writer, gutter_width, start_line + 1, "│   ", line_index.getLineSlice(source, start_line + 1));
                        try writer.splatByteAll(' ', gutter_width + 1);
                        try self.style_config.writeStyled(writer, .dim, Glyphs.DOTTED_VERTICAL);
                        try writer.writeByte(' ');
                        try self.style_config.writeStyled(writer, .dim, Glyphs.DOTTED_VERTICAL);
                        try writer.writeByte('\n');
                        try self.writeSourceLine(writer, gutter_width, end_line - 1, "│   ", line_index.getLineSlice(source, end_line - 1));
                    }
                }
                try self.writeSourceLine(writer, gutter_width, end_line, "│   ", line_index.getLineSlice(source, end_line));

                try writer.splatByteAll(' ', gutter_width + 1);
                try self.style_config.writeStyled(writer, .dim, Glyphs.VERTICAL);
                try writer.writeByte(' ');
                try self.style_config.writeStyled(writer, underline_role, "╰─");
                try self.style_config.writeRepeated(
                    writer,
                    underline_role,
                    Glyphs.HORIZONTAL,
                    @max(@as(usize, 1), label_item.end_loc.col_utf8 -| 1) + 1,
                );
                try self.style_config.writeStyled(writer, underline_role, underline_glyph);
                if (label_item.label.len > 0) {
                    try writer.writeByte(' ');
                    try self.style_config.writeStyled(writer, underline_role, label_item.label);
                }
                try writer.writeByte('\n');
                last_rendered_line = end_line;
            }
        }
    }

    /// Writes a numbered source line (`40 │     let packet = …`).
    fn writeSourceLine(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        gutter_width: usize,
        line_num: u32,
        multiline_prefix: ?[]const u8,
        line_text: []const u8,
    ) std.Io.Writer.Error!void {
        const line_digits = countDigitsBase10(line_num);
        if (gutter_width > line_digits) {
            try writer.splatByteAll(' ', gutter_width - line_digits);
        }
        var num_buf: [16]u8 = undefined;
        var num_writer = std.Io.Writer.fixed(&num_buf);
        num_writer.print("{d}", .{line_num}) catch unreachable;
        try self.style_config.writeStyled(writer, .dim, num_writer.buffered());
        try writer.writeByte(' ');
        try self.style_config.writeStyled(writer, .dim, Glyphs.VERTICAL);
        try writer.writeByte(' ');
        if (multiline_prefix) |prefix_str| {
            try self.style_config.writeStyled(writer, .dim, prefix_str);
        }
        try writer.writeAll(line_text);
        try writer.writeByte('\n');
    }

    /// Writes an empty vertical gutter connector line (`  │\n`).
    fn writeGutterBarLine(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        gutter_width: usize,
    ) std.Io.Writer.Error!void {
        try writer.splatByteAll(' ', gutter_width + 1);
        try self.style_config.writeStyled(writer, .dim, Glyphs.VERTICAL);
        try writer.writeByte('\n');
    }

    /// Renders `SuggestedFix` diff previews and `notes` at the bottom of a file snippet box.
    fn renderBoxFooter(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        gutter_width: usize,
        suggestions: []const SuggestedFix,
        notes: []const []const u8,
    ) !void {
        if (suggestions.len == 0 and notes.len == 0) {
            try writer.splatByteAll(' ', gutter_width + 1);
            try self.style_config.writeStyled(writer, .dim, "╰───────");
            try writer.writeByte('\n');
            return;
        }

        var has_open_diff_box = false;
        for (suggestions, 0..) |fix_item, i| {
            if (fix_item.edits.len > 0) {
                try writer.splatByteAll(' ', gutter_width + 1);
                try self.style_config.writeStyled(writer, .dim, "├╴ ");
                try self.style_config.writeStyled(writer, .help, "help");
                try writer.print(": {s}\n", .{fix_item.message});
                for (fix_item.edits) |edit_item| {
                    try self.renderEditDiffLines(writer, gutter_width, edit_item);
                }
                has_open_diff_box = true;
            } else {
                try writer.splatByteAll(' ', gutter_width + 1);
                try self.style_config.writeStyled(
                    writer,
                    .dim,
                    if ((i + 1 == suggestions.len) and (notes.len == 0)) "╰─▸ " else "├─▸ ",
                );
                try self.writeFormattedNoteText(writer, fix_item.message);
                try writer.writeByte('\n');
                has_open_diff_box = false;
            }
        }

        for (notes, 0..) |note_text, i| {
            try writer.splatByteAll(' ', gutter_width + 1);
            try self.style_config.writeStyled(writer, .dim, if (i + 1 == notes.len) "╰─▸ " else "├─▸ ");
            try self.writeFormattedNoteText(writer, note_text);
            try writer.writeByte('\n');
            has_open_diff_box = false;
        }

        if (has_open_diff_box) {
            try writer.splatByteAll(' ', gutter_width + 1);
            try self.style_config.writeStyled(writer, .dim, "╰───────");
            try writer.writeByte('\n');
        }
    }

    /// Renders `-` and `+` diff preview lines for a single `TextEdit`.
    fn renderEditDiffLines(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        gutter_width: usize,
        edit_item: TextEdit,
    ) !void {
        if (edit_item.file_id.isNone() or
            edit_item.replacement_id.isNone() or
            edit_item.replacement_id.asInt() >= self.interner.countStrings() or
            edit_item.start_byte > edit_item.end_byte)
        {
            return;
        }
        const source = self.source_map.getFileSource(edit_item.file_id) orelse return;
        const line_index = try self.source_map.getLineIndex(edit_item.file_id);
        const start_loc = line_index.resolveLineCol(source, edit_item.start_byte);
        const line_bounds = line_index.getLineBounds(source, start_loc.line - 1);
        const original_line = source[line_bounds.start..line_bounds.end];

        const line_digits = countDigitsBase10(start_loc.line);
        // [1] Emit `-` removal line:
        if (gutter_width > line_digits) {
            try writer.splatByteAll(' ', gutter_width - line_digits);
        }
        try writer.print("{d} ", .{start_loc.line});
        try self.style_config.writeStyled(writer, .diff_remove, "- ");
        try self.style_config.writeStyled(writer, .diff_remove, original_line);
        try writer.writeByte('\n');

        // [2] Emit `+` addition line with spliced replacement:
        if (gutter_width > line_digits) {
            try writer.splatByteAll(' ', gutter_width - line_digits);
        }
        try writer.print("{d} ", .{start_loc.line});
        try self.style_config.writeStyled(writer, .diff_add, "+ ");
        try self.style_config.writeStyled(
            writer,
            .diff_add,
            original_line[0..@min(edit_item.start_byte -| line_bounds.start, original_line.len)],
        );
        try self.style_config.writeStyled(writer, .diff_add, self.interner.get(edit_item.replacement_id));
        try self.style_config.writeStyled(
            writer,
            .diff_add,
            original_line[@min(edit_item.end_byte -| line_bounds.start, original_line.len)..],
        );
        try writer.writeByte('\n');
    }

    /// Renders notes and suggestions when a diagnostic has no associated source file.
    fn renderStandaloneNotes(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        indent_spaces: usize,
        suggestions: []const SuggestedFix,
        notes: []const []const u8,
    ) std.Io.Writer.Error!void {
        for (suggestions, 0..) |fix_item, i| {
            try writer.splatByteAll(' ', indent_spaces);
            try self.style_config.writeStyled(
                writer,
                .dim,
                if ((i + 1 == suggestions.len) and (notes.len == 0)) "╰─▸ " else "├─▸ ",
            );
            try self.writeFormattedNoteText(writer, fix_item.message);
            try writer.writeByte('\n');
        }
        for (notes, 0..) |note_text, i| {
            try writer.splatByteAll(' ', indent_spaces);
            try self.style_config.writeStyled(writer, .dim, if (i + 1 == notes.len) "╰─▸ " else "├─▸ ");
            try self.writeFormattedNoteText(writer, note_text);
            try writer.writeByte('\n');
        }
    }

    /// Writes a `help:` or `note:` footer message, avoiding duplicate prefixes.
    fn writeFormattedNoteText(
        self: DiagnosticRenderer,
        writer: *std.Io.Writer,
        note_text: []const u8,
    ) std.Io.Writer.Error!void {
        if (std.mem.startsWith(u8, note_text, "help: ")) {
            try self.style_config.writeStyled(writer, .help, "help");
            try writer.writeAll(note_text["help".len..]);
        } else if (std.mem.startsWith(u8, note_text, "note: ")) {
            try self.style_config.writeStyled(writer, .note, "note");
            try writer.writeAll(note_text["note".len..]);
        } else {
            try self.style_config.writeStyled(writer, .help, "help");
            try writer.writeAll(": ");
            try writer.writeAll(note_text);
        }
    }
};

test "test_renderer_docs_skill_canonical_single_line_format" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    // Construct a 42-line source buffer matching `.agents/skills/docs/SKILL.md` Section 4:
    var src_buf: [2048]u8 = undefined;
    var src_writer = std.Io.Writer.fixed(&src_buf);
    var line_idx: usize = 1;
    while (line_idx < 40) : (line_idx += 1) {
        try src_writer.writeAll("// padding\n");
    }
    const line_40_start: u32 = @intCast(src_writer.buffered().len);
    try src_writer.writeAll("    let packet = consume_payload(buffer)\n");
    try src_writer.writeAll("    log_status(\"dispatched\")\n");
    const line_42_start: u32 = @intCast(src_writer.buffered().len);
    try src_writer.writeAll("    return read_header(buffer)\n");

    const file_id = try source_map.setOverlay("src/net/socket.cx", src_writer.buffered(), .root);
    const used_span = Span.init(file_id, line_42_start + 23, line_42_start + 29);

    const labels = [_]LabeledSpan{
        .{ .span = Span.init(file_id, line_40_start + 33, line_40_start + 39), .label = "value moved here", .style = .secondary },
        .{ .span = used_span, .label = "value used here after transfer", .style = .primary },
    };
    const notes = [_][]const u8{
        "help: pass a borrowed view via `buffer.as_slice()` if `consume_payload` does not retain ownership",
    };

    var out_buf: [2048]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.MONOCHROME).renderDiagnostic(&out_writer, .{
        .code = .e0302_use_after_move,
        .severity = .err,
        .primary_span = used_span,
        .message = "use of moved value `buffer` after scope transfer",
        .labels = &labels,
        .notes = &notes,
    });

    const expected =
        "✗ error[E0302]: use of moved value `buffer` after scope transfer\n" ++
        "   ╭─▸ src/net/socket.cx:42:24\n" ++
        "   │\n" ++
        "40 │     let packet = consume_payload(buffer)\n" ++
        "   │                                  ────── value moved here\n" ++
        "41 │     log_status(\"dispatched\")\n" ++
        "42 │     return read_header(buffer)\n" ++
        "   │                        ^^^^^^ value used here after transfer\n" ++
        "   │\n" ++
        "   ╰─▸ help: pass a borrowed view via `buffer.as_slice()` if `consume_payload` does not retain ownership\n";
    try std.testing.expectEqualStrings(expected, out_writer.buffered());
}

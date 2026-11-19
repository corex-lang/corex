//! CoreX Hybrid Steerable Wadler-Lindig Formatter & 8-Byte `DocArena` (`stage0/src/fmt_engine.zig`)
//!
//! Implements the deterministic, comment-preserving source formatter (`corex fmt`) and autofix pass
//! (`corex fmt --fix`) specified in `DR-03` Section 7, `DR-14` Section 1, and `DR-22` Section 3.4.
//! Lowers the lossless Concrete Syntax Tree (`LosslessCstArena`) and `TokenBuffer` into a flat array
//! of 8-byte `DocInst` document algebra instructions with $O(1)$ open-group `flat_width` backpatching.
//!
//! - **8-Byte `DocInst` & $O(1)$ Group Backpatching:** Packs every document algebra instruction into
//!   an `extern struct` of exactly 8 bytes (`DocOp` + `mode_or_delta` + `flat_width` + `payload`).
//!   `DocArena.endGroup()` backpatches `flat_width` in $O(1)$ time without recursive tree walks.
//! - **100% Comment Preservation & `line_suffix` Queue:** Pre-classifies inter-token trivia into
//!   leading comments and same-line trailing comments (`line_suffix`), handles dangling comments in
//!   empty `{}` / `()` / `[]` containers, and flushes all unconsumed comments up through `.eof`.
//! - **Steerable & `DR-22` Canonical Formatting:** Respects user trailing commas (`force_break` vs
//!   `auto_fit`), formats literal arrays with `> 8` elements in `columnar_grid`, rewrites `Option[T]`
//!   to `T?` and `Result[T, E]` to `T!E`, strips redundant `-> unit`, groups marker attributes onto
//!   one sorted line, normalizes `42_u64` suffixes and `extern "C"`, shifts `"""…"""` multiline
//!   strings by `new_indent - old_indent`, and honors `// corex fmt: off`.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");

const FileId = mem_foundation.FileId;
const TokenKind = syntax_arenas.TokenKind;
const TokenIndex = mem_foundation.TokenIndex;
const TokenBuffer = syntax_arenas.TokenBuffer;
const TriviaKind = syntax_arenas.TriviaKind;
const TriviaPiece = syntax_arenas.TriviaPiece;
const CstNodeKind = syntax_arenas.CstNodeKind;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const CstNodeRecord = syntax_arenas.CstNodeRecord;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstArena = syntax_arenas.AstArena;

// ---------------------------------------- TYPES ----------------------------------------

// ---------------- Document Algebra Primitives -----------------

/// Document algebra opcode discriminant (`1` byte inside `DocInst`, `DR-14` Section 1.2).
pub const DocOp = enum(u8) {
    /// No-operation placeholder instruction (`0`).
    nop = 0,
    /// Single-line UTF-8 text slice stored in `DocArena.string_bytes` (`1`).
    text = 1,
    /// Emits `" "` when the enclosing group renders flat, or `"\n"` + indent when broken (`2`).
    line = 2,
    /// Emits `""` when the enclosing group renders flat, or `"\n"` + indent when broken (`3`).
    soft_line = 3,
    /// Unconditional line break (`"\n"` + indent) that poisons all enclosing open groups (`4`).
    hard_line = 4,
    /// Unconditional blank line (`"\n\n"`, clamped to at most 1 blank line) that poisons groups (`5`).
    blank_line = 5,
    /// Increases current indentation level by `mode_or_delta` spaces (`6`).
    indent = 6,
    /// Decreases current indentation level by `mode_or_delta` spaces (`7`).
    dedent = 7,
    /// Begins a formatting group whose `flat_width` is backpatched by `endGroup` (`8`).
    group_begin = 8,
    /// Closes the innermost open formatting group (`9`).
    group_end = 9,
    /// Selects `break_text` when the enclosing group is broken, or `flat_text` when flat (`10`).
    if_break = 10,
    /// Queues a trailing comment to be flushed immediately before the next newline (`11`).
    line_suffix = 11,
    /// Emits a raw multi-line suppressed slice (`// corex fmt: off` … `on`) verbatim (`12`).
    verbatim_text = 12,
    /// Emits a `"""…"""` multiline string shifted by `new_indent - old_indent` (`13`, `DR-22` §3.4).
    multiline_string = 13,
};

/// Group breaking policy stored in `DocInst.mode_or_delta` on `.group_begin` (`DR-14` Section 1.2).
pub const GroupMode = enum(u8) {
    /// Renders flat if `effective_col + flat_width <= max_line_width`, otherwise breaks (`0`).
    auto_fit = 0,
    /// Unconditionally breaks across multiple lines (e.g., user trailing comma steerability) (`1`).
    force_break = 1,
    /// Formats numeric/literal arrays with `> 8` elements in aligned multi-column rows (`2`).
    columnar_grid = 2,
};

/// Exact 8-byte Wadler-Lindig document algebra instruction (`DR-14` Section 1.2).
pub const DocInst = extern struct {
    /// Document algebra opcode discriminant (`1` byte).
    op: DocOp,
    /// `GroupMode` for `.group_begin`, or indentation space delta for `.indent` / `.dedent` (`1` byte).
    mode_or_delta: u8 = 0,
    /// Pre-computed flat column width (`0xFFFF` = `INF_WIDTH` when multiline or poisoned, `2` bytes).
    flat_width: u16 = 0,
    /// Byte offset into `DocArena.string_bytes` or index into auxiliary slice tables (`4` bytes).
    payload: u32 = 0,

    comptime {
        std.debug.assert(@sizeOf(DocInst) == 8);
    }
};

/// Open group stack frame used by `DocArena` for $O(1)$ `flat_width` backpatching (`DR-14` Section 1.2).
pub const OpenGroupFrame = struct {
    /// Index of the `.group_begin` instruction in `DocArena.instructions`.
    inst_index: u32,
    /// Cumulative `DocArena.running_width` recorded when `beginGroup` was called.
    start_width: u32,
    /// Whether an inner `.hard_line`, `.blank_line`, `.line_suffix`, or `force_break` poisoned this group.
    is_broken: bool = false,
};

/// Pair of alternative text slices evaluated by `DocOp.if_break`.
pub const IfBreakPair = struct {
    /// Text emitted when the enclosing group breaks across multiple lines (e.g., `","`).
    break_text: []const u8,
    /// Text emitted when the enclosing group fits on a single flat line (e.g., `""`).
    flat_text: []const u8,
};

/// Stored `"""…"""` multiline string literal and its original source line indentation (`DR-22` §3.4).
pub const MultilineStringEntry = struct {
    /// Owned raw UTF-8 lexeme of the triple-quoted string or byte-string literal.
    raw_lexeme: []u8,
    /// Leading space indentation of the source line containing the opening `"""` delimiter.
    old_line_indent: u32,
};

/// Contiguous arena of 8-byte `DocInst` instructions with $O(1)$ group `flat_width` backpatching.
pub const DocArena = struct {
    /// Backing allocator for instruction, group frame, and text buffers.
    allocator: std.mem.Allocator,
    /// Flat sequence of 8-byte document algebra instructions.
    instructions: std.ArrayList(DocInst) = .empty,
    /// Dynamic stack of currently open formatting groups awaiting `endGroup` backpatching.
    open_groups: std.ArrayList(OpenGroupFrame) = .empty,
    /// Contiguous byte buffer storing all emitted `.text` slices.
    string_bytes: std.ArrayList(u8) = .empty,
    /// Owned copies of queued `.line_suffix` comment strings indexed by `DocInst.payload`.
    line_suffix_slices: std.ArrayList([]const u8) = .empty,
    /// Table of `(break_text, flat_text)` pairs indexed by `.if_break` `DocInst.payload`.
    if_break_pairs: std.ArrayList(IfBreakPair) = .empty,
    /// Table of verbatim suppressed source slices indexed by `.verbatim_text` `DocInst.payload`.
    verbatim_slices: std.ArrayList([]const u8) = .empty,
    /// Table of triple-quoted multiline string literals indexed by `.multiline_string` `DocInst.payload`.
    multiline_strings: std.ArrayList(MultilineStringEntry) = .empty,
    /// Monotonically advancing flat column width counter used to compute group widths in $O(1)$.
    running_width: u32 = 0,

    /// Initializes an empty `DocArena` bound to `allocator`.
    pub fn init(allocator: std.mem.Allocator) DocArena {
        return .{ .allocator = allocator };
    }

    /// Releases all instruction, group stack, and string storage owned by `self`.
    pub fn deinit(self: *DocArena) void {
        for (self.line_suffix_slices.items) |slice| {
            self.allocator.free(slice);
        }
        for (self.if_break_pairs.items) |pair| {
            self.allocator.free(pair.break_text);
            self.allocator.free(pair.flat_text);
        }
        for (self.verbatim_slices.items) |slice| {
            self.allocator.free(slice);
        }
        for (self.multiline_strings.items) |entry| {
            self.allocator.free(entry.raw_lexeme);
        }
        self.instructions.deinit(self.allocator);
        self.open_groups.deinit(self.allocator);
        self.string_bytes.deinit(self.allocator);
        self.line_suffix_slices.deinit(self.allocator);
        self.if_break_pairs.deinit(self.allocator);
        self.verbatim_slices.deinit(self.allocator);
        self.multiline_strings.deinit(self.allocator);
        self.* = undefined;
    }

    /// Marks all currently open groups on `self.open_groups` as broken (`flat_width = INF_WIDTH`).
    pub fn poisonOpenGroups(self: *DocArena) void {
        for (self.open_groups.items) |*frame| {
            frame.is_broken = true;
        }
    }

    /// Emits `text` as one or more `.text` instructions, chunking slices larger than `0xFFFE` bytes.
    pub fn emitText(self: *DocArena, text: []const u8) !void {
        if (text.len == 0) return;
        if (std.mem.indexOfScalar(u8, text, '\n') != null) {
            self.poisonOpenGroups();
        }
        var offset: usize = 0;
        while (offset < text.len) {
            const chunk_len: u16 = @intCast(@min(text.len - offset, MAX_TEXT_CHUNK_LEN));
            const byte_start: u32 = @intCast(self.string_bytes.items.len);
            try self.string_bytes.appendSlice(self.allocator, text[offset .. offset + chunk_len]);
            try self.instructions.append(self.allocator, .{
                .op = .text,
                .mode_or_delta = 0,
                .flat_width = chunk_len,
                .payload = byte_start,
            });
            self.running_width +|= chunk_len;
            offset += chunk_len;
        }
    }

    /// Emits a raw multi-line suppressed source region (`// corex fmt: off` … `on`) verbatim.
    pub fn emitVerbatimText(self: *DocArena, raw_slice: []const u8) !void {
        if (raw_slice.len == 0) return;
        self.poisonOpenGroups();
        const owned_copy = try self.allocator.dupe(u8, raw_slice);
        errdefer self.allocator.free(owned_copy);
        const slice_idx: u32 = @intCast(self.verbatim_slices.items.len);
        try self.verbatim_slices.append(self.allocator, owned_copy);
        try self.instructions.append(self.allocator, .{
            .op = .verbatim_text,
            .mode_or_delta = 0,
            .flat_width = INF_WIDTH,
            .payload = slice_idx,
        });
    }

    /// Emits a `"""…"""` multiline string literal to be delta-shifted by `DocRenderer` (`DR-22` §3.4).
    pub fn emitMultilineString(
        self: *DocArena,
        raw_lexeme: []const u8,
        old_line_indent: u32,
    ) !void {
        if (raw_lexeme.len == 0) return;
        self.poisonOpenGroups();
        const owned_lexeme = try self.allocator.dupe(u8, raw_lexeme);
        errdefer self.allocator.free(owned_lexeme);
        const entry_idx: u32 = @intCast(self.multiline_strings.items.len);
        try self.multiline_strings.append(self.allocator, .{
            .raw_lexeme = owned_lexeme,
            .old_line_indent = old_line_indent,
        });
        try self.instructions.append(self.allocator, .{
            .op = .multiline_string,
            .mode_or_delta = 0,
            .flat_width = INF_WIDTH,
            .payload = entry_idx,
        });
    }

    /// Emits a `.line` instruction (`" "` when flat, `"\n"` + indent when broken).
    pub fn emitLine(self: *DocArena) !void {
        try self.instructions.append(self.allocator, .{
            .op = .line,
            .mode_or_delta = 1,
            .flat_width = 1,
            .payload = 0,
        });
        self.running_width +|= 1;
    }

    /// Emits a `.soft_line` instruction (`""` when flat, `"\n"` + indent when broken).
    pub fn emitSoftLine(self: *DocArena) !void {
        try self.instructions.append(self.allocator, .{
            .op = .soft_line,
            .mode_or_delta = 0,
            .flat_width = 0,
            .payload = 0,
        });
    }

    /// Emits an unconditional `.hard_line` instruction and poisons all open groups.
    pub fn emitHardLine(self: *DocArena) !void {
        self.poisonOpenGroups();
        try self.instructions.append(self.allocator, .{
            .op = .hard_line,
            .mode_or_delta = 0,
            .flat_width = INF_WIDTH,
            .payload = 0,
        });
    }

    /// Emits an unconditional `.blank_line` instruction (`\n\n`) and poisons all open groups.
    pub fn emitBlankLine(self: *DocArena) !void {
        self.poisonOpenGroups();
        try self.instructions.append(self.allocator, .{
            .op = .blank_line,
            .mode_or_delta = 0,
            .flat_width = INF_WIDTH,
            .payload = 0,
        });
    }

    /// Increases indentation by `spaces` columns (`INDENT_SPACES = 4` by default).
    pub fn beginIndent(self: *DocArena, spaces: u8) !void {
        try self.instructions.append(self.allocator, .{
            .op = .indent,
            .mode_or_delta = spaces,
            .flat_width = 0,
            .payload = 0,
        });
    }

    /// Decreases indentation by `spaces` columns (`INDENT_SPACES = 4` by default).
    pub fn endIndent(self: *DocArena, spaces: u8) !void {
        try self.instructions.append(self.allocator, .{
            .op = .dedent,
            .mode_or_delta = spaces,
            .flat_width = 0,
            .payload = 0,
        });
    }

    /// Opens a formatting group with `mode`, returning the `.group_begin` instruction index.
    pub fn beginGroup(self: *DocArena, mode: GroupMode) !u32 {
        if (mode == .force_break) {
            self.poisonOpenGroups();
        }
        const inst_index: u32 = @intCast(self.instructions.items.len);
        try self.instructions.append(self.allocator, .{
            .op = .group_begin,
            .mode_or_delta = @backingInt(mode),
            .flat_width = 0,
            .payload = 0,
        });
        try self.open_groups.append(self.allocator, .{
            .inst_index = inst_index,
            .start_width = self.running_width,
            .is_broken = (mode == .force_break),
        });
        return inst_index;
    }

    /// Closes the innermost open group and backpatches its `.group_begin` `flat_width` in $O(1)$ time.
    pub fn endGroup(self: *DocArena) !void {
        if (self.open_groups.items.len == 0) return;
        const frame = self.open_groups.pop().?;
        const end_inst_index: u32 = @intCast(self.instructions.items.len);
        const width_delta = self.running_width -| frame.start_width;
        const computed_width: u16 = if (frame.is_broken or width_delta >= INF_WIDTH)
            INF_WIDTH
        else
            @intCast(width_delta);

        self.instructions.items[frame.inst_index].flat_width = computed_width;
        self.instructions.items[frame.inst_index].payload = end_inst_index;
        if (frame.is_broken and self.open_groups.items.len > 0) {
            self.open_groups.items[self.open_groups.items.len - 1].is_broken = true;
        }
        try self.instructions.append(self.allocator, .{
            .op = .group_end,
            .mode_or_delta = 0,
            .flat_width = computed_width,
            .payload = frame.inst_index,
        });
    }

    /// Emits an `.if_break` instruction choosing `break_text` when broken or `flat_text` when flat.
    pub fn emitIfBreak(self: *DocArena, break_text: []const u8, flat_text: []const u8) !void {
        const owned_break = try self.allocator.dupe(u8, break_text);
        errdefer self.allocator.free(owned_break);
        const owned_flat = try self.allocator.dupe(u8, flat_text);
        errdefer self.allocator.free(owned_flat);

        const pair_idx: u32 = @intCast(self.if_break_pairs.items.len);
        try self.if_break_pairs.append(self.allocator, .{
            .break_text = owned_break,
            .flat_text = owned_flat,
        });
        const flat_len: u16 = @intCast(@min(flat_text.len, MAX_TEXT_CHUNK_LEN));
        try self.instructions.append(self.allocator, .{
            .op = .if_break,
            .mode_or_delta = 0,
            .flat_width = flat_len,
            .payload = pair_idx,
        });
        self.running_width +|= flat_len;
    }

    /// Queues a trailing comment (`line_suffix`) and poisons all enclosing open groups.
    pub fn emitLineSuffix(self: *DocArena, comment_text: []const u8) !void {
        const trimmed = std.mem.trim(u8, comment_text, " \t\r\n");
        if (trimmed.len == 0) return;
        self.poisonOpenGroups();
        const owned_comment = try self.allocator.dupe(u8, trimmed);
        errdefer self.allocator.free(owned_comment);
        const slice_idx: u32 = @intCast(self.line_suffix_slices.items.len);
        try self.line_suffix_slices.append(self.allocator, owned_comment);
        try self.instructions.append(self.allocator, .{
            .op = .line_suffix,
            .mode_or_delta = 0,
            .flat_width = INF_WIDTH,
            .payload = slice_idx,
        });
    }

    /// Returns the UTF-8 slice for a `.text` instruction in $O(1)$ time.
    pub inline fn getTextSlice(self: *const DocArena, inst: DocInst) []const u8 {
        const start: usize = inst.payload;
        const end: usize = start + inst.flat_width;
        return self.string_bytes.items[start..end];
    }
};

/// Single-pass $O(N)$ linear renderer executing a `DocArena` into formatted UTF-8 source text.
pub const DocRenderer = struct {
    /// Backing allocator for output bytes and dynamic stacks.
    allocator: std.mem.Allocator,
    /// Maximum target line width before breaking `auto_fit` groups (`100` by default).
    max_line_width: u16 = MAX_LINE_WIDTH,
    /// Output byte buffer accumulating formatted source text.
    out: std.ArrayList(u8) = .empty,
    /// Dynamic queue of trailing comments (`line_suffix`) waiting for the next line break.
    line_suffix_queue: std.ArrayList([]const u8) = .empty,
    /// Stack of active group break decisions (`true` = broken, `false` = flat).
    group_break_stack: std.ArrayList(bool) = .empty,
    /// Current logical indentation level in spaces.
    indent_spaces: u32 = 0,
    /// Current 0-based column offset on the active line.
    current_col: u32 = 0,
    /// Deferred indentation spaces to emit before the first non-empty text on a new line.
    pending_indent_spaces: u32 = 0,
    /// Materialized leading space count of the currently active output line.
    current_line_indent: u32 = 0,
    /// Count of consecutive trailing `\n` bytes currently at the end of `out` (`0..2`).
    consecutive_newlines: u8 = 0,
    /// Whether the renderer is positioned at the start of a fresh line awaiting deferred indent.
    is_at_line_start: bool = true,

    /// Initializes a `DocRenderer` bound to `allocator` and `max_line_width`.
    pub fn init(allocator: std.mem.Allocator, max_line_width: u16) DocRenderer {
        return .{
            .allocator = allocator,
            .max_line_width = max_line_width,
        };
    }

    /// Releases internal queues and output buffer if not transferred via `toOwnedSlice`.
    pub fn deinit(self: *DocRenderer) void {
        self.out.deinit(self.allocator);
        self.line_suffix_queue.deinit(self.allocator);
        self.group_break_stack.deinit(self.allocator);
        self.* = undefined;
    }

    /// Returns whether the innermost enclosing formatting group is currently broken.
    pub inline fn isCurrentGroupBroken(self: *const DocRenderer) bool {
        if (self.group_break_stack.items.len == 0) return false;
        return self.group_break_stack.items[self.group_break_stack.items.len - 1];
    }

    /// Appends `slice` to `self.out`, materializing deferred indentation spaces if at line start.
    fn writeTextSlice(self: *DocRenderer, slice: []const u8) !void {
        if (slice.len == 0) return;
        if (self.is_at_line_start) {
            try self.out.appendNTimes(self.allocator, ' ', self.pending_indent_spaces);
            self.current_line_indent = self.pending_indent_spaces;
            self.current_col = self.pending_indent_spaces;
            self.is_at_line_start = false;
            self.consecutive_newlines = 0;
        }
        try self.out.appendSlice(self.allocator, slice);
        self.current_col += @intCast(slice.len);
    }

    /// Appends `slice` to `self.out` while stripping any `\r` carriage returns (`\r\n` -> `\n`).
    fn appendSliceNormalizedLf(self: *DocRenderer, slice: []const u8) !void {
        for (slice) |byte_val| {
            if (byte_val == '\r') continue;
            try self.out.append(self.allocator, byte_val);
        }
    }

    /// Renders a triple-quoted `"""…"""` literal shifted by `emitted_open_line_indent - old_line_indent` (`DR-22` §3.4).
    fn renderMultilineString(self: *DocRenderer, entry: MultilineStringEntry) !void {
        const parsed = extractMultilineTripleQuoteParts(entry.raw_lexeme) orelse {
            try self.writeTextSlice(entry.raw_lexeme);
            return;
        };

        try self.writeTextSlice(parsed.open_header);
        const emitted_open_indent = self.current_line_indent;
        try self.out.append(self.allocator, '\n');

        const is_interp_allowed = !parsed.is_raw and !parsed.is_byte;
        var last_outer_lf: ?usize = null;
        var scan_pos: usize = 0;
        while (findNextOuterLineFeedInMultiline(parsed.body_after_open_nl, scan_pos, parsed.is_raw, is_interp_allowed)) |lf_pos| {
            last_outer_lf = lf_pos;
            scan_pos = lf_pos + 1;
        }

        const close_prefix = if (last_outer_lf) |lf_idx|
            parsed.body_after_open_nl[lf_idx + 1 ..]
        else
            parsed.body_after_open_nl;

        var is_valid_spaces_only = true;
        for (close_prefix) |prefix_byte| {
            if (prefix_byte != ' ') {
                is_valid_spaces_only = false;
                break;
            }
        }
        var min_leading_spaces: usize = close_prefix.len;

        if (last_outer_lf) |final_lf_idx| {
            const content_end: usize = if (final_lf_idx > 0 and parsed.body_after_open_nl[final_lf_idx - 1] == '\r')
                final_lf_idx - 1
            else
                final_lf_idx;
            const content_bytes = parsed.body_after_open_nl[0..content_end];

            var line_start: usize = 0;
            while (true) {
                const maybe_lf = findNextOuterLineFeedInMultiline(content_bytes, line_start, parsed.is_raw, is_interp_allowed);
                const raw_line_end = maybe_lf orelse content_bytes.len;
                const clean_line_end = if (raw_line_end > line_start and content_bytes[raw_line_end - 1] == '\r')
                    raw_line_end - 1
                else
                    raw_line_end;
                const line_slice = content_bytes[line_start..clean_line_end];

                if (line_slice.len > 0) {
                    if (line_slice[0] == '\t') {
                        is_valid_spaces_only = false;
                    } else {
                        var space_count: usize = 0;
                        while (space_count < line_slice.len and line_slice[space_count] == ' ') : (space_count += 1) {}
                        min_leading_spaces = @min(min_leading_spaces, space_count);
                    }
                }
                if (maybe_lf) |lf_pos| {
                    line_start = lf_pos + 1;
                } else {
                    break;
                }
            }

            const raw_delta: isize = @as(isize, @intCast(emitted_open_indent)) -
                @as(isize, @intCast(entry.old_line_indent));
            const eff_delta: isize = if (!is_valid_spaces_only)
                0
            else
                @max(raw_delta, -@as(isize, @intCast(min_leading_spaces)));

            line_start = 0;
            while (true) {
                const maybe_lf = findNextOuterLineFeedInMultiline(content_bytes, line_start, parsed.is_raw, is_interp_allowed);
                const raw_line_end = maybe_lf orelse content_bytes.len;
                const clean_line_end = if (raw_line_end > line_start and content_bytes[raw_line_end - 1] == '\r')
                    raw_line_end - 1
                else
                    raw_line_end;
                const line_slice = content_bytes[line_start..clean_line_end];

                if (line_slice.len > 0) {
                    if (eff_delta >= 0) {
                        try self.out.appendNTimes(self.allocator, ' ', @intCast(eff_delta));
                        try self.appendSliceNormalizedLf(line_slice);
                    } else {
                        const drop_spaces: usize = @intCast(-eff_delta);
                        try self.appendSliceNormalizedLf(line_slice[drop_spaces..]);
                    }
                }
                try self.out.append(self.allocator, '\n');

                if (maybe_lf) |lf_pos| {
                    line_start = lf_pos + 1;
                } else {
                    break;
                }
            }

            const new_close_spaces: usize = @intCast(@as(isize, @intCast(close_prefix.len)) + eff_delta);
            try self.out.appendNTimes(self.allocator, ' ', new_close_spaces);
            try self.out.appendSlice(self.allocator, parsed.close_delim);
            self.current_line_indent = @intCast(new_close_spaces);
            self.current_col = @intCast(new_close_spaces + parsed.close_delim.len);
            self.is_at_line_start = false;
            self.consecutive_newlines = 0;
            return;
        }

        const raw_delta: isize = @as(isize, @intCast(emitted_open_indent)) -
            @as(isize, @intCast(entry.old_line_indent));
        const eff_delta: isize = if (!is_valid_spaces_only)
            0
        else
            @max(raw_delta, -@as(isize, @intCast(min_leading_spaces)));
        const new_close_spaces: usize = @intCast(@as(isize, @intCast(close_prefix.len)) + eff_delta);
        try self.out.appendNTimes(self.allocator, ' ', new_close_spaces);
        try self.out.appendSlice(self.allocator, parsed.close_delim);
        self.current_line_indent = @intCast(new_close_spaces);
        self.current_col = @intCast(new_close_spaces + parsed.close_delim.len);
        self.is_at_line_start = false;
        self.consecutive_newlines = 0;
    }

    /// Flushes all queued `line_suffix` comments and emits a line break (or blank line).
    pub fn flushNewline(self: *DocRenderer, is_blank_line: bool) !void {
        // Strip any trailing horizontal spaces before flushing `line_suffix` or `\n`:
        while (self.out.items.len > 0 and self.out.items[self.out.items.len - 1] == ' ') {
            _ = self.out.pop();
            self.current_col -|= 1;
        }

        // [1] Flush queued `line_suffix` comments before emitting `\n`:
        if (self.line_suffix_queue.items.len > 0) {
            if (self.is_at_line_start) {
                try self.out.appendNTimes(self.allocator, ' ', self.pending_indent_spaces);
                self.current_line_indent = self.pending_indent_spaces;
                self.current_col = self.pending_indent_spaces;
                self.is_at_line_start = false;
                self.consecutive_newlines = 0;
            }
            for (self.line_suffix_queue.items) |suffix| {
                if (self.out.items.len > 0 and
                    self.out.items[self.out.items.len - 1] != ' ' and
                    self.out.items[self.out.items.len - 1] != '\n')
                {
                    try self.out.append(self.allocator, ' ');
                    self.current_col += 1;
                }
                try self.out.appendSlice(self.allocator, suffix);
                self.current_col += @intCast(suffix.len);
            }
            self.line_suffix_queue.clearRetainingCapacity();
        }

        // [2] Avoid emitting leading newlines at the very start of the file:
        if (self.out.items.len == 0) {
            self.current_col = 0;
            self.current_line_indent = 0;
            self.is_at_line_start = true;
            self.pending_indent_spaces = self.indent_spaces;
            return;
        }

        // [3] Clamp consecutive newlines so at most 1 blank line (`\n\n`) can ever be emitted:
        if (is_blank_line) {
            while (self.consecutive_newlines < 2) {
                try self.out.append(self.allocator, '\n');
                self.consecutive_newlines += 1;
            }
        } else if (self.consecutive_newlines == 0) {
            try self.out.append(self.allocator, '\n');
            self.consecutive_newlines = 1;
        }

        self.current_col = 0;
        self.current_line_indent = 0;
        self.is_at_line_start = true;
        self.pending_indent_spaces = self.indent_spaces;
    }

    /// Executes all instructions in `arena` in $O(N)$ time and returns the owned formatted slice.
    pub fn render(self: *DocRenderer, arena: *const DocArena) ![]u8 {
        self.out.clearRetainingCapacity();
        self.line_suffix_queue.clearRetainingCapacity();
        self.group_break_stack.clearRetainingCapacity();
        self.indent_spaces = 0;
        self.current_col = 0;
        self.pending_indent_spaces = 0;
        self.current_line_indent = 0;
        self.consecutive_newlines = 0;
        self.is_at_line_start = true;

        for (arena.instructions.items) |inst| {
            switch (inst.op) {
                .nop => {},
                .text => {
                    try self.writeTextSlice(arena.getTextSlice(inst));
                },
                .verbatim_text => {
                    const raw_slice = arena.verbatim_slices.items[inst.payload];
                    if (raw_slice.len == 0) continue;
                    if (self.is_at_line_start and raw_slice[0] != ' ' and raw_slice[0] != '\t') {
                        try self.out.appendNTimes(self.allocator, ' ', self.pending_indent_spaces);
                        self.current_line_indent = self.pending_indent_spaces;
                        self.current_col = self.pending_indent_spaces;
                    }
                    self.is_at_line_start = false;
                    self.consecutive_newlines = 0;
                    for (raw_slice) |byte_val| {
                        if (byte_val == '\r') continue;
                        try self.out.append(self.allocator, byte_val);
                        if (byte_val == '\n') {
                            self.current_col = 0;
                            self.current_line_indent = 0;
                            self.is_at_line_start = true;
                            self.pending_indent_spaces = self.indent_spaces;
                            if (self.consecutive_newlines < 2) self.consecutive_newlines += 1;
                        } else {
                            self.current_col += 1;
                            self.is_at_line_start = false;
                            self.consecutive_newlines = 0;
                        }
                    }
                },
                .multiline_string => {
                    try self.renderMultilineString(arena.multiline_strings.items[inst.payload]);
                },
                .line => {
                    if (self.isCurrentGroupBroken()) {
                        try self.flushNewline(false);
                    } else if (!self.is_at_line_start) {
                        try self.writeTextSlice(" ");
                    }
                },
                .soft_line => {
                    if (self.isCurrentGroupBroken()) {
                        try self.flushNewline(false);
                    }
                },
                .hard_line => {
                    try self.flushNewline(false);
                },
                .blank_line => {
                    try self.flushNewline(true);
                },
                .indent => {
                    self.indent_spaces += inst.mode_or_delta;
                    if (self.is_at_line_start) {
                        self.pending_indent_spaces = self.indent_spaces;
                    }
                },
                .dedent => {
                    self.indent_spaces -|= inst.mode_or_delta;
                    if (self.is_at_line_start) {
                        self.pending_indent_spaces = self.indent_spaces;
                    }
                },
                .group_begin => {
                    const mode: GroupMode = @fromBackingInt(@intCast(inst.mode_or_delta));
                    const effective_col = if (self.is_at_line_start)
                        self.pending_indent_spaces
                    else
                        self.current_col;
                    const is_broken = switch (mode) {
                        .force_break => true,
                        .auto_fit, .columnar_grid => inst.flat_width == INF_WIDTH or
                            (effective_col + inst.flat_width > self.max_line_width),
                    };
                    try self.group_break_stack.append(self.allocator, is_broken);
                },
                .group_end => {
                    _ = self.group_break_stack.pop();
                },
                .if_break => {
                    const pair = arena.if_break_pairs.items[inst.payload];
                    try self.writeTextSlice(if (self.isCurrentGroupBroken()) pair.break_text else pair.flat_text);
                },
                .line_suffix => {
                    try self.line_suffix_queue.append(
                        self.allocator,
                        arena.line_suffix_slices.items[inst.payload],
                    );
                },
            }
        }

        // Flush any remaining `line_suffix` comments at EOF:
        if (self.line_suffix_queue.items.len > 0) {
            try self.flushNewline(false);
        }

        // Normalize EOF to end with exactly one `\n` for non-empty files:
        while (self.out.items.len > 1 and
            self.out.items[self.out.items.len - 1] == '\n' and
            self.out.items[self.out.items.len - 2] == '\n')
        {
            _ = self.out.pop();
        }
        if (self.out.items.len > 0 and self.out.items[self.out.items.len - 1] != '\n') {
            try self.out.append(self.allocator, '\n');
        }

        return self.out.toOwnedSlice(self.allocator);
    }
};

/// Configuration options controlling `corex fmt` and `corex fmt --fix` (`DR-14` Section 1.5).
pub const FormatOptions = struct {
    /// Whether `--fix` mode (canonical identifier casing and missing `;` insertion) is active.
    is_fix_mode: bool = false,
    /// Target maximum line width in columns (`100` by default).
    max_line_width: u16 = MAX_LINE_WIDTH,
};

/// Result returned by `formatSource`, `formatSourceWithOptions`, and `formatTokensAndCst`.
pub const FormatResult = struct {
    /// Owned UTF-8 formatted text slice (must be freed via `deinit` or `allocator.free`).
    formatted_text: []u8,
    /// Whether `formatted_text` differs from the original input source.
    is_changed: bool,
    /// Whether lexical or parse errors were encountered in the input source.
    has_syntax_errors: bool,

    /// Releases `formatted_text` back to `allocator`.
    pub fn deinit(self: *FormatResult, allocator: std.mem.Allocator) void {
        allocator.free(self.formatted_text);
        self.* = undefined;
    }
};

// --------------- Trivia & CST Formatter Context ---------------

/// Paired `.context_binding` CST subtree and its optional trailing `,` token.
const WithBindingEntry = struct {
    /// CST node index of the `.context_binding` entry.
    binding_id: CstNodeIndex,
    /// Trailing `,` token index following this binding, or `.none` when omitted.
    comma_tok: TokenIndex = .none,
};

/// Byte range in `source` suppressed by `// corex fmt: off` … `// corex fmt: on`.
const SuppressedRange = struct {
    /// Starting byte offset in `source` (including the `// corex fmt: off` comment).
    off_start: u32,
    /// Ending byte offset in `source` (including the matching `// corex fmt: on` comment or EOF).
    on_end: u32,
    /// Whether this suppressed range has already been emitted into `DocArena`.
    is_emitted: bool = false,
};

/// Syntactic declaration role of an identifier token for `--fix` casing normalization.
const FixDeclRole = enum(u2) {
    none = 0,
    type_decl = 1,
    const_decl = 2,
    value_decl = 3,
};

/// Pre-classified leading and same-line trailing trivia metadata for a single token in `TokenBuffer`.
const TokenTriviaMeta = struct {
    /// Start index in `trivia_slice` for this token's leading trivia.
    leading_start: u32 = 0,
    /// End index in `trivia_slice` for this token's leading trivia.
    leading_end: u32 = 0,
    /// Start index in `trivia_slice` for this token's direct trailing trivia.
    trailing_start: u32 = 0,
    /// End index in `trivia_slice` for this token's direct trailing trivia.
    trailing_end: u32 = 0,
    /// Start index in `trivia_slice` of same-line trailing trivia stolen from next token.
    stolen_trailing_start: u32 = 0,
    /// End index in `trivia_slice` of same-line trailing trivia stolen from next token.
    stolen_trailing_end: u32 = 0,
    /// Whether at least 1 newline occurred between the previous real token and this token.
    has_leading_newline: bool = false,
    /// Whether at least 2 consecutive newlines (a blank line) occurred before this token or its comments.
    has_leading_blank_line: bool = false,
    /// Whether `leading_start .. leading_end` contains any comment or shebang piece.
    has_leading_comments: bool = false,
    /// Whether `leading_start .. leading_end` contains a `///` or `//!` doc comment.
    has_doc_comment: bool = false,
    /// Whether this token has any same-line trailing comments.
    has_trailing_comments: bool = false,
    /// Whether the newline separating the previous token's trailing comment from this token was consumed.
    has_split_newline: bool = false,
    /// Whether this token's leading trivia has been emitted.
    is_leading_consumed: bool = false,
    /// Whether this token's trailing trivia has been emitted.
    is_trailing_consumed: bool = false,
    /// Whether this token itself has been visited by the formatter.
    is_token_emitted: bool = false,
    /// Declaration role if this token is the defining identifier of an item, field, param, or local.
    decl_role: FixDeclRole = .none,
};

/// Prepared formatter trivia table borrowing `TokenBuffer.trivia` or owning an uncoalesced expansion.
const PreparedTriviaTable = struct {
    /// Active trivia slice indexed by `TokenTriviaMeta` ranges.
    trivia_slice: []const TriviaPiece,
    /// Owned expanded trivia buffer when `TRIVIA_FLAG_COALESCED` was present (`null` in the common case).
    owned_trivia: ?[]TriviaPiece = null,
    /// Per-token trivia classification table.
    token_meta: []TokenTriviaMeta,
};

/// Sortable entry representing a single specifier inside a braced `use a.b.{…};` group.
const UseSpecEntry = struct {
    /// CST node index of the child `.use_tree` node.
    node_idx: CstNodeIndex,
    /// Normalized sort key slice (`self` sorts before all other ASCII keys).
    sort_key: []const u8,
    /// Trailing comma token immediately following this specifier (or `.none` if omitted).
    comma_tok: TokenIndex = .none,
    /// Whether this specifier starts with the `self` keyword.
    is_self: bool,

    /// Compares two `UseSpecEntry` items (`self` first, then lexicographical ASCII byte order).
    pub fn lessThan(_: void, lhs: UseSpecEntry, rhs: UseSpecEntry) bool {
        if (lhs.is_self != rhs.is_self) {
            return lhs.is_self;
        }
        return std.mem.order(u8, lhs.sort_key, rhs.sort_key) == .lt;
    }
};

/// Parsed prefix, body, and closing delimiter slices of a multiline `"""…"""` literal (`DR-22` §3.4).
const ParsedMultilineLiteral = struct {
    /// Opening prefix through `"""` (e.g., `"""`, `r#"""`, `b"""`, `br#"""`), plus any horizontal spaces before `\n`.
    open_header: []const u8,
    /// Raw body bytes strictly after the opening `\r?\n` and before the closing `"""[#*]`.
    body_after_open_nl: []const u8,
    /// Closing delimiter slice (`"""` followed by matching `#` count).
    close_delim: []const u8,
    /// Whether the literal uses raw `r` / `br` escaping rules.
    is_raw: bool,
    /// Whether the literal uses byte `b` / `br` prefix rules.
    is_byte: bool,
};

/// Sortable entry for parameterless `@marker` attributes (`@inline @no_alloc @no_panic`, `DR-22` §3.4).
const MarkerAttrEntry = struct {
    /// CST node index of the parameterless `.attribute` node.
    node_idx: CstNodeIndex,
    /// Attribute identifier lexeme used for lexicographical ASCII sorting.
    sort_name: []const u8,
    /// Original 0-based position for deterministic tie-breaking on duplicate markers.
    orig_order: usize,

    /// Compares two `MarkerAttrEntry` items lexicographically by `sort_name`.
    pub fn lessThan(_: void, lhs: MarkerAttrEntry, rhs: MarkerAttrEntry) bool {
        const cmp = std.mem.order(u8, lhs.sort_name, rhs.sort_name);
        if (cmp != .eq) return cmp == .lt;
        return lhs.orig_order < rhs.orig_order;
    }
};

/// Precedence tiers of the unified 4-tier `Type` grammar (`DR-22` Sections 1.3 & 3.3).
const TypePrec = enum(u8) {
    /// Unparenthesized open context (`|`, `+`, `is`/`where`, `distinct`).
    tier0_open = 0,
    /// Non-associative `Ok ! Err` result type (`Tier 1`).
    tier1_result = 1,
    /// Prefix `&T`, `&mut T`, `&out T`, `own T`, `~T` (`Tier 2`).
    tier2_prefix = 2,
    /// Postfix `T?` optional type (`Tier 3`).
    tier3_postfix = 3,
    /// Atomic/primary types (`T`, `&[T]`, `*T`, `*mut T`, `[T; N]`, `(T, U)`, `fn()`, `|…|`) (`Tier 4`).
    tier4_primary = 4,
};

/// Canonicalizable standard-library `Option[T]` or `Result[T, E]` generic `.named_type` (`DR-22` §3.4).
const CanonicalStdlibType = union(enum) {
    /// `Option[T]` rewritable to `T?`.
    option: struct {
        name_tok: TokenIndex,
        close_bracket_tok: TokenIndex,
        inner_type_id: CstNodeIndex,
    },
    /// `Result[T, E]` rewritable to `T!E`.
    result: struct {
        name_tok: TokenIndex,
        close_bracket_tok: TokenIndex,
        ok_type_id: CstNodeIndex,
        err_type_id: CstNodeIndex,
    },
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical maximum column width for `corex fmt` (`DR-03` Section 7 & `DR-14` Section 1.2).
pub const MAX_LINE_WIDTH: u16 = 100;
/// Canonical block and group indentation step in spaces (`4` spaces).
pub const INDENT_SPACES: u16 = 4;
/// Sentinel `flat_width` value (`0xFFFF`) marking multiline or broken groups.
pub const INF_WIDTH: u16 = 0xFFFF;
/// Maximum byte length of a single `.text` instruction chunk (`0xFFFE` = `65,534`).
pub const MAX_TEXT_CHUNK_LEN: u16 = 0xFFFE;
/// Minimum number of elements (`> 8`) required to activate `GroupMode.columnar_grid` on literal arrays.
pub const COLUMNAR_GRID_MIN_ELEMENTS: usize = 9;
/// Maximum number of columns per row when rendering a `GroupMode.columnar_grid` literal array.
pub const COLUMNAR_GRID_MAX_COLS: usize = 8;

// -------------------------------------- INTERNALS --------------------------------------

// ---------------- Multiline String Indentation ----------------

/// Returns whether `slice[start_idx..]` begins with at least `expected_hashes` `'#'` bytes.
inline fn hasHashPrefixAt(slice: []const u8, start_idx: usize, expected_hashes: usize) bool {
    if (start_idx + expected_hashes > slice.len) return false;
    var hash_idx: usize = 0;
    while (hash_idx < expected_hashes) : (hash_idx += 1) {
        if (slice[start_idx + hash_idx] != '#') return false;
    }
    return true;
}

/// Returns whether `slice[quote_pos..]` opens a multiline `"""` literal rather than single-line `r#""…""#`.
inline fn isTripleQuoteRunOpening(
    slice: []const u8,
    quote_pos: usize,
    is_raw: bool,
    hash_count: usize,
) bool {
    var quote_run: usize = 0;
    while (quote_pos + quote_run < slice.len and slice[quote_pos + quote_run] == '"') : (quote_run += 1) {}
    if (quote_run < 3) return false;
    if (is_raw and hash_count > 0 and hasHashPrefixAt(slice, quote_pos + quote_run, hash_count)) {
        return false;
    }
    return true;
}

/// Splits a multiline triple-quoted string or byte-string `lexeme` (`[b][r[#*]]"""\r?\n…"""[#*]`), or returns `null`.
fn extractMultilineTripleQuoteParts(lexeme: []const u8) ?ParsedMultilineLiteral {
    if (lexeme.len < 7) return null;
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
    if (cursor + 6 + hash_count > lexeme.len) return null;
    if (!isTripleQuoteRunOpening(lexeme, cursor, is_raw, hash_count)) return null;

    const close_len: usize = 3 + hash_count;
    const close_pos: usize = lexeme.len - close_len;
    if (!hasHashPrefixAt(lexeme, lexeme.len - hash_count, hash_count)) return null;
    if (lexeme[close_pos] != '"' or lexeme[close_pos + 1] != '"' or lexeme[close_pos + 2] != '"') return null;

    // Require an opening line break immediately after `"""` (allowing horizontal whitespace before `\r?\n`):
    var header_end: usize = cursor + 3;
    while (header_end < close_pos and (lexeme[header_end] == ' ' or lexeme[header_end] == '\t')) : (header_end += 1) {}
    var body_start: usize = header_end;
    if (body_start < close_pos and lexeme[body_start] == '\r') {
        body_start += 1;
    }
    if (body_start >= close_pos or lexeme[body_start] != '\n') return null;
    body_start += 1;

    return .{
        .open_header = lexeme[0 .. cursor + 3],
        .body_after_open_nl = lexeme[body_start..close_pos],
        .close_delim = lexeme[close_pos..],
        .is_raw = is_raw,
        .is_byte = is_byte,
    };
}

/// Returns whether `byte_val` is an ASCII identifier continuation character (`[A-Za-z0-9_]`).
inline fn isAsciiIdentContinueByte(byte_val: u8) bool {
    return std.ascii.isAlphanumeric(byte_val) or byte_val == '_';
}

/// Skips a non-interpolated `'…'`, `b'…'`, `b"…"`, or `b"""…"""` literal inside an `{expr}` scan.
fn skipQuotedLiteralInHole(
    body_bytes: []const u8,
    after_open_idx: usize,
    quote_byte: u8,
    is_triple: bool,
) usize {
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
fn skipRawStringInHole(body_bytes: []const u8, after_r_idx: usize) usize {
    var cursor = after_r_idx;
    var hash_count: usize = 0;
    while (cursor < body_bytes.len and body_bytes[cursor] == '#') : (cursor += 1) {
        hash_count += 1;
    }
    if (cursor >= body_bytes.len or body_bytes[cursor] != '"') return cursor;
    const is_triple = isTripleQuoteRunOpening(body_bytes, cursor, true, hash_count);
    const quote_len: usize = if (is_triple) 3 else 1;
    cursor += quote_len;

    while (cursor < body_bytes.len) {
        if (body_bytes[cursor] == '"') {
            if (is_triple) {
                if (cursor + 2 < body_bytes.len and
                    body_bytes[cursor + 1] == '"' and
                    body_bytes[cursor + 2] == '"' and
                    hasHashPrefixAt(body_bytes, cursor + 3, hash_count))
                {
                    return cursor + 3 + hash_count;
                }
                cursor += 1;
                continue;
            }
            if (hasHashPrefixAt(body_bytes, cursor + 1, hash_count)) {
                return cursor + 1 + hash_count;
            }
        }
        cursor += 1;
    }
    return body_bytes.len;
}

/// Skips an interpolated `"…"` or `"""…"""` literal nested inside an `{expr}` scan.
fn skipInterpolatedStringInHole(body_bytes: []const u8, after_open_idx: usize, is_triple: bool) usize {
    var cursor = after_open_idx;
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
                    body_bytes[cursor + 2] == '"')
                {
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
            cursor = skipInterpolationHoleInMultiline(body_bytes, cursor);
            continue;
        }
        cursor += 1;
    }
    return body_bytes.len;
}

/// Advances past a `{expr}` interpolation hole inside `body_bytes` starting at `open_brace_idx`.
fn skipInterpolationHoleInMultiline(body_bytes: []const u8, open_brace_idx: usize) usize {
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
            (cursor == 0 or !isAsciiIdentContinueByte(body_bytes[cursor - 1])) and
            cursor + 1 < body_bytes.len and
            (body_bytes[cursor + 1] == '"' or body_bytes[cursor + 1] == '#'))
        {
            cursor = skipRawStringInHole(body_bytes, cursor + 1);
        } else if (cur_byte == 'b' and
            (cursor == 0 or !isAsciiIdentContinueByte(body_bytes[cursor - 1])) and
            cursor + 1 < body_bytes.len)
        {
            if (body_bytes[cursor + 1] == '\'') {
                cursor = skipQuotedLiteralInHole(body_bytes, cursor + 2, '\'', false);
            } else if (body_bytes[cursor + 1] == '"') {
                const is_triple = cursor + 3 < body_bytes.len and
                    body_bytes[cursor + 2] == '"' and
                    body_bytes[cursor + 3] == '"';
                const step: usize = if (is_triple) 4 else 2;
                cursor = skipQuotedLiteralInHole(body_bytes, cursor + step, '"', is_triple);
            } else if (body_bytes[cursor + 1] == 'r' and cursor + 2 < body_bytes.len and
                (body_bytes[cursor + 2] == '"' or body_bytes[cursor + 2] == '#'))
            {
                cursor = skipRawStringInHole(body_bytes, cursor + 2);
            } else {
                cursor += 1;
            }
        } else if (cur_byte == '"') {
            const is_triple = cursor + 2 < body_bytes.len and
                body_bytes[cursor + 1] == '"' and
                body_bytes[cursor + 2] == '"';
            const step: usize = if (is_triple) 3 else 1;
            cursor = skipInterpolatedStringInHole(body_bytes, cursor + step, is_triple);
        } else if (cur_byte == '\'') {
            cursor = skipQuotedLiteralInHole(body_bytes, cursor + 1, '\'', false);
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

/// Scans `body_bytes` from `start_pos` for the next outer `\n`, skipping `{expr}` holes when enabled.
fn findNextOuterLineFeedInMultiline(
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
            cursor = skipInterpolationHoleInMultiline(body_bytes, cursor);
            continue;
        }
        cursor += 1;
    }
    return null;
}

// --------------- Trivia & Suppression Pre-Pass ----------------

/// Returns whether `kind` is a comment or shebang trivia piece that must be preserved.
inline fn isCommentOrShebangTrivia(kind: TriviaKind) bool {
    return switch (kind) {
        .line_comment,
        .doc_comment,
        .module_doc_comment,
        .block_comment,
        .shebang,
        => true,
        else => false,
    };
}

/// Returns whether `kind` is a line feed or CRLF newline trivia piece.
inline fn isNewlineTrivia(kind: TriviaKind) bool {
    return kind == .newline_lf or kind == .newline_crlf;
}

/// Checks whether a `.line_comment` slice is a `// corex fmt: off` or `// corex fmt: on` directive.
fn classifyFmtDirective(comment_slice: []const u8) enum { none, fmt_off, fmt_on } {
    if (!std.mem.startsWith(u8, comment_slice, "//")) return .none;
    if (std.mem.startsWith(u8, comment_slice, "///") or std.mem.startsWith(u8, comment_slice, "//!")) {
        return .none;
    }
    const body = std.mem.trim(u8, comment_slice[2..], " \t\r\n");
    if (std.mem.eql(u8, body, "corex fmt: off")) return .fmt_off;
    if (std.mem.eql(u8, body, "corex fmt: on")) return .fmt_on;
    return .none;
}

/// Extracts all `// corex fmt: off` … `// corex fmt: on` byte ranges from `trivia_slice`.
fn extractSuppressedRanges(
    allocator: std.mem.Allocator,
    source: []const u8,
    trivia_slice: []const TriviaPiece,
) !std.ArrayList(SuppressedRange) {
    var ranges: std.ArrayList(SuppressedRange) = .empty;
    errdefer ranges.deinit(allocator);

    var active_off_start: ?u32 = null;
    for (trivia_slice) |piece| {
        if (piece.kind != .line_comment) continue;
        const start: usize = piece.byte_offset;
        const end: usize = @min(source.len, start + piece.byte_len);
        if (start >= end) continue;
        const slice = source[start..end];
        switch (classifyFmtDirective(slice)) {
            .fmt_off => {
                if (active_off_start == null) {
                    active_off_start = piece.byte_offset;
                }
            },
            .fmt_on => {
                if (active_off_start) |off_byte| {
                    try ranges.append(allocator, .{
                        .off_start = off_byte,
                        .on_end = @intCast(end),
                    });
                    active_off_start = null;
                }
            },
            .none => {},
        }
    }
    if (active_off_start) |off_byte| {
        try ranges.append(allocator, .{
            .off_start = off_byte,
            .on_end = @intCast(source.len),
        });
    }
    return ranges;
}

/// Appends chunked `TriviaPiece` records (`<= 65,535` bytes each) into `dest`.
fn appendChunkedTriviaPieces(
    allocator: std.mem.Allocator,
    dest: *std.ArrayList(TriviaPiece),
    kind: TriviaKind,
    start_offset: u32,
    total_len: usize,
) !void {
    var cur_off = start_offset;
    var rem = total_len;
    while (rem > 0) {
        const chunk: u16 = @intCast(@min(rem, @as(usize, std.math.maxInt(u16))));
        try dest.append(allocator, .{
            .kind = kind,
            .flags = 0,
            .byte_len = chunk,
            .byte_offset = cur_off,
        });
        cur_off += chunk;
        rem -= chunk;
    }
}

/// Expands a `TriviaPiece` (splitting `TRIVIA_FLAG_COALESCED` slots back into atomic pieces) into `dest`.
fn appendExpandedTriviaPiece(
    allocator: std.mem.Allocator,
    source: []const u8,
    piece: TriviaPiece,
    dest: *std.ArrayList(TriviaPiece),
) !void {
    if ((piece.flags & syntax_arenas.TRIVIA_FLAG_COALESCED) == 0) {
        try dest.append(allocator, piece);
        return;
    }
    const start_pos: usize = piece.byte_offset;
    const end_pos: usize = @min(source.len, start_pos + piece.byte_len);
    var cursor = start_pos;
    while (cursor < end_pos) {
        const byte_val = source[cursor];
        if (cursor == 0 and byte_val == '#' and cursor + 1 < end_pos and source[cursor + 1] == '!') {
            const run_start = cursor;
            cursor += 2;
            while (cursor < end_pos and source[cursor] != '\n' and source[cursor] != '\r') : (cursor += 1) {}
            try appendChunkedTriviaPieces(allocator, dest, .shebang, @intCast(run_start), cursor - run_start);
        } else if (byte_val == ' ') {
            const run_start = cursor;
            cursor += 1;
            while (cursor < end_pos and source[cursor] == ' ') : (cursor += 1) {}
            try appendChunkedTriviaPieces(allocator, dest, .spaces, @intCast(run_start), cursor - run_start);
        } else if (byte_val == '\t') {
            const run_start = cursor;
            cursor += 1;
            while (cursor < end_pos and source[cursor] == '\t') : (cursor += 1) {}
            try appendChunkedTriviaPieces(allocator, dest, .tabs, @intCast(run_start), cursor - run_start);
        } else if (byte_val == '\n') {
            try appendChunkedTriviaPieces(allocator, dest, .newline_lf, @intCast(cursor), 1);
            cursor += 1;
        } else if (byte_val == '\r') {
            if (cursor + 1 < end_pos and source[cursor + 1] == '\n') {
                try appendChunkedTriviaPieces(allocator, dest, .newline_crlf, @intCast(cursor), 2);
                cursor += 2;
            } else {
                try appendChunkedTriviaPieces(allocator, dest, .skipped_unexpected, @intCast(cursor), 1);
                cursor += 1;
            }
        } else if (byte_val == '/' and cursor + 1 < end_pos and source[cursor + 1] == '/') {
            const run_start = cursor;
            var comment_kind: TriviaKind = .line_comment;
            if (cursor + 2 < end_pos) {
                if (source[cursor + 2] == '!') {
                    comment_kind = .module_doc_comment;
                } else if (source[cursor + 2] == '/' and (cursor + 3 >= end_pos or source[cursor + 3] != '/')) {
                    comment_kind = .doc_comment;
                }
            }
            cursor += 2;
            while (cursor < end_pos and source[cursor] != '\n' and source[cursor] != '\r') : (cursor += 1) {}
            try appendChunkedTriviaPieces(allocator, dest, comment_kind, @intCast(run_start), cursor - run_start);
        } else if (byte_val == '/' and cursor + 1 < end_pos and source[cursor + 1] == '*') {
            const run_start = cursor;
            cursor += 2;
            var depth: u32 = 1;
            while (cursor < end_pos and depth > 0) {
                if (source[cursor] == '/' and cursor + 1 < end_pos and source[cursor + 1] == '*') {
                    depth += 1;
                    cursor += 2;
                } else if (source[cursor] == '*' and cursor + 1 < end_pos and source[cursor + 1] == '/') {
                    depth -= 1;
                    cursor += 2;
                } else {
                    cursor += 1;
                }
            }
            try appendChunkedTriviaPieces(allocator, dest, .block_comment, @intCast(run_start), cursor - run_start);
        } else {
            try appendChunkedTriviaPieces(allocator, dest, .skipped_unexpected, @intCast(cursor), 1);
            cursor += 1;
        }
    }
}

/// Pre-classifies leading and same-line trailing trivia for every token in `token_buffer`.
fn buildTokenTriviaMeta(
    allocator: std.mem.Allocator,
    source: []const u8,
    token_buffer: *const TokenBuffer,
) !PreparedTriviaTable {
    const token_count = token_buffer.countTokens();
    const meta_table = try allocator.alloc(TokenTriviaMeta, token_count);
    errdefer allocator.free(meta_table);
    @memset(meta_table, .{});

    var has_coalesced = false;
    for (token_buffer.trivia.items) |piece| {
        if ((piece.flags & syntax_arenas.TRIVIA_FLAG_COALESCED) != 0) {
            has_coalesced = true;
            break;
        }
    }

    var owned_trivia: ?[]TriviaPiece = null;
    errdefer if (owned_trivia) |owned| allocator.free(owned);

    if (has_coalesced) {
        var expanded: std.ArrayList(TriviaPiece) = .empty;
        errdefer expanded.deinit(allocator);
        var tok_idx: usize = 0;
        while (tok_idx < token_count) : (tok_idx += 1) {
            const tok_id = TokenIndex.fromInt(@intCast(tok_idx));
            meta_table[tok_idx].leading_start = @intCast(expanded.items.len);
            for (token_buffer.getLeadingTrivia(tok_id)) |piece| {
                try appendExpandedTriviaPiece(allocator, source, piece, &expanded);
            }
            meta_table[tok_idx].leading_end = @intCast(expanded.items.len);
            meta_table[tok_idx].trailing_start = @intCast(expanded.items.len);
            for (token_buffer.getTrailingTrivia(tok_id)) |piece| {
                try appendExpandedTriviaPiece(allocator, source, piece, &expanded);
            }
            meta_table[tok_idx].trailing_end = @intCast(expanded.items.len);
        }
        owned_trivia = try expanded.toOwnedSlice(allocator);
    } else {
        var tok_idx: usize = 0;
        while (tok_idx < token_count) : (tok_idx += 1) {
            const rec = token_buffer.getToken(TokenIndex.fromInt(@intCast(tok_idx)));
            const lead_start: u32 = rec.trivia_span.start_index;
            const lead_end: u32 = lead_start + rec.trivia_span.leading_count;
            meta_table[tok_idx].leading_start = lead_start;
            meta_table[tok_idx].leading_end = lead_end;
            meta_table[tok_idx].trailing_start = lead_end;
            meta_table[tok_idx].trailing_end = lead_end + rec.trivia_span.trailing_count;
        }
    }

    const all_trivia: []const TriviaPiece = if (owned_trivia) |owned| owned else token_buffer.trivia.items;
    var prev_real_tok: ?u32 = null;

    var i: usize = 0;
    while (i < token_count) : (i += 1) {
        const tok_id = TokenIndex.fromInt(@intCast(i));
        const rec = token_buffer.getToken(tok_id);
        var meta = &meta_table[i];
        const lead_start: u32 = meta.leading_start;
        const lead_end: u32 = meta.leading_end;
        const trail_start: u32 = meta.trailing_start;
        const trail_end: u32 = meta.trailing_end;

        // Check any explicit trailing trivia attached directly to `tok_id`:
        var tr_idx: u32 = trail_start;
        while (tr_idx < trail_end) : (tr_idx += 1) {
            if (isCommentOrShebangTrivia(all_trivia[tr_idx].kind)) {
                meta.has_trailing_comments = true;
            }
        }

        // Partition `tok_id`'s leading trivia between `prev_real_tok` trailing and `tok_id` leading:
        if (prev_real_tok) |prev_idx| {
            var first_nl_idx: ?u32 = null;
            var has_comment_before_nl = false;
            var scan_idx: u32 = lead_start;
            while (scan_idx < lead_end) : (scan_idx += 1) {
                const kind = all_trivia[scan_idx].kind;
                if (isNewlineTrivia(kind)) {
                    first_nl_idx = scan_idx;
                    break;
                }
                if (isCommentOrShebangTrivia(kind)) {
                    has_comment_before_nl = true;
                }
            }

            if (first_nl_idx) |nl_idx| {
                meta.has_leading_newline = true;
                if (has_comment_before_nl) {
                    meta_table[prev_idx].stolen_trailing_start = lead_start;
                    meta_table[prev_idx].stolen_trailing_end = nl_idx;
                    meta_table[prev_idx].has_trailing_comments = true;
                    meta.leading_start = nl_idx + 1;
                    meta.has_split_newline = true;
                }
            } else if (rec.kind == .eof and has_comment_before_nl) {
                meta_table[prev_idx].stolen_trailing_start = lead_start;
                meta_table[prev_idx].stolen_trailing_end = lead_end;
                meta_table[prev_idx].has_trailing_comments = true;
                meta.leading_start = lead_end;
            }
        }

        // Compute `has_leading_blank_line`, `has_leading_comments`, and `has_doc_comment` on `meta`:
        var consecutive_newlines: u32 = if (meta.has_split_newline) 1 else 0;
        var has_seen_comment = false;
        var scan_idx: u32 = meta.leading_start;
        while (scan_idx < meta.leading_end) : (scan_idx += 1) {
            const kind = all_trivia[scan_idx].kind;
            if (isNewlineTrivia(kind)) {
                consecutive_newlines += 1;
                if (!has_seen_comment and consecutive_newlines >= 2) {
                    meta.has_leading_blank_line = true;
                }
            } else if (isCommentOrShebangTrivia(kind)) {
                if (!has_seen_comment and consecutive_newlines >= 2) {
                    meta.has_leading_blank_line = true;
                }
                has_seen_comment = true;
                meta.has_leading_comments = true;
                if (kind == .doc_comment or kind == .module_doc_comment) {
                    meta.has_doc_comment = true;
                }
                consecutive_newlines = 0;
            }
        }
        if (!has_seen_comment and consecutive_newlines >= 2) {
            meta.has_leading_blank_line = true;
        }
        if (consecutive_newlines >= 1) {
            meta.has_leading_newline = true;
        }

        if (!rec.flags.is_synthesized and rec.kind != .eof) {
            prev_real_tok = @intCast(i);
        }
    }

    return .{
        .trivia_slice = all_trivia,
        .owned_trivia = owned_trivia,
        .token_meta = meta_table,
    };
}

// ----------------- CST Node & Token Utilities -----------------

/// Checks whether `cst_arena` or `token_buffer` contains unrecoverable syntax errors.
fn hasBlockingSyntaxErrors(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    is_fix_mode: bool,
) bool {
    // [1] Any lexical error (unterminated string/comment/char or invalid byte) blocks formatting:
    const token_count = token_buffer.countTokens();
    var tok_i: usize = 0;
    while (tok_i < token_count) : (tok_i += 1) {
        const rec = token_buffer.getToken(TokenIndex.fromInt(@intCast(tok_i)));
        if (rec.flags.has_lexer_error and !isRenamableIdentifierKind(rec.kind)) return true;
        if (rec.kind == .invalid_token and !rec.flags.is_synthesized) return true;
    }

    // [2] Inspect CST nodes for syntax errors, ignoring single-line trailing comma markers in calls:
    const node_count = cst_arena.countNodes();
    var node_i: usize = 0;
    while (node_i < node_count) : (node_i += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(node_i)));
        if (node.kind == .invalid_parse_subtree) return true;
        if (node.kind == .invalid_parse_leaf) {
            if (!node.token.isNone() and node.flags.is_missing_or_injected) {
                const tok_rec = token_buffer.getToken(node.token);
                if (tok_rec.kind == .comma and !tok_rec.flags.is_synthesized) {
                    continue;
                }
            }
            return true;
        }
        if (node.flags.has_error) {
            if (node.kind == .file_end) continue;
            if (node.kind == .call_expr or node.kind == .view_block_expr or node.kind == .field_or_method_expr) {
                if (isHarmlessTrailingCommaCall(token_buffer, cst_arena, CstNodeIndex.fromInt(@intCast(node_i)))) {
                    continue;
                }
            }
            if (is_fix_mode and isFixableMissingSemicolonNode(token_buffer, cst_arena, CstNodeIndex.fromInt(@intCast(node_i)))) {
                continue;
            }
            return true;
        }
    }
    return false;
}

/// Returns `true` if `call_node_idx` only has `has_error` due to a single-line trailing comma before `)`.
fn isHarmlessTrailingCommaCall(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    call_node_idx: CstNodeIndex,
) bool {
    const root_node = cst_arena.getNode(call_node_idx);
    const end_idx: usize = call_node_idx.asInt() + root_node.subtree_size;
    var has_closing_rparen = false;
    var idx: usize = call_node_idx.asInt() + 1;
    while (idx < end_idx) : (idx += 1) {
        const child = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(idx)));
        if (child.kind == .invalid_parse_subtree) return false;
        if (child.kind == .invalid_parse_leaf) {
            if (child.token.isNone() or !child.flags.is_missing_or_injected) return false;
            const tok_rec = token_buffer.getToken(child.token);
            if (tok_rec.kind != .comma or tok_rec.flags.is_synthesized) return false;
            continue;
        }
        if (child.subtree_size == 1 and !child.token.isNone()) {
            const tok_rec = token_buffer.getToken(child.token);
            if (tok_rec.flags.is_synthesized) return false;
            if (tok_rec.kind == .rparen) {
                has_closing_rparen = true;
            }
        }
    }
    return has_closing_rparen;
}

/// Returns `true` if `node_idx` in `--fix` mode only has `has_error` due to a missing trailing `;`.
fn isFixableMissingSemicolonNode(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    node_idx: CstNodeIndex,
) bool {
    const node = cst_arena.getNode(node_idx);
    switch (node.kind) {
        .local_decl_stmt,
        .return_stmt,
        .break_stmt,
        .continue_stmt,
        .yield_stmt,
        .defer_stmt,
        .assign_stmt,
        .expr_stmt,
        .use_item,
        .const_item,
        .extern_static_item,
        .type_alias_item,
        .mod_item,
        .extern_block_item,
        .fn_item,
        .subscript_item,
        .trait_member,
        .impl_member,
        => {},
        else => return false,
    }
    const end_idx: usize = node_idx.asInt() + node.subtree_size;
    var has_closing_rbrace = false;
    var has_error_child = false;
    var child_idx: usize = node_idx.asInt() + 1;
    while (child_idx < end_idx) : (child_idx += 1) {
        const child_id = CstNodeIndex.fromInt(@intCast(child_idx));
        const child = cst_arena.getNode(child_id);
        if (child.kind == .invalid_parse_subtree or child.kind == .invalid_parse_leaf) {
            return false;
        }
        if (child.flags.has_error) {
            has_error_child = true;
        }
        if (child.subtree_size == 1 and !child.token.isNone()) {
            const tok_rec = token_buffer.getToken(child.token);
            if (tok_rec.flags.is_synthesized and tok_rec.kind != .semi) {
                return false;
            }
            if (!tok_rec.flags.is_synthesized and tok_rec.kind == .rbrace) {
                has_closing_rbrace = true;
            }
        }
    }
    if (node.kind == .extern_block_item) {
        return has_closing_rbrace and has_error_child;
    }
    return true;
}

// ---------------- CstFormatter Implementation -----------------

/// Returns whether `kind` is an identifier token kind eligible for `--fix` casing normalization.
inline fn isRenamableIdentifierKind(kind: TokenKind) bool {
    return kind == .ident or kind == .type_ident or kind == .const_ident;
}

/// Returns whether `kind` is an assignment or compound-assignment operator token.
inline fn isAssignmentOperatorToken(kind: TokenKind) bool {
    return switch (kind) {
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
        => true,
        else => false,
    };
}

/// Stateful CST-to-`DocArena` formatter lowering a `LosslessCstArena` and `TokenBuffer` into `DocInst`s.
const CstFormatter = struct {
    /// Backing allocator for temporary child lists, sort buffers, and `--fix` rename maps.
    allocator: std.mem.Allocator,
    /// Original UTF-8 source buffer.
    source: []const u8,
    /// Token and trivia stream produced by the CoreX lexer.
    token_buffer: *const TokenBuffer,
    /// Lossless Concrete Syntax Tree produced by the CoreX parser.
    cst_arena: *const LosslessCstArena,
    /// Target document algebra arena receiving 8-byte `DocInst` instructions.
    doc_arena: *DocArena,
    /// Active trivia slice (borrowed from `token_buffer` or expanded in `owned_trivia`).
    trivia_slice: []const TriviaPiece,
    /// Owned expanded trivia buffer when `TRIVIA_FLAG_COALESCED` was present (`null` otherwise).
    owned_trivia: ?[]TriviaPiece = null,
    /// Pre-classified per-token trivia metadata table indexed by `TokenIndex.asInt()`.
    token_meta: []TokenTriviaMeta,
    /// Pre-extracted `// corex fmt: off` … `// corex fmt: on` byte ranges.
    suppressed_ranges: std.ArrayList(SuppressedRange),
    /// Role-specific map from original type/trait/variant lexeme to `PascalCase` replacement in `--fix` mode.
    type_rename_map: std.StringHashMapUnmanaged([]const u8) = .empty,
    /// Role-specific map from original constant lexeme to `SCREAMING_SNAKE_CASE` replacement in `--fix` mode.
    const_rename_map: std.StringHashMapUnmanaged([]const u8) = .empty,
    /// Role-specific map from original function/field/variable lexeme to `snake_case` replacement in `--fix` mode.
    value_rename_map: std.StringHashMapUnmanaged([]const u8) = .empty,
    /// Raw lexemes declared as types, traits, or enum variants in this file.
    declared_type_names: std.StringHashMapUnmanaged(void) = .empty,
    /// Raw lexemes declared as constants in this file.
    declared_const_names: std.StringHashMapUnmanaged(void) = .empty,
    /// Raw lexemes declared as functions, fields, parameters, or local bindings in this file.
    declared_value_names: std.StringHashMapUnmanaged(void) = .empty,
    /// Owned string slices allocated for `*_rename_map` values.
    rename_allocations: std.ArrayList([]u8) = .empty,
    /// Nesting depth of syntactic type positions (e.g., `.named_type`, `.type_params`, `.type_args`).
    in_type_context: u32 = 0,
    /// Nesting depth inside `.index_expr` `[…]` brackets for compact `$-K` formatting (`DR-21` §3.3).
    index_bracket_depth: u32 = 0,
    /// Whether `--fix` mode (casing normalization and missing `;` synthesis) is enabled.
    is_fix_mode: bool,

    /// Initializes a `CstFormatter` and runs trivia/suppression/rename pre-passes.
    pub fn init(
        allocator: std.mem.Allocator,
        source: []const u8,
        token_buffer: *const TokenBuffer,
        cst_arena: *const LosslessCstArena,
        doc_arena: *DocArena,
        is_fix_mode: bool,
    ) !CstFormatter {
        const prepared = try buildTokenTriviaMeta(allocator, source, token_buffer);
        errdefer {
            allocator.free(prepared.token_meta);
            if (prepared.owned_trivia) |owned| allocator.free(owned);
        }
        var suppressed_ranges = try extractSuppressedRanges(allocator, source, prepared.trivia_slice);
        errdefer suppressed_ranges.deinit(allocator);

        var self = CstFormatter{
            .allocator = allocator,
            .source = source,
            .token_buffer = token_buffer,
            .cst_arena = cst_arena,
            .doc_arena = doc_arena,
            .trivia_slice = prepared.trivia_slice,
            .owned_trivia = prepared.owned_trivia,
            .token_meta = prepared.token_meta,
            .suppressed_ranges = suppressed_ranges,
            .is_fix_mode = is_fix_mode,
        };
        if (is_fix_mode and cst_arena.countNodes() > 0) {
            try self.collectFixRenames(CstNodeIndex.fromInt(0));
        }
        return self;
    }

    /// Releases temporary trivia metadata, suppression ranges, and `--fix` rename allocations.
    pub fn deinit(self: *CstFormatter) void {
        for (self.rename_allocations.items) |owned_str| {
            self.allocator.free(owned_str);
        }
        self.rename_allocations.deinit(self.allocator);
        self.type_rename_map.deinit(self.allocator);
        self.const_rename_map.deinit(self.allocator);
        self.value_rename_map.deinit(self.allocator);
        self.declared_type_names.deinit(self.allocator);
        self.declared_const_names.deinit(self.allocator);
        self.declared_value_names.deinit(self.allocator);
        self.suppressed_ranges.deinit(self.allocator);
        if (self.owned_trivia) |owned| self.allocator.free(owned);
        self.allocator.free(self.token_meta);
        self.* = undefined;
    }

    /// Returns whether `leaf_node` is a parser-injected duplicate recovery anchor that must be skipped.
    inline fn shouldSkipLeaf(self: *const CstFormatter, leaf_node: CstNodeRecord) bool {
        if (leaf_node.token.isNone()) return true;
        const tok_rec = self.token_buffer.getToken(leaf_node.token);
        if (leaf_node.flags.is_missing_or_injected and !tok_rec.flags.is_synthesized) {
            return true;
        }
        if (tok_rec.kind == .invalid_token and tok_rec.flags.is_synthesized) {
            return true;
        }
        return false;
    }

    /// Returns whether `leaf_node` is a zero-length comment-carrier leaf (`token == .none` or `.eof`).
    inline fn isZeroLengthCommentCarrierLeaf(self: *const CstFormatter, leaf_node: CstNodeRecord) bool {
        if (leaf_node.subtree_size != 1) return false;
        if (leaf_node.token.isNone()) return true;
        const tok_rec = self.token_buffer.getToken(leaf_node.token);
        if (tok_rec.kind == .eof) return true;
        return tok_rec.kind == .invalid_token and tok_rec.flags.is_synthesized and tok_rec.byte_len == 0;
    }

    /// Appends the direct CST children of composite node `parent_idx` into `out_children`.
    fn collectDirectChildren(
        self: *const CstFormatter,
        parent_idx: CstNodeIndex,
        out_children: *std.ArrayList(CstNodeIndex),
    ) !void {
        const parent = self.cst_arena.getNode(parent_idx);
        const end_idx: usize = parent_idx.asInt() + parent.subtree_size;
        var child_cursor: usize = parent_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child_id = CstNodeIndex.fromInt(@intCast(child_cursor));
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1) {
                if (!self.shouldSkipLeaf(child)) {
                    try out_children.append(self.allocator, child_id);
                } else if (!child.token.isNone()) {
                    const tok_rec = self.token_buffer.getToken(child.token);
                    if (tok_rec.kind == .invalid_token and tok_rec.flags.is_synthesized) {
                        // Carrier token; keep in list if it holds comments:
                        const meta = self.token_meta[child.token.asInt()];
                        if (meta.has_leading_comments or meta.has_trailing_comments) {
                            try out_children.append(self.allocator, child_id);
                        }
                    }
                }
            } else {
                try out_children.append(self.allocator, child_id);
            }
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
    }

    /// Returns the first real (non-synthesized) `TokenIndex` inside `node_idx`'s subtree, or `.none`.
    fn findFirstTokenInSubtree(self: *const CstFormatter, node_idx: CstNodeIndex) TokenIndex {
        const root = self.cst_arena.getNode(node_idx);
        if (root.subtree_size == 1) {
            if (!self.shouldSkipLeaf(root)) return root.token;
            return .none;
        }
        const end_idx: usize = node_idx.asInt() + root.subtree_size;
        var idx: usize = node_idx.asInt() + 1;
        while (idx < end_idx) : (idx += 1) {
            const node = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(idx)));
            if (node.subtree_size == 1 and !self.shouldSkipLeaf(node)) {
                const tok_rec = self.token_buffer.getToken(node.token);
                if (!tok_rec.flags.is_synthesized) return node.token;
            }
        }
        return root.token;
    }

    /// Returns the last real (non-synthesized) `TokenIndex` inside `node_idx`'s subtree, or `.none`.
    fn findLastTokenInSubtree(self: *const CstFormatter, node_idx: CstNodeIndex) TokenIndex {
        const root = self.cst_arena.getNode(node_idx);
        if (root.subtree_size == 1) {
            if (!self.shouldSkipLeaf(root)) return root.token;
            return .none;
        }
        const end_idx: usize = node_idx.asInt() + root.subtree_size;
        var last_tok: TokenIndex = .none;
        var idx: usize = node_idx.asInt() + 1;
        while (idx < end_idx) : (idx += 1) {
            const node = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(idx)));
            if (node.subtree_size == 1 and !self.shouldSkipLeaf(node)) {
                const tok_rec = self.token_buffer.getToken(node.token);
                if (!tok_rec.flags.is_synthesized) {
                    last_tok = node.token;
                }
            }
        }
        return last_tok;
    }

    /// Returns the raw UTF-8 lexeme of `tok_id` in `self.source`.
    inline fn getTokenLexeme(self: *const CstFormatter, tok_id: TokenIndex) []const u8 {
        if (tok_id.isNone()) return "";
        const rec = self.token_buffer.getToken(tok_id);
        if (rec.flags.is_synthesized) return "";
        const start: usize = rec.byte_offset;
        const end: usize = @min(self.source.len, start + rec.byte_len);
        return self.source[start..end];
    }

    /// Returns the starting byte offset of `node_idx` (including its leading comments if present).
    fn getNodeLeadingStartByte(self: *const CstFormatter, node_idx: CstNodeIndex) u32 {
        const first_tok = self.findFirstTokenInSubtree(node_idx);
        if (first_tok.isNone()) return 0;
        const meta = self.token_meta[first_tok.asInt()];
        const all_trivia = self.trivia_slice;
        var idx: u32 = meta.leading_start;
        while (idx < meta.leading_end) : (idx += 1) {
            if (isCommentOrShebangTrivia(all_trivia[idx].kind)) {
                return all_trivia[idx].byte_offset;
            }
        }
        return self.token_buffer.getToken(first_tok).byte_offset;
    }

    /// Returns the ending byte offset of `node_idx` (including any same-line trailing comments).
    fn getNodeTrailingEndByte(self: *const CstFormatter, node_idx: CstNodeIndex) u32 {
        const last_tok = self.findLastTokenInSubtree(node_idx);
        if (last_tok.isNone()) return 0;
        const rec = self.token_buffer.getToken(last_tok);
        var max_end: u32 = rec.byte_offset + rec.byte_len;
        const meta = self.token_meta[last_tok.asInt()];
        const all_trivia = self.trivia_slice;
        for (all_trivia[meta.trailing_start..meta.trailing_end]) |piece| {
            if (isCommentOrShebangTrivia(piece.kind)) {
                max_end = @max(max_end, piece.byte_offset + piece.byte_len);
            }
        }
        var idx: u32 = meta.stolen_trailing_start;
        while (idx < meta.stolen_trailing_end) : (idx += 1) {
            const piece = all_trivia[idx];
            if (isCommentOrShebangTrivia(piece.kind)) {
                max_end = @max(max_end, piece.byte_offset + piece.byte_len);
            }
        }
        return max_end;
    }

    /// Returns whether `node_idx` is preceded by a user blank line (`>= 2` consecutive newlines).
    fn hasNodeLeadingBlankLine(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        const first_tok = self.findFirstTokenInSubtree(node_idx);
        if (first_tok.isNone()) return false;
        return self.token_meta[first_tok.asInt()].has_leading_blank_line;
    }

    /// Returns whether `node_idx` has an outer `///` or `//!` doc comment attached to its first token.
    fn hasNodeDocComment(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        const first_tok = self.findFirstTokenInSubtree(node_idx);
        if (first_tok.isNone()) return false;
        return self.token_meta[first_tok.asInt()].has_doc_comment;
    }

    /// Returns whether `node_idx`'s tokens span across more than a single source line.
    fn isNodeMultilineInSource(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        const first_tok = self.findFirstTokenInSubtree(node_idx);
        const last_tok = self.findLastTokenInSubtree(node_idx);
        if (first_tok.isNone() or last_tok.isNone()) return false;
        const start_byte: usize = self.token_buffer.getToken(first_tok).byte_offset;
        const end_rec = self.token_buffer.getToken(last_tok);
        const end_byte: usize = @min(self.source.len, @as(usize, end_rec.byte_offset) + end_rec.byte_len);
        if (start_byte >= end_byte) return false;
        return std.mem.indexOfScalar(u8, self.source[start_byte..end_byte], '\n') != null;
    }

    /// Returns whether any token in `[start_tok .. end_tok]` has unconsumed leading or trailing comments.
    fn hasUnconsumedCommentsInTokenRange(
        self: *const CstFormatter,
        start_tok: u32,
        end_tok: u32,
        has_end_leading_included: bool,
        has_start_trailing_included: bool,
    ) bool {
        if (start_tok >= self.token_meta.len) return false;
        if (has_start_trailing_included) {
            const start_meta = self.token_meta[start_tok];
            if (!start_meta.is_trailing_consumed and start_meta.has_trailing_comments) return true;
        }
        var tok_i: u32 = start_tok + 1;
        const limit: u32 = @min(end_tok, @as(u32, @intCast(self.token_meta.len)));
        while (tok_i < limit) : (tok_i += 1) {
            const meta = self.token_meta[tok_i];
            if (!meta.is_leading_consumed and meta.has_leading_comments) return true;
            if (!meta.is_trailing_consumed and meta.has_trailing_comments) return true;
        }
        if (has_end_leading_included and end_tok < self.token_meta.len) {
            const end_meta = self.token_meta[end_tok];
            if (!end_meta.is_leading_consumed and end_meta.has_leading_comments) return true;
        }
        return false;
    }

    /// Returns whether `tok_id` has unconsumed leading comments.
    inline fn hasUnconsumedLeadingComments(self: *const CstFormatter, tok_id: TokenIndex) bool {
        if (tok_id.isNone() or tok_id.asInt() >= self.token_meta.len) return false;
        const meta = self.token_meta[tok_id.asInt()];
        return !meta.is_leading_consumed and meta.has_leading_comments;
    }

    /// Returns whether the document instruction stream is currently at the start of a line.
    fn hasTrailingNewlineInstruction(self: *const CstFormatter) bool {
        const insts = self.doc_arena.instructions.items;
        var idx: usize = insts.len;
        while (idx > 0) {
            idx -= 1;
            switch (insts[idx].op) {
                .nop, .indent, .dedent, .group_begin, .group_end => continue,
                .hard_line, .blank_line => return true,
                else => return false,
            }
        }
        return true;
    }

    /// Emits all unconsumed leading comments of `tok_id` into `self.doc_arena`.
    fn emitLeadingTrivia(
        self: *CstFormatter,
        tok_id: TokenIndex,
        is_blank_line_allowed: bool,
    ) !void {
        if (tok_id.isNone() or tok_id.asInt() >= self.token_meta.len) return;
        var meta = &self.token_meta[tok_id.asInt()];
        if (meta.is_leading_consumed) return;
        meta.is_leading_consumed = true;

        if (!meta.has_leading_comments) return;

        const all_trivia = self.trivia_slice;
        var newline_count: u32 = if (meta.has_split_newline) 1 else 0;
        var has_emitted_any_comment = false;
        var last_was_line_comment = false;

        var idx: u32 = meta.leading_start;
        while (idx < meta.leading_end) : (idx += 1) {
            const piece = all_trivia[idx];
            if (isNewlineTrivia(piece.kind)) {
                newline_count += 1;
                continue;
            }
            if (!isCommentOrShebangTrivia(piece.kind)) continue;

            const start: usize = piece.byte_offset;
            const end: usize = @min(self.source.len, start + piece.byte_len);
            const raw_slice = self.source[start..end];
            const trimmed = std.mem.trimEnd(u8, raw_slice, " \t\r\n");

            if (has_emitted_any_comment) {
                if (is_blank_line_allowed and newline_count >= 2) {
                    try self.doc_arena.emitBlankLine();
                } else if (last_was_line_comment or newline_count >= 1) {
                    try self.doc_arena.emitHardLine();
                } else {
                    try self.doc_arena.emitText(" ");
                }
            } else if ((piece.kind != .block_comment or newline_count >= 1) and
                self.doc_arena.instructions.items.len > 0 and
                !self.hasTrailingNewlineInstruction())
            {
                if (is_blank_line_allowed and newline_count >= 2) {
                    try self.doc_arena.emitBlankLine();
                } else {
                    try self.doc_arena.emitHardLine();
                }
            }

            try self.doc_arena.emitText(trimmed);
            has_emitted_any_comment = true;
            last_was_line_comment = (piece.kind != .block_comment);
            newline_count = 0;
        }

        if (has_emitted_any_comment) {
            if (is_blank_line_allowed and newline_count >= 2) {
                try self.doc_arena.emitBlankLine();
            } else if (last_was_line_comment or newline_count >= 1) {
                try self.doc_arena.emitHardLine();
            } else {
                const tok_rec = self.token_buffer.getToken(tok_id);
                if (tok_rec.kind != .eof and !tok_rec.flags.is_synthesized) {
                    try self.doc_arena.emitText(" ");
                }
            }
        }
    }

    /// Emits all unconsumed same-line trailing comments of `tok_id` as `line_suffix` instructions.
    fn emitTrailingTrivia(self: *CstFormatter, tok_id: TokenIndex) !void {
        if (tok_id.isNone() or tok_id.asInt() >= self.token_meta.len) return;
        var meta = &self.token_meta[tok_id.asInt()];
        if (meta.is_trailing_consumed) return;
        meta.is_trailing_consumed = true;

        if (!meta.has_trailing_comments) return;

        const all_trivia = self.trivia_slice;
        for (all_trivia[meta.trailing_start..meta.trailing_end]) |piece| {
            if (!isCommentOrShebangTrivia(piece.kind)) continue;
            const start: usize = piece.byte_offset;
            const end: usize = @min(self.source.len, start + piece.byte_len);
            try self.doc_arena.emitLineSuffix(self.source[start..end]);
        }

        var idx: u32 = meta.stolen_trailing_start;
        while (idx < meta.stolen_trailing_end) : (idx += 1) {
            const piece = all_trivia[idx];
            if (!isCommentOrShebangTrivia(piece.kind)) continue;
            const start: usize = piece.byte_offset;
            const end: usize = @min(self.source.len, start + piece.byte_len);
            try self.doc_arena.emitLineSuffix(self.source[start..end]);
        }
    }

    /// Flushes any unconsumed leading or trailing comments on tokens in `[start_tok .. end_tok)`.
    fn flushUnconsumedCommentsInRange(
        self: *CstFormatter,
        start_tok: u32,
        end_tok: u32,
        is_blank_line_allowed: bool,
    ) !void {
        const limit: u32 = @min(end_tok, @as(u32, @intCast(self.token_meta.len)));
        var tok_i: u32 = start_tok;
        while (tok_i < limit) : (tok_i += 1) {
            const tok_id = TokenIndex.fromInt(tok_i);
            const meta = self.token_meta[tok_i];
            const has_lead = !meta.is_leading_consumed and meta.has_leading_comments;
            const has_trail = !meta.is_trailing_consumed and meta.has_trailing_comments;
            if (!has_lead and !has_trail) continue;

            if (has_lead) {
                if (self.doc_arena.instructions.items.len > 0 and !self.hasTrailingNewlineInstruction()) {
                    if (is_blank_line_allowed and meta.has_leading_blank_line) {
                        try self.doc_arena.emitBlankLine();
                    } else {
                        try self.doc_arena.emitHardLine();
                    }
                }
                try self.emitLeadingTrivia(tok_id, is_blank_line_allowed);
                if (!has_trail and !self.hasTrailingNewlineInstruction()) {
                    try self.doc_arena.emitHardLine();
                }
            }
            if (has_trail) {
                if (!has_lead and meta.has_leading_newline and
                    self.doc_arena.instructions.items.len > 0 and
                    !self.hasTrailingNewlineInstruction())
                {
                    if (is_blank_line_allowed and meta.has_leading_blank_line) {
                        try self.doc_arena.emitBlankLine();
                    } else {
                        try self.doc_arena.emitHardLine();
                    }
                }
                try self.emitTrailingTrivia(tok_id);
                try self.doc_arena.emitHardLine();
            }
        }
    }

    /// Resolves the output text for `tok_id`, applying role-aware `--fix` renaming when active.
    fn resolveIdentifierFixText(self: *const CstFormatter, tok_id: TokenIndex, kind: TokenKind) []const u8 {
        const raw_lexeme = self.getTokenLexeme(tok_id);
        if (!self.is_fix_mode or !isRenamableIdentifierKind(kind)) return raw_lexeme;

        const role = self.token_meta[tok_id.asInt()].decl_role;
        switch (role) {
            .type_decl => return self.type_rename_map.get(raw_lexeme) orelse raw_lexeme,
            .const_decl => return self.const_rename_map.get(raw_lexeme) orelse raw_lexeme,
            .value_decl => return self.value_rename_map.get(raw_lexeme) orelse raw_lexeme,
            .none => {
                if (self.in_type_context > 0) {
                    if (self.declared_type_names.contains(raw_lexeme)) {
                        return self.type_rename_map.get(raw_lexeme) orelse raw_lexeme;
                    }
                    if (self.declared_const_names.contains(raw_lexeme)) {
                        return self.const_rename_map.get(raw_lexeme) orelse raw_lexeme;
                    }
                    return self.type_rename_map.get(raw_lexeme) orelse raw_lexeme;
                }
                if (self.declared_value_names.contains(raw_lexeme)) {
                    return self.value_rename_map.get(raw_lexeme) orelse raw_lexeme;
                }
                if (self.declared_const_names.contains(raw_lexeme)) {
                    return self.const_rename_map.get(raw_lexeme) orelse raw_lexeme;
                }
                if (self.declared_type_names.contains(raw_lexeme)) {
                    return self.type_rename_map.get(raw_lexeme) orelse raw_lexeme;
                }
                return raw_lexeme;
            },
        }
    }

    /// Computes the leading horizontal column indentation of the line containing `byte_offset` in `self.source`.
    fn computeLineIndentAtByte(self: *const CstFormatter, byte_offset: u32) u32 {
        const clamped_off: usize = @min(self.source.len, @as(usize, byte_offset));
        var line_start: usize = clamped_off;
        while (line_start > 0 and self.source[line_start - 1] != '\n') : (line_start -= 1) {}
        var indent_cols: u32 = 0;
        var scan_idx: usize = line_start;
        while (scan_idx < self.source.len) : (scan_idx += 1) {
            if (self.source[scan_idx] == ' ') {
                indent_cols += 1;
            } else if (self.source[scan_idx] == '\t') {
                indent_cols += INDENT_SPACES;
            } else {
                break;
            }
        }
        return indent_cols;
    }

    /// Emits `tok_id`'s leading trivia and glyph text without consuming its trailing trivia yet.
    fn emitTokenLeadingAndGlyph(
        self: *CstFormatter,
        tok_id: TokenIndex,
        override_text: ?[]const u8,
        is_blank_line_allowed: bool,
    ) !void {
        if (tok_id.isNone()) return;
        try self.emitLeadingTrivia(tok_id, is_blank_line_allowed);
        const rec = self.token_buffer.getToken(tok_id);
        self.token_meta[tok_id.asInt()].is_token_emitted = true;

        if (override_text) |custom_str| {
            try self.doc_arena.emitText(custom_str);
        } else if (!rec.flags.is_synthesized and rec.kind != .eof) {
            if (!rec.flags.has_lexer_error and (rec.kind == .int_lit or rec.kind == .float_lit)) {
                const raw_num = self.getTokenLexeme(tok_id);
                if (lexer.extractNumericSuffix(raw_num)) |parsed_num| {
                    if (parsed_num.suffix_type != null and !parsed_num.has_underscore_sep) {
                        try self.doc_arena.emitText(parsed_num.digits_slice);
                        try self.doc_arena.emitText("_");
                        try self.doc_arena.emitText(parsed_num.suffix_slice);
                        return;
                    }
                } else |_| {}
            }
            if (!rec.flags.has_lexer_error and
                (rec.kind == .string_lit or rec.kind == .byte_string_lit))
            {
                const raw_str = self.getTokenLexeme(tok_id);
                if (extractMultilineTripleQuoteParts(raw_str) != null) {
                    try self.doc_arena.emitMultilineString(
                        raw_str,
                        self.computeLineIndentAtByte(rec.byte_offset),
                    );
                    return;
                }
            }
            try self.doc_arena.emitText(self.resolveIdentifierFixText(tok_id, rec.kind));
        }
    }

    /// Emits a token leaf (with its leading and trailing trivia), applying `--fix` casing if active.
    fn emitTokenWithTrivia(
        self: *CstFormatter,
        tok_id: TokenIndex,
        override_text: ?[]const u8,
        is_blank_line_allowed: bool,
    ) !void {
        if (tok_id.isNone()) return;
        try self.emitTokenLeadingAndGlyph(tok_id, override_text, is_blank_line_allowed);
        try self.emitTrailingTrivia(tok_id);
    }

    /// Formats an empty delimiter pair (`{}`, `()`, `[]`), preserving any dangling inner comments.
    fn formatEmptyContainer(
        self: *CstFormatter,
        open_tok: TokenIndex,
        close_tok: TokenIndex,
        open_str: []const u8,
        close_str: []const u8,
    ) !void {
        if (!open_tok.isNone()) {
            try self.emitLeadingTrivia(open_tok, false);
            self.token_meta[open_tok.asInt()].is_token_emitted = true;
        }
        try self.doc_arena.emitText(open_str);

        const has_dangling = if (!open_tok.isNone() and !close_tok.isNone())
            self.hasUnconsumedCommentsInTokenRange(open_tok.asInt(), close_tok.asInt(), true, true)
        else
            false;

        if (has_dangling) {
            try self.doc_arena.beginIndent(INDENT_SPACES);
            if (!open_tok.isNone()) {
                try self.emitTrailingTrivia(open_tok);
            }
            try self.doc_arena.emitHardLine();
            try self.flushUnconsumedCommentsInRange(open_tok.asInt() + 1, close_tok.asInt(), true);
            if (self.hasUnconsumedLeadingComments(close_tok)) {
                if (!self.hasTrailingNewlineInstruction()) {
                    try self.doc_arena.emitHardLine();
                }
                try self.emitLeadingTrivia(close_tok, true);
            }
            try self.doc_arena.endIndent(INDENT_SPACES);
            try self.doc_arena.emitHardLine();
        } else {
            if (!open_tok.isNone()) {
                try self.emitTrailingTrivia(open_tok);
            }
            if (!close_tok.isNone()) {
                try self.emitLeadingTrivia(close_tok, false);
            }
        }

        try self.doc_arena.emitText(close_str);
        if (!close_tok.isNone()) {
            self.token_meta[close_tok.asInt()].is_token_emitted = true;
            try self.emitTrailingTrivia(close_tok);
        }
    }

    /// Marks all tokens, trivia, and suppression directives in `[start_byte .. end_byte]` as consumed.
    fn markByteRangeConsumed(self: *CstFormatter, start_byte: u32, end_byte: u32) void {
        for (self.suppressed_ranges.items) |*supp| {
            if (supp.off_start >= start_byte and supp.off_start < end_byte) {
                supp.is_emitted = true;
            }
        }

        const all_trivia = self.trivia_slice;
        const token_count = self.token_buffer.countTokens();
        var i: usize = 0;
        while (i < token_count) : (i += 1) {
            const tok_id = TokenIndex.fromInt(@intCast(i));
            const rec = self.token_buffer.getToken(tok_id);
            var meta = &self.token_meta[i];

            if (!rec.flags.is_synthesized and rec.byte_offset >= start_byte and rec.byte_offset < end_byte) {
                meta.is_token_emitted = true;
                meta.is_leading_consumed = true;
                meta.is_trailing_consumed = true;
                continue;
            }
            if (meta.leading_start < meta.leading_end) {
                var has_advanced_lead = false;
                while (meta.leading_start < meta.leading_end) {
                    const piece = all_trivia[meta.leading_start];
                    if (piece.byte_offset >= start_byte and piece.byte_offset < end_byte) {
                        meta.leading_start += 1;
                        has_advanced_lead = true;
                    } else {
                        break;
                    }
                }
                if (meta.leading_start >= meta.leading_end) {
                    meta.is_leading_consumed = true;
                    meta.has_leading_comments = false;
                    meta.has_doc_comment = false;
                } else if (has_advanced_lead) {
                    meta.has_split_newline = false;
                    meta.has_leading_blank_line = false;
                    meta.has_leading_newline = false;
                    meta.has_leading_comments = false;
                    meta.has_doc_comment = false;
                    var consecutive_newlines: u32 = 0;
                    var has_seen_comment = false;
                    var scan_idx: u32 = meta.leading_start;
                    while (scan_idx < meta.leading_end) : (scan_idx += 1) {
                        const kind = all_trivia[scan_idx].kind;
                        if (isNewlineTrivia(kind)) {
                            consecutive_newlines += 1;
                            if (!has_seen_comment and consecutive_newlines >= 2) {
                                meta.has_leading_blank_line = true;
                            }
                        } else if (isCommentOrShebangTrivia(kind)) {
                            if (!has_seen_comment and consecutive_newlines >= 2) {
                                meta.has_leading_blank_line = true;
                            }
                            has_seen_comment = true;
                            meta.has_leading_comments = true;
                            if (kind == .doc_comment or kind == .module_doc_comment) {
                                meta.has_doc_comment = true;
                            }
                            consecutive_newlines = 0;
                        }
                    }
                    if (!has_seen_comment and consecutive_newlines >= 2) {
                        meta.has_leading_blank_line = true;
                    }
                    if (consecutive_newlines >= 1) {
                        meta.has_leading_newline = true;
                    }
                }
            }
            if (meta.stolen_trailing_start < meta.stolen_trailing_end) {
                const first_tr = all_trivia[meta.stolen_trailing_start];
                const last_tr = all_trivia[meta.stolen_trailing_end - 1];
                if (first_tr.byte_offset >= start_byte and
                    last_tr.byte_offset + last_tr.byte_len <= end_byte)
                {
                    meta.is_trailing_consumed = true;
                }
            }
        }
    }

    /// Checks if `siblings[index]` starts inside a `// corex fmt: off` range or has `@fmt_off`.
    fn tryEmitSuppressedSiblingSpan(
        self: *CstFormatter,
        siblings: []const CstNodeIndex,
        index: *usize,
    ) !bool {
        const curr_node = siblings[index.*];

        // [1] Check for `@fmt_off` attribute directly on `curr_node`:
        if (self.hasFmtOffAttribute(curr_node)) {
            const start_byte = self.getNodeLeadingStartByte(curr_node);
            const end_byte = self.getNodeTrailingEndByte(curr_node);
            if (end_byte > start_byte and end_byte <= self.source.len) {
                self.markByteRangeConsumed(start_byte, end_byte);
                try self.doc_arena.emitVerbatimText(self.source[start_byte..end_byte]);
                index.* += 1;
                return true;
            }
        }

        // [2] Check `// corex fmt: off` … `// corex fmt: on` directives:
        const node_lead_byte = self.getNodeLeadingStartByte(curr_node);
        const node_end_byte = self.getNodeTrailingEndByte(curr_node);

        for (self.suppressed_ranges.items) |*supp| {
            if (supp.is_emitted) continue;
            if (supp.off_start <= node_end_byte and supp.on_end >= node_lead_byte) {
                supp.is_emitted = true;
                var max_on_end: u32 = supp.on_end;
                var last_idx = index.*;
                while (true) {
                    var has_advanced = false;
                    while (last_idx + 1 < siblings.len) {
                        const next_first_tok = self.findFirstTokenInSubtree(siblings[last_idx + 1]);
                        if (next_first_tok.isNone()) break;
                        const next_rec = self.token_buffer.getToken(next_first_tok);
                        if (next_rec.kind != .eof and next_rec.byte_offset < max_on_end) {
                            last_idx += 1;
                            has_advanced = true;
                        } else {
                            break;
                        }
                    }
                    const cur_end = @max(max_on_end, self.getNodeTrailingEndByte(siblings[last_idx]));
                    for (self.suppressed_ranges.items) |*other_supp| {
                        if (!other_supp.is_emitted and
                            other_supp.off_start <= cur_end and
                            other_supp.on_end >= node_lead_byte)
                        {
                            other_supp.is_emitted = true;
                            if (other_supp.on_end > max_on_end) {
                                max_on_end = other_supp.on_end;
                                has_advanced = true;
                            }
                        }
                    }
                    if (!has_advanced) break;
                }
                const slice_start: usize = @min(node_lead_byte, supp.off_start);
                const slice_end: usize = @min(
                    self.source.len,
                    @max(@as(usize, max_on_end), @as(usize, self.getNodeTrailingEndByte(siblings[last_idx]))),
                );
                self.markByteRangeConsumed(@intCast(slice_start), @intCast(slice_end));
                try self.doc_arena.emitVerbatimText(self.source[slice_start..slice_end]);
                index.* = last_idx + 1;
                return true;
            }
        }
        return false;
    }

    /// Returns whether `node_idx` has a direct `@fmt_off` `.attribute` child.
    fn hasFmtOffAttribute(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        const node = self.cst_arena.getNode(node_idx);
        if (node.subtree_size <= 1) return false;
        const end_idx: usize = node_idx.asInt() + node.subtree_size;
        var child_cursor: usize = node_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child_id = CstNodeIndex.fromInt(@intCast(child_cursor));
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                const attr_end: usize = child_cursor + child.subtree_size;
                var tok_cursor: usize = child_cursor + 1;
                while (tok_cursor < attr_end) : (tok_cursor += 1) {
                    const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(tok_cursor)));
                    if (leaf.subtree_size == 1 and !leaf.token.isNone()) {
                        if (std.mem.eql(u8, self.getTokenLexeme(leaf.token), "fmt_off")) return true;
                    }
                }
            }
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
        return false;
    }

    /// Returns `true` if `node_idx` (`.fn_item`) carries `@constructor` or `@builder_item` (`SE-22`).
    fn hasPascalExemptFnAttr(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        const node = self.cst_arena.getNode(node_idx);
        const end_idx: usize = node_idx.asInt() + node.subtree_size;
        var child_cursor: usize = node_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child_id = CstNodeIndex.fromInt(@intCast(child_cursor));
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                const attr_end: usize = child_cursor + child.subtree_size;
                var tok_cursor: usize = child_cursor + 1;
                while (tok_cursor < attr_end) : (tok_cursor += 1) {
                    const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(tok_cursor)));
                    if (leaf.subtree_size == 1 and !leaf.token.isNone()) {
                        const kind = self.token_buffer.getToken(leaf.token).kind;
                        if (kind == .at) continue;
                        const lex = self.getTokenLexeme(leaf.token);
                        if (std.mem.eql(u8, lex, "constructor") or std.mem.eql(u8, lex, "builder_item")) {
                            return true;
                        }
                        break;
                    }
                }
            }
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
        return false;
    }

    /// Pre-scans declarations in `--fix` mode to build the `old_name -> new_name` casing rename map.
    fn collectFixRenames(self: *CstFormatter, root_idx: CstNodeIndex) !void {
        const total_nodes = self.cst_arena.countNodes();
        var exempt_fn_end_idx: usize = 0;
        var extern_fn_end_idx: usize = 0;
        var extern_block_end_idx: usize = 0;
        var idx: usize = root_idx.asInt();
        while (idx < total_nodes) : (idx += 1) {
            const node_id = CstNodeIndex.fromInt(@intCast(idx));
            const node = self.cst_arena.getNode(node_id);
            switch (node.kind) {
                .extern_block_item => {
                    extern_block_end_idx = @max(
                        extern_block_end_idx,
                        idx + @max(@as(usize, 1), node.subtree_size),
                    );
                },
                .fn_item => {
                    const fn_end_idx = idx + @max(@as(usize, 1), node.subtree_size);
                    if (idx < extern_block_end_idx or self.hasDirectTokenKind(node_id, .kw_extern)) {
                        extern_fn_end_idx = @max(extern_fn_end_idx, fn_end_idx);
                    } else if (self.hasPascalExemptFnAttr(node_id)) {
                        exempt_fn_end_idx = @max(exempt_fn_end_idx, fn_end_idx);
                    }
                },
                .struct_item, .union_item, .enum_item, .trait_item, .type_alias_item => {
                    if (self.findDeclIdentifierToken(node_id)) |tok_id| {
                        try self.registerFixRename(tok_id, .pascal_case);
                    }
                },
                .enum_variant => {
                    if (self.findFirstIdentTokenInDirectChildren(node_id)) |tok_id| {
                        try self.registerFixRename(tok_id, .pascal_case);
                    }
                },
                .type_param => {
                    if (!self.hasDirectTokenKind(node_id, .kw_const)) {
                        if (self.findFirstIdentTokenInDirectChildren(node_id)) |tok_id| {
                            try self.registerFixRename(tok_id, .pascal_case);
                        }
                    } else if (self.findFirstIdentTokenInDirectChildren(node_id)) |tok_id| {
                        try self.registerFixRename(tok_id, .screaming_snake_case);
                    }
                },
                .const_item => {
                    if (self.findDeclIdentifierToken(node_id)) |tok_id| {
                        try self.registerFixRename(tok_id, .screaming_snake_case);
                    }
                },
                .fn_sig => {
                    if (self.findFirstIdentTokenInDirectChildren(node_id)) |tok_id| {
                        const is_extern_exempt = idx < extern_fn_end_idx;
                        const is_pascal_exempt = idx < exempt_fn_end_idx and
                            self.token_buffer.getToken(tok_id).kind == .type_ident;
                        if (!is_extern_exempt and !is_pascal_exempt) {
                            try self.registerFixRename(tok_id, .snake_case);
                        }
                    }
                },
                .struct_field, .fn_param, .closure_param, .mod_item, .loop_label, .at_pat => {
                    if (self.findFirstIdentTokenInDirectChildren(node_id)) |tok_id| {
                        try self.registerFixRename(tok_id, .snake_case);
                    }
                },
                .walrus_cond_expr => {
                    if (self.findWalrusIdentToken(node_id)) |tok_id| {
                        try self.registerFixRename(tok_id, .snake_case);
                    }
                },
                .for_header => {
                    try self.registerForHeaderFixRenames(node_id);
                },
                .local_decl_stmt => {
                    if (self.findLocalDeclIdentToken(node_id)) |tok_id| {
                        try self.registerFixRename(tok_id, .snake_case);
                    }
                },
                .use_tree => {
                    if (self.findInlineUseAliasIdentToken(node_id)) |tok_id| {
                        try self.registerFixRename(tok_id, .snake_case);
                    }
                },
                else => {},
            }
        }
    }

    /// Target casing convention for `--fix` identifier normalization.
    const TargetCase = enum {
        pascal_case,
        snake_case,
        screaming_snake_case,
    };

    /// Converts `tok_id`'s lexeme to `target_case` and records it in the role-specific rename map.
    fn registerFixRename(self: *CstFormatter, tok_id: TokenIndex, target_case: TargetCase) !void {
        if (tok_id.isNone()) return;
        const rec = self.token_buffer.getToken(tok_id);
        if (rec.flags.is_synthesized or rec.flags.has_lexer_error or !isRenamableIdentifierKind(rec.kind)) return;
        const raw_name = self.getTokenLexeme(tok_id);
        if (raw_name.len == 0 or std.mem.eql(u8, raw_name, "_") or std.mem.eql(u8, raw_name, "self") or
            std.mem.eql(u8, raw_name, "Self") or std.mem.eql(u8, raw_name, "subscript"))
        {
            return;
        }
        switch (target_case) {
            .pascal_case => {
                self.token_meta[tok_id.asInt()].decl_role = .type_decl;
                try self.declared_type_names.put(self.allocator, raw_name, {});
            },
            .screaming_snake_case => {
                self.token_meta[tok_id.asInt()].decl_role = .const_decl;
                try self.declared_const_names.put(self.allocator, raw_name, {});
            },
            .snake_case => {
                self.token_meta[tok_id.asInt()].decl_role = .value_decl;
                try self.declared_value_names.put(self.allocator, raw_name, {});
            },
        }
        const converted = switch (target_case) {
            .pascal_case => try lexer.toPascalCase(self.allocator, raw_name),
            .snake_case => try lexer.toSnakeCase(self.allocator, raw_name),
            .screaming_snake_case => try lexer.toScreamingSnakeCase(self.allocator, raw_name),
        };
        if (std.mem.eql(u8, raw_name, converted)) {
            self.allocator.free(converted);
            return;
        }
        try self.rename_allocations.append(self.allocator, converted);
        switch (target_case) {
            .pascal_case => try self.type_rename_map.put(self.allocator, raw_name, converted),
            .screaming_snake_case => try self.const_rename_map.put(self.allocator, raw_name, converted),
            .snake_case => try self.value_rename_map.put(self.allocator, raw_name, converted),
        }
    }

    /// Finds the declaration identifier token immediately following an item introducer keyword.
    fn findDeclIdentifierToken(self: *const CstFormatter, item_idx: CstNodeIndex) ?TokenIndex {
        const item = self.cst_arena.getNode(item_idx);
        const end_idx: usize = item_idx.asInt() + item.subtree_size;
        var seen_introducer = false;
        var child_cursor: usize = item_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_cursor)));
            if (child.subtree_size == 1 and !self.shouldSkipLeaf(child)) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (seen_introducer and isRenamableIdentifierKind(tok_kind)) {
                    return child.token;
                }
                switch (child.kind) {
                    .struct_introducer,
                    .union_introducer,
                    .enum_introducer,
                    .trait_introducer,
                    .type_alias_introducer,
                    .const_introducer,
                    .mod_introducer,
                    => seen_introducer = true,
                    else => {},
                }
            }
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
        return null;
    }

    /// Finds the first identifier token among the direct leaf children of `node_idx`.
    fn findFirstIdentTokenInDirectChildren(self: *const CstFormatter, node_idx: CstNodeIndex) ?TokenIndex {
        const node = self.cst_arena.getNode(node_idx);
        const end_idx: usize = node_idx.asInt() + node.subtree_size;
        var child_cursor: usize = node_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_cursor)));
            if (child.subtree_size == 1 and !self.shouldSkipLeaf(child)) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (isRenamableIdentifierKind(tok_kind)) {
                    return child.token;
                }
            }
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
        return null;
    }

    /// Finds the bound identifier token inside a `local_decl_stmt` (`let [mut] ident = …`).
    fn findLocalDeclIdentToken(self: *const CstFormatter, decl_idx: CstNodeIndex) ?TokenIndex {
        const decl = self.cst_arena.getNode(decl_idx);
        const end_idx: usize = decl_idx.asInt() + decl.subtree_size;
        var child_cursor: usize = decl_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child_id = CstNodeIndex.fromInt(@intCast(child_cursor));
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .ident_pat) {
                if (child.subtree_size == 1 and !self.shouldSkipLeaf(child)) {
                    return child.token;
                }
                return self.findFirstIdentTokenInDirectChildren(child_id);
            }
            if (child.subtree_size == 1 and !self.shouldSkipLeaf(child)) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .colon or tok_kind == .eq) break;
            }
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
        return null;
    }

    /// Finds the `<snake_alias>` identifier token inside an inline `use "<spec>" as <alias>;` `.use_tree`.
    fn findInlineUseAliasIdentToken(self: *const CstFormatter, tree_idx: CstNodeIndex) ?TokenIndex {
        const tree = self.cst_arena.getNode(tree_idx);
        const end_idx: usize = tree_idx.asInt() + tree.subtree_size;
        var has_leading_string = false;
        var has_seen_as = false;
        var child_cursor: usize = tree_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_cursor)));
            if (child.subtree_size == 1 and !self.shouldSkipLeaf(child)) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (!has_leading_string) {
                    if (tok_kind != .string_lit) return null;
                    has_leading_string = true;
                } else if (tok_kind == .kw_as) {
                    has_seen_as = true;
                } else if (has_seen_as and isRenamableIdentifierKind(tok_kind)) {
                    return child.token;
                }
            }
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
        return null;
    }

    /// Finds the bound identifier token inside a `.walrus_cond_expr` (`([var] ident [: T] := expr)`).
    fn findWalrusIdentToken(self: *const CstFormatter, walrus_idx: CstNodeIndex) ?TokenIndex {
        const walrus = self.cst_arena.getNode(walrus_idx);
        const end_idx: usize = walrus_idx.asInt() + walrus.subtree_size;
        var child_cursor: usize = walrus_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_cursor)));
            if (child.subtree_size == 1 and !self.shouldSkipLeaf(child)) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (isRenamableIdentifierKind(tok_kind)) return child.token;
                if (tok_kind == .colon or tok_kind == .colon_eq) break;
            }
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
        return null;
    }

    /// Registers bound element/index identifiers inside a `.for_header` (`pat [, idx] in iter`).
    fn registerForHeaderFixRenames(self: *CstFormatter, header_idx: CstNodeIndex) !void {
        const header = self.cst_arena.getNode(header_idx);
        const end_idx: usize = header_idx.asInt() + header.subtree_size;
        var has_seen_comma = false;
        var child_cursor: usize = header_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child_id = CstNodeIndex.fromInt(@intCast(child_cursor));
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .ident_pat) {
                const pat_tok = if (child.subtree_size == 1 and !self.shouldSkipLeaf(child))
                    child.token
                else
                    self.findFirstIdentTokenInDirectChildren(child_id) orelse .none;
                try self.registerFixRename(pat_tok, .snake_case);
            } else if (child.subtree_size == 1 and !self.shouldSkipLeaf(child)) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_in) break;
                if (tok_kind == .comma) {
                    has_seen_comma = true;
                } else if (has_seen_comma and isRenamableIdentifierKind(tok_kind)) {
                    try self.registerFixRename(child.token, .snake_case);
                }
            }
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
    }

    /// Returns whether `node_idx` has a direct leaf child whose `TokenKind` equals `target_kind`.
    fn hasDirectTokenKind(
        self: *const CstFormatter,
        node_idx: CstNodeIndex,
        target_kind: TokenKind,
    ) bool {
        const node = self.cst_arena.getNode(node_idx);
        const end_idx: usize = node_idx.asInt() + node.subtree_size;
        var child_cursor: usize = node_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_cursor)));
            if (child.subtree_size == 1 and !self.shouldSkipLeaf(child)) {
                if (self.token_buffer.getToken(child.token).kind == target_kind) return true;
            }
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
        return false;
    }

    /// Formats the root `.file_end` CST node and flushes all remaining trivia up to `.eof`.
    pub fn formatRoot(self: *CstFormatter) !void {
        if (self.cst_arena.countNodes() == 0) {
            try self.flushUnconsumedCommentsInRange(0, @intCast(self.token_meta.len), true);
            return;
        }
        const root_id = CstNodeIndex.fromInt(0);
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(root_id, &children);

        try self.formatItemSequence(children.items, true);

        // Emit any remaining unemitted `// corex fmt: off` ranges at the end of the file:
        for (self.suppressed_ranges.items) |*supp| {
            if (!supp.is_emitted and supp.off_start < supp.on_end and supp.on_end <= self.source.len) {
                supp.is_emitted = true;
                self.markByteRangeConsumed(supp.off_start, supp.on_end);
                if (self.doc_arena.instructions.items.len > 0) {
                    try self.doc_arena.emitHardLine();
                }
                try self.doc_arena.emitVerbatimText(self.source[supp.off_start..supp.on_end]);
            }
        }

        // Guarantee 100% of comments (including on `.eof`) are flushed:
        const eof_tok_idx: u32 = @intCast(self.token_meta.len);
        if (self.hasUnconsumedCommentsInTokenRange(0, eof_tok_idx, false, true)) {
            if (self.doc_arena.instructions.items.len > 0) {
                const last_op = self.doc_arena.instructions.items[self.doc_arena.instructions.items.len - 1].op;
                if (last_op != .hard_line and last_op != .blank_line and last_op != .line_suffix) {
                    if (eof_tok_idx > 0 and self.token_meta[eof_tok_idx - 1].has_leading_blank_line) {
                        try self.doc_arena.emitBlankLine();
                    } else {
                        try self.doc_arena.emitHardLine();
                    }
                }
            }
            try self.flushUnconsumedCommentsInRange(0, eof_tok_idx, true);
        }
    }

    /// Formats a sequence of top-level or member items according to `DR-03` Section 7 spacing rules.
    fn formatItemSequence(
        self: *CstFormatter,
        items: []const CstNodeIndex,
        is_module_scope: bool,
    ) anyerror!void {
        var prev_item_idx: ?CstNodeIndex = null;
        var i: usize = 0;
        while (i < items.len) {
            const child_id = items[i];
            const child = self.cst_arena.getNode(child_id);

            // Strip standalone `.empty_stmt` or bare `.semi` leaves while preserving their comments:
            if (child.kind == .empty_stmt or
                (child.subtree_size == 1 and !child.token.isNone() and
                    self.token_buffer.getToken(child.token).kind == .semi))
            {
                try self.flushNodeComments(child_id);
                i += 1;
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const rec = self.token_buffer.getToken(child.token);
                if (rec.kind == .eof or (rec.kind == .invalid_token and rec.flags.is_synthesized)) {
                    if (rec.kind != .eof) {
                        try self.flushNodeComments(child_id);
                    }
                    i += 1;
                    continue;
                }
            }

            if (prev_item_idx) |prev_id| {
                const prev_kind = self.cst_arena.getNode(prev_id).kind;
                const curr_kind = child.kind;
                const has_blank_or_doc = self.hasNodeLeadingBlankLine(child_id) or
                    self.hasNodeDocComment(child_id);

                if (prev_kind == .use_item and curr_kind == .use_item and !has_blank_or_doc) {
                    try self.doc_arena.emitHardLine();
                } else if (((prev_kind == .const_item and curr_kind == .const_item) or
                    (prev_kind == .type_alias_item and curr_kind == .type_alias_item)) and
                    !has_blank_or_doc and !self.isNodeMultilineInSource(prev_id) and
                    !self.isNodeMultilineInSource(child_id))
                {
                    try self.doc_arena.emitHardLine();
                } else if (!is_module_scope and !has_blank_or_doc and
                    self.isCompactTraitSignatureItem(prev_id) and
                    self.isCompactTraitSignatureItem(child_id) and
                    !self.isNodeMultilineInSource(prev_id))
                {
                    try self.doc_arena.emitHardLine();
                } else {
                    try self.doc_arena.emitBlankLine();
                }
            }

            if (try self.tryEmitSuppressedSiblingSpan(items, &i)) {
                prev_item_idx = items[i - 1];
                continue;
            }

            try self.formatNode(child_id);
            prev_item_idx = child_id;
            i += 1;
        }
    }

    /// Returns whether `node_idx` is a bodyless member signature (`type`, `const`, `static`, `fn …;`, or `subscript …;`).
    fn isCompactTraitSignatureItem(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        const node = self.cst_arena.getNode(node_idx);
        return switch (node.kind) {
            .type_alias_item, .const_item, .extern_static_item => true,
            .trait_member, .fn_item, .subscript_item => !self.hasDirectChildKind(node_idx, .block) and
                !self.hasDirectChildKind(node_idx, .fn_expr_body),
            else => false,
        };
    }

    /// Returns whether `node_idx` has a direct composite child with `CstNodeKind == target_kind`.
    fn hasDirectChildKind(
        self: *const CstFormatter,
        node_idx: CstNodeIndex,
        target_kind: CstNodeKind,
    ) bool {
        const node = self.cst_arena.getNode(node_idx);
        const end_idx: usize = node_idx.asInt() + node.subtree_size;
        var child_cursor: usize = node_idx.asInt() + 1;
        while (child_cursor < end_idx) {
            const child = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_cursor)));
            if (child.kind == target_kind) return true;
            child_cursor += @max(@as(usize, 1), child.subtree_size);
        }
        return false;
    }

    /// Flushes all leading and trailing comments attached to tokens within `node_idx`.
    fn flushNodeComments(self: *CstFormatter, node_idx: CstNodeIndex) !void {
        const first_tok = self.findFirstTokenInSubtree(node_idx);
        const last_tok = self.findLastTokenInSubtree(node_idx);
        if (first_tok.isNone() or last_tok.isNone()) return;
        try self.flushUnconsumedCommentsInRange(first_tok.asInt(), last_tok.asInt() + 1, true);
    }

    /// Formats a `.visibility_modifier` CST node (`pub`, `pub(pkg)`, or `pub(super)`, `ADR-22E`).
    fn formatVisibilityModifier(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        const node = self.cst_arena.getNode(node_idx);
        if (node.subtree_size == 1) {
            if (!self.shouldSkipLeaf(node)) {
                try self.emitTokenWithTrivia(node.token, "pub", false);
            }
            return;
        }

        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                } else if (tok_kind == .lparen) {
                    try self.emitTokenWithTrivia(child.token, "(", false);
                } else if (tok_kind == .rparen) {
                    try self.emitTokenWithTrivia(child.token, ")", false);
                } else {
                    const scope_lex = self.getTokenLexeme(child.token);
                    try self.emitTokenWithTrivia(child.token, scope_lex, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Extracts the identifier name of an `.attribute` CST node (`@inline` -> `"inline"`).
    fn extractAttributeSortName(self: *const CstFormatter, attr_id: CstNodeIndex) []const u8 {
        const attr_node = self.cst_arena.getNode(attr_id);
        const end_idx: usize = attr_id.asInt() + attr_node.subtree_size;
        var cursor: usize = attr_id.asInt() + 1;
        while (cursor < end_idx) : (cursor += 1) {
            const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
            if (leaf.subtree_size == 1 and !self.shouldSkipLeaf(leaf)) {
                const tok_kind = self.token_buffer.getToken(leaf.token).kind;
                if (tok_kind != .at) {
                    return self.getTokenLexeme(leaf.token);
                }
            }
        }
        return "";
    }

    /// Formats leading `.attribute` children on items/members: stacks `@attr(…)` above sorted `@marker` line (`DR-22` §3.4).
    fn formatLeadingStackedAttributes(
        self: *CstFormatter,
        children: []const CstNodeIndex,
    ) anyerror!usize {
        var attr_end: usize = 0;
        while (attr_end < children.len and self.cst_arena.getNode(children[attr_end]).kind == .attribute) {
            attr_end += 1;
        }
        if (attr_end == 0) return 0;
        if (attr_end == 1) {
            try self.formatAttribute(children[0]);
            try self.doc_arena.emitHardLine();
            return 1;
        }

        const first_tok = self.findFirstTokenInSubtree(children[0]);
        const last_tok = self.findLastTokenInSubtree(children[attr_end - 1]);
        if (!first_tok.isNone()) {
            try self.emitLeadingTrivia(first_tok, false);
        }

        const has_inner_comments = !first_tok.isNone() and !last_tok.isNone() and
            (self.hasUnconsumedCommentsInTokenRange(first_tok.asInt(), last_tok.asInt(), true, true) or
                (!self.token_meta[last_tok.asInt()].is_trailing_consumed and
                    self.token_meta[last_tok.asInt()].has_trailing_comments));

        if (has_inner_comments) {
            for (children[0..attr_end]) |attr_id| {
                try self.formatAttribute(attr_id);
                try self.doc_arena.emitHardLine();
            }
            return attr_end;
        }

        var param_attrs: std.ArrayList(CstNodeIndex) = .empty;
        defer param_attrs.deinit(self.allocator);
        var marker_attrs: std.ArrayList(MarkerAttrEntry) = .empty;
        defer marker_attrs.deinit(self.allocator);

        for (children[0..attr_end], 0..) |attr_id, order_i| {
            if (self.hasDirectTokenKind(attr_id, .lparen)) {
                try param_attrs.append(self.allocator, attr_id);
            } else {
                try marker_attrs.append(self.allocator, .{
                    .node_idx = attr_id,
                    .sort_name = self.extractAttributeSortName(attr_id),
                    .orig_order = order_i,
                });
            }
        }
        std.mem.sort(MarkerAttrEntry, marker_attrs.items, {}, MarkerAttrEntry.lessThan);

        for (param_attrs.items) |param_attr_id| {
            try self.formatAttribute(param_attr_id);
            try self.doc_arena.emitHardLine();
        }
        if (marker_attrs.items.len > 0) {
            for (marker_attrs.items, 0..) |entry, marker_i| {
                if (marker_i > 0) {
                    try self.doc_arena.emitText(" ");
                }
                try self.formatAttribute(entry.node_idx);
            }
            try self.doc_arena.emitHardLine();
        }
        return attr_end;
    }

    /// Formats leading inline `.attribute` children (`@builder |…|`, `@unused x: i32`, `@state var x`), sorting markers.
    fn formatLeadingInlineAttributes(
        self: *CstFormatter,
        children: []const CstNodeIndex,
    ) anyerror!usize {
        var attr_end: usize = 0;
        while (attr_end < children.len and self.cst_arena.getNode(children[attr_end]).kind == .attribute) {
            attr_end += 1;
        }
        if (attr_end == 0) return 0;
        if (attr_end == 1) {
            try self.formatAttribute(children[0]);
            try self.doc_arena.emitText(" ");
            return 1;
        }

        const first_tok = self.findFirstTokenInSubtree(children[0]);
        const last_tok = self.findLastTokenInSubtree(children[attr_end - 1]);
        if (!first_tok.isNone()) {
            try self.emitLeadingTrivia(first_tok, false);
        }

        const has_inner_comments = !first_tok.isNone() and !last_tok.isNone() and
            (self.hasUnconsumedCommentsInTokenRange(first_tok.asInt(), last_tok.asInt(), true, true) or
                (!self.token_meta[last_tok.asInt()].is_trailing_consumed and
                    self.token_meta[last_tok.asInt()].has_trailing_comments));

        if (has_inner_comments) {
            for (children[0..attr_end]) |attr_id| {
                try self.formatAttribute(attr_id);
                try self.doc_arena.emitText(" ");
            }
            return attr_end;
        }

        var param_attrs: std.ArrayList(CstNodeIndex) = .empty;
        defer param_attrs.deinit(self.allocator);
        var marker_attrs: std.ArrayList(MarkerAttrEntry) = .empty;
        defer marker_attrs.deinit(self.allocator);

        for (children[0..attr_end], 0..) |attr_id, order_i| {
            if (self.hasDirectTokenKind(attr_id, .lparen)) {
                try param_attrs.append(self.allocator, attr_id);
            } else {
                try marker_attrs.append(self.allocator, .{
                    .node_idx = attr_id,
                    .sort_name = self.extractAttributeSortName(attr_id),
                    .orig_order = order_i,
                });
            }
        }
        std.mem.sort(MarkerAttrEntry, marker_attrs.items, {}, MarkerAttrEntry.lessThan);

        for (param_attrs.items) |param_attr_id| {
            try self.formatAttribute(param_attr_id);
            try self.doc_arena.emitText(" ");
        }
        for (marker_attrs.items) |entry| {
            try self.formatAttribute(entry.node_idx);
            try self.doc_arena.emitText(" ");
        }
        return attr_end;
    }

    /// Formats an `@attribute` CST node (`@attr` or `@attr(args)`).
    fn formatAttribute(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var prev_tok_kind: ?TokenKind = null;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (prev_tok_kind) |prev_k| {
                    if (prev_k == .comma) {
                        try self.doc_arena.emitText(" ");
                    } else if (tok_kind == .eq or prev_k == .eq) {
                        try self.doc_arena.emitText(" ");
                    } else if (prev_k == .colon) {
                        try self.doc_arena.emitText(" ");
                    }
                }
                try self.emitTokenWithTrivia(child.token, null, false);
                prev_tok_kind = tok_kind;
            } else {
                if (prev_tok_kind) |prev_k| {
                    if (prev_k == .comma or prev_k == .eq or prev_k == .colon) {
                        try self.doc_arena.emitText(" ");
                    }
                }
                try self.formatNode(child_id);
                prev_tok_kind = .ident;
            }
        }
    }

    /// Formats a `.use_item` declaration (`[Vis] use a.b.{…};`).
    fn formatUseItem(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        const start_idx = try self.formatLeadingStackedAttributes(children.items);
        var has_emitted_semi = false;
        for (children.items[start_idx..]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .visibility_modifier) {
                try self.formatVisibilityModifier(child_id);
                try self.doc_arena.emitText(" ");
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (child.kind == .use_introducer or tok_kind == .kw_use) {
                    try self.emitTokenWithTrivia(child.token, "use", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    has_emitted_semi = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .use_tree) {
                try self.formatUseTree(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_emitted_semi) {
            try self.doc_arena.emitText(";");
        }
    }

    /// Formats a `.use_tree` node, sorting braced specifiers lexicographically (`self` first).
    fn formatUseTree(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        // Find `{` and `}` among direct children if this `use_tree` has a braced group:
        var lbrace_pos: ?usize = null;
        var rbrace_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .lbrace and lbrace_pos == null) {
                    lbrace_pos = idx;
                } else if (tok_kind == .rbrace) {
                    rbrace_pos = idx;
                }
            }
        }

        if (lbrace_pos == null or rbrace_pos == null or rbrace_pos.? <= lbrace_pos.?) {
            // Simple path or `as` alias:
            for (children.items) |child_id| {
                const child = self.cst_arena.getNode(child_id);
                if (child.subtree_size == 1 and !child.token.isNone()) {
                    const tok_kind = self.token_buffer.getToken(child.token).kind;
                    if (tok_kind == .kw_as) {
                        try self.doc_arena.emitText(" ");
                        try self.emitTokenWithTrivia(child.token, "as", false);
                        try self.doc_arena.emitText(" ");
                    } else {
                        try self.emitTokenWithTrivia(child.token, null, false);
                    }
                } else if (child.kind == .use_tree) {
                    try self.formatUseTree(child_id);
                } else {
                    try self.formatNode(child_id);
                }
            }
            return;
        }

        const lb_idx = lbrace_pos.?;
        const rb_idx = rbrace_pos.?;

        // [1] Emit prefix before `{`:
        for (children.items[0..lb_idx]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                try self.emitTokenWithTrivia(child.token, null, false);
            } else {
                try self.formatNode(child_id);
            }
        }

        const open_brace_tok = self.cst_arena.getNode(children.items[lb_idx]).token;
        const close_brace_tok = self.cst_arena.getNode(children.items[rb_idx]).token;

        // [2] Collect `.use_tree` specifiers and detect trailing comma inside `{ … }`:
        var specs: std.ArrayList(UseSpecEntry) = .empty;
        defer specs.deinit(self.allocator);
        var has_trailing_comma = false;

        for (children.items[lb_idx + 1 .. rb_idx]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .use_tree) {
                has_trailing_comma = false;
                const first_tok = self.findFirstTokenInSubtree(child_id);
                const last_tok = self.findLastTokenInSubtree(child_id);
                var sort_key: []const u8 = "";
                if (!first_tok.isNone() and !last_tok.isNone()) {
                    const start_b: usize = self.token_buffer.getToken(first_tok).byte_offset;
                    const end_rec = self.token_buffer.getToken(last_tok);
                    const end_b: usize = @min(self.source.len, @as(usize, end_rec.byte_offset) + end_rec.byte_len);
                    if (start_b < end_b) {
                        sort_key = std.mem.trim(u8, self.source[start_b..end_b], " \t\r\n");
                    }
                }
                const is_self = std.mem.eql(u8, sort_key, "self") or
                    std.mem.startsWith(u8, sort_key, "self ");
                try specs.append(self.allocator, .{
                    .node_idx = child_id,
                    .sort_key = sort_key,
                    .is_self = is_self,
                });
            } else if (child.subtree_size == 1 and !child.token.isNone()) {
                if (self.token_buffer.getToken(child.token).kind == .comma) {
                    has_trailing_comma = true;
                    if (specs.items.len > 0) {
                        specs.items[specs.items.len - 1].comma_tok = child.token;
                    }
                }
            }
        }

        if (specs.items.len == 0) {
            try self.formatEmptyContainer(open_brace_tok, close_brace_tok, "{", "}");
            return;
        }

        const has_inner_comments = if (!open_brace_tok.isNone() and !close_brace_tok.isNone())
            self.hasUnconsumedCommentsInTokenRange(open_brace_tok.asInt(), close_brace_tok.asInt(), true, true)
        else
            false;

        if (!has_inner_comments and specs.items.len > 1) {
            std.mem.sort(UseSpecEntry, specs.items, {}, UseSpecEntry.lessThan);
        }

        // Mark comma tokens inside `{ … }` as consumed when no inner comments are attached:
        if (!has_inner_comments) {
            for (children.items[lb_idx + 1 .. rb_idx]) |child_id| {
                const child = self.cst_arena.getNode(child_id);
                if (child.subtree_size == 1 and !child.token.isNone()) {
                    if (self.token_buffer.getToken(child.token).kind == .comma) {
                        self.token_meta[child.token.asInt()].is_token_emitted = true;
                    }
                }
            }
        }

        try self.emitTokenLeadingAndGlyph(open_brace_tok, "{", false);
        const group_mode: GroupMode = if (has_trailing_comma or has_inner_comments)
            .force_break
        else
            .auto_fit;
        _ = try self.doc_arena.beginGroup(group_mode);
        try self.emitTrailingTrivia(open_brace_tok);
        try self.doc_arena.emitSoftLine();
        try self.doc_arena.beginIndent(INDENT_SPACES);

        for (specs.items, 0..) |spec, spec_i| {
            try self.formatUseTree(spec.node_idx);
            if (!spec.comma_tok.isNone()) {
                try self.emitLeadingTrivia(spec.comma_tok, false);
                self.token_meta[spec.comma_tok.asInt()].is_token_emitted = true;
            }
            if (spec_i + 1 < specs.items.len) {
                try self.doc_arena.emitText(",");
                if (!spec.comma_tok.isNone()) {
                    try self.emitTrailingTrivia(spec.comma_tok);
                }
                try self.doc_arena.emitLine();
            } else {
                try self.doc_arena.emitIfBreak(",", "");
                if (!spec.comma_tok.isNone()) {
                    try self.emitTrailingTrivia(spec.comma_tok);
                }
            }
        }

        if (self.hasUnconsumedLeadingComments(close_brace_tok)) {
            try self.doc_arena.emitHardLine();
            try self.emitLeadingTrivia(close_brace_tok, false);
        }
        try self.doc_arena.endIndent(INDENT_SPACES);
        try self.doc_arena.emitSoftLine();
        try self.doc_arena.endGroup();
        try self.emitTokenWithTrivia(close_brace_tok, "}", false);
    }

    /// Formats a `.const_item` declaration (`[Vis] const NAME: Type = expr;`).
    fn formatConstItem(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        const start_idx = try self.formatLeadingStackedAttributes(children.items);
        var has_emitted_semi = false;
        for (children.items[start_idx..]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .visibility_modifier) {
                try self.formatVisibilityModifier(child_id);
                try self.doc_arena.emitText(" ");
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (child.kind == .const_introducer or tok_kind == .kw_const) {
                    try self.emitTokenWithTrivia(child.token, "const", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    has_emitted_semi = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_emitted_semi) {
            try self.doc_arena.emitText(";");
        }
    }

    /// Formats a `.type_alias_item` declaration (`[Vis] type Name[T] = Target;`).
    fn formatTypeAliasItem(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        // Check if this is a `type Name = bit_field u32 { … }` with a braced field block:
        var lbrace_pos: ?usize = null;
        var rbrace_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .lbrace and lbrace_pos == null) lbrace_pos = idx;
                if (tok_kind == .rbrace) rbrace_pos = idx;
            }
        }
        if (lbrace_pos != null and rbrace_pos != null) {
            try self.formatStructOrUnionOrEnum(node_idx);
            return;
        }

        const start_idx = try self.formatLeadingStackedAttributes(children.items);
        var has_emitted_semi = false;
        for (children.items[start_idx..]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .visibility_modifier) {
                try self.formatVisibilityModifier(child_id);
                try self.doc_arena.emitText(" ");
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (child.kind == .type_alias_introducer or tok_kind == .kw_type) {
                    try self.emitTokenWithTrivia(child.token, "type", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .plus) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "+", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_is) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "is", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    has_emitted_semi = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_emitted_semi) {
            try self.doc_arena.emitText(";");
        }
    }

    /// Formats a `.mod_item` declaration (`[Vis] mod name;` or `[Vis] mod name { … }`).
    fn formatModItem(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var lbrace_pos: ?usize = null;
        var rbrace_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .lbrace and lbrace_pos == null) lbrace_pos = idx;
                if (tok_kind == .rbrace) rbrace_pos = idx;
            }
        }

        if (lbrace_pos == null or rbrace_pos == null) {
            const start_idx = try self.formatLeadingStackedAttributes(children.items);
            var has_semi = false;
            for (children.items[start_idx..]) |child_id| {
                const child = self.cst_arena.getNode(child_id);
                if (child.kind == .visibility_modifier) {
                    try self.formatVisibilityModifier(child_id);
                    try self.doc_arena.emitText(" ");
                    continue;
                }
                if (child.subtree_size == 1 and !child.token.isNone()) {
                    const tok_kind = self.token_buffer.getToken(child.token).kind;
                    if (tok_kind == .kw_pub) {
                        try self.emitTokenWithTrivia(child.token, "pub", false);
                        try self.doc_arena.emitText(" ");
                    } else if (child.kind == .mod_introducer or tok_kind == .kw_mod) {
                        try self.emitTokenWithTrivia(child.token, "mod", false);
                        try self.doc_arena.emitText(" ");
                    } else if (tok_kind == .semi) {
                        try self.emitTokenWithTrivia(child.token, ";", false);
                        has_semi = true;
                    } else {
                        try self.emitTokenWithTrivia(child.token, null, false);
                    }
                } else {
                    try self.formatNode(child_id);
                }
            }
            if (!has_semi) try self.doc_arena.emitText(";");
            return;
        }

        const lb_idx = lbrace_pos.?;
        const rb_idx = rbrace_pos.?;
        const start_idx = try self.formatLeadingStackedAttributes(children.items[0..lb_idx]);
        for (children.items[start_idx..lb_idx]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .visibility_modifier) {
                try self.formatVisibilityModifier(child_id);
                try self.doc_arena.emitText(" ");
            } else if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (child.kind == .mod_introducer or tok_kind == .kw_mod) {
                    try self.emitTokenWithTrivia(child.token, "mod", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        try self.doc_arena.emitText(" ");
        const open_brace_tok = self.cst_arena.getNode(children.items[lb_idx]).token;
        const close_brace_tok = self.cst_arena.getNode(children.items[rb_idx]).token;
        const body_items = children.items[lb_idx + 1 .. rb_idx];
        if (body_items.len == 0) {
            try self.formatEmptyContainer(open_brace_tok, close_brace_tok, "{", "}");
            return;
        }
        try self.emitTokenWithTrivia(open_brace_tok, "{", false);
        try self.doc_arena.beginIndent(INDENT_SPACES);
        try self.doc_arena.emitHardLine();
        try self.formatItemSequence(body_items, true);
        try self.emitLeadingTriviaBeforeCloseBrace(close_brace_tok);
        try self.doc_arena.endIndent(INDENT_SPACES);
        try self.doc_arena.emitHardLine();
        try self.emitTokenWithTrivia(close_brace_tok, "}", false);
    }

    /// Emits any unconsumed leading comments on `close_tok` while still inside `+4` block indentation.
    fn emitLeadingTriviaBeforeCloseBrace(self: *CstFormatter, close_tok: TokenIndex) !void {
        if (close_tok.isNone() or close_tok.asInt() >= self.token_meta.len) return;
        const meta = self.token_meta[close_tok.asInt()];
        if (!meta.is_leading_consumed and meta.has_leading_comments) {
            if (meta.has_leading_blank_line) {
                try self.doc_arena.emitBlankLine();
            } else {
                try self.doc_arena.emitHardLine();
            }
            try self.emitLeadingTrivia(close_tok, true);
        }
    }

    /// Formats a `.struct_item` (including `bit_field`), `.union_item`, or `.enum_item` declaration.
    fn formatStructOrUnionOrEnum(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var lbrace_pos: ?usize = null;
        var rbrace_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .lbrace and lbrace_pos == null) lbrace_pos = idx;
                if (tok_kind == .rbrace) rbrace_pos = idx;
            }
        }

        const header_end = lbrace_pos orelse children.items.len;
        const start_idx = try self.formatLeadingStackedAttributes(children.items[0..header_end]);
        for (children.items[start_idx..header_end]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .visibility_modifier) {
                try self.formatVisibilityModifier(child_id);
                try self.doc_arena.emitText(" ");
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_struct or tok_kind == .kw_union or
                    tok_kind == .kw_enum or tok_kind == .kw_bit_field or tok_kind == .kw_type)
                {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }

        if (lbrace_pos == null or rbrace_pos == null) return;
        const lb_idx = lbrace_pos.?;
        const rb_idx = rbrace_pos.?;
        const open_brace_tok = self.cst_arena.getNode(children.items[lb_idx]).token;
        const close_brace_tok = self.cst_arena.getNode(children.items[rb_idx]).token;

        try self.doc_arena.emitText(" ");

        var members: std.ArrayList(CstNodeIndex) = .empty;
        defer members.deinit(self.allocator);
        for (children.items[lb_idx + 1 .. rb_idx]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .struct_field or child.kind == .enum_variant) {
                try members.append(self.allocator, child_id);
            }
        }

        if (members.items.len == 0) {
            try self.formatEmptyContainer(open_brace_tok, close_brace_tok, "{", "}");
        } else {
            try self.emitTokenWithTrivia(open_brace_tok, "{", false);
            try self.doc_arena.beginIndent(INDENT_SPACES);
            try self.doc_arena.emitHardLine();

            var mem_i: usize = 0;
            while (mem_i < members.items.len) {
                if (mem_i > 0) {
                    if (self.hasNodeLeadingBlankLine(members.items[mem_i])) {
                        try self.doc_arena.emitBlankLine();
                    } else {
                        try self.doc_arena.emitHardLine();
                    }
                }
                if (try self.tryEmitSuppressedSiblingSpan(members.items, &mem_i)) {
                    continue;
                }
                const mem_id = members.items[mem_i];
                const mem_node = self.cst_arena.getNode(mem_id);
                if (mem_node.kind == .struct_field) {
                    try self.formatStructField(mem_id);
                } else {
                    try self.formatEnumVariant(mem_id);
                }
                mem_i += 1;
            }

            try self.emitLeadingTriviaBeforeCloseBrace(close_brace_tok);
            try self.doc_arena.endIndent(INDENT_SPACES);
            try self.doc_arena.emitHardLine();
            try self.emitTokenWithTrivia(close_brace_tok, "}", false);
        }

        // Strip optional trailing `;` after `type Name = bit_field u32 { … };` while preserving comments:
        for (children.items[rb_idx + 1 ..]) |after_id| {
            const after = self.cst_arena.getNode(after_id);
            if (after.subtree_size == 1 and !after.token.isNone() and
                self.token_buffer.getToken(after.token).kind == .semi)
            {
                if (self.hasUnconsumedLeadingComments(after.token)) {
                    if (!self.hasTrailingNewlineInstruction()) {
                        try self.doc_arena.emitHardLine();
                    }
                    try self.emitLeadingTrivia(after.token, false);
                }
                self.token_meta[after.token.asInt()].is_token_emitted = true;
                try self.emitTrailingTrivia(after.token);
            }
        }
    }

    /// Formats a `.struct_field` node, ensuring a trailing `,` separator.
    fn formatStructField(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        const start_idx = try self.formatLeadingStackedAttributes(children.items);
        var has_emitted_comma = false;
        for (children.items[start_idx..]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .visibility_modifier) {
                try self.formatVisibilityModifier(child_id);
                try self.doc_arena.emitText(" ");
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .pipe) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "|", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .comma or tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ",", false);
                    has_emitted_comma = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_emitted_comma) {
            try self.doc_arena.emitText(",");
        }
    }

    /// Formats an `.enum_variant` node, ensuring a trailing `,` separator.
    fn formatEnumVariant(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        // Check if variant has a struct-style `{ … }` payload:
        var lbrace_pos: ?usize = null;
        var rbrace_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .lbrace and lbrace_pos == null) lbrace_pos = idx;
                if (tok_kind == .rbrace) rbrace_pos = idx;
            }
        }

        const header_end = lbrace_pos orelse children.items.len;
        var idx = try self.formatLeadingStackedAttributes(children.items[0..header_end]);
        var has_emitted_comma = false;
        while (idx < children.items.len) : (idx += 1) {
            if (lbrace_pos != null and rbrace_pos != null and idx == lbrace_pos.?) {
                const lb_idx = lbrace_pos.?;
                const rb_idx = rbrace_pos.?;
                const open_brace_tok = self.cst_arena.getNode(children.items[lb_idx]).token;
                const close_brace_tok = self.cst_arena.getNode(children.items[rb_idx]).token;
                try self.doc_arena.emitText(" ");
                const inner_fields = children.items[lb_idx + 1 .. rb_idx];
                if (inner_fields.len == 0) {
                    try self.formatEmptyContainer(open_brace_tok, close_brace_tok, "{", "}");
                } else {
                    try self.emitTokenWithTrivia(open_brace_tok, "{", false);
                    try self.doc_arena.beginIndent(INDENT_SPACES);
                    try self.doc_arena.emitHardLine();
                    for (inner_fields, 0..) |field_id, field_i| {
                        if (field_i > 0) try self.doc_arena.emitHardLine();
                        try self.formatStructField(field_id);
                    }
                    try self.emitLeadingTriviaBeforeCloseBrace(close_brace_tok);
                    try self.doc_arena.endIndent(INDENT_SPACES);
                    try self.doc_arena.emitHardLine();
                    try self.emitTokenWithTrivia(close_brace_tok, "}", false);
                }
                idx = rb_idx;
                continue;
            }

            const child_id = children.items[idx];
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                try self.formatAttribute(child_id);
                try self.doc_arena.emitHardLine();
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .comma or tok_kind == .semi) {
                    if (idx + 1 == children.items.len) {
                        try self.emitTokenWithTrivia(child.token, ",", false);
                        has_emitted_comma = true;
                    } else {
                        try self.emitTokenWithTrivia(child.token, ",", false);
                        try self.doc_arena.emitText(" ");
                    }
                } else if (tok_kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_emitted_comma) {
            try self.doc_arena.emitText(",");
        }
    }

    /// Formats a `.trait_item` or `.impl_item` declaration.
    fn formatTraitOrImpl(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var lbrace_pos: ?usize = null;
        var rbrace_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .lbrace and lbrace_pos == null) lbrace_pos = idx;
                if (tok_kind == .rbrace) rbrace_pos = idx;
            }
        }

        const header_end = lbrace_pos orelse children.items.len;
        const start_idx = try self.formatLeadingStackedAttributes(children.items[0..header_end]);
        {
            self.in_type_context += 1;
            defer self.in_type_context -= 1;
            var prev_was_impl_with_type_params = false;
            var idx: usize = start_idx;
            while (idx < header_end) : (idx += 1) {
                const child_id = children.items[idx];
                const child = self.cst_arena.getNode(child_id);
                if (child.kind == .visibility_modifier) {
                    try self.formatVisibilityModifier(child_id);
                    try self.doc_arena.emitText(" ");
                    continue;
                }
                if (child.subtree_size == 1 and !child.token.isNone()) {
                    const tok_kind = self.token_buffer.getToken(child.token).kind;
                    if (tok_kind == .kw_pub) {
                        try self.emitTokenWithTrivia(child.token, "pub", false);
                        try self.doc_arena.emitText(" ");
                    } else if (tok_kind == .kw_unsafe) {
                        try self.emitTokenWithTrivia(child.token, "unsafe", false);
                        try self.doc_arena.emitText(" ");
                    } else if (child.kind == .trait_introducer or tok_kind == .kw_trait) {
                        try self.emitTokenWithTrivia(child.token, "trait", false);
                        try self.doc_arena.emitText(" ");
                    } else if (child.kind == .impl_introducer or tok_kind == .kw_impl) {
                        try self.emitTokenWithTrivia(child.token, "impl", false);
                        const next_is_type_params = (idx + 1 < header_end and
                            self.cst_arena.getNode(children.items[idx + 1]).kind == .type_params);
                        if (!next_is_type_params) {
                            try self.doc_arena.emitText(" ");
                        } else {
                            prev_was_impl_with_type_params = true;
                        }
                    } else if (tok_kind == .kw_for) {
                        try self.doc_arena.emitText(" ");
                        try self.emitTokenWithTrivia(child.token, "for", false);
                        try self.doc_arena.emitText(" ");
                    } else if (tok_kind == .colon) {
                        try self.emitTokenWithTrivia(child.token, ":", false);
                        try self.doc_arena.emitText(" ");
                    } else if (tok_kind == .plus) {
                        try self.doc_arena.emitText(" ");
                        try self.emitTokenWithTrivia(child.token, "+", false);
                        try self.doc_arena.emitText(" ");
                    } else {
                        try self.emitTokenWithTrivia(child.token, null, false);
                    }
                } else {
                    try self.formatNode(child_id);
                    if (child.kind == .type_params and prev_was_impl_with_type_params) {
                        try self.doc_arena.emitText(" ");
                        prev_was_impl_with_type_params = false;
                    }
                }
            }
        }

        if (lbrace_pos == null or rbrace_pos == null) return;
        const lb_idx = lbrace_pos.?;
        const rb_idx = rbrace_pos.?;
        const open_brace_tok = self.cst_arena.getNode(children.items[lb_idx]).token;
        const close_brace_tok = self.cst_arena.getNode(children.items[rb_idx]).token;

        try self.doc_arena.emitText(" ");
        const body_items = children.items[lb_idx + 1 .. rb_idx];
        if (body_items.len == 0) {
            try self.formatEmptyContainer(open_brace_tok, close_brace_tok, "{", "}");
            return;
        }

        try self.emitTokenWithTrivia(open_brace_tok, "{", false);
        try self.doc_arena.beginIndent(INDENT_SPACES);
        try self.doc_arena.emitHardLine();
        try self.formatItemSequence(body_items, false);
        try self.emitLeadingTriviaBeforeCloseBrace(close_brace_tok);
        try self.doc_arena.endIndent(INDENT_SPACES);
        try self.doc_arena.emitHardLine();
        try self.emitTokenWithTrivia(close_brace_tok, "}", false);
    }

    /// Formats a `.fn_item`, `.trait_member`, or `.impl_member` declaration (`DR-22` §3.4).
    fn formatFnOrMember(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        const start_idx = try self.formatLeadingStackedAttributes(children.items);
        var has_block_body = false;
        var has_emitted_semi = false;
        for (children.items[start_idx..]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .visibility_modifier) {
                try self.formatVisibilityModifier(child_id);
                try self.doc_arena.emitText(" ");
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_async or tok_kind == .kw_unsafe or
                    tok_kind == .kw_extern or tok_kind == .kw_comptime)
                {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .string_lit) {
                    const abi_lex = self.getTokenLexeme(child.token);
                    const abi_override: ?[]const u8 = if (std.ascii.eqlIgnoreCase(abi_lex, "\"c\""))
                        "\"C\""
                    else
                        null;
                    try self.emitTokenWithTrivia(child.token, abi_override, false);
                    try self.doc_arena.emitText(" ");
                } else if (child.kind == .fn_introducer or tok_kind == .kw_fn) {
                    try self.emitTokenWithTrivia(child.token, "fn", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    has_emitted_semi = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .fn_sig) {
                try self.formatFnSigWithOptions(child_id, true);
            } else if (child.kind == .fn_expr_body) {
                has_emitted_semi = true;
                try self.formatFnExprBody(child_id);
            } else if (child.kind == .block) {
                has_block_body = true;
                try self.doc_arena.emitText(" ");
                try self.formatBlock(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_block_body and !has_emitted_semi) {
            try self.doc_arena.emitText(";");
        }
    }

    /// Formats an `.extern_block_item` declaration (`[attrs] [vis] [unsafe] extern ["C"] { … }`).
    fn formatExternBlockItem(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var lbrace_pos: ?usize = null;
        var rbrace_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .lbrace and lbrace_pos == null) lbrace_pos = idx;
                if (tok_kind == .rbrace) rbrace_pos = idx;
            }
        }

        const header_end = lbrace_pos orelse children.items.len;
        const start_idx = try self.formatLeadingStackedAttributes(children.items[0..header_end]);
        for (children.items[start_idx..header_end]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .visibility_modifier) {
                try self.formatVisibilityModifier(child_id);
                try self.doc_arena.emitText(" ");
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_unsafe) {
                    try self.emitTokenWithTrivia(child.token, "unsafe", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_extern) {
                    try self.emitTokenWithTrivia(child.token, "extern", false);
                } else if (tok_kind == .string_lit) {
                    try self.doc_arena.emitText(" ");
                    const abi_lex = self.getTokenLexeme(child.token);
                    const abi_override: ?[]const u8 = if (std.ascii.eqlIgnoreCase(abi_lex, "\"c\""))
                        "\"C\""
                    else
                        null;
                    try self.emitTokenWithTrivia(child.token, abi_override, false);
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }

        if (lbrace_pos == null or rbrace_pos == null) return;
        const lb_idx = lbrace_pos.?;
        const rb_idx = rbrace_pos.?;
        const open_brace_tok = self.cst_arena.getNode(children.items[lb_idx]).token;
        const close_brace_tok = self.cst_arena.getNode(children.items[rb_idx]).token;

        try self.doc_arena.emitText(" ");
        const body_items = children.items[lb_idx + 1 .. rb_idx];
        if (body_items.len == 0) {
            try self.formatEmptyContainer(open_brace_tok, close_brace_tok, "{", "}");
            return;
        }

        try self.emitTokenWithTrivia(open_brace_tok, "{", false);
        try self.doc_arena.beginIndent(INDENT_SPACES);
        try self.doc_arena.emitHardLine();
        try self.formatItemSequence(body_items, false);
        try self.emitLeadingTriviaBeforeCloseBrace(close_brace_tok);
        try self.doc_arena.endIndent(INDENT_SPACES);
        try self.doc_arena.emitHardLine();
        try self.emitTokenWithTrivia(close_brace_tok, "}", false);
    }

    /// Formats an `.extern_static_item` declaration (`[attrs] [vis] [unsafe] [extern ["ABI"]] static [mut] name: Type;`).
    fn formatExternStaticItem(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        const start_idx = try self.formatLeadingStackedAttributes(children.items);
        var has_seen_static_kw = false;
        var has_seen_colon = false;
        var has_emitted_semi = false;

        for (children.items[start_idx..]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .visibility_modifier) {
                try self.formatVisibilityModifier(child_id);
                try self.doc_arena.emitText(" ");
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_unsafe) {
                    try self.emitTokenWithTrivia(child.token, "unsafe", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_extern) {
                    try self.emitTokenWithTrivia(child.token, "extern", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .string_lit and !has_seen_static_kw) {
                    const abi_lex = self.getTokenLexeme(child.token);
                    const abi_override: ?[]const u8 = if (std.ascii.eqlIgnoreCase(abi_lex, "\"c\""))
                        "\"C\""
                    else
                        null;
                    try self.emitTokenWithTrivia(child.token, abi_override, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .ident and !has_seen_static_kw and
                    std.mem.eql(u8, self.getTokenLexeme(child.token), "static"))
                {
                    has_seen_static_kw = true;
                    try self.emitTokenWithTrivia(child.token, "static", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_mut and !has_seen_colon) {
                    try self.emitTokenWithTrivia(child.token, "mut", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    has_seen_colon = true;
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    has_emitted_semi = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_emitted_semi) {
            try self.doc_arena.emitText(";");
        }
    }

    /// Formats a `.subscript_item` declaration (`[Vis] subscript[T](params) -> Type { let { … } inout { … } }`, `SE-21`).
    fn formatSubscriptItem(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        const start_idx = try self.formatLeadingStackedAttributes(children.items);
        var has_block_body = false;
        var has_emitted_semi = false;
        for (children.items[start_idx..]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .visibility_modifier) {
                try self.formatVisibilityModifier(child_id);
                try self.doc_arena.emitText(" ");
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (child.kind == .subscript_introducer or tok_kind == .kw_subscript) {
                    try self.emitTokenWithTrivia(child.token, "subscript", false);
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    has_emitted_semi = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .fn_sig) {
                try self.formatFnSigWithOptions(child_id, false);
            } else if (child.kind == .block) {
                has_block_body = true;
                try self.doc_arena.emitText(" ");
                try self.formatBlock(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_block_body and !has_emitted_semi) {
            try self.doc_arena.emitText(";");
        }
    }

    /// Formats a `.subscript_arm` accessor block (`let { yield …; }` or `inout { yield …; }`, `SE-21`).
    fn formatSubscriptArm(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_let) {
                    try self.emitTokenWithTrivia(child.token, "let", false);
                } else if (tok_kind == .ident and std.mem.eql(u8, self.getTokenLexeme(child.token), "inout")) {
                    try self.emitTokenWithTrivia(child.token, "inout", false);
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .block) {
                try self.doc_arena.emitText(" ");
                try self.formatBlock(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.test_item` or `.bench_item` declaration (`[async] test "…" [(params)] [-> Ret] { … }`, `SE-16`).
    fn formatTestOrBenchItem(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        const start_idx = try self.formatLeadingStackedAttributes(children.items);
        for (children.items[start_idx..]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_async) {
                    try self.emitTokenWithTrivia(child.token, "async", false);
                    try self.doc_arena.emitText(" ");
                } else if (child.kind == .test_introducer or
                    (tok_kind == .ident and std.mem.eql(u8, self.getTokenLexeme(child.token), "test")))
                {
                    try self.emitTokenWithTrivia(child.token, "test", false);
                    try self.doc_arena.emitText(" ");
                } else if (child.kind == .bench_introducer or
                    (tok_kind == .ident and std.mem.eql(u8, self.getTokenLexeme(child.token), "bench")))
                {
                    try self.emitTokenWithTrivia(child.token, "bench", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .param_list) {
                try self.doc_arena.emitText(" ");
                try self.formatParamList(child_id);
            } else if (child.kind == .return_type) {
                try self.formatReturnTypeWithOptions(child_id, true);
            } else if (child.kind == .block) {
                try self.doc_arena.emitText(" ");
                try self.formatBlock(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Returns whether `expr_id` is a delimited/block-headed expression that hugs `=` in `= expr;`.
    fn isHuggedFnBodyExpr(self: *const CstFormatter, expr_id: CstNodeIndex) bool {
        return switch (self.cst_arena.getNode(expr_id).kind) {
            .block,
            .match_expr,
            .struct_lit_expr,
            .view_block_expr,
            .with_expr,
            .if_expr,
            .for_stmt,
            .while_stmt,
            .loop_expr,
            .array_expr,
            .call_expr,
            .closure_expr,
            => true,
            else => false,
        };
    }

    /// Formats a `.fn_expr_body` node (` = expr;` inline when `< 100` cols, or indented on break).
    fn formatFnExprBody(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var eq_tok: TokenIndex = .none;
        var semi_tok: TokenIndex = .none;
        var expr_id: ?CstNodeIndex = null;

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (self.isZeroLengthCommentCarrierLeaf(child)) {
                if (!child.token.isNone()) {
                    try self.flushUnconsumedCommentsInRange(child.token.asInt(), child.token.asInt() + 1, true);
                }
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .eq and eq_tok.isNone()) {
                    eq_tok = child.token;
                    continue;
                } else if (tok_kind == .semi) {
                    semi_tok = child.token;
                    continue;
                }
            }
            if (expr_id == null) {
                expr_id = child_id;
            }
        }

        if (!eq_tok.isNone()) {
            try self.doc_arena.emitText(" ");
            try self.emitTokenWithTrivia(eq_tok, "=", false);
        }

        if (expr_id) |body_expr_id| {
            const first_expr_tok = self.findFirstTokenInSubtree(body_expr_id);
            const has_user_break = !first_expr_tok.isNone() and
                self.token_meta[first_expr_tok.asInt()].has_leading_newline;

            if (self.isHuggedFnBodyExpr(body_expr_id) and !has_user_break) {
                try self.doc_arena.emitText(" ");
                try self.formatNode(body_expr_id);
                if (!semi_tok.isNone()) {
                    try self.emitTokenWithTrivia(semi_tok, ";", false);
                } else {
                    try self.doc_arena.emitText(";");
                }
                return;
            }

            const mode: GroupMode = if (has_user_break) .force_break else .auto_fit;
            _ = try self.doc_arena.beginGroup(mode);
            try self.doc_arena.beginIndent(INDENT_SPACES);
            try self.doc_arena.emitLine();
            try self.formatNode(body_expr_id);
            if (!semi_tok.isNone()) {
                if (self.hasUnconsumedLeadingComments(semi_tok)) {
                    try self.emitLeadingTrivia(semi_tok, false);
                }
                self.token_meta[semi_tok.asInt()].is_token_emitted = true;
            }
            try self.doc_arena.emitText(";");
            try self.doc_arena.endIndent(INDENT_SPACES);
            try self.doc_arena.endGroup();
            if (!semi_tok.isNone()) {
                try self.emitTrailingTrivia(semi_tok);
            }
            return;
        }

        if (!semi_tok.isNone()) {
            try self.emitTokenWithTrivia(semi_tok, ";", false);
        } else {
            try self.doc_arena.emitText(";");
        }
    }

    /// Formats a `.fn_sig` node (`name[T](params) -> Ret where …`), stripping redundant `-> unit`.
    fn formatFnSig(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatFnSigWithOptions(node_idx, true);
    }

    /// Formats a `.fn_sig` node, stripping `-> unit` when `is_unit_strip_allowed` is `true` (`false` on `subscript`).
    fn formatFnSigWithOptions(
        self: *CstFormatter,
        node_idx: CstNodeIndex,
        is_unit_strip_allowed: bool,
    ) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                try self.emitTokenWithTrivia(child.token, null, false);
            } else if (child.kind == .type_params) {
                try self.formatTypeParams(child_id);
            } else if (child.kind == .param_list) {
                try self.formatParamList(child_id);
            } else if (child.kind == .return_type) {
                try self.formatReturnTypeWithOptions(child_id, is_unit_strip_allowed);
            } else if (child.kind == .where_clause) {
                try self.formatWhereClause(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Returns whether `arrow_tok` + `type_node_id` is a comment-free `-> unit` return annotation (`DR-22` §3.4).
    fn isStrippableUnitReturnPair(
        self: *const CstFormatter,
        arrow_tok: TokenIndex,
        type_node_id: CstNodeIndex,
    ) bool {
        if (arrow_tok.isNone() or arrow_tok.asInt() >= self.token_meta.len) return false;
        const type_node = self.cst_arena.getNode(type_node_id);
        if (type_node.kind != .prim_type_node or type_node.subtree_size != 1 or type_node.token.isNone()) {
            return false;
        }
        if (!std.mem.eql(u8, self.getTokenLexeme(type_node.token), "unit")) return false;
        if (self.hasUnconsumedLeadingComments(arrow_tok)) return false;
        const arrow_meta = self.token_meta[arrow_tok.asInt()];
        if (!arrow_meta.is_trailing_consumed and arrow_meta.has_trailing_comments) return false;
        if (self.hasUnconsumedLeadingComments(type_node.token)) return false;
        return true;
    }

    /// Marks a stripped `-> unit` token pair as consumed while preserving any trailing comment on `unit`.
    fn consumeStrippedUnitReturnPair(
        self: *CstFormatter,
        arrow_tok: TokenIndex,
        type_node_id: CstNodeIndex,
    ) !void {
        const unit_tok = self.cst_arena.getNode(type_node_id).token;
        self.token_meta[arrow_tok.asInt()].is_token_emitted = true;
        self.token_meta[arrow_tok.asInt()].is_leading_consumed = true;
        self.token_meta[arrow_tok.asInt()].is_trailing_consumed = true;
        if (!unit_tok.isNone() and unit_tok.asInt() < self.token_meta.len) {
            self.token_meta[unit_tok.asInt()].is_token_emitted = true;
            self.token_meta[unit_tok.asInt()].is_leading_consumed = true;
            try self.emitTrailingTrivia(unit_tok);
        }
    }

    /// Formats a `.return_type` node (` -> Type`), omitting redundant `-> unit` by default (`DR-22` §3.4).
    fn formatReturnType(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatReturnTypeWithOptions(node_idx, true);
    }

    /// Formats a `.return_type` node, stripping `-> unit` when `is_unit_strip_allowed` is `true`.
    fn formatReturnTypeWithOptions(
        self: *CstFormatter,
        node_idx: CstNodeIndex,
        is_unit_strip_allowed: bool,
    ) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        if (is_unit_strip_allowed and children.items.len == 2) {
            const first_child = self.cst_arena.getNode(children.items[0]);
            if (first_child.subtree_size == 1 and !first_child.token.isNone() and
                self.token_buffer.getToken(first_child.token).kind == .arrow and
                self.isStrippableUnitReturnPair(first_child.token, children.items[1]))
            {
                try self.consumeStrippedUnitReturnPair(first_child.token, children.items[1]);
                return;
            }
        }

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .arrow) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "->", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.param_list` node (including `/`, `*` zone separators and `...` variadics, `DR-22` §3.4).
    fn formatParamList(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatSteerableDelimitedList(node_idx, null, .lparen, .rparen, "(", ")", false);
    }

    /// Formats a single `.fn_param` node (`[var] [&[mut] | own] self` or `[var] name: Type [= default]`).
    fn formatFnParam(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        const start_idx = try self.formatLeadingInlineAttributes(children.items);
        var idx: usize = start_idx;
        while (idx < children.items.len) : (idx += 1) {
            const child_id = children.items[idx];
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_var or tok_kind == .kw_mut or tok_kind == .kw_own or
                    tok_kind == .kw_let or tok_kind == .kw_comptime)
                {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .ident and idx > 0) {
                    const prev_child = self.cst_arena.getNode(children.items[idx - 1]);
                    const is_after_colon = prev_child.subtree_size == 1 and !prev_child.token.isNone() and
                        self.token_buffer.getToken(prev_child.token).kind == .colon;
                    try self.emitTokenWithTrivia(child.token, null, false);
                    if (is_after_colon and idx + 1 < children.items.len) {
                        try self.doc_arena.emitText(" ");
                    }
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.type_params` generic parameter list (`[T: Bound1 + Bound2, const N: usize]`).
    fn formatTypeParams(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        self.in_type_context += 1;
        defer self.in_type_context -= 1;
        try self.formatSteerableDelimitedList(
            node_idx,
            .type_param,
            .lbracket,
            .rbracket,
            "[",
            "]",
            false,
        );
    }

    /// Formats a single `.type_param` node (`T: Bound1 + Bound2 = Default` or `const N: usize`).
    fn formatTypeParam(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_const) {
                    try self.emitTokenWithTrivia(child.token, "const", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .plus) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "+", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.where_clause` node (` where T: Bound1 + Bound2, U: Bound3`).
    fn formatWhereClause(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        self.in_type_context += 1;
        defer self.in_type_context -= 1;
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        try self.doc_arena.emitText(" ");
        var pred_count: usize = 0;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_where) {
                    try self.emitTokenWithTrivia(child.token, "where", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .comma) {
                    try self.emitTokenWithTrivia(child.token, ",", false);
                }
            } else if (child.kind == .where_pred) {
                if (pred_count > 0) {
                    try self.doc_arena.emitText(" ");
                }
                try self.formatWherePred(child_id);
                pred_count += 1;
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.where_pred` node (`T: Bound1 + Bound2`).
    fn formatWherePred(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .plus) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "+", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.type_args` list (`[T, U]`).
    fn formatTypeArgs(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatSteerableDelimitedList(node_idx, null, .lbracket, .rbracket, "[", "]", false);
    }

    /// Formats a steerable comma-separated list (`()`, `[]`, `{}`) with `if_break(",", "")`.
    fn formatSteerableDelimitedList(
        self: *CstFormatter,
        node_idx: CstNodeIndex,
        expected_elem_kind: ?CstNodeKind,
        open_kind: TokenKind,
        close_kind: TokenKind,
        open_str: []const u8,
        close_str: []const u8,
        has_flat_inner_padding: bool,
    ) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var open_pos: ?usize = null;
        var close_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == open_kind and open_pos == null) open_pos = idx;
                if (tok_kind == close_kind) close_pos = idx;
            }
        }

        if (open_pos == null or close_pos == null or close_pos.? <= open_pos.?) {
            try self.formatGenericChildren(node_idx);
            return;
        }

        const op_idx = open_pos.?;
        const cl_idx = close_pos.?;

        // Emit any prefix children before `open_kind`:
        for (children.items[0..op_idx]) |prefix_id| {
            try self.formatNode(prefix_id);
        }

        const open_tok = self.cst_arena.getNode(children.items[op_idx]).token;
        const close_tok = self.cst_arena.getNode(children.items[cl_idx]).token;

        const ElemWithSep = struct {
            elem_id: CstNodeIndex,
            comma_tok: TokenIndex = .none,
        };
        var elements: std.ArrayList(ElemWithSep) = .empty;
        defer elements.deinit(self.allocator);
        var has_trailing_comma = false;

        for (children.items[op_idx + 1 .. cl_idx]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .comma) {
                    has_trailing_comma = true;
                    if (elements.items.len > 0) {
                        elements.items[elements.items.len - 1].comma_tok = child.token;
                    }
                    continue;
                }
            }
            if (expected_elem_kind) |exp_k| {
                if (child.kind != exp_k) continue;
            }
            has_trailing_comma = false;
            try elements.append(self.allocator, .{ .elem_id = child_id });
        }

        if (elements.items.len == 0) {
            try self.formatEmptyContainer(open_tok, close_tok, open_str, close_str);
            return;
        }

        const is_call_node = node_idx.asInt() < self.cst_arena.countNodes() and
            self.cst_arena.getNode(node_idx).kind == .call_expr;
        if (is_call_node and elements.items.len == 1 and
            self.isHuggedSingleClosureCallArg(
                elements.items[0].elem_id,
                open_tok,
                close_tok,
                has_trailing_comma,
            ))
        {
            try self.emitTokenWithTrivia(open_tok, open_str, false);
            try self.formatCallArg(elements.items[0].elem_id);
            try self.emitTokenWithTrivia(close_tok, close_str, false);
            return;
        }

        try self.emitTokenLeadingAndGlyph(open_tok, open_str, false);
        const group_mode: GroupMode = if (has_trailing_comma) .force_break else .auto_fit;
        _ = try self.doc_arena.beginGroup(group_mode);
        try self.emitTrailingTrivia(open_tok);
        if (has_flat_inner_padding) {
            try self.doc_arena.emitLine();
        } else {
            try self.doc_arena.emitSoftLine();
        }
        try self.doc_arena.beginIndent(INDENT_SPACES);

        const is_index_brackets = node_idx.asInt() < self.cst_arena.countNodes() and
            self.cst_arena.getNode(node_idx).kind == .index_expr;
        if (is_index_brackets) {
            self.index_bracket_depth += 1;
        }
        defer if (is_index_brackets) {
            self.index_bracket_depth -= 1;
        };

        for (elements.items, 0..) |entry, elem_i| {
            try self.formatNode(entry.elem_id);
            if (!entry.comma_tok.isNone()) {
                try self.emitLeadingTrivia(entry.comma_tok, false);
                self.token_meta[entry.comma_tok.asInt()].is_token_emitted = true;
            }
            if (elem_i + 1 < elements.items.len) {
                try self.doc_arena.emitText(",");
                if (!entry.comma_tok.isNone()) {
                    try self.emitTrailingTrivia(entry.comma_tok);
                }
                try self.doc_arena.emitLine();
            } else {
                const node_kind_opt: ?CstNodeKind = if (node_idx.asInt() < self.cst_arena.countNodes())
                    self.cst_arena.getNode(node_idx).kind
                else
                    null;
                const elem_node = self.cst_arena.getNode(entry.elem_id);
                const is_variadic_or_slice_rest = elem_node.kind == .variadic_param or
                    (node_kind_opt == .slice_pat and
                        ((elem_node.kind == .wildcard_pat and
                            !elem_node.token.isNone() and
                            self.token_buffer.getToken(elem_node.token).kind == .dotdot) or
                            (elem_node.kind == .ident_pat and
                                self.hasDirectTokenKind(entry.elem_id, .dotdot))));
                const is_paren_or_tuple = (node_kind_opt == .tuple_or_paren_expr or node_kind_opt == .tuple_type);
                if (is_variadic_or_slice_rest) {
                    // Never emit a trailing comma after `...` variadic param or `.slice_pat` `..` rest pattern.
                } else if (is_paren_or_tuple and elements.items.len == 1) {
                    if (has_trailing_comma) {
                        try self.doc_arena.emitText(",");
                    }
                } else {
                    try self.doc_arena.emitIfBreak(",", "");
                }
                if (!entry.comma_tok.isNone()) {
                    try self.emitTrailingTrivia(entry.comma_tok);
                }
            }
        }

        if (!close_tok.isNone()) {
            const close_meta = self.token_meta[close_tok.asInt()];
            if (!close_meta.is_leading_consumed and close_meta.has_leading_comments) {
                try self.doc_arena.emitHardLine();
                try self.emitLeadingTrivia(close_tok, true);
            }
        }
        try self.doc_arena.endIndent(INDENT_SPACES);
        if (has_flat_inner_padding) {
            try self.doc_arena.emitLine();
        } else {
            try self.doc_arena.emitSoftLine();
        }
        try self.doc_arena.endGroup();
        try self.emitTokenWithTrivia(close_tok, close_str, false);
    }

    /// Formats a `.block` CST node (`{ stmts… [tail_expr] }` or `unsafe { … }` / `comptime { … }`).
    fn formatBlock(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        // Check for prefix `comptime` / `unsafe` / `async` block wrapper (with optional attributes/trailing `;`):
        var inner_block_pos: ?usize = null;
        var wrapper_kw_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .block and inner_block_pos == null) {
                inner_block_pos = idx;
            } else if (child.subtree_size == 1 and !child.token.isNone() and inner_block_pos == null) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_comptime or tok_kind == .kw_unsafe or tok_kind == .kw_async) {
                    wrapper_kw_pos = idx;
                }
            }
        }
        if (wrapper_kw_pos != null and inner_block_pos != null and wrapper_kw_pos.? < inner_block_pos.?) {
            const blk_idx = inner_block_pos.?;
            const start_idx = try self.formatLeadingStackedAttributes(children.items[0..blk_idx]);
            for (children.items[start_idx..blk_idx]) |prefix_id| {
                const prefix = self.cst_arena.getNode(prefix_id);
                if (prefix.subtree_size == 1 and !prefix.token.isNone()) {
                    try self.emitTokenWithTrivia(prefix.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.formatNode(prefix_id);
                }
            }
            try self.formatBlock(children.items[blk_idx]);
            for (children.items[blk_idx + 1 ..]) |suffix_id| {
                const suffix = self.cst_arena.getNode(suffix_id);
                if (suffix.subtree_size == 1 and !suffix.token.isNone() and
                    self.token_buffer.getToken(suffix.token).kind == .semi)
                {
                    if (self.hasUnconsumedLeadingComments(suffix.token)) {
                        if (!self.hasTrailingNewlineInstruction()) {
                            try self.doc_arena.emitHardLine();
                        }
                        try self.emitLeadingTrivia(suffix.token, false);
                    }
                    self.token_meta[suffix.token.asInt()].is_token_emitted = true;
                    try self.emitTrailingTrivia(suffix.token);
                } else {
                    try self.formatNode(suffix_id);
                }
            }
            return;
        }

        var lbrace_pos: ?usize = null;
        var rbrace_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .lbrace and lbrace_pos == null) lbrace_pos = idx;
                if (tok_kind == .rbrace) rbrace_pos = idx;
            }
        }

        if (lbrace_pos == null or rbrace_pos == null or rbrace_pos.? <= lbrace_pos.?) {
            try self.formatGenericChildren(node_idx);
            return;
        }

        const lb_idx = lbrace_pos.?;
        const rb_idx = rbrace_pos.?;
        const open_brace_tok = self.cst_arena.getNode(children.items[lb_idx]).token;
        const close_brace_tok = self.cst_arena.getNode(children.items[rb_idx]).token;

        // Filter out standalone `.empty_stmt` and bare `.semi` tokens while flushing their comments:
        var real_stmts: std.ArrayList(CstNodeIndex) = .empty;
        defer real_stmts.deinit(self.allocator);

        for (children.items[lb_idx + 1 .. rb_idx]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .empty_stmt or
                (child.subtree_size == 1 and !child.token.isNone() and
                    self.token_buffer.getToken(child.token).kind == .semi))
            {
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const rec = self.token_buffer.getToken(child.token);
                if (rec.kind == .invalid_token and rec.flags.is_synthesized) {
                    continue;
                }
            }
            try real_stmts.append(self.allocator, child_id);
        }

        if (real_stmts.items.len == 0) {
            try self.formatEmptyContainer(open_brace_tok, close_brace_tok, "{", "}");
            return;
        }

        try self.emitTokenWithTrivia(open_brace_tok, "{", false);
        try self.doc_arena.beginIndent(INDENT_SPACES);
        try self.doc_arena.emitHardLine();

        var stmt_i: usize = 0;
        var prev_end_tok: u32 = open_brace_tok.asInt() + 1;
        while (stmt_i < real_stmts.items.len) {
            const stmt_id = real_stmts.items[stmt_i];
            const first_tok = self.findFirstTokenInSubtree(stmt_id);
            if (!first_tok.isNone() and first_tok.asInt() > prev_end_tok) {
                try self.flushUnconsumedCommentsInRange(prev_end_tok, first_tok.asInt(), true);
            }

            if (stmt_i > 0) {
                if (self.hasNodeLeadingBlankLine(stmt_id) or self.hasNodeDocComment(stmt_id)) {
                    try self.doc_arena.emitBlankLine();
                } else {
                    try self.doc_arena.emitHardLine();
                }
            }

            if (try self.tryEmitSuppressedSiblingSpan(real_stmts.items, &stmt_i)) {
                const last_emitted = real_stmts.items[stmt_i - 1];
                const last_t = self.findLastTokenInSubtree(last_emitted);
                if (!last_t.isNone()) prev_end_tok = last_t.asInt() + 1;
                continue;
            }

            try self.formatNode(stmt_id);
            const last_t = self.findLastTokenInSubtree(stmt_id);
            if (!last_t.isNone()) prev_end_tok = last_t.asInt() + 1;
            stmt_i += 1;
        }

        if (!close_brace_tok.isNone() and close_brace_tok.asInt() > prev_end_tok) {
            try self.flushUnconsumedCommentsInRange(prev_end_tok, close_brace_tok.asInt(), true);
        }
        try self.emitLeadingTriviaBeforeCloseBrace(close_brace_tok);
        try self.doc_arena.endIndent(INDENT_SPACES);
        try self.doc_arena.emitHardLine();
        try self.emitTokenWithTrivia(close_brace_tok, "}", false);
    }

    /// Formats a `.local_decl_stmt` (`[@state] (let | var) pat [: Type] [= expr [else { … }]];`).
    fn formatLocalDeclStmt(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var attr_end: usize = 0;
        var is_inline_attr_eligible = true;
        while (attr_end < children.items.len and
            self.cst_arena.getNode(children.items[attr_end]).kind == .attribute) : (attr_end += 1)
        {
            const attr_id = children.items[attr_end];
            if (self.hasDirectTokenKind(attr_id, .lparen)) {
                is_inline_attr_eligible = false;
            }
            const first_tok = self.findFirstTokenInSubtree(attr_id);
            const last_tok = self.findLastTokenInSubtree(attr_id);
            if (!first_tok.isNone() and !last_tok.isNone() and
                (self.token_meta[last_tok.asInt()].has_trailing_comments or
                    self.hasUnconsumedCommentsInTokenRange(first_tok.asInt(), last_tok.asInt(), true, true)))
            {
                is_inline_attr_eligible = false;
            }
        }
        if (attr_end > 0 and attr_end < children.items.len) {
            const after_tok = self.findFirstTokenInSubtree(children.items[attr_end]);
            if (after_tok.isNone() or
                self.token_meta[after_tok.asInt()].has_leading_newline or
                self.hasUnconsumedLeadingComments(after_tok))
            {
                is_inline_attr_eligible = false;
            }
        }
        const start_idx = if (attr_end > 0 and is_inline_attr_eligible)
            try self.formatLeadingInlineAttributes(children.items)
        else
            try self.formatLeadingStackedAttributes(children.items);

        var has_decl_kw = false;
        var has_emitted_semi = false;
        for (children.items[start_idx..]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .local_decl_introducer or
                    tok_kind == .kw_let or
                    tok_kind == .kw_var or
                    tok_kind == .kw_const)
                {
                    has_decl_kw = true;
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_mut) {
                    try self.emitTokenWithTrivia(child.token, "mut", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    has_emitted_semi = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .let_else_branch) {
                try self.doc_arena.emitText(" ");
                try self.formatLetElseBranch(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
        if (has_decl_kw and !has_emitted_semi) {
            try self.doc_arena.emitText(";");
        }
    }

    /// Formats a `.let_else_branch` (`else { … }`).
    fn formatLetElseBranch(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_else) {
                    try self.emitTokenWithTrivia(child.token, "else", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.loop_label` CST node (`label:` on loops or `:label` on `break`/`continue`).
    fn formatLoopLabel(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                try self.emitTokenWithTrivia(child.token, null, false);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.return_stmt`, `.break_stmt`, or `.continue_stmt` with a guaranteed `;`.
    fn formatJumpStmt(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatJumpCore(node_idx, true);
    }

    /// Formats an expression-position `.diverging_expr` (`return`, `break`, `continue`) without `;`.
    fn formatDivergingExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatJumpCore(node_idx, false);
    }

    /// Shared jump formatter for statement (`require_semi = true`) and expression (`false`) positions.
    fn formatJumpCore(
        self: *CstFormatter,
        node_idx: CstNodeIndex,
        has_required_semi: bool,
    ) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var has_emitted_semi = false;
        var has_emitted_kw = false;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (!has_emitted_kw and (tok_kind == .kw_return or tok_kind == .kw_break or
                    tok_kind == .kw_continue or tok_kind == .kw_yield))
                {
                    has_emitted_kw = true;
                    try self.emitTokenWithTrivia(child.token, null, false);
                    const has_payload = (idx + 1 < children.items.len and
                        !(self.cst_arena.getNode(children.items[idx + 1]).subtree_size == 1 and
                            !self.cst_arena.getNode(children.items[idx + 1]).token.isNone() and
                            self.token_buffer.getToken(self.cst_arena.getNode(children.items[idx + 1]).token).kind == .semi));
                    if (has_payload) {
                        try self.doc_arena.emitText(" ");
                    }
                } else if (tok_kind == .semi) {
                    if (has_required_semi) {
                        try self.emitTokenWithTrivia(child.token, ";", false);
                        has_emitted_semi = true;
                    }
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .loop_label) {
                try self.formatLoopLabel(child_id);
                const has_following_expr = (idx + 1 < children.items.len and
                    !(self.cst_arena.getNode(children.items[idx + 1]).subtree_size == 1 and
                        !self.cst_arena.getNode(children.items[idx + 1]).token.isNone() and
                        self.token_buffer.getToken(self.cst_arena.getNode(children.items[idx + 1]).token).kind == .semi));
                if (has_following_expr) {
                    try self.doc_arena.emitText(" ");
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        // Only emit trailing `;` when `node_idx` is a statement (not `diverging_expr`):
        if (has_required_semi and !has_emitted_semi) {
            try self.doc_arena.emitText(";");
        }
    }

    /// Formats a `.defer_stmt` (`defer expr;` or `defer { … }` or `errdefer |err| { … }`).
    fn formatDeferStmt(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var has_block_body = false;
        var has_emitted_semi = false;
        var pipe_count: usize = 0;

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .defer_introducer or tok_kind == .kw_defer or tok_kind == .kw_errdefer) {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .pipe) {
                    pipe_count += 1;
                    try self.emitTokenWithTrivia(child.token, "|", false);
                    if (pipe_count == 2) {
                        try self.doc_arena.emitText(" ");
                    }
                } else if (tok_kind == .semi) {
                    if (has_block_body) {
                        if (self.hasUnconsumedLeadingComments(child.token)) {
                            if (!self.hasTrailingNewlineInstruction()) {
                                try self.doc_arena.emitHardLine();
                            }
                            try self.emitLeadingTrivia(child.token, false);
                        }
                        self.token_meta[child.token.asInt()].is_token_emitted = true;
                        try self.emitTrailingTrivia(child.token);
                    } else {
                        try self.emitTokenWithTrivia(child.token, ";", false);
                        has_emitted_semi = true;
                    }
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .block) {
                has_block_body = true;
                try self.formatBlock(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_block_body and !has_emitted_semi) {
            try self.doc_arena.emitText(";");
        }
    }

    /// Formats an `.assign_stmt` (`lhs = rhs;` or `lhs += rhs;`).
    fn formatAssignStmt(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var has_emitted_semi = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    has_emitted_semi = true;
                } else if (isAssignmentOperatorToken(tok_kind)) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_emitted_semi) {
            try self.doc_arena.emitText(";");
        }
    }

    /// Returns whether `cst_id` is a block-bodied control-flow or `comptime` statement CST node.
    fn isBlockBodiedStmtCst(self: *const CstFormatter, cst_id: CstNodeIndex) bool {
        const node = self.cst_arena.getNode(cst_id);
        return switch (node.kind) {
            .if_expr,
            .match_expr,
            .for_stmt,
            .while_stmt,
            .loop_expr,
            .with_expr,
            .block,
            => true,
            .prefix_expr => blk: {
                if (node.subtree_size <= 1) break :blk false;
                const end_idx: usize = cst_id.asInt() + node.subtree_size;
                var first_child_id: CstNodeIndex = .none;
                var last_child_id: CstNodeIndex = .none;
                var child_cursor: usize = cst_id.asInt() + 1;
                while (child_cursor < end_idx) {
                    const child_id = CstNodeIndex.fromInt(@intCast(child_cursor));
                    const child = self.cst_arena.getNode(child_id);
                    if (!self.shouldSkipLeaf(child)) {
                        if (first_child_id.isNone()) first_child_id = child_id;
                        last_child_id = child_id;
                    }
                    child_cursor += @max(@as(usize, 1), child.subtree_size);
                }
                if (first_child_id.isNone() or last_child_id.isNone()) break :blk false;
                const first_child = self.cst_arena.getNode(first_child_id);
                if (first_child.subtree_size != 1 or first_child.token.isNone()) break :blk false;
                if (self.token_buffer.getToken(first_child.token).kind != .kw_comptime) break :blk false;
                break :blk self.isBlockBodiedStmtCst(last_child_id);
            },
            else => false,
        };
    }

    /// Formats an `.expr_stmt`, stripping redundant `;` on block-bodied control-flow statements.
    fn formatExprStmt(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var expr_child: ?CstNodeIndex = null;
        var semi_tok: TokenIndex = .none;

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (self.isZeroLengthCommentCarrierLeaf(child)) {
                if (!child.token.isNone()) {
                    try self.flushUnconsumedCommentsInRange(child.token.asInt(), child.token.asInt() + 1, true);
                }
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone() and
                self.token_buffer.getToken(child.token).kind == .semi)
            {
                semi_tok = child.token;
            } else if (expr_child == null) {
                expr_child = child_id;
            }
        }

        if (expr_child) |inner_id| {
            try self.formatNode(inner_id);
            if (self.isBlockBodiedStmtCst(inner_id)) {
                if (!semi_tok.isNone()) {
                    if (self.hasUnconsumedLeadingComments(semi_tok)) {
                        if (!self.hasTrailingNewlineInstruction()) {
                            try self.doc_arena.emitHardLine();
                        }
                        try self.emitLeadingTrivia(semi_tok, false);
                    }
                    self.token_meta[semi_tok.asInt()].is_token_emitted = true;
                    try self.emitTrailingTrivia(semi_tok);
                }
            } else {
                if (!semi_tok.isNone()) {
                    try self.emitTokenWithTrivia(semi_tok, ";", false);
                } else {
                    try self.doc_arena.emitText(";");
                }
            }
        } else if (!semi_tok.isNone()) {
            if (self.hasUnconsumedLeadingComments(semi_tok)) {
                if (!self.hasTrailingNewlineInstruction()) {
                    try self.doc_arena.emitHardLine();
                }
                try self.emitLeadingTrivia(semi_tok, false);
            }
            self.token_meta[semi_tok.asInt()].is_token_emitted = true;
            try self.emitTrailingTrivia(semi_tok);
        }
    }

    /// Returns whether `subtree_idx` contains a braced expression or pattern requiring outer parens.
    fn hasStructLitOrBlockInSubtree(self: *const CstFormatter, subtree_idx: CstNodeIndex) bool {
        const root = self.cst_arena.getNode(subtree_idx);
        const end_idx: usize = subtree_idx.asInt() + root.subtree_size;
        var idx: usize = subtree_idx.asInt();
        while (idx < end_idx) : (idx += 1) {
            const node = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(idx)));
            if (node.kind == .struct_lit_expr or
                node.kind == .view_block_expr or
                node.kind == .with_expr or
                node.kind == .struct_pat or
                node.kind == .block)
            {
                return true;
            }
            if (node.kind == .contextual_variant_expr or
                node.kind == .variant_pat or
                node.kind == .path_pat)
            {
                const sub_end: usize = @min(end_idx, idx + node.subtree_size);
                var sub_idx: usize = idx + 1;
                while (sub_idx < sub_end) : (sub_idx += 1) {
                    const sub_node = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sub_idx)));
                    if (sub_node.kind == .field_init or
                        sub_node.kind == .field_pat or
                        sub_node.kind == .struct_pat_start)
                    {
                        return true;
                    }
                    if (sub_node.subtree_size == 1 and !sub_node.token.isNone() and
                        self.token_buffer.getToken(sub_node.token).kind == .lbrace)
                    {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /// Formats a control-flow header expression, stripping redundant outer `(` and `)`.
    fn formatHeaderExprStrippingOuterParens(
        self: *CstFormatter,
        expr_idx: CstNodeIndex,
    ) anyerror!void {
        const node = self.cst_arena.getNode(expr_idx);
        if (node.kind == .tuple_or_paren_expr) {
            var children: std.ArrayList(CstNodeIndex) = .empty;
            defer children.deinit(self.allocator);
            try self.collectDirectChildren(expr_idx, &children);

            if (children.items.len == 3) {
                const open_child = self.cst_arena.getNode(children.items[0]);
                const inner_id = children.items[1];
                const close_child = self.cst_arena.getNode(children.items[2]);

                if (open_child.subtree_size == 1 and !open_child.token.isNone() and
                    close_child.subtree_size == 1 and !close_child.token.isNone() and
                    self.token_buffer.getToken(open_child.token).kind == .lparen and
                    self.token_buffer.getToken(close_child.token).kind == .rparen and
                    !self.token_buffer.getToken(close_child.token).flags.is_synthesized and
                    !self.hasStructLitOrBlockInSubtree(inner_id) and
                    !self.token_meta[open_child.token.asInt()].has_leading_comments and
                    !self.token_meta[close_child.token.asInt()].has_trailing_comments and
                    !self.hasUnconsumedCommentsInTokenRange(
                        open_child.token.asInt(),
                        close_child.token.asInt(),
                        true,
                        true,
                    ))
                {
                    try self.emitLeadingTrivia(open_child.token, false);
                    self.token_meta[open_child.token.asInt()].is_token_emitted = true;
                    try self.formatHeaderExprStrippingOuterParens(inner_id);
                    self.token_meta[close_child.token.asInt()].is_token_emitted = true;
                    try self.emitTrailingTrivia(close_child.token);
                    return;
                }
            }
        }
        try self.formatNode(expr_idx);
    }

    /// Formats an `.if_expr` (`if cond { … } else if cond2 { … } else { … }`).
    fn formatIfExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .if_introducer or tok_kind == .kw_if) {
                    try self.emitTokenWithTrivia(child.token, "if", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .if_cond) {
                try self.formatConditionHeader(child_id);
                try self.doc_arena.emitText(" ");
            } else if (child.kind == .block) {
                try self.formatBlock(child_id);
            } else if (child.kind == .else_branch) {
                try self.doc_arena.emitText(" ");
                try self.formatElseBranch(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats an `.if_cond` or `.while_header` condition, stripping redundant outer parens while preserving `(x := expr)`.
    fn formatConditionHeader(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        if (children.items.len == 1) {
            try self.formatHeaderExprStrippingOuterParens(children.items[0]);
            return;
        }

        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_let) {
                    try self.emitTokenWithTrivia(child.token, "let", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (idx == 0 or (idx > 0 and
                self.cst_arena.getNode(children.items[idx - 1]).subtree_size == 1 and
                !self.cst_arena.getNode(children.items[idx - 1]).token.isNone() and
                self.token_buffer.getToken(self.cst_arena.getNode(children.items[idx - 1]).token).kind == .eq))
            {
                try self.formatHeaderExprStrippingOuterParens(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats an `.else_branch` (`else if …` or `else { … }`).
    fn formatElseBranch(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_else) {
                    try self.emitTokenWithTrivia(child.token, "else", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.for_stmt` (`[label:] [comptime] for pat [, idx] in iter { … }`), stripping outer parens on `iter`.
    fn formatForStmt(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_comptime) {
                    try self.emitTokenWithTrivia(child.token, "comptime", false);
                    try self.doc_arena.emitText(" ");
                } else if (child.kind == .for_introducer or tok_kind == .kw_for) {
                    try self.emitTokenWithTrivia(child.token, "for", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .loop_label) {
                try self.formatLoopLabel(child_id);
                try self.doc_arena.emitText(" ");
            } else if (child.kind == .for_header) {
                try self.formatForHeader(child_id);
                try self.doc_arena.emitText(" ");
            } else if (child.kind == .block) {
                try self.formatBlock(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.for_header` (`[&[mut] | ref [mut] | own | mut] pat [, idx] in iter`).
    fn formatForHeader(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var has_seen_in = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_in) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "in", false);
                    try self.doc_arena.emitText(" ");
                    has_seen_in = true;
                    continue;
                } else if (!has_seen_in and tok_kind == .comma) {
                    try self.emitTokenWithTrivia(child.token, ",", false);
                    try self.doc_arena.emitText(" ");
                    continue;
                } else if (!has_seen_in and tok_kind == .amp) {
                    try self.emitTokenWithTrivia(child.token, "&", false);
                    continue;
                } else if (!has_seen_in and
                    (tok_kind == .kw_var or tok_kind == .kw_mut or tok_kind == .kw_own))
                {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                    continue;
                }
            }
            if (has_seen_in) {
                try self.formatHeaderExprStrippingOuterParens(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.while_stmt` (`[label:] while cond { … }`), stripping outer parens on `cond`.
    fn formatWhileStmt(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .while_introducer or tok_kind == .kw_while) {
                    try self.emitTokenWithTrivia(child.token, "while", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .loop_label) {
                try self.formatLoopLabel(child_id);
                try self.doc_arena.emitText(" ");
            } else if (child.kind == .while_header) {
                try self.formatConditionHeader(child_id);
                try self.doc_arena.emitText(" ");
            } else if (child.kind == .block) {
                try self.formatBlock(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.loop_expr` (`[label:] loop { … }`).
    fn formatLoopExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .loop_introducer or tok_kind == .kw_loop) {
                    try self.emitTokenWithTrivia(child.token, "loop", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .loop_label) {
                try self.formatLoopLabel(child_id);
                try self.doc_arena.emitText(" ");
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.walrus_cond_expr` (`([var] name [: Type] := expr)`), always preserving parens (`DR-21` §3.3).
    fn formatWalrusCondExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var is_expecting_type = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_var) {
                    try self.emitTokenWithTrivia(child.token, "var", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                    is_expecting_type = true;
                } else if (tok_kind == .colon_eq) {
                    is_expecting_type = false;
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, ":=", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (is_expecting_type) {
                is_expecting_type = false;
                self.in_type_context += 1;
                defer self.in_type_context -= 1;
                try self.formatNode(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.context_binding` (`context.slot = expr`).
    fn formatContextBinding(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                if (self.token_buffer.getToken(child.token).kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.with_expr` (`with context.slot = expr, … { … }`) with trailing-comma steerability.
    fn formatWithExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var with_tok: TokenIndex = .none;
        var bindings: std.ArrayList(WithBindingEntry) = .empty;
        defer bindings.deinit(self.allocator);
        var block_id: CstNodeIndex = .none;
        var has_trailing_comma = false;

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_with and with_tok.isNone()) {
                    with_tok = child.token;
                } else if (tok_kind == .comma) {
                    has_trailing_comma = true;
                    if (bindings.items.len > 0) {
                        bindings.items[bindings.items.len - 1].comma_tok = child.token;
                    }
                }
            } else if (child.kind == .context_binding) {
                has_trailing_comma = false;
                try bindings.append(self.allocator, .{ .binding_id = child_id });
            } else if (child.kind == .block) {
                block_id = child_id;
            }
        }

        if (with_tok.isNone() or bindings.items.len == 0 or block_id.isNone()) {
            try self.formatGenericChildren(node_idx);
            return;
        }

        try self.emitTokenLeadingAndGlyph(with_tok, "with", false);
        const group_mode: GroupMode = if (has_trailing_comma) .force_break else .auto_fit;
        _ = try self.doc_arena.beginGroup(group_mode);
        try self.emitTrailingTrivia(with_tok);
        try self.doc_arena.beginIndent(INDENT_SPACES);
        try self.doc_arena.emitLine();

        for (bindings.items, 0..) |entry, bind_i| {
            try self.formatContextBinding(entry.binding_id);
            if (!entry.comma_tok.isNone()) {
                try self.emitLeadingTrivia(entry.comma_tok, false);
                self.token_meta[entry.comma_tok.asInt()].is_token_emitted = true;
            }
            if (bind_i + 1 < bindings.items.len) {
                try self.doc_arena.emitText(",");
                if (!entry.comma_tok.isNone()) {
                    try self.emitTrailingTrivia(entry.comma_tok);
                }
                try self.doc_arena.emitLine();
            } else {
                try self.doc_arena.emitIfBreak(",", "");
                if (!entry.comma_tok.isNone()) {
                    try self.emitTrailingTrivia(entry.comma_tok);
                }
            }
        }

        try self.doc_arena.endIndent(INDENT_SPACES);
        try self.doc_arena.emitLine();
        try self.doc_arena.endGroup();
        try self.formatBlock(block_id);
    }

    /// Formats a `.contextual_variant_expr` (`.Variant`, `.Variant(args)`, or `.Variant { fields }`).
    fn formatContextualVariantExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        if (self.hasDirectChildKind(node_idx, .struct_lit_start) or
            self.hasDirectTokenKind(node_idx, .lbrace))
        {
            try self.formatStructLitExpr(node_idx);
        } else if (self.hasDirectTokenKind(node_idx, .lparen)) {
            try self.formatCallExpr(node_idx);
        } else {
            try self.formatGenericChildren(node_idx);
        }
    }

    /// Formats a `.match_expr` (`match scrutinee { arms… }`), stripping outer parens on `scrutinee`.
    fn formatMatchExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var lbrace_pos: ?usize = null;
        var rbrace_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .lbrace and lbrace_pos == null) lbrace_pos = idx;
                if (tok_kind == .rbrace) rbrace_pos = idx;
            }
        }

        if (lbrace_pos == null or rbrace_pos == null or rbrace_pos.? <= lbrace_pos.?) {
            try self.formatGenericChildren(node_idx);
            return;
        }

        const lb_idx = lbrace_pos.?;
        const rb_idx = rbrace_pos.?;

        for (children.items[0..lb_idx]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .loop_label) {
                try self.formatLoopLabel(child_id);
                try self.doc_arena.emitText(" ");
            } else if (child.subtree_size == 1 and !child.token.isNone() and
                (child.kind == .match_introducer or
                    self.token_buffer.getToken(child.token).kind == .kw_match))
            {
                try self.emitTokenWithTrivia(child.token, "match", false);
                try self.doc_arena.emitText(" ");
            } else {
                try self.formatHeaderExprStrippingOuterParens(child_id);
            }
        }

        try self.doc_arena.emitText(" ");
        const open_brace_tok = self.cst_arena.getNode(children.items[lb_idx]).token;
        const close_brace_tok = self.cst_arena.getNode(children.items[rb_idx]).token;
        const arms = children.items[lb_idx + 1 .. rb_idx];

        if (arms.len == 0) {
            try self.formatEmptyContainer(open_brace_tok, close_brace_tok, "{", "}");
            return;
        }

        try self.emitTokenWithTrivia(open_brace_tok, "{", false);
        try self.doc_arena.beginIndent(INDENT_SPACES);
        try self.doc_arena.emitHardLine();

        for (arms, 0..) |arm_id, arm_i| {
            if (arm_i > 0) {
                if (self.hasNodeLeadingBlankLine(arm_id)) {
                    try self.doc_arena.emitBlankLine();
                } else {
                    try self.doc_arena.emitHardLine();
                }
            }
            try self.formatMatchArm(arm_id);
        }

        try self.emitLeadingTriviaBeforeCloseBrace(close_brace_tok);
        try self.doc_arena.endIndent(INDENT_SPACES);
        try self.doc_arena.emitHardLine();
        try self.emitTokenWithTrivia(close_brace_tok, "}", false);
    }

    /// Formats a `.match_arm` (`pat [if guard] => body,`).
    fn formatMatchArm(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var has_emitted_comma = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_if) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "if", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .fat_arrow) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=>", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .comma) {
                    try self.emitTokenWithTrivia(child.token, ",", false);
                    has_emitted_comma = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        if (!has_emitted_comma) {
            try self.doc_arena.emitText(",");
        }
    }

    /// Formats a `.call_expr` (`callee[T](arg1, name: arg2)`).
    fn formatCallExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatSteerableDelimitedList(
            node_idx,
            .call_arg,
            .lparen,
            .rparen,
            "(",
            ")",
            false,
        );
    }

    /// Formats a `.call_arg` (`[label:] expr`).
    fn formatCallArg(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.struct_lit_expr` (`Point { x: 1, y: 2 }` or `Point { ..base }`).
    fn formatStructLitExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var open_pos: ?usize = null;
        var close_pos: ?usize = null;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if ((child.kind == .struct_lit_start or tok_kind == .lbrace) and open_pos == null) {
                    open_pos = idx;
                } else if (tok_kind == .rbrace) {
                    close_pos = idx;
                }
            }
        }

        if (open_pos == null or close_pos == null or close_pos.? <= open_pos.?) {
            try self.formatGenericChildren(node_idx);
            return;
        }

        const op_idx = open_pos.?;
        const cl_idx = close_pos.?;
        {
            self.in_type_context += 1;
            defer self.in_type_context -= 1;
            for (children.items[0..op_idx]) |prefix_id| {
                try self.formatNode(prefix_id);
            }
        }
        try self.doc_arena.emitText(" ");

        const open_tok = self.cst_arena.getNode(children.items[op_idx]).token;
        const close_tok = self.cst_arena.getNode(children.items[cl_idx]).token;

        const FieldWithSep = struct {
            field_id: CstNodeIndex,
            comma_tok: TokenIndex = .none,
            is_spread: bool = false,
        };
        var fields: std.ArrayList(FieldWithSep) = .empty;
        defer fields.deinit(self.allocator);
        var has_trailing_comma = false;

        for (children.items[op_idx + 1 .. cl_idx]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                if (self.token_buffer.getToken(child.token).kind == .comma) {
                    has_trailing_comma = true;
                    if (fields.items.len > 0) {
                        fields.items[fields.items.len - 1].comma_tok = child.token;
                    }
                    continue;
                }
            }
            if (child.kind == .field_init) {
                has_trailing_comma = false;
                const is_spread = self.hasDirectTokenKind(child_id, .dotdot);
                try fields.append(self.allocator, .{
                    .field_id = child_id,
                    .is_spread = is_spread,
                });
            }
        }

        if (fields.items.len == 0) {
            try self.formatEmptyContainer(open_tok, close_tok, "{", "}");
            return;
        }

        try self.emitTokenLeadingAndGlyph(open_tok, "{", false);
        const group_mode: GroupMode = if (has_trailing_comma) .force_break else .auto_fit;
        _ = try self.doc_arena.beginGroup(group_mode);
        try self.emitTrailingTrivia(open_tok);
        try self.doc_arena.emitLine();
        try self.doc_arena.beginIndent(INDENT_SPACES);

        for (fields.items, 0..) |entry, field_i| {
            try self.formatFieldInit(entry.field_id);
            if (!entry.comma_tok.isNone()) {
                try self.emitLeadingTrivia(entry.comma_tok, false);
                self.token_meta[entry.comma_tok.asInt()].is_token_emitted = true;
            }
            if (field_i + 1 < fields.items.len) {
                try self.doc_arena.emitText(",");
                if (!entry.comma_tok.isNone()) {
                    try self.emitTrailingTrivia(entry.comma_tok);
                }
                try self.doc_arena.emitLine();
            } else {
                if (!entry.is_spread) {
                    try self.doc_arena.emitIfBreak(",", "");
                }
                if (!entry.comma_tok.isNone()) {
                    try self.emitTrailingTrivia(entry.comma_tok);
                }
            }
        }

        if (!close_tok.isNone()) {
            const close_meta = self.token_meta[close_tok.asInt()];
            if (!close_meta.is_leading_consumed and close_meta.has_leading_comments) {
                try self.doc_arena.emitHardLine();
                try self.emitLeadingTrivia(close_tok, true);
            }
        }
        try self.doc_arena.endIndent(INDENT_SPACES);
        try self.doc_arena.emitLine();
        try self.doc_arena.endGroup();
        try self.emitTokenWithTrivia(close_tok, "}", false);
    }

    /// Formats a `.field_init` (`name: expr`, shorthand `name`, `..`, `..base`, or `..own base`).
    fn formatFieldInit(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_own) {
                    try self.emitTokenWithTrivia(child.token, "own", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .comma) {
                    self.token_meta[child.token.asInt()].is_token_emitted = true;
                    try self.emitTrailingTrivia(child.token);
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.view_block_expr` (`Component(args) { … }` or `Component { … }`).
    fn formatViewBlockExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .block) {
                try self.doc_arena.emitText(" ");
                try self.formatBlock(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Returns whether `node_idx` is a scalar literal or unary-negated scalar literal expression.
    fn isScalarLiteralElement(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        const node = self.cst_arena.getNode(node_idx);
        if (node.kind == .literal_expr) return true;
        if (node.kind == .prefix_expr) {
            const end_idx: usize = node_idx.asInt() + node.subtree_size;
            var idx: usize = node_idx.asInt() + 1;
            while (idx < end_idx) : (idx += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(idx)));
                if (sub.kind == .literal_expr) return true;
            }
        }
        return false;
    }

    /// Returns the formatted byte length of `tok_id` (accounting for `42u64` -> `42_u64` suffix normalization).
    fn measureTokenFormattedByteLen(self: *const CstFormatter, tok_id: TokenIndex) usize {
        if (tok_id.isNone()) return 0;
        const tok_rec = self.token_buffer.getToken(tok_id);
        if (tok_rec.flags.is_synthesized) return 0;
        var byte_len: usize = tok_rec.byte_len;
        if (!tok_rec.flags.has_lexer_error and (tok_rec.kind == .int_lit or tok_rec.kind == .float_lit)) {
            if (lexer.extractNumericSuffix(self.getTokenLexeme(tok_id))) |parsed| {
                if (parsed.suffix_type != null and !parsed.has_underscore_sep) {
                    byte_len += 1;
                }
            } else |_| {}
        }
        return byte_len;
    }

    /// Measures the exact formatted column width of scalar literal element `elem_id`.
    fn measureScalarLiteralWidth(self: *const CstFormatter, elem_id: CstNodeIndex) usize {
        const root = self.cst_arena.getNode(elem_id);
        if (root.subtree_size == 1) {
            if (self.shouldSkipLeaf(root)) return 0;
            return self.measureTokenFormattedByteLen(root.token);
        }
        var total_bytes: usize = 0;
        const end_idx: usize = elem_id.asInt() + root.subtree_size;
        var idx: usize = elem_id.asInt() + 1;
        while (idx < end_idx) : (idx += 1) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(idx)));
            if (sub.subtree_size == 1 and !self.shouldSkipLeaf(sub)) {
                total_bytes += self.measureTokenFormattedByteLen(sub.token);
            }
        }
        return total_bytes;
    }

    /// Formats an `.array_expr` (`[a, b, c]`, `[val; count]`, or `GroupMode.columnar_grid`).
    fn formatArrayExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        // [1] Check for repeat array syntax `[val; count]`:
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone() and
                self.token_buffer.getToken(child.token).kind == .semi)
            {
                for (children.items) |sub_id| {
                    const sub = self.cst_arena.getNode(sub_id);
                    if (sub.subtree_size == 1 and !sub.token.isNone()) {
                        const tk = self.token_buffer.getToken(sub.token).kind;
                        if (tk == .semi) {
                            try self.emitTokenWithTrivia(sub.token, ";", false);
                            try self.doc_arena.emitText(" ");
                        } else {
                            try self.emitTokenWithTrivia(sub.token, null, false);
                        }
                    } else {
                        try self.formatNode(sub_id);
                    }
                }
                return;
            }
        }

        // [2] Check if eligible for `GroupMode.columnar_grid` (`> 8` scalar literal elements):
        var open_tok: TokenIndex = .none;
        var close_tok: TokenIndex = .none;
        var elements: std.ArrayList(CstNodeIndex) = .empty;
        defer elements.deinit(self.allocator);
        var has_trailing_comma = false;
        var is_all_scalars = true;

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tk = self.token_buffer.getToken(child.token).kind;
                if (tk == .lbracket and open_tok.isNone()) {
                    open_tok = child.token;
                    continue;
                } else if (tk == .rbracket) {
                    close_tok = child.token;
                    continue;
                } else if (tk == .comma) {
                    has_trailing_comma = true;
                    continue;
                }
            }
            has_trailing_comma = false;
            if (!self.isScalarLiteralElement(child_id)) {
                is_all_scalars = false;
            }
            try elements.append(self.allocator, child_id);
        }

        const has_inner_comments = if (!open_tok.isNone() and !close_tok.isNone())
            self.hasUnconsumedCommentsInTokenRange(open_tok.asInt(), close_tok.asInt(), true, true)
        else
            false;

        if (is_all_scalars and elements.items.len >= COLUMNAR_GRID_MIN_ELEMENTS and !has_inner_comments) {
            // Measure max element width for deterministic `GroupMode.columnar_grid` packing:
            var max_elem_len: usize = 1;
            for (elements.items) |elem_id| {
                max_elem_len = @max(max_elem_len, self.measureScalarLiteralWidth(elem_id));
            }

            for (children.items) |child_id| {
                const child = self.cst_arena.getNode(child_id);
                if (child.subtree_size == 1 and !child.token.isNone() and
                    self.token_buffer.getToken(child.token).kind == .comma)
                {
                    self.token_meta[child.token.asInt()].is_token_emitted = true;
                }
            }

            const cell_width = max_elem_len + 2;
            const cols_per_row: usize = std.math.clamp(
                (MAX_LINE_WIDTH - 8) / @max(@as(usize, 1), cell_width),
                1,
                COLUMNAR_GRID_MAX_COLS,
            );
            const grid_padding_spaces: [MAX_LINE_WIDTH]u8 = @splat(' ');
            const group_mode: GroupMode = if (has_trailing_comma) .force_break else .columnar_grid;

            try self.emitTokenLeadingAndGlyph(open_tok, "[", false);
            _ = try self.doc_arena.beginGroup(group_mode);
            try self.emitTrailingTrivia(open_tok);
            try self.doc_arena.beginIndent(INDENT_SPACES);
            try self.doc_arena.emitSoftLine();

            for (elements.items, 0..) |elem_id, elem_i| {
                const elem_len = self.measureScalarLiteralWidth(elem_id);
                const is_row_end = ((elem_i + 1) % cols_per_row == 0) or
                    (elem_i + 1 == elements.items.len);

                // Left-pad numeric literals within the column cell only when the grid group breaks:
                if (elem_len < max_elem_len) {
                    const pad_len = @min(max_elem_len - elem_len, grid_padding_spaces.len);
                    try self.doc_arena.emitIfBreak(grid_padding_spaces[0..pad_len], "");
                }
                try self.formatNode(elem_id);

                if (elem_i + 1 < elements.items.len) {
                    try self.doc_arena.emitText(",");
                    if (!is_row_end) {
                        try self.doc_arena.emitText(" ");
                    } else {
                        try self.doc_arena.emitLine();
                    }
                } else {
                    try self.doc_arena.emitIfBreak(",", "");
                }
            }

            try self.doc_arena.endIndent(INDENT_SPACES);
            try self.doc_arena.emitSoftLine();
            try self.emitTokenWithTrivia(close_tok, "]", false);
            try self.doc_arena.endGroup();
            return;
        }

        try self.formatSteerableDelimitedList(node_idx, null, .lbracket, .rbracket, "[", "]", false);
    }

    /// Formats a `.tuple_or_paren_expr` (`(a)` or `(a, b)`).
    fn formatTupleOrParenExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatSteerableDelimitedList(node_idx, null, .lparen, .rparen, "(", ")", false);
    }

    /// Formats a `.closure_expr` (`[@builder] [own] [async] |a: i32, b| [-> Ret] expr` or `|| { … }`).
    fn formatClosureExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        const start_idx = try self.formatLeadingInlineAttributes(children.items);
        var pipe_count: usize = 0;
        var param_count: usize = 0;
        for (children.items[start_idx..], start_idx..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            const has_return_type_next = idx + 1 < children.items.len and
                self.cst_arena.getNode(children.items[idx + 1]).kind == .return_type;
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_own or tok_kind == .kw_async) {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .pipepipe) {
                    try self.emitTokenWithTrivia(child.token, "||", false);
                    if (!has_return_type_next) {
                        try self.doc_arena.emitText(" ");
                    }
                    pipe_count = 2;
                } else if (tok_kind == .pipe) {
                    pipe_count += 1;
                    try self.emitTokenWithTrivia(child.token, "|", false);
                    if (pipe_count == 2 and !has_return_type_next) {
                        try self.doc_arena.emitText(" ");
                    }
                } else if (tok_kind == .comma) {
                    try self.emitTokenWithTrivia(child.token, ",", false);
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .closure_param) {
                if (param_count > 0) {
                    try self.doc_arena.emitText(" ");
                }
                try self.formatClosureParam(child_id);
                param_count += 1;
            } else if (child.kind == .return_type) {
                try self.formatReturnType(child_id);
                if (idx + 1 < children.items.len) {
                    try self.doc_arena.emitText(" ");
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.closure_param` (`[var | &[mut] | own] name [: Type]`).
    fn formatClosureParam(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_var or tok_kind == .kw_mut or tok_kind == .kw_own) {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Step in a flattened `|>` pipe chain (`lhs |> step1 |> step2`).
    const PipeChainStep = struct {
        pipe_tok: TokenIndex,
        rhs_node: CstNodeIndex,
    };

    /// Recursively collects left-associative `|>` `.infix_expr` steps into `steps`.
    fn collectPipeChain(
        self: *const CstFormatter,
        node_idx: CstNodeIndex,
        base_out: *CstNodeIndex,
        steps: *std.ArrayList(PipeChainStep),
    ) !bool {
        const node = self.cst_arena.getNode(node_idx);
        if (node.kind != .infix_expr) return false;

        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);
        if (children.items.len != 3) return false;

        const op_child = self.cst_arena.getNode(children.items[1]);
        if (op_child.subtree_size != 1 or op_child.token.isNone()) return false;
        if (self.token_buffer.getToken(op_child.token).kind != .pipe_gt) return false;

        const lhs_id = children.items[0];
        const rhs_id = children.items[2];
        if (!(try self.collectPipeChain(lhs_id, base_out, steps))) {
            base_out.* = lhs_id;
        }
        try steps.append(self.allocator, .{
            .pipe_tok = op_child.token,
            .rhs_node = rhs_id,
        });
        return true;
    }

    /// Step in a flattened right-associative `orelse` / `catch` chain (`lhs orelse rhs`).
    const FallbackChainStep = struct {
        /// Operator keyword token (`orelse` or `catch`).
        op_tok: TokenIndex,
        /// Opening `|` token for a `catch |err|` payload capture, or `.none`.
        open_pipe_tok: TokenIndex = .none,
        /// Captured error identifier token inside `catch |err|`, or `.none`.
        capture_tok: TokenIndex = .none,
        /// Closing `|` token for a `catch |err|` payload capture, or `.none`.
        close_pipe_tok: TokenIndex = .none,
        /// Right-hand fallback expression or block CST node index.
        rhs_node: CstNodeIndex,
    };

    /// Extracts a single `orelse` or `catch [|err|]` `.infix_expr` step when `node_idx` matches.
    fn extractFallbackStep(
        self: *const CstFormatter,
        node_idx: CstNodeIndex,
        lhs_out: *CstNodeIndex,
        step_out: *FallbackChainStep,
    ) !bool {
        if (self.cst_arena.getNode(node_idx).kind != .infix_expr) return false;

        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);
        if (children.items.len < 3) return false;

        const op_child = self.cst_arena.getNode(children.items[1]);
        if (op_child.subtree_size != 1 or op_child.token.isNone()) return false;
        const op_kind = self.token_buffer.getToken(op_child.token).kind;
        if (op_kind != .kw_orelse and op_kind != .kw_catch) return false;

        if (children.items.len == 3) {
            lhs_out.* = children.items[0];
            step_out.* = .{
                .op_tok = op_child.token,
                .rhs_node = children.items[2],
            };
            return true;
        }
        if (children.items.len == 6 and op_kind == .kw_catch) {
            const open_pipe = self.cst_arena.getNode(children.items[2]);
            const cap_ident = self.cst_arena.getNode(children.items[3]);
            const close_pipe = self.cst_arena.getNode(children.items[4]);
            if (open_pipe.subtree_size == 1 and !open_pipe.token.isNone() and
                cap_ident.subtree_size == 1 and !cap_ident.token.isNone() and
                close_pipe.subtree_size == 1 and !close_pipe.token.isNone() and
                self.token_buffer.getToken(open_pipe.token).kind == .pipe and
                self.token_buffer.getToken(close_pipe.token).kind == .pipe)
            {
                lhs_out.* = children.items[0];
                step_out.* = .{
                    .op_tok = op_child.token,
                    .open_pipe_tok = open_pipe.token,
                    .capture_tok = cap_ident.token,
                    .close_pipe_tok = close_pipe.token,
                    .rhs_node = children.items[5],
                };
                return true;
            }
        }
        return false;
    }

    /// Emits `orelse` or `catch [|err|]` operator tokens for `step`.
    fn emitFallbackStepOp(self: *CstFormatter, step: FallbackChainStep) anyerror!void {
        const op_glyph: []const u8 = if (self.token_buffer.getToken(step.op_tok).kind == .kw_orelse)
            "orelse"
        else
            "catch";
        try self.emitTokenWithTrivia(step.op_tok, op_glyph, false);
        if (!step.open_pipe_tok.isNone()) {
            try self.doc_arena.emitText(" ");
            try self.emitTokenWithTrivia(step.open_pipe_tok, "|", false);
            try self.emitTokenWithTrivia(step.capture_tok, null, false);
            try self.emitTokenWithTrivia(step.close_pipe_tok, "|", false);
        }
    }

    /// Formats an `.infix_expr`, aligning `|>` pipe chains and `orelse` / `catch` fallbacks (`DR-21` §3.3).
    fn formatInfixExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var base_node: CstNodeIndex = .none;
        var pipe_steps: std.ArrayList(PipeChainStep) = .empty;
        defer pipe_steps.deinit(self.allocator);

        if (try self.collectPipeChain(node_idx, &base_node, &pipe_steps)) {
            var has_user_newline = false;
            for (pipe_steps.items) |step| {
                if (self.token_meta[step.pipe_tok.asInt()].has_leading_newline) {
                    has_user_newline = true;
                }
            }
            const mode: GroupMode = if (has_user_newline) .force_break else .auto_fit;
            _ = try self.doc_arena.beginGroup(mode);
            try self.formatNode(base_node);
            try self.doc_arena.beginIndent(INDENT_SPACES);
            for (pipe_steps.items) |step| {
                try self.doc_arena.emitLine();
                try self.emitTokenWithTrivia(step.pipe_tok, "|>", false);
                try self.doc_arena.emitText(" ");
                try self.formatNode(step.rhs_node);
            }
            try self.doc_arena.endIndent(INDENT_SPACES);
            try self.doc_arena.endGroup();
            return;
        }

        var fallback_lhs: CstNodeIndex = .none;
        var curr_fallback: FallbackChainStep = undefined;
        if (try self.extractFallbackStep(node_idx, &fallback_lhs, &curr_fallback)) {
            var fallback_steps: std.ArrayList(FallbackChainStep) = .empty;
            defer fallback_steps.deinit(self.allocator);

            var next_lhs: CstNodeIndex = .none;
            var next_step: FallbackChainStep = undefined;
            while (try self.extractFallbackStep(curr_fallback.rhs_node, &next_lhs, &next_step)) {
                curr_fallback.rhs_node = next_lhs;
                try fallback_steps.append(self.allocator, curr_fallback);
                curr_fallback = next_step;
            }
            try fallback_steps.append(self.allocator, curr_fallback);

            try self.formatNode(fallback_lhs);
            if (fallback_steps.items.len == 1 and
                !self.token_meta[fallback_steps.items[0].op_tok.asInt()].has_leading_newline and
                self.isBlockBodiedStmtCst(fallback_steps.items[0].rhs_node))
            {
                try self.doc_arena.emitText(" ");
                try self.emitFallbackStepOp(fallback_steps.items[0]);
                try self.doc_arena.emitText(" ");
                try self.formatNode(fallback_steps.items[0].rhs_node);
                return;
            }

            var has_fallback_newline = false;
            for (fallback_steps.items) |step| {
                if (self.token_meta[step.op_tok.asInt()].has_leading_newline) {
                    has_fallback_newline = true;
                }
            }
            const fallback_mode: GroupMode = if (has_fallback_newline) .force_break else .auto_fit;
            _ = try self.doc_arena.beginGroup(fallback_mode);
            try self.doc_arena.beginIndent(INDENT_SPACES);
            for (fallback_steps.items) |step| {
                try self.doc_arena.emitLine();
                try self.emitFallbackStepOp(step);
                try self.doc_arena.emitText(" ");
                try self.formatNode(step.rhs_node);
            }
            try self.doc_arena.endIndent(INDENT_SPACES);
            try self.doc_arena.endGroup();
            return;
        }

        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        // Compact `$-K` and `$+K` integer-literal offsets inside `[…]` (`DR-21` §3.3):
        if (self.index_bracket_depth > 0 and children.items.len == 3) {
            const lhs_child = self.cst_arena.getNode(children.items[0]);
            const op_child = self.cst_arena.getNode(children.items[1]);
            const rhs_child = self.cst_arena.getNode(children.items[2]);
            if (lhs_child.subtree_size == 1 and !lhs_child.token.isNone() and
                op_child.subtree_size == 1 and !op_child.token.isNone() and
                rhs_child.subtree_size == 1 and !rhs_child.token.isNone())
            {
                const lhs_kind = self.token_buffer.getToken(lhs_child.token).kind;
                const op_kind = self.token_buffer.getToken(op_child.token).kind;
                const rhs_kind = self.token_buffer.getToken(rhs_child.token).kind;
                if (lhs_kind == .dollar and
                    (op_kind == .minus or op_kind == .plus) and
                    rhs_kind == .int_lit and
                    !self.hasUnconsumedCommentsInTokenRange(
                        lhs_child.token.asInt(),
                        rhs_child.token.asInt(),
                        true,
                        true,
                    ))
                {
                    try self.formatNode(children.items[0]);
                    try self.emitTokenWithTrivia(op_child.token, null, false);
                    try self.formatNode(children.items[2]);
                    return;
                }
            }
        }

        var pipe_capture_count: usize = 0;
        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (idx > 0 and idx + 1 < children.items.len and
                child.subtree_size == 1 and !child.token.isNone())
            {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .dotdot or tok_kind == .dotdoteq) {
                    // Range operators `0..10` and `0..=10` have no spaces around `..` / `..=`:
                    try self.emitTokenWithTrivia(child.token, null, false);
                } else if (tok_kind == .kw_is) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "is", false);
                    const next_child = self.cst_arena.getNode(children.items[idx + 1]);
                    const is_followed_by_not = next_child.subtree_size == 1 and
                        !next_child.token.isNone() and
                        self.token_buffer.getToken(next_child.token).kind == .kw_not;
                    if (!is_followed_by_not) {
                        try self.doc_arena.emitText(" ");
                    }
                } else if (tok_kind == .kw_not) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "not", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_catch or tok_kind == .kw_orelse) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .pipe and pipe_capture_count > 0) {
                    pipe_capture_count = 0;
                    try self.emitTokenWithTrivia(child.token, "|", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .pipe and children.items.len > 3) {
                    pipe_capture_count = 1;
                    try self.emitTokenWithTrivia(child.token, "|", false);
                } else if (pipe_capture_count == 1 and isRenamableIdentifierKind(tok_kind)) {
                    try self.emitTokenWithTrivia(child.token, null, false);
                } else {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.prefix_expr` (`-x`, `not x`, `~x`, `&x`, `&mut x`, `&out x`, `&raw [mut] x`, `own x`, `..b`).
    fn formatPrefixExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if ((tok_kind == .kw_mut or tok_kind == .kw_own or
                    tok_kind == .kw_let or tok_kind == .kw_not or tok_kind == .kw_comptime or
                    tok_kind == .ident) and
                    idx + 1 < children.items.len)
                {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .minus and idx + 1 < children.items.len) {
                    try self.emitTokenWithTrivia(child.token, "-", false);
                    const next_tok = self.findFirstTokenInSubtree(children.items[idx + 1]);
                    if (!next_tok.isNone() and self.token_buffer.getToken(next_tok).kind == .minus) {
                        try self.doc_arena.emitText(" ");
                    }
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a chain of `.field_or_method_expr`, `.postfix_deref_expr`, `.postfix_try_expr`, and `.postfix_await_expr`.
    fn formatPostfixChain(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var chain_nodes: std.ArrayList(CstNodeIndex) = .empty;
        defer chain_nodes.deinit(self.allocator);

        var curr_id = node_idx;
        var dot_link_count: usize = 0;
        var has_user_newline = false;

        while (true) {
            const curr = self.cst_arena.getNode(curr_id);
            if (curr.kind != .field_or_method_expr and
                curr.kind != .postfix_deref_expr and
                curr.kind != .postfix_try_expr and
                curr.kind != .postfix_await_expr)
            {
                break;
            }
            var sub_children: std.ArrayList(CstNodeIndex) = .empty;
            defer sub_children.deinit(self.allocator);
            try self.collectDirectChildren(curr_id, &sub_children);
            if (sub_children.items.len < 2) break;

            if (curr.kind == .field_or_method_expr) {
                dot_link_count += 1;
                const second = self.cst_arena.getNode(sub_children.items[1]);
                if (second.subtree_size == 1 and !second.token.isNone() and
                    self.token_meta[second.token.asInt()].has_leading_newline)
                {
                    has_user_newline = true;
                }
            }
            try chain_nodes.append(self.allocator, curr_id);
            curr_id = sub_children.items[0];
        }

        const base_id = curr_id;
        std.mem.reverse(CstNodeIndex, chain_nodes.items);

        var is_qualified_path_prefix = self.cst_arena.getNode(base_id).subtree_size == 1;
        if (is_qualified_path_prefix and chain_nodes.items.len > 1) {
            for (chain_nodes.items[0 .. chain_nodes.items.len - 1]) |prefix_link_id| {
                const prefix_link = self.cst_arena.getNode(prefix_link_id);
                if (prefix_link.kind != .field_or_method_expr or
                    self.hasDirectTokenKind(prefix_link_id, .lparen))
                {
                    is_qualified_path_prefix = false;
                    break;
                }
            }
        }

        if ((dot_link_count >= 2 and !is_qualified_path_prefix) or has_user_newline) {
            const mode: GroupMode = if (has_user_newline) .force_break else .auto_fit;
            _ = try self.doc_arena.beginGroup(mode);
            try self.formatNode(base_id);
            try self.doc_arena.beginIndent(INDENT_SPACES);

            for (chain_nodes.items) |link_id| {
                const link = self.cst_arena.getNode(link_id);
                if (link.kind == .field_or_method_expr) {
                    try self.doc_arena.emitSoftLine();
                    try self.formatSingleChainSuffix(link_id);
                } else {
                    try self.formatSingleChainSuffix(link_id);
                }
            }

            try self.doc_arena.endIndent(INDENT_SPACES);
            try self.doc_arena.endGroup();
        } else {
            try self.formatNode(base_id);
            for (chain_nodes.items) |link_id| {
                try self.formatSingleChainSuffix(link_id);
            }
        }
    }

    /// Formats the suffix portion (excluding `children[0]` receiver) of a postfix chain node.
    fn formatSingleChainSuffix(self: *CstFormatter, link_id: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(link_id, &children);
        if (children.items.len < 2) return;

        // Check if this `.field_or_method_expr` has a call argument list `( … )`:
        var lparen_pos: ?usize = null;
        var rparen_pos: ?usize = null;
        for (children.items[1..], 1..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tk = self.token_buffer.getToken(child.token).kind;
                if (tk == .lparen and lparen_pos == null) lparen_pos = idx;
                if (tk == .rparen) rparen_pos = idx;
            }
        }

        if (lparen_pos != null and rparen_pos != null and rparen_pos.? > lparen_pos.?) {
            const lp_idx = lparen_pos.?;
            for (children.items[1..lp_idx]) |pre_id| {
                const pre = self.cst_arena.getNode(pre_id);
                if (pre.subtree_size == 1 and !pre.token.isNone()) {
                    try self.emitTokenWithTrivia(pre.token, null, false);
                } else {
                    try self.formatNode(pre_id);
                }
            }
            // Format `( … )` call args on the method call using steerable comma rules:
            const open_tok = self.cst_arena.getNode(children.items[lp_idx]).token;
            const close_tok = self.cst_arena.getNode(children.items[rparen_pos.?]).token;

            const ArgWithSep = struct {
                arg_id: CstNodeIndex,
                comma_tok: TokenIndex = .none,
            };
            var args: std.ArrayList(ArgWithSep) = .empty;
            defer args.deinit(self.allocator);
            var has_trailing_comma = false;

            for (children.items[lp_idx + 1 .. rparen_pos.?]) |arg_child_id| {
                const arg_child = self.cst_arena.getNode(arg_child_id);
                if (arg_child.subtree_size == 1 and !arg_child.token.isNone()) {
                    if (self.token_buffer.getToken(arg_child.token).kind == .comma) {
                        has_trailing_comma = true;
                        if (args.items.len > 0) {
                            args.items[args.items.len - 1].comma_tok = arg_child.token;
                        }
                        continue;
                    }
                }
                if (arg_child.kind == .call_arg) {
                    has_trailing_comma = false;
                    try args.append(self.allocator, .{ .arg_id = arg_child_id });
                }
            }

            if (args.items.len == 0) {
                try self.formatEmptyContainer(open_tok, close_tok, "(", ")");
                return;
            }

            if (args.items.len == 1 and
                self.isHuggedSingleClosureCallArg(
                    args.items[0].arg_id,
                    open_tok,
                    close_tok,
                    has_trailing_comma,
                ))
            {
                try self.emitTokenWithTrivia(open_tok, "(", false);
                try self.formatCallArg(args.items[0].arg_id);
                try self.emitTokenWithTrivia(close_tok, ")", false);
                return;
            }

            try self.emitTokenLeadingAndGlyph(open_tok, "(", false);
            const arg_mode: GroupMode = if (has_trailing_comma) .force_break else .auto_fit;
            _ = try self.doc_arena.beginGroup(arg_mode);
            try self.emitTrailingTrivia(open_tok);
            try self.doc_arena.emitSoftLine();
            try self.doc_arena.beginIndent(INDENT_SPACES);

            for (args.items, 0..) |entry, arg_i| {
                try self.formatCallArg(entry.arg_id);
                if (!entry.comma_tok.isNone()) {
                    try self.emitLeadingTrivia(entry.comma_tok, false);
                    self.token_meta[entry.comma_tok.asInt()].is_token_emitted = true;
                }
                if (arg_i + 1 < args.items.len) {
                    try self.doc_arena.emitText(",");
                    if (!entry.comma_tok.isNone()) {
                        try self.emitTrailingTrivia(entry.comma_tok);
                    }
                    try self.doc_arena.emitLine();
                } else {
                    try self.doc_arena.emitIfBreak(",", "");
                    if (!entry.comma_tok.isNone()) {
                        try self.emitTrailingTrivia(entry.comma_tok);
                    }
                }
            }

            if (self.hasUnconsumedLeadingComments(close_tok)) {
                try self.doc_arena.emitHardLine();
                try self.emitLeadingTrivia(close_tok, true);
            }
            try self.doc_arena.endIndent(INDENT_SPACES);
            try self.doc_arena.emitSoftLine();
            try self.doc_arena.endGroup();
            try self.emitTokenWithTrivia(close_tok, ")", false);
            return;
        }

        for (children.items[1..]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                try self.emitTokenWithTrivia(child.token, null, false);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Returns whether `call_arg_id` is a single block-bodied closure argument that hugs `(` and `)`.
    fn isHuggedSingleClosureCallArg(
        self: *const CstFormatter,
        call_arg_id: CstNodeIndex,
        open_tok: TokenIndex,
        close_tok: TokenIndex,
        has_trailing_comma: bool,
    ) bool {
        if (has_trailing_comma or open_tok.isNone() or close_tok.isNone()) return false;
        const open_meta = self.token_meta[open_tok.asInt()];
        if (!open_meta.is_trailing_consumed and open_meta.has_trailing_comments) return false;
        if (self.hasUnconsumedLeadingComments(close_tok)) return false;

        const arg_node = self.cst_arena.getNode(call_arg_id);
        if (arg_node.kind != .call_arg or arg_node.subtree_size <= 1) return false;
        const first_arg_tok = self.findFirstTokenInSubtree(call_arg_id);
        if (first_arg_tok.isNone() or self.token_meta[first_arg_tok.asInt()].has_leading_newline) {
            return false;
        }

        const end_idx: usize = call_arg_id.asInt() + arg_node.subtree_size;
        var expr_id: CstNodeIndex = .none;
        var cursor: usize = call_arg_id.asInt() + 1;
        while (cursor < end_idx) {
            const child_id = CstNodeIndex.fromInt(@intCast(cursor));
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and self.shouldSkipLeaf(child)) {
                cursor += 1;
                continue;
            }
            if (!expr_id.isNone()) return false;
            expr_id = child_id;
            cursor += @max(@as(usize, 1), child.subtree_size);
        }
        if (expr_id.isNone()) return false;
        if (self.cst_arena.getNode(expr_id).kind != .closure_expr) return false;
        return self.hasDirectChildKind(expr_id, .block);
    }

    /// Formats an `.index_expr` (`base[i, j]`).
    fn formatIndexExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatSteerableDelimitedList(node_idx, null, .lbracket, .rbracket, "[", "]", false);
    }

    /// Formats a `.cast_expr` (`expr as Type`).
    fn formatCastExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_as) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "as", false);
                    try self.doc_arena.emitText(" ");
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Returns whether `node_idx` is a CST node representing a syntactic `Type` expression.
    fn isTypeCstNode(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        return switch (self.cst_arena.getNode(node_idx).kind) {
            .prim_type_node,
            .named_type,
            .ref_type,
            .ptr_type,
            .mode_type,
            .slice_or_array_type,
            .tuple_type,
            .fn_type,
            .closure_type,
            .optional_type,
            .result_type,
            .refined_type,
            .intersect_bound_type,
            .union_bound_type,
            => true,
            else => false,
        };
    }

    /// Returns whether `node_idx` is a Tier 4 slice reference `&[T]` or `&mut [T]` (`DR-22` Section 1.3).
    fn isSliceRefTypeNode(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        const node = self.cst_arena.getNode(node_idx);
        if (node.kind != .ref_type or node.subtree_size <= 1) return false;
        const end_idx: usize = node_idx.asInt() + node.subtree_size;
        var target_id: CstNodeIndex = .none;
        var cursor: usize = node_idx.asInt() + 1;
        while (cursor < end_idx) {
            const child_id = CstNodeIndex.fromInt(@intCast(cursor));
            const child = self.cst_arena.getNode(child_id);
            if (self.isTypeCstNode(child_id)) {
                target_id = child_id;
                break;
            }
            if (child.subtree_size == 1 and !self.shouldSkipLeaf(child)) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind != .amp and tok_kind != .kw_mut) return false;
            }
            cursor += @max(@as(usize, 1), child.subtree_size);
        }
        if (target_id.isNone()) return false;
        if (self.cst_arena.getNode(target_id).kind != .slice_or_array_type) return false;
        return !self.hasDirectTokenKind(target_id, .semi);
    }

    /// Matches comment-free `Option[T]` or `Result[T, E]` `.named_type` nodes for `T?` / `T!E` rewriting (`DR-22` §3.4).
    fn matchCanonicalStdlibType(
        self: *const CstFormatter,
        node_idx: CstNodeIndex,
    ) !?CanonicalStdlibType {
        const node = self.cst_arena.getNode(node_idx);
        if (node.kind != .named_type or node.subtree_size <= 1 or node.flags.has_error) return null;

        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);
        if (children.items.len != 2) return null;

        const name_child = self.cst_arena.getNode(children.items[0]);
        const args_id = children.items[1];
        const args_node = self.cst_arena.getNode(args_id);
        if (name_child.subtree_size != 1 or name_child.token.isNone() or args_node.kind != .type_args or args_node.flags.has_error) {
            return null;
        }
        const name_tok = name_child.token;
        const name_rec = self.token_buffer.getToken(name_tok);
        if (name_rec.flags.is_synthesized or name_rec.kind != .type_ident) return null;
        const name_lex = self.getTokenLexeme(name_tok);
        const is_option = std.mem.eql(u8, name_lex, "Option");
        const is_result = std.mem.eql(u8, name_lex, "Result");
        if (!is_option and !is_result) return null;

        var arg_children: std.ArrayList(CstNodeIndex) = .empty;
        defer arg_children.deinit(self.allocator);
        try self.collectDirectChildren(args_id, &arg_children);
        if (arg_children.items.len < 3) return null;

        const open_child = self.cst_arena.getNode(arg_children.items[0]);
        const close_child = self.cst_arena.getNode(arg_children.items[arg_children.items.len - 1]);
        if (open_child.subtree_size != 1 or open_child.token.isNone() or
            close_child.subtree_size != 1 or close_child.token.isNone())
        {
            return null;
        }
        const close_tok = close_child.token;
        if (self.token_buffer.getToken(open_child.token).kind != .lbracket or
            self.token_buffer.getToken(close_tok).kind != .rbracket or
            self.token_buffer.getToken(close_tok).flags.is_synthesized)
        {
            return null;
        }
        if (self.hasUnconsumedCommentsInTokenRange(name_tok.asInt(), close_tok.asInt(), true, true)) {
            return null;
        }

        var type_args_buf: [2]CstNodeIndex = .{ .none, .none };
        var type_arg_count: usize = 0;
        for (arg_children.items[1 .. arg_children.items.len - 1]) |arg_child_id| {
            if (self.isTypeCstNode(arg_child_id)) {
                if (type_arg_count >= 2) return null;
                type_args_buf[type_arg_count] = arg_child_id;
                type_arg_count += 1;
            } else {
                const leaf = self.cst_arena.getNode(arg_child_id);
                if (leaf.subtree_size != 1 or leaf.token.isNone() or
                    self.token_buffer.getToken(leaf.token).kind != .comma)
                {
                    return null;
                }
            }
        }

        if (is_option and type_arg_count == 1) {
            return .{
                .option = .{
                    .name_tok = name_tok,
                    .close_bracket_tok = close_tok,
                    .inner_type_id = type_args_buf[0],
                },
            };
        }
        if (is_result and type_arg_count == 2) {
            return .{
                .result = .{
                    .name_tok = name_tok,
                    .close_bracket_tok = close_tok,
                    .ok_type_id = type_args_buf[0],
                    .err_type_id = type_args_buf[1],
                },
            };
        }
        return null;
    }

    /// Computes the intrinsic 4-tier `TypePrec` of `node_idx` (`DR-22` Section 1.3).
    fn intrinsicTypePrec(self: *const CstFormatter, node_idx: CstNodeIndex) !TypePrec {
        const node = self.cst_arena.getNode(node_idx);
        if (node.subtree_size <= 1) return .tier4_primary;
        return switch (node.kind) {
            .refined_type, .intersect_bound_type, .union_bound_type => .tier0_open,
            .result_type => .tier1_result,
            .optional_type => .tier3_postfix,
            .ref_type => if (self.isSliceRefTypeNode(node_idx)) .tier4_primary else .tier2_prefix,
            .mode_type => blk: {
                const first_tok = self.findFirstTokenInSubtree(node_idx);
                if (!first_tok.isNone()) {
                    const tok_kind = self.token_buffer.getToken(first_tok).kind;
                    if (tok_kind == .kw_own or tok_kind == .tilde) break :blk .tier2_prefix;
                    if (tok_kind == .ident and std.mem.eql(u8, self.getTokenLexeme(first_tok), "distinct")) {
                        break :blk .tier0_open;
                    }
                }
                break :blk .tier4_primary;
            },
            .named_type => if (try self.matchCanonicalStdlibType(node_idx)) |canon| switch (canon) {
                .option => .tier3_postfix,
                .result => .tier1_result,
            } else .tier4_primary,
            else => .tier4_primary,
        };
    }

    /// Returns whether `node_idx` ends in an unparenthesized `.fn_type` or `.closure_type` tail.
    fn hasCallableTail(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        const node = self.cst_arena.getNode(node_idx);
        if (node.subtree_size <= 1) return false;
        return switch (node.kind) {
            .fn_type, .closure_type => true,
            .ptr_type, .ref_type, .mode_type => blk: {
                if (node.kind == .ref_type and self.isSliceRefTypeNode(node_idx)) break :blk false;
                const end_idx: usize = node_idx.asInt() + node.subtree_size;
                var last_type_child: CstNodeIndex = .none;
                var cursor: usize = node_idx.asInt() + 1;
                while (cursor < end_idx) {
                    const child_id = CstNodeIndex.fromInt(@intCast(cursor));
                    const child = self.cst_arena.getNode(child_id);
                    if (self.isTypeCstNode(child_id)) {
                        last_type_child = child_id;
                    }
                    cursor += @max(@as(usize, 1), child.subtree_size);
                }
                if (last_type_child.isNone()) break :blk false;
                break :blk self.hasCallableTail(last_type_child);
            },
            else => false,
        };
    }

    /// Marks discarded `Option[…]` / `Result[…]` wrapper tokens as consumed while preserving outer trivia.
    fn consumeStdlibTypeWrapperTokens(
        self: *CstFormatter,
        named_idx: CstNodeIndex,
        close_bracket_tok: TokenIndex,
    ) !void {
        var named_children: std.ArrayList(CstNodeIndex) = .empty;
        defer named_children.deinit(self.allocator);
        try self.collectDirectChildren(named_idx, &named_children);
        if (named_children.items.len != 2) return;

        const name_tok = self.cst_arena.getNode(named_children.items[0]).token;
        if (!name_tok.isNone() and name_tok.asInt() < self.token_meta.len) {
            self.token_meta[name_tok.asInt()].is_token_emitted = true;
            self.token_meta[name_tok.asInt()].is_leading_consumed = true;
            self.token_meta[name_tok.asInt()].is_trailing_consumed = true;
        }

        var arg_children: std.ArrayList(CstNodeIndex) = .empty;
        defer arg_children.deinit(self.allocator);
        try self.collectDirectChildren(named_children.items[1], &arg_children);
        for (arg_children.items) |arg_child_id| {
            if (self.isTypeCstNode(arg_child_id)) continue;
            const leaf = self.cst_arena.getNode(arg_child_id);
            if (leaf.subtree_size == 1 and !leaf.token.isNone() and leaf.token.asInt() < self.token_meta.len) {
                self.token_meta[leaf.token.asInt()].is_token_emitted = true;
                self.token_meta[leaf.token.asInt()].is_leading_consumed = true;
                if (leaf.token.asInt() != close_bracket_tok.asInt()) {
                    self.token_meta[leaf.token.asInt()].is_trailing_consumed = true;
                }
            }
        }
    }

    /// Formats a type CST node under the unified 4-tier `DR-22` precedence & `Option`/`Result` canonicalization rules.
    fn formatTypeNode(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatTypeNodeWithPrec(node_idx, .tier0_open, false, false);
    }

    /// Formats `node_idx` with contextual minimum precedence `min_prec` and callable-tail parenthesization guards.
    fn formatTypeNodeWithPrec(
        self: *CstFormatter,
        node_idx: CstNodeIndex,
        min_prec: TypePrec,
        has_right_suffix: bool,
        is_wrapping_bare_callable: bool,
    ) anyerror!void {
        const node = self.cst_arena.getNode(node_idx);
        if (node.subtree_size == 1) {
            if (!self.shouldSkipLeaf(node)) {
                self.in_type_context += 1;
                defer self.in_type_context -= 1;
                try self.emitTokenWithTrivia(node.token, null, false);
            }
            return;
        }

        const own_prec = try self.intrinsicTypePrec(node_idx);
        const needs_parens = (@backingInt(own_prec) < @backingInt(min_prec)) or
            ((has_right_suffix or is_wrapping_bare_callable) and self.hasCallableTail(node_idx));

        if (node.kind == .named_type) {
            if (try self.matchCanonicalStdlibType(node_idx)) |canon| {
                self.in_type_context += 1;
                defer self.in_type_context -= 1;
                switch (canon) {
                    .option => |opt_info| {
                        try self.emitLeadingTrivia(opt_info.name_tok, false);
                        try self.consumeStdlibTypeWrapperTokens(node_idx, opt_info.close_bracket_tok);
                        if (needs_parens) try self.doc_arena.emitText("(");
                        try self.formatTypeNodeWithPrec(opt_info.inner_type_id, .tier3_postfix, true, false);
                        try self.doc_arena.emitText("?");
                        if (needs_parens) try self.doc_arena.emitText(")");
                        try self.emitTrailingTrivia(opt_info.close_bracket_tok);
                        return;
                    },
                    .result => |res_info| {
                        try self.emitLeadingTrivia(res_info.name_tok, false);
                        try self.consumeStdlibTypeWrapperTokens(node_idx, res_info.close_bracket_tok);
                        if (needs_parens) try self.doc_arena.emitText("(");
                        try self.formatTypeNodeWithPrec(res_info.ok_type_id, .tier2_prefix, true, true);
                        try self.doc_arena.emitText("!");
                        try self.formatTypeNodeWithPrec(res_info.err_type_id, .tier2_prefix, false, true);
                        if (needs_parens) try self.doc_arena.emitText(")");
                        try self.emitTrailingTrivia(res_info.close_bracket_tok);
                        return;
                    },
                }
            }
        }

        const first_tok = self.findFirstTokenInSubtree(node_idx);
        if (needs_parens and !first_tok.isNone()) {
            try self.emitLeadingTrivia(first_tok, false);
        }
        if (needs_parens) {
            try self.doc_arena.emitText("(");
        }

        if (node.kind == .refined_type) {
            var children: std.ArrayList(CstNodeIndex) = .empty;
            defer children.deinit(self.allocator);
            try self.collectDirectChildren(node_idx, &children);

            for (children.items, 0..) |child_id, idx| {
                const child = self.cst_arena.getNode(child_id);
                if (idx == 0) {
                    try self.formatTypeNodeWithPrec(child_id, .tier1_result, true, false);
                } else if (child.subtree_size == 1 and !child.token.isNone()) {
                    const tok_kind = self.token_buffer.getToken(child.token).kind;
                    if (tok_kind == .kw_where or tok_kind == .kw_is) {
                        try self.doc_arena.emitText(" ");
                        try self.emitTokenWithTrivia(child.token, null, false);
                        try self.doc_arena.emitText(" ");
                    } else {
                        try self.emitTokenWithTrivia(child.token, null, false);
                    }
                } else {
                    try self.formatNode(child_id);
                }
            }
            if (needs_parens) try self.doc_arena.emitText(")");
            return;
        }

        self.in_type_context += 1;
        defer self.in_type_context -= 1;

        if (node.kind == .tuple_type) {
            try self.formatSteerableDelimitedList(node_idx, null, .lparen, .rparen, "(", ")", false);
            if (needs_parens) try self.doc_arena.emitText(")");
            return;
        }

        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        switch (node.kind) {
            .optional_type => {
                for (children.items, 0..) |child_id, idx| {
                    const child = self.cst_arena.getNode(child_id);
                    if (idx == 0 and self.isTypeCstNode(child_id)) {
                        try self.formatTypeNodeWithPrec(child_id, .tier3_postfix, true, false);
                    } else if (child.subtree_size == 1 and !child.token.isNone()) {
                        try self.emitTokenWithTrivia(child.token, null, false);
                    } else {
                        try self.formatNode(child_id);
                    }
                }
                if (needs_parens) try self.doc_arena.emitText(")");
                return;
            },
            .result_type => {
                var has_seen_bang = false;
                for (children.items) |child_id| {
                    const child = self.cst_arena.getNode(child_id);
                    if (child.subtree_size == 1 and !child.token.isNone() and
                        self.token_buffer.getToken(child.token).kind == .bang)
                    {
                        has_seen_bang = true;
                        try self.emitTokenWithTrivia(child.token, "!", false);
                    } else if (self.isTypeCstNode(child_id)) {
                        try self.formatTypeNodeWithPrec(child_id, .tier2_prefix, !has_seen_bang, true);
                    } else {
                        try self.formatNode(child_id);
                    }
                }
                if (needs_parens) try self.doc_arena.emitText(")");
                return;
            },
            .ptr_type => {
                for (children.items) |child_id| {
                    const child = self.cst_arena.getNode(child_id);
                    if (self.isTypeCstNode(child_id)) {
                        try self.formatTypeNodeWithPrec(child_id, .tier4_primary, false, false);
                    } else if (child.subtree_size == 1 and !child.token.isNone()) {
                        const tok_kind = self.token_buffer.getToken(child.token).kind;
                        try self.emitTokenWithTrivia(child.token, null, false);
                        if (tok_kind == .kw_mut or tok_kind == .kw_const) {
                            try self.doc_arena.emitText(" ");
                        }
                    } else {
                        try self.formatNode(child_id);
                    }
                }
                if (needs_parens) try self.doc_arena.emitText(")");
                return;
            },
            .ref_type => {
                const target_prec: TypePrec = if (self.isSliceRefTypeNode(node_idx)) .tier4_primary else .tier2_prefix;
                for (children.items, 0..) |child_id, idx| {
                    const child = self.cst_arena.getNode(child_id);
                    if (self.isTypeCstNode(child_id)) {
                        try self.formatTypeNodeWithPrec(child_id, target_prec, false, false);
                    } else if (child.subtree_size == 1 and !child.token.isNone()) {
                        const tok_kind = self.token_buffer.getToken(child.token).kind;
                        try self.emitTokenWithTrivia(child.token, null, false);
                        if (tok_kind == .kw_mut or tok_kind == .kw_let or
                            (tok_kind == .ident and idx + 1 < children.items.len))
                        {
                            try self.doc_arena.emitText(" ");
                        }
                    } else {
                        try self.formatNode(child_id);
                    }
                }
                if (needs_parens) try self.doc_arena.emitText(")");
                return;
            },
            .mode_type => {
                const target_prec: TypePrec = switch (own_prec) {
                    .tier0_open => .tier0_open,
                    .tier2_prefix => .tier2_prefix,
                    else => .tier4_primary,
                };
                for (children.items, 0..) |child_id, idx| {
                    const child = self.cst_arena.getNode(child_id);
                    if (self.isTypeCstNode(child_id)) {
                        try self.formatTypeNodeWithPrec(child_id, target_prec, false, false);
                    } else if (child.subtree_size == 1 and !child.token.isNone()) {
                        const tok_kind = self.token_buffer.getToken(child.token).kind;
                        try self.emitTokenWithTrivia(child.token, null, false);
                        if ((tok_kind == .kw_own or tok_kind == .hash_soa or tok_kind == .ident) and
                            idx + 1 < children.items.len)
                        {
                            try self.doc_arena.emitText(" ");
                        }
                    } else {
                        try self.formatNode(child_id);
                    }
                }
                if (needs_parens) try self.doc_arena.emitText(")");
                return;
            },
            .intersect_bound_type, .union_bound_type => {
                for (children.items) |child_id| {
                    const child = self.cst_arena.getNode(child_id);
                    if (child.subtree_size == 1 and !child.token.isNone()) {
                        const tok_kind = self.token_buffer.getToken(child.token).kind;
                        if (tok_kind == .plus or tok_kind == .pipe) {
                            try self.doc_arena.emitText(" ");
                            try self.emitTokenWithTrivia(child.token, null, false);
                            try self.doc_arena.emitText(" ");
                        } else {
                            try self.emitTokenWithTrivia(child.token, null, false);
                        }
                    } else {
                        try self.formatNode(child_id);
                    }
                }
                if (needs_parens) try self.doc_arena.emitText(")");
                return;
            },
            else => {},
        }

        const start_idx = if (node.kind == .fn_type or node.kind == .closure_type)
            try self.formatLeadingInlineAttributes(children.items)
        else
            0;

        var idx: usize = start_idx;
        while (idx < children.items.len) : (idx += 1) {
            const child_id = children.items[idx];
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_mut or tok_kind == .kw_own or
                    tok_kind == .kw_const or tok_kind == .kw_let or
                    (tok_kind == .kw_async and node.kind != .named_type) or
                    tok_kind == .kw_unsafe or tok_kind == .kw_extern or
                    tok_kind == .hash_soa)
                {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .string_lit and node.kind == .fn_type) {
                    const abi_lex = self.getTokenLexeme(child.token);
                    const abi_override: ?[]const u8 = if (std.ascii.eqlIgnoreCase(abi_lex, "\"c\""))
                        "\"C\""
                    else
                        null;
                    try self.emitTokenWithTrivia(child.token, abi_override, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .comma) {
                    const is_after_variadic = idx > 0 and
                        self.cst_arena.getNode(children.items[idx - 1]).kind == .variadic_param;
                    if (is_after_variadic) {
                        try self.emitLeadingTrivia(child.token, false);
                        self.token_meta[child.token.asInt()].is_token_emitted = true;
                        try self.emitTrailingTrivia(child.token);
                    } else {
                        try self.emitTokenWithTrivia(child.token, ",", false);
                        if (idx + 1 < children.items.len) {
                            const next_c = self.cst_arena.getNode(children.items[idx + 1]);
                            const is_close = next_c.subtree_size == 1 and !next_c.token.isNone() and
                                (self.token_buffer.getToken(next_c.token).kind == .rparen or
                                    self.token_buffer.getToken(next_c.token).kind == .pipe);
                            if (!is_close) try self.doc_arena.emitText(" ");
                        }
                    }
                } else if (tok_kind == .arrow) {
                    if ((node.kind == .fn_type or node.kind == .closure_type) and
                        idx + 1 < children.items.len and
                        self.isStrippableUnitReturnPair(child.token, children.items[idx + 1]))
                    {
                        try self.consumeStrippedUnitReturnPair(child.token, children.items[idx + 1]);
                        idx += 1;
                        continue;
                    }
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "->", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .bang and idx > 0) {
                    try self.emitTokenWithTrivia(child.token, "!", false);
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        if (needs_parens) {
            try self.doc_arena.emitText(")");
        }
    }

    /// Formats a braced pattern (`.struct_pat` or `{ … }`-bodied `.variant_pat`), suppressing `,` after `..`.
    fn formatBracedPatternNode(
        self: *CstFormatter,
        children: []const CstNodeIndex,
        op_idx: usize,
        cl_idx: usize,
    ) anyerror!void {
        {
            self.in_type_context += 1;
            defer self.in_type_context -= 1;
            for (children[0..op_idx]) |prefix_id| {
                try self.formatNode(prefix_id);
            }
        }
        try self.doc_arena.emitText(" ");

        const open_tok = self.cst_arena.getNode(children[op_idx]).token;
        const close_tok = self.cst_arena.getNode(children[cl_idx]).token;

        const PatFieldWithSep = struct {
            field_id: CstNodeIndex,
            comma_tok: TokenIndex = .none,
            is_rest: bool = false,
        };
        var fields: std.ArrayList(PatFieldWithSep) = .empty;
        defer fields.deinit(self.allocator);
        var has_trailing_comma = false;

        for (children[op_idx + 1 .. cl_idx]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                if (self.token_buffer.getToken(child.token).kind == .comma) {
                    has_trailing_comma = true;
                    if (fields.items.len > 0) {
                        fields.items[fields.items.len - 1].comma_tok = child.token;
                    }
                    continue;
                }
            }
            has_trailing_comma = false;
            const is_rest = self.hasDirectTokenKind(child_id, .dotdot) or
                (child.subtree_size == 1 and !child.token.isNone() and
                    self.token_buffer.getToken(child.token).kind == .dotdot);
            try fields.append(self.allocator, .{
                .field_id = child_id,
                .is_rest = is_rest,
            });
        }

        if (fields.items.len == 0) {
            try self.formatEmptyContainer(open_tok, close_tok, "{", "}");
            return;
        }

        try self.emitTokenLeadingAndGlyph(open_tok, "{", false);
        const group_mode: GroupMode = if (has_trailing_comma) .force_break else .auto_fit;
        _ = try self.doc_arena.beginGroup(group_mode);
        try self.emitTrailingTrivia(open_tok);
        try self.doc_arena.emitLine();
        try self.doc_arena.beginIndent(INDENT_SPACES);

        for (fields.items, 0..) |entry, field_i| {
            try self.formatNode(entry.field_id);
            if (!entry.comma_tok.isNone()) {
                try self.emitLeadingTrivia(entry.comma_tok, false);
                self.token_meta[entry.comma_tok.asInt()].is_token_emitted = true;
            }
            if (field_i + 1 < fields.items.len) {
                try self.doc_arena.emitText(",");
                if (!entry.comma_tok.isNone()) {
                    try self.emitTrailingTrivia(entry.comma_tok);
                }
                try self.doc_arena.emitLine();
            } else {
                if (!entry.is_rest) {
                    try self.doc_arena.emitIfBreak(",", "");
                }
                if (!entry.comma_tok.isNone()) {
                    try self.emitTrailingTrivia(entry.comma_tok);
                }
            }
        }

        if (self.hasUnconsumedLeadingComments(close_tok)) {
            try self.doc_arena.emitHardLine();
            try self.emitLeadingTrivia(close_tok, true);
        }
        try self.doc_arena.endIndent(INDENT_SPACES);
        try self.doc_arena.emitLine();
        try self.doc_arena.endGroup();
        try self.emitTokenWithTrivia(close_tok, "}", false);
    }

    /// Formats a pattern CST node (`.tuple_pat`, `.slice_pat`, `.struct_pat`, `.at_pat`, `.or_pat`, `.ident_pat`).
    fn formatPatternNode(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        const node = self.cst_arena.getNode(node_idx);
        switch (node.kind) {
            .tuple_pat => {
                try self.formatSteerableDelimitedList(node_idx, null, .lparen, .rparen, "(", ")", false);
                return;
            },
            .slice_pat => {
                try self.formatSteerableDelimitedList(node_idx, null, .lbracket, .rbracket, "[", "]", false);
                return;
            },
            .struct_pat, .variant_pat => {
                var children: std.ArrayList(CstNodeIndex) = .empty;
                defer children.deinit(self.allocator);
                try self.collectDirectChildren(node_idx, &children);

                var lbrace_pos: ?usize = null;
                var rbrace_pos: ?usize = null;
                var lparen_pos: ?usize = null;
                var rparen_pos: ?usize = null;
                for (children.items, 0..) |child_id, idx| {
                    const child = self.cst_arena.getNode(child_id);
                    if (child.subtree_size == 1 and !child.token.isNone()) {
                        const tok_kind = self.token_buffer.getToken(child.token).kind;
                        if ((child.kind == .struct_pat_start or tok_kind == .lbrace) and lbrace_pos == null) {
                            lbrace_pos = idx;
                        } else if (tok_kind == .rbrace) {
                            rbrace_pos = idx;
                        } else if (tok_kind == .lparen and lparen_pos == null) {
                            lparen_pos = idx;
                        } else if (tok_kind == .rparen) {
                            rparen_pos = idx;
                        }
                    }
                }
                if (lbrace_pos != null and rbrace_pos != null and rbrace_pos.? > lbrace_pos.?) {
                    try self.formatBracedPatternNode(children.items, lbrace_pos.?, rbrace_pos.?);
                    return;
                }
                if (lparen_pos != null and rparen_pos != null and rparen_pos.? > lparen_pos.?) {
                    try self.formatSteerableDelimitedList(node_idx, null, .lparen, .rparen, "(", ")", false);
                    return;
                }
            },
            else => {},
        }

        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_var or tok_kind == .kw_mut or tok_kind == .kw_own) {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .at and node.kind == .at_pat) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "@", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .pipe) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "|", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .comma) {
                    try self.emitTokenWithTrivia(child.token, ",", false);
                    if (idx + 1 < children.items.len) {
                        const next_c = self.cst_arena.getNode(children.items[idx + 1]);
                        const is_close = next_c.subtree_size == 1 and !next_c.token.isNone() and
                            (self.token_buffer.getToken(next_c.token).kind == .rparen or
                                self.token_buffer.getToken(next_c.token).kind == .rbrace);
                        if (!is_close) try self.doc_arena.emitText(" ");
                    }
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Fallback helper formatting all direct children of `node_idx` sequentially.
    fn formatGenericChildren(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            try self.formatNode(child_id);
        }
    }

    /// Dispatches CST node `node_idx` to its canonical `DR-03` / `DR-14` / `DR-21` / `DR-22` formatting routine.
    fn formatNode(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        const node = self.cst_arena.getNode(node_idx);
        if (node.subtree_size == 1) {
            if (!self.shouldSkipLeaf(node)) {
                try self.emitTokenWithTrivia(node.token, null, false);
            }
            return;
        }

        switch (node.kind) {
            .file_end => try self.formatRoot(),
            .attribute => try self.formatAttribute(node_idx),
            .visibility_modifier => try self.formatVisibilityModifier(node_idx),
            .use_item => try self.formatUseItem(node_idx),
            .use_tree => try self.formatUseTree(node_idx),
            .const_item => try self.formatConstItem(node_idx),
            .type_alias_item => try self.formatTypeAliasItem(node_idx),
            .mod_item => try self.formatModItem(node_idx),
            .struct_item, .union_item, .enum_item => try self.formatStructOrUnionOrEnum(node_idx),
            .struct_field => try self.formatStructField(node_idx),
            .enum_variant => try self.formatEnumVariant(node_idx),
            .trait_item, .impl_item => try self.formatTraitOrImpl(node_idx),
            .extern_block_item => try self.formatExternBlockItem(node_idx),
            .extern_static_item => try self.formatExternStaticItem(node_idx),
            .fn_item, .trait_member, .impl_member => try self.formatFnOrMember(node_idx),
            .subscript_item => try self.formatSubscriptItem(node_idx),
            .subscript_arm => try self.formatSubscriptArm(node_idx),
            .test_item, .bench_item => try self.formatTestOrBenchItem(node_idx),
            .fn_sig => try self.formatFnSig(node_idx),
            .fn_expr_body => try self.formatFnExprBody(node_idx),
            .return_type => try self.formatReturnType(node_idx),
            .param_list => try self.formatParamList(node_idx),
            .fn_param => try self.formatFnParam(node_idx),
            .type_params => try self.formatTypeParams(node_idx),
            .type_param => try self.formatTypeParam(node_idx),
            .where_clause => try self.formatWhereClause(node_idx),
            .where_pred => try self.formatWherePred(node_idx),
            .type_args => try self.formatTypeArgs(node_idx),
            .block => try self.formatBlock(node_idx),
            .local_decl_stmt => try self.formatLocalDeclStmt(node_idx),
            .let_else_branch => try self.formatLetElseBranch(node_idx),
            .return_stmt, .break_stmt, .continue_stmt, .yield_stmt => try self.formatJumpStmt(node_idx),
            .diverging_expr => try self.formatDivergingExpr(node_idx),
            .loop_label => try self.formatLoopLabel(node_idx),
            .defer_stmt => try self.formatDeferStmt(node_idx),
            .assign_stmt => try self.formatAssignStmt(node_idx),
            .expr_stmt => try self.formatExprStmt(node_idx),
            .empty_stmt => try self.flushNodeComments(node_idx),
            .if_expr => try self.formatIfExpr(node_idx),
            .if_cond, .while_header => try self.formatConditionHeader(node_idx),
            .else_branch => try self.formatElseBranch(node_idx),
            .for_stmt => try self.formatForStmt(node_idx),
            .for_header => try self.formatForHeader(node_idx),
            .while_stmt => try self.formatWhileStmt(node_idx),
            .loop_expr => try self.formatLoopExpr(node_idx),
            .walrus_cond_expr => try self.formatWalrusCondExpr(node_idx),
            .with_expr => try self.formatWithExpr(node_idx),
            .context_binding => try self.formatContextBinding(node_idx),
            .contextual_variant_expr => try self.formatContextualVariantExpr(node_idx),
            .match_expr => try self.formatMatchExpr(node_idx),
            .match_arm => try self.formatMatchArm(node_idx),
            .call_expr => try self.formatCallExpr(node_idx),
            .call_arg => try self.formatCallArg(node_idx),
            .struct_lit_expr => try self.formatStructLitExpr(node_idx),
            .field_init => try self.formatFieldInit(node_idx),
            .view_block_expr => try self.formatViewBlockExpr(node_idx),
            .array_expr => try self.formatArrayExpr(node_idx),
            .tuple_or_paren_expr => try self.formatTupleOrParenExpr(node_idx),
            .closure_expr => try self.formatClosureExpr(node_idx),
            .closure_param => try self.formatClosureParam(node_idx),
            .infix_expr => try self.formatInfixExpr(node_idx),
            .prefix_expr => try self.formatPrefixExpr(node_idx),
            .field_or_method_expr, .postfix_deref_expr, .postfix_try_expr, .postfix_await_expr => {
                try self.formatPostfixChain(node_idx);
            },
            .index_expr => try self.formatIndexExpr(node_idx),
            .cast_expr => try self.formatCastExpr(node_idx),
            .prim_type_node,
            .named_type,
            .ref_type,
            .ptr_type,
            .mode_type,
            .slice_or_array_type,
            .tuple_type,
            .fn_type,
            .closure_type,
            .optional_type,
            .result_type,
            .refined_type,
            .intersect_bound_type,
            .union_bound_type,
            => try self.formatTypeNode(node_idx),
            .wildcard_pat,
            .literal_pat,
            .range_pat,
            .tuple_pat,
            .slice_pat,
            .ident_pat,
            .at_pat,
            .variant_pat,
            .path_pat,
            .struct_pat,
            .field_pat,
            .or_pat,
            => try self.formatPatternNode(node_idx),
            else => try self.formatGenericChildren(node_idx),
        }
    }
};

// ---------------- Script Frontmatter Splicing -----------------

/// Byte-range metadata for an optional top-of-file `#!` + `--- … ---` script TOML frontmatter block.
const ScriptFrontmatterPrefix = struct {
    /// Byte offset immediately following the closing `---` fence line (including its line ending).
    fence_end: usize,
    /// `true` when at least one blank line separates the closing `---` fence from a non-empty `.cx` body.
    has_blank_separator: bool,
};

/// Returns `true` when `line_no_nl` is a TOML frontmatter `---` delimiter followed only by `' '` or `'\t'`.
fn isFrontmatterFenceLine(line_no_nl: []const u8) bool {
    if (line_no_nl.len < 3 or !std.mem.startsWith(u8, line_no_nl, "---")) return false;
    for (line_no_nl[3..]) |byte_val| {
        if (byte_val != ' ' and byte_val != '\t') return false;
    }
    return true;
}

/// Returns `true` when `rest_slice` begins with an empty/whitespace-only line terminated by `\n`.
fn hasLeadingBlankLineInSlice(rest_slice: []const u8) bool {
    var idx: usize = 0;
    while (idx < rest_slice.len) : (idx += 1) {
        const byte_val = rest_slice[idx];
        if (byte_val == '\n') return true;
        if (byte_val == '\r') {
            return idx + 1 < rest_slice.len and rest_slice[idx + 1] == '\n';
        }
        if (byte_val != ' ' and byte_val != '\t') return false;
    }
    return false;
}

/// Scans `source` for a top-of-file `[BOM][#!…\n]---\n…\n---[\n]` script TOML frontmatter prefix.
fn extractScriptFrontmatterPrefix(source: []const u8) ?ScriptFrontmatterPrefix {
    var cursor: usize = if (std.mem.startsWith(u8, source, "\xEF\xBB\xBF")) 3 else 0;
    if (cursor < source.len and std.mem.startsWith(u8, source[cursor..], "#!")) {
        const shebang_nl = std.mem.indexOfScalar(u8, source[cursor..], '\n') orelse return null;
        cursor += shebang_nl + 1;
    }
    if (cursor >= source.len) return null;
    const open_nl = std.mem.indexOfScalar(u8, source[cursor..], '\n') orelse return null;
    const open_raw = source[cursor .. cursor + open_nl];
    const open_line = if (open_raw.len > 0 and open_raw[open_raw.len - 1] == '\r')
        open_raw[0 .. open_raw.len - 1]
    else
        open_raw;
    if (!isFrontmatterFenceLine(open_line)) return null;
    cursor += open_nl + 1;

    while (cursor < source.len) {
        if (std.mem.indexOfScalar(u8, source[cursor..], '\n')) |line_nl| {
            const line_raw = source[cursor .. cursor + line_nl];
            const line_clean = if (line_raw.len > 0 and line_raw[line_raw.len - 1] == '\r')
                line_raw[0 .. line_raw.len - 1]
            else
                line_raw;
            const next_cursor = cursor + line_nl + 1;
            if (isFrontmatterFenceLine(line_clean)) {
                return .{
                    .fence_end = next_cursor,
                    .has_blank_separator = hasLeadingBlankLineInSlice(source[next_cursor..]),
                };
            }
            cursor = next_cursor;
        } else {
            const tail_raw = source[cursor..];
            const tail_clean = if (tail_raw.len > 0 and tail_raw[tail_raw.len - 1] == '\r')
                tail_raw[0 .. tail_raw.len - 1]
            else
                tail_raw;
            if (isFrontmatterFenceLine(tail_clean)) {
                return .{
                    .fence_end = source.len,
                    .has_blank_separator = false,
                };
            }
            break;
        }
    }
    return null;
}

/// Allocates a copy of `source` with non-newline bytes in `[0 .. fence_end)` blanked to `' '` (`0x20`).
fn allocateMaskedFrontmatterSource(
    allocator: std.mem.Allocator,
    source: []const u8,
    fence_end: usize,
) ![]u8 {
    const masked = try allocator.dupe(u8, source);
    var i: usize = 0;
    while (i < fence_end) : (i += 1) {
        if (masked[i] != '\n' and masked[i] != '\r') {
            masked[i] = ' ';
        }
    }
    return masked;
}

/// Splices the script frontmatter `prefix` (normalizing `\r\n` to `\n`) onto the formatted `.cx` `body_text`.
fn spliceFrontmatterAndBody(
    allocator: std.mem.Allocator,
    source: []const u8,
    prefix: ScriptFrontmatterPrefix,
    body_text: []const u8,
) ![]u8 {
    const raw_header = source[0..prefix.fence_end];
    var cr_skip_count: usize = 0;
    for (raw_header, 0..) |byte_val, i| {
        if (byte_val == '\r' and (i + 1 == raw_header.len or raw_header[i + 1] == '\n')) {
            cr_skip_count += 1;
        }
    }
    const norm_header_len = raw_header.len - cr_skip_count;
    const has_header_nl = raw_header.len > 0 and raw_header[raw_header.len - 1] == '\n';
    const extra_header_nl: usize = if (!has_header_nl) 1 else 0;
    const extra_sep_nl: usize = if (body_text.len > 0 and prefix.has_blank_separator) 1 else 0;

    const total_len = norm_header_len + extra_header_nl + extra_sep_nl + body_text.len;
    const out_buf = try allocator.alloc(u8, total_len);
    var write_off: usize = 0;
    if (cr_skip_count == 0) {
        @memcpy(out_buf[0..raw_header.len], raw_header);
        write_off = raw_header.len;
    } else {
        for (raw_header, 0..) |byte_val, i| {
            if (byte_val == '\r' and (i + 1 == raw_header.len or raw_header[i + 1] == '\n')) continue;
            out_buf[write_off] = byte_val;
            write_off += 1;
        }
    }
    if (extra_header_nl == 1) {
        out_buf[write_off] = '\n';
        write_off += 1;
    }
    if (extra_sep_nl == 1) {
        out_buf[write_off] = '\n';
        write_off += 1;
    }
    if (body_text.len > 0) {
        @memcpy(out_buf[write_off .. write_off + body_text.len], body_text);
    }
    return out_buf;
}

/// Formats an already-masked `masked_source` with its corresponding `token_buffer` and `cst_arena`, then splices `prefix`.
fn formatMaskedTokensAndCstWithPrefix(
    allocator: std.mem.Allocator,
    original_source: []const u8,
    masked_source: []const u8,
    prefix: ScriptFrontmatterPrefix,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    options: FormatOptions,
) !FormatResult {
    const is_fix_mode = options.is_fix_mode;
    if (hasBlockingSyntaxErrors(token_buffer, cst_arena, is_fix_mode)) {
        return .{
            .formatted_text = try allocator.dupe(u8, original_source),
            .is_changed = false,
            .has_syntax_errors = true,
        };
    }

    var doc_arena = DocArena.init(allocator);
    defer doc_arena.deinit();

    var cst_formatter = try CstFormatter.init(
        allocator,
        masked_source,
        token_buffer,
        cst_arena,
        &doc_arena,
        is_fix_mode,
    );
    defer cst_formatter.deinit();

    try cst_formatter.formatRoot();

    var renderer = DocRenderer.init(allocator, options.max_line_width);
    defer renderer.deinit();

    const formatted_body = try renderer.render(&doc_arena);
    defer allocator.free(formatted_body);

    const spliced = try spliceFrontmatterAndBody(allocator, original_source, prefix, formatted_body);
    return .{
        .formatted_text = spliced,
        .is_changed = !std.mem.eql(u8, original_source, spliced),
        .has_syntax_errors = false,
    };
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Converts `ident` to `PascalCase` (`DR-03` Section 3.3 & `DR-14` Section 1.5).
pub const toPascalCase = lexer.toPascalCase;
/// Converts `ident` to `snake_case` (`DR-03` Section 3.3 & `DR-14` Section 1.5).
pub const toSnakeCase = lexer.toSnakeCase;
/// Converts `ident` to `SCREAMING_SNAKE_CASE` (`DR-03` Section 3.3 & `DR-14` Section 1.5).
pub const toScreamingSnakeCase = lexer.toScreamingSnakeCase;

/// Formats an already-tokenized `token_buffer` and `cst_arena` using `options`.
pub fn formatTokensAndCst(
    allocator: std.mem.Allocator,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    options: FormatOptions,
) !FormatResult {
    if (extractScriptFrontmatterPrefix(source)) |prefix| {
        const has_unmasked_frontmatter_tokens = token_buffer.countTokens() > 0 and
            token_buffer.getToken(TokenIndex.fromInt(0)).byte_offset < prefix.fence_end;
        if (has_unmasked_frontmatter_tokens) {
            return formatSourceWithOptions(allocator, source, FileId.fromInt(0), options);
        }
        const masked_source = try allocateMaskedFrontmatterSource(allocator, source, prefix.fence_end);
        defer allocator.free(masked_source);
        return formatMaskedTokensAndCstWithPrefix(
            allocator,
            source,
            masked_source,
            prefix,
            token_buffer,
            cst_arena,
            options,
        );
    }

    const is_fix_mode = options.is_fix_mode;
    const has_errors = hasBlockingSyntaxErrors(token_buffer, cst_arena, is_fix_mode);
    if (has_errors) {
        const verbatim_copy = try allocator.dupe(u8, source);
        return .{
            .formatted_text = verbatim_copy,
            .is_changed = false,
            .has_syntax_errors = true,
        };
    }

    var doc_arena = DocArena.init(allocator);
    defer doc_arena.deinit();

    var cst_formatter = try CstFormatter.init(
        allocator,
        source,
        token_buffer,
        cst_arena,
        &doc_arena,
        is_fix_mode,
    );
    defer cst_formatter.deinit();

    try cst_formatter.formatRoot();

    var renderer = DocRenderer.init(allocator, options.max_line_width);
    defer renderer.deinit();

    const formatted = try renderer.render(&doc_arena);
    const is_changed = !std.mem.eql(u8, source, formatted);
    return .{
        .formatted_text = formatted,
        .is_changed = is_changed,
        .has_syntax_errors = false,
    };
}

/// Tokenizes, parses, and formats `source` according to `options` (`DR-14` Section 1).
pub fn formatSourceWithOptions(
    allocator: std.mem.Allocator,
    source: []const u8,
    file_id: FileId,
    options: FormatOptions,
) !FormatResult {
    var token_buffer = TokenBuffer.init(allocator);
    defer token_buffer.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    defer ast_arena.deinit();

    if (extractScriptFrontmatterPrefix(source)) |prefix| {
        const masked_source = try allocateMaskedFrontmatterSource(allocator, source, prefix.fence_end);
        defer allocator.free(masked_source);
        _ = try parser.parseSource(
            masked_source,
            file_id,
            &token_buffer,
            &cst_arena,
            &ast_arena,
            null,
            null,
        );
        return formatMaskedTokensAndCstWithPrefix(
            allocator,
            source,
            masked_source,
            prefix,
            &token_buffer,
            &cst_arena,
            options,
        );
    }

    _ = try parser.parseSource(
        source,
        file_id,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        null,
        null,
    );
    return formatTokensAndCst(allocator, source, &token_buffer, &cst_arena, options);
}

/// Tokenizes, parses, and formats `source` using canonical default `FormatOptions`.
pub fn formatSource(
    allocator: std.mem.Allocator,
    source: []const u8,
    file_id: FileId,
) !FormatResult {
    return formatSourceWithOptions(allocator, source, file_id, .{});
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_doc_inst_is_exact_8_bytes_and_arena_backpatches_flat_width" {
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(DocInst));

    var arena = DocArena.init(std.testing.allocator);
    defer arena.deinit();

    const grp_idx = try arena.beginGroup(.auto_fit);
    try arena.emitText("fn foo(");
    try arena.emitSoftLine();
    try arena.emitText("x: i32");
    try arena.emitIfBreak(",", "");
    try arena.emitSoftLine();
    try arena.emitText(")");
    try arena.endGroup();

    // "fn foo(" (7) + "x: i32" (6) + ")" (1) = 14 columns in flat mode:
    try std.testing.expectEqual(@as(u16, 14), arena.instructions.items[grp_idx].flat_width);

    // Poisoned group with `.hard_line` must backpatch `INF_WIDTH` (`0xFFFF`):
    const broken_idx = try arena.beginGroup(.auto_fit);
    try arena.emitText("a");
    try arena.emitHardLine();
    try arena.emitText("b");
    try arena.endGroup();
    try std.testing.expectEqual(INF_WIDTH, arena.instructions.items[broken_idx].flat_width);
}

test "test_doc_renderer_flushes_line_suffix_comments_and_clamps_blank_lines" {
    var arena = DocArena.init(std.testing.allocator);
    defer arena.deinit();

    try arena.emitText("let a = 1;");
    try arena.emitLineSuffix("// first comment");
    try arena.emitBlankLine();
    try arena.emitBlankLine();
    try arena.emitText("let b = 2;");

    var renderer = DocRenderer.init(std.testing.allocator, MAX_LINE_WIDTH);
    defer renderer.deinit();
    const out = try renderer.render(&arena);
    defer std.testing.allocator.free(out);

    try std.testing.expectEqualStrings(
        "let a = 1; // first comment\n\nlet b = 2;\n",
        out,
    );
}

test "test_format_use_tree_sorting_and_trailing_comma_steerability" {
    const src_flat =
        "use cx.col.{HashMap, BTreeMap, self, Vec};\n" ++
        "use cx.mem;\n";
    var res_flat = try formatSource(std.testing.allocator, src_flat, FileId.fromInt(0));
    defer res_flat.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(
        "use cx.col.{self, BTreeMap, HashMap, Vec};\n" ++
            "use cx.mem;\n",
        res_flat.formatted_text,
    );

    // Trailing comma inside `use` braces forces multiline break:
    const src_broken = "use cx.col.{Vec, BTreeMap,};\n";
    var res_broken = try formatSource(std.testing.allocator, src_broken, FileId.fromInt(0));
    defer res_broken.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(
        "use cx.col.{\n" ++
            "    BTreeMap,\n" ++
            "    Vec,\n" ++
            "};\n",
        res_broken.formatted_text,
    );
}

test "test_format_columnar_grid_array_with_more_than_8_elements" {
    const src =
        "fn main() {\n" ++
        "    let table = [\n" ++
        "        1, 20, 300, 4, 50, 600, 7, 80, 900, 10,\n" ++
        "    ];\n" ++
        "}\n";
    var res = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer res.deinit(std.testing.allocator);

    const expected =
        "fn main() {\n" ++
        "    let table = [\n" ++
        "          1,  20, 300,   4,  50, 600,   7,  80,\n" ++
        "        900,  10,\n" ++
        "    ];\n" ++
        "}\n";
    try std.testing.expectEqualStrings(expected, res.formatted_text);
}

test "test_format_pipe_and_method_chains" {
    const src =
        "fn process() {\n" ++
        "    let res = input\n" ++
        "        |> parse()\n" ++
        "        |> validate();\n" ++
        "    let items = data\n" ++
        "        .iter()\n" ++
        "        .collect()?;\n" ++
        "}\n";
    var res = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer res.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(src, res.formatted_text);
}

test "test_format_strips_redundant_outer_parens_and_redundant_semicolons" {
    const src =
        "fn check(val: i32) {\n" ++
        "    ;\n" ++
        "    if (val > 0) {\n" ++
        "        while (val > 10) {\n" ++
        "            break;\n" ++
        "        };\n" ++
        "    };\n" ++
        "    for item in (0..10) {\n" ++
        "        match (item) {\n" ++
        "            0 => {},\n" ++
        "            _ => {},\n" ++
        "        };\n" ++
        "    };\n" ++
        "}\n";
    var res = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer res.deinit(std.testing.allocator);

    const expected =
        "fn check(val: i32) {\n" ++
        "    if val > 0 {\n" ++
        "        while val > 10 {\n" ++
        "            break;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    for item in 0..10 {\n" ++
        "        match item {\n" ++
        "            0 => {},\n" ++
        "            _ => {},\n" ++
        "        }\n" ++
        "    }\n" ++
        "}\n";
    try std.testing.expectEqualStrings(expected, res.formatted_text);
}

test "test_format_preserves_100_percent_comments_and_is_idempotent" {
    const src =
        "// Module header comment\n" ++
        "struct Point {\n" ++
        "    x: i32, // trailing on x\n" ++
        "    // leading on y\n" ++
        "    y: i32\n" ++
        "}\n" ++
        "fn empty_fn() {\n" ++
        "    // dangling comment in empty block\n" ++
        "}\n" ++
        "// trailing EOF comment\n";

    var pass1 = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);

    const expected =
        "// Module header comment\n" ++
        "struct Point {\n" ++
        "    x: i32, // trailing on x\n" ++
        "    // leading on y\n" ++
        "    y: i32,\n" ++
        "}\n\n" ++
        "fn empty_fn() {\n" ++
        "    // dangling comment in empty block\n" ++
        "}\n" ++
        "// trailing EOF comment\n";
    try std.testing.expectEqualStrings(expected, pass1.formatted_text);

    // Verify `fmt(fmt(source)) == fmt(source)` idempotency:
    var pass2 = try formatSource(std.testing.allocator, pass1.formatted_text, FileId.fromInt(0));
    defer pass2.deinit(std.testing.allocator);
    try std.testing.expectEqualStrings(pass1.formatted_text, pass2.formatted_text);
    try std.testing.expect(!pass2.is_changed);
}

test "test_format_honors_corex_fmt_off_and_on_directives" {
    const src =
        "const A: i32 = 1;\n\n" ++
        "// corex fmt: off\n" ++
        "const   RAW_MATRIX:   i32  =   42;\n" ++
        "// corex fmt: on\n\n" ++
        "const B: i32 = 2;\n";

    var res = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer res.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(src, res.formatted_text);
}

test "test_format_fix_mode_normalizes_casing_and_inserts_missing_semicolons" {
    const src =
        "const max_limit: i32 = 100\n" ++
        "struct my_point {\n" ++
        "     XVal: i32,\n" ++
        "}\n" ++
        "fn ComputeSum(InputVal: i32) -> i32 {\n" ++
        "    let LocalTotal = InputVal + max_limit\n" ++
        "    return LocalTotal\n" ++
        "}\n";

    var res = try formatSourceWithOptions(
        std.testing.allocator,
        src,
        FileId.fromInt(0),
        .{ .is_fix_mode = true },
    );
    defer res.deinit(std.testing.allocator);

    const expected =
        "const MAX_LIMIT: i32 = 100;\n\n" ++
        "struct MyPoint {\n" ++
        "    x_val: i32,\n" ++
        "}\n\n" ++
        "fn compute_sum(input_val: i32) -> i32 {\n" ++
        "    let local_total = input_val + MAX_LIMIT;\n" ++
        "    return local_total;\n" ++
        "}\n";
    try std.testing.expectEqualStrings(expected, res.formatted_text);
    try std.testing.expect(res.is_changed);
}

test "test_format_broken_syntax_falls_back_safely" {
    const broken_src = "fn broken( { let x = ; }\n";
    var res = try formatSource(std.testing.allocator, broken_src, FileId.fromInt(0));
    defer res.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(broken_src, res.formatted_text);
    try std.testing.expect(!res.is_changed);
    try std.testing.expect(res.has_syntax_errors);
}

test "test_format_red_team_syntax_constructs_and_patterns" {
    const src =
        "unsafe impl Send for Foo {}\n\n" ++
        "type Callback = unsafe fn(lhs: i32, rhs: i32) -> i32;\n" ++
        "type AsyncTask = async fn(input_val: i32) -> i32;\n\n" ++
        "impl Grid {\n" ++
        "    subscript(idx: usize) -> &i32 {\n" ++
        "        let {\n" ++
        "            yield &self.cells[idx];\n" ++
        "        }\n\n" ++
        "        inout {\n" ++
        "            yield &mut self.cells[idx];\n" ++
        "        }\n" ++
        "    }\n" ++
        "}\n\n" ++
        "fn evaluate(point_val: Point, opt_val: Option) -> i32 {\n" ++
        "    let neg_one = -point_val.x;\n" ++
        "    let double_neg = - -neg_one;\n" ++
        "    match point_val {\n" ++
        "        Point { x, y, .. } => x + y,\n" ++
        "    }\n" ++
        "    match opt_val {\n" ++
        "        Option.Some(inner_val) => inner_val,\n" ++
        "        Option.Pair { first_val, second_val } => first_val + second_val,\n" ++
        "        _ => double_neg,\n" ++
        "    }\n" ++
        "}\n";

    var res = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer res.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(src, res.formatted_text);
    try std.testing.expect(!res.is_changed);
}

test "test_format_red_team_comments_and_idempotency" {
    const src =
        "use cx.io.{\n" ++
        "    Read, // comment on Read\n" ++
        "    Write,\n" ++
        "    // comment before close brace\n" ++
        "};\n\n" ++
        "fn comment_edges(cond: bool) -> i32 {\n" ++
        "    ; // comment on empty stmt\n" ++
        "    let assigned =\n" ++
        "        // comment after eq\n" ++
        "        42;\n" ++
        "    if (/* keep parens */ cond) {\n" ++
        "        defer {\n" ++
        "            let clean = 1;\n" ++
        "        }\n" ++
        "        // comment before stripped defer semi\n" ++
        "        ;\n" ++
        "    }\n" ++
        "    // comment before stripped if semi\n" ++
        "    ;\n" ++
        "    return assigned;\n" ++
        "}\n";

    var pass1 = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);

    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "Read, // comment on Read") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "// comment before close brace") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "// comment on empty stmt") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "// comment after eq\n    42;") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "if (/* keep parens */ cond)") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "// comment before stripped defer semi") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "// comment before stripped if semi") != null);

    var pass2 = try formatSource(std.testing.allocator, pass1.formatted_text, FileId.fromInt(0));
    defer pass2.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(pass1.formatted_text, pass2.formatted_text);
    try std.testing.expect(!pass2.is_changed);
}

test "test_format_red_team_role_aware_fix_renaming" {
    const src =
        "struct foo {\n" ++
        "    inner_val: i32,\n" ++
        "}\n\n" ++
        "fn process_item(foo: foo) -> i32 {\n" ++
        "    return foo.inner_val;\n" ++
        "}\n";

    var res = try formatSourceWithOptions(
        std.testing.allocator,
        src,
        FileId.fromInt(0),
        .{ .is_fix_mode = true },
    );
    defer res.deinit(std.testing.allocator);

    const expected =
        "struct Foo {\n" ++
        "    inner_val: i32,\n" ++
        "}\n\n" ++
        "fn process_item(foo: Foo) -> i32 {\n" ++
        "    return foo.inner_val;\n" ++
        "}\n";
    try std.testing.expectEqualStrings(expected, res.formatted_text);
}

test "test_format_phase5_comptime_intrinsics_and_is_pattern_idempotence" {
    const src =
        "fn inspect[T](comptime label: str, status: Status) -> usize {\n" ++
        "    @compile_assert(@size_of[T]() > 0, label);\n" ++
        "    comptime {\n" ++
        "        @compile_assert(true, \"ok\");\n" ++
        "    };\n" ++
        "    comptime if @size_of[T]() == 8 {\n" ++
        "        let sz = @align_of[T]();\n" ++
        "    };\n" ++
        "    comptime for idx in 0..4 {\n" ++
        "        let step = idx;\n" ++
        "    }\n" ++
        "    if status is Ready {\n" ++
        "        return comptime @size_of[T]();\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";

    var pass1 = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);

    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "fn inspect[T](comptime label: str, status: Status) -> usize") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "@compile_assert(@size_of[T]() > 0, label);") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "comptime for idx in 0..4 {") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "if status is Ready {") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "return comptime @size_of[T]();") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    };\n") == null);

    var pass2 = try formatSource(std.testing.allocator, pass1.formatted_text, FileId.fromInt(0));
    defer pass2.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(pass1.formatted_text, pass2.formatted_text);
    try std.testing.expect(!pass2.is_changed);
}

test "test_format_dr21_surface_elevations_and_legacy_coloncolon_bailout" {
    const src =
        "fn is_empty(buf: &[u8]) -> bool = buf.len() == 0;\n\n" ++
        "fn process(items: &[u32], opt_val: Option[u32], raw: str) -> usize {\n" ++
        "    if (count := items.len()) > 0 and opt_val is not .None {\n" ++
        "        with context.allocator = arena, context.logger = log {\n" ++
        "            let parsed = raw |> trim() |> parse_usize() catch |err| 0;\n" ++
        "            let found = search: for item, idx in items[1..$ - 1] {\n" ++
        "                if item == parsed {\n" ++
        "                    break :search idx;\n" ++
        "                }\n" ++
        "            } orelse return 0;\n" ++
        "            match items {\n" ++
        "                whole @ [first, ..middle, last] => return found + whole.len(),\n" ++
        "                _ => return count,\n" ++
        "            }\n" ++
        "        }\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";

    var pass1 = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);
    try std.testing.expect(!pass1.has_syntax_errors);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "if (count := items.len()) > 0 and opt_val is not .None {") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "items[1..$-1]") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "} orelse return 0;") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "whole @ [first, ..middle, last]") != null);

    var pass2 = try formatSource(std.testing.allocator, pass1.formatted_text, FileId.fromInt(0));
    defer pass2.deinit(std.testing.allocator);
    try std.testing.expectEqualStrings(pass1.formatted_text, pass2.formatted_text);
    try std.testing.expect(!pass2.is_changed);

    // Legacy `::` emits `E0112` (`has_lexer_error`), causing safe verbatim formatter bailout:
    const legacy_src = "use cx::io::Read;\n";
    var legacy_res = try formatSource(std.testing.allocator, legacy_src, FileId.fromInt(0));
    defer legacy_res.deinit(std.testing.allocator);
    try std.testing.expect(legacy_res.has_syntax_errors);
    try std.testing.expect(!legacy_res.is_changed);
    try std.testing.expectEqualStrings(legacy_src, legacy_res.formatted_text);
}

test "test_format_dr22_canonical_rules_multiline_strings_and_idempotency" {
    const src =
        "pub(pkg) extern \"c\" fn printf(fmt: *u8, ...) -> i32;\n\n" ++
        "@no_panic\n" ++
        "@cfg(target_os: \"linux\")\n" ++
        "@inline\n" ++
        "@no_alloc\n" ++
        "pub(super) fn compute[T: Clone + Hash | Default](\n" ++
        "    ptr: *mut Option[u8],\n" ++
        "    opt_ptr: Option[*mut u8],\n" ++
        "    slice_opt: Option[&[u8]],\n" ++
        "    ref_opt: Option[&u8],\n" ++
        "    cb_opt: Option[fn() -> unit],\n" ++
        "    nested_res: Result[Result[u32, E1], E2],\n" ++
        "    ref_res: &Result[u32, IoError],\n" ++
        "    /,\n" ++
        "    *,\n" ++
        "    out_slot: &out u64,\n" ++
        ") -> unit {\n" ++
        "    @state var paused: bool = false;\n" ++
        "    let count = 42u64;\n" ++
        "    let ratio = 0.5f32;\n" ++
        "    let raw_p = &raw mut out_slot;\n" ++
        "    out_slot = raw_p.* + count + (ratio as u64);\n" ++
        "    let updated = Config { enabled: not paused, ..own base_cfg };\n" ++
        "    let task = own async || -> unit {\n" ++
        "  let msg = \"\"\"\n" ++
        "  line one\n" ++
        "    line two\n" ++
        "  \"\"\";\n" ++
        "            let dedented = \"\"\"\n" ++
        "            alpha\n" ++
        "              beta\n" ++
        "            \"\"\";\n" ++
        "    };\n" ++
        "    fsm: match state {\n" ++
        "        0 => continue :fsm 1,\n" ++
        "        _ => {},\n" ++
        "    }\n" ++
        "}\n\n" ++
        "fn render(body: @builder |&mut UiScope| -> unit) -> unit {\n" ++
        "    Card(title: \"Demo\") {\n" ++
        "        body(&mut scope);\n" ++
        "    }\n" ++
        "}\n\n" ++
        "test \"unit return stripped\" (fx: &Fixture) -> unit {\n" ++
        "    let ok = fx.check();\n" ++
        "}\n";

    var pass1 = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);
    try std.testing.expect(!pass1.has_syntax_errors);

    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "pub(pkg) extern \"C\" fn printf(fmt: *u8, ...) -> i32;") != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        pass1.formatted_text,
        "@cfg(target_os: \"linux\")\n@inline @no_alloc @no_panic\npub(super) fn compute[T: Clone + Hash | Default](",
    ) != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "ptr: *mut (u8?),") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "opt_ptr: *mut u8?,") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "slice_opt: &[u8]?,") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "ref_opt: (&u8)?,") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "cb_opt: (fn())?,") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "nested_res: (u32!E1)!E2,") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "ref_res: &(u32!IoError),") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "out_slot: &out u64,\n) {\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    @state var paused: bool = false;\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    let count = 42_u64;\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    let ratio = 0.5_f32;\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    let raw_p = &raw mut out_slot;\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    out_slot = raw_p.* + count + (ratio as u64);\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "..own base_cfg") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    let task = own async || {\n") != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        pass1.formatted_text,
        "        let msg = \"\"\"\n        line one\n          line two\n        \"\"\";\n",
    ) != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        pass1.formatted_text,
        "        let dedented = \"\"\"\n        alpha\n          beta\n        \"\"\";\n",
    ) != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    fsm: match state {\n        0 => continue :fsm 1,\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "fn render(body: @builder |&mut UiScope|) {\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "test \"unit return stripped\" (fx: &Fixture) {\n") != null);

    var pass2 = try formatSource(std.testing.allocator, pass1.formatted_text, FileId.fromInt(0));
    defer pass2.deinit(std.testing.allocator);
    try std.testing.expectEqualStrings(pass1.formatted_text, pass2.formatted_text);
    try std.testing.expect(!pass2.is_changed);
}

test "test_stage4_attributed_block_match_no_spurious_semi_and_raw_quote_runs" {
    const src =
        "pub fn run(state: i32, ptr: *i32) -> i32 {\n" ++
        "    let quoted = r#\"\"\"\"#;\n" ++
        "    let doc = \"\"\"\n" ++
        "        prefix {r#\"\"\"\"#} suffix\n" ++
        "        \"\"\";\n" ++
        "    @cfg(debug)\n" ++
        "    comptime {\n" ++
        "        let _ = 1;\n" ++
        "    }\n" ++
        "    @cfg(debug)\n" ++
        "    fsm: match state {\n" ++
        "        0 => continue :fsm 1,\n" ++
        "        _ => state,\n" ++
        "    }\n" ++
        "}\n";

    var pass1 = try formatSource(std.testing.allocator, src, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);
    try std.testing.expect(!pass1.has_syntax_errors);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "let quoted = r#\"\"\"\"#;\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    comptime {\n        let _ = 1;\n    }\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    comptime {\n        let _ = 1;\n    };") == null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "        _ => state,\n    }\n}\n") != null);

    var pass2 = try formatSource(std.testing.allocator, pass1.formatted_text, FileId.fromInt(0));
    defer pass2.deinit(std.testing.allocator);
    try std.testing.expectEqualStrings(pass1.formatted_text, pass2.formatted_text);
    try std.testing.expect(!pass2.is_changed);
}

test "test_format_extern_blocks_extern_static_and_comments_idempotency" {
    const raw_src =
        "// Leading extern block comment\n" ++
        "pub extern \"c\" {\n" ++
        "    // Foreign allocator signature\n" ++
        "    pub fn CreateFileW(path: *u16, access: u32) -> *mut opaque; // inline comment\n" ++
        "    fn EVP_DigestInit_ex(ctx: *mut opaque) -> i32;\n" ++
        "    pub(pkg) static mut _errno: i32;\n" ++
        "    const INVALID_HANDLE: usize = 0;\n" ++
        "    // Dangling comment before close\n" ++
        "}\n\n" ++
        "extern {}\n\n" ++
        "@link_name(\"_errno\")\n" ++
        "pub extern \"c\" static mut __errno_ptr: *mut i32;\n";

    var pass1 = try formatSource(std.testing.allocator, raw_src, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);
    try std.testing.expect(!pass1.has_syntax_errors);

    const expected =
        "// Leading extern block comment\n" ++
        "pub extern \"C\" {\n" ++
        "    // Foreign allocator signature\n" ++
        "    pub fn CreateFileW(path: *u16, access: u32) -> *mut opaque; // inline comment\n" ++
        "    fn EVP_DigestInit_ex(ctx: *mut opaque) -> i32;\n" ++
        "    pub(pkg) static mut _errno: i32;\n" ++
        "    const INVALID_HANDLE: usize = 0;\n" ++
        "    // Dangling comment before close\n" ++
        "}\n\n" ++
        "extern {}\n\n" ++
        "@link_name(\"_errno\")\n" ++
        "pub extern \"C\" static mut __errno_ptr: *mut i32;\n";
    try std.testing.expectEqualStrings(expected, pass1.formatted_text);

    var pass2 = try formatSource(std.testing.allocator, pass1.formatted_text, FileId.fromInt(0));
    defer pass2.deinit(std.testing.allocator);
    try std.testing.expect(!pass2.has_syntax_errors);
    try std.testing.expect(!pass2.is_changed);
    try std.testing.expectEqualStrings(expected, pass2.formatted_text);

    // Verify `--fix` mode preserves foreign C symbol names while inserting missing `;`:
    const fix_src =
        "extern \"C\" {\n" ++
        "    fn CreateFileW(path: *u16) -> *mut opaque;\n" ++
        "    static mut _errno_Val: i32\n" ++
        "}\n";
    var fix_res = try formatSourceWithOptions(
        std.testing.allocator,
        fix_src,
        FileId.fromInt(1),
        .{ .is_fix_mode = true },
    );
    defer fix_res.deinit(std.testing.allocator);
    try std.testing.expect(!fix_res.has_syntax_errors);
    try std.testing.expect(std.mem.indexOf(u8, fix_res.formatted_text, "fn CreateFileW(") != null);
    try std.testing.expect(std.mem.indexOf(u8, fix_res.formatted_text, "static mut _errno_Val: i32;") != null);
}

test "test_format_kw_async_module_paths_canonical_unchanged" {
    const canonical_src =
        "pub mod async;\n\n" ++
        "use cx.async.{TaskGroup, TaskHandle};\n\n" ++
        "pub async fn spawn_all(grp: &mut cx.async.TaskGroup[IoError], sub: &async.TaskGroup[IoError]) {\n" ++
        "    async.yield_now().await;\n" ++
        "    cx.async.task_group(|group| {\n" ++
        "        let _ = group;\n" ++
        "    });\n" ++
        "}\n";

    var res = try formatSource(std.testing.allocator, canonical_src, FileId.fromInt(0));
    defer res.deinit(std.testing.allocator);
    try std.testing.expect(!res.has_syntax_errors);
    try std.testing.expect(!res.is_changed);
    try std.testing.expectEqualStrings(canonical_src, res.formatted_text);
}

test "test_format_r1_wrapped_variadic_extern_fn_and_slice_rest_pattern_no_trailing_comma" {
    const raw_src =
        "pub extern \"C\" fn cx_format_diagnostic_variadic_record(" ++
        "sink_handle: *mut DiagnosticSink, format_template_utf8: *u8, severity_level: u32, ...) -> i32;\n\n" ++
        "pub fn inspect_long_slice(elements: &[i32]) -> i32 {\n" ++
        "    match elements {\n" ++
        "        [first_header_word, second_header_word, third_header_word, " ++
        "fourth_header_word, ..trailing_payload_words] => first_header_word,\n" ++
        "        [only_first_long_element_binding, only_second_long_element_binding, " ++
        "only_third_long_element_binding, ..] => only_first_long_element_binding,\n" ++
        "        _ => 0,\n" ++
        "    }\n" ++
        "}\n";

    var pass1 = try formatSource(std.testing.allocator, raw_src, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);
    try std.testing.expect(!pass1.has_syntax_errors);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "...,") == null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "..trailing_payload_words,") == null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "..,") == null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "    ...\n) -> i32;") != null);

    var pass2 = try formatSource(std.testing.allocator, pass1.formatted_text, FileId.fromInt(0));
    defer pass2.deinit(std.testing.allocator);
    try std.testing.expect(!pass2.has_syntax_errors);
    try std.testing.expect(!pass2.is_changed);
    try std.testing.expectEqualStrings(pass1.formatted_text, pass2.formatted_text);
}

test "test_format_script_toml_frontmatter_and_inline_string_use_idempotency" {
    const raw_script =
        "#!/usr/bin/env corex\n" ++
        "---\n" ++
        "[dependencies]\n" ++
        "corex-http = \"2.1.0\" # preserve verbatim TOML comment\n" ++
        "---\n\n" ++
        "use   \"https://github.com/org/repo.git#v1.0.0\"   as   repo_client ;\n\n" ++
        "pub fn main() -> i32 { return 0; }\n";

    var pass1 = try formatSource(std.testing.allocator, raw_script, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);
    try std.testing.expect(!pass1.has_syntax_errors);
    try std.testing.expect(pass1.is_changed);

    const expected =
        "#!/usr/bin/env corex\n" ++
        "---\n" ++
        "[dependencies]\n" ++
        "corex-http = \"2.1.0\" # preserve verbatim TOML comment\n" ++
        "---\n\n" ++
        "use \"https://github.com/org/repo.git#v1.0.0\" as repo_client;\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    return 0;\n" ++
        "}\n";
    try std.testing.expectEqualStrings(expected, pass1.formatted_text);

    var pass2 = try formatSource(std.testing.allocator, pass1.formatted_text, FileId.fromInt(0));
    defer pass2.deinit(std.testing.allocator);
    try std.testing.expect(!pass2.has_syntax_errors);
    try std.testing.expect(!pass2.is_changed);
    try std.testing.expectEqualStrings(expected, pass2.formatted_text);

    const fix_src = "use \"corex-http@^2.1.0\" as HttpClient\n";
    var fix_res = try formatSourceWithOptions(
        std.testing.allocator,
        fix_src,
        FileId.fromInt(1),
        .{ .is_fix_mode = true },
    );
    defer fix_res.deinit(std.testing.allocator);
    try std.testing.expect(!fix_res.has_syntax_errors);
    try std.testing.expectEqualStrings("use \"corex-http@^2.1.0\" as http_client;\n", fix_res.formatted_text);

    const crlf_script =
        "#!/usr/bin/env corex\r\n" ++
        "---\r\n" ++
        "[dependencies]\r\n" ++
        "corex-http = \"2.1.0\"\r\n" ++
        "---\r\n\r\n" ++
        "pub fn main() -> i32 { return 0; }\r\n";
    var crlf_res = try formatSource(std.testing.allocator, crlf_script, FileId.fromInt(2));
    defer crlf_res.deinit(std.testing.allocator);
    try std.testing.expect(!crlf_res.has_syntax_errors);
    try std.testing.expect(crlf_res.is_changed);
    try std.testing.expect(std.mem.indexOfScalar(u8, crlf_res.formatted_text, '\r') == null);
}

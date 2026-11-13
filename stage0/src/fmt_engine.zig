//! CoreX Hybrid Steerable Wadler-Lindig Formatter & 8-Byte `DocArena` (`stage0/src/fmt_engine.zig`)
//!
//! Implements the deterministic, comment-preserving source formatter (`corex fmt`) and autofix pass
//! (`corex fmt --fix`) specified in `DR-03` Section 7 and `DR-14` Section 1. Lowers the lossless
//! Concrete Syntax Tree (`LosslessCstArena`) and `TokenBuffer` into a flat array of 8-byte `DocInst`
//! document algebra instructions with $O(1)$ open-group `flat_width` backpatching.
//!
//! - **8-Byte `DocInst` & $O(1)$ Group Backpatching:** Packs every document algebra instruction into
//!   an `extern struct` of exactly 8 bytes (`DocOp` + `mode_or_delta` + `flat_width` + `payload`).
//!   `DocArena.endGroup()` backpatches `flat_width` in $O(1)$ time without recursive tree walks.
//! - **100% Comment Preservation & `line_suffix` Queue:** Pre-classifies inter-token trivia into
//!   leading comments and same-line trailing comments (`line_suffix`), handles dangling comments in
//!   empty `{}` / `()` / `[]` containers, and flushes all unconsumed comments up through `.eof`.
//! - **Steerable Formatting & Columnar Grids:** Respects user trailing commas (`GroupMode.force_break`
//!   vs `GroupMode.auto_fit`), formats literal arrays with `> 8` elements in `GroupMode.columnar_grid`,
//!   aligns multiline `|>` pipe and `.` postfix chains, strips redundant outer parentheses on
//!   `if`/`while`/`for`/`match` headers, sorts braced `use` specifiers, and honors `// corex fmt: off`.

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
        self.instructions.deinit(self.allocator);
        self.open_groups.deinit(self.allocator);
        self.string_bytes.deinit(self.allocator);
        self.line_suffix_slices.deinit(self.allocator);
        self.if_break_pairs.deinit(self.allocator);
        self.verbatim_slices.deinit(self.allocator);
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
            self.current_col = self.pending_indent_spaces;
            self.is_at_line_start = false;
            self.consecutive_newlines = 0;
        }
        try self.out.appendSlice(self.allocator, slice);
        self.current_col += @intCast(slice.len);
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
                        self.current_col = self.pending_indent_spaces;
                    }
                    self.is_at_line_start = false;
                    self.consecutive_newlines = 0;
                    for (raw_slice) |byte_val| {
                        if (byte_val == '\r') continue;
                        try self.out.append(self.allocator, byte_val);
                        if (byte_val == '\n') {
                            self.current_col = 0;
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
    /// Start index in `token_buffer.trivia.items` for this token's leading trivia.
    leading_start: u32 = 0,
    /// End index in `token_buffer.trivia.items` for this token's leading trivia.
    leading_end: u32 = 0,
    /// Start index in `token_buffer.trivia.items` of same-line trailing trivia stolen from next token.
    stolen_trailing_start: u32 = 0,
    /// End index in `token_buffer.trivia.items` of same-line trailing trivia stolen from next token.
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

/// Sortable entry representing a single specifier inside a braced `use a::b::{…};` group.
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

/// Extracts all `// corex fmt: off` … `// corex fmt: on` byte ranges from `token_buffer.trivia`.
fn extractSuppressedRanges(
    allocator: std.mem.Allocator,
    source: []const u8,
    token_buffer: *const TokenBuffer,
) !std.ArrayList(SuppressedRange) {
    var ranges: std.ArrayList(SuppressedRange) = .empty;
    errdefer ranges.deinit(allocator);

    var active_off_start: ?u32 = null;
    for (token_buffer.trivia.items) |piece| {
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

/// Pre-classifies leading and same-line trailing trivia for every token in `token_buffer`.
fn buildTokenTriviaMeta(
    allocator: std.mem.Allocator,
    token_buffer: *const TokenBuffer,
) ![]TokenTriviaMeta {
    const token_count = token_buffer.countTokens();
    const meta_table = try allocator.alloc(TokenTriviaMeta, token_count);
    @memset(meta_table, .{});

    const all_trivia = token_buffer.trivia.items;
    var prev_real_tok: ?u32 = null;

    var i: usize = 0;
    while (i < token_count) : (i += 1) {
        const tok_id = TokenIndex.fromInt(@intCast(i));
        const rec = token_buffer.getToken(tok_id);
        const lead_start: u32 = rec.trivia_span.start_index;
        const lead_count: u32 = rec.trivia_span.leading_count;
        const lead_end: u32 = lead_start + lead_count;
        const trail_start: u32 = lead_end;
        const trail_end: u32 = trail_start + rec.trivia_span.trailing_count;

        var meta = &meta_table[i];
        meta.leading_start = lead_start;
        meta.leading_end = lead_end;

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

    return meta_table;
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
        if (rec.flags.has_lexer_error) return true;
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
        .defer_stmt,
        .assign_stmt,
        .expr_stmt,
        .use_item,
        .const_item,
        .type_alias_item,
        .mod_item,
        .fn_item,
        .trait_member,
        .impl_member,
        => {},
        else => return false,
    }
    const end_idx: usize = node_idx.asInt() + node.subtree_size;
    var child_idx: usize = node_idx.asInt() + 1;
    while (child_idx < end_idx) {
        const child_id = CstNodeIndex.fromInt(@intCast(child_idx));
        const child = cst_arena.getNode(child_id);
        if (child.kind == .invalid_parse_subtree or child.kind == .invalid_parse_leaf) {
            return false;
        }
        if (child.subtree_size == 1 and !child.token.isNone()) {
            const tok_rec = token_buffer.getToken(child.token);
            if (tok_rec.flags.is_synthesized and tok_rec.kind != .semi) {
                return false;
            }
        }
        child_idx += child.subtree_size;
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
        const token_meta = try buildTokenTriviaMeta(allocator, token_buffer);
        errdefer allocator.free(token_meta);
        var suppressed_ranges = try extractSuppressedRanges(allocator, source, token_buffer);
        errdefer suppressed_ranges.deinit(allocator);

        var self = CstFormatter{
            .allocator = allocator,
            .source = source,
            .token_buffer = token_buffer,
            .cst_arena = cst_arena,
            .doc_arena = doc_arena,
            .token_meta = token_meta,
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
        const all_trivia = self.token_buffer.trivia.items;
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
        for (self.token_buffer.getTrailingTrivia(last_tok)) |piece| {
            if (isCommentOrShebangTrivia(piece.kind)) {
                max_end = @max(max_end, piece.byte_offset + piece.byte_len);
            }
        }
        const meta = self.token_meta[last_tok.asInt()];
        const all_trivia = self.token_buffer.trivia.items;
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

        const all_trivia = self.token_buffer.trivia.items;
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

        for (self.token_buffer.getTrailingTrivia(tok_id)) |piece| {
            if (!isCommentOrShebangTrivia(piece.kind)) continue;
            const start: usize = piece.byte_offset;
            const end: usize = @min(self.source.len, start + piece.byte_len);
            try self.doc_arena.emitLineSuffix(self.source[start..end]);
        }

        const all_trivia = self.token_buffer.trivia.items;
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

        const all_trivia = self.token_buffer.trivia.items;
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

    /// Pre-scans declarations in `--fix` mode to build the `old_name -> new_name` casing rename map.
    fn collectFixRenames(self: *CstFormatter, root_idx: CstNodeIndex) !void {
        const total_nodes = self.cst_arena.countNodes();
        var idx: usize = root_idx.asInt();
        while (idx < total_nodes) : (idx += 1) {
            const node_id = CstNodeIndex.fromInt(@intCast(idx));
            const node = self.cst_arena.getNode(node_id);
            switch (node.kind) {
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
                .fn_sig, .struct_field, .fn_param, .closure_param, .mod_item => {
                    if (self.findFirstIdentTokenInDirectChildren(node_id)) |tok_id| {
                        try self.registerFixRename(tok_id, .snake_case);
                    }
                },
                .local_decl_stmt => {
                    if (self.findLocalDeclIdentToken(node_id)) |tok_id| {
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
        if (rec.flags.is_synthesized or !isRenamableIdentifierKind(rec.kind)) return;
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

    /// Returns whether `node_idx` is a bodyless trait member signature (`type`, `const`, or `fn …;`).
    fn isCompactTraitSignatureItem(self: *const CstFormatter, node_idx: CstNodeIndex) bool {
        const node = self.cst_arena.getNode(node_idx);
        return switch (node.kind) {
            .type_alias_item, .const_item => true,
            .trait_member, .fn_item => !self.hasDirectChildKind(node_idx, .block),
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

    /// Formats a `.use_item` declaration (`[pub] use a::b::{…};`).
    fn formatUseItem(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var has_emitted_semi = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                try self.formatAttribute(child_id);
                try self.doc_arena.emitHardLine();
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .visibility_modifier or tok_kind == .kw_pub) {
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

    /// Formats a `.const_item` declaration (`[pub] const NAME: Type = expr;`).
    fn formatConstItem(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var has_emitted_semi = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                try self.formatAttribute(child_id);
                try self.doc_arena.emitHardLine();
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .visibility_modifier or tok_kind == .kw_pub) {
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

    /// Formats a `.type_alias_item` declaration (`[pub] type Name[T] = Target;`).
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

        var has_emitted_semi = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                try self.formatAttribute(child_id);
                try self.doc_arena.emitHardLine();
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .visibility_modifier or tok_kind == .kw_pub) {
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

    /// Formats a `.mod_item` declaration (`[pub] mod name;` or `[pub] mod name { … }`).
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
            var has_semi = false;
            for (children.items) |child_id| {
                const child = self.cst_arena.getNode(child_id);
                if (child.kind == .attribute) {
                    try self.formatAttribute(child_id);
                    try self.doc_arena.emitHardLine();
                    continue;
                }
                if (child.subtree_size == 1 and !child.token.isNone()) {
                    const tok_kind = self.token_buffer.getToken(child.token).kind;
                    if (child.kind == .visibility_modifier or tok_kind == .kw_pub) {
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
        for (children.items[0..lb_idx]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                try self.formatAttribute(child_id);
                try self.doc_arena.emitHardLine();
            } else if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .visibility_modifier or tok_kind == .kw_pub) {
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

    /// Formats a `.struct_item`, `.union_item`, or `.enum_item` declaration.
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
        for (children.items[0..header_end]) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                try self.formatAttribute(child_id);
                try self.doc_arena.emitHardLine();
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .visibility_modifier or tok_kind == .kw_pub) {
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

    /// Formats a `.struct_field` node, normalizing any legacy `;` separator to `,`.
    fn formatStructField(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var has_emitted_comma = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                try self.formatAttribute(child_id);
                try self.doc_arena.emitHardLine();
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .visibility_modifier or tok_kind == .kw_pub) {
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

    /// Formats an `.enum_variant` node, normalizing any `;` separator to `,`.
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

        var has_emitted_comma = false;
        var idx: usize = 0;
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
                    for (inner_fields, 0..) |f_id, f_i| {
                        if (f_i > 0) try self.doc_arena.emitHardLine();
                        try self.formatStructField(f_id);
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
        {
            self.in_type_context += 1;
            defer self.in_type_context -= 1;
            var prev_was_impl_with_type_params = false;
            for (children.items[0..header_end], 0..) |child_id, idx| {
                const child = self.cst_arena.getNode(child_id);
                if (child.kind == .attribute) {
                    try self.formatAttribute(child_id);
                    try self.doc_arena.emitHardLine();
                    continue;
                }
                if (child.subtree_size == 1 and !child.token.isNone()) {
                    const tok_kind = self.token_buffer.getToken(child.token).kind;
                    if (child.kind == .visibility_modifier or tok_kind == .kw_pub) {
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

    /// Formats a `.fn_item`, `.trait_member`, or `.impl_member` declaration.
    fn formatFnOrMember(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var has_block_body = false;
        var has_emitted_semi = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                try self.formatAttribute(child_id);
                try self.doc_arena.emitHardLine();
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .visibility_modifier or tok_kind == .kw_pub) {
                    try self.emitTokenWithTrivia(child.token, "pub", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_async or tok_kind == .kw_unsafe or
                    tok_kind == .kw_extern or tok_kind == .kw_comptime)
                {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .string_lit) {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (child.kind == .fn_introducer or tok_kind == .kw_fn) {
                    const lex = self.getTokenLexeme(child.token);
                    try self.emitTokenWithTrivia(child.token, null, false);
                    if (std.mem.eql(u8, lex, "subscript")) {
                        const next_tok = if (child.token.asInt() + 1 < self.token_buffer.countTokens())
                            self.token_buffer.getToken(TokenIndex.fromInt(child.token.asInt() + 1)).kind
                        else
                            .eof;
                        if (next_tok != .lparen and next_tok != .lbracket) {
                            try self.doc_arena.emitText(" ");
                        }
                    } else {
                        try self.doc_arena.emitText(" ");
                    }
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    has_emitted_semi = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else if (child.kind == .fn_sig) {
                try self.formatFnSig(child_id);
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

    /// Formats a `.fn_sig` node (`name[T](params) -> Ret where …`).
    fn formatFnSig(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
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
                try self.formatReturnType(child_id);
            } else if (child.kind == .where_clause) {
                try self.formatWhereClause(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.return_type` node (` -> Type` or `: Type` on `subscript`).
    fn formatReturnType(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

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

    /// Formats a `.param_list` node (`(a: i32, b: String)`), respecting trailing-comma steerability.
    fn formatParamList(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatSteerableDelimitedList(node_idx, .fn_param, .lparen, .rparen, "(", ")", false);
    }

    /// Formats a single `.fn_param` node (`[&[mut] | mut] self` or `name: [mode] Type [= default]`).
    fn formatFnParam(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                try self.formatAttribute(child_id);
                try self.doc_arena.emitText(" ");
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .eq) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "=", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .kw_mut or tok_kind == .kw_own or tok_kind == .kw_ref or
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
                const is_single_elem_tuple = (node_idx.asInt() < self.cst_arena.countNodes() and
                    self.cst_arena.getNode(node_idx).kind == .tuple_or_paren_expr and
                    elements.items.len == 1 and has_trailing_comma);
                if (is_single_elem_tuple) {
                    try self.doc_arena.emitText(",");
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
            for (children.items[0..blk_idx]) |prefix_id| {
                const prefix = self.cst_arena.getNode(prefix_id);
                if (prefix.kind == .attribute) {
                    try self.formatAttribute(prefix_id);
                    try self.doc_arena.emitHardLine();
                } else if (prefix.subtree_size == 1 and !prefix.token.isNone()) {
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

    /// Formats a `.local_decl_stmt` (`let [mut] pat [: Type] [= expr [else { … }]];`).
    fn formatLocalDeclStmt(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var has_emitted_semi = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.kind == .attribute) {
                try self.formatAttribute(child_id);
                try self.doc_arena.emitHardLine();
                continue;
            }
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (child.kind == .local_decl_introducer or tok_kind == .kw_let or tok_kind == .kw_var) {
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
        if (!has_emitted_semi) {
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

    /// Formats a `.return_stmt`, `.break_stmt`, or `.continue_stmt` with a guaranteed `;`.
    fn formatJumpStmt(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
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
                    tok_kind == .kw_continue or std.mem.eql(u8, self.getTokenLexeme(child.token), "yield")))
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
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    has_emitted_semi = true;
                } else {
                    try self.emitTokenWithTrivia(child.token, null, false);
                }
            } else {
                try self.formatNode(child_id);
            }
        }
        // Only emit trailing `;` when `node_idx` is a statement (not an inline `yield expr` expression):
        if (!has_emitted_semi) {
            const first_tok = self.findFirstTokenInSubtree(node_idx);
            const is_yield_expr = !first_tok.isNone() and
                std.mem.eql(u8, self.getTokenLexeme(first_tok), "yield");
            if (!is_yield_expr) {
                try self.doc_arena.emitText(";");
            }
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

    /// Returns whether `subtree_idx` contains any `.struct_lit_expr`, `.view_block_expr`, or `.block`.
    fn hasStructLitOrBlockInSubtree(self: *const CstFormatter, subtree_idx: CstNodeIndex) bool {
        const root = self.cst_arena.getNode(subtree_idx);
        const end_idx: usize = subtree_idx.asInt() + root.subtree_size;
        var idx: usize = subtree_idx.asInt();
        while (idx < end_idx) : (idx += 1) {
            const kind = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(idx))).kind;
            if (kind == .struct_lit_expr or kind == .view_block_expr or kind == .block) {
                return true;
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

    /// Formats an `.if_cond` or `.while_header` (`[let pat =] cond [|cap|]`), stripping outer parens.
    fn formatConditionHeader(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        if (children.items.len == 1) {
            try self.formatHeaderExprStrippingOuterParens(children.items[0]);
            return;
        }

        var pipe_count: usize = 0;
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
                } else if (tok_kind == .pipe) {
                    if (pipe_count == 0) {
                        try self.doc_arena.emitText(" ");
                    }
                    pipe_count += 1;
                    try self.emitTokenWithTrivia(child.token, "|", false);
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

    /// Formats a `.for_stmt` (`[comptime] for pat in iter { … }`), stripping outer parens on `iter`.
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

    /// Formats a `.for_header` (`pat in iter`), stripping redundant outer parens on `iter`.
    fn formatForHeader(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var seen_kw_in = false;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_in) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "in", false);
                    try self.doc_arena.emitText(" ");
                    seen_kw_in = true;
                    continue;
                }
            }
            if (seen_kw_in) {
                try self.formatHeaderExprStrippingOuterParens(child_id);
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.while_stmt` (`while cond { … }`), stripping outer parens on `cond`.
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

    /// Formats a `.loop_expr` (`loop { … }`).
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
            } else {
                try self.formatNode(child_id);
            }
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
            if (child.subtree_size == 1 and !child.token.isNone() and
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

    /// Formats a `.field_init` (`name: expr`, shorthand `name`, or `..base`).
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
            // Measure total flat width and max element width:
            var max_elem_len: usize = 1;
            var total_flat_len: usize = 2;
            for (elements.items, 0..) |elem_id, elem_i| {
                const first_t = self.findFirstTokenInSubtree(elem_id);
                const last_t = self.findLastTokenInSubtree(elem_id);
                const start_b: usize = self.token_buffer.getToken(first_t).byte_offset;
                const end_rec = self.token_buffer.getToken(last_t);
                const end_b: usize = @min(self.source.len, @as(usize, end_rec.byte_offset) + end_rec.byte_len);
                const elem_len = end_b -| start_b;
                max_elem_len = @max(max_elem_len, elem_len);
                total_flat_len += elem_len + (if (elem_i + 1 < elements.items.len) @as(usize, 2) else 0);
            }

            const should_break_grid = has_trailing_comma or
                self.isNodeMultilineInSource(node_idx) or
                (total_flat_len + 16 > MAX_LINE_WIDTH);

            if (should_break_grid) {
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

                try self.emitTokenWithTrivia(open_tok, "[", false);
                _ = try self.doc_arena.beginGroup(.columnar_grid);
                self.doc_arena.poisonOpenGroups();
                try self.doc_arena.beginIndent(INDENT_SPACES);
                try self.doc_arena.emitHardLine();

                for (elements.items, 0..) |elem_id, elem_i| {
                    const first_t = self.findFirstTokenInSubtree(elem_id);
                    const last_t = self.findLastTokenInSubtree(elem_id);
                    const start_b: usize = self.token_buffer.getToken(first_t).byte_offset;
                    const end_rec = self.token_buffer.getToken(last_t);
                    const end_b: usize = @min(self.source.len, @as(usize, end_rec.byte_offset) + end_rec.byte_len);
                    const elem_len = end_b -| start_b;

                    const is_row_end = ((elem_i + 1) % cols_per_row == 0) or
                        (elem_i + 1 == elements.items.len);

                    // Left-pad numeric literals within the column cell so digits align cleanly:
                    if (elem_len < max_elem_len) {
                        var pad_i: usize = 0;
                        while (pad_i < max_elem_len - elem_len) : (pad_i += 1) {
                            try self.doc_arena.emitText(" ");
                        }
                    }
                    try self.formatNode(elem_id);
                    try self.doc_arena.emitText(",");

                    if (!is_row_end) {
                        try self.doc_arena.emitText(" ");
                    } else if (elem_i + 1 < elements.items.len) {
                        try self.doc_arena.emitHardLine();
                    }
                }

                try self.doc_arena.endIndent(INDENT_SPACES);
                try self.doc_arena.emitHardLine();
                try self.doc_arena.endGroup();
                try self.emitTokenWithTrivia(close_tok, "]", false);
                return;
            }
        }

        try self.formatSteerableDelimitedList(node_idx, null, .lbracket, .rbracket, "[", "]", false);
    }

    /// Formats a `.tuple_or_paren_expr` (`(a)` or `(a, b)`).
    fn formatTupleOrParenExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        try self.formatSteerableDelimitedList(node_idx, null, .lparen, .rparen, "(", ")", false);
    }

    /// Formats a `.closure_expr` (`|a: i32, b| expr` or `|| { … }`).
    fn formatClosureExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        var pipe_count: usize = 0;
        var param_count: usize = 0;
        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .pipepipe) {
                    try self.emitTokenWithTrivia(child.token, "||", false);
                    try self.doc_arena.emitText(" ");
                    pipe_count = 2;
                } else if (tok_kind == .pipe) {
                    pipe_count += 1;
                    try self.emitTokenWithTrivia(child.token, "|", false);
                    if (pipe_count == 2) {
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
            } else {
                try self.formatNode(child_id);
            }
        }
    }

    /// Formats a `.closure_param` (`[mut] name [: Type]`).
    fn formatClosureParam(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items) |child_id| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_mut or tok_kind == .kw_own or tok_kind == .kw_ref) {
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

    /// Formats an `.infix_expr`, aligning `|>` pipe chains with leading `|>` on broken lines.
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

        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

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
                } else if (tok_kind == .kw_catch) {
                    try self.doc_arena.emitText(" ");
                    try self.emitTokenWithTrivia(child.token, "catch", false);
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

    /// Formats a `.prefix_expr` (`-x`, `!x`, `~x`, `&x`, `&mut x`, `*x`, `comptime expr`).
    fn formatPrefixExpr(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if ((tok_kind == .kw_mut or tok_kind == .kw_own or tok_kind == .kw_ref or
                    tok_kind == .kw_let or tok_kind == .kw_comptime or tok_kind == .ident) and
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

    /// Formats a chain of `.field_or_method_expr`, `.postfix_try_expr`, and `.postfix_await_expr` nodes.
    fn formatPostfixChain(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        var chain_nodes: std.ArrayList(CstNodeIndex) = .empty;
        defer chain_nodes.deinit(self.allocator);

        var curr_id = node_idx;
        var dot_link_count: usize = 0;
        var has_user_newline = false;

        while (true) {
            const curr = self.cst_arena.getNode(curr_id);
            if (curr.kind != .field_or_method_expr and
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

        if (dot_link_count >= 2 or has_user_newline) {
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

    /// Formats a type CST node (`.ref_type`, `.ptr_type`, `.mode_type`, `.slice_or_array_type`, `.fn_type`).
    fn formatTypeNode(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        self.in_type_context += 1;
        defer self.in_type_context -= 1;

        const node = self.cst_arena.getNode(node_idx);
        if (node.kind == .tuple_type) {
            try self.formatSteerableDelimitedList(node_idx, null, .lparen, .rparen, "(", ")", false);
            return;
        }

        var children: std.ArrayList(CstNodeIndex) = .empty;
        defer children.deinit(self.allocator);
        try self.collectDirectChildren(node_idx, &children);

        for (children.items, 0..) |child_id, idx| {
            const child = self.cst_arena.getNode(child_id);
            if (child.subtree_size == 1 and !child.token.isNone()) {
                const tok_kind = self.token_buffer.getToken(child.token).kind;
                if (tok_kind == .kw_mut or tok_kind == .kw_own or tok_kind == .kw_ref or
                    tok_kind == .kw_const or tok_kind == .kw_let or
                    tok_kind == .kw_async or tok_kind == .kw_unsafe or
                    tok_kind == .hash_soa or
                    (tok_kind == .ident and idx + 1 < children.items.len and
                        (node.kind == .mode_type or node.kind == .ref_type)))
                {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .semi) {
                    try self.emitTokenWithTrivia(child.token, ";", false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .comma) {
                    try self.emitTokenWithTrivia(child.token, ",", false);
                    if (idx + 1 < children.items.len) {
                        const next_c = self.cst_arena.getNode(children.items[idx + 1]);
                        const is_close = next_c.subtree_size == 1 and !next_c.token.isNone() and
                            self.token_buffer.getToken(next_c.token).kind == .rparen;
                        if (!is_close) try self.doc_arena.emitText(" ");
                    }
                } else if (tok_kind == .arrow) {
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

    /// Formats a pattern CST node (`.tuple_pat`, `.struct_pat`, `.field_pat`, `.or_pat`, `.ident_pat`).
    fn formatPatternNode(self: *CstFormatter, node_idx: CstNodeIndex) anyerror!void {
        const node = self.cst_arena.getNode(node_idx);
        switch (node.kind) {
            .tuple_pat => {
                try self.formatSteerableDelimitedList(node_idx, null, .lparen, .rparen, "(", ")", false);
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
                if (tok_kind == .kw_mut or tok_kind == .kw_own or tok_kind == .kw_ref) {
                    try self.emitTokenWithTrivia(child.token, null, false);
                    try self.doc_arena.emitText(" ");
                } else if (tok_kind == .colon) {
                    try self.emitTokenWithTrivia(child.token, ":", false);
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

    /// Dispatches CST node `node_idx` to its canonical `DR-03` / `DR-14` formatting routine.
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
            .use_item => try self.formatUseItem(node_idx),
            .use_tree => try self.formatUseTree(node_idx),
            .const_item => try self.formatConstItem(node_idx),
            .type_alias_item => try self.formatTypeAliasItem(node_idx),
            .mod_item => try self.formatModItem(node_idx),
            .struct_item, .union_item, .enum_item => try self.formatStructOrUnionOrEnum(node_idx),
            .struct_field => try self.formatStructField(node_idx),
            .enum_variant => try self.formatEnumVariant(node_idx),
            .trait_item, .impl_item => try self.formatTraitOrImpl(node_idx),
            .fn_item, .trait_member, .impl_member => try self.formatFnOrMember(node_idx),
            .fn_sig => try self.formatFnSig(node_idx),
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
            .return_stmt, .break_stmt, .continue_stmt => try self.formatJumpStmt(node_idx),
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
            .field_or_method_expr, .postfix_try_expr, .postfix_await_expr => {
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
            .optional_type,
            => try self.formatTypeNode(node_idx),
            .wildcard_pat,
            .literal_pat,
            .range_pat,
            .tuple_pat,
            .ident_pat,
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
        "use std::collections::{HashMap, BTreeMap, self, Vec};\n" ++
        "use core::mem;\n";
    var res_flat = try formatSource(std.testing.allocator, src_flat, FileId.fromInt(0));
    defer res_flat.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(
        "use std::collections::{self, BTreeMap, HashMap, Vec};\n" ++
            "use core::mem;\n",
        res_flat.formatted_text,
    );

    // Trailing comma inside `use` braces forces multiline break:
    const src_broken = "use std::collections::{Vec, BTreeMap,};\n";
    var res_broken = try formatSource(std.testing.allocator, src_broken, FileId.fromInt(0));
    defer res_broken.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(
        "use std::collections::{\n" ++
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
        "    x: i32; // trailing on x\n" ++
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
        "    subscript cell_at(idx: usize) -> i32 {\n" ++
        "        return 0;\n" ++
        "    }\n\n" ++
        "    subscript(idx: usize) -> i32 {\n" ++
        "        return 0;\n" ++
        "    }\n" ++
        "}\n\n" ++
        "fn evaluate(point_val: Point, opt_val: Option) -> i32 {\n" ++
        "    let neg_one = -point_val.x;\n" ++
        "    let double_neg = - -neg_one;\n" ++
        "    match point_val {\n" ++
        "        Point { x, y, .. } => x + y,\n" ++
        "    }\n" ++
        "    match opt_val {\n" ++
        "        Option::Some(inner_val) => inner_val,\n" ++
        "        Option::Pair { first_val, second_val } => first_val + second_val,\n" ++
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
        "use std::io::{\n" ++
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

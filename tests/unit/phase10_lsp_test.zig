//! Phase 10 Language Server Protocol (`LSP 3.17`) End-to-End Verification Suite
//!
//! Exercises `corex.lsp_server.runServerStream`, `corex.VfsSourceMap`, and `corex.CompilerDb` across
//! the complete LSP 3.17 lifecycle, UTF-16 vs. UTF-8 astral position negotiation, `didChange` batch
//! coalescing, `$/cancelRequest` pre-draining, push/pull diagnostics, semantic token deltas, `DR-17`
//! contract/capability hovers, cross-file navigation, inlay hints, hygienic renames, and formatting.
//!
//! All multi-file workspace fixtures execute inside isolated `.zig-cache/tmp/phase10_lsp_*` directories
//! under `std.testing.allocator` with zero memory leaks and zero host-state side effects.

const std = @import("std");
const corex = @import("corex");

const lsp_server = corex.lsp_server;
const LspServerOptions = lsp_server.LspServerOptions;

// ---------------------------------------- TYPES ----------------------------------------

/// Parsed `SemanticTokensEdit` record decoded from a `semanticTokens/full/delta` JSON response.
const DecodedSemanticEdit = struct {
    /// Zero-based start offset in the previous `u32` token data array.
    start: usize,
    /// Number of `u32` elements deleted starting at `start`.
    delete_count: usize,
    /// Owned slice of replacement `u32` elements inserted at `start`.
    replacement: []u32,

    /// Releases the owned `replacement` slice.
    fn deinit(self: *DecodedSemanticEdit, allocator: std.mem.Allocator) void {
        allocator.free(self.replacement);
        self.* = undefined;
    }
};

/// Captured exit status and outbound JSON-RPC frame payloads from a `runServerStream` session.
const LspTranscriptOutcome = struct {
    /// Process exit status returned by `lsp_server.runServerStream`.
    exit_code: u8,
    /// Owned raw wire bytes written by the server.
    raw_wire: []u8,
    /// Owned array of slices into `raw_wire` representing each outbound JSON frame body.
    frames: [][]const u8,

    /// Releases `frames` and `raw_wire` buffers.
    fn deinit(self: *LspTranscriptOutcome, allocator: std.mem.Allocator) void {
        allocator.free(self.frames);
        allocator.free(self.raw_wire);
        self.* = undefined;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Monotonic sequence counter guaranteeing collision-free temporary directories across test threads.
var next_workspace_seq: std.atomic.Value(u32) = .init(1);

// -------------------------------------- INTERNALS --------------------------------------

// ------------------- JSON-RPC Wire Helpers --------------------

/// Escapes `raw_text` as a JSON string literal (`"…"`) into `writer`.
fn writeEscapedJsonString(writer: *std.Io.Writer, raw_text: []const u8) !void {
    try writer.writeByte('"');
    for (raw_text) |byte_val| {
        switch (byte_val) {
            '"' => try writer.writeAll("\\\""),
            '\\' => try writer.writeAll("\\\\"),
            '\n' => try writer.writeAll("\\n"),
            '\r' => try writer.writeAll("\\r"),
            '\t' => try writer.writeAll("\\t"),
            else => {
                if (byte_val < 0x20) {
                    try writer.print("\\u{x:0>4}", .{byte_val});
                } else {
                    try writer.writeByte(byte_val);
                }
            },
        }
    }
    try writer.writeByte('"');
}

/// Appends a `Content-Length` framed JSON-RPC message onto `inbound_buf`.
fn appendLspFrame(
    allocator: std.mem.Allocator,
    inbound_buf: *std.ArrayListUnmanaged(u8),
    json_body: []const u8,
) !void {
    const header_str = try std.fmt.allocPrint(
        allocator,
        "Content-Length: {d}\r\n\r\n",
        .{json_body.len},
    );
    defer allocator.free(header_str);
    try inbound_buf.appendSlice(allocator, header_str);
    try inbound_buf.appendSlice(allocator, json_body);
}

/// Appends a `textDocument/didOpen` notification frame for `(uri_str, version_num, source_text)`.
fn appendDidOpenFrame(
    allocator: std.mem.Allocator,
    inbound_buf: *std.ArrayListUnmanaged(u8),
    uri_str: []const u8,
    version_num: i64,
    source_text: []const u8,
) !void {
    var msg_alloc = std.Io.Writer.Allocating.init(allocator);
    defer msg_alloc.deinit();
    try msg_alloc.writer.writeAll("{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":");
    try writeEscapedJsonString(&msg_alloc.writer, uri_str);
    try msg_alloc.writer.print(",\"languageId\":\"corex\",\"version\":{d},\"text\":", .{version_num});
    try writeEscapedJsonString(&msg_alloc.writer, source_text);
    try msg_alloc.writer.writeAll("}}}");
    try appendLspFrame(allocator, inbound_buf, msg_alloc.written());
}

/// Parses the decimal `Content-Length` header value from a raw LSP header block.
fn extractFrameContentLength(header_bytes: []const u8) ?usize {
    var line_iter = std.mem.splitSequence(u8, header_bytes, "\r\n");
    while (line_iter.next()) |header_line| {
        const prefix = "Content-Length:";
        if (header_line.len >= prefix.len and
            std.ascii.eqlIgnoreCase(header_line[0..prefix.len], prefix))
        {
            const trimmed_digits = std.mem.trim(u8, header_line[prefix.len..], " \t");
            return std.fmt.parseUnsigned(usize, trimmed_digits, 10) catch null;
        }
    }
    return null;
}

/// Executes `lsp_server.runServerStream` over `inbound_bytes` and extracts all outbound JSON bodies.
fn executeLspTranscript(
    allocator: std.mem.Allocator,
    io: std.Io,
    inbound_bytes: []const u8,
    log_writer: ?*std.Io.Writer,
    options: LspServerOptions,
) !LspTranscriptOutcome {
    var fixed_reader = std.Io.Reader.fixed(inbound_bytes);
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();

    const exit_status = try lsp_server.runServerStream(
        allocator,
        io,
        null,
        &fixed_reader,
        &out_alloc.writer,
        log_writer,
        options,
    );

    const raw_copy = try allocator.dupe(u8, out_alloc.written());
    errdefer allocator.free(raw_copy);

    var frame_list: std.ArrayListUnmanaged([]const u8) = .empty;
    errdefer frame_list.deinit(allocator);

    var cursor: usize = 0;
    while (cursor < raw_copy.len) {
        const sep_pos = std.mem.indexOfPos(u8, raw_copy, cursor, "\r\n\r\n") orelse break;
        const body_len = extractFrameContentLength(raw_copy[cursor..sep_pos]) orelse break;
        const body_start = sep_pos + 4;
        if (body_start + body_len > raw_copy.len) break;
        try frame_list.append(allocator, raw_copy[body_start .. body_start + body_len]);
        cursor = body_start + body_len;
    }

    return .{
        .exit_code = exit_status,
        .raw_wire = raw_copy,
        .frames = try frame_list.toOwnedSlice(allocator),
    };
}

/// Finds the first outbound JSON frame containing `id_fragment`, or `null` if absent.
fn findFrameByIdFragment(frames: []const []const u8, id_fragment: []const u8) ?[]const u8 {
    for (frames) |frame_json| {
        if (std.mem.indexOf(u8, frame_json, id_fragment) != null) return frame_json;
    }
    return null;
}

/// Extracts the string value following `"resultId":"` inside `frame_json`.
fn extractResultIdSlice(frame_json: []const u8) ?[]const u8 {
    const marker = "\"resultId\":\"";
    const marker_pos = std.mem.indexOf(u8, frame_json, marker) orelse return null;
    const val_start = marker_pos + marker.len;
    const val_end = std.mem.indexOfScalarPos(u8, frame_json, val_start, '"') orelse return null;
    return frame_json[val_start..val_end];
}

/// Extracts a flat `u32` array following `field_marker` (e.g., `"\"data\":["`) in `frame_json`.
fn extractJsonU32Array(
    allocator: std.mem.Allocator,
    frame_json: []const u8,
    field_marker: []const u8,
) ![]u32 {
    const start_pos = (std.mem.indexOf(u8, frame_json, field_marker) orelse return error.MissingField) +
        field_marker.len;
    const end_pos = std.mem.indexOfScalarPos(u8, frame_json, start_pos, ']') orelse return error.UnterminatedArray;
    const body_slice = std.mem.trim(u8, frame_json[start_pos..end_pos], " \t\r\n");
    if (body_slice.len == 0) return allocator.alloc(u32, 0);

    var values: std.ArrayListUnmanaged(u32) = .empty;
    errdefer values.deinit(allocator);
    var item_iter = std.mem.splitScalar(u8, body_slice, ',');
    while (item_iter.next()) |num_str| {
        const clean_digits = std.mem.trim(u8, num_str, " \t\r\n");
        try values.append(allocator, try std.fmt.parseUnsigned(u32, clean_digits, 10));
    }
    return values.toOwnedSlice(allocator);
}

/// Extracts the first `SemanticTokensEdit` (`start`, `deleteCount`, `data`) from a delta response frame.
fn extractFirstSemanticDeltaEdit(
    allocator: std.mem.Allocator,
    delta_json: []const u8,
) !DecodedSemanticEdit {
    const edits_pos = std.mem.indexOf(u8, delta_json, "\"edits\":[{") orelse return error.MissingEdits;
    const sub_slice = delta_json[edits_pos..];

    const start_marker = "\"start\":";
    const start_val_off = (std.mem.indexOf(u8, sub_slice, start_marker) orelse return error.MissingStart) +
        start_marker.len;
    const start_comma = std.mem.indexOfScalarPos(u8, sub_slice, start_val_off, ',') orelse return error.MalformedEdit;

    const del_marker = "\"deleteCount\":";
    const del_val_off = (std.mem.indexOf(u8, sub_slice, del_marker) orelse return error.MissingDeleteCount) +
        del_marker.len;
    const del_comma = std.mem.indexOfScalarPos(u8, sub_slice, del_val_off, ',') orelse return error.MalformedEdit;

    return .{
        .start = try std.fmt.parseUnsigned(usize, sub_slice[start_val_off..start_comma], 10),
        .delete_count = try std.fmt.parseUnsigned(usize, sub_slice[del_val_off..del_comma], 10),
        .replacement = try extractJsonU32Array(allocator, sub_slice[del_comma..], "\"data\":["),
    };
}

// ----------------- Workspace Fixture Helpers ------------------

/// Creates an isolated `.zig-cache/tmp/phase10_lsp_<label>_<seq>` directory and returns its relative path.
fn createTempWorkspaceDir(allocator: std.mem.Allocator, io: std.Io, label: []const u8) ![]u8 {
    const rel_dir = try std.fmt.allocPrint(
        allocator,
        ".zig-cache/tmp/phase10_lsp_{s}_{d}",
        .{ label, next_workspace_seq.fetchAdd(1, .monotonic) },
    );
    errdefer allocator.free(rel_dir);
    std.Io.Dir.cwd().deleteTree(io, rel_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, rel_dir);
    return rel_dir;
}

/// Writes `file_bytes` to `<workspace_dir>/<rel_path>`, creating parent directories automatically.
fn writeWorkspaceFile(
    allocator: std.mem.Allocator,
    io: std.Io,
    workspace_dir: []const u8,
    rel_path: []const u8,
    file_bytes: []const u8,
) !void {
    const full_path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ workspace_dir, rel_path });
    defer allocator.free(full_path);
    if (std.fs.path.dirname(full_path)) |parent_dir| {
        try std.Io.Dir.cwd().createDirPath(io, parent_dir);
    }
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = full_path,
        .data = file_bytes,
    });
}

/// Resolves an existing disk path to a normalized canonical `file://` URI suitable for LSP requests.
fn resolvePathToFileUri(allocator: std.mem.Allocator, io: std.Io, disk_path: []const u8) ![]u8 {
    const real_os_path = try std.Io.Dir.cwd().realPathFileAlloc(io, disk_path, allocator);
    defer allocator.free(real_os_path);

    var norm_buf = try allocator.alloc(u8, real_os_path.len);
    defer allocator.free(norm_buf);
    var i: usize = 0;
    while (i < real_os_path.len) : (i += 1) {
        norm_buf[i] = if (real_os_path[i] == '\\') '/' else real_os_path[i];
    }
    if (norm_buf.len >= 2 and std.ascii.isAlphabetic(norm_buf[0]) and norm_buf[1] == ':') {
        norm_buf[0] = std.ascii.toLower(norm_buf[0]);
        return std.fmt.allocPrint(allocator, "file:///{s}", .{norm_buf});
    }
    if (norm_buf.len > 0 and norm_buf[0] == '/') {
        return std.fmt.allocPrint(allocator, "file://{s}", .{norm_buf});
    }
    return std.fmt.allocPrint(allocator, "file:///{s}", .{norm_buf});
}

// ---------------------------------------- MAIN -----------------------------------------

// ----------------- LSP 3.17 End-to-End Tests ------------------

test "test_lsp_lifecycle_utf16_vs_utf8_encoding_and_surrogate_positions" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Sending `exit` without a preceding `shutdown` must return non-zero exit code `1`:
    {
        var ungraceful_in: std.ArrayListUnmanaged(u8) = .empty;
        defer ungraceful_in.deinit(allocator);
        try appendLspFrame(
            allocator,
            &ungraceful_in,
            "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}",
        );
        var ungraceful_out = try executeLspTranscript(allocator, io, ungraceful_in.items, null, .{});
        defer ungraceful_out.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 1), ungraceful_out.exit_code);
    }

    // [2] Verify pre-init `-32002`, default `utf-16` vs negotiated `utf-8`, and post-shutdown `-32600`;
    // `"𐍈"` (`U+10348`) + `"𝐀"` (`U+1D400`) on line 2 = 8 UTF-8 bytes vs 4 UTF-16 code units (`+4` delta):
    for ([_]bool{ false, true }) |is_utf8_mode| {
        var inbound: std.ArrayListUnmanaged(u8) = .empty;
        defer inbound.deinit(allocator);

        // Pre-init notification is ignored silently; pre-init request `#10` must return `-32002`:
        try appendLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}",
        );
        try appendLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"textDocument/hover\",\"params\":{}}",
        );

        // `initialize` (`#1`); omit `positionEncodings` for default `utf-16`, or negotiate `utf-8`:
        const init_json = if (is_utf8_mode)
            "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
                "\"general\":{\"positionEncodings\":[\"utf-8\",\"utf-16\"]},\"textDocument\":{\"diagnostic\":{}}}}}"
        else
            "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
                "\"textDocument\":{\"diagnostic\":{}}}}}";
        try appendLspFrame(allocator, &inbound, init_json);
        try appendLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}");
        try appendLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"method\":\"$/setTrace\",\"params\":{\"value\":\"messages\"}}",
        );

        // Duplicate `initialize` (`#11`) must be rejected with `-32600` (`InvalidRequest`):
        try appendLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"initialize\",\"params\":{\"capabilities\":{}}}",
        );

        const astral_uri = "file:///D%3A/virt/astral_probe.cx";
        const astral_src =
            "pub fn id_fn(val_in: i32) -> i32 { return val_in; }\n" ++
            "pub fn astral_probe() -> i32 {\n" ++
            "    let glyph_pair = \"𐍈𝐀\"; let target_num: i32 = 100; let out_v = id_fn(target_num);\n" ++
            "    let _ = glyph_pair;\n" ++
            "    return out_v;\n" ++
            "}\n";
        try appendDidOpenFrame(allocator, &inbound, astral_uri, 1, astral_src);

        // Hover on `id_fn` call (`72..77` in UTF-8 vs `68..73` in UTF-16 on line 2):
        const hover_col: u32 = if (is_utf8_mode) 74 else 70;
        const hover_req = try std.fmt.allocPrint(
            allocator,
            "{{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":{{" ++
                "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":2,\"character\":{d}}}}}}}",
            .{ astral_uri, hover_col },
        );
        defer allocator.free(hover_req);
        try appendLspFrame(allocator, &inbound, hover_req);

        // `didChange` replacing `100` (`55..58` in UTF-8 vs `51..54` in UTF-16 on line 2) with `"\\uD800\\uDF48"` (`"𐍈"` -> `E0401`):
        const lit_start_col: u32 = if (is_utf8_mode) 55 else 51;
        const change_req = try std.fmt.allocPrint(
            allocator,
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{" ++
                "\"textDocument\":{{\"uri\":\"{s}\",\"version\":2}}," ++
                "\"contentChanges\":[{{\"range\":{{\"start\":{{\"line\":2,\"character\":{d}}}," ++
                "\"end\":{{\"line\":2,\"character\":{d}}}}},\"text\":\"\\\"\\uD800\\uDF48\\\"\"}}]}}}}",
            .{ astral_uri, lit_start_col, lit_start_col + 3 },
        );
        defer allocator.free(change_req);
        try appendLspFrame(allocator, &inbound, change_req);

        // Pull `textDocument/diagnostic` (`#3`) to verify `E0401` column span after `"𐍈𝐀"`:
        try appendLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/diagnostic\",\"params\":" ++
                "{\"textDocument\":{\"uri\":\"file:///D%3A/virt/astral_probe.cx\"}}}",
        );

        // `shutdown` (`#4`), post-shutdown request (`#5` -> `-32600`), and `exit` (`0`):
        try appendLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"shutdown\",\"params\":null}");
        try appendLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/hover\",\"params\":{}}",
        );
        try appendLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

        var trace_buf = std.Io.Writer.Allocating.init(allocator);
        defer trace_buf.deinit();
        var outcome = try executeLspTranscript(allocator, io, inbound.items, &trace_buf.writer, .{});
        defer outcome.deinit(allocator);

        try std.testing.expectEqual(@as(u8, 0), outcome.exit_code);
        try std.testing.expect(std.mem.indexOf(u8, trace_buf.written(), "[corex-lsp] ->") != null);

        try std.testing.expect(
            std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":10").?, "-32002") != null,
        );

        const expected_enc = if (is_utf8_mode) "\"positionEncoding\":\"utf-8\"" else "\"positionEncoding\":\"utf-16\"";
        try std.testing.expect(
            std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":1,").?, expected_enc) != null,
        );

        try std.testing.expect(
            std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":11").?, "-32600") != null,
        );

        const hover_resp = findFrameByIdFragment(outcome.frames, "\"id\":2").?;
        const expected_hover_range = if (is_utf8_mode)
            "\"range\":{\"start\":{\"line\":2,\"character\":72},\"end\":{\"line\":2,\"character\":77}}"
        else
            "\"range\":{\"start\":{\"line\":2,\"character\":68},\"end\":{\"line\":2,\"character\":73}}";
        try std.testing.expect(
            std.mem.indexOf(u8, hover_resp, "pub fn id_fn(val_in: i32) -> i32") != null,
        );
        try std.testing.expect(std.mem.indexOf(u8, hover_resp, expected_hover_range) != null);

        const diag_resp = findFrameByIdFragment(outcome.frames, "\"id\":3").?;
        // `"𐍈"` literal (`"\"𐍈\""`) spans 6 UTF-8 bytes (`55..61`) vs 4 UTF-16 code units (`51..55`):
        const expected_diag_range = if (is_utf8_mode)
            "\"range\":{\"start\":{\"line\":2,\"character\":55},\"end\":{\"line\":2,\"character\":61}}"
        else
            "\"range\":{\"start\":{\"line\":2,\"character\":51},\"end\":{\"line\":2,\"character\":55}}";
        try std.testing.expect(std.mem.indexOf(u8, diag_resp, "\"code\":\"E0401\"") != null);
        try std.testing.expect(std.mem.indexOf(u8, diag_resp, expected_diag_range) != null);

        try std.testing.expect(
            std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":4").?, "\"result\":null") != null,
        );
        try std.testing.expect(
            std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":5").?, "-32600") != null,
        );
    }
}

test "test_lsp_did_change_coalescing_cancellation_and_diagnostics" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const diag_uri = "file:///D%3A/virt/coalesce_diag.cx";
    const initial_cx =
        "@linear\n" ++
        "pub struct LeaseHandle {\n" ++
        "    pub id_num: i32,\n" ++
        "}\n" ++
        "pub fn consume_lease(lease: own LeaseHandle) -> i32 {\n" ++
        "    let LeaseHandle { id_num } = lease;\n" ++
        "    return id_num;\n" ++
        "}\n" ++
        "@deprecated(since: \"0.1.0\", reason: \"use modern_inc\", upgrade: \"modern_inc($0)\")\n" ++
        "pub fn legacy_inc(val: i32) -> i32 {\n" ++
        "    return val + 1;\n" ++
        "}\n" ++
        "pub fn modern_inc(val: i32) -> i32 {\n" ++
        "    return val + 2;\n" ++
        "}\n" ++
        "pub fn trigger_all(lease: own LeaseHandle) -> i32 {\n" ++
        "    let unused_local = 10;\n" ++
        "    let first_use = consume_lease(own lease);\n" ++
        "    let second_use = consume_lease(own lease);\n" ++
        "    return legacy_inc(first_use + second_use);\n" ++
        "}\n";

    // [1] Push diagnostics mode; verify 3 consecutive `didChange` frames coalesce into 1 `version: 4` push
    //     and pipelined `$/cancelRequest` pre-drain returns `-32800` for both int and string IDs:
    {
        var push_in: std.ArrayListUnmanaged(u8) = .empty;
        defer push_in.deinit(allocator);

        // Omit `capabilities.textDocument.diagnostic` so push `publishDiagnostics` is active:
        try appendLspFrame(
            allocator,
            &push_in,
            "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
                "\"general\":{\"positionEncodings\":[\"utf-8\"]}}}}",
        );
        try appendDidOpenFrame(allocator, &push_in, diag_uri, 1, initial_cx);

        // Three consecutive buffered `didChange` notifications (`v2` -> `v3` -> `v4`) on `unused_local` literal:
        try appendLspFrame(
            allocator,
            &push_in,
            "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{" ++
                "\"textDocument\":{\"uri\":\"file:///D%3A/virt/coalesce_diag.cx\",\"version\":2}," ++
                "\"contentChanges\":[{\"range\":{\"start\":{\"line\":16,\"character\":23}," ++
                "\"end\":{\"line\":16,\"character\":25}},\"text\":\"20\"}]}}",
        );
        try appendLspFrame(
            allocator,
            &push_in,
            "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{" ++
                "\"textDocument\":{\"uri\":\"file:///D%3A/virt/coalesce_diag.cx\",\"version\":3}," ++
                "\"contentChanges\":[{\"range\":{\"start\":{\"line\":16,\"character\":23}," ++
                "\"end\":{\"line\":16,\"character\":25}},\"text\":\"30\"}]}}",
        );
        try appendLspFrame(
            allocator,
            &push_in,
            "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{" ++
                "\"textDocument\":{\"uri\":\"file:///D%3A/virt/coalesce_diag.cx\",\"version\":4}," ++
                "\"contentChanges\":[{\"range\":{\"start\":{\"line\":16,\"character\":23}," ++
                "\"end\":{\"line\":16,\"character\":25}},\"text\":\"45\"}]}}",
        );

        // Pipelined requests `#51` and `"cancel-str-id"` immediately followed by `$/cancelRequest`:
        try appendLspFrame(
            allocator,
            &push_in,
            "{\"jsonrpc\":\"2.0\",\"id\":51,\"method\":\"workspace/symbol\",\"params\":{\"query\":\"lease\"}}",
        );
        try appendLspFrame(
            allocator,
            &push_in,
            "{\"jsonrpc\":\"2.0\",\"id\":\"cancel-str-id\",\"method\":\"textDocument/documentSymbol\"," ++
                "\"params\":{\"textDocument\":{\"uri\":\"file:///D%3A/virt/coalesce_diag.cx\"}}}",
        );
        try appendLspFrame(
            allocator,
            &push_in,
            "{\"jsonrpc\":\"2.0\",\"method\":\"$/cancelRequest\",\"params\":{\"id\":51}}",
        );
        try appendLspFrame(
            allocator,
            &push_in,
            "{\"jsonrpc\":\"2.0\",\"method\":\"$/cancelRequest\",\"params\":{\"id\":\"cancel-str-id\"}}",
        );
        try appendLspFrame(allocator, &push_in, "{\"jsonrpc\":\"2.0\",\"id\":99,\"method\":\"shutdown\",\"params\":null}");
        try appendLspFrame(allocator, &push_in, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

        var push_out = try executeLspTranscript(allocator, io, push_in.items, null, .{});
        defer push_out.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 0), push_out.exit_code);

        var has_push_v1 = false;
        var has_push_v2_or_v3 = false;
        var push_v4_frame: ?[]const u8 = null;
        for (push_out.frames) |frame_json| {
            if (std.mem.indexOf(u8, frame_json, "\"method\":\"textDocument/publishDiagnostics\"") == null) continue;
            if (std.mem.indexOf(u8, frame_json, "\"version\":1") != null) has_push_v1 = true;
            if (std.mem.indexOf(u8, frame_json, "\"version\":2") != null or
                std.mem.indexOf(u8, frame_json, "\"version\":3") != null)
            {
                has_push_v2_or_v3 = true;
            }
            if (std.mem.indexOf(u8, frame_json, "\"version\":4") != null) push_v4_frame = frame_json;
        }
        try std.testing.expect(has_push_v1);
        try std.testing.expect(!has_push_v2_or_v3);
        try std.testing.expect(push_v4_frame != null);

        // Verify `W0402` (`tags:[1]`), `W0403` (`tags:[2]`), and `E0313` `relatedInformation` in push payload:
        try std.testing.expect(std.mem.indexOf(u8, push_v4_frame.?, "\"code\":\"W0402\"") != null);
        try std.testing.expect(std.mem.indexOf(u8, push_v4_frame.?, "\"tags\":[1]") != null);
        try std.testing.expect(std.mem.indexOf(u8, push_v4_frame.?, "\"code\":\"W0403\"") != null);
        try std.testing.expect(std.mem.indexOf(u8, push_v4_frame.?, "\"tags\":[2]") != null);
        try std.testing.expect(std.mem.indexOf(u8, push_v4_frame.?, "\"code\":\"E0313\"") != null);
        try std.testing.expect(std.mem.indexOf(u8, push_v4_frame.?, "\"relatedInformation\":[{") != null);

        try std.testing.expect(
            std.mem.indexOf(u8, findFrameByIdFragment(push_out.frames, "\"id\":51").?, "-32800") != null,
        );
        try std.testing.expect(
            std.mem.indexOf(
                u8,
                findFrameByIdFragment(push_out.frames, "\"id\":\"cancel-str-id\"").?,
                "-32800",
            ) != null,
        );
    }

    // [2] Pull `textDocument/diagnostic` mode; verify `full` report + `previousResultId` `"unchanged"` caching:
    {
        var pull_in: std.ArrayListUnmanaged(u8) = .empty;
        defer pull_in.deinit(allocator);

        try appendLspFrame(
            allocator,
            &pull_in,
            "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
                "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
        );
        try appendDidOpenFrame(allocator, &pull_in, diag_uri, 1, initial_cx);
        try appendLspFrame(
            allocator,
            &pull_in,
            "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/diagnostic\",\"params\":{" ++
                "\"textDocument\":{\"uri\":\"file:///D%3A/virt/coalesce_diag.cx\"}}}",
        );
        try appendLspFrame(allocator, &pull_in, "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"shutdown\",\"params\":null}");
        try appendLspFrame(allocator, &pull_in, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

        var first_pull_out = try executeLspTranscript(allocator, io, pull_in.items, null, .{});
        defer first_pull_out.deinit(allocator);

        for (first_pull_out.frames) |frame_json| {
            try std.testing.expect(
                std.mem.indexOf(u8, frame_json, "\"method\":\"textDocument/publishDiagnostics\"") == null,
            );
        }

        const full_diag = findFrameByIdFragment(first_pull_out.frames, "\"id\":2").?;
        try std.testing.expect(std.mem.indexOf(u8, full_diag, "\"kind\":\"full\"") != null);
        try std.testing.expect(std.mem.indexOf(u8, full_diag, "\"code\":\"W0402\"") != null);
        try std.testing.expect(std.mem.indexOf(u8, full_diag, "\"tags\":[1]") != null);
        try std.testing.expect(std.mem.indexOf(u8, full_diag, "\"code\":\"W0403\"") != null);
        try std.testing.expect(std.mem.indexOf(u8, full_diag, "\"tags\":[2]") != null);
        try std.testing.expect(std.mem.indexOf(u8, full_diag, "\"relatedInformation\":[{") != null);

        const cached_res_id = extractResultIdSlice(full_diag).?;
        try std.testing.expectEqual(@as(usize, 32), cached_res_id.len);

        // Re-query with `previousResultId` in a fresh multi-step session to assert `"kind":"unchanged"`:
        var unchanged_in: std.ArrayListUnmanaged(u8) = .empty;
        defer unchanged_in.deinit(allocator);
        try appendLspFrame(
            allocator,
            &unchanged_in,
            "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
                "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
        );
        try appendDidOpenFrame(allocator, &unchanged_in, diag_uri, 1, initial_cx);
        const re_pull_req = try std.fmt.allocPrint(
            allocator,
            "{{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/diagnostic\",\"params\":{{" ++
                "\"textDocument\":{{\"uri\":\"{s}\"}},\"previousResultId\":\"{s}\"}}}}",
            .{ diag_uri, cached_res_id },
        );
        defer allocator.free(re_pull_req);
        try appendLspFrame(allocator, &unchanged_in, re_pull_req);
        try appendLspFrame(
            allocator,
            &unchanged_in,
            "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"shutdown\",\"params\":null}",
        );
        try appendLspFrame(allocator, &unchanged_in, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

        var unchanged_out = try executeLspTranscript(allocator, io, unchanged_in.items, null, .{});
        defer unchanged_out.deinit(allocator);
        try std.testing.expect(
            std.mem.indexOf(
                u8,
                findFrameByIdFragment(unchanged_out.frames, "\"id\":2").?,
                "\"kind\":\"unchanged\"",
            ) != null,
        );
    }
}

test "test_lsp_semantic_tokens_delta_hover_and_dr17_contracts" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const sem_uri = "file:///D%3A/virt/sem_contracts.cx";
    const contracts_cx =
        "pub const HEADER_SEED: i32 = 7; /// trailing comment on previous constant\n" ++
        "/// Clamps telemetry sample within real-time bounds.\n" ++
        "@no_alloc\n" ++
        "@no_panic\n" ++
        "@max_stack(256)\n" ++
        "pub fn clamp_sample(sample: i32, ceiling: i32) -> i32 {\n" ++
        "    if sample > ceiling {\n" ++
        "        return ceiling;\n" ++
        "    }\n" ++
        "    return sample;\n" ++
        "}\n" ++
        "/// Reads raw MMIO status word.\n" ++
        "pub fn read_mmio_word(reg_addr: *i32) -> i32 {\n" ++
        "    return unsafe { reg_addr.* };\n" ++
        "}\n";

    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
            "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
    );
    try appendDidOpenFrame(allocator, &inbound, sem_uri, 1, contracts_cx);

    // `semanticTokens/full` (`#2`) -> `resultId` `"0000000000000001"`, then `full/delta` (`#3`) unchanged:
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/semanticTokens/full\"," ++
            "\"params\":{\"textDocument\":{\"uri\":\"file:///D%3A/virt/sem_contracts.cx\"}}}",
    );
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/semanticTokens/full/delta\"," ++
            "\"params\":{\"textDocument\":{\"uri\":\"file:///D%3A/virt/sem_contracts.cx\"}," ++
            "\"previousResultId\":\"0000000000000001\"}}",
    );

    // `semanticTokens/range` (`#4`) restricted to lines `5..10`:
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/semanticTokens/range\"," ++
            "\"params\":{\"textDocument\":{\"uri\":\"file:///D%3A/virt/sem_contracts.cx\"}," ++
            "\"range\":{\"start\":{\"line\":5,\"character\":0},\"end\":{\"line\":10,\"character\":2}}}}",
    );

    // Mutate `7` -> `4096` on line 0 (`version: 2`), then query `full/delta` (`#5` against `"0000000000000002"`) and `full` (`#6`):
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///D%3A/virt/sem_contracts.cx\",\"version\":2}," ++
            "\"contentChanges\":[{\"range\":{\"start\":{\"line\":0,\"character\":29}," ++
            "\"end\":{\"line\":0,\"character\":30}},\"text\":\"4096\"}]}}",
    );
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/semanticTokens/full/delta\"," ++
            "\"params\":{\"textDocument\":{\"uri\":\"file:///D%3A/virt/sem_contracts.cx\"}," ++
            "\"previousResultId\":\"0000000000000002\"}}",
    );
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"textDocument/semanticTokens/full\"," ++
            "\"params\":{\"textDocument\":{\"uri\":\"file:///D%3A/virt/sem_contracts.cx\"}}}",
    );

    // Hover on `@no_alloc @no_panic @max_stack(256)` `clamp_sample` (`#7`, line 5, col 8) and `read_mmio_word` (`#8`, line 12, col 8):
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///D%3A/virt/sem_contracts.cx\"},\"position\":{\"line\":5,\"character\":8}}}",
    );
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///D%3A/virt/sem_contracts.cx\"},\"position\":{\"line\":12,\"character\":8}}}",
    );
    try appendLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"shutdown\",\"params\":null}");
    try appendLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var outcome = try executeLspTranscript(allocator, io, inbound.items, null, .{});
    defer outcome.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), outcome.exit_code);

    // [1] Verify 5-int full stream, empty unchanged delta, and viewport range clipping:
    const full_v1_json = findFrameByIdFragment(outcome.frames, "\"id\":2").?;
    const full_v1_data = try extractJsonU32Array(allocator, full_v1_json, "\"data\":[");
    defer allocator.free(full_v1_data);
    try std.testing.expect(full_v1_data.len >= 25);
    try std.testing.expectEqual(@as(usize, 0), full_v1_data.len % 5);

    try std.testing.expect(
        std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":3").?, "\"edits\":[]") != null,
    );

    const range_json = findFrameByIdFragment(outcome.frames, "\"id\":4").?;
    const range_data = try extractJsonU32Array(allocator, range_json, "\"data\":[");
    defer allocator.free(range_data);
    try std.testing.expect(range_data.len > 0 and range_data.len < full_v1_data.len);
    try std.testing.expectEqual(@as(usize, 0), range_data.len % 5);

    // [2] Apply `semanticTokens/full/delta` edit to `full_v1_data` and assert exact equality with `full_v2_data`:
    const edit_delta_json = findFrameByIdFragment(outcome.frames, "\"id\":5").?;
    var sem_edit = try extractFirstSemanticDeltaEdit(allocator, edit_delta_json);
    defer sem_edit.deinit(allocator);

    const full_v2_json = findFrameByIdFragment(outcome.frames, "\"id\":6").?;
    const full_v2_data = try extractJsonU32Array(allocator, full_v2_json, "\"data\":[");
    defer allocator.free(full_v2_data);

    var patched_tokens: std.ArrayListUnmanaged(u32) = .empty;
    defer patched_tokens.deinit(allocator);
    try patched_tokens.appendSlice(allocator, full_v1_data[0..sem_edit.start]);
    try patched_tokens.appendSlice(allocator, sem_edit.replacement);
    try patched_tokens.appendSlice(allocator, full_v1_data[sem_edit.start + sem_edit.delete_count ..]);
    try std.testing.expectEqualSlices(u32, full_v2_data, patched_tokens.items);

    // [3] Verify `DR-17` contract verification, stack budget, pure vs `[unsafe_op]` capabilities, and `///` docs:
    const clamp_hover = findFrameByIdFragment(outcome.frames, "\"id\":7").?;
    try std.testing.expect(
        std.mem.indexOf(u8, clamp_hover, "pub fn clamp_sample(sample: i32, ceiling: i32) -> i32") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, clamp_hover, "✓ @no_alloc (verified)") != null);
    try std.testing.expect(std.mem.indexOf(u8, clamp_hover, "✓ @no_panic (verified)") != null);
    try std.testing.expect(std.mem.indexOf(u8, clamp_hover, "• capabilities: none (pure)") != null);
    try std.testing.expect(std.mem.indexOf(u8, clamp_hover, "(budget: 256 B)") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, clamp_hover, "Clamps telemetry sample within real-time bounds.") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, clamp_hover, "trailing comment on previous constant") == null,
    );

    const mmio_hover = findFrameByIdFragment(outcome.frames, "\"id\":8").?;
    try std.testing.expect(
        std.mem.indexOf(u8, mmio_hover, "pub fn read_mmio_word(reg_addr: *i32) -> i32") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, mmio_hover, "• capabilities: [unsafe_op]") != null);
    try std.testing.expect(std.mem.indexOf(u8, mmio_hover, "Reads raw MMIO status word.") != null);
}

test "test_lsp_navigation_visibility_references_symbols_and_inlay_hints" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const ws_dir = try createTempWorkspaceDir(allocator, io, "nav_refs");
    defer {
        std.Io.Dir.cwd().deleteTree(io, ws_dir) catch {};
        allocator.free(ws_dir);
    }

    try writeWorkspaceFile(
        allocator,
        io,
        ws_dir,
        "corex.toml",
        "[package]\nname = \"lsp-nav-refs\"\nversion = \"0.1.0\"\nedition = \"2026\"\n",
    );

    const geom_cx =
        "pub struct Vec2 {\n" ++
        "    pub x_coord: i32,\n" ++
        "    pub y_coord: i32,\n" ++
        "    secret_tag: i32 = 0,\n" ++
        "}\n" ++
        "impl Vec2 {\n" ++
        "    pub fn length_sq(&self) -> i32 {\n" ++
        "        return self.x_coord * self.x_coord + self.y_coord * self.y_coord + self.secret_tag;\n" ++
        "    }\n" ++
        "}\n" ++
        "fn internal_bias(raw_v: i32) -> i32 {\n" ++
        "    return raw_v + 1;\n" ++
        "}\n" ++
        "@no_alloc\n" ++
        "pub fn make_vec2(px: i32, py: i32) -> Vec2 {\n" ++
        "    return Vec2 { x_coord: internal_bias(px), y_coord: py };\n" ++
        "}\n" ++
        "pub fn shift_vec2(target: &mut Vec2, delta_x: i32) {\n" ++
        "    target.x_coord = target.x_coord + delta_x;\n" ++
        "}\n";
    try writeWorkspaceFile(allocator, io, ws_dir, "src/geom.cx", geom_cx);

    const peer_cx =
        "fn internal_bias(other_v: i32) -> i32 {\n" ++
        "    return other_v - 1;\n" ++
        "}\n" ++
        "pub fn peer_metric() -> i32 {\n" ++
        "    return internal_bias(9);\n" ++
        "}\n";
    try writeWorkspaceFile(allocator, io, ws_dir, "src/peer.cx", peer_cx);

    const main_cx =
        "mod geom;\n" ++
        "mod peer;\n" ++
        "use geom.{Vec2, make_vec2, shift_vec2};\n" ++
        "pub fn run_demo() -> i32 {\n" ++
        "    var origin = make_vec2(3, 4);\n" ++
        "    shift_vec2(&mut origin, 5);\n" ++
        "    let norm_val = origin.length_sq();\n" ++
        "    return norm_val + peer.peer_metric();\n" ++
        "}\n";
    try writeWorkspaceFile(allocator, io, ws_dir, "src/main.cx", main_cx);

    const toml_path = try std.fmt.allocPrint(allocator, "{s}/corex.toml", .{ws_dir});
    defer allocator.free(toml_path);
    const toml_uri = try resolvePathToFileUri(allocator, io, toml_path);
    defer allocator.free(toml_uri);
    const ws_uri = toml_uri[0 .. toml_uri.len - "/corex.toml".len];

    const main_path = try std.fmt.allocPrint(allocator, "{s}/src/main.cx", .{ws_dir});
    defer allocator.free(main_path);
    const main_uri = try resolvePathToFileUri(allocator, io, main_path);
    defer allocator.free(main_uri);

    const geom_path = try std.fmt.allocPrint(allocator, "{s}/src/geom.cx", .{ws_dir});
    defer allocator.free(geom_path);
    const geom_uri = try resolvePathToFileUri(allocator, io, geom_path);
    defer allocator.free(geom_uri);

    const peer_path = try std.fmt.allocPrint(allocator, "{s}/src/peer.cx", .{ws_dir});
    defer allocator.free(peer_path);
    const peer_uri = try resolvePathToFileUri(allocator, io, peer_path);
    defer allocator.free(peer_uri);

    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    const init_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{{" ++
            "\"rootUri\":\"{s}\",\"capabilities\":{{\"general\":{{\"positionEncodings\":[\"utf-8\"]}}," ++
            "\"textDocument\":{{\"diagnostic\":{{}}}}}}}}}}",
        .{ws_uri},
    );
    defer allocator.free(init_req);
    try appendLspFrame(allocator, &inbound, init_req);
    try appendDidOpenFrame(allocator, &inbound, main_uri, 1, main_cx);
    try appendDidOpenFrame(allocator, &inbound, geom_uri, 1, geom_cx);

    // `#2` Cross-file `definition` on `make_vec2` call in `src/main.cx` (line 4, col 20 -> `src/geom.cx` line 14):
    const def_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/definition\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":4,\"character\":20}}}}}}",
        .{main_uri},
    );
    defer allocator.free(def_req);
    try appendLspFrame(allocator, &inbound, def_req);

    // `#3` Cross-file `typeDefinition` on `origin` in `src/main.cx` (line 4, col 9 -> `pub struct Vec2` in `src/geom.cx`):
    const typedef_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/typeDefinition\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":4,\"character\":9}}}}}}",
        .{main_uri},
    );
    defer allocator.free(typedef_req);
    try appendLspFrame(allocator, &inbound, typedef_req);

    // `#4` Public `references` on `make_vec2` in `src/geom.cx` (line 14, col 9 -> hits in both `geom.cx` & `main.cx`):
    const pub_refs_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/references\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":14,\"character\":9}}," ++
            "\"context\":{{\"includeDeclaration\":true}}}}}}",
        .{geom_uri},
    );
    defer allocator.free(pub_refs_req);
    try appendLspFrame(allocator, &inbound, pub_refs_req);

    // `#5` Private `Visibility`-pruned `references` on `internal_bias` in `src/geom.cx` (line 10, col 5 -> excludes `peer.cx`):
    const priv_refs_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/references\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":10,\"character\":5}}," ++
            "\"context\":{{\"includeDeclaration\":true}}}}}}",
        .{geom_uri},
    );
    defer allocator.free(priv_refs_req);
    try appendLspFrame(allocator, &inbound, priv_refs_req);

    // `#6` Intra-file `documentHighlight` on `origin` in `src/main.cx` (line 4, col 9 -> Write `3` & Read `2`):
    const hl_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"textDocument/documentHighlight\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":4,\"character\":9}}}}}}",
        .{main_uri},
    );
    defer allocator.free(hl_req);
    try appendLspFrame(allocator, &inbound, hl_req);

    // `#7` Hierarchical `documentSymbol` on `src/geom.cx` & `#8` `workspace/symbol` (`"make_vec"`):
    const doc_sym_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/documentSymbol\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}}}}}}",
        .{geom_uri},
    );
    defer allocator.free(doc_sym_req);
    try appendLspFrame(allocator, &inbound, doc_sym_req);
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"workspace/symbol\",\"params\":{\"query\":\"make_vec\"}}",
    );

    // `#9` `signatureHelp` inside `shift_vec2(&mut origin, 5)` at arg 1 (line 5, col 28) & `#10` `inlayHint` on `main.cx`:
    const sig_help_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/signatureHelp\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":5,\"character\":28}}}}}}",
        .{main_uri},
    );
    defer allocator.free(sig_help_req);
    try appendLspFrame(allocator, &inbound, sig_help_req);

    const inlay_main_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"textDocument/inlayHint\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}}," ++
            "\"range\":{{\"start\":{{\"line\":0,\"character\":0}},\"end\":{{\"line\":9,\"character\":0}}}}}}}}",
        .{main_uri},
    );
    defer allocator.free(inlay_main_req);
    try appendLspFrame(allocator, &inbound, inlay_main_req);

    // `#11` Lexical scope `completion` at start of line 7 in `main.cx`, then `didChange` (`origin.`) + `#12` dot `completion`:
    const scope_comp_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"textDocument/completion\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":7,\"character\":4}}}}}}",
        .{main_uri},
    );
    defer allocator.free(scope_comp_req);
    try appendLspFrame(allocator, &inbound, scope_comp_req);

    const dot_change_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\",\"version\":2}}," ++
            "\"contentChanges\":[{{\"range\":{{\"start\":{{\"line\":7,\"character\":0}}," ++
            "\"end\":{{\"line\":7,\"character\":0}}}},\"text\":\"    let dot_probe = origin.\\n\"}}]}}}}",
        .{main_uri},
    );
    defer allocator.free(dot_change_req);
    try appendLspFrame(allocator, &inbound, dot_change_req);

    const dot_comp_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":12,\"method\":\"textDocument/completion\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":7,\"character\":27}}}}}}",
        .{main_uri},
    );
    defer allocator.free(dot_comp_req);
    try appendLspFrame(allocator, &inbound, dot_comp_req);

    try appendLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":13,\"method\":\"shutdown\",\"params\":null}");
    try appendLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var outcome = try executeLspTranscript(allocator, io, inbound.items, null, .{});
    defer outcome.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), outcome.exit_code);

    const def_resp = findFrameByIdFragment(outcome.frames, "\"id\":2").?;
    try std.testing.expect(std.mem.indexOf(u8, def_resp, geom_uri) != null);
    try std.testing.expect(std.mem.indexOf(u8, def_resp, "\"line\":14") != null);

    const typedef_resp = findFrameByIdFragment(outcome.frames, "\"id\":3").?;
    try std.testing.expect(std.mem.indexOf(u8, typedef_resp, geom_uri) != null);
    try std.testing.expect(std.mem.indexOf(u8, typedef_resp, "\"line\":0") != null);

    const pub_refs_resp = findFrameByIdFragment(outcome.frames, "\"id\":4").?;
    try std.testing.expect(std.mem.indexOf(u8, pub_refs_resp, geom_uri) != null);
    try std.testing.expect(std.mem.indexOf(u8, pub_refs_resp, main_uri) != null);

    const priv_refs_resp = findFrameByIdFragment(outcome.frames, "\"id\":5").?;
    try std.testing.expect(std.mem.indexOf(u8, priv_refs_resp, geom_uri) != null);
    try std.testing.expect(std.mem.indexOf(u8, priv_refs_resp, peer_uri) == null);

    const hl_resp = findFrameByIdFragment(outcome.frames, "\"id\":6").?;
    try std.testing.expect(std.mem.indexOf(u8, hl_resp, "\"kind\":3") != null);
    try std.testing.expect(std.mem.indexOf(u8, hl_resp, "\"kind\":2") != null);

    const doc_sym_resp = findFrameByIdFragment(outcome.frames, "\"id\":7").?;
    try std.testing.expect(std.mem.indexOf(u8, doc_sym_resp, "\"name\":\"Vec2\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, doc_sym_resp, "\"children\":[{") != null);
    try std.testing.expect(std.mem.indexOf(u8, doc_sym_resp, "\"name\":\"x_coord\"") != null);

    try std.testing.expect(
        std.mem.indexOf(
            u8,
            findFrameByIdFragment(outcome.frames, "\"id\":8").?,
            "\"name\":\"make_vec2\"",
        ) != null,
    );

    const sig_resp = findFrameByIdFragment(outcome.frames, "\"id\":9").?;
    try std.testing.expect(
        std.mem.indexOf(u8, sig_resp, "pub fn shift_vec2(target: &mut Vec2, delta_x: i32)") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, sig_resp, "\"activeParameter\":1") != null);

    const inlay_resp = findFrameByIdFragment(outcome.frames, "\"id\":10").?;
    try std.testing.expect(std.mem.indexOf(u8, inlay_resp, "\": Vec2\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, inlay_resp, "\": i32\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, inlay_resp, "\"px:\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, inlay_resp, "\"target:\"") != null);

    const scope_comp_resp = findFrameByIdFragment(outcome.frames, "\"id\":11").?;
    try std.testing.expect(std.mem.indexOf(u8, scope_comp_resp, "\"label\":\"origin\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, scope_comp_resp, "\"label\":\"make_vec2\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, scope_comp_resp, "\"label\":\"cx\"") != null);

    const dot_comp_resp = findFrameByIdFragment(outcome.frames, "\"id\":12").?;
    try std.testing.expect(std.mem.indexOf(u8, dot_comp_resp, "\"label\":\"x_coord\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, dot_comp_resp, "\"label\":\"length_sq\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, dot_comp_resp, "\"label\":\"secret_tag\"") == null);
}

test "test_lsp_hygienic_rename_code_action_and_range_formatting" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const ws_dir = try createTempWorkspaceDir(allocator, io, "rename_fmt");
    defer {
        std.Io.Dir.cwd().deleteTree(io, ws_dir) catch {};
        allocator.free(ws_dir);
    }

    try writeWorkspaceFile(
        allocator,
        io,
        ws_dir,
        "corex.toml",
        "[package]\nname = \"lsp-rename-fmt\"\nversion = \"0.1.0\"\nedition = \"2026\"\n",
    );

    const math_ops_cx =
        "pub const SCALE_FACTOR: i32 = 4;\n" ++
        "pub struct PairBox {\n" ++
        "    pub left_v: i32,\n" ++
        "    pub right_v: i32,\n" ++
        "}\n" ++
        "pub fn compute_delta(base_v: i32, step_v: i32) -> i32 {\n" ++
        "    let inner_local = step_v * SCALE_FACTOR;\n" ++
        "    return base_v + inner_local;\n" ++
        "}\n";
    try writeWorkspaceFile(allocator, io, ws_dir, "src/math_ops.cx", math_ops_cx);

    const main_cx =
        "mod math_ops;\n" ++
        "use cx.mem.size_of_type;\n" ++
        "use math_ops.{PairBox, SCALE_FACTOR, compute_delta};\n" ++
        "@deprecated(since: \"0.2.0\", reason: \"use modern_double\", upgrade: \"modern_double($0)\")\n" ++
        "pub fn legacy_double(input_v: i32) -> i32 {\n" ++
        "    return input_v * 2;\n" ++
        "}\n" ++
        "pub fn modern_double(input_v: i32) -> i32 {\n" ++
        "    return input_v + input_v;\n" ++
        "}\n" ++
        "pub fn check_flag(flag: bool) -> bool {\n" ++
        "    if flag { return true; } else { return false; }\n" ++
        "}\n" ++
        "pub fn entry_calc() -> i32 {\n" ++
        "    let shadow_guard = 1;\n" ++
        "    let delta = compute_delta(10, 20);\n" ++
        "    let dep_val = legacy_double(delta);\n" ++
        "    let boxed = PairBox { left_v: dep_val, right_v: SCALE_FACTOR };\n" ++
        "    return boxed.left_v + boxed.right_v + shadow_guard + (size_of_type[i32]() as i32);\n" ++
        "}\n";
    try writeWorkspaceFile(allocator, io, ws_dir, "src/main.cx", main_cx);

    const toml_path = try std.fmt.allocPrint(allocator, "{s}/corex.toml", .{ws_dir});
    defer allocator.free(toml_path);
    const toml_uri = try resolvePathToFileUri(allocator, io, toml_path);
    defer allocator.free(toml_uri);
    const ws_uri = toml_uri[0 .. toml_uri.len - "/corex.toml".len];

    const main_path = try std.fmt.allocPrint(allocator, "{s}/src/main.cx", .{ws_dir});
    defer allocator.free(main_path);
    const main_uri = try resolvePathToFileUri(allocator, io, main_path);
    defer allocator.free(main_uri);

    const math_path = try std.fmt.allocPrint(allocator, "{s}/src/math_ops.cx", .{ws_dir});
    defer allocator.free(math_path);
    const math_uri = try resolvePathToFileUri(allocator, io, math_path);
    defer allocator.free(math_uri);

    const messy_uri = "file:///D%3A/virt/messy_fmt.cx";
    const messy_cx =
        "pub fn keep_messy( a_in:i32,b_in:i32 )->i32{return a_in+b_in;}\n\n" ++
        "pub fn format_target( c_in:i32,d_in:i32 )->i32{return c_in*d_in;}\n";

    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    const init_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{{" ++
            "\"rootUri\":\"{s}\",\"capabilities\":{{\"general\":{{\"positionEncodings\":[\"utf-8\"]}}," ++
            "\"textDocument\":{{\"diagnostic\":{{}}}}}}}}}}",
        .{ws_uri},
    );
    defer allocator.free(init_req);
    try appendLspFrame(allocator, &inbound, init_req);
    try appendDidOpenFrame(allocator, &inbound, main_uri, 1, main_cx);
    try appendDidOpenFrame(allocator, &inbound, math_uri, 1, math_ops_cx);
    try appendDidOpenFrame(allocator, &inbound, messy_uri, 1, messy_cx);

    // `#2` `prepareRename` & `#3` cross-file `rename` on `compute_delta` in `src/main.cx` (line 15, col 20 -> `compute_offset`):
    const prep_ok_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/prepareRename\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":15,\"character\":20}}}}}}",
        .{main_uri},
    );
    defer allocator.free(prep_ok_req);
    try appendLspFrame(allocator, &inbound, prep_ok_req);

    const rename_ok_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/rename\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":15,\"character\":20}}," ++
            "\"newName\":\"compute_offset\"}}}}",
        .{main_uri},
    );
    defer allocator.free(rename_ok_req);
    try appendLspFrame(allocator, &inbound, rename_ok_req);

    // `#4` Keyword (`"return"`) & `#5` `DR-03` casing (`"ComputeDelta"`) rejections (`-32602`):
    const kw_rej_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/rename\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":15,\"character\":20}}," ++
            "\"newName\":\"return\"}}}}",
        .{main_uri},
    );
    defer allocator.free(kw_rej_req);
    try appendLspFrame(allocator, &inbound, kw_rej_req);

    const case_rej_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/rename\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":15,\"character\":20}}," ++
            "\"newName\":\"ComputeDelta\"}}}}",
        .{main_uri},
    );
    defer allocator.free(case_rej_req);
    try appendLspFrame(allocator, &inbound, case_rej_req);

    // `#6` Cross-file shadowing collision (`compute_delta` -> `"shadow_guard"` bound in `entry_calc` -> `-32803`):
    const shadow_rej_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"textDocument/rename\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":15,\"character\":20}}," ++
            "\"newName\":\"shadow_guard\"}}}}",
        .{main_uri},
    );
    defer allocator.free(shadow_rej_req);
    try appendLspFrame(allocator, &inbound, shadow_rej_req);

    // `#7` `prepareRename` (`null`) & `#8` `rename` (`-32803`) on `.std_core` symbol `size_of_type` (line 18, col 60):
    const std_prep_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/prepareRename\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":18,\"character\":60}}}}}}",
        .{main_uri},
    );
    defer allocator.free(std_prep_req);
    try appendLspFrame(allocator, &inbound, std_prep_req);

    const std_ren_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"textDocument/rename\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":18,\"character\":60}}," ++
            "\"newName\":\"custom_size_of\"}}}}",
        .{main_uri},
    );
    defer allocator.free(std_ren_req);
    try appendLspFrame(allocator, &inbound, std_ren_req);

    // `#9` `codeAction` over `check_flag` (`W0202`) and `entry_calc` (`W0403` `@deprecated` upgrade):
    const code_act_req = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/codeAction\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}}," ++
            "\"range\":{{\"start\":{{\"line\":10,\"character\":0}},\"end\":{{\"line\":19,\"character\":0}}}}," ++
            "\"context\":{{\"diagnostics\":[]}}}}}}",
        .{main_uri},
    );
    defer allocator.free(code_act_req);
    try appendLspFrame(allocator, &inbound, code_act_req);

    // `#10` `rangeFormatting` (line 2 only) & `#11` whole-document `formatting` on `messy_fmt.cx`:
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"textDocument/rangeFormatting\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///D%3A/virt/messy_fmt.cx\"}," ++
            "\"range\":{\"start\":{\"line\":2,\"character\":0},\"end\":{\"line\":2,\"character\":60}}," ++
            "\"options\":{\"tabSize\":4,\"insertSpaces\":true}}}",
    );
    try appendLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"textDocument/formatting\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///D%3A/virt/messy_fmt.cx\"}," ++
            "\"options\":{\"tabSize\":4,\"insertSpaces\":true}}}",
    );

    try appendLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":12,\"method\":\"shutdown\",\"params\":null}");
    try appendLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var outcome = try executeLspTranscript(allocator, io, inbound.items, null, .{});
    defer outcome.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), outcome.exit_code);

    try std.testing.expect(
        std.mem.indexOf(
            u8,
            findFrameByIdFragment(outcome.frames, "\"id\":2").?,
            "\"placeholder\":\"compute_delta\"",
        ) != null,
    );

    const rename_ok_resp = findFrameByIdFragment(outcome.frames, "\"id\":3").?;
    try std.testing.expect(std.mem.indexOf(u8, rename_ok_resp, math_uri) != null);
    try std.testing.expect(std.mem.indexOf(u8, rename_ok_resp, main_uri) != null);
    try std.testing.expect(std.mem.indexOf(u8, rename_ok_resp, "\"newText\":\"compute_offset\"") != null);

    try std.testing.expect(
        std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":4").?, "-32602") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":5").?, "-32602") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":6").?, "-32803") != null,
    );

    try std.testing.expect(
        std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":7").?, "\"result\":null") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, findFrameByIdFragment(outcome.frames, "\"id\":8").?, "-32803") != null,
    );

    const code_act_resp = findFrameByIdFragment(outcome.frames, "\"id\":9").?;
    try std.testing.expect(std.mem.indexOf(u8, code_act_resp, "\"kind\":\"quickfix\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, code_act_resp, "\"code\":\"W0202\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, code_act_resp, "return flag;") != null);
    try std.testing.expect(std.mem.indexOf(u8, code_act_resp, "\"code\":\"W0403\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, code_act_resp, "modern_double(delta)") != null);

    const range_fmt_resp = findFrameByIdFragment(outcome.frames, "\"id\":10").?;
    try std.testing.expect(std.mem.indexOf(u8, range_fmt_resp, "\"start\":{\"line\":2,\"character\":21}") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, range_fmt_resp, "c_in: i32, d_in: i32) -> i32 {\\n    return c_in * d_in;\\n") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, range_fmt_resp, "keep_messy") == null);

    const full_fmt_resp = findFrameByIdFragment(outcome.frames, "\"id\":11").?;
    try std.testing.expect(std.mem.indexOf(u8, full_fmt_resp, "pub fn keep_messy(a_in: i32, b_in: i32) -> i32") != null);
    try std.testing.expect(std.mem.indexOf(u8, full_fmt_resp, "pub fn format_target(c_in: i32, d_in: i32) -> i32") != null);
}

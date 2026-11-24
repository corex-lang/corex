//! Phase 10 100,000-LOC Incremental LSP & Zero-Legacy Upgrade Benchmark Suite
//!
//! Pre-populates a realistic 100,000-LOC multi-module CoreX workspace (`250` `.cx` modules x `400`
//! LOC) inside a persistent `corex lsp` (`runServerStream`) session and benchmarks incremental
//! `didChange` + pull `diagnostic` (`< 10 ms` P99), `completion` + `hover` + `definition` +
//! `semanticTokens/full/delta` (`< 10 ms` P99), and 3-tier `upgrade_engine.upgradeSource` synergy.
//!
//! Executes `5` untimed warmup iterations and `100` measured iterations per workload, asserting both
//! `BenchHarness` table metrics and sorted 100-sample P99 (`samples[98] < 10 ms`) latency budgets.

const std = @import("std");
const corex = @import("corex");

const lsp_server = corex.lsp_server;
const upgrade_engine = corex.upgrade_engine;
const FileId = corex.FileId;
const StyleConfig = corex.StyleConfig;
const BenchCase = corex.bench_harness.BenchCase;
const BenchConfig = corex.bench_harness.BenchConfig;
const BenchResult = corex.bench_harness.BenchResult;

// ---------------------------------------- TYPES ----------------------------------------

/// Lock-free single-producer/single-consumer turn stream pipe feeding a persistent `runServerStream` thread.
const LspTurnPipe = struct {
    /// Backing allocator for `captured_resp_buf`.
    allocator: std.mem.Allocator,
    /// Borrowed `std.Io` handle driving futex `Event` wakeups.
    io: std.Io,
    /// Backing storage for `reader` (`64 KiB` holds an entire multi-request batch in one `stream` call).
    reader_storage: [64 * 1024]u8 = undefined,
    /// Backing storage for `writer` (`64 KiB` buffers outbound JSON-RPC frames prior to `flush`).
    writer_storage: [64 * 1024]u8 = undefined,
    /// Custom `std.Io.Reader` passed into `lsp_server.runServerStream`.
    reader: std.Io.Reader = undefined,
    /// Custom `std.Io.Writer` passed into `lsp_server.runServerStream`.
    writer: std.Io.Writer = undefined,
    /// Signaled by client once `staged_req_bytes` and `expected_resp_frames` are published.
    req_ready_event: std.Io.Event = .unset,
    /// Signaled by server `writer.flush` once `completed_resp_frames >= expected_resp_frames`.
    resp_ready_event: std.Io.Event = .unset,
    /// Inbound wire bytes staged by client for the upcoming turn.
    staged_req_bytes: []const u8 = &.{},
    /// Set by client with `exit` frame to close `reader` cleanly with `error.EndOfStream`.
    is_eof_staged: bool = false,
    /// Server-private view of the active turn's inbound wire slice.
    active_req_bytes: []const u8 = &.{},
    /// Server-private read offset within `active_req_bytes`.
    active_req_cursor: usize = 0,
    /// Server-private EOF latch set once `is_eof_staged` has been observed.
    is_eof_latched: bool = false,
    /// Number of complete outbound JSON-RPC frames awaited before waking client.
    expected_resp_frames: usize = 0,
    /// Number of complete outbound JSON-RPC frames observed in the current turn.
    completed_resp_frames: usize = 0,
    /// Byte offset of the next unparsed frame header inside `captured_resp_buf`.
    parsed_resp_offset: usize = 0,
    /// Accumulated outbound JSON-RPC wire bytes for the active turn.
    captured_resp_buf: std.ArrayListUnmanaged(u8) = .empty,

    /// Allocates and pins a heap-resident `LspTurnPipe` with bound `Reader` and `Writer` vtables.
    fn create(allocator: std.mem.Allocator, io: std.Io) !*LspTurnPipe {
        const pipe = try allocator.create(LspTurnPipe);
        errdefer allocator.destroy(pipe);
        pipe.* = .{
            .allocator = allocator,
            .io = io,
        };
        pipe.reader = .{
            .vtable = &PIPE_READER_VTABLE,
            .buffer = &pipe.reader_storage,
            .seek = 0,
            .end = 0,
        };
        pipe.writer = .{
            .vtable = &PIPE_WRITER_VTABLE,
            .buffer = &pipe.writer_storage,
            .end = 0,
        };
        try pipe.captured_resp_buf.ensureTotalCapacity(allocator, 64 * 1024);
        return pipe;
    }

    /// Releases `captured_resp_buf` and destroys the heap-allocated `LspTurnPipe`.
    fn destroy(self: *LspTurnPipe) void {
        const allocator = self.allocator;
        self.captured_resp_buf.deinit(allocator);
        allocator.destroy(self);
    }

    /// Publishes `req_wire_bytes` to the persistent `LspSession` and waits for `expected_frames` responses.
    fn submitTurnAndWait(
        self: *LspTurnPipe,
        req_wire_bytes: []const u8,
        expected_frames: usize,
    ) []const u8 {
        self.captured_resp_buf.clearRetainingCapacity();
        self.parsed_resp_offset = 0;
        self.completed_resp_frames = 0;
        self.expected_resp_frames = expected_frames;
        self.staged_req_bytes = req_wire_bytes;
        self.resp_ready_event.reset();
        self.req_ready_event.set(self.io);
        if (expected_frames > 0) {
            self.resp_ready_event.waitUncancelable(self.io);
        }
        return self.captured_resp_buf.items;
    }

    /// Sends final `exit` bytes followed by EOF so `runServerStream` terminates cleanly.
    fn submitFinalExitAndEof(self: *LspTurnPipe, exit_wire_bytes: []const u8) void {
        self.captured_resp_buf.clearRetainingCapacity();
        self.parsed_resp_offset = 0;
        self.completed_resp_frames = 0;
        self.expected_resp_frames = 0;
        self.staged_req_bytes = exit_wire_bytes;
        self.is_eof_staged = true;
        self.req_ready_event.set(self.io);
    }
};

/// Context passed into the persistent background `lsp_server.runServerStream` worker thread.
const ServerWorkerCtx = struct {
    /// Backing allocator shared with the persistent `LspSession`.
    allocator: std.mem.Allocator,
    /// `std.Io` capability handle for VFS reads and futex events.
    io: std.Io,
    /// Hermetic environment map providing `COREX_HOME`.
    env_map: *const std.process.Environ.Map,
    /// Bidirectional turn pipe linking benchmark cases to `LspSession`.
    pipe: *LspTurnPipe,
    /// Exit status returned by `runServerStream` upon `shutdown` + `exit`.
    exit_code: u8 = 255,
    /// Captured error if `runServerStream` fails unexpectedly.
    server_err: ?anyerror = null,
};

/// Prepared 100,000-LOC workspace, persistent `LspSession` worker, and P99 sample buffers.
const PreparedPhase10BenchState = struct {
    /// Borrowed `std.Io` handle from `main`.
    io: std.Io,
    /// Scratch directory `.zig-cache/phase10_bench_env` deleted on exit.
    scratch_dir: []u8,
    /// Hermetic `COREX_HOME` directory inside `scratch_dir`.
    corex_home_dir: []u8,
    /// Heap-pinned environment map passed to the persistent LSP worker thread.
    env_map: *std.process.Environ.Map,
    /// Heap-pinned turn pipe driving `lsp_server.runServerStream`.
    pipe: *LspTurnPipe,
    /// Heap-pinned worker context for the persistent LSP server thread.
    worker_ctx: *ServerWorkerCtx,
    /// Persistent OS thread running a single `LspSession` across all warmup and measured turns.
    server_thread: std.Thread,
    /// Canonical `file://` URI for `ws/src/mod_125.cx`.
    mod125_uri: []u8,
    /// Monotonically increasing document version sent in `textDocument/didChange`.
    next_doc_version: i64 = 2,
    /// Monotonically increasing JSON-RPC `id` counter.
    next_rpc_id: i64 = 10,
    /// Latest 16-hex-character `resultId` returned by `semanticTokens/full` or `full/delta`.
    latest_sem_result_id: [16]u8 = @splat('0'),
    /// Invocation counter for Case 1 (`0 .. BENCH_WARMUP_COUNT + BENCH_MEASURED_COUNT`).
    case1_call_count: usize = 0,
    /// Recorded nanosecond durations for the `100` measured iterations of Case 1.
    case1_samples_ns: [BENCH_MEASURED_COUNT]u64 = @splat(0),
    /// Invocation counter for Case 2 (`0 .. BENCH_WARMUP_COUNT + BENCH_MEASURED_COUNT`).
    case2_call_count: usize = 0,
    /// Recorded nanosecond durations for the `100` measured iterations of Case 2.
    case2_samples_ns: [BENCH_MEASURED_COUNT]u64 = @splat(0),

    /// Shuts down the persistent `LspSession`, joins `server_thread`, and deletes `scratch_dir`.
    fn deinit(self: *PreparedPhase10BenchState, allocator: std.mem.Allocator) void {
        var shutdown_buf: [256]u8 = undefined;
        const shutdown_frame = formatSingleLspFrame(
            &shutdown_buf,
            "{\"jsonrpc\":\"2.0\",\"id\":999999,\"method\":\"shutdown\",\"params\":null}",
        );
        _ = self.pipe.submitTurnAndWait(shutdown_frame, 1);

        var exit_buf: [256]u8 = undefined;
        const exit_frame = formatSingleLspFrame(
            &exit_buf,
            "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}",
        );
        self.pipe.submitFinalExitAndEof(exit_frame);
        self.server_thread.join();

        allocator.free(self.mod125_uri);
        allocator.destroy(self.worker_ctx);
        self.pipe.destroy();
        self.env_map.deinit();
        allocator.destroy(self.env_map);
        allocator.free(self.corex_home_dir);
        std.Io.Dir.cwd().deleteTree(self.io, self.scratch_dir) catch {};
        allocator.free(self.scratch_dir);
        self.* = undefined;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Untimed warmup iterations executed prior to each timed workload (`5`).
const BENCH_WARMUP_COUNT: u32 = 5;
/// Measured iterations per workload (`100`, `>= 30` per `.agents/skills/bench/SKILL.md` §3).
const BENCH_MEASURED_COUNT: u32 = 100;
/// Total `.cx` modules generated in the synthetic workspace (`root.cx` + `mod_001`..`mod_249` = `250`).
const WORKSPACE_MODULE_COUNT: usize = 250;
/// Exact newline-terminated line count in every generated `.cx` module (`25` items x `16` lines = `400`).
const LINES_PER_MODULE: usize = 400;
/// Exact total workspace line count (`250 * 400 = 100,000` LOC).
const EXPECTED_WORKSPACE_LOC: usize = WORKSPACE_MODULE_COUNT * LINES_PER_MODULE;
/// Hard P99 latency ceiling (`10 ms` = `10,000,000 ns`) for 100,000-LOC incremental LSP requests.
const MAX_LSP_P99_BUDGET_NS: u64 = 10_000_000;
/// Zero-based P99 index into `100` sorted ascending latency samples (`samples[98]`).
const P99_SAMPLE_INDEX: usize = 98;

/// Custom `std.Io.Reader.VTable` delivering one staged turn batch per `LspSession` cycle.
const PIPE_READER_VTABLE = std.Io.Reader.VTable{
    .stream = streamPipeReader,
};

/// Custom `std.Io.Writer.VTable` capturing outbound JSON-RPC frames and waking the benchmark caller.
const PIPE_WRITER_VTABLE = std.Io.Writer.VTable{
    .drain = drainPipeWriter,
    .flush = flushPipeWriter,
};

/// Representative multi-item legacy `DR-21`..`DR-24` `.cx` module for Case 3 (`upgradeSource`).
const LEGACY_SYNERGY_MODULE_CX: []const u8 =
    \\//! Legacy packet synergy module for 3-tier upgrade benchmarking.
    \\
    \\use std::io;
    \\use cx.ffi.c_void;
    \\
    \\@link_name("free_legacy")
    \\extern "c" fn free_legacy(ptr: *const c_void) -> unit;
    \\
    \\/// Packet wire scheduling tier.
    \\@repr(u8)
    \\pub enum PacketMode {
    \\    Fast = 0;
    \\    Safe = 1;
    \\}
    \\
    \\type HeaderFlags = bit_field u8 {
    \\    ready: bool | 1;
    \\    lane: u8 | 7;
    \\};
    \\
    \\@repr(C)
    \\@align(bytes = 16)
    \\@zero_pad
    \\pub struct WireHeader {
    \\    pub tag: u32;
    \\    pub flags: u32;
    \\}
    \\
    \\pub struct Envelope[T] {
    \\    pub payload: T;
    \\}
    \\
    \\impl[T] Envelope[T] {
    \\    pub fn wrap(val: T) -> Envelope[T] {
    \\        return Envelope[T] { payload: val };
    \\    }
    \\}
    \\
    \\/* Redundant private contract helper migrated by UR-24-00 & UR-24-05 */
    \\@inline
    \\@no_alloc
    \\@no_panic
    \\fn bias_step(cur_val: i32) -> i32 {
    \\    if cur_val > 0 { cur_val + 1 } else { 1 }
    \\}
    \\
    \\@noalloc
    \\pub fn transform_packet[T: Numeric](
    \\    ref item: T,
    \\    inout counter: i32,
    \\    set completed: bool,
    \\    maybe_opt: Option[i32],
    \\    nested_res: Result[i32, u32],
    \\    bytes_view: &[u8],
    \\    raw_slot: *i32,
    \\    is_active: bool,
    \\    bit_mask: u32,
    \\) -> usize {
    \\    let _keep_item = item;
    \\    let _keep_res = nested_res catch 0;
    \\    let mut local_acc = bias_step(counter);
    \\    let _escaped = "\{tag\}";
    \\    let _interp_note = "acc={local_acc}";
    \\    let _banner = """
    \\        packet {local_acc=}
    \\        """;
    \\    if local_acc > 0 && (local_acc == 1 || local_acc == 2) {
    \\        local_acc += 1;
    \\    }
    \\    let wrapped = Envelope.wrap[i32](7);
    \\    let fallback_v = maybe_opt.unwrap_or(0) + wrapped.payload + if is_active { 1 } else { 0 };
    \\    let _ptr_ro: *u8 = bytes_view.ptr;
    \\    let tail_slice = bytes_view[0 .. bytes_view.len - 2];
    \\    let deref_num = unsafe { *raw_slot };
    \\    if !is_active {
    \\        let inv_bits = !bit_mask;
    \\        completed = false;
    \\        return (inv_bits as usize) + (fallback_v as usize) + (deref_num as usize);
    \\    }
    \\    let .Some(mut unwrapped_v) = maybe_opt else {
    \\        completed = false;
    \\        return 0;
    \\    };
    \\    unwrapped_v += 1;
    \\    counter = unwrapped_v;
    \\    completed = unwrapped_v > 0;
    \\    return tail_slice.len;
    \\}
    \\
    \\@test
    \\pub fn test_transform_packet_smoke() -> unit {
    \\    var seed_val: i32 = 3;
    \\}
++ "\n";

/// Shared benchmark fixture initialized once in `main` and cleaned up on exit.
var shared_bench_state: ?PreparedPhase10BenchState = null;

// -------------------------------------- INTERNALS --------------------------------------

// -------------------- LSP Turn Stream Pipe --------------------

/// Streams staged client request bytes into `lsp_server.runServerStream`, blocking cleanly between turns.
fn streamPipeReader(
    reader: *std.Io.Reader,
    writer: *std.Io.Writer,
    limit: std.Io.Limit,
) std.Io.Reader.StreamError!usize {
    const pipe: *LspTurnPipe = @fieldParentPtr("reader", reader);
    while (pipe.active_req_cursor >= pipe.active_req_bytes.len) {
        if (pipe.is_eof_latched) return error.EndOfStream;
        pipe.req_ready_event.waitUncancelable(pipe.io);
        pipe.req_ready_event.reset();
        pipe.active_req_bytes = pipe.staged_req_bytes;
        pipe.active_req_cursor = 0;
        if (pipe.is_eof_staged) {
            pipe.is_eof_latched = true;
            if (pipe.active_req_bytes.len == 0) return error.EndOfStream;
        }
    }
    const rem_slice = pipe.active_req_bytes[pipe.active_req_cursor..];
    const max_len = if (limit.toInt()) |lim_n| @min(lim_n, rem_slice.len) else rem_slice.len;
    const written_len = try writer.write(rem_slice[0..max_len]);
    pipe.active_req_cursor += written_len;
    return written_len;
}

/// Appends buffered and vectored outbound JSON-RPC bytes into `pipe.captured_resp_buf`.
fn drainPipeWriter(
    writer: *std.Io.Writer,
    data: []const []const u8,
    splat: usize,
) std.Io.Writer.Error!usize {
    const pipe: *LspTurnPipe = @fieldParentPtr("writer", writer);
    if (writer.end > 0) {
        pipe.captured_resp_buf.appendSlice(pipe.allocator, writer.buffer[0..writer.end]) catch {
            return error.WriteFailed;
        };
        writer.end = 0;
    }
    var consumed_from_data: usize = 0;
    if (data.len > 1) {
        for (data[0 .. data.len - 1]) |slice_part| {
            pipe.captured_resp_buf.appendSlice(pipe.allocator, slice_part) catch return error.WriteFailed;
            consumed_from_data += slice_part.len;
        }
    }
    const tail_part = data[data.len - 1];
    var rep_idx: usize = 0;
    while (rep_idx < splat) : (rep_idx += 1) {
        pipe.captured_resp_buf.appendSlice(pipe.allocator, tail_part) catch return error.WriteFailed;
        consumed_from_data += tail_part.len;
    }
    return consumed_from_data;
}

/// Parses newly flushed `Content-Length` frames in $O(1)$ per frame and wakes the client once complete.
fn flushPipeWriter(writer: *std.Io.Writer) std.Io.Writer.Error!void {
    const pipe: *LspTurnPipe = @fieldParentPtr("writer", writer);
    if (writer.end > 0) {
        pipe.captured_resp_buf.appendSlice(pipe.allocator, writer.buffer[0..writer.end]) catch {
            return error.WriteFailed;
        };
        writer.end = 0;
    }

    const buf_items = pipe.captured_resp_buf.items;
    while (pipe.parsed_resp_offset < buf_items.len) {
        const sep_idx = std.mem.indexOfPos(
            u8,
            buf_items,
            pipe.parsed_resp_offset,
            "\r\n\r\n",
        ) orelse break;
        const header_slice = buf_items[pipe.parsed_resp_offset..sep_idx];
        const body_len = extractContentLengthFast(header_slice) orelse return error.WriteFailed;
        const frame_end = sep_idx + 4 + body_len;
        if (frame_end > buf_items.len) break;
        pipe.parsed_resp_offset = frame_end;
        pipe.completed_resp_frames += 1;
    }

    if (pipe.expected_resp_frames > 0 and pipe.completed_resp_frames >= pipe.expected_resp_frames) {
        pipe.expected_resp_frames = 0;
        pipe.resp_ready_event.set(pipe.io);
    }
}

/// Extracts `Content-Length: <N>` from an outbound LSP frame header slice.
fn extractContentLengthFast(header_bytes: []const u8) ?usize {
    const prefix = "Content-Length:";
    const start_pos = std.mem.indexOf(u8, header_bytes, prefix) orelse return null;
    const after_colon = std.mem.trim(u8, header_bytes[start_pos + prefix.len ..], " \t\r\n");
    const line_end = std.mem.indexOfAny(u8, after_colon, "\r\n") orelse after_colon.len;
    return std.fmt.parseUnsigned(usize, after_colon[0..line_end], 10) catch null;
}

/// Entrypoint for the persistent background `lsp_server.runServerStream` thread.
fn runPersistentLspWorker(ctx: *ServerWorkerCtx) void {
    ctx.exit_code = lsp_server.runServerStream(
        ctx.allocator,
        ctx.io,
        ctx.env_map,
        &ctx.pipe.reader,
        &ctx.pipe.writer,
        null,
        .{},
    ) catch |err| blk: {
        ctx.server_err = err;
        ctx.pipe.resp_ready_event.set(ctx.io);
        break :blk 1;
    };
}

/// Formats a single `Content-Length: <N>\r\n\r\n<json>` frame into `out_buf`.
fn formatSingleLspFrame(out_buf: []u8, json_body: []const u8) []const u8 {
    var fixed_writer = std.Io.Writer.fixed(out_buf);
    fixed_writer.print("Content-Length: {d}\r\n\r\n{s}", .{ json_body.len, json_body }) catch unreachable;
    return fixed_writer.buffered();
}

/// Appends a `Content-Length: <N>\r\n\r\n<json>` frame onto `writer`.
fn appendLspFrameToWriter(writer: *std.Io.Writer, json_body: []const u8) !void {
    try writer.print("Content-Length: {d}\r\n\r\n{s}", .{ json_body.len, json_body });
}

/// Writes `raw_text` as a RFC 8259 JSON string literal (`"…"`) onto `writer`.
fn writeJsonEscapedString(writer: *std.Io.Writer, raw_text: []const u8) !void {
    try writer.writeByte('"');
    for (raw_text) |ch_byte| {
        switch (ch_byte) {
            '"' => try writer.writeAll("\\\""),
            '\\' => try writer.writeAll("\\\\"),
            '\n' => try writer.writeAll("\\n"),
            '\r' => try writer.writeAll("\\r"),
            '\t' => try writer.writeAll("\\t"),
            0x00...0x08, 0x0B...0x0C, 0x0E...0x1F => {
                try writer.print("\\u{x:0>4}", .{ch_byte});
            },
            else => try writer.writeByte(ch_byte),
        }
    }
    try writer.writeByte('"');
}

/// Extracts a 16-hex-character `"resultId":"<16-hex>"` token from `wire_bytes` if present.
fn extractSemanticResultId(wire_bytes: []const u8) ?[16]u8 {
    const needle = "\"resultId\":\"";
    var search_from: usize = 0;
    var found_id: ?[16]u8 = null;
    while (std.mem.indexOfPos(u8, wire_bytes, search_from, needle)) |hit_pos| {
        const val_start = hit_pos + needle.len;
        if (val_start + 17 <= wire_bytes.len and wire_bytes[val_start + 16] == '"') {
            var id_arr: [16]u8 = undefined;
            @memcpy(&id_arr, wire_bytes[val_start .. val_start + 16]);
            found_id = id_arr;
        }
        search_from = hit_pos + needle.len;
    }
    return found_id;
}

// ------------------- Workspace & Workloads --------------------

/// Counts newline characters (`\n`) in `text`.
fn countNewlines(text: []const u8) usize {
    var line_count: usize = 0;
    for (text) |byte_val| {
        if (byte_val == '\n') line_count += 1;
    }
    return line_count;
}

/// Generates a 400-line well-typed `.cx` module (`SamplePair` + `25` `@no_alloc @no_panic` functions).
fn writeSynthetic400LocModule(
    allocator: std.mem.Allocator,
    io: std.Io,
    src_dir: []const u8,
    mod_ordinal: usize,
) !usize {
    var buf: std.ArrayListUnmanaged(u8) = .empty;
    defer buf.deinit(allocator);
    try buf.ensureTotalCapacity(allocator, 20 * 1024);

    var alloc_writer = std.Io.Writer.Allocating.fromArrayList(allocator, &buf);
    defer buf = alloc_writer.toArrayList();
    const writer = &alloc_writer.writer;

    // Item 0 (`16` lines; `0..15`):
    try writer.print(
        "/| Module {d:0>3} state vector for incremental LSP scaling benchmark.\n" ++
            "pub struct SamplePair {{\n" ++
            "    /| Primary horizontal metric value.\n" ++
            "    pub x_metric: i32,\n" ++
            "    /| Secondary vertical metric value.\n" ++
            "    pub y_metric: i32,\n" ++
            "}}\n\n" ++
            "/| Constructs a `SamplePair` and computes scaled delta for `func_00`.\n" ++
            "/| Enforces zero-allocation and panic-free modular arithmetic contracts.\n" ++
            "@no_alloc @no_panic\n" ++
            "pub fn func_00(seed_val: i32) -> i32 {{\n" ++
            "    let pair = SamplePair {{ x_metric: seed_val, y_metric: {d} }};\n" ++
            "    let sum_val = pair.x_metric +% pair.y_metric;\n" ++
            "    return sum_val ^ 3;\n" ++
            "}}\n",
        .{ mod_ordinal, @as(usize, (mod_ordinal % 97) + 1) },
    );

    // Items `1..24` (`24` functions x `16` lines = `384` lines; total = `400` lines):
    var fn_idx: usize = 1;
    while (fn_idx < 25) : (fn_idx += 1) {
        try writer.print(
            "\n/| Computes deterministic modular step for `func_{d:0>2}`.\n" ++
                "/| Enforces zero-allocation and panic-free modular step invariants.\n" ++
                "@no_alloc @no_panic\n" ++
                "pub fn func_{d:0>2}(input_val: i32, bias_val: i32) -> i32 {{\n" ++
                "    let pair = SamplePair {{ x_metric: input_val, y_metric: bias_val }};\n" ++
                "    var acc_val: i32 = pair.x_metric +% 10;\n" ++
                "    if acc_val > 0 {{\n" ++
                "        acc_val = acc_val +% pair.y_metric;\n" ++
                "    }} else {{\n" ++
                "        acc_val = acc_val -% pair.y_metric;\n" ++
                "    }}\n" ++
                "    let folded_val = acc_val ^ {d};\n" ++
                "    let prev_val = func_00(folded_val);\n" ++
                "    return prev_val +% 1;\n" ++
                "}}\n",
            .{ fn_idx, fn_idx, fn_idx + 11 },
        );
    }

    const content = alloc_writer.written();
    const lines = countNewlines(content);
    if (lines != LINES_PER_MODULE) return error.UnexpectedModuleLineCount;

    const file_path = try std.fmt.allocPrint(allocator, "{s}/mod_{d:0>3}.cx", .{ src_dir, mod_ordinal });
    defer allocator.free(file_path);
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = file_path, .data = content });
    return lines;
}

/// Generates `src/root.cx` (`400` lines: `249` `pub mod` items + `7`-line struct + `9` x `16`-line functions).
fn writeSynthetic400LocRootModule(
    allocator: std.mem.Allocator,
    io: std.Io,
    src_dir: []const u8,
) !usize {
    var buf: std.ArrayListUnmanaged(u8) = .empty;
    defer buf.deinit(allocator);
    try buf.ensureTotalCapacity(allocator, 16 * 1024);

    var alloc_writer = std.Io.Writer.Allocating.fromArrayList(allocator, &buf);
    defer buf = alloc_writer.toArrayList();
    const writer = &alloc_writer.writer;

    var mod_idx: usize = 1;
    while (mod_idx < WORKSPACE_MODULE_COUNT) : (mod_idx += 1) {
        try writer.print("pub mod mod_{d:0>3};\n", .{mod_idx});
    }

    // `7` lines (`249 + 7 = 256` lines):
    try writer.writeAll(
        "\n/| Root workspace summary record for the 100,000-LOC LSP benchmark corpus.\n" ++
            "pub struct RootSummary {\n" ++
            "    pub checksum: i32,\n" ++
            "    pub sample_count: i32,\n" ++
            "    pub flags: i32,\n" ++
            "}\n",
    );

    // `9` functions x `16` lines = `144` lines (`256 + 144 = 400` lines):
    var fn_idx: usize = 0;
    while (fn_idx < 9) : (fn_idx += 1) {
        const target_mod = fn_idx * 25 + 1;
        try writer.print(
            "\n/| Aggregates cross-module sample `{d}` from `mod_{d:0>3}`.\n" ++
                "/| Preserves panic-free cross-module probe invariants.\n" ++
                "@no_alloc @no_panic\n" ++
                "pub fn root_probe_{d:0>2}(seed_val: i32) -> i32 {{\n" ++
                "    let remote_val = mod_{d:0>3}.func_00(seed_val);\n" ++
                "    let summary = RootSummary {{ checksum: remote_val, sample_count: 1, flags: {d} }};\n" ++
                "    var total_val: i32 = summary.checksum +% summary.sample_count;\n" ++
                "    if total_val > 0 {{\n" ++
                "        total_val = total_val +% summary.flags;\n" ++
                "    }} else {{\n" ++
                "        total_val = total_val -% summary.flags;\n" ++
                "    }}\n" ++
                "    let mixed_val = total_val ^ 5;\n" ++
                "    return mixed_val;\n" ++
                "}}\n",
            .{ fn_idx, target_mod, fn_idx, target_mod, fn_idx + 1 },
        );
    }

    const content = alloc_writer.written();
    const lines = countNewlines(content);
    if (lines != LINES_PER_MODULE) return error.UnexpectedRootLineCount;

    const root_path = try std.fmt.allocPrint(allocator, "{s}/root.cx", .{src_dir});
    defer allocator.free(root_path);
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = root_path, .data = content });
    return lines;
}

/// Initializes the 100,000-LOC workspace on disk, spawns persistent `corex lsp`, and pre-warms `mod_125.cx`.
fn preparePhase10BenchState(allocator: std.mem.Allocator, io: std.Io) !PreparedPhase10BenchState {
    const scratch_dir = try allocator.dupe(u8, ".zig-cache/phase10_bench_env");
    errdefer allocator.free(scratch_dir);
    std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, scratch_dir);

    const corex_home = try std.fmt.allocPrint(allocator, "{s}/home", .{scratch_dir});
    errdefer allocator.free(corex_home);
    const ws_dir = try std.fmt.allocPrint(allocator, "{s}/ws", .{scratch_dir});
    defer allocator.free(ws_dir);
    const src_dir = try std.fmt.allocPrint(allocator, "{s}/src", .{ws_dir});
    defer allocator.free(src_dir);

    try std.Io.Dir.cwd().createDirPath(io, corex_home);
    try std.Io.Dir.cwd().createDirPath(io, src_dir);

    // [1] Write `corex.toml` and `250` `.cx` modules (`250 x 400 = 100,000` LOC):
    const toml_path = try std.fmt.allocPrint(allocator, "{s}/corex.toml", .{ws_dir});
    defer allocator.free(toml_path);
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = toml_path,
        .data = "[package]\nname = \"lsp-scale-100k\"\nversion = \"0.1.0\"\n" ++
            "edition = \"2026\"\n\n[lib]\npath = \"src/root.cx\"\n",
    });

    var total_loc: usize = try writeSynthetic400LocRootModule(allocator, io, src_dir);
    var mod_idx: usize = 1;
    while (mod_idx < WORKSPACE_MODULE_COUNT) : (mod_idx += 1) {
        total_loc += try writeSynthetic400LocModule(allocator, io, src_dir, mod_idx);
    }
    if (total_loc != EXPECTED_WORKSPACE_LOC) return error.WorkspaceLocMismatch;

    // [2] Spawn persistent `lsp_server.runServerStream` worker thread:
    const env_map = try allocator.create(std.process.Environ.Map);
    errdefer allocator.destroy(env_map);
    env_map.* = std.process.Environ.Map.init(allocator);
    errdefer env_map.deinit();
    try env_map.put("COREX_HOME", corex_home);

    const pipe = try LspTurnPipe.create(allocator, io);
    errdefer pipe.destroy();

    const worker_ctx = try allocator.create(ServerWorkerCtx);
    errdefer allocator.destroy(worker_ctx);
    worker_ctx.* = .{
        .allocator = allocator,
        .io = io,
        .env_map = env_map,
        .pipe = pipe,
    };

    const server_thread = try std.Thread.spawn(
        .{ .stack_size = 16 * 1024 * 1024 },
        runPersistentLspWorker,
        .{worker_ctx},
    );
    errdefer {
        var exit_err_buf: [256]u8 = undefined;
        const exit_err_frame = formatSingleLspFrame(
            &exit_err_buf,
            "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}",
        );
        pipe.submitFinalExitAndEof(exit_err_frame);
        server_thread.join();
    }

    // [3] Pre-warm `initialize` (`250` modules mounted) + `didOpen` (`mod_125.cx`) + initial `semanticTokens/full`:
    var abs_ws_interner = try corex.StringInterner.init(allocator);
    defer abs_ws_interner.deinit();
    var abs_vfs = corex.VfsSourceMap.init(allocator, &abs_ws_interner);
    defer abs_vfs.deinit(io);
    const norm_toml_id = try abs_vfs.resolvePath(io, toml_path);
    const norm_toml_path = abs_vfs.interner.get(norm_toml_id);
    const norm_ws_dir = std.fs.path.dirname(norm_toml_path) orelse ws_dir;

    const ws_uri = try lsp_server.encodePathToFileUri(allocator, norm_ws_dir);
    defer allocator.free(ws_uri);
    const mod125_disk_path = try std.fmt.allocPrint(allocator, "{s}/src/mod_125.cx", .{norm_ws_dir});
    defer allocator.free(mod125_disk_path);
    const mod125_uri = try lsp_server.encodePathToFileUri(allocator, mod125_disk_path);
    errdefer allocator.free(mod125_uri);

    const init_json = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{{" ++
            "\"workspaceFolders\":[{{\"uri\":\"{s}\",\"name\":\"ws\"}}]," ++
            "\"capabilities\":{{\"general\":{{\"positionEncodings\":[\"utf-8\"]}}," ++
            "\"textDocument\":{{\"diagnostic\":{{}}}}}}}}}}",
        .{ws_uri},
    );
    defer allocator.free(init_json);
    var init_frame_buf: [2048]u8 = undefined;
    const init_resp = pipe.submitTurnAndWait(formatSingleLspFrame(&init_frame_buf, init_json), 1);
    if (std.mem.indexOf(u8, init_resp, "\"capabilities\"") == null) {
        return error.LspInitializeFailed;
    }

    const mod125_bytes = try std.Io.Dir.cwd().readFileAlloc(
        io,
        mod125_disk_path,
        allocator,
        .limited(1024 * 1024),
    );
    defer allocator.free(mod125_bytes);

    var open_batch = std.Io.Writer.Allocating.init(allocator);
    defer open_batch.deinit();
    try appendLspFrameToWriter(
        &open_batch.writer,
        "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}",
    );

    var did_open_body = std.Io.Writer.Allocating.init(allocator);
    defer did_open_body.deinit();
    try did_open_body.writer.print(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{" ++
            "\"uri\":\"{s}\",\"languageId\":\"corex\",\"version\":1,\"text\":",
        .{mod125_uri},
    );
    try writeJsonEscapedString(&did_open_body.writer, mod125_bytes);
    try did_open_body.writer.writeAll("}}}");
    try appendLspFrameToWriter(&open_batch.writer, did_open_body.written());

    const warm_diag_json = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/diagnostic\"," ++
            "\"params\":{{\"textDocument\":{{\"uri\":\"{s}\"}}}}}}",
        .{mod125_uri},
    );
    defer allocator.free(warm_diag_json);
    try appendLspFrameToWriter(&open_batch.writer, warm_diag_json);

    const warm_sem_json = try std.fmt.allocPrint(
        allocator,
        "{{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/semanticTokens/full\"," ++
            "\"params\":{{\"textDocument\":{{\"uri\":\"{s}\"}}}}}}",
        .{mod125_uri},
    );
    defer allocator.free(warm_sem_json);
    try appendLspFrameToWriter(&open_batch.writer, warm_sem_json);

    const warm_resp = pipe.submitTurnAndWait(open_batch.written(), 2);
    if (std.mem.indexOf(u8, warm_resp, "\"items\":[]") == null) {
        return error.WarmupDiagnosticsNotClean;
    }

    return .{
        .io = io,
        .scratch_dir = scratch_dir,
        .corex_home_dir = corex_home,
        .env_map = env_map,
        .pipe = pipe,
        .worker_ctx = worker_ctx,
        .server_thread = server_thread,
        .mod125_uri = mod125_uri,
        .latest_sem_result_id = extractSemanticResultId(warm_resp) orelse return error.MissingInitialSemanticResultId,
    };
}

/// Case 1 (`lsp_100kloc_did_change_diagnostics`): Incremental keystroke edit + pull diagnostics (`< 10 ms` P99).
fn benchLsp100kDidChangeDiagnostics(_: std.mem.Allocator) !usize {
    const state = if (shared_bench_state) |*ptr| ptr else return error.MissingBenchState;

    const doc_ver = state.next_doc_version;
    state.next_doc_version += 1;
    const req_id = state.next_rpc_id;
    state.next_rpc_id += 1;
    const new_lit: []const u8 = if ((doc_ver & 1) == 0) "11" else "10";

    var change_buf: [768]u8 = undefined;
    var change_writer = std.Io.Writer.fixed(&change_buf);
    try change_writer.print(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\",\"version\":{d}}}," ++
            "\"contentChanges\":[{{\"range\":{{\"start\":{{\"line\":198,\"character\":40}}," ++
            "\"end\":{{\"line\":198,\"character\":42}}}},\"text\":\"{s}\"}}]}}}}",
        .{ state.mod125_uri, doc_ver, new_lit },
    );

    var diag_buf: [512]u8 = undefined;
    var diag_writer = std.Io.Writer.fixed(&diag_buf);
    try diag_writer.print(
        "{{\"jsonrpc\":\"2.0\",\"id\":{d},\"method\":\"textDocument/diagnostic\"," ++
            "\"params\":{{\"textDocument\":{{\"uri\":\"{s}\"}}}}}}",
        .{ req_id, state.mod125_uri },
    );

    var wire_buf: [1536]u8 = undefined;
    var wire_writer = std.Io.Writer.fixed(&wire_buf);
    try appendLspFrameToWriter(&wire_writer, change_writer.buffered());
    try appendLspFrameToWriter(&wire_writer, diag_writer.buffered());

    const start_ts = std.Io.Clock.Timestamp.now(state.io, .awake);
    const resp_bytes = state.pipe.submitTurnAndWait(wire_writer.buffered(), 1);
    const end_ts = std.Io.Clock.Timestamp.now(state.io, .awake);

    if (std.mem.indexOf(u8, resp_bytes, "\"items\":[]") == null) {
        return error.UnexpectedLspDiagnosticError;
    }

    const call_idx = state.case1_call_count;
    state.case1_call_count += 1;
    if (call_idx >= BENCH_WARMUP_COUNT) {
        const sample_slot = call_idx - BENCH_WARMUP_COUNT;
        if (sample_slot < BENCH_MEASURED_COUNT) {
            state.case1_samples_ns[sample_slot] = @intCast(
                @max(@as(i96, 0), start_ts.durationTo(end_ts).raw.nanoseconds),
            );
        }
    }

    std.mem.doNotOptimizeAway(resp_bytes.ptr);
    return resp_bytes.len;
}

/// Case 2 (`lsp_100kloc_completion_hover_def_tokens`): Completion + Hover + Definition + Delta Tokens (`< 10 ms` P99).
fn benchLsp100kCompletionHoverDefTokens(_: std.mem.Allocator) !usize {
    const state = if (shared_bench_state) |*ptr| ptr else return error.MissingBenchState;

    const id_comp = state.next_rpc_id;
    const id_hover = id_comp + 1;
    const id_def = id_comp + 2;
    const id_sem = id_comp + 3;
    state.next_rpc_id += 4;

    var comp_buf: [512]u8 = undefined;
    var comp_writer = std.Io.Writer.fixed(&comp_buf);
    try comp_writer.print(
        "{{\"jsonrpc\":\"2.0\",\"id\":{d},\"method\":\"textDocument/completion\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":198,\"character\":28}}}}}}",
        .{ id_comp, state.mod125_uri },
    );

    var hover_buf: [512]u8 = undefined;
    var hover_writer = std.Io.Writer.fixed(&hover_buf);
    try hover_writer.print(
        "{{\"jsonrpc\":\"2.0\",\"id\":{d},\"method\":\"textDocument/hover\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":205,\"character\":21}}}}}}",
        .{ id_hover, state.mod125_uri },
    );

    var def_buf: [512]u8 = undefined;
    var def_writer = std.Io.Writer.fixed(&def_buf);
    try def_writer.print(
        "{{\"jsonrpc\":\"2.0\",\"id\":{d},\"method\":\"textDocument/definition\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"position\":{{\"line\":205,\"character\":21}}}}}}",
        .{ id_def, state.mod125_uri },
    );

    var sem_buf: [512]u8 = undefined;
    var sem_writer = std.Io.Writer.fixed(&sem_buf);
    try sem_writer.print(
        "{{\"jsonrpc\":\"2.0\",\"id\":{d},\"method\":\"textDocument/semanticTokens/full/delta\",\"params\":{{" ++
            "\"textDocument\":{{\"uri\":\"{s}\"}},\"previousResultId\":\"{s}\"}}}}",
        .{ id_sem, state.mod125_uri, &state.latest_sem_result_id },
    );

    var wire_buf: [3072]u8 = undefined;
    var wire_writer = std.Io.Writer.fixed(&wire_buf);
    try appendLspFrameToWriter(&wire_writer, comp_writer.buffered());
    try appendLspFrameToWriter(&wire_writer, hover_writer.buffered());
    try appendLspFrameToWriter(&wire_writer, def_writer.buffered());
    try appendLspFrameToWriter(&wire_writer, sem_writer.buffered());

    const start_ts = std.Io.Clock.Timestamp.now(state.io, .awake);
    const resp_bytes = state.pipe.submitTurnAndWait(wire_writer.buffered(), 4);
    const end_ts = std.Io.Clock.Timestamp.now(state.io, .awake);

    if (std.mem.indexOf(u8, resp_bytes, "x_metric") == null or
        std.mem.indexOf(u8, resp_bytes, "fn func_00") == null)
    {
        return error.UnexpectedLspFeatureResponse;
    }
    if (extractSemanticResultId(resp_bytes)) |updated_id| {
        state.latest_sem_result_id = updated_id;
    } else {
        return error.MissingDeltaSemanticResultId;
    }

    const call_idx = state.case2_call_count;
    state.case2_call_count += 1;
    if (call_idx >= BENCH_WARMUP_COUNT) {
        const sample_slot = call_idx - BENCH_WARMUP_COUNT;
        if (sample_slot < BENCH_MEASURED_COUNT) {
            state.case2_samples_ns[sample_slot] = @intCast(
                @max(@as(i96, 0), start_ts.durationTo(end_ts).raw.nanoseconds),
            );
        }
    }

    std.mem.doNotOptimizeAway(resp_bytes.ptr);
    return resp_bytes.len;
}

/// Case 3 (`upgrade_3tier_synergy_module`): 3-tier `DR-21`..`DR-24` `upgradeSource` fixed-point migration.
fn benchUpgrade3TierSynergyModule(allocator: std.mem.Allocator) !usize {
    var upg_res = try upgrade_engine.upgradeSource(
        allocator,
        LEGACY_SYNERGY_MODULE_CX,
        FileId.fromInt(1),
        .{},
    );
    defer upg_res.deinit(allocator);

    if (!upg_res.is_changed or upg_res.is_rolled_back) {
        return error.UpgradeSynergyBenchmarkFailed;
    }
    std.mem.doNotOptimizeAway(upg_res.upgraded_source.ptr);
    return upg_res.upgraded_source.len;
}

/// Sorts a 100-sample latency array ascending and returns the exact P99 sample (`samples[98]`).
fn computeSortedP99Ns(raw_samples: *const [BENCH_MEASURED_COUNT]u64) u64 {
    var sorted_copy: [BENCH_MEASURED_COUNT]u64 = raw_samples.*;
    std.mem.sort(u64, &sorted_copy, {}, std.sort.asc(u64));
    return sorted_copy[P99_SAMPLE_INDEX];
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 10 100,000-LOC incremental LSP and Zero-Legacy `upgrade` benchmark suite.
pub fn main(init: std.process.Init) !void {
    shared_bench_state = try preparePhase10BenchState(init.gpa, init.io);
    defer {
        if (shared_bench_state) |*state_ref| {
            state_ref.deinit(init.gpa);
            shared_bench_state = null;
        }
    }

    const cases = [_]BenchCase{
        .{
            .name = "lsp_100kloc_did_change_diagnostics (< 10 ms P99)",
            .run_fn = benchLsp100kDidChangeDiagnostics,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "lsp_100kloc_completion_hover_def_tokens (< 10 ms P99)",
            .run_fn = benchLsp100kCompletionHoverDefTokens,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "upgrade_3tier_synergy_module (DR-21..DR-24)",
            .run_fn = benchUpgrade3TierSynergyModule,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
    };

    var results: [cases.len]BenchResult = undefined;
    for (cases, 0..) |bench_case, i| {
        results[i] = try corex.bench_harness.runCase(init.gpa, init.io, bench_case);
    }

    const state_ptr = &(shared_bench_state orelse return error.MissingBenchState);
    const case1_p99_ns = computeSortedP99Ns(&state_ptr.case1_samples_ns);
    const case2_p99_ns = computeSortedP99Ns(&state_ptr.case2_samples_ns);

    var stdout_buf: [8192]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writerStreaming(init.io, &stdout_buf);
    const style_config: StyleConfig = .{
        .is_color_enabled = corex.style.isColorEnabled(.auto, init.io, std.Io.File.stdout(), init.environ_map),
    };

    try style_config.writeStatusHeader(
        &stdout_writer.interface,
        .success,
        corex.Glyphs.POINTER_SOLID,
        "corex bench",
        "Phase 10 100,000-LOC Incremental LSP & Zero-Legacy Upgrade Suite (5 warmup, 100 measured)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, &results);

    if (case1_p99_ns >= MAX_LSP_P99_BUDGET_NS or results[0].stats.p95_ns >= MAX_LSP_P99_BUDGET_NS) {
        try stdout_writer.interface.flush();
        return error.LspDidChangeDiagnosticsP99Exceeded;
    }
    if (case2_p99_ns >= MAX_LSP_P99_BUDGET_NS or results[1].stats.p95_ns >= MAX_LSP_P99_BUDGET_NS) {
        try stdout_writer.interface.flush();
        return error.LspInteractiveFeaturesP99Exceeded;
    }

    var p99_c1_buf: [32]u8 = undefined;
    var p99_c2_buf: [32]u8 = undefined;
    var footer_buf: [256]u8 = undefined;
    try style_config.writeStatusHeader(
        &stdout_writer.interface,
        .success,
        corex.Glyphs.SUCCESS,
        "budgets",
        try std.fmt.bufPrint(
            &footer_buf,
            "100K-LOC LSP P99 verified (< 10 ms): didChange+diag P99 = {s}, completion+hover+def+delta P99 = {s}",
            .{
                corex.bench_harness.formatDurationNs(&p99_c1_buf, case1_p99_ns),
                corex.bench_harness.formatDurationNs(&p99_c2_buf, case2_p99_ns),
            },
        ),
    );
    try stdout_writer.interface.writeByte('\n');
    try stdout_writer.interface.flush();
}

//! Four-Tier Differential Backend Execution Oracle (`DR-20` `D-07A`)
//!
//! Executes a CoreX program across all four Stage-0 semantic and native execution tiers:
//! Tier 1 (`pre_opt_vm`: post-SAST `--dev` `D1`–`D5` `MirVm`), Tier 2 (`post_opt_vm`: post-SAST
//! `--release` `D1`–`D5` + `R1`–`R6` `MirVm`), Tier 3 (`tier_a_c99`: `-ofmt=c` ISO C99 + `zig cc`
//! native executable), and Tier 4 (`tier_b_llvm`: LLVM 20–23 `.ll` `-O2` + `zig cc` native
//! executable).
//!
//! Asserts exact bit-for-bit parity across `has_trapped`, `exit_code`, `return_scalar_i64`,
//! `stdout_bytes`, `stderr_bytes`, and `drop_trace` (`[]const i64`), rendering a monochrome
//! Unicode box-drawing divergence report (`╭`, `│`, `╰`, `├`, `─`, `✓`, `✗`) on any mismatch.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const diagnostic = @import("diag/diagnostic.zig");
const router = @import("cli/router.zig");
const mir = @import("mir.zig");
const mir_vm = @import("mir_vm.zig");
const query_db = @import("query_db.zig");
const codegen_abi = @import("codegen_abi.zig");

const FileId = mem_foundation.FileId;
const TokenBuffer = syntax_arenas.TokenBuffer;
const DiagnosticSink = diagnostic.DiagnosticSink;
const TargetSpec = codegen_abi.TargetSpec;
const CompilerDb = query_db.CompilerDb;

// ---------------------------------------- TYPES ----------------------------------------

// ---------------- Oracle Tier Outcome & Report ----------------

/// Canonical 4-tier execution stage identifier (`DR-20` `D-07A`).
pub const OracleTierId = enum(u8) {
    /// Tier 1: Post-SAST `--dev` (`D1`–`D5`) `MirVm` execution.
    pre_opt_vm = 0,
    /// Tier 2: Post-SAST `--release` (`D1`–`D5` + `R1`–`R6`) `MirVm` execution.
    post_opt_vm = 1,
    /// Tier 3: Tier A (`-ofmt=c`) ISO C99 native binary compiled via `zig cc`.
    tier_a_c99 = 2,
    /// Tier 4: Tier B (`LLVM 20–23`) `--release` (`-O2`) native binary compiled via `zig cc`.
    tier_b_llvm = 3,

    /// Returns the human-readable column label for `self` in differential tables.
    pub fn asColumnName(self: OracleTierId) []const u8 {
        return switch (self) {
            .pre_opt_vm => "Tier 1 (Dev VM)",
            .post_opt_vm => "Tier 2 (Rel VM)",
            .tier_a_c99 => "Tier 3 (C99)",
            .tier_b_llvm => "Tier 4 (LLVM)",
        };
    }
};

/// Observable runtime behavior captured from executing `main` on a single backend tier.
pub const OracleTierOutcome = struct {
    /// `true` if execution terminated via `@trap()`, `@panic(…)`, arithmetic overflow, or OOB check.
    has_trapped: bool = false,
    /// Process exit status (`101` on trap, `@sys_exit(code)` argument, `1` on `Result::Err`, or `u8` return).
    exit_code: i32 = 0,
    /// Exact 64-bit integer scalar returned by `main` (`0` for `unit`, `Result`, traps, or `@sys_exit`).
    return_scalar_i64: i64 = 0,
    /// Captured `stdout` (`fd = 1`) byte stream owned by `allocator`.
    stdout_bytes: []u8 = &.{},
    /// Captured `stderr` (`fd = 2`) byte stream owned by `allocator`.
    stderr_bytes: []u8 = &.{},
    /// Ordered `@drop_trace(id)` lifecycle ledger owned by `allocator`.
    drop_trace: []i64 = &.{},

    /// Releases all heap slices owned by `self`.
    pub fn deinit(self: *OracleTierOutcome, allocator: std.mem.Allocator) void {
        if (self.stdout_bytes.len > 0) allocator.free(self.stdout_bytes);
        if (self.stderr_bytes.len > 0) allocator.free(self.stderr_bytes);
        if (self.drop_trace.len > 0) allocator.free(self.drop_trace);
        self.* = undefined;
    }

    /// Returns `true` if `self` and `other` agree across all six observable channels.
    pub fn eql(self: OracleTierOutcome, other: OracleTierOutcome) bool {
        return self.has_trapped == other.has_trapped and
            self.exit_code == other.exit_code and
            self.return_scalar_i64 == other.return_scalar_i64 and
            std.mem.eql(u8, self.stdout_bytes, other.stdout_bytes) and
            std.mem.eql(u8, self.stderr_bytes, other.stderr_bytes) and
            std.mem.eql(i64, self.drop_trace, other.drop_trace);
    }
};

/// Configuration options for `runFourTierDiffOracle` and `runFourTierDiffOracleOnDb`.
pub const DiffOracleOptions = struct {
    /// Zig `Io` handle used to invoke `zig cc`, execute native binaries, and clean up temp files.
    io: std.Io,
    /// Optional host environment map forwarded to `zig cc` and child executables.
    environ_map: ?*const std.process.Environ.Map = null,
    /// Optional `VfsSourceMap` used for `#line` / DWARF emission during Tier 3 & Tier 4 builds.
    vfs_source_map: ?*const vfs_sourcemap.VfsSourceMap = null,
    /// Optional workspace root directory for `@embed_bytes` sandboxing.
    workspace_root: ?[]const u8 = null,
    /// Optional in-memory VFS map for `@embed_bytes`.
    virtual_files: ?*const std.StringHashMapUnmanaged([]const u8) = null,
    /// Optional additional `FileId`s linked into the same module when calling `runFourTierDiffOracleOnDb`.
    extra_file_ids: []const FileId = &.{},
    /// Step-count cap enforced on Tier 1 and Tier 2 `MirVm` runs.
    comptime_step_limit: u64 = router.DEFAULT_COMPTIME_STEP_LIMIT,
    /// Optional diagnostic sink receiving front-end or codegen errors.
    diagnostic_sink: ?*DiagnosticSink = null,
};

/// Complete 4-tier differential verification result (`DR-20` `D-07A`).
pub const DiffOracleReport = struct {
    /// Per-tier observable execution outcomes (`0..3`).
    outcomes: [TIER_COUNT]OracleTierOutcome,
    /// `true` iff Tier 1, Tier 2, Tier 3, and Tier 4 agree across every observable channel.
    is_all_matching: bool,
    /// Monochrome Unicode box-drawing diff table (non-empty whenever `!is_all_matching`).
    rendered_diff_table: []u8 = &.{},

    /// Releases all owned buffers across `outcomes` and `rendered_diff_table`.
    pub fn deinit(self: *DiffOracleReport, allocator: std.mem.Allocator) void {
        var tier_i: usize = 0;
        while (tier_i < TIER_COUNT) : (tier_i += 1) {
            self.outcomes[tier_i].deinit(allocator);
        }
        if (self.rendered_diff_table.len > 0) {
            allocator.free(self.rendered_diff_table);
        }
        self.* = undefined;
    }
};

/// Error set returned by the 4-tier differential oracle.
pub const DiffOracleError = query_db.ModuleCompileError || error{
    /// Target module does not define a zero-argument `main` entrypoint.
    MissingMainEntrypoint,
    /// Native host executable failed to launch or read its `COREX_ORACLE_TRACE_FILE`.
    NativeExecutionFailed,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Total number of execution tiers compared by `diff_oracle` (`4`).
pub const TIER_COUNT: usize = 4;

/// Maximum `stdout` or `stderr` capture size per native child execution (`4 MiB`).
const MAX_CAPTURE_BYTES: usize = 4 * 1024 * 1024;

/// Monotonic atomic counter preventing scratch-path collisions across parallel oracle runs.
var next_oracle_scratch_seq = std.atomic.Value(u32).init(1);

// -------------------------------------- INTERNALS --------------------------------------

// --------------------- MirVm Tier Runner ----------------------

/// Locates the zero-argument `main` entrypoint `MirBody` inside `bodies`, preferring `root_file_id`.
fn findMainEntrypointBody(
    bodies: []const mir.MirBody,
    interner: *const mem_foundation.StringInterner,
    root_file_id: FileId,
) ?*const mir.MirBody {
    var fallback_main: ?*const mir.MirBody = null;
    for (bodies) |*cand_body| {
        if (cand_body.param_count != 0) continue;
        if (!std.mem.eql(u8, interner.get(cand_body.name), "main")) continue;
        if (cand_body.def_id.fileId() == root_file_id) {
            return cand_body;
        }
        if (fallback_main == null) {
            fallback_main = cand_body;
        }
    }
    return fallback_main;
}

/// Executes `root_file_id` (and reachable modules) in `MirVm` under `--dev` (`false`) or `--release` (`true`).
fn executeVmTierOnDb(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    root_file_id: FileId,
    reachable_files: []const FileId,
    is_release_mode: bool,
    host_spec: TargetSpec,
    options: DiffOracleOptions,
) DiffOracleError!OracleTierOutcome {
    var owned_bodies: std.ArrayListUnmanaged(mir.MirBody) = .empty;
    defer {
        for (owned_bodies.items) |*body_item| body_item.deinit();
        owned_bodies.deinit(allocator);
    }
    db.collectOptimizedModuleBodies(
        allocator,
        root_file_id,
        reachable_files,
        is_release_mode,
        options.diagnostic_sink,
        &owned_bodies,
    ) catch |comp_err| switch (comp_err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Cancelled => return error.Cancelled,
        else => return error.FrontendErrors,
    };

    const main_body = findMainEntrypointBody(owned_bodies.items, &db.interner, root_file_id) orelse
        return error.MissingMainEntrypoint;

    var file_tokens: std.AutoHashMapUnmanaged(u32, *const TokenBuffer) = .empty;
    defer file_tokens.deinit(allocator);
    var parsed_iter = db.parsed_artifacts.iterator();
    while (parsed_iter.next()) |kv| {
        try file_tokens.put(allocator, kv.key_ptr.*, &kv.value_ptr.token_buffer);
    }

    var stdout_buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer stdout_buf.deinit(allocator);
    var stderr_buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer stderr_buf.deinit(allocator);

    var vm_sink = DiagnosticSink.init(allocator);
    defer vm_sink.deinit();

    var vm_engine = try mir_vm.MirVm.init(
        allocator,
        &db.interner,
        &db.type_pool,
        &db.symbol_table,
        &db.rodata_pool,
        null,
        &vm_sink,
        .{
            .step_budget = options.comptime_step_limit,
            .target_layout = host_spec.asTargetLayout(),
            .workspace_root = if (options.workspace_root) |ws_root| ws_root else db.workspace_root,
            .io = options.io,
            .virtual_files = if (options.virtual_files) |vfs_map| vfs_map else db.virtual_files,
            .file_tokens = &file_tokens,
            .compiler_db = db,
            .stdout_capture = &stdout_buf,
            .stderr_capture = &stderr_buf,
            .is_oracle_runtime_mode = true,
        },
    );
    defer vm_engine.deinit();

    for (owned_bodies.items) |*body_ptr| {
        const sym_idx = if (!body_ptr.symbol_index.isNone())
            body_ptr.symbol_index
        else
            db.symbol_table.def_to_symbol.get(body_ptr.def_id.asInt()) orelse .none;
        _ = try vm_engine.registerBody(body_ptr, sym_idx);
    }

    var has_trapped = false;
    var exit_code: i32 = 0;
    var return_scalar_i64: i64 = 0;

    if (vm_engine.evalBody(main_body, &.{})) |eval_res| {
        const unwrapped_ret = db.type_pool.unwrapUnderlyingType(main_body.ret_ty);
        if (vm_engine.slotToComptimeValue(eval_res.type_id, eval_res.repr, eval_res.slot, null)) |ct_val| {
            switch (ct_val) {
                .int_val => |int_v| {
                    const bits_u128: u128 = @bitCast(int_v);
                    if (unwrapped_ret != .i128_ty and unwrapped_ret != .u128_ty) {
                        const raw_u64: u64 = @truncate(bits_u128);
                        return_scalar_i64 = @bitCast(raw_u64);
                        exit_code = @intCast(@as(u8, @truncate(raw_u64)));
                    }
                },
                .variant => |variant_val| {
                    if (!unwrapped_ret.isPrimitiveOrSentinel() and
                        db.type_pool.getNode(unwrapped_ret).tag == .result_ty and
                        variant_val.tag_ordinal == 1)
                    {
                        exit_code = 1;
                    }
                },
                else => {},
            }
        } else |conv_err| switch (conv_err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Cancelled => return error.Cancelled,
            else => {
                has_trapped = true;
                exit_code = 101;
            },
        }
    } else |eval_err| switch (eval_err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Cancelled => return error.Cancelled,
        error.ProcessExited => {
            has_trapped = false;
            exit_code = vm_engine.exited_with_code orelse 0;
            return_scalar_i64 = 0;
        },
        else => {
            has_trapped = true;
            exit_code = 101;
            return_scalar_i64 = 0;
        },
    }

    const owned_drops = if (vm_engine.asDropTraceSlice().len > 0)
        try allocator.dupe(i64, vm_engine.asDropTraceSlice())
    else
        @as([]i64, &.{});
    errdefer if (owned_drops.len > 0) allocator.free(owned_drops);

    const owned_stdout = if (stdout_buf.items.len > 0)
        try stdout_buf.toOwnedSlice(allocator)
    else blk: {
        stdout_buf.deinit(allocator);
        break :blk @as([]u8, &.{});
    };
    errdefer if (owned_stdout.len > 0) allocator.free(owned_stdout);

    const owned_stderr = if (stderr_buf.items.len > 0)
        try stderr_buf.toOwnedSlice(allocator)
    else blk: {
        stderr_buf.deinit(allocator);
        break :blk @as([]u8, &.{});
    };

    return .{
        .has_trapped = has_trapped,
        .exit_code = exit_code,
        .return_scalar_i64 = return_scalar_i64,
        .stdout_bytes = owned_stdout,
        .stderr_bytes = owned_stderr,
        .drop_trace = owned_drops,
    };
}

// ------------------ Native Executable Runner ------------------

/// Parses a `COREX_ORACLE_TRACE_FILE` log (`DROP:`, `TRAP:1`, `EXIT:`, `ERR:1`, `RET:`) into outcome fields.
fn parseOracleTraceContents(
    allocator: std.mem.Allocator,
    trace_text: []const u8,
    term_state: std.process.Child.Term,
    has_trapped_out: *bool,
    out_exit_code: *i32,
    out_ret_scalar: *i64,
    out_drops: *std.ArrayListUnmanaged(i64),
) !void {
    var has_explicit_terminal = false;
    var line_iter = std.mem.splitScalar(u8, trace_text, '\n');
    while (line_iter.next()) |raw_line| {
        const clean_line = std.mem.trimEnd(u8, raw_line, "\r ");
        if (clean_line.len == 0) continue;

        if (std.mem.startsWith(u8, clean_line, "DROP:")) {
            const payload = clean_line["DROP:".len..];
            if (std.fmt.parseInt(i64, payload, 10)) |drop_id| {
                try out_drops.append(allocator, drop_id);
            } else |_| {}
        } else if (std.mem.eql(u8, clean_line, "TRAP:1")) {
            has_trapped_out.* = true;
            out_exit_code.* = 101;
            out_ret_scalar.* = 0;
            has_explicit_terminal = true;
        } else if (std.mem.startsWith(u8, clean_line, "EXIT:")) {
            const payload = clean_line["EXIT:".len..];
            has_trapped_out.* = false;
            out_exit_code.* = std.fmt.parseInt(i32, payload, 10) catch 0;
            out_ret_scalar.* = 0;
            has_explicit_terminal = true;
        } else if (std.mem.eql(u8, clean_line, "ERR:1")) {
            has_trapped_out.* = false;
            out_exit_code.* = 1;
            out_ret_scalar.* = 0;
            has_explicit_terminal = true;
        } else if (std.mem.startsWith(u8, clean_line, "RET:")) {
            const payload = clean_line["RET:".len..];
            has_trapped_out.* = false;
            const parsed_i64: i64 = if (std.mem.startsWith(u8, payload, "-"))
                (std.fmt.parseInt(i64, payload, 10) catch 0)
            else
                @bitCast(std.fmt.parseUnsigned(u64, payload, 10) catch 0);
            out_ret_scalar.* = parsed_i64;
            out_exit_code.* = @intCast(@as(u8, @truncate(@as(u64, @bitCast(parsed_i64)))));
            has_explicit_terminal = true;
        }
    }

    if (!has_explicit_terminal) {
        switch (term_state) {
            .exited => |status_u8| {
                out_exit_code.* = status_u8;
                if (status_u8 == 101) {
                    has_trapped_out.* = true;
                }
            },
            else => {
                has_trapped_out.* = true;
                out_exit_code.* = 101;
            },
        }
    }
}

/// Compiles `root_file_id` with `backend` and executes the resulting native binary under `COREX_ORACLE_TRACE_FILE`.
fn executeNativeTierOnDb(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    root_file_id: FileId,
    backend: codegen_abi.CodegenBackend,
    tier_tag: []const u8,
    options: DiffOracleOptions,
) DiffOracleError!OracleTierOutcome {
    const host_spec = backend.targetSpec();
    const seq_id = next_oracle_scratch_seq.fetchAdd(1, .monotonic);
    const scratch_dir = try std.fmt.allocPrint(
        allocator,
        ".zig-cache/cx_oracle_{s}_{d}",
        .{ tier_tag, seq_id },
    );
    defer allocator.free(scratch_dir);
    defer std.Io.Dir.cwd().deleteTree(options.io, scratch_dir) catch {};

    const exe_path = try std.fmt.allocPrint(
        allocator,
        "{s}/oracle_bin{s}",
        .{ scratch_dir, host_spec.executableExtension() },
    );
    defer allocator.free(exe_path);

    const trace_path = try std.fmt.allocPrint(allocator, "{s}/oracle.trace", .{scratch_dir});
    defer allocator.free(trace_path);

    var artifact = try db.compileModuleArtifact(root_file_id, backend, .{
        .module_name = tier_tag,
        .extra_file_ids = options.extra_file_ids,
        .vfs_source_map = options.vfs_source_map,
        .is_dev_got_enabled = false,
        .is_oracle_trace_enabled = true,
        .artifact_kind = .executable,
        .output_path = exe_path,
        .io = options.io,
        .environ_map = options.environ_map,
        .diagnostic_sink = options.diagnostic_sink,
    });
    defer artifact.deinit(allocator);

    var child_env = std.process.Environ.Map.init(allocator);
    defer child_env.deinit();
    if (options.environ_map) |parent_env| {
        var env_iter = parent_env.iterator();
        while (env_iter.next()) |entry| {
            try child_env.put(entry.key_ptr.*, entry.value_ptr.*);
        }
    }
    try child_env.put("COREX_ORACLE_TRACE_FILE", trace_path);

    const run_res = std.process.run(allocator, options.io, .{
        .argv = &.{exe_path},
        .environ_map = &child_env,
        .stdout_limit = .limited(MAX_CAPTURE_BYTES),
        .stderr_limit = .limited(MAX_CAPTURE_BYTES),
    }) catch return error.NativeExecutionFailed;
    errdefer {
        allocator.free(run_res.stdout);
        allocator.free(run_res.stderr);
    }

    const trace_bytes = std.Io.Dir.cwd().readFileAlloc(
        options.io,
        trace_path,
        allocator,
        .limited(MAX_CAPTURE_BYTES),
    ) catch try allocator.alloc(u8, 0);
    defer allocator.free(trace_bytes);

    var has_trapped = false;
    var exit_code: i32 = 0;
    var return_scalar_i64: i64 = 0;
    var drop_list: std.ArrayListUnmanaged(i64) = .empty;
    errdefer drop_list.deinit(allocator);

    try parseOracleTraceContents(
        allocator,
        trace_bytes,
        run_res.term,
        &has_trapped,
        &exit_code,
        &return_scalar_i64,
        &drop_list,
    );

    const owned_drops = if (drop_list.items.len > 0)
        try drop_list.toOwnedSlice(allocator)
    else blk: {
        drop_list.deinit(allocator);
        break :blk @as([]i64, &.{});
    };
    errdefer if (owned_drops.len > 0) allocator.free(owned_drops);

    const owned_stdout = if (run_res.stdout.len > 0) blk: {
        const duped = try allocator.dupe(u8, run_res.stdout);
        allocator.free(run_res.stdout);
        break :blk duped;
    } else blk: {
        allocator.free(run_res.stdout);
        break :blk @as([]u8, &.{});
    };
    errdefer if (owned_stdout.len > 0) allocator.free(owned_stdout);

    const owned_stderr = if (run_res.stderr.len > 0) blk: {
        const duped = try allocator.dupe(u8, run_res.stderr);
        allocator.free(run_res.stderr);
        break :blk duped;
    } else blk: {
        allocator.free(run_res.stderr);
        break :blk @as([]u8, &.{});
    };

    return .{
        .has_trapped = has_trapped,
        .exit_code = exit_code,
        .return_scalar_i64 = return_scalar_i64,
        .stdout_bytes = owned_stdout,
        .stderr_bytes = owned_stderr,
        .drop_trace = owned_drops,
    };
}

// ------------------- Monochrome Diff Table --------------------

/// Formats a compact, single-line preview of `raw_bytes` (escaping `\n`, `\r`, `\t`) into `out_buf`.
fn formatBytesCellSummary(allocator: std.mem.Allocator, raw_bytes: []const u8) ![]u8 {
    var out: std.ArrayListUnmanaged(u8) = .empty;
    errdefer out.deinit(allocator);
    try out.append(allocator, '"');
    var shown_count: usize = 0;
    for (raw_bytes) |byte_val| {
        if (shown_count >= 16) {
            try out.appendSlice(allocator, "…");
            break;
        }
        switch (byte_val) {
            '\n' => try out.appendSlice(allocator, "\\n"),
            '\r' => try out.appendSlice(allocator, "\\r"),
            '\t' => try out.appendSlice(allocator, "\\t"),
            0x20...0x7E => try out.append(allocator, byte_val),
            else => {
                var hex_buf: [4]u8 = undefined;
                const hex_s = std.fmt.bufPrint(&hex_buf, "\\x{x:0>2}", .{byte_val}) catch "";
                try out.appendSlice(allocator, hex_s);
            },
        }
        shown_count += 1;
    }
    try out.append(allocator, '"');
    return out.toOwnedSlice(allocator);
}

/// Formats `drops` (`[]const i64`) into a compact `[id0, id1, …]` summary cell.
fn formatDropsCellSummary(allocator: std.mem.Allocator, drops: []const i64) ![]u8 {
    var out: std.ArrayListUnmanaged(u8) = .empty;
    errdefer out.deinit(allocator);
    try out.append(allocator, '[');
    for (drops, 0..) |drop_val, idx| {
        if (idx >= 5) {
            try out.appendSlice(allocator, ", …");
            break;
        }
        if (idx > 0) try out.appendSlice(allocator, ", ");
        var num_buf: [32]u8 = undefined;
        try out.appendSlice(allocator, std.fmt.bufPrint(&num_buf, "{d}", .{drop_val}) catch "0");
    }
    try out.append(allocator, ']');
    return out.toOwnedSlice(allocator);
}

/// Appends `text` padded with trailing spaces to `col_width` display columns into `out`.
fn appendPaddedCell(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    text: []const u8,
    col_width: usize,
) !void {
    try out.appendSlice(allocator, text);
    const display_cols = countUtf8Codepoints(text);
    if (display_cols < col_width) {
        var pad_i: usize = 0;
        while (pad_i < col_width - display_cols) : (pad_i += 1) {
            try out.append(allocator, ' ');
        }
    }
}

/// Counts UTF-8 codepoints in `text` so monochrome Unicode glyphs (`✓`, `✗`, `…`) align to exact column widths.
fn countUtf8Codepoints(text: []const u8) usize {
    var count: usize = 0;
    var i: usize = 0;
    while (i < text.len) : (i += 1) {
        if ((text[i] & 0xC0) != 0x80) count += 1;
    }
    return count;
}

/// Appends `count` copies of horizontal box-drawing bar `─` (`U+2500`) into `out`.
fn appendHorizontalRule(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    count: usize,
) !void {
    var idx: usize = 0;
    while (idx < count) : (idx += 1) {
        try out.appendSlice(allocator, "─");
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Compares `outcomes` across all 4 tiers and renders a monochrome Unicode box-drawing diff table on mismatch.
pub fn compareOutcomesAndRenderTable(
    allocator: std.mem.Allocator,
    outcomes: *const [TIER_COUNT]OracleTierOutcome,
) !struct { is_all_matching: bool, rendered_table: []u8 } {
    const base = outcomes[0];
    if (base.eql(outcomes[1]) and base.eql(outcomes[2]) and base.eql(outcomes[3])) {
        return .{ .is_all_matching = true, .rendered_table = &.{} };
    }

    const row_names = [6][]const u8{
        "has_trapped",
        "exit_code",
        "return_i64",
        "stdout",
        "stderr",
        "drop_trace",
    };
    const row_matches = [6]bool{
        base.has_trapped == outcomes[1].has_trapped and
            base.has_trapped == outcomes[2].has_trapped and
            base.has_trapped == outcomes[3].has_trapped,
        base.exit_code == outcomes[1].exit_code and
            base.exit_code == outcomes[2].exit_code and
            base.exit_code == outcomes[3].exit_code,
        base.return_scalar_i64 == outcomes[1].return_scalar_i64 and
            base.return_scalar_i64 == outcomes[2].return_scalar_i64 and
            base.return_scalar_i64 == outcomes[3].return_scalar_i64,
        std.mem.eql(u8, base.stdout_bytes, outcomes[1].stdout_bytes) and
            std.mem.eql(u8, base.stdout_bytes, outcomes[2].stdout_bytes) and
            std.mem.eql(u8, base.stdout_bytes, outcomes[3].stdout_bytes),
        std.mem.eql(u8, base.stderr_bytes, outcomes[1].stderr_bytes) and
            std.mem.eql(u8, base.stderr_bytes, outcomes[2].stderr_bytes) and
            std.mem.eql(u8, base.stderr_bytes, outcomes[3].stderr_bytes),
        std.mem.eql(i64, base.drop_trace, outcomes[1].drop_trace) and
            std.mem.eql(i64, base.drop_trace, outcomes[2].drop_trace) and
            std.mem.eql(i64, base.drop_trace, outcomes[3].drop_trace),
    };

    var cells: [6][TIER_COUNT][]u8 = undefined;
    var init_rows: usize = 0;
    defer {
        var r_idx: usize = 0;
        while (r_idx < init_rows) : (r_idx += 1) {
            var c_idx: usize = 0;
            while (c_idx < TIER_COUNT) : (c_idx += 1) {
                allocator.free(cells[r_idx][c_idx]);
            }
        }
    }

    var row_i: usize = 0;
    while (row_i < 6) : (row_i += 1) {
        var col_i: usize = 0;
        while (col_i < TIER_COUNT) : (col_i += 1) {
            const tier_out = outcomes[col_i];
            cells[row_i][col_i] = switch (row_i) {
                0 => try allocator.dupe(u8, if (tier_out.has_trapped) "true" else "false"),
                1 => try std.fmt.allocPrint(allocator, "{d}", .{tier_out.exit_code}),
                2 => try std.fmt.allocPrint(allocator, "{d}", .{tier_out.return_scalar_i64}),
                3 => try formatBytesCellSummary(allocator, tier_out.stdout_bytes),
                4 => try formatBytesCellSummary(allocator, tier_out.stderr_bytes),
                5 => try formatDropsCellSummary(allocator, tier_out.drop_trace),
                else => unreachable,
            };
        }
        init_rows += 1;
    }

    const tier_ids = [TIER_COUNT]OracleTierId{ .pre_opt_vm, .post_opt_vm, .tier_a_c99, .tier_b_llvm };
    var col_widths: [TIER_COUNT + 2]usize = .{ 12, 6, 0, 0, 0, 0 };
    var tier_col: usize = 0;
    while (tier_col < TIER_COUNT) : (tier_col += 1) {
        var max_w = countUtf8Codepoints(tier_ids[tier_col].asColumnName());
        var r_idx: usize = 0;
        while (r_idx < 6) : (r_idx += 1) {
            max_w = @max(max_w, countUtf8Codepoints(cells[r_idx][tier_col]));
        }
        col_widths[2 + tier_col] = max_w;
    }

    var table_buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer table_buf.deinit(allocator);

    // Render top border (`╭───┬───╮`):
    try table_buf.appendSlice(allocator, "╭");
    for (col_widths, 0..) |width_val, w_idx| {
        if (w_idx > 0) try table_buf.appendSlice(allocator, "┬");
        try appendHorizontalRule(allocator, &table_buf, width_val + 2);
    }
    try table_buf.appendSlice(allocator, "╮\n");

    // Header row:
    try table_buf.appendSlice(allocator, "│ ");
    try appendPaddedCell(allocator, &table_buf, "Channel", col_widths[0]);
    try table_buf.appendSlice(allocator, " │ ");
    try appendPaddedCell(allocator, &table_buf, "Parity", col_widths[1]);
    for (tier_ids, 0..) |tid, t_idx| {
        try table_buf.appendSlice(allocator, " │ ");
        try appendPaddedCell(allocator, &table_buf, tid.asColumnName(), col_widths[2 + t_idx]);
    }
    try table_buf.appendSlice(allocator, " │\n");

    // Render header separator (`├───┼───┤`):
    try table_buf.appendSlice(allocator, "├");
    for (col_widths, 0..) |width_val, w_idx| {
        if (w_idx > 0) try table_buf.appendSlice(allocator, "┼");
        try appendHorizontalRule(allocator, &table_buf, width_val + 2);
    }
    try table_buf.appendSlice(allocator, "┤\n");

    // Data rows:
    row_i = 0;
    while (row_i < 6) : (row_i += 1) {
        try table_buf.appendSlice(allocator, "│ ");
        try appendPaddedCell(allocator, &table_buf, row_names[row_i], col_widths[0]);
        try table_buf.appendSlice(allocator, " │ ");
        const status_glyph = if (row_matches[row_i]) "✓" else "✗";
        try appendPaddedCell(allocator, &table_buf, status_glyph, col_widths[1]);
        var col_i: usize = 0;
        while (col_i < TIER_COUNT) : (col_i += 1) {
            try table_buf.appendSlice(allocator, " │ ");
            try appendPaddedCell(allocator, &table_buf, cells[row_i][col_i], col_widths[2 + col_i]);
        }
        try table_buf.appendSlice(allocator, " │\n");
    }

    // Render bottom border (`╰───┴───╯`):
    try table_buf.appendSlice(allocator, "╰");
    for (col_widths, 0..) |width_val, w_idx| {
        if (w_idx > 0) try table_buf.appendSlice(allocator, "┴");
        try appendHorizontalRule(allocator, &table_buf, width_val + 2);
    }
    try table_buf.appendSlice(allocator, "╯\n");

    return .{
        .is_all_matching = false,
        .rendered_table = try table_buf.toOwnedSlice(allocator),
    };
}

/// Runs the 4-tier differential backend oracle against `root_file_id` (and reachable modules) in `db`.
pub fn runFourTierDiffOracleOnDb(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    root_file_id: FileId,
    options: DiffOracleOptions,
) DiffOracleError!DiffOracleReport {
    const host_spec = TargetSpec.host();
    db.setTargetSpec(host_spec);
    db.setComptimeStepLimit(options.comptime_step_limit);
    if (options.workspace_root != null or options.virtual_files != null) {
        db.setEmbedSandbox(options.workspace_root, options.virtual_files);
    }
    db.setEmbedIo(options.io);

    var reachable_files: std.ArrayListUnmanaged(FileId) = .empty;
    defer reachable_files.deinit(allocator);
    try db.collectReachableModuleFiles(root_file_id, options.extra_file_ids, &reachable_files);

    // Validate front-end, SAST, and constant evaluation once before running all 4 tiers:
    var has_front_errors = false;
    for (reachable_files.items) |mod_fid| {
        if ((try db.parseCst(mod_fid)).diagnostics.hasErrors()) has_front_errors = true;
        if ((try db.resolveSignatures(mod_fid)).error_count > 0) has_front_errors = true;
        for ((try db.extractItemTree(mod_fid)).entries) |entry| {
            if ((try db.typecheckBody(entry.def_id)).error_count > 0) has_front_errors = true;
            if (!(try db.verifySastMir(entry.def_id)).is_verified_sound) has_front_errors = true;
            if (!has_front_errors and (entry.kind == .const_decl or entry.kind == .extern_block)) {
                const ct_art = db.evalComptimeDef(entry.def_id) catch |ct_err| switch (ct_err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.Cancelled => return error.Cancelled,
                    else => {
                        has_front_errors = true;
                        continue;
                    },
                };
                if (ct_art.has_errors) has_front_errors = true;
            }
        }
    }
    if (has_front_errors) return error.FrontendErrors;

    var outcomes: [TIER_COUNT]OracleTierOutcome = undefined;
    var completed_tiers: usize = 0;
    errdefer {
        var idx: usize = 0;
        while (idx < completed_tiers) : (idx += 1) {
            outcomes[idx].deinit(allocator);
        }
    }

    // [1] Execute Tier 1 post-SAST `--dev` (`D1`–`D5`) `MirVm`:
    outcomes[0] = try executeVmTierOnDb(
        allocator,
        db,
        root_file_id,
        reachable_files.items,
        false,
        host_spec,
        options,
    );
    completed_tiers = 1;

    // [2] Execute Tier 2 post-SAST `--release` (`D1`–`D5` + `R1`–`R6`) `MirVm`:
    outcomes[1] = try executeVmTierOnDb(
        allocator,
        db,
        root_file_id,
        reachable_files.items,
        true,
        host_spec,
        options,
    );
    completed_tiers = 2;

    // [3] Execute Tier 3 (`-ofmt=c`) ISO C99 -> `zig cc` native host executable:
    outcomes[2] = try executeNativeTierOnDb(
        allocator,
        db,
        root_file_id,
        .{
            .tier_a_c99 = .{
                .target = host_spec,
                .is_release_mode = false,
                .is_fuzz_instrumented = false,
                .has_line_directives = false,
            },
        },
        "tier_a_c99",
        options,
    );
    completed_tiers = 3;

    // [4] Execute Tier 4 (`LLVM 20–23`) `--release` (`-O2`) -> `zig cc` native host executable:
    outcomes[3] = try executeNativeTierOnDb(
        allocator,
        db,
        root_file_id,
        .{
            .tier_b_llvm = .{
                .target = host_spec,
                .opt_level = .release_fast_o2,
                .is_release_mode = true,
                .is_fuzz_instrumented = false,
            },
        },
        "tier_b_llvm",
        options,
    );
    completed_tiers = 4;

    const cmp_res = try compareOutcomesAndRenderTable(allocator, &outcomes);
    return .{
        .outcomes = outcomes,
        .is_all_matching = cmp_res.is_all_matching,
        .rendered_diff_table = cmp_res.rendered_table,
    };
}

/// Runs the 4-tier differential backend oracle on a single self-contained `.cx` `source_text` buffer.
pub fn runFourTierDiffOracle(
    allocator: std.mem.Allocator,
    source_text: []const u8,
    options: DiffOracleOptions,
) DiffOracleError!DiffOracleReport {
    var db = CompilerDb.init(allocator) catch return error.OutOfMemory;
    defer db.deinit();

    const root_file_id = FileId.fromInt(0);
    _ = try db.setInput(root_file_id, source_text, .low);
    return runFourTierDiffOracleOnDb(allocator, &db, root_file_id, options);
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_diff_oracle_monochrome_table_rendering_on_simulated_divergence" {
    const simulated = [TIER_COUNT]OracleTierOutcome{
        .{ .has_trapped = false, .exit_code = 42, .return_scalar_i64 = 42 },
        .{ .has_trapped = false, .exit_code = 42, .return_scalar_i64 = 42 },
        .{ .has_trapped = false, .exit_code = 42, .return_scalar_i64 = 42 },
        .{ .has_trapped = false, .exit_code = 99, .return_scalar_i64 = 99 },
    };

    const rendered = try compareOutcomesAndRenderTable(std.testing.allocator, &simulated);
    defer if (rendered.rendered_table.len > 0) std.testing.allocator.free(rendered.rendered_table);

    try std.testing.expect(!rendered.is_all_matching);
    try std.testing.expect(std.mem.indexOf(u8, rendered.rendered_table, "╭") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered.rendered_table, "│") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered.rendered_table, "├") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered.rendered_table, "╰") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered.rendered_table, "─") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered.rendered_table, "✓") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered.rendered_table, "✗") != null);
}

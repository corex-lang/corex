//! Unit Tests for Hybrid Steerable Wadler-Lindig Formatter (`tests/unit/fmt_engine_test.zig`)
//!
//! Exercises the 8-byte `DocInst` layout, `DocArena` $O(1)$ `flat_width` backpatching and `> 65,534`
//! byte chunking, `DocRenderer` `line_suffix` flushing, `DR-03` & `DR-14` Section 1.4 formatting rules,
//! 100% comment preservation, `// corex fmt: off` / `@fmt_off` suppression, `--fix` normalization, and
//! `corex fmt` CLI routing (`--check`, `--fix`, syntax error exit codes).
//!
//! - Guarantees `fmt(fmt(x)) == fmt(x)` idempotency and zero comment loss across all formatting modes.

const std = @import("std");
const corex = @import("corex");

const fmt_engine = corex.fmt_engine;
const router = corex.router;
const FileId = corex.FileId;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const AstArena = corex.AstArena;
const DocOp = corex.DocOp;
const GroupMode = corex.GroupMode;
const DocInst = corex.DocInst;
const DocArena = corex.DocArena;
const DocRenderer = corex.DocRenderer;
const FormatOptions = corex.FormatOptions;
const DiagnosticSink = corex.DiagnosticSink;

// -------------------------------------- INTERNALS --------------------------------------

/// Formats `source` with `options`, asserts zero syntax errors, and verifies `fmt(fmt(source)) == fmt(source)`.
fn expectCanonicalFormat(
    source: []const u8,
    expected_output: []const u8,
    options: FormatOptions,
) !void {
    var pass1 = try fmt_engine.formatSourceWithOptions(
        std.testing.allocator,
        source,
        FileId.fromInt(0),
        options,
    );
    defer pass1.deinit(std.testing.allocator);

    try std.testing.expect(!pass1.has_syntax_errors);
    try std.testing.expectEqualStrings(expected_output, pass1.formatted_text);

    // Verify 100% second-pass idempotency (`fmt(fmt(x)) == fmt(x)`):
    var pass2 = try fmt_engine.formatSourceWithOptions(
        std.testing.allocator,
        pass1.formatted_text,
        FileId.fromInt(0),
        options,
    );
    defer pass2.deinit(std.testing.allocator);

    try std.testing.expect(!pass2.has_syntax_errors);
    try std.testing.expect(!pass2.is_changed);
    try std.testing.expectEqualStrings(pass1.formatted_text, pass2.formatted_text);
}

// ------------------------------------- PUBLIC API --------------------------------------

// -------------- DocInst, DocArena & DocRenderer ---------------

test "test_fmt_doc_inst_layout_arena_backpatching_and_large_text_chunking" {
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(DocInst));
    try std.testing.expectEqual(@as(u8, 0), @backingInt(DocOp.nop));
    try std.testing.expectEqual(@as(u8, 1), @backingInt(DocOp.text));
    try std.testing.expectEqual(@as(u8, 2), @backingInt(DocOp.line));
    try std.testing.expectEqual(@as(u8, 8), @backingInt(DocOp.group_begin));
    try std.testing.expectEqual(@as(u8, 6), @backingInt(DocOp.indent));
    try std.testing.expectEqual(@as(u8, 7), @backingInt(DocOp.dedent));

    var arena = DocArena.init(std.testing.allocator);
    defer arena.deinit();

    // [1] Flat group width backpatching in $O(1)$ time:
    const flat_group_idx = try arena.beginGroup(.auto_fit);
    try arena.emitText("call(");
    try arena.emitSoftLine();
    try arena.emitText("arg_a,");
    try arena.emitLine();
    try arena.emitText("arg_b");
    try arena.emitIfBreak(",", "");
    try arena.emitSoftLine();
    try arena.emitText(")");
    try arena.endGroup();

    // "call(" (5) + "arg_a," (6) + " " (1) + "arg_b" (5) + ")" (1) = 18 columns:
    try std.testing.expectEqual(@as(u16, 18), arena.instructions.items[flat_group_idx].flat_width);

    // [2] Open-group poisoning via `.force_break`, `.hard_line`, `.blank_line`, and `.line_suffix`:
    const outer_group_idx = try arena.beginGroup(.auto_fit);
    const inner_forced_idx = try arena.beginGroup(.force_break);
    try arena.emitText("forced");
    try arena.endGroup();
    try arena.endGroup();
    try std.testing.expectEqual(fmt_engine.INF_WIDTH, arena.instructions.items[inner_forced_idx].flat_width);
    try std.testing.expectEqual(fmt_engine.INF_WIDTH, arena.instructions.items[outer_group_idx].flat_width);

    const suffix_group_idx = try arena.beginGroup(.auto_fit);
    try arena.emitText("stmt;");
    try arena.emitLineSuffix("// trailing comment");
    try arena.endGroup();
    try std.testing.expectEqual(fmt_engine.INF_WIDTH, arena.instructions.items[suffix_group_idx].flat_width);

    // [3] Chunking of text slices exceeding `MAX_TEXT_CHUNK_LEN` (`65,534` bytes):
    const large_len: usize = @as(usize, fmt_engine.MAX_TEXT_CHUNK_LEN) + 128;
    const large_buf = try std.testing.allocator.alloc(u8, large_len);
    defer std.testing.allocator.free(large_buf);
    @memset(large_buf, 'a');

    const inst_count_before = arena.instructions.items.len;
    try arena.emitText(large_buf);
    try std.testing.expectEqual(inst_count_before + 2, arena.instructions.items.len);
    try std.testing.expectEqual(
        fmt_engine.MAX_TEXT_CHUNK_LEN,
        arena.instructions.items[inst_count_before].flat_width,
    );
    try std.testing.expectEqual(
        @as(u16, 128),
        arena.instructions.items[inst_count_before + 1].flat_width,
    );
}

test "test_fmt_doc_renderer_line_suffix_flushing_and_zero_blank_line_whitespace" {
    var arena = DocArena.init(std.testing.allocator);
    defer arena.deinit();

    try arena.emitText("fn sample() {");
    try arena.beginIndent(4);
    try arena.emitHardLine();
    try arena.emitText("let first = 1;");
    try arena.emitLineSuffix("// comment one");
    try arena.emitBlankLine();
    try arena.emitBlankLine();
    try arena.emitText("let second = 2;");
    try arena.endIndent(4);
    try arena.emitHardLine();
    try arena.emitText("}");

    var renderer = DocRenderer.init(std.testing.allocator, fmt_engine.MAX_LINE_WIDTH);
    defer renderer.deinit();
    const rendered = try renderer.render(&arena);
    defer std.testing.allocator.free(rendered);

    // Verify `line_suffix` flushed before `\n\n` and zero trailing spaces exist on the blank line:
    try std.testing.expectEqualStrings(
        "fn sample() {\n" ++
            "    let first = 1; // comment one\n" ++
            "\n" ++
            "    let second = 2;\n" ++
            "}\n",
        rendered,
    );
}

// ----------- Top-Level Spacing, Use Sorting & Grids -----------

test "test_fmt_top_level_item_spacing_use_sorting_and_comment_preserving_use_trees" {
    // [1] Consecutive `use` items and single-line `const` items group tightly; functions/types have 1 blank line:
    const spacing_src =
        "use cx.io.{Write, self, Read, BufReader as Br};\n" ++
        "use cx.mem;\n" ++
        "const MIN_PORT: u16 = 80;\n" ++
        "const MAX_PORT: u16 = 8080;\n" ++
        "pub struct Endpoint {\n" ++
        "    pub port: u16,\n" ++
        "}\n" ++
        "pub fn default_endpoint() -> Endpoint {\n" ++
        "    return Endpoint { port: MIN_PORT };\n" ++
        "}\n";

    const spacing_expected =
        "use cx.io.{self, BufReader as Br, Read, Write};\n" ++
        "use cx.mem;\n\n" ++
        "const MIN_PORT: u16 = 80;\n" ++
        "const MAX_PORT: u16 = 8080;\n\n" ++
        "pub struct Endpoint {\n" ++
        "    pub port: u16,\n" ++
        "}\n\n" ++
        "pub fn default_endpoint() -> Endpoint {\n" ++
        "    return Endpoint { port: MIN_PORT };\n" ++
        "}\n";
    try expectCanonicalFormat(spacing_src, spacing_expected, .{});

    // [2] Braced `use` tree with trailing comma forces vertical break and sorts `self` first:
    const broken_use_src = "use cx.col.{HashSet, BTreeMap, self, Vec,};\n";
    const broken_use_expected =
        "use cx.col.{\n" ++
        "    self,\n" ++
        "    BTreeMap,\n" ++
        "    HashSet,\n" ++
        "    Vec,\n" ++
        "};\n";
    try expectCanonicalFormat(broken_use_src, broken_use_expected, .{});

    // [3] Braced `use` tree with attached comments preserves comments without losing trivia:
    const commented_use_src =
        "use cx.io.{\n" ++
        "    Write, // keep write comment\n" ++
        "    Read,\n" ++
        "};\n";
    try expectCanonicalFormat(commented_use_src, commented_use_src, .{});
}

test "test_fmt_steerable_lists_and_columnar_grid_literal_arrays" {
    // [1] Steerable struct literals and calls (`auto_fit` without trailing comma vs `force_break` with trailing comma):
    const steerable_src =
        "fn build() {\n" ++
        "    let flat_pt = Point { x: 1, y: 2 };\n" ++
        "    let broken_pt = Point {\n" ++
        "        x: 1,\n" ++
        "        y: 2,\n" ++
        "    };\n" ++
        "    let flat_call = connect(host, port);\n" ++
        "    let broken_call = connect(\n" ++
        "        host,\n" ++
        "        port,\n" ++
        "    );\n" ++
        "}\n";
    try expectCanonicalFormat(steerable_src, steerable_src, .{});

    // [2] `GroupMode.columnar_grid` for literal arrays with `> 8` elements:
    const grid_src =
        "fn table_lookup() {\n" ++
        "    let lut = [\n" ++
        "        0, 12, 255, 4, 64, 128, 9, 1024, 32, 7, 19, 88,\n" ++
        "    ];\n" ++
        "}\n";
    const grid_expected =
        "fn table_lookup() {\n" ++
        "    let lut = [\n" ++
        "           0,   12,  255,    4,   64,  128,    9, 1024,\n" ++
        "          32,    7,   19,   88,\n" ++
        "    ];\n" ++
        "}\n";
    try expectCanonicalFormat(grid_src, grid_expected, .{});
}

// ----------- Chains, Control Flow, Types & Patterns -----------

test "test_fmt_pipe_chains_method_chains_control_flow_parens_and_semicolons" {
    const src =
        "fn pipeline(raw_input: i32, items: &[i32]) -> i32 {\n" ++
        "    ;\n" ++
        "    let cleaned = raw_input\n" ++
        "        |> validate_bounds()\n" ++
        "        |> normalize_scale();\n" ++
        "    let total = items\n" ++
        "        .iter()\n" ++
        "        .filter_positive()\n" ++
        "        .fold_sum();\n" ++
        "    if (cleaned > 0) {\n" ++
        "        while (cleaned < 100) {\n" ++
        "            break;\n" ++
        "        };\n" ++
        "    };\n" ++
        "    for elem in (items) {\n" ++
        "        match (elem) {\n" ++
        "            0 => {},\n" ++
        "            _ => {},\n" ++
        "        };\n" ++
        "    };\n" ++
        "    loop {\n" ++
        "        break;\n" ++
        "    };\n" ++
        "    defer {\n" ++
        "        let done = 1;\n" ++
        "    };\n" ++
        "    return total;\n" ++
        "}\n";

    const expected =
        "fn pipeline(raw_input: i32, items: &[i32]) -> i32 {\n" ++
        "    let cleaned = raw_input\n" ++
        "        |> validate_bounds()\n" ++
        "        |> normalize_scale();\n" ++
        "    let total = items\n" ++
        "        .iter()\n" ++
        "        .filter_positive()\n" ++
        "        .fold_sum();\n" ++
        "    if cleaned > 0 {\n" ++
        "        while cleaned < 100 {\n" ++
        "            break;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    for elem in items {\n" ++
        "        match elem {\n" ++
        "            0 => {},\n" ++
        "            _ => {},\n" ++
        "        }\n" ++
        "    }\n" ++
        "    loop {\n" ++
        "        break;\n" ++
        "    }\n" ++
        "    defer {\n" ++
        "        let done = 1;\n" ++
        "    }\n" ++
        "    return total;\n" ++
        "}\n";
    try expectCanonicalFormat(src, expected, .{});
}

test "test_fmt_advanced_declarations_function_types_unary_ops_and_patterns" {
    const src =
        "unsafe impl Sync for SharedBuffer {}\n\n" ++
        "pub comptime fn compute_table_len(base: usize) -> usize {\n" ++
        "    return base * 2;\n" ++
        "}\n\n" ++
        "type UnsafeHandler = unsafe fn(code: i32, flags: u32) -> i32;\n" ++
        "type AsyncWorker = async fn(task_id: u64) -> u32!IoError;\n\n" ++
        "impl Matrix {\n" ++
        "    pub subscript(row_idx: usize, col_idx: usize) -> &[f64] {\n" ++
        "        let {\n" ++
        "            yield self.rows;\n" ++
        "        }\n" ++
        "    }\n\n" ++
        "    pub subscript(idx: usize) -> f64 {\n" ++
        "        let {\n" ++
        "            yield 0.0;\n" ++
        "        }\n" ++
        "        inout {\n" ++
        "            yield &mut self.slot;\n" ++
        "        }\n" ++
        "    }\n" ++
        "}\n\n" ++
        "pub fn inspect_pattern(pt: Point, role: Role, flag: bool) -> i32 {\n" ++
        "    let inv_flag = not flag;\n" ++
        "    let neg_x = -pt.x;\n" ++
        "    let double_neg = - -neg_x;\n" ++
        "    match pt {\n" ++
        "        Point { x, y, .. } => x + y,\n" ++
        "    }\n" ++
        "    return match role {\n" ++
        "        .Auditor { department_id } => department_id,\n" ++
        "        .Ok(val) => val,\n" ++
        "        _ => double_neg,\n" ++
        "    };\n" ++
        "}\n";

    try expectCanonicalFormat(src, src, .{});

    const dr21_fmt_src =
        "pub fn is_empty_slice(buf: &[u8]) -> bool = buf.len() == 0;\n\n" ++
        "pub fn scan_tail(frame: &[u8], hdr_len: usize, scratch: &mut Arena) -> u8 {\n" ++
        "    if (rem := frame.len()) >= 4 {\n" ++
        "        let head = frame[..$-4];\n" ++
        "        let dyn_tail = frame[..$ - hdr_len];\n" ++
        "        let found: u8 = search: for byte_val, idx in head {\n" ++
        "            if idx > 0 and byte_val != dyn_tail[0] {\n" ++
        "                break :search byte_val;\n" ++
        "            }\n" ++
        "        } orelse return 0;\n" ++
        "        with context.allocator = &mut scratch {\n" ++
        "            return found + (rem as u8);\n" ++
        "        }\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";
    try expectCanonicalFormat(dr21_fmt_src, dr21_fmt_src, .{});
}

// ---------- Comments, Directives & Fix Normalization ----------

test "test_fmt_comment_preservation_empty_containers_and_fmt_off_directives" {
    const src =
        "/# Module-level doc comment\n\n" ++
        "// Leading file comment\n" ++
        "pub struct EmptyStruct {\n" ++
        "    // Dangling comment inside empty struct braces\n" ++
        "}\n\n" ++
        "pub fn empty_containers(\n" ++
        "    // Dangling comment inside empty parameter list\n" ++
        ") {\n" ++
        "    let empty_arr = [\n" ++
        "        // Dangling comment inside empty array brackets\n" ++
        "    ];\n" ++
        "    let empty_call = invoke(\n" ++
        "        // Dangling comment inside empty call parens\n" ++
        "    );\n" ++
        "}\n\n" ++
        "// corex fmt: off\n" ++
        "const   UNFORMATTED_MATRIX:   [i32; 4] = [ 1,   2,  3,    4 ];\n" ++
        "// corex fmt: on\n\n" ++
        "@fmt_off\n" ++
        "const   ATTR_SUPPRESSED:  i32  =   99;\n" ++
        "// Trailing EOF comment\n";

    try expectCanonicalFormat(src, src, .{});
}

test "test_fmt_fix_mode_casing_helpers_role_isolation_and_missing_semicolons" {
    // [1] Standalone casing helpers (`toPascalCase`, `toSnakeCase`, `toScreamingSnakeCase`):
    const pascal = try fmt_engine.toPascalCase(std.testing.allocator, "http_request_header");
    defer std.testing.allocator.free(pascal);
    try std.testing.expectEqualStrings("HttpRequestHeader", pascal);

    const snake = try fmt_engine.toSnakeCase(std.testing.allocator, "ComputeFrameChecksum");
    defer std.testing.allocator.free(snake);
    try std.testing.expectEqualStrings("compute_frame_checksum", snake);

    const screaming = try fmt_engine.toScreamingSnakeCase(std.testing.allocator, "maxRetryCount");
    defer std.testing.allocator.free(screaming);
    try std.testing.expectEqualStrings("MAX_RETRY_COUNT", screaming);

    // [2] `--fix` mode with role-scoped renaming (type `packet` -> `Packet` vs param `packet` -> `packet`)
    // and missing semicolon insertion:
    const unfixed_src =
        "const default_timeout: u32 = 500\n\n" ++
        "pub struct packet {\n" ++
        "    pub PayloadLen: u32,\n" ++
        "}\n\n" ++
        "pub enum conn_state {\n" ++
        "    idle_state,\n" ++
        "    active_state(u32),\n" ++
        "}\n\n" ++
        "pub fn SendPacket(packet: packet) -> u32 {\n" ++
        "    let TotalWait = packet.PayloadLen + default_timeout\n" ++
        "    return TotalWait\n" ++
        "}\n";

    const fixed_expected =
        "const DEFAULT_TIMEOUT: u32 = 500;\n\n" ++
        "pub struct Packet {\n" ++
        "    pub payload_len: u32,\n" ++
        "}\n\n" ++
        "pub enum ConnState {\n" ++
        "    IdleState,\n" ++
        "    ActiveState(u32),\n" ++
        "}\n\n" ++
        "pub fn send_packet(packet: Packet) -> u32 {\n" ++
        "    let total_wait = packet.payload_len + DEFAULT_TIMEOUT;\n" ++
        "    return total_wait;\n" ++
        "}\n";

    try expectCanonicalFormat(unfixed_src, fixed_expected, .{ .is_fix_mode = true });

    // [3] Direct `formatTokensAndCst` invocation on pre-parsed buffers:
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();

    _ = try corex.parseSource(
        fixed_expected,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        null,
        null,
    );
    var pre_parsed_res = try fmt_engine.formatTokensAndCst(
        std.testing.allocator,
        fixed_expected,
        &token_buf,
        &cst_arena,
        .{},
    );
    defer pre_parsed_res.deinit(std.testing.allocator);
    try std.testing.expect(!pre_parsed_res.is_changed);
    try std.testing.expectEqualStrings(fixed_expected, pre_parsed_res.formatted_text);
}

// ------------- CLI Router Integration (corex fmt) -------------

test "test_fmt_cli_router_check_fix_and_error_handling" {
    var out_buf: [4096]u8 = undefined;
    var err_buf: [4096]u8 = undefined;

    // [1] `corex fmt` with `0` files succeeds with exit code `0`:
    var out_writer = std.Io.Writer.fixed(&out_buf);
    var err_writer = std.Io.Writer.fixed(&err_buf);
    const zero_files_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{ "--color=never", "fmt" },
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 0), zero_files_exit);
    try std.testing.expectEqualStrings(
        "✓ fmt: CoreX source files formatted canonically\n",
        out_writer.buffered(),
    );

    // [2] Write a temporary `.cx` file to test `fmt --check`, `fmt --fix`, and `fmt` on syntax errors:
    const tmp_path = ".zig-cache/tmp_fmt_cli_test.cx";
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, tmp_path) catch {};

    try std.Io.Dir.cwd().writeFile(std.testing.io, .{
        .sub_path = tmp_path,
        .data = "const   UNFORMATTED_CONST:  i32  =   10;\n",
    });

    // `corex fmt --check` on unformatted file returns exit code `1`:
    out_writer = std.Io.Writer.fixed(&out_buf);
    err_writer = std.Io.Writer.fixed(&err_buf);
    const check_fail_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{ "--color=never", "fmt", "--check", tmp_path },
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 1), check_fail_exit);
    try std.testing.expect(std.mem.indexOf(u8, err_writer.buffered(), "✗ fmt --check:") != null);

    // `corex fmt --fix` rewrites a file with non-standard casing & missing `;` and returns exit code `0`:
    try std.Io.Dir.cwd().writeFile(std.testing.io, .{
        .sub_path = tmp_path,
        .data = "const bad_const: i32 = 10\nfn BadFn( ) -> i32 { return bad_const }\n",
    });
    out_writer = std.Io.Writer.fixed(&out_buf);
    err_writer = std.Io.Writer.fixed(&err_buf);
    const fix_ok_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{ "--color=never", "fmt", "--fix", tmp_path },
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 0), fix_ok_exit);

    // Subsequent `corex fmt --check` on the formatted file returns exit code `0`:
    out_writer = std.Io.Writer.fixed(&out_buf);
    err_writer = std.Io.Writer.fixed(&err_buf);
    const check_pass_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{ "--color=never", "fmt", "--check", tmp_path },
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 0), check_pass_exit);

    // [3] `corex fmt` on a file with blocking syntax errors returns exit code `1` without corrupting file:
    try std.Io.Dir.cwd().writeFile(std.testing.io, .{
        .sub_path = tmp_path,
        .data = "fn broken_syntax( { let x = ; }\n",
    });
    out_writer = std.Io.Writer.fixed(&out_buf);
    err_writer = std.Io.Writer.fixed(&err_buf);
    const syntax_err_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{ "--color=never", "fmt", tmp_path },
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 1), syntax_err_exit);
    try std.testing.expect(std.mem.indexOf(u8, err_writer.buffered(), "✗ fmt: syntax errors in") != null);

    // [4] Rejecting `--check` and `--fix` on non-`fmt` subcommands (`E0001`):
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    const bad_check = try router.parseArgs(&.{ "check", "--check" }, &sink);
    try std.testing.expectEqual(router.CommandAction.invalid, bad_check.action);
    try std.testing.expect(sink.hasErrors());
}

test "test_fmt_struct_payload_variant_cond_parens_and_columnar_grid_idempotency" {
    // [1] Preserve mandatory parens around brace-carrying `.variant_pat` and `.contextual_variant_expr`:
    const variant_brace_cond_src =
        "fn handle_event(ev: Event) -> i32 {\n" ++
        "    if ev is (.Click { x }) {\n" ++
        "        return x;\n" ++
        "    }\n" ++
        "    if ev is (Event.Click { x }) {\n" ++
        "        return x;\n" ++
        "    }\n" ++
        "    if (ev == .Click { x: 10 }) {\n" ++
        "        return 1;\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";
    try expectCanonicalFormat(variant_brace_cond_src, variant_brace_cond_src, .{});

    // Verify the formatted output re-parses with zero syntax errors:
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var parse_sink = DiagnosticSink.init(std.testing.allocator);
    defer parse_sink.deinit();
    _ = try corex.parseSource(
        variant_brace_cond_src,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &parse_sink,
        null,
    );
    try std.testing.expectEqual(@as(u32, 0), parse_sink.error_count);

    // [2] 9-element >100-col scalar array literal without trailing comma is idempotent on Pass 1 & Pass 2:
    const long_nine_elem_src =
        "fn thresholds() {\n" ++
        "    let limits = [1000000001, 1000000002, 1000000003, 1000000004, " ++
        "1000000005, 1000000006, 1000000007, 1000000008, 1000000009];\n" ++
        "}\n";
    var grid_pass1 = try fmt_engine.formatSourceWithOptions(
        std.testing.allocator,
        long_nine_elem_src,
        FileId.fromInt(0),
        .{},
    );
    defer grid_pass1.deinit(std.testing.allocator);
    try std.testing.expect(!grid_pass1.has_syntax_errors);

    var grid_pass2 = try fmt_engine.formatSourceWithOptions(
        std.testing.allocator,
        grid_pass1.formatted_text,
        FileId.fromInt(0),
        .{},
    );
    defer grid_pass2.deinit(std.testing.allocator);
    try std.testing.expect(!grid_pass2.has_syntax_errors);
    try std.testing.expect(!grid_pass2.is_changed);
    try std.testing.expectEqualStrings(grid_pass1.formatted_text, grid_pass2.formatted_text);

    // [3] Expression-bodied functions with trailing comments and `.invalid_token` handling:
    const expr_body_comment_src = "fn answer() -> i32 = 42; // trailing answer comment\n";
    try expectCanonicalFormat(expr_body_comment_src, expr_body_comment_src, .{});

    var invalid_tok_res = try fmt_engine.formatSourceWithOptions(
        std.testing.allocator,
        "fn broken() -> i32 = @;\n",
        FileId.fromInt(0),
        .{},
    );
    defer invalid_tok_res.deinit(std.testing.allocator);
    try std.testing.expect(invalid_tok_res.has_syntax_errors);
}

test "test_fmt_preserves_comments_across_slot14_coalesced_trivia" {
    const coalesced_header_src =
        "/# Line 1 of module header\n" ++
        "/# Line 2 of module header\n" ++
        "/# Line 3 of module header\n" ++
        "/# Line 4 of module header\n" ++
        "/# Line 5 of module header\n" ++
        "/# Line 6 of module header\n" ++
        "/# Line 7 of module header\n" ++
        "\n" ++
        "// ------------------------------------- PUBLIC API --------------------------------------\n" ++
        "\n" ++
        "/| Triggers an immediate hardware trap without losing slot-14 coalesced comments.\n" ++
        "@cold\n" ++
        "pub fn trap() -> never {\n" ++
        "    @trap();\n" ++
        "}\n";
    const expected_canonical_src =
        "/# Line 1 of module header\n" ++
        "/# Line 2 of module header\n" ++
        "/# Line 3 of module header\n" ++
        "/# Line 4 of module header\n" ++
        "/# Line 5 of module header\n" ++
        "/# Line 6 of module header\n" ++
        "/# Line 7 of module header\n\n" ++
        "// ------------------------------------- PUBLIC API --------------------------------------\n" ++
        "/| Triggers an immediate hardware trap without losing slot-14 coalesced comments.\n" ++
        "@cold\n" ++
        "pub fn trap() -> never {\n" ++
        "    @trap();\n" ++
        "}\n";
    try expectCanonicalFormat(coalesced_header_src, expected_canonical_src, .{});
}

test "test_fmt_dr22_type_canonicalization_multiline_strings_and_attributes" {
    const uncanonical_src =
        "pub(pkg) extern \"c\" fn printf(fmt: *u8, ...) -> i32;\n\n" ++
        "@no_panic\n" ++
        "@cfg(os == \"windows\")\n" ++
        "@inline\n" ++
        "@no_alloc\n" ++
        "pub(super) fn normalize(\n" ++
        "    opt_val: Option[u32],\n" ++
        "    res_val: Result[u32, IoError],\n" ++
        "    /,\n" ++
        "    *,\n" ++
        "    out_slot: &out u64,\n" ++
        ") -> unit {\n" ++
        "    let count = 42u64;\n" ++
        "    let ratio = 0.5f32;\n" ++
        "    let raw_p = &raw mut out_slot;\n" ++
        "    out_slot.* = raw_p.* + count + (ratio as u64);\n" ++
        "    let updated = Config { enabled: true, ..own base_cfg };\n" ++
        "  let msg = \"\n" ++
        "  line one\n" ++
        "    line two\n" ++
        "  \";\n" ++
        "    _ = (opt_val, res_val, updated, msg);\n" ++
        "    fsm: match state {\n" ++
        "        0 => continue :fsm 1,\n" ++
        "        _ => {},\n" ++
        "    }\n" ++
        "}\n";

    var pass1 = try fmt_engine.formatSource(std.testing.allocator, uncanonical_src, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);
    try std.testing.expect(!pass1.has_syntax_errors);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "pub(pkg) extern \"C\" fn printf(fmt: *u8, ...) -> i32;") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, pass1.formatted_text, "@cfg(os == \"windows\") @inline @no_alloc @no_panic\npub(super) fn normalize(") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "opt_val: u32?,") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "res_val: u32!IoError,") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "out_slot: &out u64,\n) {\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "let count = 42_u64;") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "let ratio = 0.5_f32;") != null);
    try std.testing.expect(std.mem.indexOf(u8, pass1.formatted_text, "..own base_cfg") != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        pass1.formatted_text,
        "    let msg = \"\n    line one\n      line two\n    \";\n",
    ) != null);

    try expectCanonicalFormat(pass1.formatted_text, pass1.formatted_text, .{});

    // `@constructor` and `@builder_item` functions preserve `PascalCase` with zero `W0201` warnings (`SE-22`):
    const pascal_exempt_src =
        "@constructor\n" ++
        "pub fn Button(label: str) -> i32 {\n" ++
        "    _ = label;\n" ++
        "    return 1;\n" ++
        "}\n\n" ++
        "@builder_item\n" ++
        "pub fn TextRow(scope: &mut i32, count: i32) {\n" ++
        "    scope.* += count;\n" ++
        "}\n";
    var exempt_tok = TokenBuffer.init(std.testing.allocator);
    defer exempt_tok.deinit();
    var exempt_cst = LosslessCstArena.init(std.testing.allocator);
    defer exempt_cst.deinit();
    var exempt_ast = AstArena.init(std.testing.allocator);
    defer exempt_ast.deinit();
    var exempt_sink = DiagnosticSink.init(std.testing.allocator);
    defer exempt_sink.deinit();
    _ = try corex.parseSource(
        pascal_exempt_src,
        FileId.fromInt(0),
        &exempt_tok,
        &exempt_cst,
        &exempt_ast,
        &exempt_sink,
        null,
    );
    try std.testing.expectEqual(@as(usize, 0), exempt_sink.diagnostics.items.len);
    try expectCanonicalFormat(pascal_exempt_src, pascal_exempt_src, .{ .is_fix_mode = true });
}

test "test_fmt_dr23_doc_spacing_fenced_blocks_and_fix_healing" {
    // [1] `corex fmt` normalizes `/|Summary` -> `/| Summary`, preserves indented & fenced ```` ```cx ```` blocks,
    // strips trailing spaces on empty `/|` / `/#` lines, and inserts 1 blank line after `/#`:
    const unspaced_doc_src =
        "/#Tight module header\n" ++
        "/#   \n" ++
        "/#Second header line\n" ++
        "/|Summary without leading space.\n" ++
        "/|   \n" ++
        "/|     indented list item stays aligned\n" ++
        "/| ```cx\n" ++
        "/| let raw = \"\n" ++
        "/|     kept verbatim\n" ++
        "/|     \";\n" ++
        "/| _ = raw;\n" ++
        "/| ```\n" ++
        "pub fn documented_api(seed: u32) -> u32 {\n" ++
        "    _ = seed;\n" ++
        "    return 42_u32;\n" ++
        "}\n";

    const expected_doc_src =
        "/# Tight module header\n" ++
        "/#\n" ++
        "/# Second header line\n\n" ++
        "/| Summary without leading space.\n" ++
        "/|\n" ++
        "/|     indented list item stays aligned\n" ++
        "/| ```cx\n" ++
        "/| let raw = \"\n" ++
        "/|     kept verbatim\n" ++
        "/|     \";\n" ++
        "/| _ = raw;\n" ++
        "/| ```\n" ++
        "pub fn documented_api(seed: u32) -> u32 {\n" ++
        "    _ = seed;\n" ++
        "    return 42_u32;\n" ++
        "}\n";

    try expectCanonicalFormat(unspaced_doc_src, expected_doc_src, .{});

    // [2] `corex fmt --fix` heals `/** … */` / `//!` / `///` (`E0118`), detached `/|` (`E0230`), and `let _ =` (`E0234`):
    const unhealed_src =
        "//! Legacy module header.\n\n" ++
        "/**\n" ++
        " * Block comment healed to line comment.\n" ++
        " */\n" ++
        "pub struct Counter {\n" ++
        "    pub count: u32,\n" ++
        "}\n\n" ++
        "/| Detached doc comment healed by removing blank line.\n\n" ++
        "pub fn reset_counter(val: u32) -> u32 {\n" ++
        "    let _ = val;\n" ++
        "    return 0_u32;\n" ++
        "}\n";

    var healed_pass1 = try fmt_engine.formatSourceWithOptions(
        std.testing.allocator,
        unhealed_src,
        FileId.fromInt(0),
        .{ .is_fix_mode = true },
    );
    defer healed_pass1.deinit(std.testing.allocator);
    try std.testing.expect(healed_pass1.is_changed);
    try std.testing.expect(std.mem.indexOf(u8, healed_pass1.formatted_text, "/**") == null);
    try std.testing.expect(std.mem.indexOf(u8, healed_pass1.formatted_text, "/# Legacy module header.\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, healed_pass1.formatted_text, "// Block comment healed to line comment.") != null);
    try std.testing.expect(
        std.mem.indexOf(
            u8,
            healed_pass1.formatted_text,
            "/| Detached doc comment healed by removing blank line.\npub fn reset_counter",
        ) != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, healed_pass1.formatted_text, "let _ =") == null);
    try std.testing.expect(std.mem.indexOf(u8, healed_pass1.formatted_text, "    _ = val;\n") != null);

    var healed_pass2 = try fmt_engine.formatSourceWithOptions(
        std.testing.allocator,
        healed_pass1.formatted_text,
        FileId.fromInt(0),
        .{},
    );
    defer healed_pass2.deinit(std.testing.allocator);
    try std.testing.expect(!healed_pass2.has_syntax_errors);
    try std.testing.expect(!healed_pass2.is_changed);
    try std.testing.expectEqualStrings(healed_pass1.formatted_text, healed_pass2.formatted_text);
}

// ----------- DR-24 Packing, Inline If & Fmt Strings -----------

test "test_fmt_dr24_horizontal_attr_packing_repr_link_inline_if_and_fmt_holes" {
    const raw_dr24_src =
        "/# DR-24 formatter verification.\n" ++
        "@derive(Copy, Debug)\n" ++
        "@repr(zero_pad: true, align: .CacheLine, C)\n" ++
        "@cfg(target_os: \"linux\")\n" ++
        "pub struct SlabHeader {\n" ++
        "    /| Cache-aligned DMA pointer.\n" ++
        "    pub dma_addr: u64,\n" ++
        "}\n\n" ++
        "@must_use\n" ++
        "@no_panic\n" ++
        "@no_alloc\n" ++
        "@link(section: \".text.hot\", name: \"cx_classify_tier\")\n" ++
        "@cfg(target_os: \"linux\")\n" ++
        "@allow(W0202)\n" ++
        "pub fn classify(byte_len: u32, flags: u16, healthy: bool) -> str {\n" ++
        "    let tier = if byte_len == 0_u32 => 0_u16 else if (flags & 1_u16) != 0_u16 => 2_u16 else 1_u16;\n" ++
        "    return f\"st={if healthy =>  \"UP\"  else  \"DOWN\"} tier={ tier = :#06x}\";\n" ++
        "}\n";

    var pass1 = try fmt_engine.formatSource(std.testing.allocator, raw_dr24_src, FileId.fromInt(0));
    defer pass1.deinit(std.testing.allocator);
    try std.testing.expect(!pass1.has_syntax_errors);
    try std.testing.expect(pass1.is_changed);

    // Comment-free `@attr` group with `indent + flat_width <= 100` packs on 1 line in canonical Tier 1->4 order:
    try std.testing.expect(std.mem.indexOf(
        u8,
        pass1.formatted_text,
        "@cfg(target_os: \"linux\") @repr(C, align: .CacheLine, zero_pad: true) @derive(Copy, Debug)\n" ++
            "pub struct SlabHeader",
    ) != null);
    // `> 100`-col `@attr` stack breaks parameterized attributes per line while packing Tier-4 markers on the final line:
    try std.testing.expect(std.mem.indexOf(
        u8,
        pass1.formatted_text,
        "@cfg(target_os: \"linux\")\n" ++
            "@allow(W0202)\n" ++
            "@link(name: \"cx_classify_tier\", section: \".text.hot\")\n" ++
            "@no_alloc @no_panic @must_use\n" ++
            "pub fn classify(",
    ) != null);
    // Chained `if … => … else if … => … else …` indents `+4` and `f"…"` inner holes format canonically:
    try std.testing.expect(std.mem.indexOf(
        u8,
        pass1.formatted_text,
        "    let tier = if byte_len == 0_u32 => 0_u16\n" ++
            "        else if (flags & 1_u16) != 0_u16 => 2_u16\n" ++
            "        else 1_u16;\n",
    ) != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        pass1.formatted_text,
        "    return f\"st={if healthy => \"UP\" else \"DOWN\"} tier={tier=:#06x}\";\n",
    ) != null);

    try expectCanonicalFormat(pass1.formatted_text, pass1.formatted_text, .{});
}

test "test_fmt_multiline_string_spaces_only_blank_lines_dedent_and_line_budget_guard" {
    // [1] Over-indented multiline string (`12`-space closing `"`) with a `2`-space blank middle line dedents to col `4` with `""`:
    const overindented_multiline_src =
        "pub fn build_banner() -> str {\n" ++
        "            let banner = \"\n" ++
        "            header line\n" ++
        "  \n" ++
        "              indented detail\n" ++
        "      \r\n" ++
        "            \";\n" ++
        "            return banner;\n" ++
        "}\n";

    const expected_multiline_src =
        "pub fn build_banner() -> str {\n" ++
        "    let banner = \"\n" ++
        "    header line\n" ++
        "\n" ++
        "      indented detail\n" ++
        "\n" ++
        "    \";\n" ++
        "    return banner;\n" ++
        "}\n";

    try expectCanonicalFormat(overindented_multiline_src, expected_multiline_src, .{});

    // [2] `fitsInlineFatArrowIfLineBudget` rejects `> 100`-col inline arms (`4 + 11 + 86 == 101`) while allowing `<= 100`:
    const long_if_src =
        "pub fn calc(flag: bool) -> i32 {\n" ++
        "    if flag {\n" ++
        "        compute_weighted_metric_value(alpha_factor, beta_factor, gamma_factor, delta_weight_0)\n" ++
        "    } else {\n" ++
        "        0\n" ++
        "    }\n" ++
        "}\n";
    const if_offset: u32 = @intCast(std.mem.indexOf(u8, long_if_src, "if flag").?);
    const if_end: u32 = @intCast(std.mem.lastIndexOfScalar(u8, long_if_src[0 .. long_if_src.len - 2], '}').? + 1);
    const long_arm = "compute_weighted_metric_value(alpha_factor, beta_factor, gamma_factor, delta_weight_0)";
    try std.testing.expectEqual(@as(usize, 86), long_arm.len);

    try std.testing.expect(!(try fmt_engine.fitsInlineFatArrowIfLineBudget(
        std.testing.allocator,
        long_if_src,
        if_offset,
        if_end,
        &.{"flag"},
        &.{ long_arm, "0" },
        false,
        false,
    )));
    try std.testing.expect(try fmt_engine.fitsInlineFatArrowIfLineBudget(
        std.testing.allocator,
        long_if_src,
        if_offset,
        if_end,
        &.{"flag"},
        &.{ "compute_weighted_metric_value(alpha_factor, beta_factor)", "0" },
        false,
        false,
    ));
}

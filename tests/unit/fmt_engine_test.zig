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
        "use std::io::{Write, self, Read, BufReader as Br};\n" ++
        "use core::mem;\n" ++
        "const MIN_PORT: u16 = 80;\n" ++
        "const MAX_PORT: u16 = 8080;\n" ++
        "pub struct Endpoint {\n" ++
        "    pub port: u16,\n" ++
        "}\n" ++
        "pub fn default_endpoint() -> Endpoint {\n" ++
        "    return Endpoint { port: MIN_PORT };\n" ++
        "}\n";

    const spacing_expected =
        "use std::io::{self, BufReader as Br, Read, Write};\n" ++
        "use core::mem;\n\n" ++
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
    const broken_use_src = "use std::collections::{HashSet, BTreeMap, self, Vec,};\n";
    const broken_use_expected =
        "use std::collections::{\n" ++
        "    self,\n" ++
        "    BTreeMap,\n" ++
        "    HashSet,\n" ++
        "    Vec,\n" ++
        "};\n";
    try expectCanonicalFormat(broken_use_src, broken_use_expected, .{});

    // [3] Braced `use` tree with attached comments preserves comments without losing trivia:
    const commented_use_src =
        "use std::io::{\n" ++
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
        "type AsyncWorker = async fn(task_id: u64) -> Result[u32, IoError];\n\n" ++
        "impl Matrix {\n" ++
        "    pub subscript row_slice(row_idx: usize) -> &[f64] {\n" ++
        "        return self.rows;\n" ++
        "    }\n\n" ++
        "    pub subscript(idx: usize) -> f64 {\n" ++
        "        return 0.0;\n" ++
        "    }\n" ++
        "}\n\n" ++
        "pub fn inspect_pattern(pt: Point, role: Role, flag: bool) -> i32 {\n" ++
        "    let inv_flag = !flag;\n" ++
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
}

// ---------- Comments, Directives & Fix Normalization ----------

test "test_fmt_comment_preservation_empty_containers_and_fmt_off_directives" {
    const src =
        "//! Module-level doc comment\n" ++
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

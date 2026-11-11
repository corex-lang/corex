//! Unit Tests for Diagnostic Catalog, Patcher & Renderer (`tests/unit/diagnostic_test.zig`)
//!
//! Verifies `DiagnosticCode` catalog lookups, `DiagnosticSink` 100-error cap and arena cloning,
//! `TransactionalPatcher` interval scheduling and byte splicing, and `DiagnosticRenderer` output.
//!
//! Covers single-line, multi-line elided (`┆`), cross-file stitched (`├─▸`), and diff-preview diagnostics.

const std = @import("std");
const corex = @import("corex");

const diag = corex.diagnostic;
const FileId = corex.FileId;
const Span = corex.Span;
const StringInterner = corex.StringInterner;
const VfsSourceMap = corex.VfsSourceMap;
const StyleConfig = corex.StyleConfig;
const Severity = corex.Severity;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticSink = corex.DiagnosticSink;
const LabeledSpan = corex.LabeledSpan;
const SuggestedFix = corex.SuggestedFix;
const TextEdit = corex.TextEdit;
const TransactionalPatcher = corex.TransactionalPatcher;
const DiagnosticRenderer = corex.DiagnosticRenderer;

// ------------------------------------- PUBLIC API --------------------------------------

// -------------- Severity & Catalog Lookup Tests ---------------

test "test_diagnostic_severity_and_catalog_code_resolution" {
    try std.testing.expectEqualStrings("error", Severity.err.asLabel());
    try std.testing.expectEqualStrings("warning", Severity.warning.asLabel());
    try std.testing.expectEqualStrings("note", Severity.info.asLabel());
    try std.testing.expectEqualStrings("help", Severity.help.asLabel());

    try std.testing.expectEqual(DiagnosticCode.e0302_use_after_move, DiagnosticCode.fromCodeStr("E0302").?);
    try std.testing.expectEqual(DiagnosticCode.e0503_forbidden_comptime_operation, DiagnosticCode.fromCodeStr("E0503").?);
    try std.testing.expectEqual(DiagnosticCode.e0504_comptime_out_of_bounds, DiagnosticCode.fromCodeStr("E0504").?);
    try std.testing.expectEqual(DiagnosticCode.e0505_comptime_uninitialized_read, DiagnosticCode.fromCodeStr("E0505").?);
    try std.testing.expectEqual(DiagnosticCode.e0506_comptime_invalid_pointer, DiagnosticCode.fromCodeStr("E0506").?);
    try std.testing.expectEqual(DiagnosticCode.e0507_comptime_arithmetic_trap, DiagnosticCode.fromCodeStr("E0507").?);
    try std.testing.expectEqual(DiagnosticCode.e0508_comptime_resource_limit_exceeded, DiagnosticCode.fromCodeStr("E0508").?);
    try std.testing.expectEqual(DiagnosticCode.e0509_comptime_evaluation_cycle, DiagnosticCode.fromCodeStr("E0509").?);
    try std.testing.expectEqual(DiagnosticCode.e0510_compile_assertion_failed, DiagnosticCode.fromCodeStr("E0510").?);
    try std.testing.expectEqual(DiagnosticCode.w0308_unused_region_allocation, DiagnosticCode.fromCodeStr("W0308").?);
    try std.testing.expect(DiagnosticCode.fromCodeStr("E9999") == null);

    try std.testing.expectEqualStrings("E0302", DiagnosticCode.e0302_use_after_move.asCodeStr());
    try std.testing.expectEqual(Severity.err, DiagnosticCode.e0302_use_after_move.defaultSeverity());
    try std.testing.expectEqual(Severity.warning, DiagnosticCode.w0201_non_canonical_identifier_case.defaultSeverity());
}

// -------------------- DiagnosticSink Tests --------------------

test "test_diagnostic_sink_arena_cloning_and_error_cap_enforcement" {
    var sink = DiagnosticSink.initWithLimit(std.testing.allocator, 3);
    defer sink.deinit();

    // [1] Emit diagnostics from stack buffers that are immediately overwritten:
    var stack_msg: [32]u8 = undefined;
    var i: usize = 0;
    while (i < 5) : (i += 1) {
        var msg_writer = std.Io.Writer.fixed(&stack_msg);
        try msg_writer.print("error number {d}", .{i});
        try sink.emit(.{
            .code = .e0201_unexpected_token,
            .severity = .err,
            .message = msg_writer.buffered(),
        });
    }

    // [2] Only the first 3 errors must be stored; `has_reached_limit` must be set:
    try std.testing.expect(sink.hasErrors());
    try std.testing.expect(sink.has_reached_limit);
    try std.testing.expectEqual(@as(u32, 3), sink.error_count);
    try std.testing.expectEqual(@as(usize, 3), sink.countDiagnostics());
    try std.testing.expectEqualStrings("error number 0", sink.asSlice()[0].message);
    try std.testing.expectEqualStrings("error number 2", sink.asSlice()[2].message);

    // [3] Warnings must still be accepted even after the error limit is reached:
    try sink.emit(.{
        .code = .w0101_redundant_escape_sequence,
        .severity = .warning,
        .message = "redundant escape",
    });
    try std.testing.expectEqual(@as(u32, 1), sink.warning_count);
    try std.testing.expectEqual(@as(usize, 4), sink.countDiagnostics());
}

// ----------------- TransactionalPatcher Tests -----------------

test "test_transactional_patcher_conflict_detection_and_priority_scheduling" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    const file_id = FileId.fromInt(0);
    const rep_alpha = try interner.intern("alpha");
    const rep_beta = try interner.intern("beta");

    // [1] Verify pairwise conflict algebra (including zero-width boundary touches and adjacent edits):
    const edit_0_4 = TextEdit{ .file_id = file_id, .start_byte = 0, .end_byte = 4, .replacement_id = rep_alpha };
    const edit_4_8 = TextEdit{ .file_id = file_id, .start_byte = 4, .end_byte = 8, .replacement_id = rep_beta };
    const insert_at_4 = TextEdit{ .file_id = file_id, .start_byte = 4, .end_byte = 4, .replacement_id = rep_alpha };

    try std.testing.expect(!TransactionalPatcher.hasEditConflict(edit_0_4, edit_4_8));
    try std.testing.expect(TransactionalPatcher.hasEditConflict(edit_0_4, insert_at_4));
    try std.testing.expect(TransactionalPatcher.hasEditConflict(insert_at_4, edit_4_8));
    try std.testing.expect(!TransactionalPatcher.hasEditConflict(
        edit_0_4,
        .{ .file_id = FileId.fromInt(1), .start_byte = 0, .end_byte = 4, .replacement_id = rep_alpha },
    ));

    // [2] Schedule competing fixes: `.memory_safety` must beat `.formatting` on overlap:
    const source_code = "let value = compute(old_arg);";
    const fmt_edits = [_]TextEdit{.{
        .file_id = file_id,
        .start_byte = 20,
        .end_byte = 27,
        .replacement_id = try interner.intern("formatted_arg"),
    }};
    const safety_edits = [_]TextEdit{.{
        .file_id = file_id,
        .start_byte = 20,
        .end_byte = 27,
        .replacement_id = try interner.intern("&mut old_arg"),
    }};
    const prefix_edits = [_]TextEdit{.{
        .file_id = file_id,
        .start_byte = 0,
        .end_byte = 3,
        .replacement_id = try interner.intern("var"),
    }};
    const self_overlapping_edits = [_]TextEdit{
        .{ .file_id = file_id, .start_byte = 4, .end_byte = 9, .replacement_id = rep_alpha },
        .{ .file_id = file_id, .start_byte = 6, .end_byte = 9, .replacement_id = rep_beta },
    };
    const inverted_second_edit_bundle = [_]TextEdit{
        .{ .file_id = file_id, .start_byte = 4, .end_byte = 4, .replacement_id = rep_alpha },
        .{ .file_id = file_id, .start_byte = 9, .end_byte = 4, .replacement_id = rep_beta },
    };

    const candidate_fixes = [_]SuggestedFix{
        .{
            .message = "cosmetic rename",
            .applicability = .machine_applicable,
            .priority = .formatting,
            .edits = &fmt_edits,
        },
        .{
            .message = "invalid self-overlapping bundle",
            .applicability = .machine_applicable,
            .priority = .memory_safety,
            .edits = &self_overlapping_edits,
        },
        .{
            .message = "regression: inverted second edit must be rejected without underflow",
            .applicability = .machine_applicable,
            .priority = .memory_safety,
            .edits = &inverted_second_edit_bundle,
        },
        .{
            .message = "borrow mutably for safety",
            .applicability = .machine_applicable,
            .priority = .memory_safety,
            .edits = &safety_edits,
        },
        .{
            .message = "use mutable binding keyword",
            .applicability = .machine_applicable,
            .priority = .syntax_canonicalization,
            .edits = &prefix_edits,
        },
    };

    const outcome = try TransactionalPatcher.apply(
        std.testing.allocator,
        source_code,
        file_id,
        &candidate_fixes,
        &interner,
    );
    defer std.testing.allocator.free(outcome.patched_source);

    try std.testing.expectEqual(@as(u32, 2), outcome.applied_count);
    try std.testing.expectEqual(@as(u32, 3), outcome.skipped_conflict_count);
    try std.testing.expectEqualStrings("var value = compute(&mut old_arg);", outcome.patched_source);

    // Verify out-of-range `replacement_id` handles are atomically rejected:
    const invalid_outcome = try TransactionalPatcher.apply(
        std.testing.allocator,
        source_code,
        file_id,
        &[_]SuggestedFix{.{
            .message = "unregistered replacement handle",
            .applicability = .machine_applicable,
            .priority = .memory_safety,
            .edits = &[_]TextEdit{.{
                .file_id = file_id,
                .start_byte = 0,
                .end_byte = 3,
                .replacement_id = corex.StringId.fromInt(9999),
            }},
        }},
        &interner,
    );
    defer std.testing.allocator.free(invalid_outcome.patched_source);
    try std.testing.expectEqual(@as(u32, 0), invalid_outcome.applied_count);
    try std.testing.expectEqual(@as(u32, 1), invalid_outcome.skipped_conflict_count);
}

// ------------------ DiagnosticRenderer Tests ------------------

test "test_diagnostic_renderer_multiline_elision_diff_and_colored_mode" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    // Build an 8-line source file so a span from line 1 to line 8 triggers `┆` elision (`> 5` lines):
    const multiline_src =
        "fn outer() {\n" ++
        "    let a = 1;\n" ++
        "    let b = 2;\n" ++
        "    let c = 3;\n" ++
        "    let d = 4;\n" ++
        "    let e = 5;\n" ++
        "    let f = 6;\n" ++
        "    return a;\n";
    const file_id = try source_map.setOverlay("src/parser/block.cx", multiline_src, .root);

    const span_all = Span.init(file_id, 0, @intCast(multiline_src.len - 1));
    var sink = DiagnosticSink.initWithLimit(std.testing.allocator, 1);
    defer sink.deinit();
    try sink.emit(.{
        .code = .e0202_unclosed_delimiter,
        .severity = .err,
        .primary_span = span_all,
        .message = "unclosed `{` delimiter in function body",
        .labels = &.{.{ .span = span_all, .label = "unclosed block body", .style = .primary }},
        .suggestions = &[_]SuggestedFix{.{
            .message = "close block with `}`",
            .edits = &[_]TextEdit{.{
                .file_id = file_id,
                .start_byte = @intCast(multiline_src.len - 10),
                .end_byte = @intCast(multiline_src.len - 1),
                .replacement_id = try interner.intern("return a; }"),
            }},
        }},
    });

    var mono_buf: [4096]u8 = undefined;
    var mono_writer = std.Io.Writer.fixed(&mono_buf);
    try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.MONOCHROME).renderAll(&mono_writer, &sink);
    const mono_out = mono_writer.buffered();

    try std.testing.expect(std.mem.indexOf(u8, mono_out, "┆") != null);
    try std.testing.expect(std.mem.indexOf(u8, mono_out, "├╴ help: close block with `}`") != null);
    try std.testing.expect(std.mem.indexOf(u8, mono_out, "-     return a;") != null);
    try std.testing.expect(std.mem.indexOf(u8, mono_out, "+     return a; }") != null);
    try std.testing.expect(std.mem.indexOf(u8, mono_out, "aborting due to 1 previous errors") != null);

    // Verify colored rendering emits ANSI SGR sequences without altering visible structure:
    var color_buf: [4096]u8 = undefined;
    var color_writer = std.Io.Writer.fixed(&color_buf);
    try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.COLORED).renderAll(&color_writer, &sink);
    try std.testing.expect(std.mem.indexOf(u8, color_writer.buffered(), "\x1b[") != null);
}

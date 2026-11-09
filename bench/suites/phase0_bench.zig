//! Phase 0 Foundation Microbenchmark Suite (`bench/suites/phase0_bench.zig`)
//!
//! Benchmarks `BumpArena` 64 KiB slab allocation and $O(1)$ checkpoint/restore, `StringInterner`
//! `Wyhash(0)` symbol deduplication, `LineIndex` newline indexing and $O(\log L)$ coordinate lookup,
//! and `TransactionalPatcher` conflict-free byte splicing.
//!
//! Executed via `zig build bench`, enforcing 5 warmup iterations and 30 timed iterations per workload
//! and outputting the canonical monochrome Unicode report table.

const std = @import("std");
const corex = @import("corex");

const BumpArena = corex.BumpArena;
const FileId = corex.FileId;
const LineIndex = corex.LineIndex;
const StringInterner = corex.StringInterner;
const SuggestedFix = corex.SuggestedFix;
const TextEdit = corex.TextEdit;
const TransactionalPatcher = corex.TransactionalPatcher;
const StyleConfig = corex.StyleConfig;
const BenchCase = corex.bench_harness.BenchCase;

// -------------------------------------- INTERNALS --------------------------------------

/// Benchmarks 10,000 16-byte aligned allocations and $O(1)$ checkpoint/restore on `BumpArena`.
fn benchBumpArenaSlabs(allocator: std.mem.Allocator) !usize {
    var arena = BumpArena.init(allocator);
    defer arena.deinit();

    const saved_checkpoint = arena.checkpoint();
    var i: usize = 0;
    while (i < 10_000) : (i += 1) {
        const block = try arena.allocAligned(24, 16);
        block[0] = @truncate(i);
        std.mem.doNotOptimizeAway(block.ptr);
    }
    const allocated_bytes = arena.total_allocated;
    arena.restore(saved_checkpoint);
    return allocated_bytes;
}

/// Benchmarks `StringInterner` `Wyhash(0)` interning and $O(1)$ deduplication across 1,024 symbols.
fn benchStringInternerWyhash(allocator: std.mem.Allocator) !usize {
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();

    const identifiers = [_][]const u8{
        "fn",           "let",              "var",          "struct",
        "enum",         "trait",            "impl",         "comptime",
        "BumpArena",    "StringInterner",   "VfsSourceMap", "LineIndex",
        "TokenBuffer",  "LosslessCstArena", "AstArena",     "DiagnosticSink",
        "resolve_path", "resolve_symbol",   "parse_expr",   "emit_diagnostic",
        "context",      "allocator",        "cancel_token", "Result",
    };

    var i: usize = 0;
    while (i < 1_024) : (i += 1) {
        std.mem.doNotOptimizeAway(try interner.intern(identifiers[i % identifiers.len]));
    }
    return interner.countStrings() * 32;
}

/// Benchmarks `LineIndex` construction and $O(\log L)$ binary search across a multi-line buffer.
fn benchLineIndexLookup(allocator: std.mem.Allocator) !usize {
    const sample_chunk =
        "pub fn process_packet(buffer: &[u8]) -> Result[usize, IoError] {\r\n" ++
        "    let header = parse_header(buffer)?;\n" ++
        "    // Verify payload length and checksum:\n" ++
        "    return Ok(header.payload_len);\r\n" ++
        "}\n";

    var source_builder: std.ArrayList(u8) = .empty;
    defer source_builder.deinit(allocator);
    var rep_idx: usize = 0;
    while (rep_idx < 64) : (rep_idx += 1) {
        try source_builder.appendSlice(allocator, sample_chunk);
    }

    var line_index = try LineIndex.build(allocator, source_builder.items);
    defer line_index.deinit(allocator);

    var offset: u32 = 0;
    while (offset < source_builder.items.len) : (offset += 29) {
        std.mem.doNotOptimizeAway(line_index.resolveLineCol(source_builder.items, offset));
    }
    return line_index.countLines() * @sizeOf(u32);
}

/// Benchmarks `TransactionalPatcher` interval scheduling and single-pass $O(N + M)$ splicing.
fn benchTransactionalPatcher(allocator: std.mem.Allocator) !usize {
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();

    const file_id = FileId.fromInt(0);
    const outcome = try TransactionalPatcher.apply(
        allocator,
        "let alpha = compute(first_arg, second_arg, third_arg, fourth_arg);",
        file_id,
        &[_]SuggestedFix{.{
            .message = "pass mutable borrow",
            .applicability = .machine_applicable,
            .priority = .memory_safety,
            .edits = &[_]TextEdit{.{
                .file_id = file_id,
                .start_byte = 20,
                .end_byte = 29,
                .replacement_id = try interner.intern("&mut first_arg"),
            }},
        }},
        &interner,
    );
    defer allocator.free(outcome.patched_source);
    std.mem.doNotOptimizeAway(outcome.patched_source.ptr);
    return outcome.patched_source.len;
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 0 benchmark suite and prints the monochrome Unicode table to `stdout`.
pub fn main(init: std.process.Init) !void {
    const results = try corex.bench_harness.runSuite(
        init.gpa,
        init.io,
        &[_]BenchCase{
            .{ .name = "BumpArena (10k allocs + O(1) restore)", .run_fn = benchBumpArenaSlabs },
            .{ .name = "StringInterner (1,024 Wyhash symbols)", .run_fn = benchStringInternerWyhash },
            .{ .name = "LineIndex (build + O(log L) lookup)", .run_fn = benchLineIndexLookup },
            .{ .name = "TransactionalPatcher (O(N+M) splice)", .run_fn = benchTransactionalPatcher },
        },
    );
    defer init.gpa.free(results);

    var stdout_buf: [4096]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writerStreaming(init.io, &stdout_buf);
    const style_config: StyleConfig = .{
        .is_color_enabled = corex.style.isColorEnabled(.auto, init.io, std.Io.File.stdout(), init.environ_map),
    };

    try style_config.writeStatusHeader(
        &stdout_writer.interface,
        .success,
        corex.Glyphs.POINTER_SOLID,
        "corex bench",
        "Phase 0 Foundation Benchmark Suite (5 warmup, 30 measured iterations)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, results);
    try stdout_writer.interface.flush();
}

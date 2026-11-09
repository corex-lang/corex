//! Statistical Performance Benchmark Harness & Monochrome Table Reporter
//!
//! Executes microbenchmarks and compiler scaling suites with mandatory warmup and `>= 30` timed
//! iterations, computing minimum, median, P95, sample standard deviation, and MAD outlier metrics.
//!
//! Renders benchmark reports using `TableRenderer` and the monochrome Unicode box-drawing vocabulary
//! specified in `.agents/skills/bench/SKILL.md` Section 3 and `AGENTS.md` Section 5.

const std = @import("std");
const mem = @import("../mem_foundation.zig");
const vfs = @import("../vfs_sourcemap.zig");
const style = @import("../cli/style.zig");
const box_draw = @import("../cli/box_draw.zig");

const StyleConfig = style.StyleConfig;
const TableColumn = box_draw.TableColumn;
const TableRenderer = box_draw.TableRenderer;

// ---------------------------------------- TYPES ----------------------------------------

/// Execution parameters governing warmup and timed sample counts for a benchmark workload.
pub const BenchConfig = struct {
    /// Number of untimed warmup iterations executed prior to measurement (minimum 5 recommended).
    warmup_iterations: u32 = DEFAULT_WARMUP_ITERATIONS,
    /// Number of timed iterations recorded for statistical aggregation (clamped to `>= 30`).
    measured_iterations: u32 = DEFAULT_MEASURED_ITERATIONS,
};

/// Aggregated statistical metrics computed over a sorted sample of iteration durations.
pub const BenchStats = struct {
    /// Minimum observed iteration latency (ns).
    min_ns: u64,
    /// Maximum observed iteration latency (ns).
    max_ns: u64,
    /// Median (P50) iteration latency (ns).
    median_ns: u64,
    /// 95th percentile iteration latency (ns).
    p95_ns: u64,
    /// Arithmetic mean iteration latency (ns).
    mean_ns: f64,
    /// Sample standard deviation across measured iterations (ns).
    stddev_ns: f64,
    /// Median Absolute Deviation from the median (ns).
    mad_ns: u64,
    /// Peak or total bytes allocated during a single measured iteration.
    bytes_allocated: usize,
};

/// Function pointer signature for a benchmark workload returning bytes allocated per iteration.
pub const BenchFn = *const fn (allocator: std.mem.Allocator) anyerror!usize;

/// Descriptor for a named benchmark workload and its execution configuration.
pub const BenchCase = struct {
    /// Human-readable benchmark name displayed in the report table.
    name: []const u8,
    /// Workload callback invoked on each warmup and measured iteration.
    run_fn: BenchFn,
    /// Iteration count configuration.
    config: BenchConfig = .{},
};

/// Completed benchmark measurement pairing a workload name with its `BenchStats`.
pub const BenchResult = struct {
    /// Workload name matching `BenchCase.name`.
    name: []const u8,
    /// Effective number of timed iterations executed.
    iterations: u32,
    /// Statistical latency and memory summary.
    stats: BenchStats,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Default number of untimed warmup iterations per workload (`.agents/skills/bench/SKILL.md` Section 3).
pub const DEFAULT_WARMUP_ITERATIONS: u32 = 5;
/// Minimum required number of measured iterations per workload (`.agents/skills/bench/SKILL.md` Section 3).
pub const DEFAULT_MEASURED_ITERATIONS: u32 = 30;
/// Maximum number of rows rendered in a single stack-formatted benchmark table.
pub const MAX_BENCH_RESULTS: usize = 64;

// -------------------------------------- INTERNALS --------------------------------------

/// Computes the median of a pre-sorted slice of `u64` values.
fn computeSortedMedian(sorted_values: []const u64) u64 {
    if (sorted_values.len == 0) return 0;
    const mid_idx = sorted_values.len / 2;
    if (sorted_values.len % 2 == 1) {
        return sorted_values[mid_idx];
    }
    return (sorted_values[mid_idx - 1] + sorted_values[mid_idx]) / 2;
}

/// Built-in Phase 0 workload benchmarking `BumpArena` allocation and checkpoint restoration.
fn benchPhase0BumpArena(allocator: std.mem.Allocator) !usize {
    var arena = mem.BumpArena.init(allocator);
    defer arena.deinit();

    const saved_cp = arena.checkpoint();
    var i: usize = 0;
    while (i < 1_000) : (i += 1) {
        std.mem.doNotOptimizeAway((try arena.allocAligned(32, 16)).ptr);
    }
    const peak_bytes = arena.total_allocated;
    arena.restore(saved_cp);
    return peak_bytes;
}

/// Built-in Phase 0 workload benchmarking `StringInterner` `Wyhash(0)` deduplication.
fn benchPhase0StringInterner(allocator: std.mem.Allocator) !usize {
    var interner = try mem.StringInterner.init(allocator);
    defer interner.deinit();

    const sample_tokens = [_][]const u8{
        "fn",      "let",       "mut",        "struct",
        "enum",    "trait",     "impl",       "return",
        "context", "allocator", "BumpArena",  "StringInterner",
        "Span",    "FileId",    "TokenIndex", "LosslessCstArena",
    };
    var i: usize = 0;
    while (i < 256) : (i += 1) {
        std.mem.doNotOptimizeAway(try interner.intern(sample_tokens[i % sample_tokens.len]));
    }
    return interner.countStrings() * @sizeOf(mem.StringId);
}

/// Built-in Phase 0 workload benchmarking `LineIndex` construction and $O(\log L)$ lookup.
fn benchPhase0LineIndex(allocator: std.mem.Allocator) !usize {
    const sample_source =
        "fn compute_metric(input_slice: &[u64]) -> u64 {\r\n" ++
        "    var accumulator: u64 = 0;\n" ++
        "    for item_val in input_slice {\r\n" ++
        "        accumulator += item_val;\n" ++
        "    }\n" ++
        "    return accumulator;\n" ++
        "}\n";
    var line_index = try vfs.LineIndex.build(allocator, sample_source);
    defer line_index.deinit(allocator);

    var byte_offset: u32 = 0;
    while (byte_offset < sample_source.len) : (byte_offset += 11) {
        std.mem.doNotOptimizeAway(line_index.resolveLineCol(sample_source, byte_offset));
    }
    return line_index.countLines() * @sizeOf(u32);
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Computes `BenchStats` (`min`, `max`, `median`, `p95`, `mean`, `stddev`, `mad`) from `raw_samples_ns`.
pub fn computeStats(
    allocator: std.mem.Allocator,
    raw_samples_ns: []const u64,
    bytes_allocated: usize,
) !BenchStats {
    if (raw_samples_ns.len == 0) {
        return .{
            .min_ns = 0,
            .max_ns = 0,
            .median_ns = 0,
            .p95_ns = 0,
            .mean_ns = 0.0,
            .stddev_ns = 0.0,
            .mad_ns = 0,
            .bytes_allocated = bytes_allocated,
        };
    }

    // [1] Copy and sort raw sample durations in ascending order:
    const sorted_samples = try allocator.dupe(u64, raw_samples_ns);
    defer allocator.free(sorted_samples);
    std.mem.sort(u64, sorted_samples, {}, std.sort.asc(u64));

    const n = sorted_samples.len;
    const median_ns = computeSortedMedian(sorted_samples);

    // [2] Compute arithmetic mean and sample standard deviation:
    var sum_ns: f64 = 0.0;
    for (sorted_samples) |sample_val| {
        sum_ns += @floatFromInt(sample_val);
    }
    const mean_ns = sum_ns / @as(f64, @floatFromInt(n));

    var variance_accum: f64 = 0.0;
    for (sorted_samples) |sample_val| {
        const delta = @as(f64, @floatFromInt(sample_val)) - mean_ns;
        variance_accum += delta * delta;
    }

    // [3] Compute Median Absolute Deviation (`MAD = median(|x_i - median|)`):
    const abs_deviations = try allocator.alloc(u64, n);
    defer allocator.free(abs_deviations);
    for (sorted_samples, 0..) |sample_val, i| {
        abs_deviations[i] = if (sample_val >= median_ns)
            sample_val - median_ns
        else
            median_ns - sample_val;
    }
    std.mem.sort(u64, abs_deviations, {}, std.sort.asc(u64));

    return .{
        .min_ns = sorted_samples[0],
        .max_ns = sorted_samples[n - 1],
        .median_ns = median_ns,
        .p95_ns = sorted_samples[@min(n - 1, (n * 95) / 100)],
        .mean_ns = mean_ns,
        .stddev_ns = if (n > 1) @sqrt(variance_accum / @as(f64, @floatFromInt(n - 1))) else 0.0,
        .mad_ns = computeSortedMedian(abs_deviations),
        .bytes_allocated = bytes_allocated,
    };
}

/// Executes `bench_case` with warmup and `>= 30` measured iterations using `.awake` monotonic timestamps.
pub fn runCase(
    allocator: std.mem.Allocator,
    io: std.Io,
    bench_case: BenchCase,
) !BenchResult {
    const measured_count = @max(DEFAULT_MEASURED_ITERATIONS, bench_case.config.measured_iterations);

    // [1] Execute untimed warmup iterations:
    var warmup_idx: u32 = 0;
    while (warmup_idx < bench_case.config.warmup_iterations) : (warmup_idx += 1) {
        std.mem.doNotOptimizeAway(try bench_case.run_fn(allocator));
    }

    // [2] Execute timed measurement iterations:
    const samples_ns = try allocator.alloc(u64, measured_count);
    defer allocator.free(samples_ns);
    var peak_bytes: usize = 0;

    var iter_idx: usize = 0;
    while (iter_idx < measured_count) : (iter_idx += 1) {
        const start_ts = std.Io.Clock.Timestamp.now(io, .awake);
        const iter_bytes = try bench_case.run_fn(allocator);
        const end_ts = std.Io.Clock.Timestamp.now(io, .awake);
        if (iter_bytes > peak_bytes) {
            peak_bytes = iter_bytes;
        }
        samples_ns[iter_idx] = @intCast(@max(@as(i96, 0), start_ts.durationTo(end_ts).raw.nanoseconds));
    }

    return .{
        .name = bench_case.name,
        .iterations = measured_count,
        .stats = try computeStats(allocator, samples_ns, peak_bytes),
    };
}

/// Executes a slice of `BenchCase` workloads and returns a caller-owned slice of `BenchResult` records.
pub fn runSuite(
    allocator: std.mem.Allocator,
    io: std.Io,
    cases: []const BenchCase,
) ![]BenchResult {
    const results = try allocator.alloc(BenchResult, cases.len);
    errdefer allocator.free(results);
    for (cases, 0..) |bench_case, i| {
        results[i] = try runCase(allocator, io, bench_case);
    }
    return results;
}

/// Formats a duration in nanoseconds into a compact human-readable string (`ns`, `us`, or `ms`).
pub fn formatDurationNs(buffer: []u8, duration_ns: u64) []const u8 {
    var writer = std.Io.Writer.fixed(buffer);
    if (duration_ns < 1_000) {
        writer.print("{d}ns", .{duration_ns}) catch unreachable;
    } else if (duration_ns < 1_000_000) {
        writer.print("{d}.{d:0>2}us", .{ duration_ns / 1_000, (duration_ns % 1_000) / 10 }) catch unreachable;
    } else {
        writer.print("{d}.{d:0>2}ms", .{ duration_ns / 1_000_000, (duration_ns % 1_000_000) / 10_000 }) catch unreachable;
    }
    return writer.buffered();
}

/// Formats a byte count into a compact human-readable string (`B`, `KiB`, or `MiB`).
pub fn formatBytes(buffer: []u8, byte_count: usize) []const u8 {
    var writer = std.Io.Writer.fixed(buffer);
    if (byte_count < 1024) {
        writer.print("{d} B", .{byte_count}) catch unreachable;
    } else if (byte_count < 1024 * 1024) {
        writer.print("{d}.{d} KiB", .{ byte_count / 1024, ((byte_count % 1024) * 10) / 1024 }) catch unreachable;
    } else {
        writer.print("{d}.{d} MiB", .{ byte_count / (1024 * 1024), ((byte_count % (1024 * 1024)) * 10) / (1024 * 1024) }) catch unreachable;
    }
    return writer.buffered();
}

/// Renders a slice of `BenchResult` records as an aligned monochrome Unicode box-drawing table.
pub fn renderResultsTable(
    writer: *std.Io.Writer,
    style_config: StyleConfig,
    results: []const BenchResult,
) !void {
    const columns = [_]TableColumn{
        .{ .header = "Benchmark", .alignment = .left },
        .{ .header = "Iterations", .alignment = .right },
        .{ .header = "Min", .alignment = .right },
        .{ .header = "Median", .alignment = .right },
        .{ .header = "P95", .alignment = .right },
        .{ .header = "StdDev", .alignment = .right },
        .{ .header = "MAD", .alignment = .right },
        .{ .header = "Peak Mem", .alignment = .right },
    };

    const clamped_count = @min(results.len, MAX_BENCH_RESULTS);
    var cell_buffers: [MAX_BENCH_RESULTS][7][32]u8 = undefined;
    var row_cells_storage: [MAX_BENCH_RESULTS][8][]const u8 = undefined;
    var row_slices: [MAX_BENCH_RESULTS][]const []const u8 = undefined;

    for (results[0..clamped_count], 0..) |bench_res, i| {
        var iter_writer = std.Io.Writer.fixed(&cell_buffers[i][0]);
        iter_writer.print("{d}", .{bench_res.iterations}) catch unreachable;

        row_cells_storage[i] = .{
            bench_res.name,
            iter_writer.buffered(),
            formatDurationNs(&cell_buffers[i][1], bench_res.stats.min_ns),
            formatDurationNs(&cell_buffers[i][2], bench_res.stats.median_ns),
            formatDurationNs(&cell_buffers[i][3], bench_res.stats.p95_ns),
            formatDurationNs(&cell_buffers[i][4], @intFromFloat(@max(0.0, @round(bench_res.stats.stddev_ns)))),
            formatDurationNs(&cell_buffers[i][5], bench_res.stats.mad_ns),
            formatBytes(&cell_buffers[i][6], bench_res.stats.bytes_allocated),
        };
        row_slices[i] = &row_cells_storage[i];
    }

    try TableRenderer.init(style_config).renderTable(writer, &columns, row_slices[0..clamped_count]);
}

/// Runs the built-in Phase 0 foundation microbenchmark suite and renders the report table to `writer`.
pub fn runDefaultPhase0Suite(
    allocator: std.mem.Allocator,
    io: std.Io,
    writer: *std.Io.Writer,
    style_config: StyleConfig,
) !void {
    const default_cases = [_]BenchCase{
        .{ .name = "BumpArena (1k x 32B + restore)", .run_fn = benchPhase0BumpArena },
        .{ .name = "StringInterner (256 Wyhash lookups)", .run_fn = benchPhase0StringInterner },
        .{ .name = "LineIndex (build + resolveLineCol)", .run_fn = benchPhase0LineIndex },
    };
    const results = try runSuite(allocator, io, &default_cases);
    defer allocator.free(results);

    try style_config.writeStatusHeader(
        writer,
        .success,
        style.Glyphs.POINTER_SOLID,
        "corex bench",
        "Phase 0 Foundation Benchmark Suite (5 warmup, 30 measured iterations)",
    );
    try writer.writeByte('\n');
    try renderResultsTable(writer, style_config, results);
}

test "test_bench_harness_stats_and_table_rendering" {
    const stats = try computeStats(
        std.testing.allocator,
        &[_]u64{ 120, 100, 110, 130, 140, 105, 115, 200, 125, 110 },
        65_536,
    );
    try std.testing.expect(stats.min_ns <= stats.median_ns);
    try std.testing.expect(stats.median_ns <= stats.p95_ns);
    try std.testing.expect(stats.p95_ns <= stats.max_ns);
    try std.testing.expectEqual(@as(u64, 100), stats.min_ns);
    try std.testing.expectEqual(@as(u64, 200), stats.max_ns);
    try std.testing.expectEqual(@as(u64, 117), stats.median_ns);
    try std.testing.expect(stats.mad_ns > 0);
    try std.testing.expect(stats.stddev_ns > 0.0);

    var table_buf: [2048]u8 = undefined;
    var table_writer = std.Io.Writer.fixed(&table_buf);
    try renderResultsTable(&table_writer, StyleConfig.MONOCHROME, &.{.{
        .name = "BumpArena",
        .iterations = 30,
        .stats = stats,
    }});
    try std.testing.expect(std.mem.indexOf(u8, table_writer.buffered(), "│ BumpArena │") != null);
}

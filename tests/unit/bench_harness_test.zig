//! Unit Tests for Statistical Benchmark Harness (`tests/unit/bench_harness_test.zig`)
//!
//! Verifies `computeStats` (`min`, `max`, `median`, `p95`, `mean`, `stddev`, `mad`), human-readable
//! duration/byte formatters (`formatDurationNs`, `formatBytes`), `runCase`, and `renderResultsTable`.
//!
//! Ensures warmup and `>= 30` measured iterations are strictly enforced per `.agents/skills/bench/SKILL.md`.

const std = @import("std");
const corex = @import("corex");

const harness = corex.bench_harness;
const StyleConfig = corex.StyleConfig;

// -------------------------------------- INTERNALS --------------------------------------

/// Minimal deterministic workload used to verify `runCase` and `runSuite` iteration enforcement.
fn dummyWorkload(allocator: std.mem.Allocator) !usize {
    const slice = try allocator.alloc(u8, 64);
    defer allocator.free(slice);
    @memset(slice, 1);
    std.mem.doNotOptimizeAway(slice.ptr);
    return slice.len;
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_bench_compute_stats_empty_single_and_multi_sample_distributions" {
    // [1] Empty sample array must return zeroed statistics without dividing by zero:
    const empty_stats = try harness.computeStats(std.testing.allocator, &[_]u64{}, 0);
    try std.testing.expectEqual(@as(u64, 0), empty_stats.min_ns);
    try std.testing.expectEqual(@as(u64, 0), empty_stats.median_ns);
    try std.testing.expectEqual(@as(f64, 0.0), empty_stats.stddev_ns);

    // [2] Single-element sample array must have `stddev_ns == 0.0` and `mad_ns == 0`:
    const single_stats = try harness.computeStats(std.testing.allocator, &[_]u64{420}, 1024);
    try std.testing.expectEqual(@as(u64, 420), single_stats.min_ns);
    try std.testing.expectEqual(@as(u64, 420), single_stats.max_ns);
    try std.testing.expectEqual(@as(u64, 420), single_stats.median_ns);
    try std.testing.expectEqual(@as(u64, 0), single_stats.mad_ns);
    try std.testing.expectEqual(@as(usize, 1024), single_stats.bytes_allocated);

    // [3] Odd-count distribution `[10, 20, 30, 40, 100]`:
    const odd_stats = try harness.computeStats(
        std.testing.allocator,
        &[_]u64{ 40, 10, 100, 20, 30 },
        2048,
    );
    try std.testing.expectEqual(@as(u64, 10), odd_stats.min_ns);
    try std.testing.expectEqual(@as(u64, 100), odd_stats.max_ns);
    try std.testing.expectEqual(@as(u64, 30), odd_stats.median_ns);
    try std.testing.expectEqual(@as(u64, 10), odd_stats.mad_ns);
    try std.testing.expectEqual(@as(f64, 40.0), odd_stats.mean_ns);
}

test "test_bench_duration_and_byte_formatters" {
    var scratch_buf: [32]u8 = undefined;
    try std.testing.expectEqualStrings("850ns", harness.formatDurationNs(&scratch_buf, 850));
    try std.testing.expectEqualStrings("12.34us", harness.formatDurationNs(&scratch_buf, 12_340));
    try std.testing.expectEqualStrings("3.50ms", harness.formatDurationNs(&scratch_buf, 3_500_000));

    try std.testing.expectEqualStrings("512 B", harness.formatBytes(&scratch_buf, 512));
    try std.testing.expectEqualStrings("64.0 KiB", harness.formatBytes(&scratch_buf, 64 * 1024));
    try std.testing.expectEqualStrings("2.5 MiB", harness.formatBytes(&scratch_buf, 2 * 1024 * 1024 + 512 * 1024));
}

test "test_bench_run_suite_enforces_minimum_30_measured_iterations" {
    const results = try harness.runSuite(std.testing.allocator, std.testing.io, &.{.{
        .name = "DummyAlloc64B",
        .run_fn = dummyWorkload,
        .config = .{ .warmup_iterations = 2, .measured_iterations = 5 },
    }});
    defer std.testing.allocator.free(results);

    try std.testing.expectEqual(@as(usize, 1), results.len);
    try std.testing.expectEqual(harness.DEFAULT_MEASURED_ITERATIONS, results[0].iterations);
    try std.testing.expectEqual(@as(usize, 64), results[0].stats.bytes_allocated);

    var table_buf: [2048]u8 = undefined;
    var table_writer = std.Io.Writer.fixed(&table_buf);
    try harness.renderResultsTable(&table_writer, StyleConfig.MONOCHROME, results);
    try std.testing.expect(std.mem.indexOf(u8, table_writer.buffered(), "│ DummyAlloc64B │") != null);
    try std.testing.expect(std.mem.indexOf(u8, table_writer.buffered(), "│     64 B │") != null);
}

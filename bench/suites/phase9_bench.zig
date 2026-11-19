//! Phase 9 Package Solver (`Bounded-MVS`), Warm Lock/VFS Mount & CAS Crypto Benchmark Suite
//!
//! Measures 500-dependency cold `Bounded-MVS` + `FeatureBitset512` resolution (`< 5 ms` budget),
//! warm 50-package `corex.lock` parsing + zero-copy `.cxtree` `VfsSourceMap` mounting (`< 1 ms`
//! budget), and `.cxtree` / `.cxi` keyed `BLAKE3` + `128 KiB` Bao `.obao` streaming throughput.
//!
//! Enforces strict latency budgets automatically and renders a monochrome Unicode benchmark table.

const std = @import("std");
const corex = @import("corex");

const pkg_manifest = corex.pkg_manifest;
const pkg_cache = corex.pkg_cache;
const pkg_resolver = corex.pkg_resolver;
const pkg_cxi_seam = corex.pkg_cxi_seam;
const vfs_sourcemap = corex.vfs_sourcemap;
const BumpArena = corex.BumpArena;
const StringInterner = corex.StringInterner;
const FileId = corex.FileId;
const PackageId = corex.PackageId;
const Span = corex.Span;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;
const StyleConfig = corex.StyleConfig;
const BenchCase = corex.bench_harness.BenchCase;
const BenchConfig = corex.bench_harness.BenchConfig;
const BenchResult = corex.bench_harness.BenchResult;

// ---------------------------------------- TYPES ----------------------------------------

/// Pre-populated 500-dependency sparse index, 50-package `corex.lock`/`.cxtree` corpus, and `128 KiB` Bao payload.
const PreparedPhase9BenchState = struct {
    /// Borrowed `std.Io` handle from `main`.
    io: std.Io,
    /// Scratch directory `.zig-cache/phase9_bench_env` cleaned up at exit.
    scratch_dir: []u8,
    /// Hermetic `COREX_HOME` directory holding pre-populated sparse index & shared `.cxtree` for Case 1.
    corex_home_dir: []u8,
    /// Pre-initialized `StringInterner` owning root manifest symbols for Case 1.
    cold_interner: StringInterner,
    /// Arena backing `cold_bundle.root_manifest` slices for Case 1.
    cold_manifest_arena: BumpArena,
    /// Pre-parsed root `WorkspaceManifestBundle` (`is_script = true` to avoid root dir crawl) for Case 1.
    cold_bundle: pkg_manifest.WorkspaceManifestBundle,
    /// Pre-serialized 50-package `corex.lock` v1 buffer for Case 2.
    warm_lockfile_bytes: []u8,
    /// Pre-built 8-byte-aligned `.cxtree` buffers (`50` packages x `4` files = `200` VFS entries) for Case 2.
    warm_cxtrees: [WARM_MOUNT_PKG_COUNT][]align(8) u8,
    /// Pre-formatted canonical package names (`"warm-pkg-00"` .. `"warm-pkg-49"`) for Case 2.
    warm_pkg_names: [WARM_MOUNT_PKG_COUNT][11]u8,
    /// Pre-sorted `CxiFnRecord` array (`64` records) for Case 3 `.cxi` serialization & keyed `BLAKE3`.
    cxi_fn_records: [CXI_BENCH_FN_COUNT]pkg_cxi_seam.CxiFnRecord,
    /// Pre-sorted `CxiTypeRecord` array (`32` records) for Case 3 `.cxi` serialization & keyed `BLAKE3`.
    cxi_type_records: [CXI_BENCH_TYPE_COUNT]pkg_cxi_seam.CxiTypeRecord,
    /// Deterministic `128 KiB` archive payload hashed and verified via Bao `.obao` in Case 3.
    bao_payload: []u8,
    /// Expected unkeyed `BLAKE3` root digest of `bao_payload`.
    bao_root_blake3: [32]u8,

    /// Deletes `scratch_dir` and frees all heap-owned benchmark fixtures.
    fn deinit(self: *PreparedPhase9BenchState, allocator: std.mem.Allocator) void {
        for (self.warm_cxtrees) |tree_buf| {
            allocator.free(tree_buf);
        }
        allocator.free(self.bao_payload);
        allocator.free(self.warm_lockfile_bytes);
        self.cold_bundle.deinit();
        self.cold_manifest_arena.deinit();
        self.cold_interner.deinit();
        allocator.free(self.corex_home_dir);
        std.Io.Dir.cwd().deleteTree(self.io, self.scratch_dir) catch {};
        allocator.free(self.scratch_dir);
        self.* = undefined;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical benchmark warmup count (`5` untimed iterations).
const BENCH_WARMUP_COUNT: u32 = 5;
/// Canonical benchmark timed count (`30` measured iterations).
const BENCH_MEASURED_COUNT: u32 = 30;
/// Total external dependencies resolved in Benchmark 1 (`500` external + `1` root = `501` packages).
const COLD_RESOLVE_DEP_COUNT: usize = 500;
/// Hard median latency ceiling (`5 ms` = `5,000,000 ns`) for 500-dep cold `Bounded-MVS` resolution.
const MAX_COLD_MVS_MEDIAN_NS: u64 = 5_000_000;
/// Number of external packages parsed from `corex.lock` and mounted into `VfsSourceMap` in Benchmark 2.
const WARM_MOUNT_PKG_COUNT: usize = 50;
/// Hard median latency ceiling (`1 ms` = `1,000,000 ns`) for warm 50-pkg `corex.lock` + `.cxtree` VFS mount.
const MAX_WARM_MOUNT_MEDIAN_NS: u64 = 1_000_000;
/// Number of `CxTreeInputEntry` records hashed per `.cxtree` build in Benchmark 3.
const CXTREE_BENCH_ENTRY_COUNT: usize = 32;
/// Number of `CxiFnRecord` entries serialized and hashed in Benchmark 3.
const CXI_BENCH_FN_COUNT: usize = 64;
/// Number of `CxiTypeRecord` entries serialized and hashed in Benchmark 3.
const CXI_BENCH_TYPE_COUNT: usize = 32;
/// Byte length (`128 KiB`) of the multi-chunk Bao payload encoded and verified in Benchmark 3.
const BAO_BENCH_PAYLOAD_BYTES: usize = 128 * 1024;

/// Shared benchmark fixture initialized once at startup and cleaned up on exit.
var shared_bench_state: ?PreparedPhase9BenchState = null;

// -------------------------------------- INTERNALS --------------------------------------

/// Initializes the 500-package sparse index, 50-package `corex.lock`/`.cxtree` set, and `128 KiB` Bao buffer.
fn preparePhase9BenchState(allocator: std.mem.Allocator, io: std.Io) !PreparedPhase9BenchState {
    const scratch_dir = try allocator.dupe(u8, ".zig-cache/phase9_bench_env");
    errdefer allocator.free(scratch_dir);
    std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, scratch_dir);

    const corex_home = try std.fmt.allocPrint(allocator, "{s}/corex_home", .{scratch_dir});
    errdefer allocator.free(corex_home);
    const ws_dir = try std.fmt.allocPrint(allocator, "{s}/cold_ws", .{scratch_dir});
    defer allocator.free(ws_dir);
    try std.Io.Dir.cwd().createDirPath(io, ws_dir);

    var cache = try pkg_cache.PkgCache.init(allocator, corex_home, 1024, 16 * 1024 * 1024);
    defer cache.deinit();

    // [1] Publish shared `.cxtree` (`src/root.cx`) in `corex_home` and write 500 sparse-index NDJSON files:
    const stub_src = "pub fn exported_fn() -> i32 = 42;\n";
    var stub_b3: [32]u8 = undefined;
    std.crypto.hash.Blake3.hash(stub_src, &stub_b3, .{});
    try cache.publishBlob(io, stub_src, stub_b3, null, Span.init(.none, 0, 0));

    const shared_entries = [_]pkg_cache.CxTreeInputEntry{
        .{ .rel_path = "src/root.cx", .file_mode = 0x01, .file_size = stub_src.len, .file_blake3 = stub_b3 },
    };
    const shared_tree = try pkg_cache.buildCxTreeBytes(
        allocator,
        "bench-stub",
        &shared_entries,
        null,
        Span.init(.none, 0, 0),
    );
    defer allocator.free(shared_tree.bytes);
    try cache.publishCxTree(io, shared_tree.bytes, shared_tree.tree_blake3, null, Span.init(.none, 0, 0));
    const tree_hex = std.fmt.bytesToHex(shared_tree.tree_blake3, .lower);

    // Populate `<cas_root>/index/default/index/<sparse_rel>` for `dep-000` .. `dep-499` with diamond edges + features:
    for (0..COLD_RESOLVE_DEP_COUNT) |pkg_i| {
        var name_buf: [16]u8 = undefined;
        const pkg_name = try std.fmt.bufPrint(&name_buf, "dep-{d:0>3}", .{pkg_i});

        var ndjson_buf: std.ArrayList(u8) = .empty;
        defer ndjson_buf.deinit(allocator);

        for ([_]u32{ 0, 1 }) |minor_v| {
            const head_txt = try std.fmt.allocPrint(
                allocator,
                "{{\"name\":\"{s}\",\"vers\":\"1.{d}.0\",\"tree_hash\":\"b3:{s}\",\"deps\":[",
                .{ pkg_name, minor_v, &tree_hex },
            );
            defer allocator.free(head_txt);
            try ndjson_buf.appendSlice(allocator, head_txt);

            const child_left = pkg_i * 2 + 1;
            const child_right = pkg_i * 2 + 2;
            const diamond_hop = pkg_i + 7;
            var dep_emitted: usize = 0;

            if (child_left < COLD_RESOLVE_DEP_COUNT) {
                const c_txt = try std.fmt.allocPrint(
                    allocator,
                    "{{\"name\":\"dep-{d:0>3}\",\"req\":\"1.0.0\",\"features\":[\"tls\"]}}",
                    .{child_left},
                );
                defer allocator.free(c_txt);
                try ndjson_buf.appendSlice(allocator, c_txt);
                dep_emitted += 1;
            }
            if (child_right < COLD_RESOLVE_DEP_COUNT) {
                if (dep_emitted > 0) try ndjson_buf.appendSlice(allocator, ",");
                const c_txt = try std.fmt.allocPrint(
                    allocator,
                    "{{\"name\":\"dep-{d:0>3}\",\"req\":\"1.1.0\",\"features\":[\"json\"]}}",
                    .{child_right},
                );
                defer allocator.free(c_txt);
                try ndjson_buf.appendSlice(allocator, c_txt);
                dep_emitted += 1;
            }
            if (minor_v == 1 and diamond_hop < COLD_RESOLVE_DEP_COUNT and diamond_hop != child_left and diamond_hop != child_right) {
                if (dep_emitted > 0) try ndjson_buf.appendSlice(allocator, ",");
                const c_txt = try std.fmt.allocPrint(
                    allocator,
                    "{{\"name\":\"dep-{d:0>3}\",\"req\":\"1.1.0\",\"features\":[\"tls\",\"json\"]}}",
                    .{diamond_hop},
                );
                defer allocator.free(c_txt);
                try ndjson_buf.appendSlice(allocator, c_txt);
            }

            try ndjson_buf.appendSlice(
                allocator,
                "],\"features\":{\"default\":[\"tls\"],\"tls\":[],\"json\":[]}}\n",
            );
        }

        var rel_buf: [160]u8 = undefined;
        const sparse_rel = pkg_resolver.formatSparseIndexRelPath(pkg_name, &rel_buf).?;
        const idx_path = try std.fmt.allocPrint(
            allocator,
            "{s}/index/default/index/{s}",
            .{ cache.cas_root, sparse_rel },
        );
        defer allocator.free(idx_path);
        if (std.fs.path.dirname(idx_path)) |parent_d| {
            try std.Io.Dir.cwd().createDirPath(io, parent_d);
        }
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = idx_path, .data = ndjson_buf.items });
    }

    const cold_toml_path = try std.fmt.allocPrint(allocator, "{s}/corex.toml", .{ws_dir});
    defer allocator.free(cold_toml_path);
    const cold_toml_text =
        "[package]\nname = \"bench-cold-root\"\nversion = \"0.1.0\"\n" ++
        "[dependencies]\ndep-000 = { version = \"1.1.0\", features = [\"tls\", \"json\"] }\n";

    var cold_interner = try StringInterner.init(allocator);
    errdefer cold_interner.deinit();
    const host_cfg = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.host(), false);
    var cold_manifest_arena = BumpArena.init(allocator);
    errdefer cold_manifest_arena.deinit();
    var parsed_cold = try pkg_manifest.parseManifest(
        allocator,
        &cold_manifest_arena,
        &cold_interner,
        FileId.fromInt(0),
        cold_toml_text,
        &host_cfg,
        null,
    );
    parsed_cold.doc.deinit(allocator);
    var cold_bundle = try pkg_manifest.bundleFromSingleManifest(
        allocator,
        ws_dir,
        cold_toml_path,
        parsed_cold.manifest,
        true,
    );
    errdefer cold_bundle.deinit();

    // [2] Build 50-package `corex.lock` v1 buffer + 50 `.cxtree` manifests (`4` files each) for Benchmark 2:
    var warm_cxtrees: [WARM_MOUNT_PKG_COUNT][]align(8) u8 = undefined;
    var warm_names: [WARM_MOUNT_PKG_COUNT][11]u8 = undefined;
    var initialized_trees: usize = 0;
    errdefer {
        for (warm_cxtrees[0..initialized_trees]) |tb| allocator.free(tb);
    }

    var lock_builder: std.ArrayList(u8) = .empty;
    defer lock_builder.deinit(allocator);
    try lock_builder.appendSlice(
        allocator,
        "# @generated by CoreX. Do not edit manually.\nversion = 1\n" ++
            "root_manifest_blake3 = \"b3:1111111111111111111111111111111111111111111111111111111111111111\"\n",
    );

    for (0..WARM_MOUNT_PKG_COUNT) |pkg_idx| {
        _ = try std.fmt.bufPrint(&warm_names[pkg_idx], "warm-pkg-{d:0>2}", .{pkg_idx});
        const pkg_entries = [_]pkg_cache.CxTreeInputEntry{
            .{ .rel_path = "corex.toml", .file_mode = 0x01, .file_size = 48, .file_blake3 = stub_b3 },
            .{ .rel_path = "src/helpers.cx", .file_mode = 0x01, .file_size = 128, .file_blake3 = stub_b3 },
            .{ .rel_path = "src/root.cx", .file_mode = 0x01, .file_size = 256, .file_blake3 = stub_b3 },
            .{ .rel_path = "src/types.cx", .file_mode = 0x01, .file_size = 96, .file_blake3 = stub_b3 },
        };
        const built = try pkg_cache.buildCxTreeBytes(
            allocator,
            &warm_names[pkg_idx],
            &pkg_entries,
            null,
            Span.init(.none, 0, 0),
        );
        warm_cxtrees[pkg_idx] = built.bytes;
        initialized_trees += 1;

        const w_tree_hex = std.fmt.bytesToHex(built.tree_blake3, .lower);
        const pkg_block = try std.fmt.allocPrint(
            allocator,
            "\n[[package]]\nname = \"{s}\"\nversion = \"1.{d}.0\"\n" ++
                "source = \"registry+https://index.corexlang.dev\"\n" ++
                "checksum = \"b3:{s}\"\ntree_hash = \"b3:{s}\"\n" ++
                "max_caps = [\"net\"]\n" ++
                "cxi_blake3 = \"b3:{s}\"\n" ++
                "features = [\"default\", \"tls\"]\ndependencies = []\n",
            .{ &warm_names[pkg_idx], pkg_idx, &w_tree_hex, &w_tree_hex, &w_tree_hex },
        );
        defer allocator.free(pkg_block);
        try lock_builder.appendSlice(allocator, pkg_block);
    }
    const owned_lock_bytes = try lock_builder.toOwnedSlice(allocator);
    errdefer allocator.free(owned_lock_bytes);

    // [3] Prepare pre-sorted `.cxi` records (`64` fns + `32` types) and `128 KiB` Bao payload for Benchmark 3:
    var cxi_fns: [CXI_BENCH_FN_COUNT]pkg_cxi_seam.CxiFnRecord = undefined;
    for (&cxi_fns, 0..) |*fn_rec, idx| {
        fn_rec.* = .{
            .symbol_path_hash = (@as(u64, idx) + 1) * 0x1000_0003,
            .sig_type_hash = 0x9E37_79B9_7F4A_7C15 ^ @as(u64, idx),
            .shape_hash64 = 0xBF58_476D_1CE4_E5B9 +% @as(u64, idx),
            .summary_bits = .{ idx, 1, 0, 0, 0 },
        };
    }
    var cxi_types: [CXI_BENCH_TYPE_COUNT]pkg_cxi_seam.CxiTypeRecord = undefined;
    for (&cxi_types, 0..) |*ty_rec, idx| {
        ty_rec.* = .{
            .symbol_path_hash = (@as(u64, idx) + 1) * 0x2000_0005,
            .shape_hash64 = 0x94D0_49BB_1331_11EB ^ @as(u64, idx),
            .field_hash64 = 0xD6E8_FEB8_6659_FD93 +% @as(u64, idx),
            .layout_meta = .{ 16, 8, @intCast(idx), 0 },
        };
    }

    const bao_buf = try allocator.alloc(u8, BAO_BENCH_PAYLOAD_BYTES);
    for (bao_buf, 0..) |*byte_ptr, idx| {
        byte_ptr.* = @truncate((idx *% 73) ^ (idx >> 8) ^ 0xA5);
    }
    var bao_root: [32]u8 = undefined;
    std.crypto.hash.Blake3.hash(bao_buf, &bao_root, .{});

    return .{
        .io = io,
        .scratch_dir = scratch_dir,
        .corex_home_dir = corex_home,
        .cold_interner = cold_interner,
        .cold_manifest_arena = cold_manifest_arena,
        .cold_bundle = cold_bundle,
        .warm_lockfile_bytes = owned_lock_bytes,
        .warm_cxtrees = warm_cxtrees,
        .warm_pkg_names = warm_names,
        .cxi_fn_records = cxi_fns,
        .cxi_type_records = cxi_types,
        .bao_payload = bao_buf,
        .bao_root_blake3 = bao_root,
    };
}

/// Case 1 (`mvs_cold_resolve_500_deps`): Cold 500-dependency `Bounded-MVS` + `FeatureBitset512` unification (`< 5 ms`).
fn benchColdMvsResolve500Deps(allocator: std.mem.Allocator) !usize {
    const state = if (shared_bench_state) |*ptr| ptr else return error.MissingBenchState;

    var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &state.cold_interner);
    defer vfs.deinit(state.io);
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    var resolved = (try pkg_resolver.resolveProjectGraph(
        allocator,
        &state.cold_interner,
        &vfs,
        &state.cold_bundle,
        null,
        .{
            .io = state.io,
            .corex_home_dir = state.corex_home_dir,
        },
        &sink,
    )) orelse return error.ColdResolveFailed;
    defer resolved.deinit(allocator);

    if (!resolved.has_used_mvs_fast_path or resolved.packages.len != COLD_RESOLVE_DEP_COUNT + 1) {
        return error.UnexpectedResolvedPackageCount;
    }
    std.mem.doNotOptimizeAway(resolved.packages.len);
    return resolved.packages.len * @sizeOf(pkg_resolver.ResolvedPackageNode);
}

/// Case 2 (`warm_lock_parse_and_vfs_mount_50_pkgs`): Warm `corex.lock` parse + 50-pkg `.cxtree` VFS mount (`< 1 ms`).
fn benchWarmLockParseAndVfsMount50Pkgs(allocator: std.mem.Allocator) !usize {
    const state = &(shared_bench_state orelse return error.MissingBenchState);

    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var lock_arena = BumpArena.init(allocator);
    defer lock_arena.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    const parsed_lock = (try pkg_manifest.parseLockfile(
        allocator,
        &lock_arena,
        &interner,
        FileId.fromInt(0),
        state.warm_lockfile_bytes,
        null,
        &sink,
    )) orelse return error.WarmLockParseFailed;
    if (parsed_lock.packages.len != WARM_MOUNT_PKG_COUNT) return error.UnexpectedLockCount;

    var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &interner);
    defer vfs.deinit(state.io);

    var mounted_file_total: usize = 0;
    for (0..WARM_MOUNT_PKG_COUNT) |pkg_idx| {
        var ver_buf: [16]u8 = undefined;
        const ver_str = try std.fmt.bufPrint(&ver_buf, "1.{d}.0", .{pkg_idx});
        const mounted_ids = try vfs.mountCxTreePackage(
            state.io,
            PackageId.fromInt(@intCast(2 + pkg_idx)),
            &state.warm_pkg_names[pkg_idx],
            ver_str,
            state.warm_cxtrees[pkg_idx],
            state.corex_home_dir,
        );
        mounted_file_total += mounted_ids.len;
        allocator.free(mounted_ids);
    }
    if (mounted_file_total != WARM_MOUNT_PKG_COUNT * 4) return error.UnexpectedMountedFileCount;
    std.mem.doNotOptimizeAway(mounted_file_total);
    return state.warm_lockfile_bytes.len;
}

/// Case 3 (`cxtree_cxi_blake3_and_bao_verify`): `.cxtree` + `.cxi` keyed `BLAKE3` & `128 KiB` Bao streaming throughput.
fn benchCxTreeCxiBlake3AndBaoVerify(allocator: std.mem.Allocator) !usize {
    const state = &(shared_bench_state orelse return error.MissingBenchState);

    var path_storage: [CXTREE_BENCH_ENTRY_COUNT][24]u8 = undefined;
    var tree_inputs: [CXTREE_BENCH_ENTRY_COUNT]pkg_cache.CxTreeInputEntry = undefined;
    for (0..CXTREE_BENCH_ENTRY_COUNT) |idx| {
        const rel_slice = try std.fmt.bufPrint(&path_storage[idx], "src/mod_{d:0>2}.cx", .{idx});
        tree_inputs[idx] = .{
            .rel_path = rel_slice,
            .file_mode = 0x01,
            .file_size = 512 + idx * 16,
            .file_blake3 = state.bao_root_blake3,
        };
    }

    const built_tree = try pkg_cache.buildCxTreeBytes(
        allocator,
        "throughput-pkg",
        &tree_inputs,
        null,
        Span.init(.none, 0, 0),
    );
    defer allocator.free(built_tree.bytes);

    const cxi_bytes = try pkg_cxi_seam.serializeCxiSummary(
        allocator,
        0x0002,
        0x0000,
        &state.cxi_fn_records,
        &state.cxi_type_records,
    );
    defer allocator.free(cxi_bytes);

    const obao_bytes = try pkg_cache.encodeBaoOutboard(allocator, state.bao_payload);
    defer allocator.free(obao_bytes);

    try pkg_cache.verifyBaoOutboard(
        state.bao_root_blake3,
        obao_bytes,
        state.bao_payload,
        null,
        Span.init(.none, 0, 0),
    );
    // Also verify a 4 KiB interior streaming slice `[32768 .. 36864)`:
    try pkg_cache.verifyBaoSlice(
        state.bao_root_blake3,
        obao_bytes,
        32 * 1024,
        4 * 1024,
        state.bao_payload[32 * 1024 .. 36 * 1024],
        null,
        Span.init(.none, 0, 0),
    );

    std.mem.doNotOptimizeAway(built_tree.tree_blake3);
    std.mem.doNotOptimizeAway(cxi_bytes.ptr);
    return built_tree.bytes.len + cxi_bytes.len + state.bao_payload.len + obao_bytes.len;
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 9 package resolution, VFS mount, and CAS cryptographic benchmark suite.
pub fn main(init: std.process.Init) !void {
    shared_bench_state = try preparePhase9BenchState(init.gpa, init.io);
    defer {
        if (shared_bench_state) |*state_ref| {
            state_ref.deinit(init.gpa);
            shared_bench_state = null;
        }
    }

    const cases = [_]BenchCase{
        .{
            .name = "mvs_cold_resolve_500_deps (< 5 ms budget)",
            .run_fn = benchColdMvsResolve500Deps,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "warm_lock_parse_vfs_mount_50_pkgs (< 1 ms budget)",
            .run_fn = benchWarmLockParseAndVfsMount50Pkgs,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "cxtree_cxi_blake3_bao_128k (CAS crypto throughput)",
            .run_fn = benchCxTreeCxiBlake3AndBaoVerify,
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
        "Phase 9 Bounded-MVS (500 Deps), Warm Lock/VFS Mount & CAS Crypto Suite (5 warmup, 30 measured)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, &results);

    if (results[0].stats.median_ns >= MAX_COLD_MVS_MEDIAN_NS) {
        try stdout_writer.interface.flush();
        return error.ColdMvsLatencyBudgetExceeded;
    }
    if (results[1].stats.median_ns >= MAX_WARM_MOUNT_MEDIAN_NS) {
        try stdout_writer.interface.flush();
        return error.WarmLockMountLatencyBudgetExceeded;
    }

    try style_config.writeStatusHeader(
        &stdout_writer.interface,
        .success,
        corex.Glyphs.SUCCESS,
        "budgets",
        "500-dep cold Bounded-MVS (< 5 ms) and 50-pkg warm lock/VFS mount (< 1 ms) verified",
    );
    try stdout_writer.interface.writeByte('\n');
    try stdout_writer.interface.flush();
}

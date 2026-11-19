//! Phase 9 Deterministic Solver Differential, Lossless TOML & CAS/Sandbox Fuzz Suite
//!
//! Exercises `Bounded-MVS` + `PubGrub` CDCL against an exhaustive brute-force SemVer/feature
//! oracle across 260+ random dependency graphs, fuzzes the lossless TOML v1.0 CST, `corex.lock`,
//! and `.cx` `#!` + `---` script frontmatter blanker, and mutates `.cxtree`, Bao `.obao`,
//! Ed25519 / RFC 6962 proofs, and `@embed_bytes` / `@c_import` sandbox paths.
//!
//! Runs deterministically via `Xoroshiro128` in `< 2s` during `zig build test` with zero leaks.

const std = @import("std");
const corex = @import("corex");

const pkg_manifest = corex.pkg_manifest;
const pkg_cache = corex.pkg_cache;
const pkg_resolver = corex.pkg_resolver;
const vfs_sourcemap = corex.vfs_sourcemap;
const style = corex.style;
const BumpArena = corex.BumpArena;
const StringInterner = corex.StringInterner;
const FileId = corex.FileId;
const PackageId = corex.PackageId;
const Span = corex.Span;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticSink = corex.DiagnosticSink;
const DiagnosticRenderer = corex.DiagnosticRenderer;
const StyleConfig = corex.StyleConfig;
const CompilerDb = corex.CompilerDb;
const TargetSpec = corex.TargetSpec;

// ---------------------------------------- TYPES ----------------------------------------

/// Compact dependency edge specification inside a synthetic fuzz candidate version.
const FuzzDepEdge = struct {
    /// Target series index (`1 .. FUZZ_SERIES_COUNT - 1`).
    target_series: u8,
    /// Inclusive minimum version index (`0 .. 2`) allowed on `target_series`.
    min_ver_idx: u8,
    /// Inclusive maximum version index (`0 .. 2`) allowed on `target_series`.
    max_ver_idx: u8,
    /// `true` when this edge is an `optional = true` dependency gated by `dep:<alias>`.
    is_optional: bool = false,
    /// Bitmask of features (`bit 0 = "f1"`, `bit 1 = "f2"`) explicitly requested on `target_series`.
    req_feat_bits: u8 = 0,
};

/// Synthetic candidate version metadata shared by the NDJSON emitter and brute-force oracle.
const FuzzCandidate = struct {
    /// Outgoing dependency edges (`<= 3`, strictly acyclic `series_i < target_series`).
    edges: [3]FuzzDepEdge = undefined,
    /// Active outgoing edge count (`0 .. 3`).
    edge_count: u8 = 0,
    /// Optional target series (`1 .. FUZZ_SERIES_COUNT - 1`) activated by feature `"f1"` (`dep:<alias>`), or `0` if none.
    f1_opt_target: u8 = 0,
    /// Optional target series (`1 .. FUZZ_SERIES_COUNT - 1`) weakly activated (`<alias>?/f2`) by `"f1"`, or `0` if none.
    f1_weak_target: u8 = 0,
    /// `true` when feature `"f1"` implies intra-package feature `"f2"`.
    has_f1_implies_f2: bool = false,
};

/// Complete synthetic multi-series dependency graph instance for differential oracle testing.
const FuzzGraphSpec = struct {
    /// Root package (`series 0`) single candidate (`0.1.0`).
    root_cand: FuzzCandidate = .{},
    /// Root enabled features bitmask (`bit 0 = "f1"`, `bit 1 = "f2"`).
    root_feat_bits: u8 = 0,
    /// External series (`1 .. FUZZ_SERIES_COUNT - 1`), each with `VERSIONS_PER_SERIES` (`3`) candidates.
    ext_cands: [EXT_SERIES_COUNT][VERSIONS_PER_SERIES]FuzzCandidate = undefined,
    /// Per-external-series `[resolution].exclude` bitmask (`bit v == 1` bans candidate `v`).
    exclude_mask: [EXT_SERIES_COUNT]u8 = @splat(0),
};

/// Evaluated assignment of versions and unified features produced by the brute-force oracle.
const OracleModel = struct {
    /// Selected version index (`0 .. 2`) per external series, or `ABSENT_VER` (`0xFF`) when unreachable.
    selected_ver: [EXT_SERIES_COUNT]u8 = @splat(ABSENT_VER),
    /// Unified enabled feature bitmask (`bit 0 = "f1"`, `bit 1 = "f2"`) per external series.
    enabled_feats: [EXT_SERIES_COUNT]u8 = @splat(0),
};

// --------------------------------------- CONSTS ----------------------------------------

/// Number of random multi-package dependency graphs verified against the brute-force oracle.
const SOLVER_DIFF_GRAPH_SEEDS: usize = 260;
/// Number of external compatibility series (`pkg-a@1.x`, `pkg-b@1.x`, `pkg-c@1.x`, `pkg-d@1.x`, `pkg-d@2.x`).
const EXT_SERIES_COUNT: usize = 5;
/// Candidate versions per external compatibility series (`0 -> .0`, `1 -> .1`, `2 -> .2`).
const VERSIONS_PER_SERIES: usize = 3;
/// Sentinel byte marking an inactive/unreachable external series in `OracleModel`.
const ABSENT_VER: u8 = 0xFF;
/// Number of lossless TOML / `corex.lock` / script frontmatter mutation fuzz iterations.
const TOML_FRONTMATTER_FUZZ_SEEDS: usize = 200;
/// Number of adversarial `.cxtree`, Bao `.obao`, RFC 6962, and `@embed_bytes` fuzz iterations.
const ADVERSARIAL_CAS_SANDBOX_SEEDS: usize = 200;

/// Canonical dependency alias strings corresponding to external series `0 .. EXT_SERIES_COUNT - 1`.
const EXT_ALIAS_NAMES = [EXT_SERIES_COUNT][]const u8{
    "pkg-a",
    "pkg-b",
    "pkg-c",
    "pkg-d-v1",
    "pkg-d-v2",
};

/// Canonical registry package names corresponding to external series `0 .. EXT_SERIES_COUNT - 1`.
const EXT_PKG_NAMES = [EXT_SERIES_COUNT][]const u8{
    "pkg-a",
    "pkg-b",
    "pkg-c",
    "pkg-d",
    "pkg-d",
};

/// Major version numbers (`1` vs `2` for coexisting `pkg-d` series) per external series.
const EXT_MAJOR_NUMS = [EXT_SERIES_COUNT]u32{ 1, 1, 1, 1, 2 };

/// Seed TOML corpus mutated during lossless CST and fault-tolerance fuzzing.
const SEED_TOML_CORPUS = [_][]const u8{
    "# Top comment\n[package]\nname = \"fuzz-pkg\"\nversion = \"1.2.3\"\n" ++
        "[dependencies]\nfoo-bar = \"1.0.0\"\n",
    "[package]\nname = \" inline-tbl \"\nversion = \"0.1.0\"\n[dependencies]\n" ++
        "net-io = { version = \">= 1.0.0, < 2.0.0\", features = [\"tls\"], optional = true }\n",
    "[workspace]\nmembers = [\"crates/*\"]\n[security]\n" ++
        "default_dep_policy = \"zero_trust\"\ndefault_allow_caps = [\"net\", \"unsafe_op\"]\n",
    "version = 1\nroot_manifest_blake3 = " ++
        "\"b3:0000000000000000000000000000000000000000000000000000000000000000\"\n" ++
        "[[package]]\nname = \"a\"\nversion = \"1.0.0\"\n",
};

/// Monotonic atomic counter isolating fuzz scratch directories.
var next_fuzz_dir_seq: std.atomic.Value(u32) = .init(1);

// -------------------------------------- INTERNALS --------------------------------------

// ----------- Solver Graph Generator & Brute Oracle ------------

/// Formats the SemVer requirement string selecting `[min_idx .. max_idx]` inside major `major_num`.
fn formatBoundsVersionReq(buf: *[64]u8, major_num: u32, min_idx: u8, max_idx: u8) []const u8 {
    if (min_idx == max_idx) {
        return std.fmt.bufPrint(buf, "={d}.{d}.0", .{ major_num, min_idx }) catch unreachable;
    }
    return std.fmt.bufPrint(
        buf,
        ">={d}.{d}.0, <={d}.{d}.0",
        .{ major_num, min_idx, major_num, max_idx },
    ) catch unreachable;
}

/// Generates a random acyclic `FuzzGraphSpec` with diamond bounds, optional/weak features, and `exclude` bans.
fn generateRandomGraphSpec(rng: std.Random) FuzzGraphSpec {
    var spec = FuzzGraphSpec{};
    spec.root_feat_bits = rng.uintLessThan(u8, 4);

    // Generate `1 .. 3` root edges into `0 .. EXT_SERIES_COUNT - 1`:
    const root_edge_cnt = rng.intRangeAtMost(u8, 1, 3);
    var used_root_targets: u8 = 0;
    for (0..root_edge_cnt) |_| {
        const target_s = rng.uintLessThan(u8, EXT_SERIES_COUNT);
        if ((used_root_targets & (@as(u8, 1) << @intCast(target_s))) != 0) continue;
        used_root_targets |= (@as(u8, 1) << @intCast(target_s));

        const v_a = rng.uintLessThan(u8, VERSIONS_PER_SERIES);
        const v_b = rng.uintLessThan(u8, VERSIONS_PER_SERIES);
        const is_opt = rng.uintLessThan(u8, 4) == 0;
        const idx = spec.root_cand.edge_count;
        spec.root_cand.edges[idx] = .{
            .target_series = target_s + 1,
            .min_ver_idx = @min(v_a, v_b),
            .max_ver_idx = @max(v_a, v_b),
            .is_optional = is_opt,
            .req_feat_bits = rng.uintLessThan(u8, 4),
        };
        spec.root_cand.edge_count += 1;
        if (is_opt and spec.root_cand.f1_opt_target == 0) {
            spec.root_cand.f1_opt_target = target_s + 1;
        }
    }
    spec.root_cand.has_f1_implies_f2 = rng.boolean();

    // Generate external series candidates (`ext_i` only depends on `target > ext_i` to guarantee acyclicity):
    for (0..EXT_SERIES_COUNT) |ext_i| {
        const ban_mode = rng.uintLessThan(u8, 4);
        if (ban_mode == 0) {
            spec.exclude_mask[ext_i] = @as(u8, 1) << @intCast(rng.uintLessThan(u8, VERSIONS_PER_SERIES));
        } else if (ban_mode == 1) {
            // Ban 2 of 3 versions to exercise tight upper/lower bound + exclude conflicts:
            spec.exclude_mask[ext_i] = 0x07 ^ (@as(u8, 1) << @intCast(rng.uintLessThan(u8, VERSIONS_PER_SERIES)));
        }
        for (0..VERSIONS_PER_SERIES) |ver_i| {
            var cand = FuzzCandidate{};
            cand.has_f1_implies_f2 = rng.boolean();
            const avail_targets = EXT_SERIES_COUNT - 1 - ext_i;
            if (avail_targets > 0) {
                const edge_cnt = rng.uintLessThan(u8, @intCast(@min(avail_targets, 2) + 1));
                var used_mask: u8 = 0;
                for (0..edge_cnt) |_| {
                    const rel_t = rng.uintLessThan(u8, @intCast(avail_targets));
                    const target_ext: u8 = @intCast(ext_i + 1 + rel_t);
                    if ((used_mask & (@as(u8, 1) << @intCast(target_ext))) != 0) continue;
                    used_mask |= (@as(u8, 1) << @intCast(target_ext));

                    const v_lo = rng.uintLessThan(u8, VERSIONS_PER_SERIES);
                    const v_hi = rng.uintLessThan(u8, VERSIONS_PER_SERIES);
                    const is_opt = rng.uintLessThan(u8, 3) == 0;
                    cand.edges[cand.edge_count] = .{
                        .target_series = target_ext + 1,
                        .min_ver_idx = @min(v_lo, v_hi),
                        .max_ver_idx = @max(v_lo, v_hi),
                        .is_optional = is_opt,
                        .req_feat_bits = rng.uintLessThan(u8, 4),
                    };
                    cand.edge_count += 1;
                    if (is_opt and cand.f1_opt_target == 0 and rng.boolean()) {
                        cand.f1_opt_target = target_ext + 1;
                    } else if (cand.f1_weak_target == 0 and rng.boolean()) {
                        cand.f1_weak_target = target_ext + 1;
                    }
                }
            }
            spec.ext_cands[ext_i][ver_i] = cand;
        }
    }
    return spec;
}

/// Evaluates whether version tuple `trial_vers` satisfies all reachability, SemVer, feature, and `exclude` rules.
fn evaluateCandidateAssignment(spec: *const FuzzGraphSpec, trial_vers: [EXT_SERIES_COUNT]u8) ?OracleModel {
    var is_reach: [EXT_SERIES_COUNT + 1]bool = @splat(false);
    var feat_bits: [EXT_SERIES_COUNT + 1]u8 = @splat(0);
    var opt_mask: [EXT_SERIES_COUNT + 1]u8 = @splat(0);

    is_reach[0] = true;
    feat_bits[0] = spec.root_feat_bits;

    // Monotone fixed-point propagation over the `(EXT_SERIES_COUNT + 1)` series:
    var has_changed = true;
    while (has_changed) {
        has_changed = false;
        for (0..EXT_SERIES_COUNT + 1) |sid| {
            if (!is_reach[sid]) continue;

            const cand: FuzzCandidate = if (sid == 0) blk_r: {
                break :blk_r spec.root_cand;
            } else blk_e: {
                const v_sel = trial_vers[sid - 1];
                if (v_sel == ABSENT_VER) return null;
                if ((spec.exclude_mask[sid - 1] & (@as(u8, 1) << @intCast(v_sel))) != 0) return null;
                break :blk_e spec.ext_cands[sid - 1][v_sel];
            };

            // [1] Intra-package feature implications (`f1 -> f2`, `f1 -> dep:<opt>`, `f1 -> <weak>?/f2`):
            if ((feat_bits[sid] & 0x01) != 0) {
                if (cand.has_f1_implies_f2 and (feat_bits[sid] & 0x02) == 0) {
                    feat_bits[sid] |= 0x02;
                    has_changed = true;
                }
                if (cand.f1_opt_target > 0) {
                    const bit = @as(u8, 1) << @intCast(cand.f1_opt_target);
                    if ((opt_mask[sid] & bit) == 0) {
                        opt_mask[sid] |= bit;
                        has_changed = true;
                    }
                }
                if (cand.f1_weak_target > 0) {
                    const weak_sid = cand.f1_weak_target;
                    var is_weak_opt = false;
                    for (cand.edges[0..cand.edge_count]) |ed| {
                        if (ed.target_series == weak_sid and ed.is_optional) is_weak_opt = true;
                    }
                    if (!is_weak_opt or is_reach[weak_sid]) {
                        if ((feat_bits[weak_sid] & 0x02) == 0) {
                            feat_bits[weak_sid] |= 0x02;
                            has_changed = true;
                        }
                    }
                }
            }

            // [2] Outgoing dependency edges:
            for (cand.edges[0..cand.edge_count]) |edge| {
                if (edge.is_optional) {
                    const bit = @as(u8, 1) << @intCast(edge.target_series);
                    if ((opt_mask[sid] & bit) == 0) continue;
                }
                const t_sid = edge.target_series;
                if (!is_reach[t_sid]) {
                    is_reach[t_sid] = true;
                    has_changed = true;
                }
                const t_ver = trial_vers[t_sid - 1];
                if (t_ver == ABSENT_VER or t_ver < edge.min_ver_idx or t_ver > edge.max_ver_idx) {
                    return null;
                }
                if ((feat_bits[t_sid] | edge.req_feat_bits) != feat_bits[t_sid]) {
                    feat_bits[t_sid] |= edge.req_feat_bits;
                    has_changed = true;
                }
            }
        }
    }

    // Reject spurious unreached packages (`!is_reach[s]` MUST have `trial_vers[s - 1] == ABSENT_VER`):
    var model = OracleModel{};
    for (0..EXT_SERIES_COUNT) |ext_i| {
        if (is_reach[ext_i + 1]) {
            model.selected_ver[ext_i] = trial_vers[ext_i];
        } else if (trial_vers[ext_i] != ABSENT_VER) {
            return null;
        }
        model.enabled_feats[ext_i] = if (is_reach[ext_i + 1]) feat_bits[ext_i + 1] else 0;
    }
    return model;
}

/// Enumerates all `4^5 = 1,024` candidate tuples to collect every valid minimal `OracleModel`.
fn collectBruteForceValidModels(
    allocator: std.mem.Allocator,
    spec: *const FuzzGraphSpec,
) !std.ArrayListUnmanaged(OracleModel) {
    var models: std.ArrayListUnmanaged(OracleModel) = .empty;
    errdefer models.deinit(allocator);

    const state_radix: usize = VERSIONS_PER_SERIES + 1; // `0..2` = versions, `3` = `ABSENT_VER`.
    const total_combos: usize = state_radix * state_radix * state_radix * state_radix * state_radix;

    for (0..total_combos) |combo_idx| {
        var rem = combo_idx;
        var tuple: [EXT_SERIES_COUNT]u8 = undefined;
        for (0..EXT_SERIES_COUNT) |pos| {
            const digit: u8 = @intCast(rem % state_radix);
            rem /= state_radix;
            tuple[pos] = if (digit == VERSIONS_PER_SERIES) ABSENT_VER else digit;
        }
        if (evaluateCandidateAssignment(spec, tuple)) |valid_model| {
            try models.append(allocator, valid_model);
        }
    }
    return models;
}

/// Serializes `spec` into root `corex.toml` and 4 sparse-index NDJSON files referencing `shared_tree_hex`.
fn writeFuzzGraphFixtures(
    allocator: std.mem.Allocator,
    io: std.Io,
    ws_toml_path: []const u8,
    reg_dir: []const u8,
    spec: *const FuzzGraphSpec,
    shared_tree_hex: *const [64]u8,
) !void {
    // [1] Build root `corex.toml`:
    var toml_buf: std.ArrayList(u8) = .empty;
    defer toml_buf.deinit(allocator);
    try toml_buf.appendSlice(allocator, "[package]\nname = \"fuzz-root\"\nversion = \"0.1.0\"\n");

    try toml_buf.appendSlice(allocator, "\n[features]\ndefault = [");
    var has_any_def = false;
    if ((spec.root_feat_bits & 0x01) != 0) {
        try toml_buf.appendSlice(allocator, "\"f1\"");
        has_any_def = true;
    }
    if ((spec.root_feat_bits & 0x02) != 0) {
        if (has_any_def) try toml_buf.appendSlice(allocator, ", ");
        try toml_buf.appendSlice(allocator, "\"f2\"");
    }
    try toml_buf.appendSlice(allocator, "]\nf1 = [");
    var has_f1_item = false;
    if (spec.root_cand.has_f1_implies_f2) {
        try toml_buf.appendSlice(allocator, "\"f2\"");
        has_f1_item = true;
    }
    if (spec.root_cand.f1_opt_target > 0) {
        if (has_f1_item) try toml_buf.appendSlice(allocator, ", ");
        const opt_alias = EXT_ALIAS_NAMES[spec.root_cand.f1_opt_target - 1];
        const dep_str = try std.fmt.allocPrint(allocator, "\"dep:{s}\"", .{opt_alias});
        defer allocator.free(dep_str);
        try toml_buf.appendSlice(allocator, dep_str);
    }
    try toml_buf.appendSlice(allocator, "]\nf2 = []\n\n[dependencies]\n");

    for (spec.root_cand.edges[0..spec.root_cand.edge_count]) |edge| {
        const ext_idx = edge.target_series - 1;
        var req_buf: [64]u8 = undefined;
        const req_str = formatBoundsVersionReq(&req_buf, EXT_MAJOR_NUMS[ext_idx], edge.min_ver_idx, edge.max_ver_idx);
        const alias_name = EXT_ALIAS_NAMES[ext_idx];
        const pkg_name = EXT_PKG_NAMES[ext_idx];

        const line_prefix = try std.fmt.allocPrint(
            allocator,
            "{s} = {{ package = \"{s}\", version = \"{s}\", optional = {s}, features = [",
            .{ alias_name, pkg_name, req_str, if (edge.is_optional) "true" else "false" },
        );
        defer allocator.free(line_prefix);
        try toml_buf.appendSlice(allocator, line_prefix);
        if ((edge.req_feat_bits & 0x01) != 0) {
            try toml_buf.appendSlice(allocator, "\"f1\"");
            if ((edge.req_feat_bits & 0x02) != 0) try toml_buf.appendSlice(allocator, ", \"f2\"");
        } else if ((edge.req_feat_bits & 0x02) != 0) {
            try toml_buf.appendSlice(allocator, "\"f2\"");
        }
        try toml_buf.appendSlice(allocator, "] }\n");
    }

    try toml_buf.appendSlice(allocator, "\n[resolution]\nexclude = [\n");
    for (0..EXT_SERIES_COUNT) |ext_i| {
        for (0..VERSIONS_PER_SERIES) |ver_i| {
            if ((spec.exclude_mask[ext_i] & (@as(u8, 1) << @intCast(ver_i))) != 0) {
                const ex_line = try std.fmt.allocPrint(
                    allocator,
                    "    \"{s}@={d}.{d}.0\", # CVE-2026-100{d}\n",
                    .{ EXT_PKG_NAMES[ext_i], EXT_MAJOR_NUMS[ext_i], ver_i, ver_i },
                );
                defer allocator.free(ex_line);
                try toml_buf.appendSlice(allocator, ex_line);
            }
        }
    }
    try toml_buf.appendSlice(allocator, "]\n");
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = ws_toml_path, .data = toml_buf.items });

    // [2] Write NDJSON sparse index files (`pkg-a`, `pkg-b`, `pkg-c`, and combined `1.x`+`2.x` `pkg-d`):
    const unique_pkgs = [_]struct { pkg_name: []const u8, series_indices: []const usize }{
        .{ .pkg_name = "pkg-a", .series_indices = &.{0} },
        .{ .pkg_name = "pkg-b", .series_indices = &.{1} },
        .{ .pkg_name = "pkg-c", .series_indices = &.{2} },
        .{ .pkg_name = "pkg-d", .series_indices = &.{ 3, 4 } },
    };

    for (unique_pkgs) |u_pkg| {
        var ndjson_buf: std.ArrayList(u8) = .empty;
        defer ndjson_buf.deinit(allocator);

        for (u_pkg.series_indices) |ext_i| {
            const maj = EXT_MAJOR_NUMS[ext_i];
            for (0..VERSIONS_PER_SERIES) |ver_i| {
                const cand = spec.ext_cands[ext_i][ver_i];
                const row_head = try std.fmt.allocPrint(
                    allocator,
                    "{{\"name\":\"{s}\",\"vers\":\"{d}.{d}.0\",\"tree_hash\":\"b3:{s}\",\"deps\":[",
                    .{ u_pkg.pkg_name, maj, ver_i, shared_tree_hex },
                );
                defer allocator.free(row_head);
                try ndjson_buf.appendSlice(allocator, row_head);

                for (cand.edges[0..cand.edge_count], 0..) |edge, ed_i| {
                    if (ed_i > 0) try ndjson_buf.appendSlice(allocator, ",");
                    const t_ext = edge.target_series - 1;
                    var req_buf: [64]u8 = undefined;
                    const req_s = formatBoundsVersionReq(&req_buf, EXT_MAJOR_NUMS[t_ext], edge.min_ver_idx, edge.max_ver_idx);
                    const dep_json = try std.fmt.allocPrint(
                        allocator,
                        "{{\"name\":\"{s}\",\"package\":\"{s}\",\"req\":\"{s}\",\"optional\":{s},\"features\":[",
                        .{ EXT_ALIAS_NAMES[t_ext], EXT_PKG_NAMES[t_ext], req_s, if (edge.is_optional) "true" else "false" },
                    );
                    defer allocator.free(dep_json);
                    try ndjson_buf.appendSlice(allocator, dep_json);
                    if ((edge.req_feat_bits & 0x01) != 0) {
                        try ndjson_buf.appendSlice(allocator, "\"f1\"");
                        if ((edge.req_feat_bits & 0x02) != 0) try ndjson_buf.appendSlice(allocator, ",\"f2\"");
                    } else if ((edge.req_feat_bits & 0x02) != 0) {
                        try ndjson_buf.appendSlice(allocator, "\"f2\"");
                    }
                    try ndjson_buf.appendSlice(allocator, "]}");
                }

                try ndjson_buf.appendSlice(allocator, "],\"features\":{\"default\":[],\"f1\":[");
                var has_act = false;
                if (cand.has_f1_implies_f2) {
                    try ndjson_buf.appendSlice(allocator, "\"f2\"");
                    has_act = true;
                }
                if (cand.f1_opt_target > 0) {
                    if (has_act) try ndjson_buf.appendSlice(allocator, ",");
                    const opt_s = try std.fmt.allocPrint(
                        allocator,
                        "\"dep:{s}\"",
                        .{EXT_ALIAS_NAMES[cand.f1_opt_target - 1]},
                    );
                    defer allocator.free(opt_s);
                    try ndjson_buf.appendSlice(allocator, opt_s);
                    has_act = true;
                }
                if (cand.f1_weak_target > 0) {
                    if (has_act) try ndjson_buf.appendSlice(allocator, ",");
                    const weak_s = try std.fmt.allocPrint(
                        allocator,
                        "\"{s}?/f2\"",
                        .{EXT_ALIAS_NAMES[cand.f1_weak_target - 1]},
                    );
                    defer allocator.free(weak_s);
                    try ndjson_buf.appendSlice(allocator, weak_s);
                }
                try ndjson_buf.appendSlice(allocator, "],\"f2\":[]}}\n");
            }
        }

        var rel_buf: [160]u8 = undefined;
        const sparse_rel = pkg_resolver.formatSparseIndexRelPath(u_pkg.pkg_name, &rel_buf).?;
        const idx_file_path = try std.fmt.allocPrint(allocator, "{s}/index/{s}", .{ reg_dir, sparse_rel });
        defer allocator.free(idx_file_path);
        if (std.fs.path.dirname(idx_file_path)) |parent_d| {
            try std.Io.Dir.cwd().createDirPath(io, parent_d);
        }
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = idx_file_path, .data = ndjson_buf.items });
    }
}

// ---------------------------------------- MAIN -----------------------------------------

// ----- Fuzz 1: Differential MVS & PubGrub vs Brute Oracle -----

test "test_fuzz_phase9_differential_mvs_pubgrub_vs_bruteforce_oracle" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const seq = next_fuzz_dir_seq.fetchAdd(1, .monotonic);
    const scratch_dir = try std.fmt.allocPrint(allocator, ".zig-cache/tmp/phase9_fuzz_solver_{d}", .{seq});
    defer allocator.free(scratch_dir);
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};

    const corex_home = try std.fmt.allocPrint(allocator, "{s}/home", .{scratch_dir});
    defer allocator.free(corex_home);
    const reg_dir = try std.fmt.allocPrint(allocator, "{s}/reg", .{scratch_dir});
    defer allocator.free(reg_dir);
    const ws_dir = try std.fmt.allocPrint(allocator, "{s}/ws", .{scratch_dir});
    defer allocator.free(ws_dir);
    try std.Io.Dir.cwd().createDirPath(io, ws_dir);

    // Pre-publish one shared minimal `.cxtree` (`src/root.cx`) into `corex_home` so all 260 runs stay in memory:
    var seed_cache = try pkg_cache.PkgCache.init(allocator, corex_home, 64, 2 * 1024 * 1024);
    defer seed_cache.deinit();
    const stub_cx = "pub fn stub() -> i32 = 1;\n";
    var stub_b3: [32]u8 = undefined;
    std.crypto.hash.Blake3.hash(stub_cx, &stub_b3, .{});
    try seed_cache.publishBlob(io, stub_cx, stub_b3, null, Span.init(.none, 0, 0));
    const tree_entries = [_]pkg_cache.CxTreeInputEntry{
        .{ .rel_path = "src/root.cx", .file_mode = 0x01, .file_size = stub_cx.len, .file_blake3 = stub_b3 },
    };
    const shared_tree = try pkg_cache.buildCxTreeBytes(allocator, "fuzz-stub", &tree_entries, null, Span.init(.none, 0, 0));
    defer allocator.free(shared_tree.bytes);
    try seed_cache.publishCxTree(io, shared_tree.bytes, shared_tree.tree_blake3, null, Span.init(.none, 0, 0));
    const shared_tree_hex = std.fmt.bytesToHex(shared_tree.tree_blake3, .lower);

    const ws_toml_path = try std.fmt.allocPrint(allocator, "{s}/corex.toml", .{ws_dir});
    defer allocator.free(ws_toml_path);
    const cfg_env = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.host(), false);

    var prng = std.Random.Xoroshiro128.init(0xC0AE_9009_2026_F022);
    const rng = prng.random();

    var satisfiable_count: usize = 0;
    var unsatisfiable_count: usize = 0;

    for (0..SOLVER_DIFF_GRAPH_SEEDS) |seed_i| {
        const graph_spec = generateRandomGraphSpec(rng);
        var valid_models = try collectBruteForceValidModels(allocator, &graph_spec);
        defer valid_models.deinit(allocator);

        try writeFuzzGraphFixtures(allocator, io, ws_toml_path, reg_dir, &graph_spec, &shared_tree_hex);

        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &interner);
        defer vfs.deinit(io);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();

        const toml_fid = try vfs.resolveOrCreatePath(io, ws_toml_path, .root);
        var bundle = try pkg_manifest.loadWorkspaceManifestBundle(
            io,
            allocator,
            &interner,
            ws_toml_path,
            toml_fid,
            &cfg_env,
            &sink,
        );
        defer bundle.deinit();
        try std.testing.expect(!sink.hasErrors());

        var maybe_resolved = try pkg_resolver.resolveProjectGraph(
            allocator,
            &interner,
            &vfs,
            &bundle,
            null,
            .{ .io = io, .corex_home_dir = corex_home, .local_registry_dir = reg_dir },
            &sink,
        );
        defer if (maybe_resolved) |*res_g| res_g.deinit(allocator);

        if (valid_models.items.len == 0) {
            unsatisfiable_count += 1;
            if (maybe_resolved != null) {
                std.debug.print("Solver fuzz seed {d}: expected UNSAT, but solver returned a graph!\n", .{seed_i});
            }
            try std.testing.expect(maybe_resolved == null);
            var has_e0010 = false;
            for (sink.diagnostics.items) |diag_item| {
                if (diag_item.code == .e0010_unsatisfiable_dependency_graph) has_e0010 = true;
            }
            try std.testing.expect(has_e0010);

            var err_out: std.Io.Writer.Allocating = .init(allocator);
            defer err_out.deinit();
            try DiagnosticRenderer.init(&vfs, &interner, StyleConfig.MONOCHROME).renderAll(&err_out.writer, &sink);
            try std.testing.expect(!style.hasBannedEmoji(err_out.written()));
            try std.testing.expect(std.mem.indexOf(u8, err_out.written(), "PubGrub Conflict Proof Tree") != null);
        } else {
            satisfiable_count += 1;
            if (maybe_resolved == null) {
                std.debug.print("Solver fuzz seed {d}: expected SAT ({d} models), got UNSAT!\n", .{
                    seed_i,
                    valid_models.items.len,
                });
            }
            try std.testing.expect(maybe_resolved != null);
            try std.testing.expect(!sink.hasErrors());

            const resolved = maybe_resolved.?;
            var solver_model = OracleModel{};
            for (resolved.packages) |pkg_node| {
                if (pkg_node.pkg_id == .root) continue;
                for (0..EXT_SERIES_COUNT) |ext_i| {
                    if (std.mem.eql(u8, pkg_node.canonical_name, EXT_PKG_NAMES[ext_i]) and
                        pkg_node.version.major == EXT_MAJOR_NUMS[ext_i])
                    {
                        solver_model.selected_ver[ext_i] = @intCast(pkg_node.version.minor);
                        var f_bits: u8 = 0;
                        for (pkg_node.enabled_features) |feat_str| {
                            if (std.mem.eql(u8, feat_str, "f1")) f_bits |= 0x01;
                            if (std.mem.eql(u8, feat_str, "f2")) f_bits |= 0x02;
                        }
                        solver_model.enabled_feats[ext_i] = f_bits;
                    }
                }
            }

            // [1] Verify `solver_model` is in `valid_models` with exact unified feature parity:
            var has_exact_match = false;
            for (valid_models.items) |cand_m| {
                if (std.mem.eql(u8, &cand_m.selected_ver, &solver_model.selected_ver) and
                    std.mem.eql(u8, &cand_m.enabled_feats, &solver_model.enabled_feats))
                {
                    has_exact_match = true;
                    break;
                }
            }
            if (!has_exact_match) {
                std.debug.print(
                    "Solver fuzz seed {d}: solver assignment {any} (feats {any}) did not match brute-force oracle!\n",
                    .{ seed_i, solver_model.selected_ver, solver_model.enabled_feats },
                );
            }
            try std.testing.expect(has_exact_match);

            // [2] Verify Pareto-minimality (and exact component-wise minimum whenever one exists!):
            for (valid_models.items) |other_m| {
                var is_strictly_smaller = false;
                var is_all_leq = true;
                for (0..EXT_SERIES_COUNT) |ext_i| {
                    const s_val: u16 = if (solver_model.selected_ver[ext_i] == ABSENT_VER) 0 else @as(u16, solver_model.selected_ver[ext_i]) + 1;
                    const o_val: u16 = if (other_m.selected_ver[ext_i] == ABSENT_VER) 0 else @as(u16, other_m.selected_ver[ext_i]) + 1;
                    if (o_val > s_val) is_all_leq = false;
                    if (o_val < s_val) is_strictly_smaller = true;
                }
                try std.testing.expect(!(is_all_leq and is_strictly_smaller));
            }
        }
    }

    try std.testing.expect(satisfiable_count >= 40);
    try std.testing.expect(unsatisfiable_count >= 40);
}

// ------ Fuzz 2: Lossless TOML, Lockfile & Script Prefix -------

test "test_fuzz_phase9_lossless_toml_lockfile_and_script_frontmatter" {
    const allocator = std.testing.allocator;
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    const host_cfg = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.host(), false);

    var prng = std.Random.Xoroshiro128.init(0x7041_C570_2026_BEEF);
    const rng = prng.random();

    for (0..TOML_FRONTMATTER_FUZZ_SEEDS) |seed_i| {
        const base = SEED_TOML_CORPUS[seed_i % SEED_TOML_CORPUS.len];
        var mutated = try allocator.dupe(u8, base);
        defer allocator.free(mutated);

        const mut_mode = rng.uintLessThan(u8, 4);
        if (mut_mode == 0 and mutated.len > 0) {
            mutated[rng.uintLessThan(usize, mutated.len)] = rng.int(u8);
        } else if (mut_mode == 1 and mutated.len > 2) {
            const cut_len = rng.uintLessThan(usize, mutated.len);
            const truncated = try allocator.dupe(u8, mutated[0..cut_len]);
            allocator.free(mutated);
            mutated = truncated;
        } else if (mut_mode == 2 and mutated.len > 0) {
            const flips = rng.intRangeAtMost(usize, 1, 4);
            for (0..flips) |_| {
                mutated[rng.uintLessThan(usize, mutated.len)] ^= (@as(u8, 1) << @intCast(rng.uintLessThan(u8, 8)));
            }
        }

        // [1] Fuzz `parseLockfile`, `parseTomlDocument`, and `parseManifest` on arbitrary byte-mutated/truncated
        //     inputs (zero panics/leaks), and verify lossless token+trivia coverage on structured TOML documents:
        {
            var m_arena = BumpArena.init(allocator);
            defer m_arena.deinit();
            var l_sink = DiagnosticSink.init(allocator);
            defer l_sink.deinit();
            _ = try pkg_manifest.parseLockfile(
                allocator,
                &m_arena,
                &interner,
                FileId.fromInt(102),
                mutated,
                null,
                &l_sink,
            );

            var raw_doc_sink = DiagnosticSink.init(allocator);
            defer raw_doc_sink.deinit();
            var raw_doc = try pkg_manifest.parseTomlDocument(
                allocator,
                FileId.fromInt(104),
                mutated,
                mutated,
                0,
                0,
                false,
                .e0013_invalid_manifest_or_pkg_name,
                &raw_doc_sink,
            );
            raw_doc.deinit(allocator);

            var raw_m_sink = DiagnosticSink.init(allocator);
            defer raw_m_sink.deinit();
            var raw_m = try pkg_manifest.parseManifest(
                allocator,
                &m_arena,
                &interner,
                FileId.fromInt(105),
                mutated,
                &host_cfg,
                &raw_m_sink,
            );
            raw_m.doc.deinit(allocator);

            // Also construct a lexically-closed TOML variant to verify CST lossless spans:
            const extra_comment = rng.intRangeAtMost(u32, 0, 999);
            const structured_toml = try std.fmt.allocPrint(
                allocator,
                "{s}# trailing fuzz comment {d}\n",
                .{ base, extra_comment },
            );
            defer allocator.free(structured_toml);

            var sink = DiagnosticSink.init(allocator);
            defer sink.deinit();
            var doc = try pkg_manifest.parseTomlDocument(
                allocator,
                FileId.fromInt(100),
                structured_toml,
                structured_toml,
                0,
                0,
                false,
                .e0013_invalid_manifest_or_pkg_name,
                &sink,
            );
            defer doc.deinit(allocator);

            var covered = try allocator.alloc(bool, structured_toml.len);
            defer allocator.free(covered);
            @memset(covered, false);
            for (doc.tokens.tokens.items(.byte_offset), doc.tokens.tokens.items(.byte_len)) |off, len| {
                try std.testing.expect(@as(usize, off) + @as(usize, len) <= structured_toml.len);
                for (off..off + len) |b_pos| {
                    try std.testing.expect(!covered[b_pos]);
                    covered[b_pos] = true;
                }
            }
            for (doc.tokens.trivia.items) |triv| {
                try std.testing.expect(@as(usize, triv.byte_offset) + @as(usize, triv.byte_len) <= structured_toml.len);
                for (triv.byte_offset..triv.byte_offset + triv.byte_len) |b_pos| {
                    try std.testing.expect(!covered[b_pos]);
                    covered[b_pos] = true;
                }
            }
            for (structured_toml, 0..) |raw_b, b_pos| {
                if (!covered[b_pos]) {
                    try std.testing.expect(
                        raw_b == ' ' or raw_b == '\t' or raw_b == '\r' or raw_b == '\n',
                    );
                }
            }

            var m_sink = DiagnosticSink.init(allocator);
            defer m_sink.deinit();
            var parsed_m = try pkg_manifest.parseManifest(
                allocator,
                &m_arena,
                &interner,
                FileId.fromInt(101),
                structured_toml,
                &host_cfg,
                &m_sink,
            );
            parsed_m.doc.deinit(allocator);
        }

        // [2] Wrap `mutated` inside `#!` + `---` script frontmatter (mixing LF & CRLF) and verify byte/line preservation:
        {
            const is_crlf = rng.boolean();
            const nl = if (is_crlf) "\r\n" else "\n";
            const cx_tail = "fn main() -> i32 {\n    return 0;\n}\n";
            const full_script = try std.fmt.allocPrint(
                allocator,
                "#!/usr/bin/env -S corex run{s}---{s}{s}{s}---{s}{s}",
                .{ nl, nl, mutated, nl, nl, cx_tail },
            );
            defer allocator.free(full_script);

            var fm_arena = BumpArena.init(allocator);
            defer fm_arena.deinit();
            var fm_sink = DiagnosticSink.init(allocator);
            defer fm_sink.deinit();
            if (try pkg_manifest.extractScriptFrontmatter(&fm_arena, FileId.fromInt(103), full_script, &fm_sink)) |ext| {
                try std.testing.expectEqual(full_script.len, ext.blanked_cx_source.len);
                for (full_script, 0..) |orig_b, b_i| {
                    const blank_b = ext.blanked_cx_source[b_i];
                    if (b_i < ext.prefix_end_byte) {
                        if (orig_b == '\r' or orig_b == '\n') {
                            try std.testing.expectEqual(orig_b, blank_b);
                        } else {
                            try std.testing.expectEqual(@as(u8, ' '), blank_b);
                        }
                    } else {
                        try std.testing.expectEqual(orig_b, blank_b);
                    }
                }
            }
        }
    }
}

// ------ Fuzz 3: Adversarial CxTree, Bao, Tlog & Sandbox -------

test "test_fuzz_phase9_adversarial_cxtree_bao_rfc6962_and_embed_escape" {
    const allocator = std.testing.allocator;
    var prng = std.Random.Xoroshiro128.init(0xBA00_6962_E001_5326);
    const rng = prng.random();

    // [1] Adversarial `.cxtree` path-traversal & case-collision rejection + binary bit-flip rejection:
    const bad_cxtree_paths = [_][]const u8{
        "",
        "/etc/passwd",
        "../secret.cx",
        "src/../../escape.cx",
        "src\\win.cx",
        "C:drive.cx",
        "./dot.cx",
        "src//double.cx",
        "src/trailing/",
        "src/bad\x00nul.cx",
    };
    const zero_b3: [32]u8 = @splat(0x11);
    for (bad_cxtree_paths) |bad_path| {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const bad_entries = [_]pkg_cache.CxTreeInputEntry{
            .{ .rel_path = bad_path, .file_mode = 0x01, .file_size = 4, .file_blake3 = zero_b3 },
        };
        try std.testing.expectError(
            error.CacheIntegrityMismatch,
            pkg_cache.buildCxTreeBytes(allocator, "adv-pkg", &bad_entries, &sink, Span.init(.none, 0, 0)),
        );
    }

    const valid_entries = [_]pkg_cache.CxTreeInputEntry{
        .{ .rel_path = "src/a.cx", .file_mode = 0x01, .file_size = 8, .file_blake3 = zero_b3 },
        .{ .rel_path = "src/b.cx", .file_mode = 0x01, .file_size = 8, .file_blake3 = zero_b3 },
    };
    const base_tree = try pkg_cache.buildCxTreeBytes(allocator, "adv-pkg", &valid_entries, null, Span.init(.none, 0, 0));
    defer allocator.free(base_tree.bytes);

    // Prepare a 6 KiB multi-chunk payload + `.obao` + RFC 6962 4-leaf proof for bit-flip fuzzing:
    var sample_blob: [6144]u8 = undefined;
    rng.bytes(&sample_blob);
    var sample_root_b3: [32]u8 = undefined;
    std.crypto.hash.Blake3.hash(&sample_blob, &sample_root_b3, .{});
    const base_obao = try pkg_cache.encodeBaoOutboard(allocator, &sample_blob);
    defer allocator.free(base_obao);

    const l0 = pkg_cache.computeRfc6962LeafHash("l0");
    const l1 = pkg_cache.computeRfc6962LeafHash("l1");
    const tlog_root = pkg_cache.computeRfc6962NodeHash(l0, l1);
    const valid_proof = [_][32]u8{l1};

    for (0..ADVERSARIAL_CAS_SANDBOX_SEEDS) |_| {
        // Flip random bit in `.cxtree` buffer -> must fail either `validateCxTreeBytes` or `tree_blake3` check:
        const corrupted_tree = try allocator.alignedAlloc(u8, .@"8", base_tree.bytes.len);
        defer allocator.free(corrupted_tree);
        @memcpy(corrupted_tree, base_tree.bytes);
        const flip_pos = rng.uintLessThan(usize, corrupted_tree.len);
        corrupted_tree[flip_pos] ^= (@as(u8, 1) << @intCast(rng.uintLessThan(u8, 8)));

        if (vfs_sourcemap.validateCxTreeBytes(allocator, corrupted_tree)) |view| {
            // Recompute keyed `tree_blake3` over `view` and ensure any entry/path bit-flip changes `tree_blake3`:
            var hasher = std.crypto.hash.Blake3.initKdf(pkg_cache.CXTREE_KDF_CONTEXT, .{});
            for (view.entries) |ent| {
                const rp = view.asEntryPath(ent);
                const mode_b = [1]u8{@intCast(ent.file_mode & 0xFF)};
                const len_le = std.mem.toBytes(std.mem.nativeToLittle(u16, ent.rel_path_len));
                const size_le = std.mem.toBytes(std.mem.nativeToLittle(u64, ent.file_size));
                hasher.update(&mode_b);
                hasher.update(&len_le);
                hasher.update(rp);
                hasher.update(&size_le);
                hasher.update(&ent.file_blake3);
            }
            var recomputed: [32]u8 = undefined;
            hasher.final(&recomputed);
            if (flip_pos >= @sizeOf(vfs_sourcemap.CxTreeHeader) and
                flip_pos < @sizeOf(vfs_sourcemap.CxTreeHeader) + view.entries.len * @sizeOf(vfs_sourcemap.CxTreeEntry))
            {
                // Unless the bit flipped inside the upper unused byte of `file_mode` (rejected if != 0x01/0x02), digest differs:
                try std.testing.expect(!std.mem.eql(u8, &recomputed, &base_tree.tree_blake3));
            }
        } else |_| {}

        // Flip random bit in `.obao` outboard or slice data -> `verifyBaoSlice` MUST reject with `E0015`:
        var obao_copy = try allocator.dupe(u8, base_obao);
        defer allocator.free(obao_copy);
        obao_copy[rng.uintLessThan(usize, obao_copy.len)] ^= (@as(u8, 1) << @intCast(rng.uintLessThan(u8, 8)));
        var bao_sink = DiagnosticSink.init(allocator);
        defer bao_sink.deinit();
        try std.testing.expectError(
            error.CacheIntegrityMismatch,
            pkg_cache.verifyBaoOutboard(sample_root_b3, obao_copy, &sample_blob, &bao_sink, Span.init(.none, 0, 0)),
        );
        try std.testing.expectEqual(
            DiagnosticCode.e0015_cache_integrity_mismatch,
            bao_sink.diagnostics.items[0].code,
        );

        // Flip random bit in RFC 6962 Merkle proof -> `verifyMerkleInclusionProof` MUST reject with `E0015`:
        var tampered_proof = valid_proof;
        tampered_proof[0][rng.uintLessThan(usize, 32)] ^= (@as(u8, 1) << @intCast(rng.uintLessThan(u8, 8)));
        var tlog_sink = DiagnosticSink.init(allocator);
        defer tlog_sink.deinit();
        try std.testing.expectError(
            error.CacheIntegrityMismatch,
            pkg_cache.verifyMerkleInclusionProof(0, 2, "l0", &tampered_proof, tlog_root, &tlog_sink, Span.init(.none, 0, 0)),
        );
        try std.testing.expectEqual(
            DiagnosticCode.e0015_cache_integrity_mismatch,
            tlog_sink.diagnostics.items[0].code,
        );
    }

    // [2] Adversarial `@embed_bytes` & `@c_import` escape strings inside `.cxtree_only` jailed package -> 100% `E0326`:
    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setPackageGraphMounted(true);
    const jailed_pkg = PackageId.fromInt(2);
    try db.setPackageEmbedJail(jailed_pkg, .{
        .cxtree_only = .{ .pkg_id = jailed_pkg, .virtual_root_prefix = "/cx/fuzz-jail@1.0.0" },
    });

    const escape_vectors = [_][]const u8{
        "../secret.bin",
        "assets/../../outside.bin",
        "/etc/shadow",
        "\\\\windows\\\\system32\\\\config",
        "C:\\\\boot.ini",
        "./rel.bin",
        "sub//bad.bin",
    };
    for (escape_vectors, 0..) |esc_vec, idx| {
        const fid = FileId.fromInt(@intCast(300 + idx));
        const cx_src = try std.fmt.allocPrint(
            allocator,
            "pub const DATA: &[u8] = @embed_bytes(\"{s}\");\n",
            .{esc_vec},
        );
        defer allocator.free(cx_src);
        _ = try db.setInput(fid, cx_src, .high);
        db.symbol_table.setFilePackageId(fid, jailed_pkg) catch unreachable;
        const item_tree = try db.extractItemTree(fid);
        const eval_art = try db.evalComptimeDef(item_tree.entries[0].def_id);
        try std.testing.expect(eval_art.has_errors);
        const diags = db.getComptimeDiagnostics(item_tree.entries[0].def_id).?;
        var has_e0326 = false;
        for (diags.diagnostics.items) |d_item| {
            if (d_item.code == .e0326_embed_path_escape) has_e0326 = true;
        }
        try std.testing.expect(has_e0326);
    }
}

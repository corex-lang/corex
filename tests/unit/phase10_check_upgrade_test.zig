//! Phase 10 Check Linter, Autofixer, Capability Auditor & Zero-Legacy Upgrade CLI Unit Suite
//!
//! Exercises end-to-end `corex.router.runCli` workflows across `corex check` (`W0202`, `W0403`,
//! `@allow(W0202)` vs. blanket `E0403`, `--deny-warnings`, `--fix`, `--caps`, `--explain-caps`),
//! `corex upgrade` (`--list`, `--explain`, `--rule`, `--check`, `--accept-caps`, `@generated`), and `corex lsp`.
//!
//! Runs every filesystem test inside an isolated `.zig-cache/phase10_test_*` scratch directory cleaned
//! up via `defer` and asserts zero banned colored emojis across all captured terminal streams.

const std = @import("std");
const corex = @import("corex");

const router = corex.router;
const style = corex.style;
const pkg_manifest = corex.pkg_manifest;
const StringInterner = corex.StringInterner;

// ---------------------------------------- TYPES ----------------------------------------

/// Captured exit status, stdout bytes, and stderr bytes from an in-process `router.runCli` call.
const CliCapture = struct {
    /// Process exit status returned by `router.runCli` (`0` on success).
    exit_code: u8,
    /// Owned UTF-8 stdout bytes written during CLI execution.
    stdout: []u8,
    /// Owned UTF-8 stderr bytes written during CLI execution.
    stderr: []u8,

    /// Releases owned `stdout` and `stderr` slices back to `allocator`.
    fn deinit(self: *CliCapture, allocator: std.mem.Allocator) void {
        allocator.free(self.stdout);
        allocator.free(self.stderr);
        self.* = undefined;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Monotonic atomic counter guaranteeing collision-free `.zig-cache/phase10_test_*` directories.
var next_scratch_seq: std.atomic.Value(u32) = .init(1);

// -------------------------------------- INTERNALS --------------------------------------

// ------------------- Scratch & CLI Helpers --------------------

/// Creates a fresh `.zig-cache/phase10_test_<label>_<seq>` scratch directory on disk.
fn createScratchDir(allocator: std.mem.Allocator, io: std.Io, label: []const u8) ![]u8 {
    const seq_num = next_scratch_seq.fetchAdd(1, .monotonic);
    const dir_path = try std.fmt.allocPrint(
        allocator,
        ".zig-cache/phase10_test_{s}_{d}",
        .{ label, seq_num },
    );
    errdefer allocator.free(dir_path);
    std.Io.Dir.cwd().deleteTree(io, dir_path) catch {};
    try std.Io.Dir.cwd().createDirPath(io, dir_path);
    return dir_path;
}

/// Removes `dir_path` recursively and frees the heap-allocated path string.
fn cleanupScratchDir(allocator: std.mem.Allocator, io: std.Io, dir_path: []u8) void {
    std.Io.Dir.cwd().deleteTree(io, dir_path) catch {};
    allocator.free(dir_path);
}

/// Writes `content` to `<base_dir>/<rel_path>`, creating parent directories automatically.
fn writeScratchFile(
    allocator: std.mem.Allocator,
    io: std.Io,
    base_dir: []const u8,
    rel_path: []const u8,
    content: []const u8,
) ![]u8 {
    const joined_path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ base_dir, rel_path });
    errdefer allocator.free(joined_path);
    if (std.fs.path.dirname(joined_path)) |parent_dir| {
        try std.Io.Dir.cwd().createDirPath(io, parent_dir);
    }
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = joined_path, .data = content });
    return joined_path;
}

/// Reads the full UTF-8 contents of `file_path` from disk (bounded to `4 MiB`).
fn readDiskFileAlloc(allocator: std.mem.Allocator, io: std.Io, file_path: []const u8) ![]u8 {
    return std.Io.Dir.cwd().readFileAlloc(io, file_path, allocator, .limited(4 * 1024 * 1024));
}

/// Executes `router.runCli` with `raw_args`, asserting zero banned emojis in `stdout` and `stderr`.
fn runCliCaptured(
    allocator: std.mem.Allocator,
    io: std.Io,
    environ_map: ?*const std.process.Environ.Map,
    raw_args: []const []const u8,
) !CliCapture {
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();
    var err_alloc = std.Io.Writer.Allocating.init(allocator);
    defer err_alloc.deinit();

    const exit_code = try router.runCli(
        allocator,
        io,
        environ_map,
        raw_args,
        &out_alloc.writer,
        &err_alloc.writer,
    );

    const stdout_copy = try allocator.dupe(u8, out_alloc.written());
    errdefer allocator.free(stdout_copy);
    const stderr_copy = try allocator.dupe(u8, err_alloc.written());
    errdefer allocator.free(stderr_copy);

    try std.testing.expect(!style.hasBannedEmoji(stdout_copy));
    try std.testing.expect(!style.hasBannedEmoji(stderr_copy));

    return .{
        .exit_code = exit_code,
        .stdout = stdout_copy,
        .stderr = stderr_copy,
    };
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_cli_check_w0202_lints_scoped_allow_fix_and_deny_warnings" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const scratch_dir = try createScratchDir(allocator, io, "check_w0202");
    defer cleanupScratchDir(allocator, io, scratch_dir);

    const home_dir = try std.fmt.allocPrint(allocator, "{s}/home", .{scratch_dir});
    defer allocator.free(home_dir);
    try std.Io.Dir.cwd().createDirPath(io, home_dir);

    var env_map = std.process.Environ.Map.init(allocator);
    defer env_map.deinit();
    try env_map.put("COREX_HOME", home_dir);

    // [1] Blanket `@allow`, `@allow(all)`, and `@allow(*)` must fail with `E0403`:
    const blanket_src =
        "@allow\n" ++
        "pub fn bare_allow(opt_val: Option[i32]) {\n" ++
        "    let _used = opt_val;\n" ++
        "    return;\n" ++
        "}\n\n" ++
        "@allow(all)\n" ++
        "pub fn all_allow() {}\n\n" ++
        "@allow(*)\n" ++
        "pub fn star_allow() {}\n";
    const blanket_path = try writeScratchFile(allocator, io, scratch_dir, "blanket_allow.cx", blanket_src);
    defer allocator.free(blanket_path);

    var blanket_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", blanket_path },
    );
    defer blanket_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 1), blanket_res.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, blanket_res.stderr, "E0403") != null);
    try std.testing.expect(std.mem.indexOf(u8, blanket_res.stderr, "forbidden") != null);

    // [2] Non-idiomatic constructs emit `W0202`, while scoped `@allow(W0202)` suppresses cleanly:
    const idioms_src =
        "// Header comment preserved across check --fix\n" ++
        "pub enum ParseIssue {\n" ++
        "    EmptyInput,\n" ++
        "}\n\n" ++
        "pub fn evaluate_flag(\n" ++
        "    cond: bool,\n" ++
        "    maybe_num: Option[i32],\n" ++
        "    outcome: Result[i32, ParseIssue],\n" ++
        ") -> bool {\n" ++
        "    // Keep local trivia inside body:\n" ++
        "    let _keep_opt = maybe_num;\n" ++
        "    let _keep_res = outcome catch 0;\n" ++
        "    if cond {\n" ++
        "        return true;\n" ++
        "    } else {\n" ++
        "        return false;\n" ++
        "    }\n" ++
        "}\n\n" ++
        "pub fn redundant_return_tail(seed: i32) {\n" ++
        "    // Trailing unit return comment preserved:\n" ++
        "    let _keep_seed = seed;\n" ++
        "    return;\n" ++
        "}\n\n" ++
        "@allow(W0202)\n" ++
        "pub fn scoped_suppressed(cond: bool, kept_opt: Option[i32]) -> bool {\n" ++
        "    let _keep = kept_opt;\n" ++
        "    if cond == true {\n" ++
        "        return true;\n" ++
        "    } else {\n" ++
        "        return false;\n" ++
        "    }\n" ++
        "}\n";
    const idioms_path = try writeScratchFile(allocator, io, scratch_dir, "idioms.cx", idioms_src);
    defer allocator.free(idioms_path);

    var check_warn_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", idioms_path },
    );
    defer check_warn_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), check_warn_res.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, check_warn_res.stderr, "W0202") != null);
    try std.testing.expect(std.mem.indexOf(u8, check_warn_res.stderr, "Option") != null);
    try std.testing.expect(std.mem.indexOf(u8, check_warn_res.stderr, "Result") != null);
    try std.testing.expect(std.mem.indexOf(u8, check_warn_res.stderr, "kept_opt") == null);

    // [3] `corex check --deny-warnings` exits `1` with monochrome failure summary:
    var deny_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--deny-warnings", idioms_path },
    );
    defer deny_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 1), deny_res.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, deny_res.stderr, "✗ check failed:") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, deny_res.stderr, "warning(s) treated as errors due to '--deny-warnings'") != null,
    );

    // [4] `corex check --fix` rewrites in-place preserving comments and `@allow(W0202)` items:
    var fix_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--fix", idioms_path },
    );
    defer fix_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), fix_res.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, fix_res.stdout, "✓ check --fix: applied ") != null);
    try std.testing.expect(std.mem.indexOf(u8, fix_res.stdout, "across 1 file(s)") != null);

    const fixed_disk_bytes = try readDiskFileAlloc(allocator, io, idioms_path);
    defer allocator.free(fixed_disk_bytes);
    try std.testing.expect(std.mem.indexOf(u8, fixed_disk_bytes, "// Header comment preserved across check --fix") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_disk_bytes, "// Keep local trivia inside body:") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_disk_bytes, "// Trailing unit return comment preserved:") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_disk_bytes, "maybe_num: i32?") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_disk_bytes, "outcome: i32!ParseIssue") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_disk_bytes, "return cond;") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_disk_bytes, "if cond == true") != null);

    // Dedicated `@allow(W0202)` file emits zero warnings and stays byte-for-byte untouched on disk:
    const sup_only_src =
        "@allow(W0202)\n" ++
        "pub fn untouched_suppressed(kept_opt: Option[i32]) -> bool {\n" ++
        "    let _keep = kept_opt;\n" ++
        "    return true;\n" ++
        "}\n";
    const sup_only_path = try writeScratchFile(allocator, io, scratch_dir, "suppressed_only.cx", sup_only_src);
    defer allocator.free(sup_only_path);

    var sup_fix_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--fix", sup_only_path },
    );
    defer sup_fix_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), sup_fix_res.exit_code);
    const sup_after_bytes = try readDiskFileAlloc(allocator, io, sup_only_path);
    defer allocator.free(sup_after_bytes);
    try std.testing.expectEqualStrings(sup_only_src, sup_after_bytes);

    // [5] Re-running `corex check --deny-warnings` converges cleanly with `exit 0`:
    var recheck_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--deny-warnings", idioms_path },
    );
    defer recheck_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), recheck_res.exit_code);
    try std.testing.expectEqual(@as(usize, 0), recheck_res.stderr.len);
}

test "test_cli_check_deprecated_w0403_caps_table_and_explain_caps" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const scratch_dir = try createScratchDir(allocator, io, "check_depr_caps");
    defer cleanupScratchDir(allocator, io, scratch_dir);

    const home_dir = try std.fmt.allocPrint(allocator, "{s}/home", .{scratch_dir});
    defer allocator.free(home_dir);
    const reg_dir = try std.fmt.allocPrint(allocator, "{s}/reg", .{scratch_dir});
    defer allocator.free(reg_dir);
    try std.Io.Dir.cwd().createDirPath(io, home_dir);
    try std.Io.Dir.cwd().createDirPath(io, reg_dir);

    var env_map = std.process.Environ.Map.init(allocator);
    defer env_map.deinit();
    try env_map.put("COREX_HOME", home_dir);
    try env_map.put("COREX_REGISTRY_DIR", reg_dir);

    // [1] `@deprecated` emits `W0403`; `check --fix` rewrites pure `$0` and skips impure side-effecting `$0`:
    const depr_src =
        "pub fn new_api(val: i32) -> i32 {\n" ++
        "    return val +% 10;\n" ++
        "}\n\n" ++
        "@deprecated(since: \"0.1.0\", reason: \"use new_api\", upgrade: \"new_api($0)\")\n" ++
        "pub fn old_api(val: i32) -> i32 {\n" ++
        "    return new_api(val);\n" ++
        "}\n\n" ++
        "pub fn new_pair(lhs: i32, rhs: i32) -> i32 {\n" ++
        "    return lhs +% rhs;\n" ++
        "}\n\n" ++
        "@deprecated(since: \"0.1.0\", reason: \"use new_pair\", upgrade: \"new_pair($0, $0)\")\n" ++
        "pub fn old_dup(val: i32) -> i32 {\n" ++
        "    return new_pair(val, val);\n" ++
        "}\n\n" ++
        "pub fn next_counter(slot: &mut i32) -> i32 {\n" ++
        "    slot.* = slot.* +% 1;\n" ++
        "    return slot.*;\n" ++
        "}\n\n" ++
        "pub fn call_deprecated(seed: i32) -> i32 {\n" ++
        "    let first_val = old_api(seed);\n" ++
        "    let second_val = old_dup(seed);\n" ++
        "    var counter: i32 = seed;\n" ++
        "    let impure_val = old_dup(next_counter(&mut counter));\n" ++
        "    return first_val +% second_val +% impure_val;\n" ++
        "}\n";
    const depr_path = try writeScratchFile(allocator, io, scratch_dir, "deprecated_demo.cx", depr_src);
    defer allocator.free(depr_path);

    var depr_check = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", depr_path },
    );
    defer depr_check.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), depr_check.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, depr_check.stderr, "W0403") != null);
    try std.testing.expect(std.mem.indexOf(u8, depr_check.stderr, "use new_api") != null);
    try std.testing.expect(std.mem.indexOf(u8, depr_check.stderr, "0.1.0") != null);

    var depr_fix = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--fix", depr_path },
    );
    defer depr_fix.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), depr_fix.exit_code);

    const depr_after = try readDiskFileAlloc(allocator, io, depr_path);
    defer allocator.free(depr_after);
    try std.testing.expect(std.mem.indexOf(u8, depr_after, "let first_val = new_api(seed);") != null);
    try std.testing.expect(std.mem.indexOf(u8, depr_after, "let second_val = new_pair(seed, seed);") != null);
    // Impure `next_counter(&mut counter)` must NOT be duplicated by `check --fix`:
    try std.testing.expect(
        std.mem.indexOf(u8, depr_after, "let impure_val = old_dup(next_counter(&mut counter));") != null,
    );

    // [2] Standalone `.cx` mode `--caps`, `--explain-caps=unsafe_op`, and `--explain-caps unsafe_op <path>`:
    const standalone_src =
        "extern \"C\" fn raw_probe_fn() -> i32;\n\n" ++
        "fn invoke_probe() -> i32 {\n" ++
        "    return unsafe { raw_probe_fn() };\n" ++
        "}\n\n" ++
        "@no_alloc\n" ++
        "@no_panic\n" ++
        "pub fn pure_step(val: i32) -> i32 {\n" ++
        "    return val +% 4;\n" ++
        "}\n\n" ++
        "pub fn run_entry() -> i32 {\n" ++
        "    return invoke_probe() +% pure_step(8);\n" ++
        "}\n";
    const standalone_path = try writeScratchFile(allocator, io, scratch_dir, "standalone_probe.cx", standalone_src);
    defer allocator.free(standalone_path);

    var st_caps = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--caps", standalone_path },
    );
    defer st_caps.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), st_caps.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, st_caps.stdout, "╭") != null);
    try std.testing.expect(std.mem.indexOf(u8, st_caps.stdout, "[ffi, unsafe_op]") != null);
    try std.testing.expect(std.mem.indexOf(u8, st_caps.stdout, "✓ standalone") != null);
    try std.testing.expect(std.mem.indexOf(u8, st_caps.stdout, "1 @no_alloc/@no_panic fns verified") != null);

    var st_exp_eq = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--explain-caps=unsafe_op", standalone_path },
    );
    defer st_exp_eq.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), st_exp_eq.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, st_exp_eq.stdout, "Capability witness:") != null);
    try std.testing.expect(std.mem.indexOf(u8, st_exp_eq.stdout, "▸ unsafe_op") != null);
    try std.testing.expect(std.mem.indexOf(u8, st_exp_eq.stdout, "╭─▸") != null);
    try std.testing.expect(std.mem.indexOf(u8, st_exp_eq.stdout, "╰─▸") != null);

    var st_exp_space = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--explain-caps", "unsafe_op", standalone_path },
    );
    defer st_exp_space.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), st_exp_space.exit_code);
    try std.testing.expectEqualStrings(st_exp_eq.stdout, st_exp_space.stdout);

    // [3] `corex.toml` Workspace mode `--caps` and `--explain-caps` (`=` and space-separated):
    const dep_root_p = try writeScratchFile(
        allocator,
        io,
        reg_dir,
        "packages/ffi-bridge-1.0.0/src/root.cx",
        "extern \"C\" fn host_ping() -> i32;\n\n" ++
            "pub fn ping_bridge() -> i32 {\n" ++
            "    return unsafe { host_ping() };\n" ++
            "}\n",
    );
    defer allocator.free(dep_root_p);
    const idx_p = try writeScratchFile(
        allocator,
        io,
        reg_dir,
        "ff/i-/ffi-bridge",
        "{\"name\":\"ffi-bridge\",\"vers\":\"1.0.0\",\"deps\":[],\"features\":{\"default\":[]}}\n",
    );
    defer allocator.free(idx_p);

    const ws_toml = try writeScratchFile(
        allocator,
        io,
        scratch_dir,
        "ws/corex.toml",
        "[package]\nname = \"audit-ws\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n" ++
            "[dependencies]\nffi-bridge = \"^1.0.0\"\n",
    );
    defer allocator.free(ws_toml);
    const ws_main = try writeScratchFile(
        allocator,
        io,
        scratch_dir,
        "ws/src/main.cx",
        "use ffi_bridge.ping_bridge;\n\n" ++
            "@no_alloc\n@no_panic\npub fn local_pure(num: i32) -> i32 = num +% 1;\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    return ping_bridge() +% local_pure(2);\n" ++
            "}\n",
    );
    defer allocator.free(ws_main);

    const mp_flag = try std.fmt.allocPrint(allocator, "--manifest-path={s}", .{ws_toml});
    defer allocator.free(mp_flag);
    const ws_dir = try std.fmt.allocPrint(allocator, "{s}/ws", .{scratch_dir});
    defer allocator.free(ws_dir);

    var ws_caps = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--caps", mp_flag },
    );
    defer ws_caps.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), ws_caps.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, ws_caps.stdout, "audit-ws") != null);
    try std.testing.expect(std.mem.indexOf(u8, ws_caps.stdout, "ffi-bridge") != null);
    try std.testing.expect(std.mem.indexOf(u8, ws_caps.stdout, "[ffi, unsafe_op]") != null);
    try std.testing.expect(std.mem.indexOf(u8, ws_caps.stdout, "2 package(s) verified") != null);

    var ws_exp_eq = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--explain-caps=unsafe_op", mp_flag },
    );
    defer ws_exp_eq.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), ws_exp_eq.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, ws_exp_eq.stdout, "Capability witness: audit-ws v0.1.0 ▸ unsafe_op") != null);

    var ws_exp_space = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--explain-caps", "unsafe_op", ws_dir },
    );
    defer ws_exp_space.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), ws_exp_space.exit_code);
    try std.testing.expectEqualStrings(ws_exp_eq.stdout, ws_exp_space.stdout);
}

test "test_cli_upgrade_list_explain_surgical_rule_check_and_accept_caps" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const scratch_dir = try createScratchDir(allocator, io, "upgrade_lsp");
    defer cleanupScratchDir(allocator, io, scratch_dir);

    const home_dir = try std.fmt.allocPrint(allocator, "{s}/home", .{scratch_dir});
    defer allocator.free(home_dir);
    const reg_dir = try std.fmt.allocPrint(allocator, "{s}/reg", .{scratch_dir});
    defer allocator.free(reg_dir);
    try std.Io.Dir.cwd().createDirPath(io, home_dir);
    try std.Io.Dir.cwd().createDirPath(io, reg_dir);

    var env_map = std.process.Environ.Map.init(allocator);
    defer env_map.deinit();
    try env_map.put("COREX_HOME", home_dir);
    try env_map.put("COREX_REGISTRY_DIR", reg_dir);

    // [1] `corex upgrade --list`, `--explain=UR-21-00`, `--explain=UR-22-06`, and `E0001` on unknown rule:
    var list_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--list" },
    );
    defer list_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), list_res.exit_code);
    try std.testing.expect(
        std.mem.indexOf(u8, list_res.stdout, "✓ 15 canonical Zero-Legacy upgrade rules registered") != null,
    );
    for (corex.UPGRADE_RULE_CATALOG) |rule_entry| {
        try std.testing.expect(std.mem.indexOf(u8, list_res.stdout, rule_entry.rule_code) != null);
    }

    var exp_21 = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--explain=UR-21-00" },
    );
    defer exp_21.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), exp_21.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, exp_21.stdout, "UR-21-00") != null);
    try std.testing.expect(std.mem.indexOf(u8, exp_21.stdout, "Before:") != null);
    try std.testing.expect(std.mem.indexOf(u8, exp_21.stdout, "After:") != null);

    var exp_22 = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--explain=UR-22-06" },
    );
    defer exp_22.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), exp_22.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, exp_22.stdout, "UR-22-06") != null);
    try std.testing.expect(std.mem.indexOf(u8, exp_22.stdout, "Before:") != null);
    try std.testing.expect(std.mem.indexOf(u8, exp_22.stdout, "After:") != null);

    var exp_bad = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--explain=UR-99-99" },
    );
    defer exp_bad.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 1), exp_bad.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, exp_bad.stderr, "E0001") != null);

    // [2] Surgical `corex upgrade --rule=UR-21-00` rewrites only `std::` -> `cx.`, leaving `Option` & `-> unit`:
    const surgical_src = "use std::io;\npub fn keep_shape(opt_v: Option[i32]) -> unit {}\n";
    const surgical_path = try writeScratchFile(allocator, io, scratch_dir, "surgical.cx", surgical_src);
    defer allocator.free(surgical_path);

    var surgical_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--rule=UR-21-00", surgical_path },
    );
    defer surgical_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), surgical_res.exit_code);

    const surgical_after = try readDiskFileAlloc(allocator, io, surgical_path);
    defer allocator.free(surgical_after);
    try std.testing.expectEqualStrings(
        "use cx.io;\npub fn keep_shape(opt_v: Option[i32]) -> unit {}\n",
        surgical_after,
    );

    // [3] `upgrade --check` (`1` -> `0`), `// @generated` skip, `edition = "2026"`, & skipped child directories:
    const upg_ws_dir = try std.fmt.allocPrint(allocator, "{s}/upg_ws", .{scratch_dir});
    defer allocator.free(upg_ws_dir);

    const upg_toml_path = try writeScratchFile(
        allocator,
        io,
        upg_ws_dir,
        "corex.toml",
        "[package]\nname = \"legacy_pkg\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );
    defer allocator.free(upg_toml_path);

    const upg_main_path = try writeScratchFile(
        allocator,
        io,
        upg_ws_dir,
        "src/main.cx",
        "use std::io;\n\npub fn compute(opt_v: Option[i32]) -> unit {\n    let mut count: i32 = 1;\n    count += 1;\n}\n",
    );
    defer allocator.free(upg_main_path);

    const gen_content = "// @generated by schema-compiler\nuse std::io;\npub fn gen_api() -> unit {}\n";
    const gen_path = try writeScratchFile(allocator, io, upg_ws_dir, "src/generated_api.cx", gen_content);
    defer allocator.free(gen_path);

    const skipped_legacy = "use std::io;\npub fn untouched() -> unit {}\n";
    const skip_zig_cache = try writeScratchFile(allocator, io, upg_ws_dir, ".zig-cache/cached.cx", skipped_legacy);
    defer allocator.free(skip_zig_cache);
    const skip_build = try writeScratchFile(allocator, io, upg_ws_dir, "build/staged.cx", skipped_legacy);
    defer allocator.free(skip_build);
    const skip_zig_out = try writeScratchFile(allocator, io, upg_ws_dir, "zig-out/out.cx", skipped_legacy);
    defer allocator.free(skip_zig_out);

    var pre_check = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--check", upg_ws_dir },
    );
    defer pre_check.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 1), pre_check.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, pre_check.stderr, "upgrade --check") != null);
    try std.testing.expect(std.mem.indexOf(u8, pre_check.stderr, "cached.cx") == null);
    try std.testing.expect(std.mem.indexOf(u8, pre_check.stderr, "staged.cx") == null);
    try std.testing.expect(std.mem.indexOf(u8, pre_check.stderr, "out.cx") == null);
    try std.testing.expect(std.mem.indexOf(u8, pre_check.stderr, "generated_api.cx") == null);

    var apply_upg = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", upg_ws_dir },
    );
    defer apply_upg.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), apply_upg.exit_code);

    const upgraded_toml_bytes = try readDiskFileAlloc(allocator, io, upg_toml_path);
    defer allocator.free(upgraded_toml_bytes);
    try std.testing.expect(std.mem.indexOf(u8, upgraded_toml_bytes, "name = \"legacy-pkg\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, upgraded_toml_bytes, "edition = \"2026\"") != null);

    const upgraded_main_bytes = try readDiskFileAlloc(allocator, io, upg_main_path);
    defer allocator.free(upgraded_main_bytes);
    try std.testing.expect(std.mem.indexOf(u8, upgraded_main_bytes, "use cx.io;") != null);
    try std.testing.expect(std.mem.indexOf(u8, upgraded_main_bytes, "opt_v: i32?") != null);
    try std.testing.expect(std.mem.indexOf(u8, upgraded_main_bytes, "var count: i32 = 1;") != null);

    const gen_after = try readDiskFileAlloc(allocator, io, gen_path);
    defer allocator.free(gen_after);
    try std.testing.expectEqualStrings(gen_content, gen_after);

    for ([_][]const u8{ skip_zig_cache, skip_build, skip_zig_out }) |skipped_p| {
        const skipped_after = try readDiskFileAlloc(allocator, io, skipped_p);
        defer allocator.free(skipped_after);
        try std.testing.expectEqualStrings(skipped_legacy, skipped_after);
    }

    var post_check = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--check", upg_ws_dir },
    );
    defer post_check.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), post_check.exit_code);
    try std.testing.expect(
        std.mem.indexOf(u8, post_check.stdout, "✓ upgrade --check: all files conform to canonical CoreX 2026") != null,
    );

    // [4] `--accept-caps` updates `corex.toml`/`corex.lock`, and NEVER overrides explicit `deny_caps`:
    const cap_dep_root = try writeScratchFile(
        allocator,
        io,
        reg_dir,
        "packages/cap-lib-1.0.0/src/root.cx",
        "extern \"C\" fn raw_cap_call() -> i32;\n\n" ++
            "pub fn run_cap() -> i32 {\n" ++
            "    return unsafe { raw_cap_call() };\n" ++
            "}\n",
    );
    defer allocator.free(cap_dep_root);
    const cap_dep_idx = try writeScratchFile(
        allocator,
        io,
        reg_dir,
        "ca/p-/cap-lib",
        "{\"name\":\"cap-lib\",\"vers\":\"1.0.0\",\"deps\":[],\"features\":{\"default\":[]}}\n",
    );
    defer allocator.free(cap_dep_idx);

    const caps_ws_dir = try std.fmt.allocPrint(allocator, "{s}/caps_ws", .{scratch_dir});
    defer allocator.free(caps_ws_dir);
    const caps_toml_path = try writeScratchFile(
        allocator,
        io,
        caps_ws_dir,
        "corex.toml",
        "[package]\nname = \"caps-consumer\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n" ++
            "[dependencies]\ncap-lib = { version = \"1.0.0\", allow_caps = [\"ffi\"] }\n",
    );
    defer allocator.free(caps_toml_path);
    const caps_main_path = try writeScratchFile(
        allocator,
        io,
        caps_ws_dir,
        "src/main.cx",
        "use cap_lib.run_cap;\npub fn main() -> i32 { return run_cap(); }\n",
    );
    defer allocator.free(caps_main_path);

    var lock_interner = try StringInterner.init(allocator);
    defer lock_interner.deinit();
    const sem_100 = (try pkg_manifest.SemVer.parse(&lock_interner, "1.0.0")).?;
    const lock_pkgs = [_]pkg_manifest.LockPackage{.{
        .name = try lock_interner.intern("cap-lib"),
        .version = sem_100,
        .source = try lock_interner.intern("registry+https://index.corexlang.dev"),
        .tree_hash = @splat(0x33),
        .max_caps = .{ .ffi = true },
        .cxi_blake3 = @splat(0x44),
    }};
    const init_lock = pkg_manifest.Lockfile{
        .root_manifest_blake3 = @splat(0x11),
        .packages = &lock_pkgs,
    };
    const init_lock_bytes = try pkg_manifest.serializeLockfile(allocator, &init_lock, &lock_interner);
    defer allocator.free(init_lock_bytes);
    const caps_lock_path = try writeScratchFile(allocator, io, caps_ws_dir, "corex.lock", init_lock_bytes);
    defer allocator.free(caps_lock_path);

    var unaccepted_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--accept-caps=fs", caps_ws_dir },
    );
    defer unaccepted_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 1), unaccepted_res.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, unaccepted_res.stderr, "E0324") != null);

    var accepted_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--accept-caps=unsafe_op", caps_ws_dir },
    );
    defer accepted_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), accepted_res.exit_code);

    const updated_caps_toml = try readDiskFileAlloc(allocator, io, caps_toml_path);
    defer allocator.free(updated_caps_toml);
    try std.testing.expect(
        std.mem.indexOf(u8, updated_caps_toml, "allow_caps = [\"ffi\", \"unsafe_op\"]") != null,
    );
    const updated_caps_lock = try readDiskFileAlloc(allocator, io, caps_lock_path);
    defer allocator.free(updated_caps_lock);
    try std.testing.expect(
        std.mem.indexOf(u8, updated_caps_lock, "max_caps = [\"ffi\", \"unsafe_op\"]") != null,
    );

    // Explicit `deny_caps = ["unsafe_op"]` must NEVER be overridden even by bare `--accept-caps`:
    const deny_toml_path = try writeScratchFile(
        allocator,
        io,
        caps_ws_dir,
        "corex.toml",
        "[package]\nname = \"caps-consumer\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n" ++
            "[dependencies]\ncap-lib = { version = \"1.0.0\", allow_caps = [\"ffi\"] }\n\n" ++
            "[security]\ndeny_caps = [\"unsafe_op\"]\n",
    );
    defer allocator.free(deny_toml_path);

    var denied_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--accept-caps", caps_ws_dir },
    );
    defer denied_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 1), denied_res.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, denied_res.stderr, "E0324") != null);
    try std.testing.expect(std.mem.indexOf(u8, denied_res.stderr, "never overrides `deny_caps`") != null);

    // [5] `corex lsp --help` succeeds cleanly, while an unexpected positional arg emits `E0001`:
    var lsp_help = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "lsp", "--help" },
    );
    defer lsp_help.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), lsp_help.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, lsp_help.stdout, "corex lsp") != null);
    try std.testing.expect(std.mem.indexOf(u8, lsp_help.stdout, "--stdio") != null);
    try std.testing.expect(std.mem.indexOf(u8, lsp_help.stdout, "--internal-core") != null);

    var lsp_pos_err = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "lsp", "unexpected_file.cx" },
    );
    defer lsp_pos_err.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 1), lsp_pos_err.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, lsp_pos_err.stderr, "E0001") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, lsp_pos_err.stderr, "unexpected positional argument `unexpected_file.cx`") != null,
    );
}

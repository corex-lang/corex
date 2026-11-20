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
    const dir_path = try std.fmt.allocPrint(
        allocator,
        ".zig-cache/phase10_test_{s}_{d}",
        .{ label, next_scratch_seq.fetchAdd(1, .monotonic) },
    );
    errdefer allocator.free(dir_path);
    std.Io.Dir.cwd().deleteTree(io, dir_path) catch {};
    try std.Io.Dir.cwd().createDirPath(io, dir_path);
    return dir_path;
}

/// Writes `content` to `<base_dir>/<rel_path>` and frees the temporary joined path buffer immediately.
fn writeScratchFileDiscard(
    allocator: std.mem.Allocator,
    io: std.Io,
    base_dir: []const u8,
    rel_path: []const u8,
    content: []const u8,
) !void {
    const joined_path = try writeScratchFile(allocator, io, base_dir, rel_path, content);
    allocator.free(joined_path);
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
        std.mem.indexOf(u8, deny_res.stderr, "warning(s) treated as errors due to `--deny-warnings`") != null,
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
    try writeScratchFileDiscard(
        allocator,
        io,
        reg_dir,
        "packages/ffi-bridge-1.0.0/src/root.cx",
        "extern \"C\" fn host_ping() -> i32;\n\n" ++
            "pub fn ping_bridge() -> i32 {\n" ++
            "    return unsafe { host_ping() };\n" ++
            "}\n",
    );
    try writeScratchFileDiscard(
        allocator,
        io,
        reg_dir,
        "ff/i-/ffi-bridge",
        "{\"name\":\"ffi-bridge\",\"vers\":\"1.0.0\",\"deps\":[],\"features\":{\"default\":[]}}\n",
    );

    const ws_toml = try writeScratchFile(
        allocator,
        io,
        scratch_dir,
        "ws/corex.toml",
        "[package]\nname = \"audit-ws\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n" ++
            "[dependencies]\nffi-bridge = \"^1.0.0\"\n",
    );
    defer allocator.free(ws_toml);
    try writeScratchFileDiscard(
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
    const surgical_path = try writeScratchFile(
        allocator,
        io,
        scratch_dir,
        "surgical.cx",
        "use std::io;\npub fn keep_shape(opt_v: Option[i32]) -> unit {}\n",
    );
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
    try writeScratchFileDiscard(
        allocator,
        io,
        reg_dir,
        "packages/cap-lib-1.0.0/src/root.cx",
        "extern \"C\" fn raw_cap_call() -> i32;\n\n" ++
            "pub fn run_cap() -> i32 {\n" ++
            "    return unsafe { raw_cap_call() };\n" ++
            "}\n",
    );
    try writeScratchFileDiscard(
        allocator,
        io,
        reg_dir,
        "ca/p-/cap-lib",
        "{\"name\":\"cap-lib\",\"vers\":\"1.0.0\",\"deps\":[],\"features\":{\"default\":[]}}\n",
    );

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
    try writeScratchFileDiscard(
        allocator,
        io,
        caps_ws_dir,
        "src/main.cx",
        "use cap_lib.run_cap;\npub fn main() -> i32 { return run_cap(); }\n",
    );

    var lock_interner = try StringInterner.init(allocator);
    defer lock_interner.deinit();
    const lock_pkgs = [_]pkg_manifest.LockPackage{.{
        .name = try lock_interner.intern("cap-lib"),
        .version = (try pkg_manifest.SemVer.parse(&lock_interner, "1.0.0")).?,
        .source = try lock_interner.intern("registry+https://index.corexlang.dev"),
        .tree_hash = @splat(0x33),
        .max_caps = .{ .ffi = true },
        .cxi_blake3 = @splat(0x44),
    }};
    const init_lock_bytes = try pkg_manifest.serializeLockfile(
        allocator,
        &(pkg_manifest.Lockfile{
            .root_manifest_blake3 = @splat(0x11),
            .packages = &lock_pkgs,
        }),
        &lock_interner,
    );
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
    try writeScratchFileDiscard(
        allocator,
        io,
        caps_ws_dir,
        "corex.toml",
        "[package]\nname = \"caps-consumer\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n" ++
            "[dependencies]\ncap-lib = { version = \"1.0.0\", allow_caps = [\"ffi\"] }\n\n" ++
            "[security]\ndeny_caps = [\"unsafe_op\"]\n",
    );

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

test "test_phase10_w0202_precedence_ur2204_array_multifile_upgrade_and_accept_caps_check" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const scratch_dir = try createScratchDir(allocator, io, "hardening_reg");
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

    // [1] `W0202` `corex check --fix` preserves `(a or b) and c`, `(a and b) |> tap`, `(a == b) == c`, and `if ({ … })`:
    const w0202_prec_src =
        "pub fn eval_guard(flag_a: bool, flag_b: bool, flag_c: bool) -> bool {\n" ++
        "    return (flag_a or flag_b) == true and flag_c;\n" ++
        "}\n\n" ++
        "pub fn tap_bool(flag_v: bool) -> bool {\n" ++
        "    return flag_v;\n" ++
        "}\n\n" ++
        "pub fn eval_pipe(flag_a: bool, flag_b: bool) -> bool {\n" ++
        "    return ((flag_a and flag_b) == true) |> tap_bool();\n" ++
        "}\n\n" ++
        "pub fn eval_eq_chain(flag_a: bool, flag_b: bool, flag_c: bool) -> bool {\n" ++
        "    return ((flag_a == flag_b) == true) == flag_c;\n" ++
        "}\n\n" ++
        "pub fn eval_block_if(seed: i32) -> i32 {\n" ++
        "    if ({\n" ++
        "        let is_ok = seed > 0;\n" ++
        "        is_ok\n" ++
        "    }) == true {\n" ++
        "        return 1;\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n\n" ++
        "pub const VERIFY_GUARD_TRUTH: bool = comptime {\n" ++
        "    @compile_assert(not eval_guard(true, false, false));\n" ++
        "    @compile_assert(eval_guard(true, false, true));\n" ++
        "    true\n" ++
        "};\n";
    const w0202_prec_path = try writeScratchFile(allocator, io, scratch_dir, "w0202_prec.cx", w0202_prec_src);
    defer allocator.free(w0202_prec_path);

    {
        var mem_db = try corex.CompilerDb.init(allocator);
        defer mem_db.deinit();
        const mem_fid = corex.FileId.fromInt(1);
        _ = try mem_db.setInput(mem_fid, w0202_prec_src, .low);
        const mem_fix_rep = try corex.check_audit.applyCheckFixesOnDb(allocator, &mem_db, .{
            .is_writing_to_disk = false,
            .candidate_files = &.{mem_fid},
        });
        try std.testing.expect(!mem_fix_rep.is_rolled_back);
        try std.testing.expect(mem_fix_rep.applied_fix_count >= 4);
    }

    var prec_fix_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--fix", w0202_prec_path },
    );
    defer prec_fix_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), prec_fix_res.exit_code);

    const prec_after = try readDiskFileAlloc(allocator, io, w0202_prec_path);
    defer allocator.free(prec_after);
    try std.testing.expect(std.mem.indexOf(u8, prec_after, "return (flag_a or flag_b) and flag_c;") != null);
    try std.testing.expect(std.mem.indexOf(u8, prec_after, "flag_a or flag_b and flag_c") == null);
    try std.testing.expect(std.mem.indexOf(u8, prec_after, "(flag_a and flag_b) |> tap_bool()") != null);
    try std.testing.expect(std.mem.indexOf(u8, prec_after, "(flag_a == flag_b) == flag_c") != null);
    try std.testing.expect(std.mem.indexOf(u8, prec_after, "== true") == null);
    try std.testing.expect(std.mem.indexOf(u8, prec_after, "let is_ok = seed > 0;") != null);

    var prec_verify_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--deny-warnings", w0202_prec_path },
    );
    defer prec_verify_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), prec_verify_res.exit_code);

    // [2] `UR-22-04` preserves `[u8; 16]` array types while upgrading `;` fields, `*const u8`, & per-arg `.ptr`:
    const ur2204_src =
        "pub struct PacketHeader {\n" ++
        "    pub raw_ptr: *const u8;\n" ++
        "    pub header: [u8; 16];\n" ++
        "    pub tag_id: u32;\n" ++
        "}\n\n" ++
        "pub fn inspect_ptrs(ro_ptr: *u8, rw_ptr: *mut u8) -> usize {\n" ++
        "    let _ = ro_ptr;\n" ++
        "    let _ = rw_ptr;\n" ++
        "    return 16;\n" ++
        "}\n\n" ++
        "pub fn pass_array_ptrs() -> usize {\n" ++
        "    var first_buf: [u8; 4] = [0, 0, 0, 0];\n" ++
        "    var second_buf: [u8; 4] = [1, 1, 1, 1];\n" ++
        "    return inspect_ptrs(first_buf.ptr, second_buf.ptr);\n" ++
        "}\n";
    const ur2204_path = try writeScratchFile(allocator, io, scratch_dir, "ur2204_array.cx", ur2204_src);
    defer allocator.free(ur2204_path);

    var ur2204_upg = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", ur2204_path },
    );
    defer ur2204_upg.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), ur2204_upg.exit_code);

    const ur2204_after = try readDiskFileAlloc(allocator, io, ur2204_path);
    defer allocator.free(ur2204_after);
    try std.testing.expect(std.mem.indexOf(u8, ur2204_after, "pub raw_ptr: *u8,") != null);
    try std.testing.expect(std.mem.indexOf(u8, ur2204_after, "pub header: [u8; 16],") != null);
    try std.testing.expect(std.mem.indexOf(u8, ur2204_after, "[u8, 16]") == null);
    try std.testing.expect(
        std.mem.indexOf(u8, ur2204_after, "inspect_ptrs(first_buf.as_ptr(), second_buf.as_mut_ptr())") != null,
    );

    var ur2204_check = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--deny-warnings", ur2204_path },
    );
    defer ur2204_check.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), ur2204_check.exit_code);

    // [3] Multi-file workspace `corex upgrade` resolves `mod legacy;` `@deprecated` + syncs `corex.lock` hash:
    const multi_ws_dir = try std.fmt.allocPrint(allocator, "{s}/multi_ws", .{scratch_dir});
    defer allocator.free(multi_ws_dir);
    const multi_toml_path = try writeScratchFile(
        allocator,
        io,
        multi_ws_dir,
        "corex.toml",
        "[package]\nname = \"multi-upg\"\nversion = \"0.1.0\"\nedition = \"2026\"\n",
    );
    defer allocator.free(multi_toml_path);
    try writeScratchFileDiscard(
        allocator,
        io,
        multi_ws_dir,
        "src/legacy.cx",
        "pub fn modern(val: i32) -> i32 {\n" ++
            "    return val +% 5;\n" ++
            "}\n\n" ++
            "@deprecated(since: \"0.2.0\", reason: \"use modern\", upgrade: \"modern($0)\")\n" ++
            "pub fn old_api(val: i32) -> i32 {\n" ++
            "    return modern(val);\n" ++
            "}\n",
    );
    const multi_main_path = try writeScratchFile(
        allocator,
        io,
        multi_ws_dir,
        "src/main.cx",
        "mod legacy;\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    return legacy.old_api(10);\n" ++
            "}\n",
    );
    defer allocator.free(multi_main_path);

    const multi_mp_flag = try std.fmt.allocPrint(allocator, "--manifest-path={s}", .{multi_toml_path});
    defer allocator.free(multi_mp_flag);
    var seed_lock_check = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", multi_mp_flag },
    );
    defer seed_lock_check.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), seed_lock_check.exit_code);

    // Introduce legacy `name = "multi_upg"` and `edition = "2024"` so `corex.lock` hash must be synced on upgrade:
    try writeScratchFileDiscard(
        allocator,
        io,
        multi_ws_dir,
        "corex.toml",
        "[package]\nname = \"multi_upg\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );

    var multi_upg_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", multi_ws_dir },
    );
    defer multi_upg_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), multi_upg_res.exit_code);

    const multi_main_after = try readDiskFileAlloc(allocator, io, multi_main_path);
    defer allocator.free(multi_main_after);
    try std.testing.expect(std.mem.indexOf(u8, multi_main_after, "old_api") == null);
    try std.testing.expect(std.mem.indexOf(u8, multi_main_after, "modern(10)") != null);

    var locked_after_upg = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--locked", "--deny-warnings", multi_mp_flag },
    );
    defer locked_after_upg.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), locked_after_upg.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, locked_after_upg.stderr, "E0014") == null);

    // [4] `corex upgrade --check --accept-caps` exits `1` on capability drift (including legacy manifests):
    try writeScratchFileDiscard(
        allocator,
        io,
        reg_dir,
        "packages/drift-lib-1.0.0/src/root.cx",
        "extern \"C\" fn drift_ffi_call() -> i32;\n\n" ++
            "pub fn invoke_drift() -> i32 {\n" ++
            "    return unsafe { drift_ffi_call() };\n" ++
            "}\n",
    );
    try writeScratchFileDiscard(
        allocator,
        io,
        reg_dir,
        "dr/if/drift-lib",
        "{\"name\":\"drift-lib\",\"vers\":\"1.0.0\",\"deps\":[],\"features\":{\"default\":[]}}\n",
    );

    const drift_ws_dir = try std.fmt.allocPrint(allocator, "{s}/drift_ws", .{scratch_dir});
    defer allocator.free(drift_ws_dir);
    const legacy_drift_toml =
        "[package]\nname = \"drift-app\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n" ++
        "[dev-dependencies]\ndrift-lib = { version = \"1.0.0\", allow_caps = [\"unsafe\"] }\n";
    const drift_toml_path = try writeScratchFile(allocator, io, drift_ws_dir, "corex.toml", legacy_drift_toml);
    defer allocator.free(drift_toml_path);
    try writeScratchFileDiscard(
        allocator,
        io,
        drift_ws_dir,
        "src/main.cx",
        "pub fn main() -> i32 {\n    return 0;\n}\n",
    );

    var drift_interner = try StringInterner.init(allocator);
    defer drift_interner.deinit();
    const drift_lock_pkgs = [_]pkg_manifest.LockPackage{.{
        .name = try drift_interner.intern("drift-lib"),
        .version = (try pkg_manifest.SemVer.parse(&drift_interner, "1.0.0")).?,
        .source = try drift_interner.intern("registry+https://index.corexlang.dev"),
        .tree_hash = @splat(0x55),
        .max_caps = .{ .unsafe_op = true },
        .cxi_blake3 = @splat(0x66),
    }};
    const drift_lock_bytes = try pkg_manifest.serializeLockfile(
        allocator,
        &(pkg_manifest.Lockfile{
            .root_manifest_blake3 = @splat(0x22),
            .packages = &drift_lock_pkgs,
        }),
        &drift_interner,
    );
    defer allocator.free(drift_lock_bytes);
    try writeScratchFileDiscard(allocator, io, drift_ws_dir, "corex.lock", drift_lock_bytes);

    var check_accept_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--check", "--accept-caps", drift_ws_dir },
    );
    defer check_accept_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 1), check_accept_res.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, check_accept_res.stderr, "pending manifest migration") != null);
    try std.testing.expect(std.mem.indexOf(u8, check_accept_res.stderr, "pending lockfile migration") != null);

    // Ensure `--check --accept-caps` did not mutate `corex.toml` or `corex.lock` on disk:
    const toml_unchanged = try readDiskFileAlloc(allocator, io, drift_toml_path);
    defer allocator.free(toml_unchanged);
    try std.testing.expectEqualStrings(legacy_drift_toml, toml_unchanged);

    // Apply `corex upgrade --accept-caps` and verify subsequent `--check --accept-caps` exits `0`:
    var apply_accept_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--accept-caps", drift_ws_dir },
    );
    defer apply_accept_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), apply_accept_res.exit_code);

    var clean_accept_check = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--check", "--accept-caps", drift_ws_dir },
    );
    defer clean_accept_check.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), clean_accept_check.exit_code);

    // Lockfile-only drift (`corex.toml` already canonical) still exits `1` under `--check --accept-caps`:
    try writeScratchFileDiscard(allocator, io, drift_ws_dir, "corex.lock", drift_lock_bytes);
    var lock_only_drift = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", "--check", "--accept-caps", drift_ws_dir },
    );
    defer lock_only_drift.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 1), lock_only_drift.exit_code);
    try std.testing.expect(std.mem.indexOf(u8, lock_only_drift.stderr, "pending lockfile migration") != null);

    // [5] `UR-22-00` preserves `r"""\n\{raw\}\n"""` and `br"""\n\{bytes\}\n"""` inside `{ … }` while upgrading `::`:
    const interp_src =
        "pub mod tag_mod {\n" ++
        "    pub fn pick(first_s: str, second_b: &[u8]) -> i32 {\n" ++
        "        let _ = first_s;\n" ++
        "        let _ = second_b;\n" ++
        "        return 7;\n" ++
        "    }\n" ++
        "}\n\n" ++
        "pub fn trigger_msg() -> never {\n" ++
        "    @panic(\"\"\"\n" ++
        "        val=\\{legacy\\}:{tag_mod::pick(\n" ++
        "            r\"\"\"\n" ++
        "            \\{raw\\}\n" ++
        "            \"\"\",\n" ++
        "            br\"\"\"\n" ++
        "            \\{bytes\\}\n" ++
        "            \"\"\",\n" ++
        "        )}\n" ++
        "        \"\"\");\n" ++
        "}\n";
    const interp_path = try writeScratchFile(allocator, io, scratch_dir, "interp_holes.cx", interp_src);
    defer allocator.free(interp_path);

    {
        var mem_upg = try corex.upgrade_engine.upgradeSource(
            allocator,
            interp_src,
            corex.FileId.fromInt(99),
            .{},
        );
        defer mem_upg.deinit(allocator);
        try std.testing.expect(mem_upg.is_changed);
        try std.testing.expect(!mem_upg.is_rolled_back);
    }

    var interp_upg_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "upgrade", interp_path },
    );
    defer interp_upg_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), interp_upg_res.exit_code);

    const interp_after = try readDiskFileAlloc(allocator, io, interp_path);
    defer allocator.free(interp_after);
    try std.testing.expect(std.mem.indexOf(u8, interp_after, "val={{legacy}}:{tag_mod.pick(") != null);
    try std.testing.expect(std.mem.indexOf(u8, interp_after, "tag_mod::pick") == null);
    try std.testing.expect(std.mem.indexOf(u8, interp_after, "\\{raw\\}") != null);
    try std.testing.expect(std.mem.indexOf(u8, interp_after, "\\{bytes\\}") != null);

    var interp_chk_res = try runCliCaptured(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--deny-warnings", interp_path },
    );
    defer interp_chk_res.deinit(allocator);
    try std.testing.expectEqual(@as(u8, 0), interp_chk_res.exit_code);
}

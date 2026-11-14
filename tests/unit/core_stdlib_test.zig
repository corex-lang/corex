//! Unit & Differential Execution Tests for Stage-1 `core` (`tests/unit/core_stdlib_test.zig`)
//!
//! Verifies all Phase 7 Stage-1 minimal `core` library invariants (`DR-08`, `phase7_spec.md` §5.1):
//! - All 12 `core/**/*.cx` files satisfy 3-part `//!` headers, `< 150` column line limits,
//!   canonical 90-char / 65-char section dividers, and `formatSourceWithOptions` idempotency
//!   (`is_changed == false`, zero parse errors).
//! - Full multi-file `core` hierarchy resolves, typechecks, lowers to `HIR`/`MIR`, and passes
//!   4-pass `mir_sast` with zero errors and zero warnings.
//! - `@cache_aligned` `core::mem::CachePadded[u64]` resolves to `64B` alignment on `x86_64` and
//!   `128B` alignment on `aarch64-macos` (`D-10A`), cross-compiles to `.o` across `x86_64-linux`,
//!   `aarch64-macos`, and `wasm32-wasi` in both Tier A and Tier B, and passes the 4-tier
//!   `diff_oracle` (`MirVm --dev`, `MirVm --release`, Tier A C99, Tier B LLVM).

const std = @import("std");
const corex = @import("corex");

const FileId = corex.FileId;
const Durability = corex.Durability;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;
const CodegenBackend = corex.CodegenBackend;
const TypeLayoutResolver = corex.TypeLayoutResolver;

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical Stage-1 `core` source file paths in deterministic module order (`12` files).
const CORE_MODULE_PATHS = [_][]const u8{
    "core/root.cx",
    "core/primitives.cx",
    "core/mem.cx",
    "core/atomic.cx",
    "core/simd.cx",
    "core/panic.cx",
    "core/runtime.cx",
    "core/sys/mod.cx",
    "core/sys/linux.cx",
    "core/sys/macos.cx",
    "core/sys/windows.cx",
    "core/sys/wasi.cx",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Prints all diagnostics in `sink` to `stderr` when a `core` verification test fails.
fn dumpSinkOnFailure(label: []const u8, sink: *const DiagnosticSink) void {
    for (sink.diagnostics.items) |diag_item| {
        std.debug.print(
            "[{s}] {s}: {s}\n",
            .{ label, @tagName(diag_item.code), diag_item.message },
        );
    }
}

/// Normalizes CRLF line endings in `raw_bytes` to LF so formatter comparisons are OS-agnostic.
fn normalizeLfAlloc(allocator: std.mem.Allocator, raw_bytes: []const u8) ![]u8 {
    var out_buf = try std.ArrayList(u8).initCapacity(allocator, raw_bytes.len);
    errdefer out_buf.deinit(allocator);
    for (raw_bytes) |byte_val| {
        if (byte_val != '\r') {
            out_buf.appendAssumeCapacity(byte_val);
        }
    }
    return out_buf.toOwnedSlice(allocator);
}

/// Validates `< 150` column width, `//!` module header, and 90/65-char dividers in `cx_path`.
fn verifyCxStyleAndDividers(cx_path: []const u8, normalized_source: []const u8) !void {
    try std.testing.expect(std.mem.startsWith(u8, normalized_source, "//! "));

    var line_iter = std.mem.splitScalar(u8, normalized_source, '\n');
    var line_num: usize = 1;
    while (line_iter.next()) |line_text| : (line_num += 1) {
        if (line_text.len >= 150) {
            std.debug.print(
                "`{s}:{d}` exceeds 150-column limit ({d} bytes)\n",
                .{ cx_path, line_num, line_text.len },
            );
            return error.CxLineTooLong;
        }
        const trimmed = std.mem.trimStart(u8, line_text, " ");
        if (std.mem.startsWith(u8, trimmed, "// ---") and std.mem.endsWith(u8, trimmed, "---")) {
            try std.testing.expect(trimmed.len == 90 or trimmed.len == 65);
            const after_prefix = trimmed[3..];
            var left_dashes: usize = 0;
            while (left_dashes < after_prefix.len and
                after_prefix[left_dashes] == '-') : (left_dashes += 1)
            {}
            var right_dashes: usize = 0;
            while (right_dashes < after_prefix.len and
                after_prefix[after_prefix.len - 1 - right_dashes] == '-') : (right_dashes += 1)
            {}
            try std.testing.expect(left_dashes == right_dashes or left_dashes + 1 == right_dashes);
        }
    }
}

/// Loads all 12 `core/**/*.cx` files into `db` starting at `base_file_id` and binds `mod` edges.
fn loadCoreTreeIntoDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    db: *CompilerDb,
    base_file_id: u32,
) ![CORE_MODULE_PATHS.len]FileId {
    var file_ids: [CORE_MODULE_PATHS.len]FileId = undefined;
    for (CORE_MODULE_PATHS, 0..) |mod_path, i| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(
            io,
            mod_path,
            allocator,
            .limited(1024 * 1024),
        );
        defer allocator.free(raw_bytes);
        const norm_bytes = try normalizeLfAlloc(allocator, raw_bytes);
        defer allocator.free(norm_bytes);

        const fid = FileId.fromInt(base_file_id + @as(u32, @intCast(i)));
        file_ids[i] = fid;
        _ = try db.setInput(fid, norm_bytes, .high);
    }

    const core_root_fid = file_ids[0];
    try db.registerRootModule("core", core_root_fid);
    try db.bindExternalModule(core_root_fid, "primitives", file_ids[1]);
    try db.bindExternalModule(core_root_fid, "mem", file_ids[2]);
    try db.bindExternalModule(core_root_fid, "atomic", file_ids[3]);
    try db.bindExternalModule(core_root_fid, "simd", file_ids[4]);
    try db.bindExternalModule(core_root_fid, "panic", file_ids[5]);
    try db.bindExternalModule(core_root_fid, "runtime", file_ids[6]);
    try db.bindExternalModule(core_root_fid, "sys", file_ids[7]);

    const sys_mod_fid = file_ids[7];
    try db.bindExternalModule(sys_mod_fid, "linux", file_ids[8]);
    try db.bindExternalModule(sys_mod_fid, "macos", file_ids[9]);
    try db.bindExternalModule(sys_mod_fid, "windows", file_ids[10]);
    try db.bindExternalModule(sys_mod_fid, "wasi", file_ids[11]);

    return file_ids;
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_core_stdlib_all_12_files_canonical_format_headers_and_zero_diagnostics" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    for (CORE_MODULE_PATHS, 0..) |mod_path, i| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(
            io,
            mod_path,
            allocator,
            .limited(1024 * 1024),
        );
        defer allocator.free(raw_bytes);
        const norm_bytes = try normalizeLfAlloc(allocator, raw_bytes);
        defer allocator.free(norm_bytes);

        try verifyCxStyleAndDividers(mod_path, norm_bytes);

        var fmt_res = try corex.formatSourceWithOptions(
            allocator,
            norm_bytes,
            FileId.fromInt(@intCast(i)),
            .{},
        );
        defer fmt_res.deinit(allocator);

        try std.testing.expect(!fmt_res.has_syntax_errors);
        if (fmt_res.is_changed) {
            std.debug.print("`{s}` is not canonically formatted by `corex fmt`!\n", .{mod_path});
        }
        try std.testing.expect(!fmt_res.is_changed);
    }

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    const core_fids = try loadCoreTreeIntoDb(allocator, io, &db, 0);

    for (core_fids, 0..) |fid, i| {
        const mod_label = CORE_MODULE_PATHS[i];
        const parsed_art = try db.parseCst(fid);
        if (parsed_art.diagnostics.diagnostics.items.len > 0) {
            dumpSinkOnFailure(mod_label, &parsed_art.diagnostics);
        }
        try std.testing.expectEqual(@as(usize, 0), parsed_art.diagnostics.diagnostics.items.len);

        const sig_art = try db.resolveSignatures(fid);
        if (db.getSignatureDiagnostics(fid)) |sig_sink| {
            if (sig_sink.diagnostics.items.len > 0) dumpSinkOnFailure(mod_label, sig_sink);
            try std.testing.expectEqual(@as(usize, 0), sig_sink.diagnostics.items.len);
        }
        try std.testing.expectEqual(@as(u32, 0), sig_art.error_count);

        const item_entries = (try db.extractItemTree(fid)).entries;
        for (item_entries) |entry| {
            const body_art = try db.typecheckBody(entry.def_id);
            if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
                if (body_sink.diagnostics.items.len > 0) dumpSinkOnFailure(mod_label, body_sink);
                try std.testing.expectEqual(@as(usize, 0), body_sink.diagnostics.items.len);
            }
            try std.testing.expectEqual(@as(u32, 0), body_art.error_count);

            const sast_art = try db.verifySastMir(entry.def_id);
            if (db.getSastDiagnostics(entry.def_id)) |sast_sink| {
                if (sast_sink.diagnostics.items.len > 0) dumpSinkOnFailure(mod_label, sast_sink);
                try std.testing.expectEqual(@as(usize, 0), sast_sink.diagnostics.items.len);
            }
            try std.testing.expect(sast_art.is_verified_sound);
        }
    }
}

test "test_core_mem_cache_padded_target_dependent_64b_vs_128b_apple_silicon" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const mem_raw = try std.Io.Dir.cwd().readFileAlloc(
        io,
        "core/mem.cx",
        allocator,
        .limited(1024 * 1024),
    );
    defer allocator.free(mem_raw);
    const mem_norm = try normalizeLfAlloc(allocator, mem_raw);
    defer allocator.free(mem_norm);

    const probe_source = try std.fmt.allocPrint(
        allocator,
        "{s}\n" ++
            "pub fn probe_cache_slot(seed: u64) -> CachePadded[u64] {{\n" ++
            "    return cache_padded_new[u64](seed);\n" ++
            "}}\n",
        .{mem_norm},
    );
    defer allocator.free(probe_source);

    const target_cases = [_]struct {
        /// Target architecture/OS triple under test.
        spec: TargetSpec,
        /// Expected byte size and alignment of `CachePadded[u64]`.
        expected_cache_bytes: u64,
        /// Expected C99 alignment attribute substring.
        expected_c_attr: []const u8,
    }{
        .{
            .spec = TargetSpec.X86_64_LINUX,
            .expected_cache_bytes = 64,
            .expected_c_attr = "aligned(64)",
        },
        .{
            .spec = TargetSpec.X86_64_WINDOWS,
            .expected_cache_bytes = 64,
            .expected_c_attr = "aligned(64)",
        },
        .{
            .spec = TargetSpec.AARCH64_MACOS,
            .expected_cache_bytes = 128,
            .expected_c_attr = "aligned(128)",
        },
    };

    for (target_cases) |case_item| {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(case_item.spec);
        const fid = FileId.fromInt(0);
        _ = try db.setInput(fid, probe_source, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var c_art = try db.compileModuleArtifact(
            fid,
            .{
                .tier_a_c99 = .{
                    .target = case_item.spec,
                    .is_release_mode = true,
                    .has_line_directives = false,
                },
            },
            .{
                .artifact_kind = .source_text,
                .diagnostic_sink = &sink,
            },
        );
        defer c_art.deinit(allocator);
        try std.testing.expect(!sink.hasErrors());
        try std.testing.expect(
            std.mem.indexOf(u8, c_art.emitted_text, case_item.expected_c_attr) != null,
        );

        var layout_resolver = TypeLayoutResolver.init(
            allocator,
            &db.type_pool,
            &db.symbol_table,
            case_item.spec,
        );
        defer layout_resolver.deinit();

        const opt_mod = try db.optimizeMirModule(fid, true);
        const probe_body = opt_mod.findBodyByName(&db.interner, "probe_cache_slot").?;
        const resolved = try layout_resolver.resolveType(probe_body.ret_ty);
        try std.testing.expectEqual(case_item.expected_cache_bytes, resolved.size_bytes);
        try std.testing.expectEqual(
            @as(u32, @intCast(case_item.expected_cache_bytes)),
            resolved.alignBytes(),
        );
    }
}

test "test_core_stdlib_cross_target_tier_a_and_tier_b_compilation" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const harness_src =
        "//! Cross-Target Stage-1 `core` Smoke Consumer\n" ++
        "use core::primitives::clamp_i32;\n" ++
        "use core::mem::{align_up_usize, size_of_type};\n" ++
        "use core::atomic::{ORDER_SEQ_CST, atomic_u32_fetch_add, atomic_u32_new};\n" ++
        "use core::simd::{add_v4i32, reduce_add_v4i32, splat_v4i32};\n" ++
        "use core::runtime::poll_reload;\n" ++
        "\n" ++
        "pub fn exercise_core_cross_target(raw_input: i32) -> i32 {\n" ++
        "    poll_reload();\n" ++
        "    let clamped: i32 = clamp_i32(raw_input, -50, 50);\n" ++
        "    var counter = atomic_u32_new(10);\n" ++
        "    let prev_count: u32 = atomic_u32_fetch_add(counter, 5, ORDER_SEQ_CST);\n" ++
        "    let vec_sum = add_v4i32(splat_v4i32(clamped), splat_v4i32(3));\n" ++
        "    let aligned_sz: usize = align_up_usize(size_of_type[u64](), 16);\n" ++
        "    return reduce_add_v4i32(vec_sum) + (prev_count as i32) + (aligned_sz as i32);\n" ++
        "}\n";

    const cross_targets = [_]struct {
        /// Target architecture/OS triple compiled via `zig cc`.
        spec: TargetSpec,
        /// Scratch object file path inside `.zig-cache/`.
        out_base: []const u8,
    }{
        .{ .spec = TargetSpec.X86_64_LINUX, .out_base = ".zig-cache/core_x86_64_linux" },
        .{ .spec = TargetSpec.AARCH64_MACOS, .out_base = ".zig-cache/core_aarch64_macos" },
        .{ .spec = TargetSpec.WASM32_WASI, .out_base = ".zig-cache/core_wasm32_wasi" },
    };

    for (cross_targets) |target_case| {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(target_case.spec);
        _ = try loadCoreTreeIntoDb(allocator, io, &db, 1);

        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, harness_src, .low);

        const c_obj_path = try std.fmt.allocPrint(allocator, "{s}_c.o", .{target_case.out_base});
        defer allocator.free(c_obj_path);
        defer std.Io.Dir.cwd().deleteFile(io, c_obj_path) catch {};

        var c_sink = DiagnosticSink.init(allocator);
        defer c_sink.deinit();
        var c_art = try db.compileModuleArtifact(
            app_fid,
            .{
                .tier_a_c99 = .{
                    .target = target_case.spec,
                    .is_release_mode = true,
                    .has_line_directives = false,
                },
            },
            .{
                .artifact_kind = .object_file,
                .output_path = c_obj_path,
                .io = io,
                .diagnostic_sink = &c_sink,
            },
        );
        defer c_art.deinit(allocator);
        if (c_sink.hasErrors()) dumpSinkOnFailure("core_cross_c", &c_sink);
        try std.testing.expect(!c_sink.hasErrors());

        const ll_obj_path = try std.fmt.allocPrint(
            allocator,
            "{s}_llvm.o",
            .{target_case.out_base},
        );
        defer allocator.free(ll_obj_path);
        defer std.Io.Dir.cwd().deleteFile(io, ll_obj_path) catch {};

        var ll_sink = DiagnosticSink.init(allocator);
        defer ll_sink.deinit();
        var ll_art = try db.compileModuleArtifact(
            app_fid,
            .{
                .tier_b_llvm = .{
                    .target = target_case.spec,
                    .is_release_mode = true,
                },
            },
            .{
                .artifact_kind = .object_file,
                .output_path = ll_obj_path,
                .io = io,
                .diagnostic_sink = &ll_sink,
            },
        );
        defer ll_art.deinit(allocator);
        if (ll_sink.hasErrors()) dumpSinkOnFailure("core_cross_llvm", &ll_sink);
        try std.testing.expect(!ll_sink.hasErrors());
    }
}

test "test_core_stdlib_four_tier_differential_oracle_end_to_end" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const app_source =
        "//! End-to-End 4-Tier Differential `core` Verification Program\n" ++
        "use core::primitives::{abs_diff_u32, clamp_i32, max_i64, min_i32};\n" ++
        "use core::mem::{\n" ++
        "    align_of_type, align_up_usize, cache_padded_new,\n" ++
        "    is_power_of_two_usize, size_of_type, zeroed_value,\n" ++
        "};\n" ++
        "use core::atomic::{\n" ++
        "    MemoryOrder, ORDER_SEQ_CST, atomic_bool_new, atomic_bool_swap,\n" ++
        "    atomic_u32_compare_exchange, atomic_u32_fetch_add,\n" ++
        "    atomic_u32_load, atomic_u32_new, fence, order_to_code,\n" ++
        "};\n" ++
        "use core::simd::{\n" ++
        "    add_v16u8, add_v4i32, mul_v4i32, reduce_add_v16u8,\n" ++
        "    reduce_add_v4i32, splat_v16u8, splat_v4i32,\n" ++
        "};\n" ++
        "use core::panic::assert_true;\n" ++
        "use core::runtime::{has_pending_reload, poll_reload, record_drop_trace};\n" ++
        "use core::sys::{write_stderr, write_stdout};\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    poll_reload();\n" ++
        "    assert_true(!has_pending_reload(), \"stage0 reload flag must be false\");\n" ++
        "    assert_true(size_of_type[u32]() == 4, \"u32 size must be 4\");\n" ++
        "    assert_true(align_of_type[u64]() == 8, \"u64 align must be 8\");\n" ++
        "    assert_true(is_power_of_two_usize(align_of_type[u64]()), \"u64 align pow2\");\n" ++
        "\n" ++
        "    let clamped_val: i32 = clamp_i32(min_i32(99, 42), 0, 30);\n" ++
        "    let diff_val: u32 = abs_diff_u32(15, 40);\n" ++
        "    let max_wide: i64 = max_i64(zeroed_value[i64](), 7);\n" ++
        "    let padded_slot = cache_padded_new[i32](clamped_val);\n" ++
        "    let rounded_off: usize = align_up_usize(size_of_type[u32]() + 1, 8);\n" ++
        "\n" ++
        "    var flag_cell = atomic_bool_new(false);\n" ++
        "    let ord_mode: MemoryOrder = .SeqCst;\n" ++
        "    let was_set: bool = atomic_bool_swap(flag_cell, true, order_to_code(ord_mode));\n" ++
        "    assert_true(!was_set, \"initial atomic bool must be false\");\n" ++
        "\n" ++
        "    var counter_cell = atomic_u32_new(10);\n" ++
        "    let prev_u32: u32 = atomic_u32_fetch_add(counter_cell, diff_val, ORDER_SEQ_CST);\n" ++
        "    let (_, did_swap) = atomic_u32_compare_exchange(\n" ++
        "        counter_cell,\n" ++
        "        35,\n" ++
        "        40,\n" ++
        "        ORDER_SEQ_CST,\n" ++
        "        ORDER_SEQ_CST,\n" ++
        "    );\n" ++
        "    assert_true(did_swap, \"cmpxchg expected 35 -> 40\");\n" ++
        "    fence(ORDER_SEQ_CST);\n" ++
        "    let final_u32: u32 = atomic_u32_load(&counter_cell, ORDER_SEQ_CST);\n" ++
        "\n" ++
        "    let v4_sum = mul_v4i32(add_v4i32(splat_v4i32(2), splat_v4i32(3)), splat_v4i32(2));\n" ++
        "    let v16_sum = add_v16u8(splat_v16u8(1), splat_v16u8(2));\n" ++
        "\n" ++
        "    record_drop_trace(101);\n" ++
        "    record_drop_trace(202);\n" ++
        "    let _ = write_stdout(\"core-stdout-ok\\n\");\n" ++
        "    let _ = write_stderr(\"core-stderr-ok\\n\");\n" ++
        "\n" ++
        "    return padded_slot.value +\n" ++
        "        (prev_u32 as i32) +\n" ++
        "        (final_u32 as i32) +\n" ++
        "        reduce_add_v4i32(v4_sum) +\n" ++
        "        (reduce_add_v16u8(v16_sum) as i32) +\n" ++
        "        (rounded_off as i32) +\n" ++
        "        (max_wide as i32);\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    _ = try loadCoreTreeIntoDb(allocator, io, &db, 1);

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, app_source, .low);

    var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, app_fid, .{ .io = io });
    defer report.deinit(allocator);

    if (!report.is_all_matching) {
        std.debug.print("{s}\n", .{report.rendered_diff_table});
    }
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // 30 + 10 + 40 + 40 + 48 + 8 + 7 = 183
    try std.testing.expectEqual(@as(i64, 183), report.outcomes[0].return_scalar_i64);
    try std.testing.expectEqualStrings("core-stdout-ok\n", report.outcomes[0].stdout_bytes);
    try std.testing.expectEqualStrings("core-stderr-ok\n", report.outcomes[0].stderr_bytes);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 101, 202 }, report.outcomes[0].drop_trace);
}

test "test_regression_core_sys_externs_dedup_and_compile_to_object" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const posix_src =
        "//! Regression probe for `core::sys::{linux,macos}` `@link_name(\"write\"/\"_exit\")` dedup\n" ++
        "use core::sys::linux::{linux_posix_exit, linux_posix_write};\n" ++
        "use core::sys::macos::{darwin_exit, darwin_write};\n\n" ++
        "pub fn exercise_posix_externs(flag: i32) -> isize {\n" ++
        "    if flag == -777 {\n" ++
        "        unsafe { linux_posix_exit(1); }\n" ++
        "    }\n" ++
        "    if flag == -888 {\n" ++
        "        unsafe { darwin_exit(2); }\n" ++
        "    }\n" ++
        "    let wrote_a: isize = unsafe { linux_posix_write(1, 0 as *u8, 0) };\n" ++
        "    let wrote_b: isize = unsafe { darwin_write(1, 0 as *u8, 0) };\n" ++
        "    return wrote_a + wrote_b;\n" ++
        "}\n";

    const wasi_src =
        "//! Regression probe for `core::sys::wasi` `wasi_snapshot_preview1` imports\n" ++
        "use core::sys::wasi::{WasiCiovec, wasi_fd_write, wasi_proc_exit};\n\n" ++
        "pub fn exercise_wasi_externs(flag: i32) -> u16 {\n" ++
        "    if flag == -999 {\n" ++
        "        unsafe { wasi_proc_exit(1); }\n" ++
        "    }\n" ++
        "    var written: usize = 0;\n" ++
        "    let iov = WasiCiovec { buf_ptr: 0 as *u8, buf_len: 0 };\n" ++
        "    return unsafe { wasi_fd_write(1, &iov as *WasiCiovec, 1, &mut written as *mut usize) };\n" ++
        "}\n";

    const cases = [_]struct {
        /// Target architecture/OS triple under test.
        spec: TargetSpec,
        /// Source program referencing `core::sys` `extern "C"` declarations.
        src: []const u8,
        /// Temporary object file stem in `.zig-cache/`.
        stem: []const u8,
    }{
        .{ .spec = TargetSpec.X86_64_LINUX, .src = posix_src, .stem = ".zig-cache/core_sys_linux" },
        .{ .spec = TargetSpec.AARCH64_MACOS, .src = posix_src, .stem = ".zig-cache/core_sys_macos" },
        .{ .spec = TargetSpec.WASM32_WASI, .src = wasi_src, .stem = ".zig-cache/core_sys_wasi" },
    };

    for (cases) |tc| {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(tc.spec);
        _ = try loadCoreTreeIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, tc.src, .low);

        const c_obj = try std.fmt.allocPrint(allocator, "{s}_c.o", .{tc.stem});
        defer allocator.free(c_obj);
        defer std.Io.Dir.cwd().deleteFile(io, c_obj) catch {};

        var c_sink = DiagnosticSink.init(allocator);
        defer c_sink.deinit();
        var c_art = try db.compileModuleArtifact(
            app_fid,
            .{ .tier_a_c99 = .{ .target = tc.spec, .is_release_mode = true, .has_line_directives = false } },
            .{ .artifact_kind = .object_file, .output_path = c_obj, .io = io, .diagnostic_sink = &c_sink },
        );
        defer c_art.deinit(allocator);
        if (c_sink.hasErrors()) dumpSinkOnFailure("core_sys_c", &c_sink);
        try std.testing.expect(!c_sink.hasErrors());

        const ll_obj = try std.fmt.allocPrint(allocator, "{s}_ll.o", .{tc.stem});
        defer allocator.free(ll_obj);
        defer std.Io.Dir.cwd().deleteFile(io, ll_obj) catch {};

        var ll_sink = DiagnosticSink.init(allocator);
        defer ll_sink.deinit();
        var ll_art = try db.compileModuleArtifact(
            app_fid,
            .{ .tier_b_llvm = .{ .target = tc.spec, .is_release_mode = true } },
            .{ .artifact_kind = .object_file, .output_path = ll_obj, .io = io, .diagnostic_sink = &ll_sink },
        );
        defer ll_art.deinit(allocator);
        if (ll_sink.hasErrors()) dumpSinkOnFailure("core_sys_ll", &ll_sink);
        try std.testing.expect(!ll_sink.hasErrors());
    }
}

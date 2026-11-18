//! Unit & Differential Execution Tests for Stage-1 `core` (`tests/unit/core_stdlib_test.zig`)
//!
//! Verifies all Phase 7.6 (`DR-22`) & Phase 8 (`DR-08`, `DR-10`) Stage-1 `core` library invariants:
//! - All 14 `core/**/*.cx` files satisfy 3-part `//!` headers, `< 150` column line limits,
//!   canonical 90-char / 65-char section dividers, and `formatSourceWithOptions` idempotency
//!   (`is_changed == false`, zero parse errors).
//! - Full multi-file `core` hierarchy resolves, typechecks, lowers to `HIR`/`MIR`, and passes
//!   4-pass `mir_sast` (`@std_cap_boundary(clears: [unsafe_op])`) with zero errors and warnings.
//! - `core.mem.CachePadded[u64]`, `core.ffi.CStr` / C scalar aliases, and `core.async` (`Poll`,
//!   `CancelSource`, `yield_now`, `block_on`, `task_group`) cross-compile and pass 4-tier `diff_oracle`.

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

/// Canonical Stage-1 `core` source file paths in deterministic module order (`14` files).
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
    "core/ffi.cx",
    "core/async.cx",
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

/// Loads all 14 `core/**/*.cx` files into `db` starting at `base_file_id` and binds `mod` edges.
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
    try db.bindExternalModule(core_root_fid, "ffi", file_ids[12]);
    try db.bindExternalModule(core_root_fid, "async", file_ids[13]);

    const sys_mod_fid = file_ids[7];
    try db.bindExternalModule(sys_mod_fid, "linux", file_ids[8]);
    try db.bindExternalModule(sys_mod_fid, "macos", file_ids[9]);
    try db.bindExternalModule(sys_mod_fid, "windows", file_ids[10]);
    try db.bindExternalModule(sys_mod_fid, "wasi", file_ids[11]);

    return file_ids;
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_core_stdlib_all_14_files_canonical_format_headers_and_zero_diagnostics" {
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
    try db.setInternalCore(true);
    const core_fids = try loadCoreTreeIntoDb(allocator, io, &db, 0);

    var has_seen_atomic_inline_test = false;
    var total_diag_count: usize = 0;
    for (core_fids, 0..) |fid, i| {
        const mod_label = CORE_MODULE_PATHS[i];
        const parsed_art = try db.parseCst(fid);
        if (parsed_art.diagnostics.diagnostics.items.len > 0) {
            dumpSinkOnFailure(mod_label, &parsed_art.diagnostics);
            total_diag_count += parsed_art.diagnostics.diagnostics.items.len;
        }

        const sig_art = try db.resolveSignatures(fid);
        if (db.getSignatureDiagnostics(fid)) |sig_sink| {
            if (sig_sink.diagnostics.items.len > 0) {
                dumpSinkOnFailure(mod_label, sig_sink);
                total_diag_count += sig_sink.diagnostics.items.len;
            }
        }
        total_diag_count += sig_art.error_count;

        const entry_count = (try db.extractItemTree(fid)).entries.len;
        var entry_i: usize = 0;
        while (entry_i < entry_count) : (entry_i += 1) {
            const entry = (try db.extractItemTree(fid)).entries[entry_i];
            if (entry.kind == .test_decl) {
                has_seen_atomic_inline_test = true;
            }
            const body_art = try db.typecheckBody(entry.def_id);
            if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
                if (body_sink.diagnostics.items.len > 0) {
                    dumpSinkOnFailure(mod_label, body_sink);
                    total_diag_count += body_sink.diagnostics.items.len;
                }
            }
            total_diag_count += body_art.error_count;

            const sast_art = try db.verifySastMir(entry.def_id);
            if (db.getSastDiagnostics(entry.def_id)) |sast_sink| {
                if (sast_sink.diagnostics.items.len > 0) {
                    dumpSinkOnFailure(mod_label, sast_sink);
                    total_diag_count += sast_sink.diagnostics.items.len;
                }
            }
            if (!sast_art.is_verified_sound) total_diag_count += 1;
        }
    }
    try std.testing.expectEqual(@as(usize, 0), total_diag_count);
    try std.testing.expect(has_seen_atomic_inline_test);
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
        try db.setInternalCore(true);
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
        if (sink.hasErrors()) dumpSinkOnFailure("cache_padded_c99", &sink);
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
        "//! Cross-Target Stage-1 `core` Smoke Consumer (`DR-22`)\n" ++
        "use cx.primitives.clamp_i32;\n" ++
        "use cx.mem.{align_up, init_slot, size_of_type, swap};\n" ++
        "use cx.atomic.{AtomicU32, Ordering, fence};\n" ++
        "use cx.simd.{add_v4i32, reduce_add_v4i32, splat_v4i32};\n" ++
        "use cx.runtime.poll_reload;\n" ++
        "\n" ++
        "pub fn exercise_core_cross_target(raw_input: i32) -> i32 {\n" ++
        "    poll_reload();\n" ++
        "    let clamped: i32 = clamp_i32(raw_input, -50, 50);\n" ++
        "    let counter = AtomicU32.new(10);\n" ++
        "    let prev_count: u32 = counter.fetch_add(5);\n" ++
        "    fence(order: Ordering.Acquire);\n" ++
        "    var slot_left: i32 = 3;\n" ++
        "    var slot_right: i32;\n" ++
        "    init_slot(&out slot_right, clamped);\n" ++
        "    swap(&mut slot_left, &mut slot_right);\n" ++
        "    let vec_sum = add_v4i32(splat_v4i32(slot_left), splat_v4i32(slot_right));\n" ++
        "    let aligned_sz: usize = align_up(size_of_type[u64](), 16);\n" ++
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
        var ll_art = db.compileModuleArtifact(
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
        ) catch |err| {
            dumpSinkOnFailure("core_cross_llvm", &ll_sink);
            return err;
        };
        defer ll_art.deinit(allocator);
        if (ll_sink.hasErrors()) dumpSinkOnFailure("core_cross_llvm", &ll_sink);
        try std.testing.expect(!ll_sink.hasErrors());
    }
}

test "test_core_stdlib_four_tier_differential_oracle_end_to_end" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const app_source =
        "//! End-to-End 4-Tier Differential `core` Verification Program (`DR-22`)\n" ++
        "use cx.primitives.{abs_diff_u32, clamp_i32, max_i64, min_i32};\n" ++
        "use cx.mem.{\n" ++
        "    CachePadded, align_of_type, align_up, align_up_usize, cache_padded_new,\n" ++
        "    copy_nonoverlapping, init_slot, is_power_of_two_usize, read_volatile_u64,\n" ++
        "    size_of_type, swap, write_volatile_u64, zeroed_value,\n" ++
        "};\n" ++
        "use cx.atomic.{AtomicBool, AtomicU32, MemoryOrder, Ordering, fence};\n" ++
        "use cx.simd.{\n" ++
        "    add_v16u8, add_v4i32, mul_v4i32, reduce_add_v16u8,\n" ++
        "    reduce_add_v4i32, splat_v16u8, splat_v4i32,\n" ++
        "};\n" ++
        "use cx.panic.assert_true;\n" ++
        "use cx.runtime.{has_pending_reload, poll_reload, record_drop_trace};\n" ++
        "use cx.sys.{write_stderr, write_stdout};\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    poll_reload();\n" ++
        "    assert_true(not has_pending_reload(), \"stage0 reload flag must be false\");\n" ++
        "    assert_true(size_of_type[u32]() == 4, \"u32 size must be 4\");\n" ++
        "    assert_true(align_of_type[u64]() == 8, \"u64 align must be 8\");\n" ++
        "    assert_true(is_power_of_two_usize(align_of_type[u64]()), \"u64 align pow2\");\n" ++
        "\n" ++
        "    let clamped_val: i32 = clamp_i32(min_i32(99, 42), 0, 30);\n" ++
        "    let diff_val: u32 = abs_diff_u32(15, 40);\n" ++
        "    let max_wide: i64 = max_i64(zeroed_value[i64](), 7);\n" ++
        "    let padded_slot: CachePadded[i32] = cache_padded_new[i32](clamped_val);\n" ++
        "    let rounded_off: usize = align_up(size_of_type[u32]() + 1, 8);\n" ++
        "    assert_true(align_up_usize(5, 8) == rounded_off, \"align_up_usize alias parity\");\n" ++
        "\n" ++
        "    var out_slot: i32;\n" ++
        "    init_slot(&out out_slot, 12);\n" ++
        "    var partner_slot: i32 = 5;\n" ++
        "    swap(&mut out_slot, &mut partner_slot);\n" ++
        "    assert_true(out_slot == 5 and partner_slot == 12, \"swap + init_slot MVS check\");\n" ++
        "\n" ++
        "    let src_arr: [i32; 2] = [3, 4];\n" ++
        "    var dst_arr: [i32; 2] = [0, 0];\n" ++
        "    let copied_len: usize = copy_nonoverlapping[i32](&mut dst_arr, &src_arr) catch 0;\n" ++
        "    assert_true(copied_len == 2 and dst_arr[1] == 4, \"copy_nonoverlapping check\");\n" ++
        "\n" ++
        "    var mmio_reg: u64 = 0;\n" ++
        "    unsafe {\n" ++
        "        write_volatile_u64(&raw mut mmio_reg, 9_u64);\n" ++
        "    }\n" ++
        "    let mmio_read: u64 = unsafe { read_volatile_u64(&raw mmio_reg) };\n" ++
        "    assert_true(mmio_read == 9_u64, \"volatile raw pointer roundtrip\");\n" ++
        "\n" ++
        "    let flag_cell = AtomicBool.new(false);\n" ++
        "    let ord_mode: Ordering = MemoryOrder.SeqCst;\n" ++
        "    let was_set: bool = flag_cell.swap(true, order: ord_mode);\n" ++
        "    assert_true(not was_set and flag_cell.load(), \"initial atomic bool must swap false -> true\");\n" ++
        "\n" ++
        "    let counter = AtomicU32.new(10);\n" ++
        "    let prev_u32: u32 = counter.fetch_add(5);\n" ++
        "    let prev_u32_2: u32 = counter.fetch_add(diff_val - 5);\n" ++
        "    assert_true(prev_u32_2 == 15, \"second fetch_add observed 15\");\n" ++
        "    assert_true(counter.compare_exchange(35, 40) is .Ok(35), \"cmpxchg expected 35 -> 40\");\n" ++
        "    assert_true(counter.compare_exchange(35, 99) is .Err(40), \"cmpxchg mismatch observes 40\");\n" ++
        "    fence();\n" ++
        "    let final_u32: u32 = counter.load(order: .Acquire);\n" ++
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
        "        (max_wide as i32) +\n" ++
        "        partner_slot +\n" ++
        "        dst_arr[0] +\n" ++
        "        (mmio_read as i32);\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    _ = try loadCoreTreeIntoDb(allocator, io, &db, 1);

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, app_source, .low);

    const parsed_app = try db.parseCst(app_fid);
    if (parsed_app.diagnostics.diagnostics.items.len > 0) {
        dumpSinkOnFailure("app_parse", &parsed_app.diagnostics);
    }
    _ = try db.resolveSignatures(app_fid);
    if (db.getSignatureDiagnostics(app_fid)) |sig_sink| {
        if (sig_sink.diagnostics.items.len > 0) dumpSinkOnFailure("app_sig", sig_sink);
    }
    for ((try db.extractItemTree(app_fid)).entries) |entry| {
        _ = try db.typecheckBody(entry.def_id);
        if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
            if (body_sink.diagnostics.items.len > 0) dumpSinkOnFailure("app_body", body_sink);
        }
        _ = try db.verifySastMir(entry.def_id);
        if (db.getSastDiagnostics(entry.def_id)) |sast_sink| {
            if (sast_sink.diagnostics.items.len > 0) dumpSinkOnFailure("app_sast", sast_sink);
        }
    }

    var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, app_fid, .{ .io = io });
    defer report.deinit(allocator);

    if (!report.is_all_matching) {
        std.debug.print("{s}\n", .{report.rendered_diff_table});
    }
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // 30 + 10 + 40 + 40 + 48 + 8 + 7 + 12 + 3 + 9 = 207
    try std.testing.expectEqual(@as(i64, 207), report.outcomes[0].return_scalar_i64);
    try std.testing.expectEqualStrings("core-stdout-ok\n", report.outcomes[0].stdout_bytes);
    try std.testing.expectEqualStrings("core-stderr-ok\n", report.outcomes[0].stderr_bytes);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 101, 202 }, report.outcomes[0].drop_trace);
}

test "test_regression_core_sys_externs_dedup_and_compile_to_object" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const posix_src =
        "//! Regression probe for `core.sys.{linux,macos}` `@link_name(\"write\"/\"_exit\")` dedup\n" ++
        "use core.sys.linux.{linux_posix_exit, linux_posix_write};\n" ++
        "use core.sys.macos.{darwin_exit, darwin_write};\n\n" ++
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

    const win32_src =
        "//! Regression probe for `core.sys.windows` `*mut opaque` `HANDLE` / `LPOVERLAPPED` prototypes\n" ++
        "use core.sys.windows.{\n" ++
        "    STD_OUTPUT_HANDLE, win32_exit_process, win32_get_std_handle, win32_write_file,\n" ++
        "};\n\n" ++
        "pub fn exercise_win32_externs(flag: i32) -> i32 {\n" ++
        "    if flag == -666 {\n" ++
        "        unsafe { win32_exit_process(1); }\n" ++
        "    }\n" ++
        "    var written: u32 = 0;\n" ++
        "    let sample_byte: u8 = b'X';\n" ++
        "    let std_handle: *mut opaque = unsafe {\n" ++
        "        win32_get_std_handle(STD_OUTPUT_HANDLE as u32)\n" ++
        "    };\n" ++
        "    let null_overlapped: *mut opaque = 0 as *mut opaque;\n" ++
        "    return unsafe {\n" ++
        "        win32_write_file(std_handle, &raw sample_byte, 1, &raw mut written, null_overlapped)\n" ++
        "    };\n" ++
        "}\n";

    const wasi_src =
        "//! Regression probe for `core.sys.wasi` `wasi_snapshot_preview1` imports\n" ++
        "use core.sys.wasi.{WasiCiovec, wasi_fd_write, wasi_proc_exit};\n\n" ++
        "pub fn exercise_wasi_externs(flag: i32) -> u16 {\n" ++
        "    if flag == -999 {\n" ++
        "        unsafe { wasi_proc_exit(1); }\n" ++
        "    }\n" ++
        "    var written: usize = 0;\n" ++
        "    let iov = WasiCiovec { buf_ptr: 0 as *u8, buf_len: 0 };\n" ++
        "    return unsafe { wasi_fd_write(1, &raw iov, 1, &raw mut written) };\n" ++
        "}\n";

    const cases = [_]struct {
        /// Target architecture/OS triple under test.
        spec: TargetSpec,
        /// Source program referencing `core.sys` `extern "C"` declarations.
        src: []const u8,
        /// Temporary object file stem in `.zig-cache/`.
        stem: []const u8,
    }{
        .{ .spec = TargetSpec.X86_64_LINUX, .src = posix_src, .stem = ".zig-cache/core_sys_linux" },
        .{ .spec = TargetSpec.AARCH64_MACOS, .src = posix_src, .stem = ".zig-cache/core_sys_macos" },
        .{ .spec = TargetSpec.X86_64_WINDOWS, .src = win32_src, .stem = ".zig-cache/core_sys_windows" },
        .{ .spec = TargetSpec.WASM32_WASI, .src = wasi_src, .stem = ".zig-cache/core_sys_wasi" },
    };

    for (cases) |tc| {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(tc.spec);
        try db.setInternalCore(true);
        _ = try loadCoreTreeIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, tc.src, .low);

        const c_obj = try std.fmt.allocPrint(allocator, "{s}_c.o", .{tc.stem});
        defer allocator.free(c_obj);
        defer std.Io.Dir.cwd().deleteFile(io, c_obj) catch {};

        var c_sink = DiagnosticSink.init(allocator);
        defer c_sink.deinit();
        var c_art = db.compileModuleArtifact(
            app_fid,
            .{ .tier_a_c99 = .{ .target = tc.spec, .is_release_mode = true, .has_line_directives = false } },
            .{ .artifact_kind = .object_file, .output_path = c_obj, .io = io, .diagnostic_sink = &c_sink },
        ) catch |err| {
            dumpSinkOnFailure("core_sys_c", &c_sink);
            return err;
        };
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

test "test_core_direct_import_without_internal_core_emits_e0218" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const forbidden_src =
        "use core.mem.size_of_type;\n" ++
        "pub fn bad_user_import() -> usize {\n" ++
        "    return size_of_type[u32]();\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    _ = try loadCoreTreeIntoDb(allocator, io, &db, 1);

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, forbidden_src, .low);

    const sig_art = try db.resolveSignatures(app_fid);
    var has_e0218 = false;
    if (db.getSignatureDiagnostics(app_fid)) |sig_sink| {
        for (sig_sink.diagnostics.items) |diag_item| {
            if (diag_item.code == .e0218_direct_core_import_forbidden) has_e0218 = true;
        }
    }
    if (!has_e0218) {
        const items = (try db.extractItemTree(app_fid)).entries;
        for (items) |entry| {
            _ = try db.typecheckBody(entry.def_id);
            if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
                for (body_sink.diagnostics.items) |diag_item| {
                    if (diag_item.code == .e0218_direct_core_import_forbidden) has_e0218 = true;
                }
            }
        }
    }
    try std.testing.expect(sig_art.error_count > 0 or has_e0218);
    try std.testing.expect(has_e0218);

    // Enabling `--internal-core` (`db.setInternalCore(true)`) lifts `E0218` cleanly:
    try db.setInternalCore(true);
    const ok_sig = try db.resolveSignatures(app_fid);
    try std.testing.expectEqual(@as(u32, 0), ok_sig.error_count);
}

test "test_core_ffi_and_async_cross_target_layouts_and_object_emission" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const cross_probe_src =
        "//! Cross-Target `cx.ffi` + `cx.async` Layout & Object Compilation Probe\n" ++
        "use cx.ffi.{CStr, VaList, c_char, c_long};\n" ++
        "use cx.async.{CancelSource, Poll, TaskHeader};\n\n" ++
        "pub fn probe_c_long(val: c_long) -> c_long = val;\n" ++
        "pub fn probe_c_char(ch: c_char) -> c_char = ch;\n" ++
        "pub fn probe_va_list(va_in: VaList) -> VaList = va_in;\n" ++
        "pub fn probe_cstr_and_async() -> usize {\n" ++
        "    let poll_item: Poll[i32] = .Ready(7);\n" ++
        "    var cancel_src = CancelSource.new();\n" ++
        "    let cancel_tok = cancel_src.as_token();\n" ++
        "    cancel_src.cancel();\n" ++
        "    let hdr = TaskHeader.empty();\n" ++
        "    let nul_bytes: [u8; 4] = [b'o', b'k', b'!', 0_u8];\n" ++
        "    let cstr_len: usize = match CStr.from_bytes_with_nul(&nul_bytes) {\n" ++
        "        .Some(valid_cstr) => valid_cstr.count_bytes(),\n" ++
        "        .None => 0,\n" ++
        "    };\n" ++
        "    if poll_item.is_ready() and cancel_tok.is_cancelled() {\n" ++
        "        return cstr_len + hdr.poll_fn;\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";

    const target_cases = [_]struct {
        /// Target architecture/OS/ABI triple under test.
        spec: TargetSpec,
        /// Expected byte width of `c_long`.
        expected_c_long_bytes: u64,
        /// Expected byte width of `VaList` struct storage.
        expected_va_bytes: u64,
        /// Scratch object file prefix inside `.zig-cache/`.
        stem: []const u8,
    }{
        .{
            .spec = TargetSpec.X86_64_LINUX_GNU,
            .expected_c_long_bytes = 8,
            .expected_va_bytes = 24,
            .stem = ".zig-cache/core_p8_x64_linux",
        },
        .{
            .spec = TargetSpec.AARCH64_LINUX_GNU,
            .expected_c_long_bytes = 8,
            .expected_va_bytes = 32,
            .stem = ".zig-cache/core_p8_arm64_linux",
        },
        .{
            .spec = TargetSpec.AARCH64_APPLE_DARWIN,
            .expected_c_long_bytes = 8,
            .expected_va_bytes = 8,
            .stem = ".zig-cache/core_p8_arm64_macos",
        },
        .{
            .spec = TargetSpec.X86_64_WINDOWS_MSVC,
            .expected_c_long_bytes = 4,
            .expected_va_bytes = 8,
            .stem = ".zig-cache/core_p8_x64_win",
        },
        .{
            .spec = TargetSpec.WASM32_UNKNOWN_WASI,
            .expected_c_long_bytes = 4,
            .expected_va_bytes = 4,
            .stem = ".zig-cache/core_p8_wasm32_wasi",
        },
    };

    for (target_cases) |target_case| {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(target_case.spec);
        _ = try loadCoreTreeIntoDb(allocator, io, &db, 1);

        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, cross_probe_src, .low);

        const opt_mod = try db.optimizeMirModule(app_fid, true);
        var resolver = TypeLayoutResolver.init(
            allocator,
            &db.type_pool,
            &db.symbol_table,
            target_case.spec,
        );
        defer resolver.deinit();

        const long_body = opt_mod.findBodyByName(&db.interner, "probe_c_long").?;
        const va_body = opt_mod.findBodyByName(&db.interner, "probe_va_list").?;
        try std.testing.expectEqual(
            target_case.expected_c_long_bytes,
            (try resolver.resolveType(long_body.ret_ty)).size_bytes,
        );
        try std.testing.expectEqual(
            target_case.expected_va_bytes,
            (try resolver.resolveType(va_body.ret_ty)).size_bytes,
        );

        const c_obj = try std.fmt.allocPrint(allocator, "{s}_c.o", .{target_case.stem});
        defer allocator.free(c_obj);
        defer std.Io.Dir.cwd().deleteFile(io, c_obj) catch {};

        var c_sink = DiagnosticSink.init(allocator);
        defer c_sink.deinit();
        var c_art = db.compileModuleArtifact(
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
                .output_path = c_obj,
                .io = io,
                .diagnostic_sink = &c_sink,
            },
        ) catch |err| {
            dumpSinkOnFailure("core_p8_c", &c_sink);
            return err;
        };
        defer c_art.deinit(allocator);
        if (c_sink.hasErrors()) dumpSinkOnFailure("core_p8_c", &c_sink);
        try std.testing.expect(!c_sink.hasErrors());

        const ll_obj = try std.fmt.allocPrint(allocator, "{s}_ll.o", .{target_case.stem});
        defer allocator.free(ll_obj);
        defer std.Io.Dir.cwd().deleteFile(io, ll_obj) catch {};

        var ll_sink = DiagnosticSink.init(allocator);
        defer ll_sink.deinit();
        var ll_art = try db.compileModuleArtifact(
            app_fid,
            .{ .tier_b_llvm = .{ .target = target_case.spec, .is_release_mode = true } },
            .{
                .artifact_kind = .object_file,
                .output_path = ll_obj,
                .io = io,
                .diagnostic_sink = &ll_sink,
            },
        );
        defer ll_art.deinit(allocator);
        if (ll_sink.hasErrors()) dumpSinkOnFailure("core_p8_ll", &ll_sink);
        try std.testing.expect(!ll_sink.hasErrors());
    }
}

test "test_core_ffi_cstr_and_async_nursery_four_tier_differential_oracle" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const app_source =
        "//! End-to-End 4-Tier Differential `cx.ffi` + `cx.async` Verification Program\n" ++
        "use cx.ffi.CStr;\n" ++
        "use cx.async.{CancelSource, Poll, Waker, block_on, task_group, yield_now};\n" ++
        "use cx.panic.assert_true;\n" ++
        "use cx.runtime.record_drop_trace;\n\n" ++
        "pub async fn async_compute_pipeline(base_len: i32) -> i32 {\n" ++
        "    yield_now().await;\n" ++
        "    let group_total: i32 = task_group(|grp| {\n" ++
        "        let first_h = grp.spawn(own async {\n" ++
        "            record_drop_trace(501);\n" ++
        "            yield_now().await;\n" ++
        "            record_drop_trace(503);\n" ++
        "            10\n" ++
        "        });\n" ++
        "        let second_h = grp.spawn_local(own async {\n" ++
        "            record_drop_trace(502);\n" ++
        "            yield_now().await;\n" ++
        "            record_drop_trace(504);\n" ++
        "            25\n" ++
        "        });\n" ++
        "        let first_join = first_h.join();\n" ++
        "        let second_join = second_h.join();\n" ++
        "        first_join.await + second_join.await\n" ++
        "    }).await;\n" ++
        "    return base_len + group_total;\n" ++
        "}\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    let valid_bytes: [u8; 6] = [b'c', b'o', b'r', b'e', b'x', 0_u8];\n" ++
        "    let empty_bytes: [u8; 1] = [0_u8];\n" ++
        "    let bad_interior_nul: [u8; 3] = [b'a', 0_u8, 0_u8];\n" ++
        "    let bad_missing_nul: [u8; 2] = [b'x', b'y'];\n" ++
        "    let parsed_cstr = CStr.from_bytes_with_nul(&valid_bytes);\n" ++
        "    let empty_cstr = CStr.from_bytes_with_nul(&empty_bytes);\n" ++
        "    assert_true(CStr.from_bytes_with_nul(&bad_interior_nul) is .None, \"interior nul\");\n" ++
        "    assert_true(CStr.from_bytes_with_nul(&bad_missing_nul) is .None, \"missing nul\");\n" ++
        "    let cstr_len: i32 = match parsed_cstr {\n" ++
        "        .Some(cs_val) => if not cs_val.is_empty() { cs_val.count_bytes() as i32 } else { -1 },\n" ++
        "        .None => -2,\n" ++
        "    };\n" ++
        "    let empty_ok: i32 = match empty_cstr {\n" ++
        "        .Some(emp_val) => if emp_val.is_empty() and emp_val.count_bytes() == 0 { 2 } else { 0 },\n" ++
        "        .None => 0,\n" ++
        "    };\n" ++
        "    let ready_poll: Poll[i32] = .Ready(4);\n" ++
        "    let pending_poll: Poll[i32] = .Pending;\n" ++
        "    assert_true(ready_poll.is_ready() and not ready_poll.is_pending(), \"poll ready\");\n" ++
        "    assert_true(pending_poll.is_pending() and not pending_poll.is_ready(), \"poll pending\");\n" ++
        "    let noop_waker = Waker.noop();\n" ++
        "    assert_true(noop_waker.is_noop(), \"noop waker\");\n" ++
        "    noop_waker.wake();\n" ++
        "    var cancel_src = CancelSource.new();\n" ++
        "    let tok_view = cancel_src.as_token();\n" ++
        "    assert_true(not cancel_src.is_cancelled() and not tok_view.is_cancelled(), \"init active\");\n" ++
        "    cancel_src.cancel();\n" ++
        "    assert_true(cancel_src.is_cancelled() and tok_view.is_cancelled(), \"cancelled view\");\n" ++
        "    return block_on(own async_compute_pipeline(cstr_len + empty_ok));\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    _ = try loadCoreTreeIntoDb(allocator, io, &db, 1);

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, app_source, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    var report = corex.runFourTierDiffOracleOnDb(
        allocator,
        &db,
        app_fid,
        .{ .io = io, .diagnostic_sink = &sink },
    ) catch |err| {
        dumpSinkOnFailure("core_p8_oracle", &sink);
        return err;
    };
    defer report.deinit(allocator);

    if (!report.is_all_matching) {
        std.debug.print("{s}\n", .{report.rendered_diff_table});
    }
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // 5 + 2 + 10 + 25 = 42
    try std.testing.expectEqual(@as(i64, 42), report.outcomes[0].return_scalar_i64);
    try std.testing.expectEqualSlices(
        i64,
        &[_]i64{ 501, 502, 503, 504 },
        report.outcomes[0].drop_trace,
    );
}

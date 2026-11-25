//! Phase 11.1 (`STD-01` Step 2) Standard Library & Stage-0 Seam Verification Suite
//!
//! Verifies all Phase 11.1 (`STD-01` Step 2) compiler seams and `stdlib/cx/` invariants:
//! - All 5 `stdlib/cx/{mod,mem,math,col,str}.cx` files satisfy `< 150` column limits, canonical
//!   90-char / 65-char centered dividers, `corex fmt` idempotency, zero blanket `@allow` suppressors,
//!   canonical `pub fn expm1`, and zero errors/warnings under `mir_sast` on host and `wasm32-wasi`.
//! - Fat-slice reference representation (`&[T]` / `&mut [T]` == `16 B` on 64-bit, `8 B` on `wasm32`,
//!   `&[T]? == 16 B` / `8 B` via `.zero_ptr` niche, while `& &[T]` and `&str` remain thin pointers).
//! - Demand-driven `.std_core` body compilation (`collectActiveModuleDefIds`) and negative safety
//!   checks (`E0406` on `cx.math.ilog2(0_u32)`, `E0328` on `cx.mem.with_scratch` escaping `str`).
//! - Full 4-tier (`MirVm` `--dev`/`--release`, ISO C99, LLVM) differential parity across `Vec`,
//!   `SmallVec`, `Deque`, `SlotMap`, `Map`, `Set`, `String`, `str.graphemes()`, `Arena`,
//!   `with_scratch`, `format_int`, `format_float`, `parse_float`, and `cx.math` without
//!   `--internal-core`.

const std = @import("std");
const corex = @import("corex");

const FileId = corex.FileId;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const DiagnosticCode = corex.DiagnosticCode;
const TargetSpec = corex.TargetSpec;
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

/// Canonical Phase 11.1 (`STD-01` Step 2) `stdlib/cx/` source file paths (`5` files).
const CX_STDLIB_PATHS = [_][]const u8{
    "stdlib/cx/mod.cx",
    "stdlib/cx/mem.cx",
    "stdlib/cx/math.cx",
    "stdlib/cx/col.cx",
    "stdlib/cx/str.cx",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `sink` contains at least one diagnostic matching `code`.
fn sinkHasCode(sink: *const DiagnosticSink, code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == code) return true;
    }
    return false;
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

/// Validates `< 150` column width, `/#` module header, and 90/65-char dividers in `cx_path`.
fn verifyCxStyleAndDividers(cx_path: []const u8, normalized_source: []const u8) !void {
    try std.testing.expect(std.mem.startsWith(u8, normalized_source, "/# "));

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

/// Mounts all `core/**/*.cx` and `stdlib/cx/*.cx` files into `db` as `.std_core` and returns the 5 `cx` `FileId`s.
fn mountStdCoreAndCxIntoDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    db: *CompilerDb,
    base_file_id: u32,
) ![CX_STDLIB_PATHS.len]FileId {
    var core_fids: [CORE_MODULE_PATHS.len]FileId = undefined;
    for (CORE_MODULE_PATHS, 0..) |mod_path, i| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(
            io,
            mod_path,
            allocator,
            .limited(2 * 1024 * 1024),
        );
        defer allocator.free(raw_bytes);
        const norm_bytes = try normalizeLfAlloc(allocator, raw_bytes);
        defer allocator.free(norm_bytes);

        const fid = FileId.fromInt(base_file_id + @as(u32, @intCast(i)));
        core_fids[i] = fid;
        try db.setFilePackageId(fid, .std_core);
        try db.setFilePath(fid, mod_path);
        _ = try db.setInput(fid, norm_bytes, .high);
    }

    const core_root_fid = core_fids[0];
    try db.registerRootModule("core", core_root_fid);
    try db.bindExternalModule(core_root_fid, "primitives", core_fids[1]);
    try db.bindExternalModule(core_root_fid, "mem", core_fids[2]);
    try db.bindExternalModule(core_root_fid, "atomic", core_fids[3]);
    try db.bindExternalModule(core_root_fid, "simd", core_fids[4]);
    try db.bindExternalModule(core_root_fid, "panic", core_fids[5]);
    try db.bindExternalModule(core_root_fid, "runtime", core_fids[6]);
    try db.bindExternalModule(core_root_fid, "sys", core_fids[7]);
    try db.bindExternalModule(core_root_fid, "ffi", core_fids[12]);
    try db.bindExternalModule(core_root_fid, "async", core_fids[13]);

    const sys_mod_fid = core_fids[7];
    try db.bindExternalModule(sys_mod_fid, "linux", core_fids[8]);
    try db.bindExternalModule(sys_mod_fid, "macos", core_fids[9]);
    try db.bindExternalModule(sys_mod_fid, "windows", core_fids[10]);
    try db.bindExternalModule(sys_mod_fid, "wasi", core_fids[11]);

    const cx_base = base_file_id + @as(u32, CORE_MODULE_PATHS.len);
    var cx_fids: [CX_STDLIB_PATHS.len]FileId = undefined;
    for (CX_STDLIB_PATHS, 0..) |cx_path, i| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(
            io,
            cx_path,
            allocator,
            .limited(2 * 1024 * 1024),
        );
        defer allocator.free(raw_bytes);
        const norm_bytes = try normalizeLfAlloc(allocator, raw_bytes);
        defer allocator.free(norm_bytes);

        const fid = FileId.fromInt(cx_base + @as(u32, @intCast(i)));
        cx_fids[i] = fid;
        try db.setFilePackageId(fid, .std_core);
        try db.setFilePath(fid, cx_path);
        _ = try db.setInput(fid, norm_bytes, .high);
    }

    const cx_mod_fid = cx_fids[0];
    try db.registerRootModule("cx", cx_mod_fid);
    try db.registerCxStdlibPreludeRoot(cx_mod_fid);
    try db.bindExternalModule(cx_mod_fid, "mem", cx_fids[1]);
    try db.bindExternalModule(cx_mod_fid, "math", cx_fids[2]);
    try db.bindExternalModule(cx_mod_fid, "col", cx_fids[3]);
    try db.bindExternalModule(cx_mod_fid, "str", cx_fids[4]);

    return cx_fids;
}

/// Collects all frontend, body, and SAST diagnostics for `fid` into `out_sink`.
fn collectAllDiagnostics(db: *CompilerDb, fid: FileId, out_sink: *DiagnosticSink) !void {
    const parsed = try db.parseCst(fid);
    for (parsed.diagnostics.diagnostics.items) |diag_item| _ = try out_sink.emit(diag_item);
    _ = try db.resolveSignatures(fid);
    if (db.getSignatureDiagnostics(fid)) |sig_sink| {
        for (sig_sink.diagnostics.items) |diag_item| _ = try out_sink.emit(diag_item);
    }
    for ((try db.extractItemTree(fid)).entries) |entry| {
        _ = try db.typecheckBody(entry.def_id);
        if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
            for (body_sink.diagnostics.items) |diag_item| _ = try out_sink.emit(diag_item);
        }
        _ = try db.verifySastMir(entry.def_id);
        if (db.getSastDiagnostics(entry.def_id)) |sast_sink| {
            for (sast_sink.diagnostics.items) |diag_item| _ = try out_sink.emit(diag_item);
        }
    }
}

/// Prints diagnostics in `sink` to `stderr` on unexpected failure.
fn dumpUnexpectedDiagnostics(label: []const u8, sink: *const DiagnosticSink) void {
    for (sink.diagnostics.items) |diag_item| {
        const first_lbl = if (diag_item.labels.len > 0) diag_item.labels[0].label else "";
        std.debug.print(
            "[{s}] fid={d} {d}..{d} {s}: {s} ({s})\n",
            .{
                label,
                diag_item.primary_span.file_id.asInt(),
                diag_item.primary_span.start_byte,
                diag_item.primary_span.end_byte,
                @tagName(diag_item.code),
                diag_item.message,
                first_lbl,
            },
        );
    }
}

// ---------------------------------------- TESTS ----------------------------------------

test "test_step2_stdlib_cx_files_format_style_and_sast_strict_clean" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    for (CX_STDLIB_PATHS, 0..) |cx_path, i| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(
            io,
            cx_path,
            allocator,
            .limited(2 * 1024 * 1024),
        );
        defer allocator.free(raw_bytes);
        const norm_bytes = try normalizeLfAlloc(allocator, raw_bytes);
        defer allocator.free(norm_bytes);

        try verifyCxStyleAndDividers(cx_path, norm_bytes);
        if (std.mem.endsWith(u8, cx_path, "math.cx")) {
            try std.testing.expect(std.mem.indexOf(u8, norm_bytes, "pub fn expm1") != null);
            try std.testing.expect(std.mem.indexOf(u8, norm_bytes, "exp_m1") == null);
            try std.testing.expect(std.mem.indexOf(u8, norm_bytes, "@allow(W0314)") == null);
        } else {
            try std.testing.expect(std.mem.indexOf(u8, norm_bytes, "@allow(") == null);
        }

        var fmt_res = try corex.formatSourceWithOptions(
            allocator,
            norm_bytes,
            FileId.fromInt(@intCast(i)),
            .{},
        );
        defer fmt_res.deinit(allocator);
        try std.testing.expect(!fmt_res.has_syntax_errors);
        try std.testing.expect(!fmt_res.is_changed);
    }

    const targets = [_]TargetSpec{
        TargetSpec.host(),
        TargetSpec.WASM32_WASI,
    };
    for (targets) |target_spec| {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(target_spec);
        const cx_fids = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        for (cx_fids) |cx_fid| {
            try collectAllDiagnostics(&db, cx_fid, &sink);
        }
        if (sink.diagnostics.items.len > 0) {
            dumpUnexpectedDiagnostics("step2_stdlib_cx_sast", &sink);
        }
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);
    }
}

test "test_step2_slice_ref_fat_layout_demand_driven_std_core_and_negative_safety" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Fat-slice `&[u8]` / `&[u8]?` (`16 B` / `8 B`) vs thin `& &[u8]` / `&str` (`8 B` / `4 B`):
    {
        const layout_src =
            "pub fn probe_slice_ref(val: &[u8]) -> &[u8] { return val; }\n" ++
            "pub fn probe_opt_slice_ref() -> &[u8]? { return .None; }\n" ++
            "pub fn probe_nested_ref(val: & &[u8]) -> & &[u8] { return val; }\n" ++
            "pub fn probe_str_ref(val: &str) -> &str { return val; }\n";
        const targets = [_]struct { spec: TargetSpec, ptr_bytes: u64 }{
            .{ .spec = TargetSpec.X86_64_LINUX, .ptr_bytes = 8 },
            .{ .spec = TargetSpec.WASM32_WASI, .ptr_bytes = 4 },
        };
        for (targets) |target_case| {
            var db = try CompilerDb.init(allocator);
            defer db.deinit();
            db.setTargetSpec(target_case.spec);
            const fid = FileId.fromInt(0);
            _ = try db.setInput(fid, layout_src, .low);

            var sink = DiagnosticSink.init(allocator);
            defer sink.deinit();
            try collectAllDiagnostics(&db, fid, &sink);
            try std.testing.expect(!sink.hasErrors());

            var resolver = TypeLayoutResolver.init(allocator, &db.type_pool, &db.symbol_table, target_case.spec);
            defer resolver.deinit();

            const opt_mod = try db.optimizeMirModule(fid, false);
            const ty0 = opt_mod.findBodyByName(&db.interner, "probe_slice_ref").?.ret_ty;
            const ty1 = opt_mod.findBodyByName(&db.interner, "probe_opt_slice_ref").?.ret_ty;
            const ty2 = opt_mod.findBodyByName(&db.interner, "probe_nested_ref").?.ret_ty;
            const ty3 = opt_mod.findBodyByName(&db.interner, "probe_str_ref").?.ret_ty;

            try std.testing.expect(db.type_pool.isSliceRefType(ty0));
            try std.testing.expect(!db.type_pool.isSliceRefType(ty2));
            try std.testing.expect(!db.type_pool.isSliceRefType(ty3));
            try std.testing.expectEqual(2 * target_case.ptr_bytes, (try resolver.resolveType(ty0)).size_bytes);
            try std.testing.expectEqual(2 * target_case.ptr_bytes, (try resolver.resolveType(ty1)).size_bytes);
            try std.testing.expectEqual(target_case.ptr_bytes, (try resolver.resolveType(ty2)).size_bytes);
            try std.testing.expectEqual(target_case.ptr_bytes, (try resolver.resolveType(ty3)).size_bytes);
        }
    }

    // [2] Demand-driven `.std_core` `DefId` worklist (`1H`):
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        const cx_fids = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

        const tiny_src =
            "pub fn main() -> i32 {\n" ++
            "    var vals = Vec[u32].new();\n" ++
            "    vals.push(9_u32);\n" ++
            "    return vals[0] as i32;\n" ++
            "}\n";
        const root_fid = FileId.fromInt(0);
        _ = try db.setInput(root_fid, tiny_src, .low);

        var reachable_files: std.ArrayListUnmanaged(FileId) = .empty;
        defer reachable_files.deinit(allocator);
        try db.collectReachableModuleFiles(root_fid, &.{}, &reachable_files);

        var total_std_defs: usize = 0;
        for (cx_fids) |cx_fid| {
            total_std_defs += (try db.extractItemTree(cx_fid)).entries.len;
        }
        for (reachable_files.items) |mod_fid| {
            _ = try db.parseCst(mod_fid);
            _ = try db.resolveSignatures(mod_fid);
        }

        var active_defs: std.ArrayListUnmanaged(corex.query_db.DefId) = .empty;
        defer active_defs.deinit(allocator);
        try db.collectActiveModuleDefIds(allocator, &.{root_fid}, reachable_files.items, &active_defs);

        try std.testing.expect(total_std_defs > 300);
        try std.testing.expect(active_defs.items.len > 0);
        try std.testing.expect(active_defs.items.len < 90);
    }

    // [3] Negative refinement (`E0406`) and scratch-escape (`E0328`) checks without `--internal-core`:
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

        const bad_ilog2_src =
            "use cx.math;\n" ++
            "pub fn bad_zero_log() -> u32 {\n" ++
            "    return math.ilog2(0_u32);\n" ++
            "}\n";
        const fid_ilog2 = FileId.fromInt(0);
        _ = try db.setInput(fid_ilog2, bad_ilog2_src, .low);
        var sink_ilog2 = DiagnosticSink.init(allocator);
        defer sink_ilog2.deinit();
        try collectAllDiagnostics(&db, fid_ilog2, &sink_ilog2);
        try std.testing.expect(sinkHasCode(&sink_ilog2, .e0406_range_refinement_violation));

        const bad_scratch_src =
            "use cx.mem.{Arena, with_scratch};\n" ++
            "pub fn bad_escape() -> str {\n" ++
            "    return with_scratch(|scratch: &mut Arena| -> str {\n" ++
            "        return scratch.dupe_str(\"dangling\");\n" ++
            "    });\n" ++
            "}\n";
        const fid_scratch = FileId.fromInt(1);
        _ = try db.setInput(fid_scratch, bad_scratch_src, .low);
        var sink_scratch = DiagnosticSink.init(allocator);
        defer sink_scratch.deinit();
        try collectAllDiagnostics(&db, fid_scratch, &sink_scratch);
        try std.testing.expect(sinkHasCode(&sink_scratch, .e0328_scratch_arena_ping_pong_conflict));
    }
}

test "test_step2_stdlib_cx_four_tier_differential_parity" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    try std.testing.expect(!db.is_internal_core);
    _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

    const smoke_app_src =
        "use cx.col.{Deque, SlotKey, SlotMap, SmallVec};\n" ++
        "use cx.math;\n" ++
        "use cx.mem.{Arena, with_scratch};\n" ++
        "use cx.str.{format_float, format_int, parse_float};\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    var nums = Vec[u32].new();\n" ++
        "    nums.push(40_u32);\n" ++
        "    nums.push(10_u32);\n" ++
        "    nums.push(30_u32);\n" ++
        "    nums[2] = 25_u32;\n" ++
        "    if nums.len() != 3 or nums[0] != 40_u32 or nums[2] != 25_u32 { return 1; }\n" ++
        "\n" ++
        "    var small = SmallVec[u32, 4].new();\n" ++
        "    var idx = 0_u32;\n" ++
        "    while idx < 6_u32 {\n" ++
        "        small.push(idx * 10_u32);\n" ++
        "        idx += 1_u32;\n" ++
        "    }\n" ++
        "    if small.len() != 6 or small[5] != 50_u32 { return 2; }\n" ++
        "\n" ++
        "    var ring = Deque[i32].new();\n" ++
        "    ring.push_back(20);\n" ++
        "    ring.push_front(10);\n" ++
        "    ring.push_back(30);\n" ++
        "    if ring.pop_front() != .Some(10) or ring.pop_back() != .Some(30) { return 3; }\n" ++
        "\n" ++
        "    var slots = SlotMap[SlotKey[u64], u64].new();\n" ++
        "    let key_a: SlotKey[u64] = slots.insert(777_u64);\n" ++
        "    if slots.remove(key_a) != .Some(777_u64) or slots.get(key_a) != .None { return 4; }\n" ++
        "\n" ++
        "    var table = Map[str, i32].new();\n" ++
        "    _ = table.insert(\"alpha\", 11);\n" ++
        "    _ = table.insert(\"beta\", 22);\n" ++
        "    if table.get(&\"beta\") is .Some(beta_ref) {\n" ++
        "        if beta_ref.* != 22 { return 5; }\n" ++
        "    } else {\n" ++
        "        return 5;\n" ++
        "    }\n" ++
        "\n" ++
        "    var seen = Set[u32].new();\n" ++
        "    _ = seen.insert(7_u32);\n" ++
        "    _ = seen.insert(7_u32);\n" ++
        "    if seen.len() != 1 or not seen.contains(&7_u32) { return 6; }\n" ++
        "\n" ++
        "    var text = String.from_str(\"hello\");\n" ++
        "    text.push_str(\", corex stdlib world!!!\");\n" ++
        "    if text.len() != 28 or not text.as_str().starts_with(\"hello, corex\") { return 7; }\n" ++
        "    var g_iter = \"a\\u{0301}b\\r\\nc\".graphemes();\n" ++
        "    var g_count: usize = 0;\n" ++
        "    while g_iter.next() is .Some(_) { g_count += 1; }\n" ++
        "    if g_count != 4 { return 8; }\n" ++
        "\n" ++
        "    var arena = Arena.new();\n" ++
        "    let duped: str = arena.dupe_str(\"arena-backed\");\n" ++
        "    if duped != \"arena-backed\" { own arena.release(); return 9; }\n" ++
        "    own arena.release();\n" ++
        "    let scratch_len: usize = with_scratch(|scratch: &mut Arena| -> usize {\n" ++
        "        scratch.dupe_str(\"ping-pong\").len()\n" ++
        "    });\n" ++
        "    if scratch_len != 9 { return 10; }\n" ++
        "\n" ++
        "    var num_buf: [u8; 64] = [0_u8; 64];\n" ++
        "    let int_txt: str = format_int(&mut num_buf, -12345_i32) catch { return 11; };\n" ++
        "    if int_txt != \"-12345\" { return 12; }\n" ++
        "    let flt_txt: str = format_float(&mut num_buf, 3.25_f64) catch { return 13; };\n" ++
        "    let parsed_f64: f64 = parse_float[f64](flt_txt) catch { return 14; };\n" ++
        "    if parsed_f64 != 3.25_f64 { return 15; }\n" ++
        "\n" ++
        "    let e0: f64 = math.expm1(0.0_f64);\n" ++
        "    let pyth: f64 = math.hypot(3.0_f64, 4.0_f64);\n" ++
        "    let trig: f64 = math.sin(0.5_f64) * math.sin(0.5_f64) + math.cos(0.5_f64) * math.cos(0.5_f64);\n" ++
        "    if e0 != 0.0_f64 or not math.approx_eq_ulp(pyth, 5.0_f64, max_ulps: 2_u64) or\n" ++
        "        not math.approx_eq_ulp(trig, 1.0_f64, max_ulps: 4_u64) { return 16; }\n" ++
        "    if math.div_ceil(10_u32, 3_u32) != 4_u32 or math.ilog2(64_u32) != 6_u32 { return 17; }\n" ++
        "    0\n" ++
        "}\n";

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, smoke_app_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("step2_4tier_app", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, app_fid, .{ .io = io });
    defer report.deinit(allocator);
    if (!report.is_all_matching) {
        std.debug.print("{s}\n", .{report.rendered_diff_table});
    }
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 0), report.outcomes[0].return_scalar_i64);
}

test "test_regression_critical03_soa_vec_as_soa_slice_immutable_and_subslice_stride_4tier" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Verify 4-word `#soa [S]` and `&#soa [S]` descriptor layouts (`32 B` on 64-bit, `16 B` on `wasm32`):
    {
        const layout_src =
            "@soa\n" ++
            "@derive(Copy, Equatable)\n" ++
            "pub struct Point2 { pub x: i32, pub y: i32 }\n" ++
            "pub fn probe_soa_slice(view: #soa [Point2]) -> #soa [Point2] { return view; }\n" ++
            "pub fn probe_soa_slice_ref(view: &#soa [Point2]) -> &#soa [Point2] { return view; }\n";
        const targets = [_]struct { spec: TargetSpec, ptr_bytes: u64 }{
            .{ .spec = TargetSpec.X86_64_LINUX, .ptr_bytes = 8 },
            .{ .spec = TargetSpec.WASM32_WASI, .ptr_bytes = 4 },
        };
        for (targets) |target_case| {
            var db = try CompilerDb.init(allocator);
            defer db.deinit();
            db.setTargetSpec(target_case.spec);
            const fid = FileId.fromInt(0);
            _ = try db.setInput(fid, layout_src, .low);

            var sink = DiagnosticSink.init(allocator);
            defer sink.deinit();
            try collectAllDiagnostics(&db, fid, &sink);
            if (sink.hasErrors()) dumpUnexpectedDiagnostics("crit03_layout", &sink);
            try std.testing.expect(!sink.hasErrors());

            var resolver = TypeLayoutResolver.init(allocator, &db.type_pool, &db.symbol_table, target_case.spec);
            defer resolver.deinit();
            const opt_mod = try db.optimizeMirModule(fid, false);
            const soa_sl_ty = opt_mod.findBodyByName(&db.interner, "probe_soa_slice").?.ret_ty;
            const soa_ref_ty = opt_mod.findBodyByName(&db.interner, "probe_soa_slice_ref").?.ret_ty;
            try std.testing.expectEqual(4 * target_case.ptr_bytes, (try resolver.resolveType(soa_sl_ty)).size_bytes);
            try std.testing.expectEqual(4 * target_case.ptr_bytes, (try resolver.resolveType(soa_ref_ty)).size_bytes);
        }
    }

    // [2] Verify `as_soa_slice(&self)` never mutates/compacts `self` (`len < cap`) and sub-slicing preserves stride across 4 tiers:
    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

    const crit03_src =
        "@soa\n" ++
        "@derive(Copy, Equatable)\n" ++
        "pub struct Particle {\n" ++
        "    pub x: i32,\n" ++
        "    pub y: i32,\n" ++
        "}\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    var pvec: #soa Vec[Particle] = #soa Vec[Particle].with_capacity(8_usize);\n" ++
        "    pvec.push(Particle { x: 1, y: 10 });\n" ++
        "    pvec.push(Particle { x: 2, y: 20 });\n" ++
        "    pvec.push(Particle { x: 3, y: 30 });\n" ++
        "    pvec.push(Particle { x: 4, y: 40 });\n" ++
        "    pvec.push(Particle { x: 5, y: 50 });\n" ++
        "    if pvec.len() != 5_usize or pvec.capacity() < 8_usize { return 1; }\n" ++
        "\n" ++
        "    let ys = pvec.y;\n" ++
        "    let full: #soa [Particle] = pvec.as_soa_slice();\n" ++
        "    if ys[0] != 10 or ys[1] != 20 or ys[2] != 30 or ys[3] != 40 or ys[4] != 50 { return 2; }\n" ++
        "    if full.len() != 5_usize or full[0].y != 10 or full[4].y != 50 { return 3; }\n" ++
        "\n" ++
        "    let sub: &#soa [Particle] = full[1..4];\n" ++
        "    if sub.len() != 3_usize { return 4; }\n" ++
        "    if sub[0].x != 2 or sub[0].y != 20 or sub[2].x != 4 or sub[2].y != 40 { return 5; }\n" ++
        "    let sub_ys = sub.y;\n" ++
        "    if sub_ys.len() != 3_usize or sub_ys[0] != 20 or sub_ys[1] != 30 or sub_ys[2] != 40 { return 6; }\n" ++
        "\n" ++
        "    let nested: &#soa [Particle] = sub[1..3];\n" ++
        "    if nested.len() != 2_usize or nested[0].x != 3 or nested[0].y != 30 or nested[1].y != 40 { return 7; }\n" ++
        "    if nested.* != (full[2..4]).* { return 8; }\n" ++
        "    0\n" ++
        "}\n";

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, crit03_src, .low);
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("crit03_app", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, app_fid, .{ .io = io });
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 0), report.outcomes[0].return_scalar_i64);
}

test "test_regression_critical04_sast_arena_drop_elision_nontrivial_string_and_proj_store" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Verify projected sub-field mutation (`wrapper.inner = …`, `proj_len != 0`) disqualifies `is_arena_drop_elided`:
    {
        const proj_store_src =
            "@linear\n" ++
            "pub struct Arena { pub pos: usize }\n" ++
            "impl Arena {\n" ++
            "    pub fn destroy(own self) {\n" ++
            "        let Arena { pos } = self;\n" ++
            "        _ = pos;\n" ++
            "    }\n" ++
            "}\n" ++
            "pub trait Drop { fn drop(&mut self); }\n" ++
            "pub struct Vec[T] { pub ptr: usize, pub len: usize }\n" ++
            "impl[T] Drop for Vec[T] {\n" ++
            "    pub fn drop(&mut self) { @drop_trace(91); }\n" ++
            "}\n" ++
            "impl[T] Vec[T] {\n" ++
            "    pub fn new() -> Vec[T] { return Vec[T] { ptr: 1, len: 0 }; }\n" ++
            "    pub fn in_arena(arena: &mut Arena) -> Vec[T] {\n" ++
            "        arena.pos = arena.pos +% 1;\n" ++
            "        return Vec[T] { ptr: 2, len: 0 };\n" ++
            "    }\n" ++
            "}\n" ++
            "pub struct Wrapper { pub inner: Vec[u64] }\n" ++
            "pub fn overwrite_subfield() -> usize {\n" ++
            "    var arena = Arena { pos: 0 };\n" ++
            "    var wrap = Wrapper { inner: Vec[u64].in_arena(&mut arena) };\n" ++
            "    wrap.inner = Vec[u64].new();\n" ++
            "    (own arena).destroy();\n" ++
            "    return wrap.inner.ptr;\n" ++
            "}\n";
        var sast_bundle = try corex.lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(0),
            proj_store_src,
            corex.TargetLayout.NATIVE_64,
            .{},
        );
        defer sast_bundle.deinit();
        try std.testing.expectEqual(@as(usize, 0), sast_bundle.diagnostics.diagnostics.items.len);
        const body_ptr = sast_bundle.mir_module.findBodyByName(&sast_bundle.interner, "overwrite_subfield").?;
        const rendered = try corex.renderMir(allocator, body_ptr, &sast_bundle.interner);
        defer allocator.free(rendered);
        try std.testing.expect(std.mem.indexOf(u8, rendered, "drop_in_place") != null);
    }

    // [2] Verify `Vec[NonTrivialDrop].in_arena` runs element destructors AND `String.new()` / `SmallVec.new()`
    //     constructed inside `with context.allocator = &mut arena` are NOT drop-elided:
    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

    const crit04_src =
        "use cx.col.SmallVec;\n" ++
        "use cx.mem.Arena;\n" ++
        "\n" ++
        "pub struct TrackedElem {\n" ++
        "    pub tag: i32,\n" ++
        "}\n" ++
        "impl AutoDrop for TrackedElem {\n" ++
        "    pub fn drop(&mut self) {\n" ++
        "        @drop_trace(self.tag as u64);\n" ++
        "    }\n" ++
        "}\n" ++
        "\n" ++
        "@inline(never)\n" ++
        "pub fn run_arena_nontrivial_vec() -> usize {\n" ++
        "    var arena = Arena.new();\n" ++
        "    var count = 0_usize;\n" ++
        "    {\n" ++
        "        var items = Vec[TrackedElem].in_arena(&mut arena);\n" ++
        "        items.push(TrackedElem { tag: 101 });\n" ++
        "        items.push(TrackedElem { tag: 102 });\n" ++
        "        count = items.len();\n" ++
        "    }\n" ++
        "    own arena.release();\n" ++
        "    count\n" ++
        "}\n" ++
        "\n" ++
        "@inline(never)\n" ++
        "pub fn run_with_ctx_inline_containers() -> usize {\n" ++
        "    var arena = Arena.new();\n" ++
        "    let total: usize = with context.allocator = &mut arena {\n" ++
        "        var text = String.new();\n" ++
        "        text.push_str(\"0123456789abcdef0123456789abcdef0123456789abcdef\");\n" ++
        "        var small = SmallVec[u32, 4].new();\n" ++
        "        var idx = 0_u32;\n" ++
        "        while idx < 8_u32 {\n" ++
        "            small.push(idx);\n" ++
        "            idx += 1_u32;\n" ++
        "        }\n" ++
        "        text.len() + small.len()\n" ++
        "    };\n" ++
        "    own arena.release();\n" ++
        "    total\n" ++
        "}\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    if run_arena_nontrivial_vec() != 2_usize { return 1; }\n" ++
        "    if run_with_ctx_inline_containers() != 56_usize { return 2; }\n" ++
        "    0\n" ++
        "}\n";

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, crit04_src, .low);
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("crit04_app", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    const opt_mod = try db.optimizeMirModule(app_fid, false);
    const inline_body = opt_mod.findBodyByName(&db.interner, "run_with_ctx_inline_containers").?;
    const inline_mir = try corex.renderMir(allocator, inline_body, &db.interner);
    defer allocator.free(inline_mir);
    try std.testing.expect(std.mem.indexOf(u8, inline_mir, "drop_in_place") != null or
        std.mem.indexOf(u8, inline_mir, "drop_if_live") != null);

    var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, app_fid, .{ .io = io });
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 0), report.outcomes[0].return_scalar_i64);
    try std.testing.expectEqual(@as(usize, 2), report.outcomes[0].drop_trace.len);
}

test "test_regression_critical05_soa_vec_in_arena_routing_and_try_push_oom_elem_drop_4tier" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

    const crit05_src =
        "use cx.mem.{AllocError, Arena, FixedBuffer};\n" ++
        "\n" ++
        "pub struct DropToken {\n" ++
        "    pub code: i32,\n" ++
        "}\n" ++
        "impl AutoDrop for DropToken {\n" ++
        "    pub fn drop(&mut self) {\n" ++
        "        @drop_trace(self.code as u64);\n" ++
        "    }\n" ++
        "}\n" ++
        "\n" ++
        "@soa\n" ++
        "@derive(Copy, Equatable)\n" ++
        "pub struct Point {\n" ++
        "    pub x: i32,\n" ++
        "    pub y: i32,\n" ++
        "}\n" ++
        "\n" ++
        "@soa\n" ++
        "pub struct TrackedParticle {\n" ++
        "    pub token: DropToken,\n" ++
        "    pub weight: i32,\n" ++
        "}\n" ++
        "\n" ++
        "pub fn is_signed_type[T: Integer]() -> bool {\n" ++
        "    @implements[T, Signed]()\n" ++
        "}\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    // [1] `#soa Vec.in_arena(&mut arena)` routes slab allocation directly through `arena`:\n" ++
        "    var arena = Arena.new();\n" ++
        "    let cp_before = arena.checkpoint();\n" ++
        "    var arena_err: i32 = 0;\n" ++
        "    {\n" ++
        "        var avec = #soa Vec[Point].in_arena(&mut arena);\n" ++
        "        avec.push(Point { x: 3, y: 30 });\n" ++
        "        avec.push(Point { x: 7, y: 70 });\n" ++
        "        if avec.len() != 2_usize or avec[0].x != 3 or avec[1].y != 70 {\n" ++
        "            arena_err = 2;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    if arena.checkpoint() == cp_before {\n" ++
        "        arena_err = 1;\n" ++
        "    }\n" ++
        "    own arena.release();\n" ++
        "    if arena_err != 0 { return arena_err; }\n" ++
        "\n" ++
        "    // [2] `#soa Vec.try_push(own elem)` drops `elem` on deterministic `OutOfMemory`:\n" ++
        "    var tiny_backing: [u8; 8] = [0_u8; 8];\n" ++
        "    var fb = FixedBuffer.init(&mut tiny_backing);\n" ++
        "    let oom_ok: bool = with context.allocator = &mut fb {\n" ++
        "        var svec = #soa Vec[TrackedParticle].new();\n" ++
        "        let push_res: unit!AllocError = svec.try_push(TrackedParticle {\n" ++
        "            token: DropToken { code: 404 },\n" ++
        "            weight: 9,\n" ++
        "        });\n" ++
        "        (push_res is .Err(.OutOfMemory)) and (svec.len() == 0_usize)\n" ++
        "    };\n" ++
        "    if not oom_ok { return 3; }\n" ++
        "\n" ++
        "    // [3] `@implements[T, Signed]()` monomorphization parity across all 4 tiers:\n" ++
        "    if not is_signed_type[i32]() or is_signed_type[u32]() { return 4; }\n" ++
        "    0\n" ++
        "}\n";

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, crit05_src, .low);
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("crit05_app", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, app_fid, .{ .io = io });
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 0), report.outcomes[0].return_scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{404}, report.outcomes[0].drop_trace);
}

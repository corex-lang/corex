//! Phase 11.2a (`STD-02` Mandatory Step 1) Compiler Seams, `core.sys` & `MirVm` Shims Suite
//!
//! Verifies all Phase 11.2a Mandatory Step 1 prerequisites before authoring `stdlib/cx/{io,path,fs,time,env,process}.cx`:
//! - `8 B` niche-packed `IoError` / `FsError` (`u64 is 2..=u64.MAX`), `SwifterrorKind.nonnull_ptr` on 64-bit
//!   targets, and `@no_panic` `.bit_or` + `.narrow()` interval proof (`0` residual `narrow_check`).
//! - `24 B` SSO `PathBuf` (`sizeof(PathBuf?) == 24` on `x86_64-linux-gnu` and `wasm32-unknown-wasi`) and
//!   real `pub mod io;` / `pub mod fs;` superseding Phase-4 synthetic `cx.io` / `cx.fs` stubs.
//! - `OutBuf.over_uninit(&out raw)` 4-tier execution parity plus negative `E0305` (concurrent access),
//!   `E0306` (scope escape), and `E0303` (reading `raw[0]` directly after `OutBuf` ends).
//! - 46-entry `WASI_PREVIEW1_IMPORT_SET` SSOT parity across C99 and LLVM emitters on `wasm32-unknown-wasi`.
//! - Zero-diagnostic `--sast-strict` cross-target verification of all 14 `core/**/*.cx` files (`stat$INODE64`
//!   vs `stat` `144 B` `DarwinStat64`, zero `shell32`), `comptime` `E0503` hermeticity, and 4-tier `diff_oracle`
//!   parity on `MirVm` host OS shims (`_cx_rt_get_argc`, clock queries, and temp file write/read/unlink).

const std = @import("std");
const builtin = @import("builtin");
const corex = @import("corex");

const FileId = corex.FileId;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const DiagnosticCode = corex.DiagnosticCode;
const TargetSpec = corex.TargetSpec;
const TypeLayoutResolver = corex.TypeLayoutResolver;
const AbiClassifier = corex.AbiClassifier;

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

/// Canonical mounted `stdlib/cx/` source file paths (`11` files).
const CX_STDLIB_PATHS = [_][]const u8{
    "stdlib/cx/mod.cx",
    "stdlib/cx/col.cx",
    "stdlib/cx/env.cx",
    "stdlib/cx/fs.cx",
    "stdlib/cx/io.cx",
    "stdlib/cx/math.cx",
    "stdlib/cx/mem.cx",
    "stdlib/cx/path.cx",
    "stdlib/cx/process.cx",
    "stdlib/cx/str.cx",
    "stdlib/cx/time.cx",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `sink` contains at least one diagnostic matching `code`.
fn sinkHasCode(sink: *const DiagnosticSink, code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == code) return true;
    }
    return false;
}

/// Normalizes CRLF line endings to LF so in-memory `CompilerDb` inputs stay OS-independent.
fn normalizeLfAlloc(allocator: std.mem.Allocator, raw_bytes: []const u8) ![]u8 {
    var out_buf = try std.ArrayList(u8).initCapacity(allocator, raw_bytes.len);
    errdefer out_buf.deinit(allocator);
    for (raw_bytes) |byte_val| {
        if (byte_val != '\r') out_buf.appendAssumeCapacity(byte_val);
    }
    return out_buf.toOwnedSlice(allocator);
}

/// Collects all parse, signature, body, and 4-pass SAST diagnostics for `fid` into `out_sink`.
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

/// Prints unexpected diagnostics in `sink` to `stderr` for immediate failure diagnosis.
fn dumpUnexpectedDiagnostics(label: []const u8, sink: *const DiagnosticSink) void {
    for (sink.diagnostics.items) |diag_item| {
        std.debug.print(
            "[{s}] fid={d} {d}..{d} {s}: {s}\n",
            .{
                label,
                diag_item.primary_span.file_id.asInt(),
                diag_item.primary_span.start_byte,
                diag_item.primary_span.end_byte,
                @tagName(diag_item.code),
                diag_item.message,
            },
        );
    }
}

/// Loads all 14 `core/**/*.cx` files into `db` starting at `base_file_id` and registers `"core"`.
fn loadCoreTreeIntoDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    db: *CompilerDb,
    base_file_id: u32,
) ![CORE_MODULE_PATHS.len]FileId {
    var file_ids: [CORE_MODULE_PATHS.len]FileId = undefined;
    for (CORE_MODULE_PATHS, 0..) |mod_path, i| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(io, mod_path, allocator, .limited(1024 * 1024));
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

/// Mounts all 14 `core/**/*.cx` and 8 Wave-3A `stdlib/cx/*.cx` files into `db` as `.std_core`.
fn loadCoreAndCxStdlibIntoDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    db: *CompilerDb,
    base_file_id: u32,
) ![CORE_MODULE_PATHS.len + CX_STDLIB_PATHS.len]FileId {
    var all_fids: [CORE_MODULE_PATHS.len + CX_STDLIB_PATHS.len]FileId = undefined;
    for (CORE_MODULE_PATHS, 0..) |mod_path, i| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(io, mod_path, allocator, .limited(2 * 1024 * 1024));
        defer allocator.free(raw_bytes);
        const norm_bytes = try normalizeLfAlloc(allocator, raw_bytes);
        defer allocator.free(norm_bytes);
        const fid = FileId.fromInt(base_file_id + @as(u32, @intCast(i)));
        all_fids[i] = fid;
        try db.setFilePackageId(fid, .std_core);
        try db.setFilePath(fid, mod_path);
        _ = try db.setInput(fid, norm_bytes, .high);
    }
    const core_root_fid = all_fids[0];
    try db.registerRootModule("core", core_root_fid);
    try db.bindExternalModule(core_root_fid, "primitives", all_fids[1]);
    try db.bindExternalModule(core_root_fid, "mem", all_fids[2]);
    try db.bindExternalModule(core_root_fid, "atomic", all_fids[3]);
    try db.bindExternalModule(core_root_fid, "simd", all_fids[4]);
    try db.bindExternalModule(core_root_fid, "panic", all_fids[5]);
    try db.bindExternalModule(core_root_fid, "runtime", all_fids[6]);
    try db.bindExternalModule(core_root_fid, "sys", all_fids[7]);
    try db.bindExternalModule(core_root_fid, "ffi", all_fids[12]);
    try db.bindExternalModule(core_root_fid, "async", all_fids[13]);

    const sys_mod_fid = all_fids[7];
    try db.bindExternalModule(sys_mod_fid, "linux", all_fids[8]);
    try db.bindExternalModule(sys_mod_fid, "macos", all_fids[9]);
    try db.bindExternalModule(sys_mod_fid, "windows", all_fids[10]);
    try db.bindExternalModule(sys_mod_fid, "wasi", all_fids[11]);
    try db.markCoreKernelSubtree(core_root_fid);

    for (CX_STDLIB_PATHS, 0..) |cx_path, i| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(io, cx_path, allocator, .limited(4 * 1024 * 1024));
        defer allocator.free(raw_bytes);
        const norm_bytes = try normalizeLfAlloc(allocator, raw_bytes);
        defer allocator.free(norm_bytes);
        const slot_idx = CORE_MODULE_PATHS.len + i;
        const fid = FileId.fromInt(base_file_id + @as(u32, @intCast(slot_idx)));
        all_fids[slot_idx] = fid;
        try db.setFilePackageId(fid, .std_core);
        try db.setFilePath(fid, cx_path);
        _ = try db.setInput(fid, norm_bytes, .high);
    }
    const cx_mod_fid = all_fids[CORE_MODULE_PATHS.len];
    try db.registerRootModule("cx", cx_mod_fid);
    try db.registerCxStdlibPreludeRoot(cx_mod_fid);
    try db.bindExternalModule(cx_mod_fid, "col", all_fids[CORE_MODULE_PATHS.len + 1]);
    try db.bindExternalModule(cx_mod_fid, "env", all_fids[CORE_MODULE_PATHS.len + 2]);
    try db.bindExternalModule(cx_mod_fid, "fs", all_fids[CORE_MODULE_PATHS.len + 3]);
    try db.bindExternalModule(cx_mod_fid, "io", all_fids[CORE_MODULE_PATHS.len + 4]);
    try db.bindExternalModule(cx_mod_fid, "math", all_fids[CORE_MODULE_PATHS.len + 5]);
    try db.bindExternalModule(cx_mod_fid, "mem", all_fids[CORE_MODULE_PATHS.len + 6]);
    try db.bindExternalModule(cx_mod_fid, "path", all_fids[CORE_MODULE_PATHS.len + 7]);
    try db.bindExternalModule(cx_mod_fid, "process", all_fids[CORE_MODULE_PATHS.len + 8]);
    try db.bindExternalModule(cx_mod_fid, "str", all_fids[CORE_MODULE_PATHS.len + 9]);
    try db.bindExternalModule(cx_mod_fid, "time", all_fids[CORE_MODULE_PATHS.len + 10]);
    return all_fids;
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_std02_step1_ioerror_fserror_8b_niche_swifterror_and_bit_or_narrow_no_panic" {
    const allocator = std.testing.allocator;

    const err_src =
        "@derive(Copy, Equatable)\n" ++
        "pub struct IoError {\n" ++
        "    raw_bits: u64 is 2..=u64.MAX,\n" ++
        "}\n" ++
        "@derive(Copy, Equatable)\n" ++
        "pub struct FsError {\n" ++
        "    raw_bits: u64 is 2..=u64.MAX,\n" ++
        "}\n" ++
        "impl IoError {\n" ++
        "    @inline @no_alloc @no_panic\n" ++
        "    pub fn from_raw_os_error(kind_tag: u8, op_tag: u8, os_code: i32) -> IoError {\n" ++
        "        let payload: u64 = ((kind_tag as u64) << 8) | ((op_tag as u64) << 16) | (((os_code as u32) as u64) << 32);\n" ++
        "        return IoError { raw_bits: (payload | 2_u64).narrow[u64 is 2..=u64.MAX]() };\n" ++
        "    }\n" ++
        "}\n" ++
        "impl FsError {\n" ++
        "    @inline @no_alloc @no_panic\n" ++
        "    pub fn from_io(err: IoError) -> FsError {\n" ++
        "        return FsError { raw_bits: (err.raw_bits | 2_u64).narrow[u64 is 2..=u64.MAX]() };\n" ++
        "    }\n" ++
        "}\n" ++
        "pub fn probe_io_opt() -> IoError? { return .None; }\n" ++
        "pub fn probe_unit_io() -> unit!IoError { return .Ok(()); }\n" ++
        "pub fn probe_fs_opt() -> FsError? { return .None; }\n" ++
        "pub fn probe_unit_fs() -> unit!FsError { return .Ok(()); }\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.X86_64_LINUX);
    try db.setInternalCore(true);
    const fid = FileId.fromInt(0);
    try db.setFilePackageId(fid, .std_core);
    _ = try db.setInput(fid, err_src, .high);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("ioerror_fserror", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var resolver = TypeLayoutResolver.init(allocator, &db.type_pool, &db.symbol_table, TargetSpec.X86_64_LINUX);
    defer resolver.deinit();

    const opt_mod = try db.optimizeMirModule(fid, false);
    const io_opt_ty = opt_mod.findBodyByName(&db.interner, "probe_io_opt").?.ret_ty;
    const unit_io_ty = opt_mod.findBodyByName(&db.interner, "probe_unit_io").?.ret_ty;
    const fs_opt_ty = opt_mod.findBodyByName(&db.interner, "probe_fs_opt").?.ret_ty;
    const unit_fs_ty = opt_mod.findBodyByName(&db.interner, "probe_unit_fs").?.ret_ty;

    try std.testing.expectEqual(@as(u64, 8), (try resolver.resolveType(io_opt_ty)).size_bytes);
    try std.testing.expectEqual(@as(u64, 8), (try resolver.resolveType(unit_io_ty)).size_bytes);
    try std.testing.expectEqual(@as(u64, 8), (try resolver.resolveType(fs_opt_ty)).size_bytes);
    try std.testing.expectEqual(@as(u64, 8), (try resolver.resolveType(unit_fs_ty)).size_bytes);

    var io_abi = try AbiClassifier.classifyFn(allocator, &resolver, .{ .params = &.{}, .ret_ty = unit_io_ty });
    defer io_abi.deinit(allocator);
    try std.testing.expectEqual(corex.codegen_abi.SwifterrorKind.nonnull_ptr, io_abi.swifterror_kind);

    var fs_abi = try AbiClassifier.classifyFn(allocator, &resolver, .{ .params = &.{}, .ret_ty = unit_fs_ty });
    defer fs_abi.deinit(allocator);
    try std.testing.expectEqual(corex.codegen_abi.SwifterrorKind.nonnull_ptr, fs_abi.swifterror_kind);

    // Confirm Pass-4 `.bit_or` interval proof eliminated `narrow_check` inside `from_raw_os_error`:
    const ctor_body = opt_mod.findBodyByName(&db.interner, "from_raw_os_error").?;
    for (ctor_body.insts.items(.op), ctor_body.insts.items(.aux_u16)) |inst_op, aux_u16| {
        if (inst_op == .intrinsic_op) {
            try std.testing.expect(aux_u16 != @backingInt(corex.mir.MirIntrinsicKind.narrow_check));
        }
    }
}

test "test_std02_step1_pathbuf_24b_sso_niche_and_real_cx_io_fs_module_resolution" {
    const allocator = std.testing.allocator;

    // [1] `sizeof(PathBuf) == 24` and `sizeof(PathBuf?) == 24` on both `x86_64-linux-gnu` and `wasm32-unknown-wasi`:
    const pathbuf_src =
        "pub trait Drop { fn drop(&mut self); }\n" ++
        "pub trait AutoDrop: Drop {}\n" ++
        "@repr(C, align: 8)\n" ++
        "pub struct PathBuf {\n" ++
        "    raw_bytes: [u8; 24],\n" ++
        "}\n" ++
        "impl Drop for PathBuf {\n" ++
        "    pub fn drop(&mut self) {}\n" ++
        "}\n" ++
        "impl AutoDrop for PathBuf {}\n" ++
        "@derive(Copy, Equatable)\n" ++
        "pub struct FsError {\n" ++
        "    raw_bits: u64 is 2..=u64.MAX,\n" ++
        "}\n" ++
        "pub fn probe_pb() -> PathBuf { return PathBuf { raw_bytes: [0; 24] }; }\n" ++
        "pub fn probe_pb_opt() -> PathBuf? { return .None; }\n" ++
        "pub fn probe_pb_opt_opt() -> PathBuf?? { return .None; }\n" ++
        "pub fn probe_pb_res() -> PathBuf!FsError { return .Ok(PathBuf { raw_bytes: [0; 24] }); }\n";

    for ([_]TargetSpec{ TargetSpec.X86_64_LINUX, TargetSpec.WASM32_WASI }) |spec| {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(spec);
        try db.setInternalCore(true);
        const fid = FileId.fromInt(0);
        try db.setFilePackageId(fid, .std_core);
        _ = try db.setInput(fid, pathbuf_src, .high);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, fid, &sink);
        if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("pathbuf_niche", &sink);
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

        var resolver = TypeLayoutResolver.init(allocator, &db.type_pool, &db.symbol_table, spec);
        defer resolver.deinit();

        const opt_mod = try db.optimizeMirModule(fid, false);
        const pb_ty = opt_mod.findBodyByName(&db.interner, "probe_pb").?.ret_ty;
        const pb_opt_ty = opt_mod.findBodyByName(&db.interner, "probe_pb_opt").?.ret_ty;
        const pb_opt2_ty = opt_mod.findBodyByName(&db.interner, "probe_pb_opt_opt").?.ret_ty;
        const pb_res_ty = opt_mod.findBodyByName(&db.interner, "probe_pb_res").?.ret_ty;

        try std.testing.expectEqual(@as(u64, 24), (try resolver.resolveType(pb_ty)).size_bytes);
        try std.testing.expectEqual(@as(u64, 24), (try resolver.resolveType(pb_opt_ty)).size_bytes);
        try std.testing.expectEqual(@as(u64, 32), (try resolver.resolveType(pb_opt2_ty)).size_bytes);
        if (!spec.isWasm()) {
            var pb_res_abi = try AbiClassifier.classifyFn(allocator, &resolver, .{ .params = &.{}, .ret_ty = pb_res_ty });
            defer pb_res_abi.deinit(allocator);
            try std.testing.expectEqual(corex.codegen_abi.SwifterrorKind.nonnull_ptr, pb_res_abi.swifterror_kind);
        }
    }

    // [2] Real `pub mod io;` and `pub mod fs;` in `cx` root cleanly replace synthetic Phase-4 stubs:
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        const cx_root_fid = FileId.fromInt(1);
        const cx_io_fid = FileId.fromInt(2);
        const cx_fs_fid = FileId.fromInt(3);
        const app_fid = FileId.fromInt(0);

        _ = try db.setInput(cx_root_fid, "pub mod io;\npub mod fs;\n", .high);
        _ = try db.setInput(cx_io_fid, "pub fn real_io_probe() -> i32 { 41 }\n", .high);
        _ = try db.setInput(cx_fs_fid, "pub fn real_fs_probe() -> i32 { 59 }\n", .high);
        _ = try db.setInput(
            app_fid,
            "use cx.*;\npub fn check_both() -> i32 { io.real_io_probe() + fs.real_fs_probe() }\n",
            .low,
        );
        try db.registerRootModule("cx", cx_root_fid);
        try db.bindExternalModule(cx_root_fid, "io", cx_io_fid);
        try db.bindExternalModule(cx_root_fid, "fs", cx_fs_fid);
        try db.registerCxStdlibPreludeRoot(cx_root_fid);

        for ([_]FileId{ cx_root_fid, cx_io_fid, cx_fs_fid, app_fid }) |fid| {
            var sink = DiagnosticSink.init(allocator);
            defer sink.deinit();
            try collectAllDiagnostics(&db, fid, &sink);
            if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("cx_io_fs_mod", &sink);
            try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);
        }
    }
}

test "test_std02_step1_outbuf_over_uninit_4tier_parity_and_e0305_e0306_e0303_soundness" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const core_outbuf_src =
        "/# Minimal `.std_core` `OutBuf` harness verifying `over_uninit(&out raw)` soundness\n" ++
        "@repr(C)\n" ++
        "pub struct OutBuf {\n" ++
        "    @non_null\n" ++
        "    base_ptr: *mut u8,\n" ++
        "    cap_bytes: usize,\n" ++
        "    init_len: usize,\n" ++
        "}\n" ++
        "impl OutBuf {\n" ++
        "    @std_cap_boundary(clears: [unsafe_op]) @inline @no_alloc @no_panic\n" ++
        "    pub fn over_uninit[const N: usize](buf: &out [u8; N]) -> OutBuf {\n" ++
        "        OutBuf {\n" ++
        "            base_ptr: (&raw mut buf.*) as *mut u8,\n" ++
        "            cap_bytes: N,\n" ++
        "            init_len: 0,\n" ++
        "        }\n" ++
        "    }\n" ++
        "    @std_cap_boundary(clears: [unsafe_op]) @no_alloc @no_panic\n" ++
        "    pub fn append_bytes(&mut self, src: &[u8]) -> usize {\n" ++
        "        let avail: usize = self.cap_bytes -| self.init_len;\n" ++
        "        let copy_n: usize = if src.len() < avail { src.len() } else { avail };\n" ++
        "        if copy_n > 0 {\n" ++
        "            unsafe {\n" ++
        "                @memcpy(self.base_ptr.add(self.init_len) as *mut opaque, src.as_ptr() as *opaque, copy_n);\n" ++
        "            }\n" ++
        "        }\n" ++
        "        self.init_len = self.init_len +% copy_n;\n" ++
        "        copy_n\n" ++
        "    }\n" ++
        "    @std_cap_boundary(clears: [unsafe_op]) @inline @no_alloc @no_panic\n" ++
        "    pub fn initialized(&self) -> &[u8] {\n" ++
        "        unsafe { @slice_from_raw_parts(self.base_ptr as *u8, self.init_len) }\n" ++
        "    }\n" ++
        "}\n";

    // [1] Positive 4-tier `diff_oracle` execution (`over_uninit` writes without caller `memset`):
    {
        const pos_app_src =
            "use cx.OutBuf;\n" ++
            "pub fn main() -> i32 {\n" ++
            "    var raw: [u8; 64];\n" ++
            "    var out = OutBuf.over_uninit(&out raw);\n" ++
            "    let wrote: usize = out.append_bytes(b\"CoreX\");\n" ++
            "    let filled: &[u8] = out.initialized();\n" ++
            "    (wrote as i32) * 100 + (filled[0] as i32) + (filled[4] as i32)\n" ++
            "}\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        const core_fid = FileId.fromInt(1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(core_fid, core_outbuf_src, .high);
        try db.registerRootModule("core", core_fid);
        _ = try db.setInput(app_fid, pos_app_src, .low);

        for ([_]FileId{ core_fid, app_fid }) |fid| {
            var sink = DiagnosticSink.init(allocator);
            defer sink.deinit();
            try collectAllDiagnostics(&db, fid, &sink);
            if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("outbuf_pos", &sink);
            try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);
        }

        var report = try corex.runFourTierDiffOracleOnDb(
            allocator,
            &db,
            app_fid,
            .{ .io = io, .extra_file_ids = &.{core_fid} },
        );
        defer report.deinit(allocator);
        if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
        try std.testing.expect(report.is_all_matching);
        // 5 * 100 + 'C' (67) + 'X' (88) = 655
        try std.testing.expectEqual(@as(i64, 655), report.outcomes[0].return_scalar_i64);
    }

    // [2] Negative `E0305`: mutating `raw` while `OutBuf` mutable loan is still live:
    {
        const neg_e0305_src =
            "use cx.OutBuf;\n" ++
            "pub fn bad_concurrent_access() -> usize {\n" ++
            "    var raw: [u8; 16] = [0; 16];\n" ++
            "    var out = OutBuf.over_uninit(&out raw);\n" ++
            "    raw[0] = 9;\n" ++
            "    out.initialized().len()\n" ++
            "}\n";
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        const core_fid = FileId.fromInt(1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(core_fid, core_outbuf_src, .high);
        try db.registerRootModule("core", core_fid);
        _ = try db.setInput(app_fid, neg_e0305_src, .low);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        try std.testing.expect(sinkHasCode(&sink, .e0305_exclusivity_violation));
    }

    // [3] Negative `E0306`: returning `OutBuf` borrowing stack-local `raw`:
    {
        const neg_e0306_src =
            "use cx.OutBuf;\n" ++
            "pub fn bad_escape() -> OutBuf {\n" ++
            "    var raw: [u8; 16];\n" ++
            "    OutBuf.over_uninit(&out raw)\n" ++
            "}\n";
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        const core_fid = FileId.fromInt(1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(core_fid, core_outbuf_src, .high);
        try db.registerRootModule("core", core_fid);
        _ = try db.setInput(app_fid, neg_e0306_src, .low);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        try std.testing.expect(sinkHasCode(&sink, .e0306_region_escape_violation));
    }

    // [4] Negative `E0303`: reading `raw[0]` directly after `OutBuf` ends (`raw` stays `maybe_uninit`!):
    {
        const neg_e0303_src =
            "use cx.OutBuf;\n" ++
            "pub fn bad_uninit_raw_read() -> u8 {\n" ++
            "    var raw: [u8; 16];\n" ++
            "    var out = OutBuf.over_uninit(&out raw);\n" ++
            "    let _wrote = out.append_bytes(b\"hi\");\n" ++
            "    raw[0]\n" ++
            "}\n";
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        const core_fid = FileId.fromInt(1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(core_fid, core_outbuf_src, .high);
        try db.registerRootModule("core", core_fid);
        _ = try db.setInput(app_fid, neg_e0303_src, .low);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        try std.testing.expect(sinkHasCode(&sink, .e0303_uninitialized_memory_read));
    }
}

test "test_std02_step1_wasi_preview1_import_set_ssot_parity_c99_and_llvm" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    for ([_][]const u8{
        "args_sizes_get",
        "args_get",
        "environ_sizes_get",
        "environ_get",
        "clock_time_get",
        "fd_close",
        "fd_datasync",
        "fd_sync",
        "fd_read",
        "fd_pread",
        "fd_write",
        "fd_pwrite",
        "fd_seek",
        "fd_tell",
        "fd_fdstat_get",
        "fd_filestat_get",
        "fd_filestat_set_size",
        "fd_prestat_get",
        "fd_prestat_dir_name",
        "fd_readdir",
        "path_create_directory",
        "path_filestat_get",
        "path_link",
        "path_open",
        "path_readlink",
        "path_remove_directory",
        "path_rename",
        "path_symlink",
        "path_unlink_file",
        "poll_oneoff",
        "proc_exit",
    }) |wasi_name| {
        try std.testing.expect(corex.codegen_abi.WASI_PREVIEW1_IMPORT_SET.has(wasi_name));
    }

    const wasi_probe_src =
        "use core.sys.wasi.*;\n" ++
        "pub fn probe_wasi_imports(fd: i32) -> u16 {\n" ++
        "    var argc: usize = 0;\n" ++
        "    var buf_sz: usize = 0;\n" ++
        "    var now_ns: u64 = 0;\n" ++
        "    var opened_fd: i32 = -1;\n" ++
        "    unsafe {\n" ++
        "        let r1 = wasi_args_sizes_get(&raw mut argc, &raw mut buf_sz);\n" ++
        "        let r2 = wasi_clock_time_get(WASI_CLOCKID_MONOTONIC, 1, &raw mut now_ns);\n" ++
        "        let r3 = wasi_path_open(fd, 0, b\".\".as_ptr(), 1, 0, WASI_RIGHTS_ALL, WASI_RIGHTS_ALL, 0, &raw mut opened_fd);\n" ++
        "        let r4 = wasi_fd_close(opened_fd);\n" ++
        "        return r1 | r2 | r3 | r4;\n" ++
        "    }\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.WASM32_WASI);
    try db.setInternalCore(true);
    const core_fids = try loadCoreTreeIntoDb(allocator, io, &db, 1);
    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, wasi_probe_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("wasi_probe", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var c_art = try db.compileModuleArtifact(
        app_fid,
        .{ .tier_a_c99 = .{ .target = TargetSpec.WASM32_WASI, .is_release_mode = true, .has_line_directives = false } },
        .{ .artifact_kind = .source_text, .extra_file_ids = &core_fids },
    );
    defer c_art.deinit(allocator);

    var ll_art = try db.compileModuleArtifact(
        app_fid,
        .{ .tier_b_llvm = .{ .target = TargetSpec.WASM32_WASI, .is_release_mode = true } },
        .{ .artifact_kind = .source_text, .extra_file_ids = &core_fids },
    );
    defer ll_art.deinit(allocator);

    for ([_][]const u8{ "args_sizes_get", "clock_time_get", "path_open", "fd_close" }) |sym_name| {
        try std.testing.expect(std.mem.indexOf(u8, c_art.emitted_text, "import_module(\"wasi_snapshot_preview1\")") != null);
        try std.testing.expect(std.mem.indexOf(u8, c_art.emitted_text, sym_name) != null);
        try std.testing.expect(std.mem.indexOf(u8, ll_art.emitted_text, "\"wasm-import-module\"=\"wasi_snapshot_preview1\"") != null);
        try std.testing.expect(std.mem.indexOf(u8, ll_art.emitted_text, sym_name) != null);
    }
}

test "test_std02_step1_core_sys_cross_target_clean_and_4tier_mir_vm_host_shims" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Verify zero `shell32` references in `core/sys/windows.cx`:
    {
        const win_sys_bytes = try std.Io.Dir.cwd().readFileAlloc(io, "core/sys/windows.cx", allocator, .limited(1024 * 1024));
        defer allocator.free(win_sys_bytes);
        try std.testing.expect(std.mem.indexOf(u8, win_sys_bytes, "shell32") == null);
    }

    // [2] Compile all 14 `core/**/*.cx` files cleanly (`0` errors, `0` warnings) across Linux, macOS (`x86_64` + `aarch64`), Windows, & WASI:
    for ([_]TargetSpec{
        TargetSpec.X86_64_LINUX,
        TargetSpec.AARCH64_LINUX,
        TargetSpec.X86_64_MACOS,
        TargetSpec.AARCH64_MACOS,
        TargetSpec.X86_64_WINDOWS_MSVC,
        TargetSpec.WASM32_WASI,
    }) |spec| {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(spec);
        try db.setInternalCore(true);
        const core_fids = try loadCoreTreeIntoDb(allocator, io, &db, 0);
        for (core_fids, 0..) |fid, idx| {
            var sink = DiagnosticSink.init(allocator);
            defer sink.deinit();
            try collectAllDiagnostics(&db, fid, &sink);
            if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics(CORE_MODULE_PATHS[idx], &sink);
            try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);
        }

        // Verify `DarwinStat64 == 144 B` and `stat$INODE64` (`x86_64`) vs `stat` (`aarch64`) on macOS targets:
        if (spec.os == .macos) {
            const probe_fid = FileId.fromInt(50);
            const probe_src =
                "use core.sys.macos.*;\n" ++
                "pub fn probe_darwin_stat(path_ptr: *u8, st_out: *mut DarwinStat64) -> i32 {\n" ++
                "    unsafe { darwin_stat(path_ptr, st_out) }\n" ++
                "}\n" ++
                "pub fn probe_stat_layout() -> DarwinStat64 { @default_init[DarwinStat64]() }\n";
            _ = try db.setInput(probe_fid, probe_src, .low);
            var probe_sink = DiagnosticSink.init(allocator);
            defer probe_sink.deinit();
            try collectAllDiagnostics(&db, probe_fid, &probe_sink);
            if (probe_sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("darwin_probe", &probe_sink);
            try std.testing.expectEqual(@as(usize, 0), probe_sink.diagnostics.items.len);

            var resolver = TypeLayoutResolver.init(allocator, &db.type_pool, &db.symbol_table, spec);
            defer resolver.deinit();
            const opt_probe = try db.optimizeMirModule(probe_fid, true);
            const stat_ty = opt_probe.findBodyByName(&db.interner, "probe_stat_layout").?.ret_ty;
            try std.testing.expectEqual(@as(u64, 144), (try resolver.resolveType(stat_ty)).size_bytes);

            var ll_art = try db.compileModuleArtifact(
                probe_fid,
                .{ .tier_b_llvm = .{ .target = spec, .is_release_mode = true } },
                .{ .artifact_kind = .source_text, .extra_file_ids = &core_fids },
            );
            defer ll_art.deinit(allocator);
            if (spec.arch == .x86_64) {
                try std.testing.expect(std.mem.indexOf(u8, ll_art.emitted_text, "stat$INODE64") != null);
            } else {
                try std.testing.expect(std.mem.indexOf(u8, ll_art.emitted_text, "stat$INODE64") == null);
            }
        }
    }

    // [3] Verify `comptime` stays 100% hermetic (`E0503` when calling `core.sys.rt_get_argc` in `const`):
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        try db.setInternalCore(true);
        _ = try loadCoreTreeIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(
            app_fid,
            "use core.sys;\npub const FORBIDDEN_ARGC: i32 = unsafe { sys.rt_get_argc() };\n",
            .low,
        );
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        try std.testing.expect(sinkHasCode(&sink, .e0503_forbidden_comptime_operation));
    }

    // [4] 4-Tier `diff_oracle` parity on `MirVm` host OS shims (`_cx_rt_get_argc`, clock query, temp file write/read/unlink):
    const host_oracle_src = if (builtin.os.tag == .windows)
        "use core.sys;\n" ++
            "use core.sys.windows.*;\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    unsafe {\n" ++
            "        let argc: i32 = sys.rt_get_argc();\n" ++
            "        let argv: *mut *mut u8 = sys.rt_get_argv();\n" ++
            "        var argv_ok: i32 = 0;\n" ++
            "        if argc >= 1 and argv != (0 as *mut *mut u8) {\n" ++
            "            let arg0: *mut u8 = argv.read();\n" ++
            "            let term_ptr: *mut u8 = argv.add(argc as usize).read();\n" ++
            "            if arg0 != (0 as *mut u8) and arg0.read() != 0 and term_ptr == (0 as *mut u8) {\n" ++
            "                argv_ok = 10;\n" ++
            "            }\n" ++
            "        }\n\n" ++
            "        var qpc_freq: i64 = 0;\n" ++
            "        var qpc_now: i64 = 0;\n" ++
            "        var wall_ft = Win32FileTime { low_date_time: 0, high_date_time: 0 };\n" ++
            "        let _ok_f = win32_query_performance_frequency(&raw mut qpc_freq);\n" ++
            "        let _ok_c = win32_query_performance_counter(&raw mut qpc_now);\n" ++
            "        win32_get_system_time_precise_as_file_time(&raw mut wall_ft);\n" ++
            "        let clock_ok: i32 = if qpc_freq > 0 and qpc_now > 0 and wall_ft.high_date_time > 0 => 20 else 0;\n\n" ++
            "        var tmp_path_w: [u16; 64] = [0; 64];\n" ++
            "        let rel_ascii = b\".zig-cache\\\\cx_std02_step1_oracle.tmp\";\n" ++
            "        var idx: usize = 0;\n" ++
            "        while idx < rel_ascii.len() {\n" ++
            "            tmp_path_w[idx] = rel_ascii[idx] as u16;\n" ++
            "            idx += 1;\n" ++
            "        }\n" ++
            "        tmp_path_w[rel_ascii.len()] = 0;\n\n" ++
            "        let fh = win32_create_file_w(\n" ++
            "            (&raw tmp_path_w) as *u16,\n" ++
            "            GENERIC_READ | GENERIC_WRITE,\n" ++
            "            FILE_SHARE_ALL,\n" ++
            "            0 as *Win32SecurityAttributes,\n" ++
            "            CREATE_ALWAYS,\n" ++
            "            FILE_ATTRIBUTE_NORMAL,\n" ++
            "            0 as *mut opaque,\n" ++
            "        );\n" ++
            "        var wrote_n: u32 = 0;\n" ++
            "        let payload = b\"STD02-WIN32-OK\";\n" ++
            "        let _wf = win32_write_file(fh, payload.as_ptr(), payload.len() as u32, &raw mut wrote_n, 0 as *mut opaque);\n" ++
            "        var seek_pos: i64 = -1;\n" ++
            "        let _sf = win32_set_file_pointer_ex(fh, 0, &raw mut seek_pos, FILE_BEGIN);\n" ++
            "        var read_buf: [u8; 16] = [0; 16];\n" ++
            "        var read_n: u32 = 0;\n" ++
            "        let _rf = win32_read_file(fh, (&raw mut read_buf) as *mut u8, 14, &raw mut read_n, 0 as *mut opaque);\n" ++
            "        let _ch = win32_close_handle(fh);\n" ++
            "        let _del = win32_delete_file_w((&raw tmp_path_w) as *u16);\n\n" ++
            "        let std_out = win32_get_std_handle(STD_OUTPUT_HANDLE);\n" ++
            "        var console_wrote: u32 = 0;\n" ++
            "        let _cw = win32_write_file(std_out, (&raw read_buf) as *u8, read_n, &raw mut console_wrote, 0 as *mut opaque);\n\n" ++
            "        let fs_ok: i32 = if wrote_n == 14 and seek_pos == 0 and read_n == 14 and\n" ++
            "            read_buf[0] == b'S' and read_buf[13] == b'K' { 40 } else { 0 };\n" ++
            "        argv_ok + clock_ok + fs_ok\n" ++
            "    }\n" ++
            "}\n"
    else if (builtin.os.tag == .linux)
        "use core.sys;\n" ++
            "use core.sys.linux.*;\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    unsafe {\n" ++
            "        let argc: i32 = sys.rt_get_argc();\n" ++
            "        let argv: *mut *mut u8 = sys.rt_get_argv();\n" ++
            "        var argv_ok: i32 = 0;\n" ++
            "        if argc >= 1 and argv != (0 as *mut *mut u8) {\n" ++
            "            let arg0: *mut u8 = argv.read();\n" ++
            "            let term_ptr: *mut u8 = argv.add(argc as usize).read();\n" ++
            "            if arg0 != (0 as *mut u8) and arg0.read() != 0 and term_ptr == (0 as *mut u8) {\n" ++
            "                argv_ok = 10;\n" ++
            "            }\n" ++
            "        }\n\n" ++
            "        var mono_ts = PosixTimespec { tv_sec: 0, tv_nsec: 0 };\n" ++
            "        let clk_rc: i32 = linux_clock_gettime(CLOCK_MONOTONIC, &raw mut mono_ts);\n" ++
            "        let clock_ok: i32 = if clk_rc == 0 and (mono_ts.tv_sec > 0 or mono_ts.tv_nsec > 0) => 20 else 0;\n\n" ++
            "        let tmp_cstr = b\".zig-cache/cx_std02_step1_oracle.tmp\\0\";\n" ++
            "        let fd: i32 = linux_openat_mode(AT_FDCWD, tmp_cstr.as_ptr(), O_CREAT | O_TRUNC | O_RDWR | O_CLOEXEC, 0o600);\n" ++
            "        let payload = b\"STD02-POSIX-OK\";\n" ++
            "        let wrote_n: isize = linux_posix_write(fd, payload.as_ptr(), payload.len());\n" ++
            "        let seek_pos: i64 = linux_lseek(fd, 0, SEEK_SET);\n" ++
            "        var read_buf: [u8; 16] = [0; 16];\n" ++
            "        let read_n: isize = linux_posix_read(fd, (&raw mut read_buf) as *mut u8, 14);\n" ++
            "        let _cl = linux_close(fd);\n" ++
            "        let _ul = linux_unlinkat(AT_FDCWD, tmp_cstr.as_ptr(), 0);\n" ++
            "        let _so = linux_posix_write(STDOUT_FILENO, (&raw read_buf) as *u8, read_n as usize);\n\n" ++
            "        let fs_ok: i32 = if wrote_n == 14 and seek_pos == 0 and read_n == 14 and\n" ++
            "            read_buf[0] == b'S' and read_buf[13] == b'K' { 40 } else { 0 };\n" ++
            "        argv_ok + clock_ok + fs_ok\n" ++
            "    }\n" ++
            "}\n"
    else
        "use core.sys;\n" ++
            "use core.sys.macos.*;\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    unsafe {\n" ++
            "        let argc: i32 = sys.rt_get_argc();\n" ++
            "        let argv: *mut *mut u8 = sys.rt_get_argv();\n" ++
            "        var argv_ok: i32 = 0;\n" ++
            "        if argc >= 1 and argv != (0 as *mut *mut u8) {\n" ++
            "            let arg0: *mut u8 = argv.read();\n" ++
            "            let term_ptr: *mut u8 = argv.add(argc as usize).read();\n" ++
            "            if arg0 != (0 as *mut u8) and arg0.read() != 0 and term_ptr == (0 as *mut u8) {\n" ++
            "                argv_ok = 10;\n" ++
            "            }\n" ++
            "        }\n\n" ++
            "        var mono_ts = PosixTimespec { tv_sec: 0, tv_nsec: 0 };\n" ++
            "        let clk_rc: i32 = darwin_clock_gettime(CLOCK_MONOTONIC, &raw mut mono_ts);\n" ++
            "        let clock_ok: i32 = if clk_rc == 0 and (mono_ts.tv_sec > 0 or mono_ts.tv_nsec > 0) => 20 else 0;\n\n" ++
            "        let tmp_cstr = b\".zig-cache/cx_std02_step1_oracle.tmp\\0\";\n" ++
            "        let fd: i32 = darwin_openat_mode(AT_FDCWD, tmp_cstr.as_ptr(), O_CREAT | O_TRUNC | O_RDWR | O_CLOEXEC, 0o600);\n" ++
            "        let payload = b\"STD02-POSIX-OK\";\n" ++
            "        let wrote_n: isize = darwin_write(fd, payload.as_ptr(), payload.len());\n" ++
            "        let seek_pos: i64 = darwin_lseek(fd, 0, SEEK_SET);\n" ++
            "        var read_buf: [u8; 16] = [0; 16];\n" ++
            "        let read_n: isize = darwin_read(fd, (&raw mut read_buf) as *mut u8, 14);\n" ++
            "        let _cl = darwin_close(fd);\n" ++
            "        let _ul = darwin_unlinkat(AT_FDCWD, tmp_cstr.as_ptr(), 0);\n" ++
            "        let _so = darwin_write(STDOUT_FILENO, (&raw read_buf) as *u8, read_n as usize);\n\n" ++
            "        let fs_ok: i32 = if wrote_n == 14 and seek_pos == 0 and read_n == 14 and\n" ++
            "            read_buf[0] == b'S' and read_buf[13] == b'K' { 40 } else { 0 };\n" ++
            "        argv_ok + clock_ok + fs_ok\n" ++
            "    }\n" ++
            "}\n";

    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        try db.setInternalCore(true);
        const core_fids = try loadCoreTreeIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, host_oracle_src, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("host_oracle", &sink);
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

        var report = try corex.runFourTierDiffOracleOnDb(
            allocator,
            &db,
            app_fid,
            .{ .io = io, .extra_file_ids = &core_fids },
        );
        defer report.deinit(allocator);
        if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
        try std.testing.expect(report.is_all_matching);
        try std.testing.expect(!report.outcomes[0].has_trapped);
        try std.testing.expectEqual(@as(i64, 70), report.outcomes[0].return_scalar_i64);
        const expected_stdout = if (builtin.os.tag == .windows) "STD02-WIN32-OK" else "STD02-POSIX-OK";
        try std.testing.expectEqualStrings(expected_stdout, report.outcomes[0].stdout_bytes);
    }
}

test "test_std02_step1_context_reactor_nominal_resolution_and_copy_iosubmission_4tier_parity" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const reactor_src =
        "use core.async.{IoSubmission, Reactor, ReactorCtx, ReactorVTable, SIM_OP_SLEEP_NS, SIM_UNHANDLED_SENTINEL};\n\n" ++
        "@repr(C)\n" ++
        "struct SimSlots {\n" ++
        "    monotonic_ns: (extern \"C\" fn(*mut opaque) -> u64)?,\n" ++
        "    wall_epoch_ns: (extern \"C\" fn(*mut opaque) -> i64)?,\n" ++
        "    fill_rng: usize,\n" ++
        "    submit_io: (extern \"C\" fn(*mut opaque, *IoSubmission) -> i64)?,\n" ++
        "    tail_slots: [usize; 4],\n" ++
        "}\n\n" ++
        "extern \"C\" fn mock_mono(ctx: *mut opaque) -> u64 {\n" ++
        "    let ptr = ctx as *u64;\n" ++
        "    if ptr.is_null() { return 0_u64; }\n" ++
        "    unsafe { ptr.* }\n" ++
        "}\n\n" ++
        "extern \"C\" fn mock_submit(ctx: *mut opaque, sub: *IoSubmission) -> i64 {\n" ++
        "    let ptr = ctx as *mut u64;\n" ++
        "    if ptr.is_null() { return SIM_UNHANDLED_SENTINEL; }\n" ++
        "    if sub.is_null() { return SIM_UNHANDLED_SENTINEL; }\n" ++
        "    let delta: u64 = unsafe { sub.*.offset_or_ns };\n" ++
        "    unsafe { ptr.* = ptr.* +| delta; }\n" ++
        "    0_i64\n" ++
        "}\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    var state = 100_u64;\n" ++
        "    let vtable = SimSlots {\n" ++
        "        monotonic_ns: .Some(mock_mono),\n" ++
        "        wall_epoch_ns: .None,\n" ++
        "        fill_rng: 0_usize,\n" ++
        "        submit_io: .Some(mock_submit),\n" ++
        "        tail_slots: [0_usize; 4],\n" ++
        "    };\n" ++
        "    let sim_reactor = Reactor { vtable: (&raw vtable) as *ReactorVTable };\n" ++
        "    let sim_ctx = ReactorCtx { state: (&raw mut state) as *mut opaque };\n" ++
        "    with context.reactor = sim_reactor {\n" ++
        "        with context.reactor_ctx = sim_ctx {\n" ++
        "            let cur_reactor: Reactor = context.reactor;\n" ++
        "            let cur_ctx: ReactorCtx = context.reactor_ctx;\n" ++
        "            let slots = cur_reactor.vtable as *SimSlots;\n" ++
        "            if not slots.is_null() {\n" ++
        "                let sub = IoSubmission {\n" ++
        "                    kind: SIM_OP_SLEEP_NS,\n" ++
        "                    flags: 0_u8,\n" ++
        "                    worker_id: 0_u16,\n" ++
        "                    fd_or_handle: -1,\n" ++
        "                    offset_or_ns: 42_u64,\n" ++
        "                    buf_ptr: @default_init[*mut u8](),\n" ++
        "                    buf_len: 0_u32,\n" ++
        "                    slot_index: 0_u32,\n" ++
        "                };\n" ++
        "                if (unsafe { slots.*.submit_io }) is .Some(cb) {\n" ++
        "                    _ = unsafe { cb(cur_ctx.state, &raw sub) };\n" ++
        "                }\n" ++
        "                if (unsafe { slots.*.monotonic_ns }) is .Some(mcb) {\n" ++
        "                    return (unsafe { mcb(cur_ctx.state) }) as i32;\n" ++
        "                }\n" ++
        "            }\n" ++
        "        }\n" ++
        "    }\n" ++
        "    0\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    try db.setInternalCore(true);
    const core_fids = try loadCoreTreeIntoDb(allocator, io, &db, 1);
    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, reactor_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("reactor_nominal", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try corex.runFourTierDiffOracleOnDb(
        allocator,
        &db,
        app_fid,
        .{ .io = io, .extra_file_ids = &core_fids },
    );
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 142), report.outcomes[0].return_scalar_i64);
}

test "test_std02_wave3a_over_uninit_clone_bufwriter_default_arg_and_c99_fmt_debug_4tier_parity" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] `MirBody.clone` preserves `sast_owner_def_id` and `sast_owner_symbol`:
    {
        var orig_body = corex.MirBody.init(allocator, FileId.fromInt(7), corex.query_db.DefId.fromInt(99));
        defer orig_body.deinit();
        orig_body.is_sast_default_probe = true;
        orig_body.sast_owner_def_id = corex.query_db.DefId.fromInt(42);
        orig_body.sast_owner_symbol = corex.symbol_resolver.SymbolIndex.fromInt(123);

        var cloned_body = try orig_body.clone(allocator);
        defer cloned_body.deinit();
        try std.testing.expect(cloned_body.is_sast_default_probe);
        try std.testing.expectEqual(orig_body.sast_owner_def_id, cloned_body.sast_owner_def_id);
        try std.testing.expectEqual(orig_body.sast_owner_symbol, cloned_body.sast_owner_symbol);
    }

    // [2] 4-Tier `diff_oracle` on mounted `cx.io`: `OutBuf.over_uninit`, `BufReader.over_uninit`, `BufWriter.over_uninit`,
    //     `BufWriter.new(sw.as_writer())` omitting `line_buffered: bool = false`, and `-ofmt=c` `@derive(Debug)` `@fmt_write`:
    {
        const wave3a_io_src =
            "use cx.io.{BufReader, BufWriter, ByteReader, IoError, IoErrorKind, OutBuf, SliceWriter};\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    var raw_out: [u8; 16];\n" ++
            "    var out_buf = OutBuf.over_uninit(&out raw_out);\n" ++
            "    let ob_len = out_buf.append(b\"cx\") as i32;\n\n" ++
            "    var br_src = ByteReader.new(b\"line1\\nline2\");\n" ++
            "    var raw_rd: [u8; 16];\n" ++
            "    var buf_rd = BufReader.over_uninit(br_src.as_reader(), &out raw_rd);\n" ++
            "    let first_line: str? = buf_rd.next_line() catch unreachable;\n" ++
            "    let br_ok: i32 = if first_line == .Some(\"line1\") => 10 else 0;\n\n" ++
            "    var sink_uninit: [u8; 32] = [0_u8; 32];\n" ++
            "    var sw_uninit = SliceWriter.new(&mut sink_uninit);\n" ++
            "    var raw_wr: [u8; 16];\n" ++
            "    var bw_uninit = BufWriter.over_uninit(sw_uninit.as_writer(), &out raw_wr);\n" ++
            "    bw_uninit.write_all(b\"ok\") catch unreachable;\n" ++
            "    bw_uninit.close() catch unreachable;\n" ++
            "    let bwu_ok: i32 = if sw_uninit.written() == \"ok\".as_bytes() => 20 else 0;\n\n" ++
            "    var dst_bytes: [u8; 256] = [0_u8; 256];\n" ++
            "    var slice_wr = SliceWriter.new(&mut dst_bytes);\n" ++
            "    var buf_wr = BufWriter.new(slice_wr.as_writer());\n" ++
            "    buf_wr.print(f\"err={IoError.from_kind(.NotFound):?}\") catch unreachable;\n" ++
            "    buf_wr.close() catch unreachable;\n" ++
            "    let dbg_str = String.fmt(f\"kind={IoErrorKind.PermissionDenied:?}\");\n" ++
            "    let written_bytes: &[u8] = slice_wr.written();\n" ++
            "    let fmt_ok: i32 = if written_bytes.len() >= 13_usize and\n" ++
            "        written_bytes[0..13] == \"err=IoError {\".as_bytes() and\n" ++
            "        dbg_str.as_str().starts_with(\"kind=\")\n" ++
            "    {\n" ++
            "        40\n" ++
            "    } else {\n" ++
            "        0\n" ++
            "    };\n" ++
            "    ob_len + br_ok + bwu_ok + fmt_ok\n" ++
            "}\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        db.setSastStrict(true);
        const std_fids = try loadCoreAndCxStdlibIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, wave3a_io_src, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("wave3a_io_oracle", &sink);
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

        var report = try corex.runFourTierDiffOracleOnDb(
            allocator,
            &db,
            app_fid,
            .{ .io = io, .extra_file_ids = &std_fids },
        );
        defer report.deinit(allocator);
        if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
        try std.testing.expect(report.is_all_matching);
        try std.testing.expect(!report.outcomes[0].has_trapped);
        try std.testing.expectEqual(@as(i64, 72), report.outcomes[0].return_scalar_i64);
    }

    // [3] Negative soundness: `BufWriter.new(sw.as_writer())` MUST still emit `E0306` when `sw` dies in an inner block:
    {
        const neg_bw_escape_src =
            "use cx.io.{BufWriter, SliceWriter};\n" ++
            "pub fn bad_bw_escape() {\n" ++
            "    var dst_bytes: [u8; 32] = [0_u8; 32];\n" ++
            "    var bw: BufWriter;\n" ++
            "    {\n" ++
            "        var sw = SliceWriter.new(&mut dst_bytes);\n" ++
            "        bw = BufWriter.new(sw.as_writer());\n" ++
            "    }\n" ++
            "    bw.close() catch unreachable;\n" ++
            "}\n";
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        const std_fids = try loadCoreAndCxStdlibIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, neg_bw_escape_src, .low);

        var escape_sink = DiagnosticSink.init(allocator);
        defer escape_sink.deinit();
        try std.testing.expectError(
            error.FrontendErrors,
            db.compileModuleArtifact(
                app_fid,
                .{ .tier_a_c99 = .{ .target = TargetSpec.host(), .is_release_mode = false, .has_line_directives = false } },
                .{ .artifact_kind = .source_text, .extra_file_ids = &std_fids, .diagnostic_sink = &escape_sink },
            ),
        );
        const proj_sink = try db.projectFileDiagnostics(app_fid);
        try std.testing.expect(
            sinkHasCode(&escape_sink, .e0306_region_escape_violation) or
                sinkHasCode(proj_sink, .e0306_region_escape_violation),
        );
    }

    // [4] Negative soundness: monomorphized `OutBuf.over_uninit(&out raw_buf)` MUST still emit `E0303`
    //     when `raw_buf[0]` is read directly after `out_buf`'s borrow ends:
    {
        const neg_uninit_read_src =
            "use cx.io.OutBuf;\n" ++
            "pub fn bad_raw_read_after_over_uninit() -> u8 {\n" ++
            "    var raw_buf: [u8; 8];\n" ++
            "    var out_buf = OutBuf.over_uninit(&out raw_buf);\n" ++
            "    let _wrote = out_buf.append(b\"hi\");\n" ++
            "    raw_buf[0]\n" ++
            "}\n";
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        _ = try loadCoreAndCxStdlibIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, neg_uninit_read_src, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        try std.testing.expect(sinkHasCode(&sink, .e0303_uninitialized_memory_read));
    }
}

test "test_std02_wave3a_union_bounds_path_as_bytes_nested_derive_eq_struct_variant_and_unit_call" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] 4-Tier `diff_oracle` on `[P: str | Path]` -> `Path.new(path)` (`[S: str | &[u8] | Path]`) + `.as_bytes()`,
    //     `@derive(Equatable)` on nested payload enum, qualified struct-variant literals, and stack array bounds proof:
    {
        const wave3a_path_src =
            "use cx.path.{Path, PathBuf, PathPrefix};\n\n" ++
            "@derive(Copy, Clone, Equatable, Debug)\n" ++
            "enum InnerKind {\n" ++
            "    Code(i32),\n" ++
            "    Named { tag: u8, len: u16 },\n" ++
            "}\n\n" ++
            "@derive(Copy, Clone, Equatable, Debug)\n" ++
            "enum OuterEvent {\n" ++
            "    Wrapped(InnerKind),\n" ++
            "    Empty,\n" ++
            "}\n\n" ++
            "fn measure_via_path_new[P: str | Path](input: P) -> usize {\n" ++
            "    Path.new(input).as_bytes().len()\n" ++
            "}\n\n" ++
            "@no_panic\n" ++
            "pub fn read_stack_byte_checked(idx: usize) -> u8 {\n" ++
            "    let table: [u8; 4] = [11_u8, 22_u8, 33_u8, 44_u8];\n" ++
            "    if idx < table.len() {\n" ++
            "        return table[idx];\n" ++
            "    }\n" ++
            "    0_u8\n" ++
            "}\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    let len_str = measure_via_path_new(\"alpha/beta\") as i32;\n" ++
            "    let existing_path = Path.new(b\"gamma\");\n" ++
            "    let len_path = measure_via_path_new(existing_path) as i32;\n" ++
            "    let owned_pb = PathBuf.from(existing_path);\n" ++
            "    let pb_ok: i32 = if owned_pb.as_bytes() == \"gamma\".as_bytes() => 10 else 0;\n\n" ++
            "    let ev_a = OuterEvent.Wrapped(InnerKind.Named { len: 9_u16, tag: 3_u8 });\n" ++
            "    let ev_b = OuterEvent.Wrapped(.Named { tag: 3_u8, len: 9_u16 });\n" ++
            "    let ev_c = OuterEvent.Wrapped(InnerKind.Code(7));\n" ++
            "    let eq_ok: i32 = if ev_a == ev_b and ev_a != ev_c => 20 else 0;\n\n" ++
            "    let pfx = PathPrefix.VerbatimUnc { share: \"shr\".as_bytes(), server: \"srv\".as_bytes() };\n" ++
            "    let pfx_ok: i32 = if (pfx is .VerbatimUnc { server, share }) {\n" ++
            "        if server == \"srv\".as_bytes() and share == \"shr\".as_bytes() => 30 else 0\n" ++
            "    } else {\n" ++
            "        0\n" ++
            "    };\n\n" ++
            "    let arr_byte = read_stack_byte_checked(2_usize) as i32;\n" ++
            "    len_str + len_path + pb_ok + eq_ok + pfx_ok + arr_byte\n" ++
            "}\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        db.setSastStrict(true);
        const std_fids = try loadCoreAndCxStdlibIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, wave3a_path_src, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("wave3a_path_oracle", &sink);
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

        var report = try corex.runFourTierDiffOracleOnDb(
            allocator,
            &db,
            app_fid,
            .{ .io = io, .extra_file_ids = &std_fids },
        );
        defer report.deinit(allocator);
        if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
        try std.testing.expect(report.is_all_matching);
        try std.testing.expect(!report.outcomes[0].has_trapped);
        // 10 + 5 + 10 + 20 + 30 + 33 = 108
        try std.testing.expectEqual(@as(i64, 108), report.outcomes[0].return_scalar_i64);
    }

    // [2] Negative compile-fail: calling a `unit`-typed expression emits `.e0401_type_mismatch`:
    {
        const bad_unit_call_src =
            "fn noop() {}\n" ++
            "pub fn bad_call() {\n" ++
            "    let u_val: unit = noop();\n" ++
            "    u_val();\n" ++
            "}\n";
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        const fid = FileId.fromInt(0);
        _ = try db.setInput(fid, bad_unit_call_src, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, fid, &sink);
        try std.testing.expect(sinkHasCode(&sink, .e0401_type_mismatch));
    }
}

test "test_std02_wave3b_win32_startupinfo_abi_stdio_tls_disjointness_alphabetical_mods_cfg_skip_and_derive_debug" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Win32 `Win32StartupInfoW` (`104 B`) & `Win32StartupInfoExW` (`112 B`) ABI layout on `x86_64-windows-msvc`
    //     plus `StdioTlsHeader` `<= 24 B` (`224..248`, 100% disjoint from `time.cx` `248..256`):
    {
        const win_abi_src =
            "use core.sys.windows.{Win32StartupInfoExW, Win32StartupInfoW};\n\n" ++
            "pub const STARTUPINFO_W_SIZE: usize = @size_of[Win32StartupInfoW]();\n" ++
            "pub const STARTUPINFO_EX_W_SIZE: usize = @size_of[Win32StartupInfoExW]();\n\n" ++
            "pub fn verify_win32_startupinfo_sizes() -> usize {\n" ++
            "    if @size_of[Win32StartupInfoW]() == 104_usize and\n" ++
            "        @size_of[Win32StartupInfoExW]() == 112_usize\n" ++
            "    {\n" ++
            "        return 216_usize;\n" ++
            "    }\n" ++
            "    0_usize\n" ++
            "}\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.X86_64_WINDOWS);
        try db.setInternalCore(true);
        const std_fids = try loadCoreAndCxStdlibIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, win_abi_src, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("win32_startupinfo_abi", &sink);
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

        const win_sys_fid = std_fids[10];
        _ = try db.resolveSignatures(win_sys_fid);
        const win_mod_scope = db.symbol_table.file_module_scopes.get(win_sys_fid.asInt()).?;
        const si_sym = db.symbol_table.lookupInScopeDirect(
            win_mod_scope,
            try db.interner.intern("Win32StartupInfoW"),
            corex.symbol_resolver.NamespaceMask.TYPE_ONLY,
        );
        const si_ex_sym = db.symbol_table.lookupInScopeDirect(
            win_mod_scope,
            try db.interner.intern("Win32StartupInfoExW"),
            corex.symbol_resolver.NamespaceMask.TYPE_ONLY,
        );
        const si_ty = db.symbol_table.getSymbol(si_sym).type_id;
        const si_ex_ty = db.symbol_table.getSymbol(si_ex_sym).type_id;

        var layout_res = TypeLayoutResolver.init(allocator, &db.type_pool, &db.symbol_table, TargetSpec.X86_64_WINDOWS);
        defer layout_res.deinit();
        const si_layout = try layout_res.resolveType(si_ty);
        const si_ex_layout = try layout_res.resolveType(si_ex_ty);
        try std.testing.expectEqual(@as(u64, 104), si_layout.size_bytes);
        try std.testing.expectEqual(@as(u64, 112), si_ex_layout.size_bytes);

        const win_target_layout = TargetSpec.X86_64_WINDOWS.asTargetLayout();
        // Verify exact Win64 `STARTUPINFOW` offsets matching `mir_vm_sys_shim.zig`:
        // `flags` (ordinal 11) == 60, `std_input` (ordinal 15) == 80, `std_output` (16) == 88, `std_error` (17) == 96,
        // and `Win32StartupInfoExW.attribute_list` (ordinal 1) == 104:
        try std.testing.expectEqual(
            @as(?u64, 60),
            corex.type_system.computeStructFieldOffset(&db.type_pool, &db.symbol_table, si_ty, 11, win_target_layout),
        );
        try std.testing.expectEqual(
            @as(?u64, 80),
            corex.type_system.computeStructFieldOffset(&db.type_pool, &db.symbol_table, si_ty, 15, win_target_layout),
        );
        try std.testing.expectEqual(
            @as(?u64, 88),
            corex.type_system.computeStructFieldOffset(&db.type_pool, &db.symbol_table, si_ty, 16, win_target_layout),
        );
        try std.testing.expectEqual(
            @as(?u64, 96),
            corex.type_system.computeStructFieldOffset(&db.type_pool, &db.symbol_table, si_ty, 17, win_target_layout),
        );
        try std.testing.expectEqual(
            @as(?u64, 104),
            corex.type_system.computeStructFieldOffset(&db.type_pool, &db.symbol_table, si_ex_ty, 1, win_target_layout),
        );

        // Verify `stdlib/cx/io.cx` `StdioTlsHeader` occupies `<= 24 B` (`224 + size <= 248`, disjoint from `248..256`):
        const io_fid = std_fids[CORE_MODULE_PATHS.len + 4];
        _ = try db.resolveSignatures(io_fid);
        const io_mod_scope = db.symbol_table.file_module_scopes.get(io_fid.asInt()).?;
        const tls_hdr_sym = db.symbol_table.lookupInScopeDirect(
            io_mod_scope,
            try db.interner.intern("StdioTlsHeader"),
            corex.symbol_resolver.NamespaceMask.TYPE_ONLY,
        );
        const tls_hdr_ty = db.symbol_table.getSymbol(tls_hdr_sym).type_id;
        const tls_hdr_layout = try layout_res.resolveType(tls_hdr_ty);
        try std.testing.expectEqual(@as(u64, 24), tls_hdr_layout.size_bytes);
        try std.testing.expect(224 + tls_hdr_layout.size_bytes <= 248);
    }

    // [2] Alphabetical `pub mod {env, fs, io, path, process, time};` cross-module `TypeId` identity
    //     (`SystemTime?`, `IoError`, `usize!IoError`, `OutBuf`, `ReaderVTable`, `PathBuf?`) + real `fs.cx` before `io`/`path`/`time`:
    {
        const root_barrel_src =
            "pub mod env;\n" ++
            "pub mod fs;\n" ++
            "pub mod io;\n" ++
            "pub mod path;\n" ++
            "pub mod process;\n" ++
            "pub mod time;\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    let env_opt = env.cached_dir();\n" ++
            "    let mtime_opt = fs.stat_mtime(true);\n" ++
            "    let proc_n = process.run_reader() catch return -1;\n" ++
            "    let has_dir: i32 = if env_opt is .Some(_) => 10 else 0;\n" ++
            "    let has_ts: i32 = if mtime_opt is .Some(ts) => ts.secs as i32 else 0;\n" ++
            "    has_dir + has_ts + (proc_n as i32)\n" ++
            "}\n";
        const env_sub_src =
            "use pkg.fs.FsError;\n" ++
            "use pkg.path.PathBuf;\n\n" ++
            "type OptPathBuf = PathBuf?;\n\n" ++
            "pub fn cached_dir() -> OptPathBuf {\n" ++
            "    .Some(PathBuf.new(3_usize))\n" ++
            "}\n\n" ++
            "pub fn probe_env_err(err: FsError) -> u64 = err.code_word();\n";
        const fs_sub_src =
            "use pkg.io.{IoError, OutBuf, ReaderVTable};\n" ++
            "use pkg.path.PathBuf;\n" ++
            "use pkg.time.SystemTime;\n\n" ++
            "@derive(Copy, Equatable)\n" ++
            "pub struct FsError {\n" ++
            "    bits: u64,\n" ++
            "}\n\n" ++
            "impl FsError {\n" ++
            "    pub fn code_word(self) -> u64 = self.bits;\n" ++
            "}\n\n" ++
            "fn fs_read_cb(ctx: *mut opaque, out: &mut OutBuf) -> usize!IoError {\n" ++
            "    _ = ctx;\n" ++
            "    out.filled += 7_usize;\n" ++
            "    .Ok(7_usize)\n" ++
            "}\n\n" ++
            "pub fn file_vtable() -> ReaderVTable {\n" ++
            "    ReaderVTable {\n" ++
            "        read_out: fs_read_cb,\n" ++
            "    }\n" ++
            "}\n\n" ++
            "pub fn stat_mtime(present: bool) -> SystemTime? {\n" ++
            "    if present {\n" ++
            "        return .Some(pkg.time.epoch_plus(25_i64));\n" ++
            "    }\n" ++
            "    .None\n" ++
            "}\n\n" ++
            "pub fn unwrap_dir(opt_p: own PathBuf?) -> usize {\n" ++
            "    if opt_p is .Some(pb) {\n" ++
            "        return pb.len;\n" ++
            "    }\n" ++
            "    0_usize\n" ++
            "}\n";
        const io_sub_src =
            "@derive(Copy, Equatable)\n" ++
            "pub struct IoError {\n" ++
            "    pub raw: u64,\n" ++
            "}\n\n" ++
            "pub struct OutBuf {\n" ++
            "    pub filled: usize,\n" ++
            "}\n\n" ++
            "@derive(Copy)\n" ++
            "pub struct ReaderVTable {\n" ++
            "    pub read_out: fn(*mut opaque, &mut OutBuf) -> usize!IoError,\n" ++
            "}\n";
        const path_sub_src =
            "pub trait Drop {\n" ++
            "    fn drop(&mut self);\n" ++
            "}\n\n" ++
            "pub struct PathBuf {\n" ++
            "    pub len: usize,\n" ++
            "}\n\n" ++
            "impl Drop for PathBuf {\n" ++
            "    pub fn drop(&mut self) {\n" ++
            "        self.len = 0_usize;\n" ++
            "    }\n" ++
            "}\n\n" ++
            "impl PathBuf {\n" ++
            "    pub fn new(len: usize) -> PathBuf = PathBuf { len };\n" ++
            "}\n";
        const process_sub_src =
            "use pkg.env;\n" ++
            "use pkg.fs;\n" ++
            "use pkg.io.{IoError, OutBuf, ReaderVTable};\n\n" ++
            "pub fn run_reader() -> usize!IoError {\n" ++
            "    let vt: ReaderVTable = fs.file_vtable();\n" ++
            "    var out = OutBuf { filled: 0_usize };\n" ++
            "    let read_n: usize = (vt.read_out)(@default_init[*mut opaque](), &mut out)?;\n" ++
            "    let dir_len: usize = fs.unwrap_dir(env.cached_dir());\n" ++
            "    .Ok(read_n + dir_len)\n" ++
            "}\n";
        const time_sub_src =
            "@derive(Copy, Equatable)\n" ++
            "pub struct SystemTime {\n" ++
            "    pub secs: i64,\n" ++
            "    pub subsec_nanos: u32,\n" ++
            "}\n\n" ++
            "pub fn epoch_plus(secs: i64) -> SystemTime = SystemTime { secs, subsec_nanos: 0_u32 };\n\n" ++
            "pub fn maybe_now(flag: bool) -> SystemTime? {\n" ++
            "    if flag => .Some(SystemTime { secs: 1_i64, subsec_nanos: 0_u32 }) else .None\n" ++
            "}\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        db.setSastStrict(true);

        const root_fid = FileId.fromInt(100);
        const sub_fids = [6]FileId{
            FileId.fromInt(101),
            FileId.fromInt(102),
            FileId.fromInt(103),
            FileId.fromInt(104),
            FileId.fromInt(105),
            FileId.fromInt(106),
        };
        const sub_names = [6][]const u8{ "env", "fs", "io", "path", "process", "time" };
        const sub_srcs = [6][]const u8{
            env_sub_src,
            fs_sub_src,
            io_sub_src,
            path_sub_src,
            process_sub_src,
            time_sub_src,
        };
        _ = try db.setInput(root_fid, root_barrel_src, .low);
        for (sub_fids, sub_names, sub_srcs) |sfid, sname, ssrc| {
            _ = try db.setInput(sfid, ssrc, .low);
            try db.bindExternalModule(root_fid, sname, sfid);
        }

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, root_fid, &sink);
        for (sub_fids) |sfid| {
            try collectAllDiagnostics(&db, sfid, &sink);
        }
        if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("alphabetical_barrel", &sink);
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

        // Assert exact `TypeId` identity for `SystemTime?` across `fs` (resolved 2nd) and `time` (resolved 6th):
        const fs_scope = db.symbol_table.file_module_scopes.get(sub_fids[1].asInt()).?;
        const time_scope = db.symbol_table.file_module_scopes.get(sub_fids[5].asInt()).?;
        const stat_fn_sym = db.symbol_table.lookupInScopeDirect(
            fs_scope,
            try db.interner.intern("stat_mtime"),
            corex.symbol_resolver.NamespaceMask.VALUE_ONLY,
        );
        const maybe_fn_sym = db.symbol_table.lookupInScopeDirect(
            time_scope,
            try db.interner.intern("maybe_now"),
            corex.symbol_resolver.NamespaceMask.VALUE_ONLY,
        );
        const stat_ret_ty = db.type_pool.getFnSignatureView(db.symbol_table.getSymbol(stat_fn_sym).type_id).?.ret_ty;
        const maybe_ret_ty = db.type_pool.getFnSignatureView(db.symbol_table.getSymbol(maybe_fn_sym).type_id).?.ret_ty;
        try std.testing.expectEqual(stat_ret_ty, maybe_ret_ty);

        var report = try corex.runFourTierDiffOracleOnDb(
            allocator,
            &db,
            root_fid,
            .{ .io = io, .extra_file_ids = &sub_fids },
        );
        defer report.deinit(allocator);
        if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
        try std.testing.expect(report.is_all_matching);
        try std.testing.expect(!report.outcomes[0].has_trapped);
        // 10 + 25 + (7 + 3) = 45
        try std.testing.expectEqual(@as(i64, 45), report.outcomes[0].return_scalar_i64);

        // Also mount all 10 real `stdlib/cx/*.cx` submodules in strictly alphabetical order:
        const alpha_cx_paths = [_][]const u8{
            "stdlib/cx/col.cx",
            "stdlib/cx/env.cx",
            "stdlib/cx/fs.cx",
            "stdlib/cx/io.cx",
            "stdlib/cx/math.cx",
            "stdlib/cx/mem.cx",
            "stdlib/cx/path.cx",
            "stdlib/cx/process.cx",
            "stdlib/cx/str.cx",
            "stdlib/cx/time.cx",
        };
        const alpha_cx_names = [_][]const u8{
            "col",
            "env",
            "fs",
            "io",
            "math",
            "mem",
            "path",
            "process",
            "str",
            "time",
        };
        const raw_mod_bytes = try std.Io.Dir.cwd().readFileAlloc(io, "stdlib/cx/mod.cx", allocator, .limited(1024 * 1024));
        defer allocator.free(raw_mod_bytes);
        const norm_mod_bytes = try normalizeLfAlloc(allocator, raw_mod_bytes);
        defer allocator.free(norm_mod_bytes);

        var real_db = try CompilerDb.init(allocator);
        defer real_db.deinit();
        real_db.setTargetSpec(TargetSpec.host());
        real_db.setSastStrict(true);
        for (CORE_MODULE_PATHS, 0..) |mod_path, idx| {
            const raw_b = try std.Io.Dir.cwd().readFileAlloc(io, mod_path, allocator, .limited(2 * 1024 * 1024));
            defer allocator.free(raw_b);
            const norm_b = try normalizeLfAlloc(allocator, raw_b);
            defer allocator.free(norm_b);
            const fid = FileId.fromInt(1 + @as(u32, @intCast(idx)));
            try real_db.setFilePackageId(fid, .std_core);
            try real_db.setFilePath(fid, mod_path);
            _ = try real_db.setInput(fid, norm_b, .high);
        }
        const core_root = FileId.fromInt(1);
        try real_db.registerRootModule("core", core_root);
        try real_db.bindExternalModule(core_root, "primitives", FileId.fromInt(2));
        try real_db.bindExternalModule(core_root, "mem", FileId.fromInt(3));
        try real_db.bindExternalModule(core_root, "atomic", FileId.fromInt(4));
        try real_db.bindExternalModule(core_root, "simd", FileId.fromInt(5));
        try real_db.bindExternalModule(core_root, "panic", FileId.fromInt(6));
        try real_db.bindExternalModule(core_root, "runtime", FileId.fromInt(7));
        try real_db.bindExternalModule(core_root, "sys", FileId.fromInt(8));
        try real_db.bindExternalModule(core_root, "ffi", FileId.fromInt(13));
        try real_db.bindExternalModule(core_root, "async", FileId.fromInt(14));
        try real_db.bindExternalModule(FileId.fromInt(8), "linux", FileId.fromInt(9));
        try real_db.bindExternalModule(FileId.fromInt(8), "macos", FileId.fromInt(10));
        try real_db.bindExternalModule(FileId.fromInt(8), "windows", FileId.fromInt(11));
        try real_db.bindExternalModule(FileId.fromInt(8), "wasi", FileId.fromInt(12));
        try real_db.markCoreKernelSubtree(core_root);

        const cx_root_fid = FileId.fromInt(20);
        try real_db.setFilePackageId(cx_root_fid, .std_core);
        try real_db.setFilePath(cx_root_fid, "stdlib/cx/mod.cx");
        _ = try real_db.setInput(cx_root_fid, norm_mod_bytes, .high);
        try real_db.registerRootModule("cx", cx_root_fid);
        try real_db.registerCxStdlibPreludeRoot(cx_root_fid);
        for (alpha_cx_paths, alpha_cx_names, 0..) |cx_path, cx_name, idx| {
            const raw_b = try std.Io.Dir.cwd().readFileAlloc(io, cx_path, allocator, .limited(4 * 1024 * 1024));
            defer allocator.free(raw_b);
            const norm_b = try normalizeLfAlloc(allocator, raw_b);
            defer allocator.free(norm_b);
            const sub_fid = FileId.fromInt(21 + @as(u32, @intCast(idx)));
            try real_db.setFilePackageId(sub_fid, .std_core);
            try real_db.setFilePath(sub_fid, cx_path);
            _ = try real_db.setInput(sub_fid, norm_b, .high);
            try real_db.bindExternalModule(cx_root_fid, cx_name, sub_fid);
        }
        try std.testing.expectEqual(@as(u32, 0), (try real_db.resolveSignatures(cx_root_fid)).error_count);
        const real_fs_fid = FileId.fromInt(23);
        var fs_sink = DiagnosticSink.init(allocator);
        defer fs_sink.deinit();
        try collectAllDiagnostics(&real_db, real_fs_fid, &fs_sink);
        if (fs_sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("real_alpha_fs", &fs_sink);
        try std.testing.expectEqual(@as(usize, 0), fs_sink.diagnostics.items.len);
    }

    // [3] `@cfg(false)` and target-gated top-level `fn` / `const` bodies skipped in `CompilerDb.typecheckBody`:
    {
        const cfg_body_src =
            "@cfg(false)\n" ++
            "const DISABLED_BAD_CONST: i32 = \"not_an_i32\";\n\n" ++
            "@cfg(false)\n" ++
            "pub fn disabled_bad_fn() -> i32 {\n" ++
            "    let wrong_ty: i32 = \"still_disabled\";\n" ++
            "    wrong_ty\n" ++
            "}\n\n" ++
            "@cfg(target.os == \"windows\")\n" ++
            "pub fn platform_code() -> i32 = 10;\n\n" ++
            "@cfg(target.os == \"linux\")\n" ++
            "pub fn platform_code() -> i32 = 20;\n\n" ++
            "struct CfgMethodHost {\n" ++
            "    base: i32,\n" ++
            "}\n\n" ++
            "impl CfgMethodHost {\n" ++
            "    @cfg(target.os == \"macos\")\n" ++
            "    pub fn map_code(macos_val: i32) -> i32 = macos_val + 1;\n\n" ++
            "    @cfg(not (target.os == \"macos\"))\n" ++
            "    pub fn map_code(posix_val: i32) -> i32 = posix_val + 2;\n\n" ++
            "    pub fn trailing_method(win_val: u32) -> u32 = win_val + 3_u32;\n" ++
            "}\n\n" ++
            "pub fn call_platform() -> i32 = platform_code() + CfgMethodHost.map_code(5) + (CfgMethodHost.trailing_method(1_u32) as i32);\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        const fid = FileId.fromInt(0);
        _ = try db.setInput(fid, cfg_body_src, .low);

        db.setTargetSpec(TargetSpec.X86_64_LINUX);
        var linux_sink = DiagnosticSink.init(allocator);
        defer linux_sink.deinit();
        try collectAllDiagnostics(&db, fid, &linux_sink);
        if (linux_sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("cfg_skip_linux", &linux_sink);
        try std.testing.expectEqual(@as(usize, 0), linux_sink.diagnostics.items.len);

        db.setTargetSpec(TargetSpec.X86_64_WINDOWS);
        var win_sink = DiagnosticSink.init(allocator);
        defer win_sink.deinit();
        try collectAllDiagnostics(&db, fid, &win_sink);
        if (win_sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("cfg_skip_win", &win_sink);
        try std.testing.expectEqual(@as(usize, 0), win_sink.diagnostics.items.len);

        // Negative check: `@cfg(true)` top-level `fn` with a body type mismatch MUST still emit `E0401`:
        const cfg_enabled_bad_src =
            "@cfg(true)\n" ++
            "pub fn enabled_bad_fn() -> i32 {\n" ++
            "    \"type_mismatch\"\n" ++
            "}\n";
        var neg_db = try CompilerDb.init(allocator);
        defer neg_db.deinit();
        const neg_fid = FileId.fromInt(0);
        _ = try neg_db.setInput(neg_fid, cfg_enabled_bad_src, .low);
        var neg_sink = DiagnosticSink.init(allocator);
        defer neg_sink.deinit();
        try collectAllDiagnostics(&neg_db, neg_fid, &neg_sink);
        try std.testing.expect(sinkHasCode(&neg_sink, .e0401_type_mismatch));
    }

    // [4] `@derive(Debug)` enum/struct formatting inside `f"{val:?}"` (`@fmt_write`) across all 4 `diff_oracle` tiers
    //     while preserving custom hand-written `impl Debug` overrides:
    {
        const derive_dbg_src =
            "@derive(Copy, Equatable, Debug)\n" ++
            "enum Mode {\n" ++
            "    Fast,\n" ++
            "    Code(i32),\n" ++
            "}\n\n" ++
            "@derive(Copy, Equatable, Debug)\n" ++
            "struct PairInfo {\n" ++
            "    count: u32,\n" ++
            "    mode: Mode,\n" ++
            "}\n\n" ++
            "@derive(Copy)\n" ++
            "struct CustomTag {\n" ++
            "    id: u32,\n" ++
            "}\n\n" ++
            "impl Debug for CustomTag {\n" ++
            "    pub fn fmt_debug(&self, out: &mut cx.FmtWriter, spec: cx.FmtSpec) -> unit!cx.FmtError {\n" ++
            "        _ = spec;\n" ++
            "        out.write_str(\"tag#\")?;\n" ++
            "        @fmt_write(out, f\"{self.id}\")\n" ++
            "    }\n" ++
            "}\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    let unit_txt = String.fmt(f\"{Mode.Fast:?}\");\n" ++
            "    let payload_txt = String.fmt(f\"{Mode.Code(42):?}\");\n" ++
            "    let pair_val = PairInfo { count: 7_u32, mode: .Fast };\n" ++
            "    let struct_txt = String.fmt(f\"{pair_val:?}\");\n" ++
            "    let custom_txt = String.fmt(f\"{CustomTag { id: 9_u32 }:?}\");\n" ++
            "    let s1: i32 = if unit_txt.as_str() == \"Fast\" => 1 else 0;\n" ++
            "    let s2: i32 = if payload_txt.as_str() == \"Code(42)\" => 10 else 0;\n" ++
            "    let s3: i32 = if struct_txt.as_str() == \"PairInfo { count: 7, mode: Fast }\" => 100 else 0;\n" ++
            "    let s4: i32 = if custom_txt.as_str() == \"tag#9\" => 1000 else 0;\n" ++
            "    s1 + s2 + s3 + s4\n" ++
            "}\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        db.setSastStrict(true);
        const std_fids = try loadCoreAndCxStdlibIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, derive_dbg_src, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("derive_debug_4tier", &sink);
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

        var report = try corex.runFourTierDiffOracleOnDb(
            allocator,
            &db,
            app_fid,
            .{ .io = io, .extra_file_ids = &std_fids },
        );
        defer report.deinit(allocator);
        if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
        try std.testing.expect(report.is_all_matching);
        try std.testing.expect(!report.outcomes[0].has_trapped);
        try std.testing.expectEqual(@as(i64, 1111), report.outcomes[0].return_scalar_i64);
    }
}

test "test_std02_step4_red_team_soundness_and_trap_parity_regressions" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] `&out` exclusive NLL loan soundness: concurrent `&raw` borrow while `OutBuf.over_uninit(&out raw)` is live MUST emit `E0305`:
    {
        const neg_out_alias_src =
            "use cx.io.OutBuf;\n" ++
            "pub fn bad_out_shared_alias() -> usize {\n" ++
            "    var raw: [u8; 64] = [0_u8; 64];\n" ++
            "    var out_buf = OutBuf.over_uninit(&out raw);\n" ++
            "    let view: &[u8] = &raw;\n" ++
            "    _ = out_buf.append(b\"cx\");\n" ++
            "    view.len()\n" ++
            "}\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        db.setSastStrict(true);
        const std_fids = try loadCoreAndCxStdlibIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, neg_out_alias_src, .low);

        var alias_sink = DiagnosticSink.init(allocator);
        defer alias_sink.deinit();
        try std.testing.expectError(
            error.FrontendErrors,
            db.compileModuleArtifact(
                app_fid,
                .{ .tier_a_c99 = .{ .target = TargetSpec.host(), .is_release_mode = false, .has_line_directives = false } },
                .{ .artifact_kind = .source_text, .extra_file_ids = &std_fids, .diagnostic_sink = &alias_sink },
            ),
        );
        const proj_sink = try db.projectFileDiagnostics(app_fid);
        try std.testing.expect(
            sinkHasCode(&alias_sink, .e0305_exclusivity_violation) or
                sinkHasCode(proj_sink, .e0305_exclusivity_violation),
        );
    }

    // [2] Function-pointer reification of `over_uninit` (`OutBuf.over_uninit[64]` / `OutBuf.over_uninit`) MUST be rejected at compile time:
    {
        const neg_over_uninit_fnptr_src =
            "use cx.io.OutBuf;\n" ++
            "pub fn bad_reify_over_uninit() -> usize {\n" ++
            "    let ctor: fn(&out [u8; 64]) -> OutBuf = OutBuf.over_uninit[64];\n" ++
            "    var raw: [u8; 64];\n" ++
            "    var out_buf = ctor(&out raw);\n" ++
            "    out_buf.capacity()\n" ++
            "}\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        const std_fids = try loadCoreAndCxStdlibIntoDb(allocator, io, &db, 1);
        _ = std_fids;
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, neg_over_uninit_fnptr_src, .low);

        var fnptr_sink = DiagnosticSink.init(allocator);
        defer fnptr_sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &fnptr_sink);
        try std.testing.expect(sinkHasCode(&fnptr_sink, .e0422_out_param_contract_violation));
    }

    // [3] 4-tier `diff_oracle` + standalone `-ofmt=c` trap parity on `unreachable` (`has_trapped == true`, `exit_code == 101`):
    {
        const trap_parity_src =
            "fn fail_step() -> i32!i32 {\n" ++
            "    .Err(9)\n" ++
            "}\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    fail_step() catch unreachable\n" ++
            "}\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        const core_fids = try loadCoreTreeIntoDb(allocator, io, &db, 1);
        for (core_fids) |cfid| try db.setFilePackageId(cfid, .std_core);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, trap_parity_src, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("trap_parity_4tier", &sink);
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

        var report = try corex.runFourTierDiffOracleOnDb(
            allocator,
            &db,
            app_fid,
            .{ .io = io, .extra_file_ids = &core_fids },
        );
        defer report.deinit(allocator);
        if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
        try std.testing.expect(report.is_all_matching);
        for (report.outcomes) |tier_outcome| {
            try std.testing.expect(tier_outcome.has_trapped);
            try std.testing.expectEqual(@as(u8, 101), tier_outcome.exit_code);
        }

        // Verify standalone `-ofmt=c` executable (without `COREX_ORACLE_TRACE_FILE`) also exits with `101`:
        const c_exe_path = if (builtin.os.tag == .windows)
            ".zig-cache/test_std02_step4_trap_c99.exe"
        else
            ".zig-cache/test_std02_step4_trap_c99";
        defer std.Io.Dir.cwd().deleteFile(io, c_exe_path) catch {};
        var c_art = try db.compileModuleArtifact(
            app_fid,
            .{ .tier_a_c99 = .{ .target = TargetSpec.host(), .is_release_mode = false, .has_line_directives = false } },
            .{ .artifact_kind = .executable, .output_path = c_exe_path, .extra_file_ids = &core_fids, .io = io },
        );
        defer c_art.deinit(allocator);
        const run_res = try std.process.run(allocator, io, .{ .argv = &.{c_exe_path} });
        defer allocator.free(run_res.stdout);
        defer allocator.free(run_res.stderr);
        try std.testing.expect(run_res.term == .exited);
        try std.testing.expectEqual(@as(u8, 101), run_res.term.exited);
    }

    // [4] `glibc 2.28` baseline: `core/sys/linux.cx` exposes `RTLD_DEFAULT` + `linux_dlsym` and never eagerly `@link`s `addchdir_np`:
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.X86_64_LINUX);
        db.setSastStrict(true);
        try db.setInternalCore(true);
        const core_fids = try loadCoreTreeIntoDb(allocator, io, &db, 1);
        for (core_fids) |cfid| try db.setFilePackageId(cfid, .std_core);

        const linux_probe_src =
            "use core.sys.linux.{PosixSpawnFileActions, RTLD_DEFAULT, linux_dlsym, linux_spawn_file_actions_addchdir_np};\n" ++
            "pub fn main() -> i32 {\n" ++
            "    var actions = PosixSpawnFileActions { opaque_words: [0_u64; 12] };\n" ++
            "    unsafe {\n" ++
            "        let missing_sym = linux_dlsym(RTLD_DEFAULT, (&b\"__cx_missing_sym__\\0\"[0]) as *u8);\n" ++
            "        if not missing_sym.is_null() {\n" ++
            "            return 1;\n" ++
            "        }\n" ++
            "        linux_spawn_file_actions_addchdir_np(&mut actions, (&b\".\\0\"[0]) as *u8)\n" ++
            "    }\n" ++
            "}\n";
        const app_fid = FileId.fromInt(0);
        try db.setFilePackageId(app_fid, .std_core);
        _ = try db.setInput(app_fid, linux_probe_src, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var c_art = try db.compileModuleArtifact(
            app_fid,
            .{ .tier_a_c99 = .{ .target = TargetSpec.X86_64_LINUX, .is_release_mode = false, .has_line_directives = false } },
            .{ .artifact_kind = .source_text, .extra_file_ids = &core_fids, .diagnostic_sink = &sink },
        );
        defer c_art.deinit(allocator);
        if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("linux_glibc228_dlsym", &sink);
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);
        try std.testing.expect(std.mem.indexOf(u8, c_art.emitted_text, "__asm__(\"dlsym\")") != null);
        try std.testing.expect(
            std.mem.indexOf(u8, c_art.emitted_text, "__asm__(\"posix_spawn_file_actions_addchdir_np\")") == null,
        );
    }

    // [5] 4-tier `diff_oracle` parity for `impl` associated `bit_field` constants, `refined_ty` `i128` casts,
    //     `@from_le_bytes` / `@from_be_bytes` on `&[u8]` slices, and single-arg `@ptr_read[T](ptr)`:
    {
        const cross_mod_seam_src =
            "use cx.fs.FilePermissions;\n" ++
            "use cx.time.Duration;\n\n" ++
            "type SubsecNano = u32 is 0..=999_999_999;\n\n" ++
            "fn widen_subsec(nanos: SubsecNano) -> i128 {\n" ++
            "    nanos as i128\n" ++
            "}\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    let perms = FilePermissions.DEFAULT_FILE;\n" ++
            "    let dur = Duration.from_nanos(2_500_000_000_u64);\n" ++
            "    let widened: i128 = widen_subsec(500_000_000_u32);\n" ++
            "    let raw_wire: [u8; 8] = [0x11_u8, 0x22_u8, 0x33_u8, 0x44_u8, 0x55_u8, 0x66_u8, 0x77_u8, 0x88_u8];\n" ++
            "    let wire_slice: &[u8] = &raw_wire;\n" ++
            "    let le_val = @from_le_bytes[u32](wire_slice);\n" ++
            "    let be_val = @from_be_bytes[u32](wire_slice);\n" ++
            "    let magic_slot = 0xCAFE_BABE_1234_5678_u64;\n" ++
            "    let magic_read = unsafe { @ptr_read[u64]((&magic_slot) as *u64) };\n" ++
            "    let p1: i32 = if perms.posix_mode == 0o644_u16 and not perms.readonly and not perms.executable => 1 else 0;\n" ++
            "    let p2: i32 = if dur.subsec_nanos() == 500_000_000_u32 and widened == 500_000_000_i128 => 10 else 0;\n" ++
            "    let p3: i32 = if le_val == 0x4433_2211_u32 and be_val == 0x1122_3344_u32 => 100 else 0;\n" ++
            "    let p4: i32 = if magic_read == 0xCAFE_BABE_1234_5678_u64 => 1000 else 0;\n" ++
            "    p1 + p2 + p3 + p4\n" ++
            "}\n";

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        db.setSastStrict(true);
        const std_fids = try loadCoreAndCxStdlibIntoDb(allocator, io, &db, 1);
        const app_fid = FileId.fromInt(0);
        _ = try db.setInput(app_fid, cross_mod_seam_src, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, app_fid, &sink);
        if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("cross_mod_seam_4tier", &sink);
        try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

        var report = try corex.runFourTierDiffOracleOnDb(
            allocator,
            &db,
            app_fid,
            .{ .io = io, .extra_file_ids = &std_fids },
        );
        defer report.deinit(allocator);
        if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
        try std.testing.expect(report.is_all_matching);
        try std.testing.expect(!report.outcomes[0].has_trapped);
        try std.testing.expectEqual(@as(i64, 1111), report.outcomes[0].return_scalar_i64);
    }
}

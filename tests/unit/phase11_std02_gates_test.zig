//! Phase 11.2a (`STD-02` §2 & §3.3) Seven-Gate Verification & Safety Suite
//!
//! Proves all seven mandatory `STD-02` architectural verification gates across all four execution
//! tiers (`Pre-Opt MirVm`, `Post-Opt MirVm`, `-ofmt=c`, and `LLVM`) plus `--release` native codegen:
//! - Gate 1: `cx.io` zero-copy streams, `OutBuf`, `BufReader`, `@linear BufWriter`, `Seek`, & `copy_stream`,
//! - Gate 2: `cx.path` `24 B` SSO `PathBuf`, cross-OS `PathFlavor`, DOS stems, & WTF-8/16 surrogates,
//! - Gate 3: `cx.time` monotonic/wall clocks, 128-bit 500-year tick scaling, & `sleep`,
//! - Gate 4: `cx.fs` thresholded `Mmap`, live `write_atomic`, `Dir.*_beneath`, `FileLock`, `FsWatcher`, & `FsDiagPathRing`,
//! - Gate 5: `cx.env` & `cx.process` zero-`shell32` PE imports, MSVCRT quoting, & `BatBadBut` defense,
//! - Gate 6: `SimReactor` virtual clock (`3,600 s` in `< 100 ms`), stdio capture, & seeded fault replay,
//! - Gate 7: Negative `compile_fail` safety matrix (`E0304`, `E0324`, `E0322`, `E0305`/`E0306`/`E0422`, `E0325`/`E0503`).
//!
//! All temporary native/filesystem artifacts live inside `.zig-cache/std02_gates_tmp_*` and clean up via `defer`.

const std = @import("std");
const builtin = @import("builtin");
const corex = @import("corex");

const FileId = corex.FileId;
const PackageId = corex.PackageId;
const Span = corex.Span;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const DiagnosticCode = corex.DiagnosticCode;
const TargetSpec = corex.TargetSpec;
const TypeLayoutResolver = corex.TypeLayoutResolver;
const mir_sast = corex.mir_sast;

// ---------------------------------------- TYPES ----------------------------------------

/// Mounted `FileId` handles for `core/**/*.cx`, `stdlib/cx/*.cx`, and optional `__std02_probe`.
const MountedStdBundle = struct {
    /// Fixed storage for up to `26` mounted standard-library `FileId`s.
    storage: [CORE_MODULE_PATHS.len + CX_STDLIB_PATHS.len + 1]FileId = undefined,
    /// Active count (`25` without probe, `26` with `__std02_probe`).
    count: usize = 0,
    /// `FileId` of `stdlib/cx/path.cx` inside `db`.
    path_fid: FileId = .none,
    /// Optional `FileId` of the mounted `cx.__std02_probe` submodule.
    probe_fid: FileId = .none,

    /// Returns the active slice of mounted `FileId`s for `extra_file_ids`.
    fn asSlice(self: *const MountedStdBundle) []const FileId {
        return self.storage[0..self.count];
    }
};

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

/// Monotonic atomic counter guaranteeing collision-free `.zig-cache/std02_gates_tmp_*` directories.
var next_tmp_seq: std.atomic.Value(u32) = .init(1);

// -------------------------------------- INTERNALS --------------------------------------

// --------------- CompilerDb Mounting & Helpers ----------------

/// Normalizes CRLF line endings in `raw_bytes` to LF so `CompilerDb` inputs stay OS-agnostic.
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

/// Mounts all 14 `core/**/*.cx` and 11 `stdlib/cx/*.cx` files (plus optional `cx.__std02_probe`) into `db`.
fn mountStdCoreAndCxIntoDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    db: *CompilerDb,
    base_file_id: u32,
    probe_src_opt: ?[]const u8,
) !MountedStdBundle {
    var bundle: MountedStdBundle = .{};
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
        bundle.storage[i] = fid;
        try db.setFilePackageId(fid, .std_core);
        try db.setFilePath(fid, mod_path);
        _ = try db.setInput(fid, norm_bytes, .high);
    }

    const core_root_fid = bundle.storage[0];
    try db.registerRootModule("core", core_root_fid);
    try db.bindExternalModule(core_root_fid, "primitives", bundle.storage[1]);
    try db.bindExternalModule(core_root_fid, "mem", bundle.storage[2]);
    try db.bindExternalModule(core_root_fid, "atomic", bundle.storage[3]);
    try db.bindExternalModule(core_root_fid, "simd", bundle.storage[4]);
    try db.bindExternalModule(core_root_fid, "panic", bundle.storage[5]);
    try db.bindExternalModule(core_root_fid, "runtime", bundle.storage[6]);
    try db.bindExternalModule(core_root_fid, "sys", bundle.storage[7]);
    try db.bindExternalModule(core_root_fid, "ffi", bundle.storage[12]);
    try db.bindExternalModule(core_root_fid, "async", bundle.storage[13]);

    const sys_mod_fid = bundle.storage[7];
    try db.bindExternalModule(sys_mod_fid, "linux", bundle.storage[8]);
    try db.bindExternalModule(sys_mod_fid, "macos", bundle.storage[9]);
    try db.bindExternalModule(sys_mod_fid, "windows", bundle.storage[10]);
    try db.bindExternalModule(sys_mod_fid, "wasi", bundle.storage[11]);
    try db.markCoreKernelSubtree(core_root_fid);

    for (CX_STDLIB_PATHS, 0..) |cx_path, i| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(
            io,
            cx_path,
            allocator,
            .limited(4 * 1024 * 1024),
        );
        defer allocator.free(raw_bytes);
        const norm_bytes = try normalizeLfAlloc(allocator, raw_bytes);
        defer allocator.free(norm_bytes);

        const slot_idx = CORE_MODULE_PATHS.len + i;
        const fid = FileId.fromInt(base_file_id + @as(u32, @intCast(slot_idx)));
        bundle.storage[slot_idx] = fid;
        try db.setFilePackageId(fid, .std_core);
        try db.setFilePath(fid, cx_path);

        if (i == 0 and probe_src_opt != null) {
            const augmented_mod = try std.fmt.allocPrint(
                allocator,
                "{s}\npub mod __std02_probe;\n",
                .{norm_bytes},
            );
            defer allocator.free(augmented_mod);
            _ = try db.setInput(fid, augmented_mod, .high);
        } else {
            _ = try db.setInput(fid, norm_bytes, .high);
        }
    }

    const cx_base = CORE_MODULE_PATHS.len;
    const cx_mod_fid = bundle.storage[cx_base];
    bundle.path_fid = bundle.storage[cx_base + 7];
    try db.registerRootModule("cx", cx_mod_fid);
    try db.registerCxStdlibPreludeRoot(cx_mod_fid);
    try db.bindExternalModule(cx_mod_fid, "col", bundle.storage[cx_base + 1]);
    try db.bindExternalModule(cx_mod_fid, "env", bundle.storage[cx_base + 2]);
    try db.bindExternalModule(cx_mod_fid, "fs", bundle.storage[cx_base + 3]);
    try db.bindExternalModule(cx_mod_fid, "io", bundle.storage[cx_base + 4]);
    try db.bindExternalModule(cx_mod_fid, "math", bundle.storage[cx_base + 5]);
    try db.bindExternalModule(cx_mod_fid, "mem", bundle.storage[cx_base + 6]);
    try db.bindExternalModule(cx_mod_fid, "path", bundle.storage[cx_base + 7]);
    try db.bindExternalModule(cx_mod_fid, "process", bundle.storage[cx_base + 8]);
    try db.bindExternalModule(cx_mod_fid, "str", bundle.storage[cx_base + 9]);
    try db.bindExternalModule(cx_mod_fid, "time", bundle.storage[cx_base + 10]);

    bundle.count = CORE_MODULE_PATHS.len + CX_STDLIB_PATHS.len;
    if (probe_src_opt) |probe_src| {
        const probe_fid = FileId.fromInt(base_file_id + @as(u32, @intCast(bundle.count)));
        bundle.storage[bundle.count] = probe_fid;
        bundle.probe_fid = probe_fid;
        bundle.count += 1;
        try db.setFilePackageId(probe_fid, .std_core);
        try db.setFilePath(probe_fid, "stdlib/cx/__std02_probe.cx");
        _ = try db.setInput(probe_fid, probe_src, .low);
        try db.bindExternalModule(cx_mod_fid, "__std02_probe", probe_fid);
    }
    return bundle;
}

/// Collects all parse, signature, body, and 4-pass SAST diagnostics for `fid` into `out_sink`.
fn collectAllDiagnostics(db: *CompilerDb, fid: FileId, out_sink: *DiagnosticSink) !void {
    const parsed = try db.parseCst(fid);
    for (parsed.diagnostics.diagnostics.items) |diag_item| {
        _ = try out_sink.emit(diag_item);
    }
    _ = try db.resolveSignatures(fid);
    if (db.getSignatureDiagnostics(fid)) |sig_sink| {
        for (sig_sink.diagnostics.items) |diag_item| {
            _ = try out_sink.emit(diag_item);
        }
    }
    const tree = try db.extractItemTree(fid);
    const def_ids = try db.allocator.alloc(corex.DefId, tree.entries.len);
    defer db.allocator.free(def_ids);
    for (tree.entries, 0..) |entry, i| {
        def_ids[i] = entry.def_id;
    }
    for (def_ids) |def_id| {
        _ = try db.typecheckBody(def_id);
        if (db.getBodyDiagnostics(def_id)) |body_sink| {
            for (body_sink.diagnostics.items) |diag_item| {
                _ = try out_sink.emit(diag_item);
            }
        }
        _ = try db.verifySastMir(def_id);
        if (db.getSastDiagnostics(def_id)) |sast_sink| {
            for (sast_sink.diagnostics.items) |diag_item| {
                _ = try out_sink.emit(diag_item);
            }
        }
    }
}

/// Returns `true` if `sink` contains at least one diagnostic matching `expected_code`.
fn sinkHasCode(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == expected_code) return true;
    }
    return false;
}

/// Prints unexpected diagnostics in `sink` to `stderr` for immediate failure triage.
fn dumpDiagnostics(label: []const u8, sink: *const DiagnosticSink) void {
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

/// Runs `runFourTierDiffOracleOnDb` and dumps any post-opt SAST, demand-body, or `MirVm` diagnostics on failure.
fn runOracleDiagnosed(
    allocator: std.mem.Allocator,
    label: []const u8,
    db: *CompilerDb,
    root_fid: FileId,
    options: corex.diff_oracle.DiffOracleOptions,
) !corex.diff_oracle.DiffOracleReport {
    var opt_sink = DiagnosticSink.init(allocator);
    defer opt_sink.deinit();
    var merged_opts = options;
    merged_opts.diagnostic_sink = &opt_sink;

    const report = corex.runFourTierDiffOracleOnDb(allocator, db, root_fid, merged_opts) catch |oracle_err| {
        if (opt_sink.diagnostics.items.len > 0) dumpDiagnostics(label, &opt_sink);
        var reach_list: std.ArrayListUnmanaged(FileId) = .empty;
        defer reach_list.deinit(allocator);
        db.collectReachableModuleFiles(root_fid, options.extra_file_ids, &reach_list) catch {};
        for (reach_list.items) |mod_fid| {
            if (db.parseCst(mod_fid)) |p_art| {
                if (p_art.diagnostics.hasErrors()) dumpDiagnostics(label, &p_art.diagnostics);
            } else |_| {}
            if (db.getSignatureDiagnostics(mod_fid)) |sig_s| {
                if (sig_s.hasErrors()) dumpDiagnostics(label, sig_s);
            }
        }
        var act_defs: std.ArrayListUnmanaged(corex.DefId) = .empty;
        defer act_defs.deinit(allocator);
        db.collectActiveModuleDefIds(allocator, &.{root_fid}, reach_list.items, &act_defs) catch {};
        for (act_defs.items) |def_id| {
            var def_name: []const u8 = "?";
            if (db.symbol_table.def_to_symbol.get(def_id.asInt())) |sym_i| {
                if (!sym_i.isNone() and sym_i.asInt() < db.symbol_table.symbols.items.len) {
                    def_name = db.symbol_table.getSymbol(sym_i).name_text;
                }
            }
            if (db.typecheckBody(def_id)) |tc_r| {
                if (tc_r.error_count > 0) {
                    std.debug.print("[{s}] tc_err fid={d} item={d} name={s}\n", .{
                        label, def_id.fileId().asInt(), def_id.itemIndex(), def_name,
                    });
                }
            } else |_| {}
            if (db.getBodyDiagnostics(def_id)) |b_sink| {
                if (b_sink.hasErrors()) dumpDiagnostics(label, b_sink);
            }
            if (db.verifySastMir(def_id)) |sast_r| {
                if (!sast_r.is_verified_sound) {
                    std.debug.print("[{s}] sast_unsound fid={d} item={d} name={s}\n", .{
                        label, def_id.fileId().asInt(), def_id.itemIndex(), def_name,
                    });
                }
            } else |_| {}
            if (db.getSastDiagnostics(def_id)) |s_sink| {
                if (s_sink.hasErrors()) dumpDiagnostics(label, s_sink);
            }
            if (db.getComptimeDiagnostics(def_id)) |ct_sink| {
                if (ct_sink.hasErrors()) dumpDiagnostics(label, ct_sink);
            }
        }
        return oracle_err;
    };

    if (report.outcomes[0].has_trapped and !report.outcomes[2].has_trapped) {
        var reachable: std.ArrayListUnmanaged(FileId) = .empty;
        defer reachable.deinit(allocator);
        try db.collectReachableModuleFiles(root_fid, options.extra_file_ids, &reachable);
        var bodies: std.ArrayListUnmanaged(corex.mir.MirBody) = .empty;
        defer {
            for (bodies.items) |*b_item| b_item.deinit();
            bodies.deinit(allocator);
        }
        try db.collectOptimizedModuleBodies(allocator, root_fid, reachable.items, false, null, &bodies);
        var vm_sink = DiagnosticSink.init(allocator);
        defer vm_sink.deinit();
        var vm = try corex.mir_vm.MirVm.init(
            allocator,
            &db.interner,
            &db.type_pool,
            &db.symbol_table,
            &db.rodata_pool,
            null,
            &vm_sink,
            .{
                .target_layout = TargetSpec.host().asTargetLayout(),
                .io = options.io,
                .compiler_db = db,
                .is_oracle_runtime_mode = true,
            },
        );
        defer vm.deinit();
        var main_ptr: ?*const corex.mir.MirBody = null;
        for (bodies.items) |*b_ptr| {
            const sym_idx = if (!b_ptr.symbol_index.isNone())
                b_ptr.symbol_index
            else
                db.symbol_table.def_to_symbol.get(b_ptr.def_id.asInt()) orelse .none;
            _ = try vm.registerBody(b_ptr, sym_idx);
            if (b_ptr.def_id.fileId() == root_fid and std.mem.eql(u8, db.interner.get(b_ptr.name), "main")) {
                main_ptr = b_ptr;
            }
        }
        if (main_ptr) |mp| {
            _ = vm.evalBody(mp, &.{}) catch |vm_err| {
                std.debug.print("[{s}] MirVm trap err={s}\n", .{ label, @errorName(vm_err) });
                dumpDiagnostics(label, &vm_sink);
            };
        }
    }
    return report;
}

/// Creates a fresh isolated `.zig-cache/std02_gates_tmp_<label>_<seq>` directory on disk.
fn createIsolatedTmpDir(allocator: std.mem.Allocator, io: std.Io, label: []const u8) ![]u8 {
    const dir_path = try std.fmt.allocPrint(
        allocator,
        ".zig-cache/std02_gates_tmp_{s}_{d}",
        .{ label, next_tmp_seq.fetchAdd(1, .monotonic) },
    );
    errdefer allocator.free(dir_path);
    std.Io.Dir.cwd().deleteTree(io, dir_path) catch {};
    try std.Io.Dir.cwd().createDirPath(io, dir_path);
    return dir_path;
}

/// Deletes `dir_path` recursively and frees its heap-allocated path slice.
fn cleanupIsolatedTmpDir(allocator: std.mem.Allocator, io: std.Io, dir_path: []u8) void {
    std.Io.Dir.cwd().deleteTree(io, dir_path) catch {};
    allocator.free(dir_path);
}

// ---------------- PE32+ & Reparse Test Helpers ----------------

/// Converts a PE32+ relative virtual address (`rva`) into a raw file offset inside `pe_bytes`.
fn peRvaToFileOffset(pe_bytes: []const u8, sec_table_off: usize, num_sections: usize, rva: u32) ?usize {
    for (0..num_sections) |sec_i| {
        const sh_off = sec_table_off + sec_i * 40;
        if (sh_off + 40 > pe_bytes.len) return null;
        const virt_size = std.mem.readInt(u32, pe_bytes[sh_off + 8 ..][0..4], .little);
        const virt_addr = std.mem.readInt(u32, pe_bytes[sh_off + 12 ..][0..4], .little);
        const raw_size = std.mem.readInt(u32, pe_bytes[sh_off + 16 ..][0..4], .little);
        const raw_ptr = std.mem.readInt(u32, pe_bytes[sh_off + 20 ..][0..4], .little);
        const span_len = @max(virt_size, raw_size);
        if (rva >= virt_addr and rva < virt_addr +| span_len) {
            const delta = rva - virt_addr;
            if (delta < raw_size) {
                const file_off = @as(usize, raw_ptr) + @as(usize, delta);
                if (file_off < pe_bytes.len) return file_off;
            }
        }
    }
    return null;
}

/// Returns `true` if `haystack` contains `needle` under ASCII case-insensitive comparison.
fn containsAsciiIgnoreCase(haystack: []const u8, needle: []const u8) bool {
    if (needle.len == 0) return true;
    if (haystack.len < needle.len) return false;
    var i: usize = 0;
    while (i <= haystack.len - needle.len) : (i += 1) {
        if (std.ascii.eqlIgnoreCase(haystack[i .. i + needle.len], needle)) return true;
    }
    return false;
}

/// Parses the PE32+ Import Directory (`DataDirectory[1]`) of `pe_bytes` and asserts `shell32.dll` is absent.
fn verifyPe32PlusZeroShell32Imports(pe_bytes: []const u8) !void {
    try std.testing.expect(pe_bytes.len >= 0x100);
    try std.testing.expectEqualSlices(u8, "MZ", pe_bytes[0..2]);
    const pe_off: usize = std.mem.readInt(u32, pe_bytes[0x3C..0x40], .little);
    try std.testing.expect(pe_off + 24 <= pe_bytes.len);
    try std.testing.expectEqualSlices(u8, "PE\x00\x00", pe_bytes[pe_off .. pe_off + 4]);

    const coff_off = pe_off + 4;
    const num_sections: usize = std.mem.readInt(u16, pe_bytes[coff_off + 2 ..][0..2], .little);
    const opt_hdr_sz: usize = std.mem.readInt(u16, pe_bytes[coff_off + 16 ..][0..2], .little);
    const opt_off = coff_off + 20;
    const sec_table_off = opt_off + opt_hdr_sz;
    try std.testing.expect(sec_table_off + num_sections * 40 <= pe_bytes.len);

    const opt_magic = std.mem.readInt(u16, pe_bytes[opt_off..][0..2], .little);
    try std.testing.expectEqual(@as(u16, 0x020B), opt_magic);
    try std.testing.expect(opt_hdr_sz >= 128);
    const import_rva = std.mem.readInt(u32, pe_bytes[opt_off + 120 ..][0..4], .little);
    const import_sz = std.mem.readInt(u32, pe_bytes[opt_off + 124 ..][0..4], .little);

    var saw_kernel32 = false;
    if (import_rva != 0 and import_sz >= 20) {
        var desc_off = peRvaToFileOffset(pe_bytes, sec_table_off, num_sections, import_rva) orelse
            return error.InvalidPeImportRva;
        while (desc_off + 20 <= pe_bytes.len) : (desc_off += 20) {
            const name_rva = std.mem.readInt(u32, pe_bytes[desc_off + 12 ..][0..4], .little);
            const first_thunk = std.mem.readInt(u32, pe_bytes[desc_off + 16 ..][0..4], .little);
            if (name_rva == 0 and first_thunk == 0) break;
            if (name_rva != 0) {
                const name_off = peRvaToFileOffset(pe_bytes, sec_table_off, num_sections, name_rva) orelse
                    return error.InvalidPeDllNameRva;
                const rem = pe_bytes[name_off..];
                const nul_idx = std.mem.indexOfScalar(u8, rem, 0) orelse rem.len;
                const dll_name = rem[0..nul_idx];
                if (std.ascii.eqlIgnoreCase(dll_name, "kernel32.dll")) {
                    saw_kernel32 = true;
                }
                try std.testing.expect(!std.ascii.eqlIgnoreCase(dll_name, "shell32.dll"));
                try std.testing.expect(!containsAsciiIgnoreCase(dll_name, "shell32"));
            }
        }
    }
    try std.testing.expect(saw_kernel32);
    try std.testing.expect(!containsAsciiIgnoreCase(pe_bytes, "shell32.dll"));
    try std.testing.expect(!containsAsciiIgnoreCase(pe_bytes, "SHGetKnownFolderPath"));
}

/// Creates an escaping symlink or unprivileged NTFS directory junction at `confined_dir_path/escape_link` -> `outside_dir_path`.
fn createEscapingReparseOrSymlink(
    allocator: std.mem.Allocator,
    io: std.Io,
    confined_dir_path: []const u8,
    outside_dir_path: []const u8,
) !void {
    if (builtin.os.tag != .windows) {
        var conf_dir = try std.Io.Dir.cwd().openDir(io, confined_dir_path, .{});
        defer conf_dir.close(io);
        try conf_dir.symLink(io, "../escape_target", "escape_link", .{ .is_directory = true });
        return;
    }

    const link_win = try std.mem.replaceOwned(u8, allocator, confined_dir_path, "/", "\\");
    defer allocator.free(link_win);
    const out_win = try std.mem.replaceOwned(u8, allocator, outside_dir_path, "/", "\\");
    defer allocator.free(out_win);
    const junction_full = try std.fmt.allocPrint(allocator, "{s}\\escape_link", .{link_win});
    defer allocator.free(junction_full);

    const mklink_res = try std.process.run(allocator, io, .{
        .argv = &.{ "cmd.exe", "/d", "/s", "/c", "mklink", "/J", junction_full, out_win },
    });
    defer allocator.free(mklink_res.stdout);
    defer allocator.free(mklink_res.stderr);
    try std.testing.expect(mklink_res.term == .exited and mklink_res.term.exited == 0);
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------------- Gate 1: cx.io Streams --------------------

test "test_std02_gate1_io_zero_copy_streams_outbuf_bufwriter_seek_and_copy" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const gate1_src =
        "use cx.io.{\n" ++
        "    BufReader,\n" ++
        "    BufWriter,\n" ++
        "    ByteReader,\n" ++
        "    IoError,\n" ++
        "    IoSlice,\n" ++
        "    LimitReader,\n" ++
        "    OutBuf,\n" ++
        "    Reader,\n" ++
        "    SliceWriter,\n" ++
        "    Writer,\n" ++
        "    WriterVTable,\n" ++
        "    copy_stream,\n" ++
        "};\n\n" ++
        "struct SmallChunkSink {\n" ++
        "    bytes: [u8; 64],\n" ++
        "    len: usize,\n" ++
        "    fail_flush: bool,\n" ++
        "    flush_calls: usize,\n" ++
        "}\n\n" ++
        "fn small_sink_write(ctx: *mut opaque, data: &[u8]) -> usize!IoError {\n" ++
        "    let sink_ptr = ctx as *mut SmallChunkSink;\n" ++
        "    if sink_ptr.is_null() {\n" ++
        "        return .Ok(0_usize);\n" ++
        "    }\n" ++
        "    if data.is_empty() {\n" ++
        "        return .Ok(0_usize);\n" ++
        "    }\n" ++
        "    let sink: &mut SmallChunkSink = unsafe { &mut sink_ptr.* };\n" ++
        "    let avail: usize = 64_usize -| sink.len;\n" ++
        "    let cap_step: usize = if data.len() > 5_usize => 5_usize else data.len();\n" ++
        "    let copy_n: usize = if cap_step < avail => cap_step else avail;\n" ++
        "    let dst_base: *mut u8 = &raw mut sink.bytes[0];\n" ++
        "    let src_base: *u8 = data.as_ptr();\n" ++
        "    if copy_n > 0_usize and not dst_base.is_null() and not src_base.is_null() {\n" ++
        "        unsafe {\n" ++
        "            @memcpy(dst_base.add(sink.len) as *mut opaque, src_base as *opaque, copy_n);\n" ++
        "        }\n" ++
        "        sink.len += copy_n;\n" ++
        "    }\n" ++
        "    .Ok(cap_step)\n" ++
        "}\n\n" ++
        "fn small_sink_flush(ctx: *mut opaque) -> unit!IoError {\n" ++
        "    let sink_ptr = ctx as *mut SmallChunkSink;\n" ++
        "    if sink_ptr.is_null() {\n" ++
        "        return .Ok(());\n" ++
        "    }\n" ++
        "    let sink: &mut SmallChunkSink = unsafe { &mut sink_ptr.* };\n" ++
        "    sink.flush_calls += 1_usize;\n" ++
        "    if sink.fail_flush {\n" ++
        "        return .Err(IoError.from_kind(.StorageFull, op: .Flush));\n" ++
        "    }\n" ++
        "    .Ok(())\n" ++
        "}\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    var score = 0;\n\n" ++
        "    // [1] `OutBuf.over_uninit` & `OutBuf.over_slice` (`append`, `filled`, `remaining`, `clear`):\n" ++
        "    var raw_uninit: [u8; 16];\n" ++
        "    var out_uninit = OutBuf.over_uninit(&out raw_uninit);\n" ++
        "    let app1: usize = out_uninit.append(b\"corex\");\n" ++
        "    let app2: usize = out_uninit.append(b\"-io-stream-overflow\");\n" ++
        "    if app1 == 5_usize and app2 == 11_usize and out_uninit.remaining() == 0_usize and\n" ++
        "        out_uninit.filled() == \"corex-io-stream-\".as_bytes()\n" ++
        "    {\n" ++
        "        out_uninit.clear();\n" ++
        "        if out_uninit.is_empty() and out_uninit.remaining() == 16_usize {\n" ++
        "            score += 1;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    var init_arr = [0_u8; 8];\n" ++
        "    var out_slice = OutBuf.over_slice(&mut init_arr);\n" ++
        "    let app_s: usize = out_slice.append(b\"ok!\");\n" ++
        "    if app_s == 3_usize and out_slice.filled() == \"ok!\".as_bytes() and out_slice.remaining() == 5_usize {\n" ++
        "        score += 2;\n" ++
        "    }\n\n" ++
        "    // [2] `BufReader` (`over_uninit` + `new`): `peek`, `consume`, `read_until`, `read_until_into`,\n" ++
        "    //     `next_line` (`\\n`, `\\r\\n`, invalid UTF-8 -> `InvalidData`), `LimitReader`, `empty`, `repeat`, `discard`:\n" ++
        "    var line_src = ByteReader.new(b\"hdr:alpha\\r\\nbeta\\nbad\\xFF\\ntail\");\n" ++
        "    var rd_backing: [u8; 16];\n" ++
        "    var buf_rd = BufReader.over_uninit(line_src.as_reader(), &out rd_backing);\n" ++
        "    let peek_ok: bool = {\n" ++
        "        let peeked: &[u8] = buf_rd.peek(4_usize) catch return -1;\n" ++
        "        peeked.len() >= 4_usize and peeked[0..4] == \"hdr:\".as_bytes()\n" ++
        "    };\n" ++
        "    if peek_ok {\n" ++
        "        buf_rd.consume(4_usize);\n" ++
        "        let l1_ok: bool = (buf_rd.next_line() catch return -2) == .Some(\"alpha\");\n" ++
        "        let l2_ok: bool = (buf_rd.next_line() catch return -3) == .Some(\"beta\");\n" ++
        "        let bad_ok: bool = if buf_rd.next_line() is .Err(bad_e) => bad_e.kind() == .InvalidData else false;\n" ++
        "        let l3_ok: bool = (buf_rd.next_line() catch return -4) == .Some(\"tail\");\n" ++
        "        let l4_ok: bool = (buf_rd.next_line() catch return -5) == .None;\n" ++
        "        if l1_ok and l2_ok and bad_ok and l3_ok and l4_ok {\n" ++
        "            score += 4;\n" ++
        "        }\n" ++
        "    }\n\n" ++
        "    var delim_src = ByteReader.new(b\"segA|segB_very_long_segment|\");\n" ++
        "    var heap_rd = BufReader.new(delim_src.as_reader());\n" ++
        "    let seg_a_ok: bool = (heap_rd.read_until(b'|') catch return -6) == .Some(\"segA\".as_bytes());\n" ++
        "    var into_vec = Vec[u8].new();\n" ++
        "    let cap_err: usize!IoError = heap_rd.read_until_into(b'|', &mut into_vec, max_bytes: 6_usize);\n" ++
        "    var lim_src = ByteReader.new(b\"0123456789\");\n" ++
        "    var lim_rd = LimitReader.new(lim_src.as_reader(), 4_u64);\n" ++
        "    var lim_out = Vec[u8].new();\n" ++
        "    let lim_n: usize = lim_rd.as_reader().read_to_end(&mut lim_out) catch return -7;\n" ++
        "    var emp_rd = Reader.empty();\n" ++
        "    var emp_buf = [1_u8; 4];\n" ++
        "    let emp_n: usize = emp_rd.read(&mut emp_buf) catch return -8;\n" ++
        "    let rep_rd = Reader.repeat(b'Q');\n" ++
        "    var rep_lim = LimitReader.new(rep_rd, 7_u64);\n" ++
        "    let disc_n: u64 = rep_lim.as_reader().discard(5_u64) catch return -9;\n" ++
        "    var rep_tail = [0_u8; 4];\n" ++
        "    let rep_got: usize = rep_lim.as_reader().read(&mut rep_tail) catch return -10;\n" ++
        "    if seg_a_ok and (cap_err is .Err(ce) and ce.kind() == .StreamTooLong) and\n" ++
        "        lim_n == 4_usize and lim_out.as_slice() == \"0123\".as_bytes() and\n" ++
        "        emp_n == 0_usize and disc_n == 5_u64 and rep_got == 2_usize and\n" ++
        "        (&rep_tail)[0..2] == \"QQ\".as_bytes()\n" ++
        "    {\n" ++
        "        score += 8;\n" ++
        "    }\n\n" ++
        "    // [3] `@linear BufWriter`: `over_uninit`, `new(line_buffered: true)`, `write_vectored` /\n" ++
        "    //     `write_all_vectored` after partial fill (`written == buf_len` never returning `Ok(0)`),\n" ++
        "    //     `.print(f\"...\")`, `close(own self)` on failing flush, and `discard(own self)`:\n" ++
        "    var line_dst = [0_u8; 64];\n" ++
        "    var line_sw = SliceWriter.new(&mut line_dst);\n" ++
        "    var line_bw = BufWriter.new(line_sw.as_writer(), line_buffered: true);\n" ++
        "    line_bw.write_all(b\"pre\") catch { line_bw.discard(); return -11; };\n" ++
        "    line_bw.print(f\"-{42_u32}\\ntail\") catch { line_bw.discard(); return -12; };\n" ++
        "    line_bw.discard();\n" ++
        "    var full_dst = [0_u8; 64];\n" ++
        "    var full_sw = SliceWriter.new(&mut full_dst);\n" ++
        "    var full_bw = BufWriter.new(full_sw.as_writer(), line_buffered: true);\n" ++
        "    full_bw.print(f\"pre-{42_u32}\\ntail\") catch { full_bw.discard(); return -13; };\n" ++
        "    full_bw.close() catch return -13;\n" ++
        "    if line_sw.written() == \"pre-42\\n\".as_bytes() and full_sw.written() == \"pre-42\\ntail\".as_bytes() {\n" ++
        "        score += 16;\n" ++
        "    }\n\n" ++
        "    let small_sink_vt = WriterVTable {\n" ++
        "        write: small_sink_write,\n" ++
        "        write_vectored: .None,\n" ++
        "        flush: .Some(small_sink_flush),\n" ++
        "    };\n" ++
        "    var chunk_sink = SmallChunkSink {\n" ++
        "        bytes: [0_u8; 64],\n" ++
        "        len: 0_usize,\n" ++
        "        fail_flush: false,\n" ++
        "        flush_calls: 0_usize,\n" ++
        "    };\n" ++
        "    let raw_sink_wr = unsafe {\n" ++
        "        Writer.from_raw((&raw mut chunk_sink) as *mut opaque, &raw small_sink_vt)\n" ++
        "    };\n" ++
        "    var vec_backing: [u8; 8];\n" ++
        "    var vec_bw = BufWriter.over_uninit(raw_sink_wr, &out vec_backing);\n" ++
        "    vec_bw.write_all(b\"ABCDEF\") catch { vec_bw.discard(); return -14; };\n" ++
        "    let iov_pair = [\n" ++
        "        IoSlice.new(b\"01234\"),\n" ++
        "        IoSlice.new(b\"\"),\n" ++
        "        IoSlice.new(b\"56789!\"),\n" ++
        "    ];\n" ++
        "    let first_vec_n: usize = vec_bw.write_vectored(&iov_pair) catch { vec_bw.discard(); return -15; };\n" ++
        "    let rem_iov = [IoSlice.new(b\"xy\"), IoSlice.new(b\"z\")];\n" ++
        "    vec_bw.write_all_vectored(&rem_iov) catch { vec_bw.discard(); return -16; };\n" ++
        "    vec_bw.close() catch return -17;\n" ++
        "    let sink_view: &[u8] = &chunk_sink.bytes;\n" ++
        "    if first_vec_n > 0_usize and chunk_sink.len >= 9_usize and chunk_sink.len <= 64_usize and\n" ++
        "        sink_view[0..6] == \"ABCDEF\".as_bytes() and\n" ++
        "        sink_view[(chunk_sink.len - 3_usize)..chunk_sink.len] == \"xyz\".as_bytes()\n" ++
        "    {\n" ++
        "        score += 32;\n" ++
        "    }\n\n" ++
        "    var fail_sink = SmallChunkSink {\n" ++
        "        bytes: [0_u8; 64],\n" ++
        "        len: 0_usize,\n" ++
        "        fail_flush: true,\n" ++
        "        flush_calls: 0_usize,\n" ++
        "    };\n" ++
        "    let fail_wr = unsafe {\n" ++
        "        Writer.from_raw((&raw mut fail_sink) as *mut opaque, &raw small_sink_vt)\n" ++
        "    };\n" ++
        "    var fail_bw = BufWriter.new(fail_wr);\n" ++
        "    fail_bw.write_all(b\"payload\") catch { fail_bw.discard(); return -18; };\n" ++
        "    let close_err: unit!IoError = fail_bw.close();\n" ++
        "    var disc_dst = [0_u8; 16];\n" ++
        "    var disc_sw = SliceWriter.new(&mut disc_dst);\n" ++
        "    var disc_bw = BufWriter.new(disc_sw.as_writer());\n" ++
        "    disc_bw.write_all(b\"dropped\") catch { disc_bw.discard(); return -19; };\n" ++
        "    disc_bw.discard();\n" ++
        "    if (close_err is .Err(fe) and fe.kind() == .StorageFull and fe.op() == .Flush) and\n" ++
        "        fail_sink.flush_calls == 1_usize and disc_sw.position() == 0_u64\n" ++
        "    {\n" ++
        "        score += 64;\n" ++
        "    }\n\n" ++
        "    // [4] `ByteReader` & `SliceWriter` `as_seeker()` + `copy_stream` (`max_bytes` -> `StreamTooLong`):\n" ++
        "    var seek_rd = ByteReader.new(b\"0123456789\");\n" ++
        "    var rd_sk = seek_rd.as_seeker();\n" ++
        "    let pos_a: u64 = rd_sk.seek(.Start(4_u64)) catch return -20;\n" ++
        "    let pos_b: u64 = rd_sk.seek(.Current(3_i64)) catch return -21;\n" ++
        "    let pos_c: u64 = rd_sk.seek(.End(-2_i64)) catch return -22;\n" ++
        "    let neg_rd: u64!IoError = rd_sk.seek(.Current(-50_i64));\n" ++
        "    rd_sk.rewind() catch return -23;\n" ++
        "    let pos_rew: u64 = rd_sk.stream_position() catch return -24;\n\n" ++
        "    var seek_dst = [0_u8; 16];\n" ++
        "    var seek_wr = SliceWriter.new(&mut seek_dst);\n" ++
        "    seek_wr.as_writer().write_all(b\"hello_world\") catch return -25;\n" ++
        "    let (wpos_a, neg_wr) = {\n" ++
        "        var wr_sk = seek_wr.as_seeker();\n" ++
        "        let wp: u64 = wr_sk.seek(.Start(6_u64)) catch return -26;\n" ++
        "        let nw: u64!IoError = wr_sk.seek(.Current(-99_i64));\n" ++
        "        (wp, nw)\n" ++
        "    };\n" ++
        "    seek_wr.as_writer().write_all(b\"COREX\") catch return -27;\n\n" ++
        "    var cp_src = ByteReader.new(b\"copy_payload_1234\");\n" ++
        "    var cp_dst_arr = [0_u8; 32];\n" ++
        "    var cp_sw = SliceWriter.new(&mut cp_dst_arr);\n" ++
        "    let cp_ok_n: u64 = {\n" ++
        "        var cp_rd_h: Reader = cp_src.as_reader();\n" ++
        "        var cp_wr_h: Writer = cp_sw.as_writer();\n" ++
        "        copy_stream(&mut cp_rd_h, &mut cp_wr_h, max_bytes: 32_u64) catch return -28\n" ++
        "    };\n" ++
        "    cp_src.as_seeker().rewind() catch return -29;\n" ++
        "    var cp_cap_arr = [0_u8; 32];\n" ++
        "    var cp_cap_sw = SliceWriter.new(&mut cp_cap_arr);\n" ++
        "    let cp_cap_res: u64!IoError = {\n" ++
        "        var cp_rd_cap: Reader = cp_src.as_reader();\n" ++
        "        var cp_wr_cap: Writer = cp_cap_sw.as_writer();\n" ++
        "        copy_stream(&mut cp_rd_cap, &mut cp_wr_cap, max_bytes: 5_u64)\n" ++
        "    };\n" ++
        "    if pos_a == 4_u64 and pos_b == 7_u64 and pos_c == 8_u64 and pos_rew == 0_u64 and\n" ++
        "        wpos_a == 6_u64 and seek_wr.written() == \"hello_COREX\".as_bytes() and\n" ++
        "        (neg_rd is .Err(nre) and nre.kind() == .InvalidInput) and\n" ++
        "        (neg_wr is .Err(nwe) and nwe.kind() == .InvalidInput) and\n" ++
        "        cp_ok_n == 17_u64 and cp_sw.written() == \"copy_payload_1234\".as_bytes() and\n" ++
        "        (cp_cap_res is .Err(cpe) and cpe.kind() == .StreamTooLong)\n" ++
        "    {\n" ++
        "        score += 128;\n" ++
        "    }\n\n" ++
        "    score\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    const std_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &db, 1, null);
    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, gate1_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpDiagnostics("gate1_io", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try runOracleDiagnosed(
        allocator,
        "gate1_io",
        &db,
        app_fid,
        .{ .io = io, .extra_file_ids = std_bundle.asSlice() },
    );
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 255), report.outcomes[0].return_scalar_i64);

    const tmp_dir = try createIsolatedTmpDir(allocator, io, "gate1_rel");
    defer cleanupIsolatedTmpDir(allocator, io, tmp_dir);
    const exe_ext = if (builtin.os.tag == .windows) ".exe" else "";
    const c_rel_exe = try std.fmt.allocPrint(allocator, "{s}/gate1_rel_c99{s}", .{ tmp_dir, exe_ext });
    defer allocator.free(c_rel_exe);
    const ll_rel_exe = try std.fmt.allocPrint(allocator, "{s}/gate1_rel_llvm{s}", .{ tmp_dir, exe_ext });
    defer allocator.free(ll_rel_exe);

    var c_art = try db.compileModuleArtifact(
        app_fid,
        .{ .tier_a_c99 = .{ .target = TargetSpec.host(), .is_release_mode = true, .has_line_directives = false } },
        .{ .artifact_kind = .executable, .output_path = c_rel_exe, .extra_file_ids = std_bundle.asSlice(), .io = io },
    );
    defer c_art.deinit(allocator);
    var ll_art = try db.compileModuleArtifact(
        app_fid,
        .{ .tier_b_llvm = .{ .target = TargetSpec.host(), .is_release_mode = true } },
        .{ .artifact_kind = .executable, .output_path = ll_rel_exe, .extra_file_ids = std_bundle.asSlice(), .io = io },
    );
    defer ll_art.deinit(allocator);

    for ([_][]const u8{ c_rel_exe, ll_rel_exe }) |exe_path| {
        const run_res = try std.process.run(allocator, io, .{ .argv = &.{exe_path} });
        defer allocator.free(run_res.stdout);
        defer allocator.free(run_res.stderr);
        try std.testing.expectEqual(std.process.Child.Term{ .exited = 255 }, run_res.term);
    }
}

// ------------------ Gate 2: cx.path & WTF-8 -------------------

test "test_std02_gate2_path_24b_sso_flavors_dos_stems_and_wtf8_surrogates" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const gate2_probe_src =
        "use cx.col.Vec;\n" ++
        "use cx.mem.Arena;\n" ++
        "use cx.path.{\n" ++
        "    Component,\n" ++
        "    ComponentsIter,\n" ++
        "    Path,\n" ++
        "    PathBuf,\n" ++
        "    PathFlavor,\n" ++
        "    Wtf8Error,\n" ++
        "    components_with_flavor,\n" ++
        "    decode_wtf16_to_path_buf,\n" ++
        "    decode_wtf16_to_wtf8,\n" ++
        "    encode_wtf8_to_wtf16,\n" ++
        "    is_dos_reserved_wtf16,\n" ++
        "    is_separator,\n" ++
        "    normalize_lexical_with_flavor,\n" ++
        "    should_promote_verbatim_win32,\n" ++
        "    strip_prefix_with_flavor,\n" ++
        "};\n" ++
        "use cx.str.String;\n\n" ++
        "fn check_reversible_components(raw_path: &[u8], flavor: PathFlavor, /) -> bool {\n" ++
        "    let view = Path.from_bytes(raw_path);\n" ++
        "    var fwd = Vec[Component].new();\n" ++
        "    var it_f: ComponentsIter = components_with_flavor(view, flavor);\n" ++
        "    while it_f.next() is .Some(comp_f) {\n" ++
        "        fwd.push(comp_f);\n" ++
        "    }\n" ++
        "    var bwd = Vec[Component].new();\n" ++
        "    var it_b: ComponentsIter = components_with_flavor(view, flavor);\n" ++
        "    while it_b.next_back() is .Some(comp_b) {\n" ++
        "        bwd.push(comp_b);\n" ++
        "    }\n" ++
        "    if fwd.len() != bwd.len() {\n" ++
        "        return false;\n" ++
        "    }\n" ++
        "    let count: usize = fwd.len();\n" ++
        "    var i = 0_usize;\n" ++
        "    while i < count {\n" ++
        "        if fwd.as_slice()[i] != bwd.as_slice()[count - 1_usize - i] {\n" ++
        "            return false;\n" ++
        "        }\n" ++
        "        i += 1_usize;\n" ++
        "    }\n" ++
        "    true\n" ++
        "}\n\n" ++
        "pub fn run_gate2() -> i32 {\n" ++
        "    var score = 0;\n\n" ++
        "    // [1] `PathBuf` 24 B SSO (`<= 23 B`) -> `System` heap (`> 23 B`) -> `in_arena` -> `.rodata`:\n" ++
        "    if @size_of[PathBuf]() == 24_usize and @size_of[PathBuf?]() == 24_usize {\n" ++
        "        score += 1;\n" ++
        "    }\n" ++
        "    var pb = PathBuf.from(\"src/main.cx\");\n" ++
        "    let was_inline: bool = pb.len() == 11_usize and pb.capacity() == 23_usize;\n" ++
        "    pb.push(\"sub_module_with_long_filename_exceeding_sso.cx\");\n" ++
        "    let grew_heap: bool = pb.len() > 23_usize and pb.capacity() > 23_usize;\n" ++
        "    let popped: bool = pb.pop();\n" ++
        "    pb.set_file_name(\"lib.cx\");\n" ++
        "    let set_ext_ok: bool = pb.set_extension(\"cxi\");\n" ++
        "    let replaced_pb: PathBuf = pb.as_path().with_file_name(\"alt.cx\");\n" ++
        "    let joined_pb: PathBuf = pb.as_path().join(\"nested\");\n" ++
        "    var arena = Arena.new(slab_bytes: 4_096_usize);\n" ++
        "    let arena_leaf_ok: bool = {\n" ++
        "        var arena_pb = PathBuf.in_arena(&mut arena, cap: 64_usize);\n" ++
        "        arena_pb.push(\"arena_root\");\n" ++
        "        arena_pb.push(\"leaf.cx\");\n" ++
        "        arena_pb.as_path().file_name_str() == .Some(\"leaf.cx\")\n" ++
        "    };\n" ++
        "    arena.release();\n" ++
        "    let rodata_pb = PathBuf.from_string(\n" ++
        "        String.from_static(\"/immutable/rodata/path/longer_than_twenty_three_bytes.cx\"),\n" ++
        "    );\n" ++
        "    if was_inline and grew_heap and popped and set_ext_ok and\n" ++
        "        pb.as_path().extension_str() == .Some(\"cxi\") and\n" ++
        "        replaced_pb.as_path().file_name_str() == .Some(\"alt.cx\") and\n" ++
        "        joined_pb.as_path().file_name_str() == .Some(\"nested\") and\n" ++
        "        arena_leaf_ok and rodata_pb.capacity() == 0_usize and rodata_pb.len() > 23_usize\n" ++
        "    {\n" ++
        "        score += 2;\n" ++
        "    }\n\n" ++
        "    // [2] Cross-OS `ComponentsIter` front-to-back == back-to-front reversal, verbatim `\\\\?\\`,\n" ++
        "    //     `normalize_lexical`, `strip_prefix`, trailing separators, & DOS reserved stems:\n" ++
        "    let rev_ok: bool = check_reversible_components(b\"/usr/local/../bin/\", .Posix) and\n" ++
        "        check_reversible_components(b\"C:\\\\dir\\\\file.cx\", .Windows) and\n" ++
        "        check_reversible_components(b\"C:rel\\\\sub\\\\\", .Windows) and\n" ++
        "        check_reversible_components(b\"\\\\\\\\server\\\\share\\\\dir\\\\a.txt\", .Windows) and\n" ++
        "        check_reversible_components(b\"\\\\\\\\?\\\\C:\\\\a\\\\..\\\\b\", .Windows);\n" ++
        "    var verb_it: ComponentsIter = components_with_flavor(Path.new(\"\\\\\\\\?\\\\C:\\\\a\\\\..\\\\b\"), .Windows);\n" ++
        "    let v0_ok: bool = verb_it.next() == .Some(.Prefix(.VerbatimDisk(b'C')));\n" ++
        "    let v1_ok: bool = verb_it.next() == .Some(.RootDir);\n" ++
        "    let v2_ok: bool = verb_it.next() == .Some(.Normal(\"a\".as_bytes()));\n" ++
        "    let v3_ok: bool = verb_it.next() == .Some(.Normal(\"..\".as_bytes()));\n" ++
        "    let v4_ok: bool = verb_it.next() == .Some(.Normal(\"b\".as_bytes()));\n" ++
        "    let verb_dots_literal: bool = v0_ok and v1_ok and v2_ok and v3_ok and v4_ok;\n\n" ++
        "    let norm_posix: PathBuf = normalize_lexical_with_flavor(Path.new(\"/usr/local/../bin/./corex/\"), .Posix);\n" ++
        "    let norm_win: PathBuf = normalize_lexical_with_flavor(Path.new(\"C:/dir/sub/../file.cx\"), .Windows);\n" ++
        "    let norm_verb: PathBuf = normalize_lexical_with_flavor(Path.new(\"\\\\\\\\?\\\\C:\\\\a\\\\..\\\\b\"), .Windows);\n" ++
        "    let stripped_opt: Path? = strip_prefix_with_flavor(\n" ++
        "        Path.new(\"C:\\\\Workspace\\\\CoreX\\\\src\\\\main.cx\"),\n" ++
        "        Path.new(\"c:/Workspace/CoreX\"),\n" ++
        "        .Windows,\n" ++
        "    );\n" ++
        "    let trail_bytes: &[u8] = Path.new(\"/usr/bin/\").as_bytes();\n" ++
        "    let has_trail: bool = not trail_bytes.is_empty() and is_separator(trail_bytes[trail_bytes.len() - 1_usize]);\n" ++
        "    if rev_ok and verb_dots_literal and\n" ++
        "        norm_posix.as_bytes() == \"/usr/bin/corex\".as_bytes() and\n" ++
        "        norm_win.as_bytes() == \"C:\\\\dir\\\\file.cx\".as_bytes() and\n" ++
        "        norm_verb.as_bytes() == \"\\\\\\\\?\\\\C:\\\\a\\\\..\\\\b\".as_bytes() and\n" ++
        "        (stripped_opt is .Some(sp) and sp.as_bytes() == \"src\\\\main.cx\".as_bytes()) and has_trail\n" ++
        "    {\n" ++
        "        score += 4;\n" ++
        "    }\n\n" ++
        "    // [3] Windows DOS reserved device stems (`CON`, `NUL.txt`, `LPT1`, `COM¹`, `CONIN$`, trailing dots/spaces):\n" ++
        "    let com_sup1: &[u8] = b\"C:\\\\tmp\\\\COM\\xC2\\xB9.log\";\n" ++
        "    let wtf16_conin = [0x0063_u16, 0x006F_u16, 0x006E_u16, 0x0069_u16, 0x006E_u16, 0x0024_u16];\n" ++
        "    let wtf16_trail = [0x0061_u16, 0x002E_u16, 0x0020_u16];\n" ++
        "    let wtf16_plain = [0x006D_u16, 0x0061_u16, 0x0069_u16, 0x006E_u16];\n" ++
        "    let dos_ok: bool = Path.new(\"CON\").has_dos_reserved_stem() and\n" ++
        "        Path.new(\"dir/NUL.txt\").has_dos_reserved_stem() and\n" ++
        "        Path.new(\"LPT1\").has_dos_reserved_stem() and\n" ++
        "        Path.from_bytes(com_sup1).has_dos_reserved_stem() and\n" ++
        "        Path.new(\"conin$\").has_dos_reserved_stem() and\n" ++
        "        Path.new(\"aux . .  \").has_dos_reserved_stem() and\n" ++
        "        not Path.new(\"config.cx\").has_dos_reserved_stem() and\n" ++
        "        is_dos_reserved_wtf16(&wtf16_conin) and\n" ++
        "        should_promote_verbatim_win32(&wtf16_conin) and\n" ++
        "        should_promote_verbatim_win32(&wtf16_trail) and\n" ++
        "        not should_promote_verbatim_win32(&wtf16_plain);\n" ++
        "    if dos_ok {\n" ++
        "        score += 8;\n" ++
        "    }\n\n" ++
        "    // [4] WTF-8 <-> UTF-16LE round-trip preserving lone surrogates (`0xD800`, `0xDC00`)\n" ++
        "    //     while rejecting 6-byte paired CESU-8 surrogates and interior NULs (`\\0`):\n" ++
        "    let lone_u16 = [0x0061_u16, 0xD800_u16, 0x005F_u16, 0xDC00_u16, 0xD800_u16];\n" ++
        "    let surr_pb: PathBuf = decode_wtf16_to_path_buf(&lone_u16);\n" ++
        "    var round_u16 = [0_u16; 8];\n" ++
        "    let enc_len: usize = encode_wtf8_to_wtf16(surr_pb.as_bytes(), &mut round_u16) catch return -30;\n" ++
        "    var dec_bytes = [0_u8; 16];\n" ++
        "    let round_view: &[u16] = &round_u16;\n" ++
        "    let dec_len: usize = decode_wtf16_to_wtf8(round_view[0..enc_len], &mut dec_bytes);\n" ++
        "    let cesu8_pair = [0xED_u8, 0xA0_u8, 0x80_u8, 0xED_u8, 0xB0_u8, 0x80_u8];\n" ++
        "    var bad_u16 = [0_u16; 8];\n" ++
        "    let cesu8_res: usize!Wtf8Error = encode_wtf8_to_wtf16(&cesu8_pair, &mut bad_u16);\n" ++
        "    let nul_res: usize!Wtf8Error = encode_wtf8_to_wtf16(b\"ab\\0cd\", &mut bad_u16);\n" ++
        "    let lone_view: &[u16] = &lone_u16;\n" ++
        "    let dec_view: &[u8] = &dec_bytes;\n" ++
        "    if enc_len == 5_usize and round_view[0..5] == lone_view and\n" ++
        "        dec_len == surr_pb.len() and dec_view[0..dec_len] == surr_pb.as_bytes() and\n" ++
        "        cesu8_res == .Err(.InvalidWtf8) and nul_res == .Err(.InteriorNulByte)\n" ++
        "    {\n" ++
        "        score += 16;\n" ++
        "    }\n\n" ++
        "    score\n" ++
        "}\n";

    const gate2_app_src =
        "pub fn main() -> i32 {\n" ++
        "    cx.__std02_probe.run_gate2()\n" ++
        "}\n";

    for ([_]TargetSpec{ TargetSpec.X86_64_LINUX, TargetSpec.X86_64_WINDOWS, TargetSpec.WASM32_WASI }) |target_spec| {
        var layout_db = try CompilerDb.init(allocator);
        defer layout_db.deinit();
        layout_db.setTargetSpec(target_spec);
        const layout_probe =
            "use cx.path.PathBuf;\n" ++
            "pub type OptPathBuf = PathBuf?;\n";
        const layout_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &layout_db, 1, null);
        const l_fid = FileId.fromInt(0);
        _ = try layout_db.setInput(l_fid, layout_probe, .low);
        _ = try layout_db.resolveSignatures(l_fid);
        _ = try layout_db.resolveSignatures(layout_bundle.path_fid);

        const path_scope = layout_db.symbol_table.file_module_scopes.get(layout_bundle.path_fid.asInt()).?;
        const l_scope = layout_db.symbol_table.file_module_scopes.get(l_fid.asInt()).?;
        const pb_sym = layout_db.symbol_table.lookupInScopeDirect(
            path_scope,
            try layout_db.interner.intern("PathBuf"),
            corex.symbol_resolver.NamespaceMask.TYPE_ONLY,
        );
        const opt_pb_sym = layout_db.symbol_table.lookupInScopeDirect(
            l_scope,
            try layout_db.interner.intern("OptPathBuf"),
            corex.symbol_resolver.NamespaceMask.TYPE_ONLY,
        );
        var resolver = TypeLayoutResolver.init(
            allocator,
            &layout_db.type_pool,
            &layout_db.symbol_table,
            target_spec,
        );
        defer resolver.deinit();
        const pb_layout = try resolver.resolveType(layout_db.symbol_table.getSymbol(pb_sym).type_id);
        const opt_pb_layout = try resolver.resolveType(layout_db.symbol_table.getSymbol(opt_pb_sym).type_id);
        try std.testing.expectEqual(@as(u64, 24), pb_layout.size_bytes);
        try std.testing.expectEqual(@as(u64, 24), opt_pb_layout.size_bytes);
    }

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    const std_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &db, 1, gate2_probe_src);
    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, gate2_app_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    try collectAllDiagnostics(&db, std_bundle.probe_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpDiagnostics("gate2_path", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try runOracleDiagnosed(
        allocator,
        "gate2_path",
        &db,
        app_fid,
        .{ .io = io, .extra_file_ids = std_bundle.asSlice() },
    );
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 31), report.outcomes[0].return_scalar_i64);
}

// ------------------- Gate 3: cx.time Clocks -------------------

test "test_std02_gate3_time_clocks_u128_scaling_and_sleep" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const gate3_probe_src =
        "use cx.time.{\n" ++
        "    Duration,\n" ++
        "    Instant,\n" ++
        "    SystemTime,\n" ++
        "    TimeError,\n" ++
        "    scale_mach_ticks_to_nanos,\n" ++
        "    scale_ticks_to_nanos_hz,\n" ++
        "    sleep,\n" ++
        "};\n\n" ++
        "pub fn run_gate3() -> i32 {\n" ++
        "    var score = 0;\n\n" ++
        "    // [1] `Duration` checked/saturating arithmetic & `Duration.MAX`:\n" ++
        "    let d_sec = Duration.from_secs(3_u64);\n" ++
        "    let d_ms = Duration.from_millis(250_u64);\n" ++
        "    let d_sum: Duration? = d_sec.checked_add(d_ms);\n" ++
        "    let d_ovf: Duration? = Duration.MAX.checked_add(Duration.from_nanos(1_u64));\n" ++
        "    let d_udf: Duration? = d_ms.checked_sub(d_sec);\n" ++
        "    let sat_hi: Duration = Duration.MAX.saturating_add(d_sec);\n" ++
        "    let sat_lo: Duration = d_ms.saturating_sub(d_sec);\n" ++
        "    let sat_mul: Duration = Duration.from_secs(u64.MAX / 2_u64).saturating_mul(4_u32);\n" ++
        "    if d_sum == .Some(Duration.from_millis(3_250_u64)) and d_ovf == .None and d_udf == .None and\n" ++
        "        sat_hi == Duration.MAX and sat_lo == Duration.ZERO and sat_mul == Duration.MAX\n" ++
        "    {\n" ++
        "        score += 1;\n" ++
        "    }\n\n" ++
        "    // [2] `Instant.now()` monotonicity (`t2 >= t1`), `sleep(Duration.ZERO)`, & `SystemTime`:\n" ++
        "    let inst1 = Instant.now();\n" ++
        "    sleep(Duration.ZERO);\n" ++
        "    let inst2 = Instant.now();\n" ++
        "    let mono_delta: Duration? = inst2.checked_duration_since(inst1);\n" ++
        "    let wall_now = SystemTime.now();\n" ++
        "    let since_epoch: Duration!TimeError = wall_now.duration_since(SystemTime.UNIX_EPOCH);\n" ++
        "    let future_ts: SystemTime = SystemTime.from_unix_timestamp(4_102_444_800_i64, 500_u32) orelse return -1;\n" ++
        "    let before_err: Duration!TimeError = SystemTime.UNIX_EPOCH.duration_since(future_ts);\n" ++
        "    let bad_subsec: SystemTime? = SystemTime.from_unix_timestamp(0_i64, 1_000_000_000_u32);\n" ++
        "    if inst2 >= inst1 and (mono_delta is .Some(_)) and\n" ++
        "        (since_epoch is .Ok(ep_dur) and ep_dur.as_secs() > 1_577_836_800_u64) and\n" ++
        "        before_err == .Err(.SystemClockBeforeEarlier) and bad_subsec == .None\n" ++
        "    {\n" ++
        "        score += 2;\n" ++
        "    }\n\n" ++
        "    // [3] 128-bit tick scaling (`10 MHz`, `24 MHz`, `1 GHz`, prime Hz, Mach `125/3`) across 500-year uptimes:\n" ++
        "    let secs_500y = 500_u64 * 365_u64 * 86_400_u64;\n" ++
        "    let exp_500y_ns: u64 = secs_500y * 1_000_000_000_u64;\n" ++
        "    let ns_10m: u64 = scale_ticks_to_nanos_hz(secs_500y * 10_000_000_u64 + 5_u64, 10_000_000_u64);\n" ++
        "    let ns_24m: u64 = scale_ticks_to_nanos_hz(secs_500y * 24_000_000_u64 + 12_u64, 24_000_000_u64);\n" ++
        "    let ns_1g: u64 = scale_ticks_to_nanos_hz(exp_500y_ns + 777_u64, 1_000_000_000_u64);\n" ++
        "    let ns_prime: u64 = scale_ticks_to_nanos_hz(19_200_003_u64 * 1_000_u64, 19_200_003_u64);\n" ++
        "    let mach_24m_ticks: u64 = secs_500y * 24_000_000_u64;\n" ++
        "    let ns_mach: u64 = scale_mach_ticks_to_nanos(mach_24m_ticks, 125_u32, 3_u32);\n" ++
        "    if ns_10m == exp_500y_ns + 500_u64 and\n" ++
        "        ns_24m == exp_500y_ns + 500_u64 and\n" ++
        "        ns_1g == exp_500y_ns + 777_u64 and\n" ++
        "        ns_prime == 1_000_000_000_000_u64 and\n" ++
        "        ns_mach == exp_500y_ns\n" ++
        "    {\n" ++
        "        score += 4;\n" ++
        "    }\n\n" ++
        "    score\n" ++
        "}\n";

    const gate3_app_src =
        "pub fn main() -> i32 {\n" ++
        "    cx.__std02_probe.run_gate3()\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    db.setSastStrict(true);
    const std_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &db, 1, gate3_probe_src);
    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, gate3_app_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    try collectAllDiagnostics(&db, std_bundle.probe_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpDiagnostics("gate3_time", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try runOracleDiagnosed(
        allocator,
        "gate3_time",
        &db,
        app_fid,
        .{ .io = io, .extra_file_ids = std_bundle.asSlice() },
    );
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 7), report.outcomes[0].return_scalar_i64);
}

// ------------------ Gate 4: cx.fs Filesystem ------------------

test "test_std02_gate4_fs_thresholded_mmap_atomic_beneath_lock_watcher_and_diag_ring" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const tmp_root = try createIsolatedTmpDir(allocator, io, "gate4_fs");
    defer cleanupIsolatedTmpDir(allocator, io, tmp_root);

    const confined_dir = try std.fmt.allocPrint(allocator, "{s}/confined", .{tmp_root});
    defer allocator.free(confined_dir);
    const confined_sub = try std.fmt.allocPrint(allocator, "{s}/confined/sub", .{tmp_root});
    defer allocator.free(confined_sub);
    const outside_dir = try std.fmt.allocPrint(allocator, "{s}/escape_target", .{tmp_root});
    defer allocator.free(outside_dir);
    try std.Io.Dir.cwd().createDirPath(io, confined_sub);
    try std.Io.Dir.cwd().createDirPath(io, outside_dir);

    const valid_child_path = try std.fmt.allocPrint(allocator, "{s}/valid.txt", .{confined_sub});
    defer allocator.free(valid_child_path);
    const outside_secret_path = try std.fmt.allocPrint(allocator, "{s}/secret.txt", .{outside_dir});
    defer allocator.free(outside_secret_path);
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = valid_child_path, .data = "confined-ok" });
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = outside_secret_path, .data = "outside-secret" });
    try createEscapingReparseOrSymlink(allocator, io, confined_dir, outside_dir);

    const gate4_probe_src = try std.fmt.allocPrint(
        allocator,
        "use cx.col.Vec;\n" ++
            "use cx.fs.{{\n" ++
            "    Dir,\n" ++
            "    DirIter,\n" ++
            "    FS_DIAG_RING_MAGIC,\n" ++
            "    File,\n" ++
            "    FileLock,\n" ++
            "    FsDiagPathRing,\n" ++
            "    FsDiagPathSlot,\n" ++
            "    FsWatcher,\n" ++
            "    OpenOptions,\n" ++
            "    StagedAtomicFile,\n" ++
            "    WatchEvent,\n" ++
            "    WatchMask,\n" ++
            "    create_dir_all,\n" ++
            "    load_file_thresholded,\n" ++
            "    materialize_file,\n" ++
            "    read_to_bytes,\n" ++
            "    remove_dir_all,\n" ++
            "    resolve_or_create_path,\n" ++
            "    resolve_path,\n" ++
            "    write_atomic,\n" ++
            "}};\n" ++
            "use cx.mem.Arena;\n" ++
            "use cx.path.{{Path, PathBuf}};\n" ++
            "use cx.str.String;\n" ++
            "use cx.time.Duration;\n\n" ++
            "const TMP_ROOT: str = \"{s}\";\n\n" ++
            "fn join_work(rel: str, /) -> PathBuf {{\n" ++
            "    Path.new(TMP_ROOT).join(\"work\").as_path().join(rel)\n" ++
            "}}\n\n" ++
            "fn is_open_file_beneath_rejected(dir: &Dir, rel: str, /) -> bool {{\n" ++
            "    match dir.open_file_beneath(rel) {{\n" ++
            "        .Ok(leaked_f) => {{\n" ++
            "            leaked_f.close();\n" ++
            "            false\n" ++
            "        }},\n" ++
            "        .Err(_) => true,\n" ++
            "    }}\n" ++
            "}}\n\n" ++
            "fn is_open_dir_beneath_rejected(dir: &Dir, rel: str, /) -> bool {{\n" ++
            "    match dir.open_dir_beneath(rel) {{\n" ++
            "        .Ok(leaked_d) => {{\n" ++
            "            leaked_d.close();\n" ++
            "            false\n" ++
            "        }},\n" ++
            "        .Err(_) => true,\n" ++
            "    }}\n" ++
            "}}\n\n" ++
            "pub fn run_gate4() -> i32 {{\n" ++
            "    let work_root: PathBuf = Path.new(TMP_ROOT).join(\"work\");\n" ++
            "    remove_dir_all(work_root.as_path()) catch {{}};\n" ++
            "    create_dir_all(work_root.as_path()) catch return -1;\n" ++
            "    var score = 0;\n\n" ++
            "    // [1] `File`/`Dir` CRUD, `as_reader`/`as_writer`/`as_seeker` sentinels, `DirIter` (no `.`/`..`),\n" ++
            "    //     `resolve_path`, & `resolve_or_create_path`:\n" ++
            "    let nested_file_pb: PathBuf = resolve_or_create_path(\n" ++
            "        join_work(\"tree/leaf/hello.txt\").as_path(),\n" ++
            "        kind: .File,\n" ++
            "    ) catch return -2;\n" ++
            "    let canon_pb: PathBuf = resolve_path(nested_file_pb.as_path()) catch return -3;\n" ++
            "    var crud_f: File = File.create(nested_file_pb.as_path()) catch return -4;\n" ++
            "    crud_f.as_writer().write_all(b\"0123456789\") catch {{ crud_f.close(); return -5; }};\n" ++
            "    crud_f.sync_close() catch return -6;\n" ++
            "    var rd_f: File = File.open(canon_pb.as_path()) catch return -7;\n" ++
            "    let seek_pos: u64 = rd_f.as_seeker().seek(.Start(4_u64)) catch {{ rd_f.close(); return -8; }};\n" ++
            "    var tail_vec = Vec[u8].new();\n" ++
            "    let got_tail: usize = rd_f.as_reader().read_to_end(&mut tail_vec) catch {{ rd_f.close(); return -9; }};\n" ++
            "    rd_f.close();\n" ++
            "    var leaf_dir: Dir = Dir.open(join_work(\"tree/leaf\").as_path()) catch return -10;\n" ++
            "    var dir_it: DirIter = leaf_dir.entries() catch {{ leaf_dir.close(); return -11; }};\n" ++
            "    var entry_count = 0_usize;\n" ++
            "    var saw_dot = false;\n" ++
            "    while true {{\n" ++
            "        let next_opt = dir_it.next() catch {{ dir_it.close(); leaf_dir.close(); return -12; }};\n" ++
            "        if next_opt is .Some(entry) {{\n" ++
            "            if entry.name.as_bytes() == \".\".as_bytes() or entry.name.as_bytes() == \"..\".as_bytes() {{\n" ++
            "                saw_dot = true;\n" ++
            "            }}\n" ++
            "            entry_count += 1_usize;\n" ++
            "        }} else {{\n" ++
            "            break;\n" ++
            "        }}\n" ++
            "    }}\n" ++
            "    dir_it.close();\n" ++
            "    leaf_dir.close();\n" ++
            "    if seek_pos == 4_u64 and got_tail == 6_usize and tail_vec.as_slice() == \"456789\".as_bytes() and\n" ++
            "        entry_count == 1_usize and not saw_dot\n" ++
            "    {{\n" ++
            "        score += 1;\n" ++
            "    }}\n\n" ++
            "    // [2] `load_file_thresholded`: `0 B`, `< 16 KiB` `ArenaBuf` + `\\0`, & `>= 16 KiB` (`20,500 B`) `Mapped` + `\\0`:\n" ++
            "    let p_zero: PathBuf = join_work(\"zero.cx\");\n" ++
            "    let p_small: PathBuf = join_work(\"small.cx\");\n" ++
            "    let p_large: PathBuf = join_work(\"large_20k.cx\");\n" ++
            "    write_atomic(p_zero.as_path(), b\"\", durability: .FastLocal) catch return -13;\n" ++
            "    var small_data = [b's'; 1024];\n" ++
            "    small_data[1023] = b';';\n" ++
            "    write_atomic(p_small.as_path(), &small_data, durability: .FastLocal) catch return -14;\n" ++
            "    var large_vec = Vec[u8].with_capacity(20_500_usize);\n" ++
            "    var li = 0_usize;\n" ++
            "    while li < 20_500_usize {{\n" ++
            "        large_vec.push(b'a' + ((li % 26_usize) as u8));\n" ++
            "        li += 1_usize;\n" ++
            "    }}\n" ++
            "    write_atomic(p_large.as_path(), large_vec.as_slice(), durability: .FastLocal) catch return -15;\n" ++
            "    var load_ok = true;\n" ++
            "    var load_arena = Arena.new(slab_bytes: 32_768_usize);\n" ++
            "    if load_file_thresholded(&mut load_arena, p_zero.as_path()) is .Ok(lf_zero) {{\n" ++
            "        let z_empty: bool = lf_zero.is_empty();\n" ++
            "        let z_nul: u8 = unsafe {{ lf_zero.as_slice().as_ptr().read() }};\n" ++
            "        lf_zero.close();\n" ++
            "        if not z_empty or z_nul != 0_u8 {{ load_ok = false; }}\n" ++
            "    }} else {{\n" ++
            "        load_ok = false;\n" ++
            "    }}\n" ++
            "    if load_file_thresholded(&mut load_arena, p_small.as_path()) is .Ok(lf_small) {{\n" ++
            "        let is_small_arena: bool = match &lf_small {{\n" ++
            "            .ArenaBuf(_) => true,\n" ++
            "            .Mapped(&_unused_m) => false,\n" ++
            "        }};\n" ++
            "        let s_len: usize = lf_small.len();\n" ++
            "        let s_nul: u8 = unsafe {{ lf_small.as_slice().as_ptr().add(s_len).read() }};\n" ++
            "        lf_small.close();\n" ++
            "        if not is_small_arena or s_len != 1024_usize or s_nul != 0_u8 {{ load_ok = false; }}\n" ++
            "    }} else {{\n" ++
            "        load_ok = false;\n" ++
            "    }}\n" ++
            "    if load_file_thresholded(&mut load_arena, p_large.as_path()) is .Ok(lf_large) {{\n" ++
            "        let is_large_mmap: bool = match &lf_large {{\n" ++
            "            .ArenaBuf(_) => false,\n" ++
            "            .Mapped(&_unused_m2) => true,\n" ++
            "        }};\n" ++
            "        let l_len: usize = lf_large.len();\n" ++
            "        let l_nul: u8 = unsafe {{ lf_large.as_slice().as_ptr().add(l_len).read() }};\n" ++
            "        let l_match: bool = l_len == 20_500_usize and lf_large.as_slice() == large_vec.as_slice();\n" ++
            "        lf_large.close();\n" ++
            "        if not is_large_mmap or l_nul != 0_u8 or not l_match {{ load_ok = false; }}\n" ++
            "    }} else {{\n" ++
            "        load_ok = false;\n" ++
            "    }}\n" ++
            "    load_arena.release();\n" ++
            "    if load_ok {{\n" ++
            "        score += 2;\n" ++
            "    }}\n\n" ++
            "    // [3] Live `write_atomic` & `StagedAtomicFile` (`FastLocal` & `CrashSafe`) while an open `File` holds old inode:\n" ++
            "    let atom_pb: PathBuf = join_work(\"live_atomic.txt\");\n" ++
            "    write_atomic(atom_pb.as_path(), b\"gen-v1-old\", durability: .FastLocal) catch return -19;\n" ++
            "    var held_old: File = File.open(atom_pb.as_path()) catch return -20;\n" ++
            "    if write_atomic(atom_pb.as_path(), b\"gen-v2-fast\", durability: .FastLocal) is .Err(_) {{\n" ++
            "        held_old.close();\n" ++
            "        return -21;\n" ++
            "    }}\n" ++
            "    var staged_v3: StagedAtomicFile = StagedAtomicFile.create(atom_pb.as_path()) catch {{\n" ++
            "        held_old.close();\n" ++
            "        return -22;\n" ++
            "    }};\n" ++
            "    staged_v3.as_writer().write_all(b\"gen-v3-crashsafe\") catch {{\n" ++
            "        staged_v3.abort();\n" ++
            "        held_old.close();\n" ++
            "        return -23;\n" ++
            "    }};\n" ++
            "    staged_v3.publish(durability: .CrashSafe) catch {{ held_old.close(); return -24; }};\n" ++
            "    var aborted_v4: StagedAtomicFile = StagedAtomicFile.create(atom_pb.as_path()) catch {{\n" ++
            "        held_old.close();\n" ++
            "        return -25;\n" ++
            "    }};\n" ++
            "    aborted_v4.as_writer().write_all(b\"aborted\") catch {{}};\n" ++
            "    aborted_v4.abort();\n" ++
            "    var old_bytes = Vec[u8].new();\n" ++
            "    _ = held_old.as_reader().read_to_end(&mut old_bytes) catch {{ held_old.close(); return -26; }};\n" ++
            "    held_old.close();\n" ++
            "    let fresh_bytes: Vec[u8] = read_to_bytes(atom_pb.as_path()) catch return -27;\n" ++
            "    if old_bytes.as_slice() == \"gen-v1-old\".as_bytes() and\n" ++
            "        fresh_bytes.as_slice() == \"gen-v3-crashsafe\".as_bytes()\n" ++
            "    {{\n" ++
            "        score += 4;\n" ++
            "    }}\n\n" ++
            "    // [4] `materialize_file` (`.ReflinkOrCopy`, `.ImmutableCas`, self-copy safety, `overwrite: false` -> `AlreadyExists`):\n" ++
            "    let mat_dst1: PathBuf = join_work(\"mat_reflink.txt\");\n" ++
            "    let mat_dst2: PathBuf = join_work(\"mat_cas.txt\");\n" ++
            "    _ = materialize_file(atom_pb.as_path(), mat_dst1.as_path(), policy: .ReflinkOrCopy) catch return -28;\n" ++
            "    _ = materialize_file(atom_pb.as_path(), mat_dst2.as_path(), policy: .ImmutableCas) catch return -29;\n" ++
            "    _ = materialize_file(mat_dst1.as_path(), mat_dst1.as_path(), overwrite: true) catch return -30;\n" ++
            "    let no_ovw_res = materialize_file(atom_pb.as_path(), mat_dst1.as_path(), overwrite: false);\n" ++
            "    let mat1_bytes: Vec[u8] = read_to_bytes(mat_dst1.as_path()) catch return -31;\n" ++
            "    let mat2_bytes: Vec[u8] = read_to_bytes(mat_dst2.as_path()) catch return -32;\n" ++
            "    if mat1_bytes.as_slice() == \"gen-v3-crashsafe\".as_bytes() and\n" ++
            "        mat2_bytes.as_slice() == \"gen-v3-crashsafe\".as_bytes() and\n" ++
            "        (no_ovw_res is .Err(me) and me.kind() == .AlreadyExists)\n" ++
            "    {{\n" ++
            "        score += 8;\n" ++
            "    }}\n\n" ++
            "    // [5] `Dir.*_beneath` confinement (valid relative child vs `..`, absolute, `:` ADS/drive, & escaping symlink/junction):\n" ++
            "    let conf_pb: PathBuf = Path.new(TMP_ROOT).join(\"confined\");\n" ++
            "    var conf_dir: Dir = Dir.open(conf_pb.as_path()) catch return -33;\n" ++
            "    conf_dir.create_dir_beneath(\"ephemeral\") catch {{ conf_dir.close(); return -34; }};\n" ++
            "    var sub_wr: File = conf_dir.open_file_beneath(\n" ++
            "        \"ephemeral/item.txt\",\n" ++
            "        OpenOptions.write_create(),\n" ++
            "    ) catch {{\n" ++
            "        conf_dir.close();\n" ++
            "        return -35;\n" ++
            "    }};\n" ++
            "    sub_wr.write_all(b\"beneath-data\") catch {{ sub_wr.close(); conf_dir.close(); return -36; }};\n" ++
            "    sub_wr.close();\n" ++
            "    var sub_rd: File = conf_dir.open_file_beneath(\"sub/valid.txt\") catch {{ conf_dir.close(); return -37; }};\n" ++
            "    var sub_vec = Vec[u8].new();\n" ++
            "    _ = sub_rd.as_reader().read_to_end(&mut sub_vec) catch {{\n" ++
            "        sub_rd.close();\n" ++
            "        conf_dir.close();\n" ++
            "        return -38;\n" ++
            "    }};\n" ++
            "    sub_rd.close();\n" ++
            "    let meta_valid = conf_dir.metadata_beneath(\"sub/valid.txt\", follow_symlinks: true) catch {{\n" ++
            "        conf_dir.close();\n" ++
            "        return -39;\n" ++
            "    }};\n" ++
            "    conf_dir.unlink_file_beneath(\"ephemeral/item.txt\") catch {{ conf_dir.close(); return -40; }};\n" ++
            "    let rej_dotdot: bool = is_open_file_beneath_rejected(&conf_dir, \"../escape_target/secret.txt\");\n" ++
            "    let rej_deep: bool = is_open_file_beneath_rejected(&conf_dir, \"sub/../../escape_target/secret.txt\");\n" ++
            "    let rej_abs: bool = is_open_file_beneath_rejected(&conf_dir, \"/etc/passwd\") and\n" ++
            "        is_open_file_beneath_rejected(&conf_dir, \"C:\\\\Windows\\\\win.ini\");\n" ++
            "    let rej_colon: bool = is_open_file_beneath_rejected(&conf_dir, \"sub/valid.txt:ads\");\n" ++
            "    let rej_link_open: bool = is_open_file_beneath_rejected(&conf_dir, \"escape_link/secret.txt\");\n" ++
            "    let rej_link_dir: bool = is_open_dir_beneath_rejected(&conf_dir, \"escape_link\");\n" ++
            "    let link_lstat = conf_dir.metadata_beneath(\"escape_link\", follow_symlinks: false);\n" ++
            "    let link_follow = conf_dir.metadata_beneath(\"escape_link\", follow_symlinks: true);\n" ++
            "    conf_dir.close();\n" ++
            "    remove_dir_all(conf_pb.as_path().join(\"ephemeral\").as_path()) catch {{}};\n" ++
            "    if sub_vec.as_slice() == \"confined-ok\".as_bytes() and meta_valid.size == 11_u64 and\n" ++
            "        rej_dotdot and rej_deep and rej_abs and rej_colon and rej_link_open and rej_link_dir and\n" ++
            "        (link_lstat is .Ok(lm) and lm.file_type == .Symlink) and (link_follow is .Err(_))\n" ++
            "    {{\n" ++
            "        score += 16;\n" ++
            "    }}\n\n" ++
            "    // [6] `FileLock` (`acquire` exclusive + nonblocking `FileLockConflict`) & `FsWatcher` (`new`, `watch`, `poll_events`):\n" ++
            "    let lock_pb: PathBuf = join_work(\"exclusive.lock\");\n" ++
            "    let lock_a: FileLock = FileLock.acquire(lock_pb.as_path(), mode: .Exclusive, nonblocking: false) catch return -41;\n" ++
            "    let lock_b_res = FileLock.acquire(lock_pb.as_path(), mode: .Exclusive, nonblocking: true);\n" ++
            "    var lock_conflict_ok = false;\n" ++
            "    match lock_b_res {{\n" ++
            "        .Err(le) => {{\n" ++
            "            lock_conflict_ok = le.kind() == .FileLockConflict;\n" ++
            "        }},\n" ++
            "        .Ok(unexpected_lock) => {{\n" ++
            "            unexpected_lock.unlock_and_close();\n" ++
            "        }},\n" ++
            "    }}\n" ++
            "    lock_a.unlock_and_close();\n\n" ++
            "    let watch_dir_pb: PathBuf = join_work(\"watched_dir\");\n" ++
            "    create_dir_all(watch_dir_pb.as_path()) catch return -42;\n" ++
            "    var watcher: FsWatcher = FsWatcher.new() catch return -43;\n" ++
            "    let watch_id = watcher.watch(watch_dir_pb.as_path(), mask: WatchMask.ALL_RECURSIVE) catch {{\n" ++
            "        watcher.close();\n" ++
            "        return -44;\n" ++
            "    }};\n" ++
            "    write_atomic(\n" ++
            "        watch_dir_pb.as_path().join(\"event_probe.txt\").as_path(),\n" ++
            "        b\"watch-payload\",\n" ++
            "        durability: .FastLocal,\n" ++
            "    ) catch {{ watcher.close(); return -45; }};\n" ++
            "    var watch_events = Vec[WatchEvent].new();\n" ++
            "    let polled_n: usize = watcher.poll_events(\n" ++
            "        &mut watch_events,\n" ++
            "        timeout: .Some(Duration.from_millis(250_u64)),\n" ++
            "    ) catch {{ watcher.close(); return -46; }};\n" ++
            "    watcher.unwatch(watch_id) catch {{ watcher.close(); return -47; }};\n" ++
            "    watcher.close();\n" ++
            "    if lock_conflict_ok and polled_n >= 1_usize and not watch_events.is_empty() and\n" ++
            "        watch_events.as_slice()[0].watch_id == watch_id\n" ++
            "    {{\n" ++
            "        score += 32;\n" ++
            "    }}\n\n" ++
            "    // [7] `FsDiagPathRing` failed-path capture + safety when `context.diagnostics` is a non-magic `8 B` struct:\n" ++
            "    var diag_ring = FsDiagPathRing {{\n" ++
            "        magic_tag: FS_DIAG_RING_MAGIC,\n" ++
            "        write_cursor: 0_u32,\n" ++
            "        reserved_word: 0_u32,\n" ++
            "        slots: [@default_init[FsDiagPathSlot](); 8],\n" ++
            "    }};\n" ++
            "    let ring_ptr: *mut FsDiagPathRing = &raw mut diag_ring;\n" ++
            "    let ring_sink: DiagSink = unsafe {{ ((&raw ring_ptr) as *DiagSink).read() }};\n" ++
            "    let missing_pb: PathBuf = join_work(\"missing_ring_target.cx\");\n" ++
            "    var ring_ok = false;\n" ++
            "    with context.diagnostics = ring_sink {{\n" ++
            "        match File.open(missing_pb.as_path()) {{\n" ++
            "            .Err(fe) => {{\n" ++
            "                let msg_txt: String = String.fmt(f\"{{fe}}\");\n" ++
            "                ring_ok = fe.kind() == .NotFound and\n" ++
            "                    fe.failed_path() == .Some(missing_pb.as_path()) and\n" ++
            "                    msg_txt.as_str().contains(\"missing_ring_target.cx\");\n" ++
            "            }},\n" ++
            "            .Ok(unexpected_f) => {{\n" ++
            "                unexpected_f.close();\n" ++
            "            }},\n" ++
            "        }}\n" ++
            "    }}\n" ++
            "    var non_magic_word = 0xCAFE_F00D_1234_5678_u64;\n" ++
            "    let non_magic_ptr: *mut u64 = &raw mut non_magic_word;\n" ++
            "    let foreign_sink: DiagSink = unsafe {{ ((&raw non_magic_ptr) as *DiagSink).read() }};\n" ++
            "    var foreign_safe = false;\n" ++
            "    with context.diagnostics = foreign_sink {{\n" ++
            "        match File.open(missing_pb.as_path()) {{\n" ++
            "            .Err(fe2) => {{\n" ++
            "                foreign_safe = fe2.failed_path() == .None and non_magic_word == 0xCAFE_F00D_1234_5678_u64;\n" ++
            "            }},\n" ++
            "            .Ok(unexpected_f2) => {{\n" ++
            "                unexpected_f2.close();\n" ++
            "            }},\n" ++
            "        }}\n" ++
            "    }}\n" ++
            "    if ring_ok and foreign_safe {{\n" ++
            "        score += 64;\n" ++
            "    }}\n\n" ++
            "    remove_dir_all(work_root.as_path()) catch {{}};\n" ++
            "    score\n" ++
            "}}\n",
        .{tmp_root},
    );
    defer allocator.free(gate4_probe_src);

    const gate4_app_src =
        "pub fn main() -> i32 {\n" ++
        "    cx.__std02_probe.run_gate4()\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    const std_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &db, 1, gate4_probe_src);
    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, gate4_app_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    try collectAllDiagnostics(&db, std_bundle.probe_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpDiagnostics("gate4_fs", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try runOracleDiagnosed(
        allocator,
        "gate4_fs",
        &db,
        app_fid,
        .{ .io = io, .extra_file_ids = std_bundle.asSlice() },
    );
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 127), report.outcomes[0].return_scalar_i64);
}

// ---------------- Gate 5: cx.env & cx.process -----------------

test "test_std02_gate5_env_process_zero_shell32_msvcrt_and_batbadbut" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const tmp_dir = try createIsolatedTmpDir(allocator, io, "gate5_proc");
    defer cleanupIsolatedTmpDir(allocator, io, tmp_dir);

    const default_corex_bin = if (builtin.os.tag == .windows)
        "build/stage0/corex.exe"
    else
        "build/stage0/corex";
    var has_stage0_bin = false;
    if (std.Io.Dir.cwd().openFile(io, default_corex_bin, .{ .mode = .read_only })) |existing_f| {
        existing_f.close(io);
        has_stage0_bin = true;
    } else |_| {}

    const fallback_bin = try std.fmt.allocPrint(
        allocator,
        "{s}/corex_ver_helper{s}",
        .{ tmp_dir, if (builtin.os.tag == .windows) ".exe" else "" },
    );
    defer allocator.free(fallback_bin);
    if (!has_stage0_bin) {
        var helper_db = try CompilerDb.init(allocator);
        defer helper_db.deinit();
        helper_db.setTargetSpec(TargetSpec.host());
        const helper_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &helper_db, 1, null);
        const helper_fid = FileId.fromInt(0);
        _ = try helper_db.setInput(
            helper_fid,
            "use cx.io.println;\npub fn main() -> i32 {\n    println(\"corex 0.1.0-helper\");\n    0\n}\n",
            .low,
        );
        var helper_art = try helper_db.compileModuleArtifact(
            helper_fid,
            .{ .tier_a_c99 = .{ .target = TargetSpec.host(), .is_release_mode = true, .has_line_directives = false } },
            .{
                .artifact_kind = .executable,
                .output_path = fallback_bin,
                .extra_file_ids = helper_bundle.asSlice(),
                .io = io,
            },
        );
        helper_art.deinit(allocator);
    }
    const target_child_bin: []const u8 = if (has_stage0_bin) default_corex_bin else fallback_bin;

    const gate5_probe_src = try std.fmt.allocPrint(
        allocator,
        "use cx.env.{{\n" ++
            "    VarError,\n" ++
            "    cache_dir,\n" ++
            "    config_dir,\n" ++
            "    current_dir,\n" ++
            "    current_exe,\n" ++
            "    data_local_dir,\n" ++
            "    get_var,\n" ++
            "    get_var_in,\n" ++
            "    get_var_os,\n" ++
            "    home_dir,\n" ++
            "    parse_win32_cmdline_in,\n" ++
            "    process_id,\n" ++
            "    remove_var,\n" ++
            "    set_var,\n" ++
            "    temp_dir,\n" ++
            "}};\n" ++
            "use cx.mem.Arena;\n" ++
            "use cx.path.{{Path, PathBuf}};\n" ++
            "use cx.process.{{Command, Output, Stdio}};\n" ++
            "use cx.str.String;\n\n" ++
            "const CHILD_EXE_PATH: str = \"{s}\";\n\n" ++
            "pub fn run_gate5() -> i32 {{\n" ++
            "    var score = 0;\n\n" ++
            "    // [1] `current_dir`, `current_exe`, `get_var*` (unset vs empty `\"\"` vs `InvalidName`), & standard dirs:\n" ++
            "    unsafe {{\n" ++
            "        remove_var(\"COREX_STD02_DEFINITELY_UNSET_VAR_991\") catch {{}};\n" ++
            "        set_var(\"COREX_STD02_EMPTY_TEST_VAR\", \"\") catch return -10;\n" ++
            "    }}\n" ++
            "    let cwd_pb: PathBuf = current_dir() catch return -1;\n" ++
            "    let exe_pb: PathBuf = current_exe() catch return -2;\n" ++
            "    var arena = Arena.new(slab_bytes: 8_192_usize);\n" ++
            "    let miss_v: String!VarError = get_var(\"COREX_STD02_DEFINITELY_UNSET_VAR_991\");\n" ++
            "    let miss_in_ok: bool = get_var_in(\n" ++
            "        &mut arena,\n" ++
            "        \"COREX_STD02_DEFINITELY_UNSET_VAR_991\",\n" ++
            "    ) == .Err(.NotPresent);\n" ++
            "    let miss_os: PathBuf? = get_var_os(\"COREX_STD02_DEFINITELY_UNSET_VAR_991\");\n" ++
            "    let empty_v: String!VarError = get_var(\"COREX_STD02_EMPTY_TEST_VAR\");\n" ++
            "    let empty_in_ok: bool = get_var_in(&mut arena, \"COREX_STD02_EMPTY_TEST_VAR\") == .Ok(\"\");\n" ++
            "    let bad_eq: String!VarError = get_var(\"=\");\n" ++
            "    let bad_kv: String!VarError = get_var(\"A=B\");\n" ++
            "    let bad_empty_in_ok: bool = get_var_in(&mut arena, \"\") == .Err(.InvalidName);\n" ++
            "    let _home_opt: PathBuf? = home_dir();\n" ++
            "    let _cache_opt: PathBuf? = cache_dir();\n" ++
            "    let _cfg_opt: PathBuf? = config_dir();\n" ++
            "    let _local_opt: PathBuf? = data_local_dir();\n" ++
            "    let tmp_pb: PathBuf = temp_dir();\n" ++
            "    if not cwd_pb.is_empty() and not exe_pb.is_empty() and not tmp_pb.is_empty() and\n" ++
            "        miss_v == .Err(.NotPresent) and miss_in_ok and miss_os == .None and\n" ++
            "        (empty_v is .Ok(ev_str) and ev_str.as_str() == \"\") and empty_in_ok and\n" ++
            "        bad_eq == .Err(.InvalidName) and bad_kv == .Err(.InvalidName) and\n" ++
            "        bad_empty_in_ok\n" ++
            "    {{\n" ++
            "        score += 1;\n" ++
            "    }}\n\n" ++
            "    // [2] `parse_win32_cmdline_in` MSVCRT `2n`/`2n+1` backslash & quote rules:\n" ++
            "    let raw_cmd_u16 = [\n" ++
            "        0x0022_u16, 0x0043_u16, 0x003A_u16, 0x005C_u16, 0x0062_u16, 0x0069_u16, 0x006E_u16, 0x005C_u16,\n" ++
            "        0x0061_u16, 0x0070_u16, 0x0070_u16, 0x002E_u16, 0x0065_u16, 0x0078_u16, 0x0065_u16, 0x0022_u16,\n" ++
            "        0x0020_u16, 0x0022_u16, 0x0061_u16, 0x005C_u16, 0x005C_u16, 0x005C_u16, 0x0022_u16, 0x0062_u16,\n" ++
            "        0x0022_u16, 0x0020_u16, 0x0022_u16, 0x0022_u16, 0x0020_u16, 0x0070_u16, 0x006C_u16, 0x0061_u16,\n" ++
            "        0x0069_u16,\n" ++
            "    ];\n" ++
            "    let parsed_argv: &[Path] = parse_win32_cmdline_in(&mut arena, &raw_cmd_u16);\n" ++
            "    if parsed_argv.len() == 4_usize and\n" ++
            "        parsed_argv[0].as_bytes() == \"C:\\\\bin\\\\app.exe\".as_bytes() and\n" ++
            "        parsed_argv[1].as_bytes() == \"a\\\\\\\"b\".as_bytes() and\n" ++
            "        parsed_argv[2].as_bytes() == \"\".as_bytes() and\n" ++
            "        parsed_argv[3].as_bytes() == \"plai\".as_bytes()\n" ++
            "    {{\n" ++
            "        score += 2;\n" ++
            "    }}\n" ++
            "    arena.release();\n\n" ++
            "    // [3] `process_id() > 0` + `Command.new(...).arg(\"--version\").stdout(Stdio.piped()).output()`:\n" ++
            "    let pid_val: u32 = process_id();\n" ++
            "    let ver_out: Output = Command.new(CHILD_EXE_PATH)\n" ++
            "        .arg(\"--version\")\n" ++
            "        .stdout(Stdio.piped())\n" ++
            "        .output() catch return -3;\n" ++
            "    if pid_val > 0_u32 and ver_out.status.is_success() and not ver_out.stdout.is_empty() {{\n" ++
            "        score += 4;\n" ++
            "    }}\n\n" ++
            "    // [4] `BatBadBut` (`CVE-2024-24576`) fail-closed `.bat`/`.cmd` rejection & `cmd_script` quote defense:\n" ++
            "    let rej_bat = Command.new(\"deploy.bat\").output();\n" ++
            "    let rej_cmd = Command.new(\"script.CMD\").output();\n" ++
            "    let rej_dots = Command.new(\"evil.bat .  \").output();\n" ++
            "    let rej_quote = Command.cmd_script(\"safe.bat\").arg(\"injected\\\"quote\").output();\n" ++
            "    if (rej_bat is .Err(e1) and e1.kind() == .InvalidScriptExtension) and\n" ++
            "        (rej_cmd is .Err(e2) and e2.kind() == .InvalidScriptExtension) and\n" ++
            "        (rej_dots is .Err(e3) and e3.kind() == .InvalidScriptExtension) and\n" ++
            "        (rej_quote is .Err(e4) and e4.kind() == .InvalidInput)\n" ++
            "    {{\n" ++
            "        score += 8;\n" ++
            "    }}\n\n" ++
            "    unsafe {{\n" ++
            "        remove_var(\"COREX_STD02_EMPTY_TEST_VAR\") catch {{}};\n" ++
            "    }}\n" ++
            "    score\n" ++
            "}}\n",
        .{target_child_bin},
    );
    defer allocator.free(gate5_probe_src);

    const gate5_app_src =
        "pub fn main() -> i32 {\n" ++
        "    cx.__std02_probe.run_gate5()\n" ++
        "}\n";

    var env_map = std.process.Environ.Map.init(allocator);
    defer env_map.deinit();
    try env_map.put("HOME", tmp_dir);
    try env_map.put("USERPROFILE", tmp_dir);
    try env_map.put("LOCALAPPDATA", tmp_dir);
    try env_map.put("APPDATA", tmp_dir);
    try env_map.put("TMPDIR", tmp_dir);
    try env_map.put("TEMP", tmp_dir);
    try env_map.put("TMP", tmp_dir);
    if (builtin.os.tag == .windows) {
        try env_map.put("SystemRoot", "C:\\Windows");
    }

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    const std_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &db, 1, gate5_probe_src);
    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, gate5_app_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    try collectAllDiagnostics(&db, std_bundle.probe_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpDiagnostics("gate5_env_proc", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try runOracleDiagnosed(
        allocator,
        "gate5_env_proc",
        &db,
        app_fid,
        .{ .io = io, .environ_map = &env_map, .extra_file_ids = std_bundle.asSlice() },
    );
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 15), report.outcomes[0].return_scalar_i64);

    if (builtin.os.tag == .windows) {
        const win_c_exe = try std.fmt.allocPrint(allocator, "{s}/gate5_pe_c99.exe", .{tmp_dir});
        defer allocator.free(win_c_exe);
        const win_ll_exe = try std.fmt.allocPrint(allocator, "{s}/gate5_pe_llvm.exe", .{tmp_dir});
        defer allocator.free(win_ll_exe);

        var pe_sink = DiagnosticSink.init(allocator);
        defer pe_sink.deinit();
        var pe_c_art = db.compileModuleArtifact(
            app_fid,
            .{ .tier_a_c99 = .{ .target = TargetSpec.host(), .is_release_mode = true, .has_line_directives = false } },
            .{
                .artifact_kind = .executable,
                .output_path = win_c_exe,
                .extra_file_ids = std_bundle.asSlice(),
                .io = io,
                .diagnostic_sink = &pe_sink,
            },
        ) catch |pe_err| {
            dumpDiagnostics("gate5_pe_c99", &pe_sink);
            return pe_err;
        };
        defer pe_c_art.deinit(allocator);
        var pe_ll_art = db.compileModuleArtifact(
            app_fid,
            .{ .tier_b_llvm = .{ .target = TargetSpec.host(), .is_release_mode = true } },
            .{
                .artifact_kind = .executable,
                .output_path = win_ll_exe,
                .extra_file_ids = std_bundle.asSlice(),
                .io = io,
                .diagnostic_sink = &pe_sink,
            },
        ) catch |pe_err| {
            dumpDiagnostics("gate5_pe_llvm", &pe_sink);
            return pe_err;
        };
        defer pe_ll_art.deinit(allocator);

        for ([_][]const u8{ win_c_exe, win_ll_exe }) |pe_path| {
            const pe_bytes = try std.Io.Dir.cwd().readFileAlloc(io, pe_path, allocator, .limited(16 * 1024 * 1024));
            defer allocator.free(pe_bytes);
            try verifyPe32PlusZeroShell32Imports(pe_bytes);
        }
    }
}

// ----------------- Gate 6: SimReactor Replay ------------------

test "test_std02_gate6_sim_reactor_virtual_clock_stdio_fault_replay_and_wasi" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const gate6_src =
        "use cx.async.{\n" ++
        "    IoSubmission,\n" ++
        "    Reactor,\n" ++
        "    ReactorCtx,\n" ++
        "    ReactorVTable,\n" ++
        "    SIM_OP_FS_CLOSE,\n" ++
        "    SIM_OP_FS_OPEN,\n" ++
        "    SIM_OP_FS_RW,\n" ++
        "    SIM_OP_SLEEP_NS,\n" ++
        "    SIM_OP_STDIO_RW,\n" ++
        "    SIM_UNHANDLED_SENTINEL,\n" ++
        "};\n" ++
        "use cx.fs.File;\n" ++
        "use cx.io.{stdin_locked, stdout_locked};\n" ++
        "use cx.time.{Duration, Instant, SystemTime, sleep};\n\n" ++
        "@repr(C)\n" ++
        "struct DetSimState {\n" ++
        "    mono_ns: u64,\n" ++
        "    wall_ns: i64,\n" ++
        "    prng: u64,\n" ++
        "    stdin_buf: [u8; 32],\n" ++
        "    stdin_len: usize,\n" ++
        "    stdin_pos: usize,\n" ++
        "    stdout_buf: [u8; 128],\n" ++
        "    stdout_len: usize,\n" ++
        "    eintr_injected: u32,\n" ++
        "    fault_injected: u32,\n" ++
        "    fs_bytes_written: usize,\n" ++
        "}\n\n" ++
        "@repr(C)\n" ++
        "struct DetReactorSlots {\n" ++
        "    monotonic_ns: (extern \"C\" fn(*mut opaque) -> u64)?,\n" ++
        "    wall_epoch_ns: (extern \"C\" fn(*mut opaque) -> i64)?,\n" ++
        "    fill_rng: usize,\n" ++
        "    submit_io: (extern \"C\" fn(*mut opaque, *IoSubmission) -> i64)?,\n" ++
        "    tail_slots: [usize; 4],\n" ++
        "}\n\n" ++
        "fn next_splitmix64(state: &mut u64, /) -> u64 {\n" ++
        "    state.* = state.* +% 0x9E37_79B9_7F4A_7C15_u64;\n" ++
        "    var z_val: u64 = state.*;\n" ++
        "    z_val = (z_val ^ (z_val >> 30_u64)) *% 0xBF58_476D_1CE4_E5B9_u64;\n" ++
        "    z_val = (z_val ^ (z_val >> 27_u64)) *% 0x94D0_49BB_1331_11EB_u64;\n" ++
        "    z_val ^ (z_val >> 31_u64)\n" ++
        "}\n\n" ++
        "extern \"C\" fn sim_mono_cb(ctx_raw: *mut opaque) -> u64 {\n" ++
        "    let st_ptr = ctx_raw as *mut DetSimState;\n" ++
        "    if st_ptr.is_null() {\n" ++
        "        return 0_u64;\n" ++
        "    }\n" ++
        "    unsafe { st_ptr.*.mono_ns }\n" ++
        "}\n\n" ++
        "extern \"C\" fn sim_wall_cb(ctx_raw: *mut opaque) -> i64 {\n" ++
        "    let st_ptr = ctx_raw as *mut DetSimState;\n" ++
        "    if st_ptr.is_null() {\n" ++
        "        return 0_i64;\n" ++
        "    }\n" ++
        "    unsafe { st_ptr.*.wall_ns }\n" ++
        "}\n\n" ++
        "extern \"C\" fn sim_submit_cb(ctx_raw: *mut opaque, sub_ptr: *IoSubmission) -> i64 {\n" ++
        "    let st_ptr = ctx_raw as *mut DetSimState;\n" ++
        "    if st_ptr.is_null() {\n" ++
        "        return SIM_UNHANDLED_SENTINEL;\n" ++
        "    }\n" ++
        "    if sub_ptr.is_null() {\n" ++
        "        return SIM_UNHANDLED_SENTINEL;\n" ++
        "    }\n" ++
        "    let st: &mut DetSimState = unsafe { &mut st_ptr.* };\n" ++
        "    let sub: IoSubmission = unsafe { sub_ptr.* };\n" ++
        "    if sub.kind == SIM_OP_SLEEP_NS {\n" ++
        "        st.mono_ns = st.mono_ns +% sub.offset_or_ns;\n" ++
        "        st.wall_ns = st.wall_ns +% (sub.offset_or_ns as i64);\n" ++
        "        return 0_i64;\n" ++
        "    }\n" ++
        "    if sub.kind == SIM_OP_STDIO_RW {\n" ++
        "        let cap = sub.buf_len as usize;\n" ++
        "        let buf_raw: *mut u8 = sub.buf_ptr;\n" ++
        "        if sub.flags == 0_u8 {\n" ++
        "            let avail: usize = st.stdin_len -| st.stdin_pos;\n" ++
        "            let take_n: usize = if avail < cap => avail else cap;\n" ++
        "            let in_base: *u8 = &raw st.stdin_buf[0];\n" ++
        "            if take_n > 0_usize and not buf_raw.is_null() and not in_base.is_null() {\n" ++
        "                unsafe {\n" ++
        "                    @memcpy(\n" ++
        "                        buf_raw as *mut opaque,\n" ++
        "                        in_base.add(st.stdin_pos) as *opaque,\n" ++
        "                        take_n,\n" ++
        "                    );\n" ++
        "                }\n" ++
        "                st.stdin_pos += take_n;\n" ++
        "            }\n" ++
        "            return take_n as i64;\n" ++
        "        }\n" ++
        "        let avail_out: usize = 128_usize -| st.stdout_len;\n" ++
        "        let copy_out: usize = if cap < avail_out => cap else avail_out;\n" ++
        "        let out_base: *mut u8 = &raw mut st.stdout_buf[0];\n" ++
        "        if copy_out > 0_usize and not buf_raw.is_null() and not out_base.is_null() {\n" ++
        "            unsafe {\n" ++
        "                @memcpy(\n" ++
        "                    out_base.add(st.stdout_len) as *mut opaque,\n" ++
        "                    buf_raw as *opaque,\n" ++
        "                    copy_out,\n" ++
        "                );\n" ++
        "            }\n" ++
        "            st.stdout_len += copy_out;\n" ++
        "        }\n" ++
        "        return cap as i64;\n" ++
        "    }\n" ++
        "    if sub.kind == SIM_OP_FS_OPEN {\n" ++
        "        return 42_i64;\n" ++
        "    }\n" ++
        "    if sub.kind == SIM_OP_FS_CLOSE {\n" ++
        "        return 0_i64;\n" ++
        "    }\n" ++
        "    if sub.kind == SIM_OP_FS_RW {\n" ++
        "        let roll: u64 = next_splitmix64(&mut st.prng);\n" ++
        "        if st.eintr_injected < 2_u32 and (roll & 3_u64) != 0_u64 {\n" ++
        "            st.eintr_injected += 1_u32;\n" ++
        "            return -4_i64;\n" ++
        "        }\n" ++
        "        if (roll & 7_u64) == 0_u64 {\n" ++
        "            st.fault_injected += 1_u32;\n" ++
        "            return -28_i64;\n" ++
        "        }\n" ++
        "        let chunk: usize = if (sub.buf_len as usize) > 3_usize => 3_usize else sub.buf_len as usize;\n" ++
        "        st.fs_bytes_written += chunk;\n" ++
        "        return chunk as i64;\n" ++
        "    }\n" ++
        "    SIM_UNHANDLED_SENTINEL\n" ++
        "}\n\n" ++
        "fn execute_sim_episode(seed: u64, /) -> u64 {\n" ++
        "    var state = DetSimState {\n" ++
        "        mono_ns: 1_000_000_000_u64,\n" ++
        "        wall_ns: 1_700_000_000_000_000_000_i64,\n" ++
        "        prng: seed,\n" ++
        "        stdin_buf: [0_u8; 32],\n" ++
        "        stdin_len: 10_usize,\n" ++
        "        stdin_pos: 0_usize,\n" ++
        "        stdout_buf: [0_u8; 128],\n" ++
        "        stdout_len: 0_usize,\n" ++
        "        eintr_injected: 0_u32,\n" ++
        "        fault_injected: 0_u32,\n" ++
        "        fs_bytes_written: 0_usize,\n" ++
        "    };\n" ++
        "    let feed_txt: &[u8] = \"sim-input\\n\".as_bytes();\n" ++
        "    unsafe {\n" ++
        "        @memcpy(\n" ++
        "            (&raw mut state.stdin_buf[0]) as *mut opaque,\n" ++
        "            feed_txt.as_ptr() as *opaque,\n" ++
        "            10_usize,\n" ++
        "        );\n" ++
        "    }\n" ++
        "    let slots = DetReactorSlots {\n" ++
        "        monotonic_ns: .Some(sim_mono_cb),\n" ++
        "        wall_epoch_ns: .Some(sim_wall_cb),\n" ++
        "        fill_rng: 0_usize,\n" ++
        "        submit_io: .Some(sim_submit_cb),\n" ++
        "        tail_slots: [0_usize; 4],\n" ++
        "    };\n" ++
        "    let reactor_val = Reactor { vtable: (&raw slots) as *ReactorVTable };\n" ++
        "    let ctx_val = ReactorCtx { state: (&raw mut state) as *mut opaque };\n\n" ++
        "    var digest = 0xCBF2_9CE4_8422_2325_u64;\n" ++
        "    with context.reactor = reactor_val {\n" ++
        "        with context.reactor_ctx = ctx_val {\n" ++
        "            let t_start = Instant.now();\n" ++
        "            let w_start = SystemTime.now();\n" ++
        "            sleep(Duration.from_secs(3_600_u64));\n" ++
        "            let elapsed_sim: Duration = Instant.now().duration_since(t_start);\n" ++
        "            let wall_sim: Duration = SystemTime.now().duration_since(w_start) catch Duration.ZERO;\n" ++
        "            if elapsed_sim.as_secs() != 3_600_u64 or wall_sim.as_secs() != 3_600_u64 {\n" ++
        "                return 0_u64;\n" ++
        "            }\n\n" ++
        "            var in_lock = stdin_locked();\n" ++
        "            var out_lock = stdout_locked();\n" ++
        "            if (in_lock.reader().next_line() catch .None) is .Some(line_txt) {\n" ++
        "                out_lock.print(f\"ack:{line_txt}\") catch {};\n" ++
        "            }\n" ++
        "            in_lock.release();\n" ++
        "            out_lock.flush_and_release() catch {};\n" ++
        "            let out_view: &[u8] = &state.stdout_buf;\n" ++
        "            if state.stdout_len != 13_usize or out_view[0..13] != \"ack:sim-input\".as_bytes() {\n" ++
        "                return 0_u64;\n" ++
        "            }\n\n" ++
        "            var sim_f: File = File.open(\"virtual/faults.bin\") catch return 0_u64;\n" ++
        "            var round = 0_usize;\n" ++
        "            while round < 16_usize {\n" ++
        "                match sim_f.write_all(b\"01234567\") {\n" ++
        "                    .Ok(_) => {\n" ++
        "                        digest = (digest ^ 0xA5_u64) *% 0x100_0000_01B3_u64;\n" ++
        "                    },\n" ++
        "                    .Err(io_err) => {\n" ++
        "                        if io_err.domain() != .SimFault or io_err.kind() != .StorageFull {\n" ++
        "                            sim_f.close();\n" ++
        "                            return 0_u64;\n" ++
        "                        }\n" ++
        "                        let raw_os: i32 = io_err.os_error() orelse 0;\n" ++
        "                        digest = (digest ^ (raw_os as u64)) *% 0x100_0000_01B3_u64;\n" ++
        "                    },\n" ++
        "                }\n" ++
        "                round += 1_usize;\n" ++
        "            }\n" ++
        "            sim_f.close();\n" ++
        "        }\n" ++
        "    }\n" ++
        "    if state.eintr_injected == 0_u32 or state.fs_bytes_written == 0_usize {\n" ++
        "        return 0_u64;\n" ++
        "    }\n" ++
        "    digest ^ (state.fs_bytes_written as u64) ^ ((state.eintr_injected as u64) << 16_u64)\n" ++
        "}\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    let run_a: u64 = execute_sim_episode(0x5EED_2026_1102_0001_u64);\n" ++
        "    let run_b: u64 = execute_sim_episode(0x5EED_2026_1102_0001_u64);\n" ++
        "    let run_c: u64 = execute_sim_episode(0x9999_AAAA_BBBB_CCCC_u64);\n" ++
        "    if run_a != 0_u64 and run_a == run_b and run_c != 0_u64 and run_a != run_c => 77 else -1\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    const std_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &db, 1, null);
    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, gate6_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpDiagnostics("gate6_sim", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try runOracleDiagnosed(
        allocator,
        "gate6_sim",
        &db,
        app_fid,
        .{ .io = io, .extra_file_ids = std_bundle.asSlice() },
    );
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 77), report.outcomes[0].return_scalar_i64);

    const tmp_dir = try createIsolatedTmpDir(allocator, io, "gate6_sim");
    defer cleanupIsolatedTmpDir(allocator, io, tmp_dir);
    const sim_exe = try std.fmt.allocPrint(
        allocator,
        "{s}/gate6_sim_native{s}",
        .{ tmp_dir, if (builtin.os.tag == .windows) ".exe" else "" },
    );
    defer allocator.free(sim_exe);
    var sim_art = try db.compileModuleArtifact(
        app_fid,
        .{ .tier_a_c99 = .{ .target = TargetSpec.host(), .is_release_mode = true, .has_line_directives = false } },
        .{ .artifact_kind = .executable, .output_path = sim_exe, .extra_file_ids = std_bundle.asSlice(), .io = io },
    );
    defer sim_art.deinit(allocator);

    const start_ts = std.Io.Clock.awake.now(io);
    const sim_run = try std.process.run(allocator, io, .{ .argv = &.{sim_exe} });
    const elapsed_ns = start_ts.untilNow(io, .awake).nanoseconds;
    defer allocator.free(sim_run.stdout);
    defer allocator.free(sim_run.stderr);
    try std.testing.expectEqual(std.process.Child.Term{ .exited = 77 }, sim_run.term);
    try std.testing.expect(elapsed_ns < 500 * std.time.ns_per_ms);

    // Cross-target `wasm32-unknown-wasi` verification across `cx.{io,path,fs,time,env,process}`:
    var wasi_db = try CompilerDb.init(allocator);
    defer wasi_db.deinit();
    wasi_db.setTargetSpec(TargetSpec.WASM32_WASI);
    const wasi_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &wasi_db, 1, null);
    const wasi_src =
        "use cx.env.{current_dir, get_var};\n" ++
        "use cx.fs.{Dir, File, load_file_thresholded};\n" ++
        "use cx.io.{BufReader, BufWriter, ByteReader, OutBuf, SliceWriter};\n" ++
        "use cx.mem.Arena;\n" ++
        "use cx.path.PathBuf;\n" ++
        "use cx.process.{Command, Stdio};\n" ++
        "use cx.time.{Duration, Instant, SystemTime, sleep};\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    var raw: [u8; 16];\n" ++
        "    var ob = OutBuf.over_uninit(&out raw);\n" ++
        "    _ = ob.append(b\"wasi\");\n" ++
        "    let pb = PathBuf.from(\"/sandbox/file.cx\");\n" ++
        "    let _t0 = Instant.now();\n" ++
        "    let _w0 = SystemTime.now();\n" ++
        "    sleep(Duration.ZERO);\n" ++
        "    if current_dir() is .Ok(_) {}\n" ++
        "    if get_var(\"HOME\") is .Ok(_) {}\n" ++
        "    if File.open(pb.as_path()) is .Ok(f_open) { f_open.close(); }\n" ++
        "    if Dir.open(\".\") is .Ok(d_open) { d_open.close(); }\n" ++
        "    var arena = Arena.new(slab_bytes: 4_096_usize);\n" ++
        "    if load_file_thresholded(&mut arena, pb.as_path()) is .Ok(loaded) { loaded.close(); }\n" ++
        "    arena.release();\n" ++
        "    if Command.new(\"tool\").stdout(Stdio.null()).status() is .Ok(_) {}\n" ++
        "    var dst = [0_u8; 16];\n" ++
        "    var sw = SliceWriter.new(&mut dst);\n" ++
        "    var bw = BufWriter.new(sw.as_writer());\n" ++
        "    bw.discard();\n" ++
        "    var br = ByteReader.new(b\"ok\\n\");\n" ++
        "    var buf_r = BufReader.new(br.as_reader());\n" ++
        "    if buf_r.next_line() is .Ok(_) {}\n" ++
        "    ob.filled_len() as i32\n" ++
        "}\n";
    const wasi_fid = FileId.fromInt(0);
    _ = try wasi_db.setInput(wasi_fid, wasi_src, .low);

    var wasi_sink = DiagnosticSink.init(allocator);
    defer wasi_sink.deinit();
    var wasi_c_art = try wasi_db.compileModuleArtifact(
        wasi_fid,
        .{ .tier_a_c99 = .{ .target = TargetSpec.WASM32_WASI, .is_release_mode = true, .has_line_directives = false } },
        .{ .artifact_kind = .source_text, .extra_file_ids = wasi_bundle.asSlice(), .diagnostic_sink = &wasi_sink },
    );
    defer wasi_c_art.deinit(allocator);
    var wasi_ll_art = try wasi_db.compileModuleArtifact(
        wasi_fid,
        .{ .tier_b_llvm = .{ .target = TargetSpec.WASM32_WASI, .is_release_mode = true } },
        .{ .artifact_kind = .source_text, .extra_file_ids = wasi_bundle.asSlice(), .diagnostic_sink = &wasi_sink },
    );
    defer wasi_ll_art.deinit(allocator);
    if (wasi_sink.diagnostics.items.len > 0) dumpDiagnostics("gate6_wasi", &wasi_sink);
    try std.testing.expectEqual(@as(usize, 0), wasi_sink.diagnostics.items.len);
    try std.testing.expect(std.mem.indexOf(u8, wasi_ll_art.emitted_text, "wasm32-unknown-wasi") != null);
}

// --------------- Gate 7: Negative Safety Matrix ---------------

test "test_std02_gate7_negative_compile_fail_linear_caps_noblock_outbuf_comptime" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    db.setSastStrict(true);
    const std_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &db, 1, null);
    const app_fid = FileId.fromInt(0);

    const NegCase = struct {
        label: []const u8,
        source: []const u8,
        expected: DiagnosticCode,
        needs_module_compile: bool = false,
    };

    const neg_cases = [_]NegCase{
        // [A] All 11 `@linear` resource leak cases (`E0304`):
        .{
            .label = "linear_leak_file",
            .source = "use cx.fs.File;\npub fn leak_file(file: own File) { _ = file.as_raw_fd(); }\n",
            .expected = .e0304_resource_or_memory_leak,
        },
        .{
            .label = "linear_leak_dir",
            .source = "use cx.fs.Dir;\npub fn leak_dir(dir: own Dir) { _ = dir.as_raw_fd(); }\n",
            .expected = .e0304_resource_or_memory_leak,
        },
        .{
            .label = "linear_leak_mmap",
            .source = "use cx.fs.Mmap;\npub fn leak_mmap(mapped: own Mmap) -> usize { mapped.len() }\n",
            .expected = .e0304_resource_or_memory_leak,
        },
        .{
            .label = "linear_leak_bufwriter",
            .source = "use cx.io.{BufWriter, Writer};\npub fn leak_bw() { let _bw = BufWriter.new(Writer.sink()); }\n",
            .expected = .e0304_resource_or_memory_leak,
        },
        .{
            .label = "linear_leak_child_process",
            .source = "use cx.process.ChildProcess;\npub fn leak_child(child: own ChildProcess) -> u32 { child.pid }\n",
            .expected = .e0304_resource_or_memory_leak,
        },
        .{
            .label = "linear_leak_stdin_lock",
            .source = "use cx.io.stdin_locked;\npub fn leak_stdin() { let _lk = stdin_locked(); }\n",
            .expected = .e0304_resource_or_memory_leak,
        },
        .{
            .label = "linear_leak_stdout_lock",
            .source = "use cx.io.stdout_locked;\npub fn leak_stdout() { let _lk = stdout_locked(); }\n",
            .expected = .e0304_resource_or_memory_leak,
        },
        .{
            .label = "linear_leak_file_lock",
            .source = "use cx.fs.FileLock;\npub fn leak_flock(flock: own FileLock) {}\n",
            .expected = .e0304_resource_or_memory_leak,
        },
        .{
            .label = "linear_leak_fs_watcher",
            .source = "use cx.fs.FsWatcher;\npub fn leak_watcher(watcher: own FsWatcher) {}\n",
            .expected = .e0304_resource_or_memory_leak,
        },
        .{
            .label = "linear_leak_staged_atomic",
            .source = "use cx.fs.StagedAtomicFile;\npub fn leak_staged(staged: own StagedAtomicFile) {}\n",
            .expected = .e0304_resource_or_memory_leak,
        },
        .{
            .label = "linear_leak_stdio_piped",
            .source = "use cx.process.Stdio;\npub fn leak_stdio() { let _piped = Stdio.piped(); }\n",
            .expected = .e0304_resource_or_memory_leak,
        },

        // [B] `@no_block` violations (`E0322`) calling blocking `cx.fs`, `cx.time`, and `cx.process` APIs:
        .{
            .label = "noblock_fs_open",
            .source = "use cx.fs.File;\n@no_block\npub fn bad_nb_fs() {\n    if File.open(\"a.txt\") is .Ok(file) { file.close(); }\n}\n",
            .expected = .e0322_no_block_contract_violation,
        },
        .{
            .label = "noblock_time_sleep",
            .source = "use cx.time.{Duration, sleep};\n@no_block\npub fn bad_nb_sleep() { sleep(Duration.from_millis(1_u64)); }\n",
            .expected = .e0322_no_block_contract_violation,
        },
        .{
            .label = "noblock_process_status",
            .source = "use cx.process.Command;\n@no_block\npub fn bad_nb_proc() {\n    if Command.new(\"tool\").status() is .Ok(_) {}\n}\n",
            .expected = .e0322_no_block_contract_violation,
        },

        // [C] `OutBuf` / `&out` soundness (`E0305` concurrent borrow, `E0306` escape, `E0422` fn-pointer reification):
        .{
            .label = "outbuf_concurrent_borrow_e0305",
            .source = "use cx.io.OutBuf;\npub fn bad_alias() -> usize {\n" ++
                "    var raw = [0_u8; 32];\n" ++
                "    var out_buf = OutBuf.over_uninit(&out raw);\n" ++
                "    let shared: &[u8] = &raw;\n" ++
                "    _ = out_buf.append(b\"x\");\n" ++
                "    shared.len()\n}\n",
            .expected = .e0305_exclusivity_violation,
            .needs_module_compile = true,
        },
        .{
            .label = "outbuf_escape_local_array_e0306",
            .source = "use cx.io.OutBuf;\npub fn bad_escape() -> OutBuf {\n" ++
                "    var local_raw: [u8; 32];\n" ++
                "    OutBuf.over_uninit(&out local_raw)\n}\n",
            .expected = .e0306_region_escape_violation,
            .needs_module_compile = true,
        },
        .{
            .label = "outbuf_reify_fnptr_e0422",
            .source = "use cx.io.OutBuf;\npub fn bad_fnptr_outbuf() -> usize {\n" ++
                "    let ctor: fn(&out [u8; 32]) -> OutBuf = OutBuf.over_uninit[32];\n" ++
                "    var raw: [u8; 32];\n" ++
                "    ctor(&out raw).capacity()\n}\n",
            .expected = .e0422_out_param_contract_violation,
        },
        .{
            .label = "bufreader_reify_fnptr_e0422",
            .source = "use cx.io.{BufReader, Reader};\npub fn bad_fnptr_bufrd() -> usize {\n" ++
                "    let ctor: fn(Reader, &out [u8; 32]) -> BufReader = BufReader.over_uninit[32];\n" ++
                "    var raw: [u8; 32];\n" ++
                "    ctor(Reader.empty(), &out raw).capacity()\n}\n",
            .expected = .e0422_out_param_contract_violation,
        },
        .{
            .label = "bufwriter_reify_fnptr_e0422",
            .source = "use cx.io.{BufWriter, Writer};\npub fn bad_fnptr_bufwr() {\n" ++
                "    let ctor = BufWriter.over_uninit[32];\n" ++
                "    _ = ctor;\n" ++
                "    _ = Writer.sink();\n}\n",
            .expected = .e0422_out_param_contract_violation,
        },

        // [D] `comptime` hermeticity (`E0325` / `E0503` on host OS I/O or clocks inside `comptime`):
        .{
            .label = "comptime_hermetic_fs_open",
            .source = "use cx.fs.File;\nconst BAD_CT_FS: i32 = comptime {\n" ++
                "    if File.open(\"Cargo.toml\") is .Ok(file) { file.close(); }\n" ++
                "    1\n};\npub fn main() -> i32 { BAD_CT_FS }\n",
            .expected = .e0503_forbidden_comptime_operation,
            .needs_module_compile = true,
        },
        .{
            .label = "comptime_hermetic_instant_now",
            .source = "use cx.time.Instant;\nconst BAD_CT_CLK: u64 = comptime {\n" ++
                "    let now_val = Instant.now();\n" ++
                "    now_val.elapsed().as_nanos()\n};\npub fn main() -> i32 { BAD_CT_CLK as i32 }\n",
            .expected = .e0503_forbidden_comptime_operation,
            .needs_module_compile = true,
        },
    };

    for (neg_cases) |case_item| {
        _ = try db.setInput(app_fid, case_item.source, .low);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        if (case_item.needs_module_compile) {
            _ = db.compileModuleArtifact(
                app_fid,
                .{ .tier_a_c99 = .{ .target = TargetSpec.host(), .is_release_mode = false, .has_line_directives = false } },
                .{ .artifact_kind = .source_text, .extra_file_ids = std_bundle.asSlice(), .diagnostic_sink = &sink },
            ) catch {};
            const proj_sink = try db.projectFileDiagnostics(app_fid);
            for (proj_sink.diagnostics.items) |diag_item| {
                _ = try sink.emit(diag_item);
            }
        } else {
            try collectAllDiagnostics(&db, app_fid, &sink);
        }
        const matched = sinkHasCode(&sink, case_item.expected) or
            (case_item.expected == .e0503_forbidden_comptime_operation and
                sinkHasCode(&sink, .e0325_comptime_sandbox_violation));
        if (!matched) {
            dumpDiagnostics(case_item.label, &sink);
        }
        try std.testing.expect(matched);
    }

    // [E] `DR-17` Package Capability Sandbox (`E0324`) for `fs`, `env`, `process`, and `clock`:
    const CapViolationCase = struct {
        label: []const u8,
        source: []const u8,
        denied_cap_bit: u16,
    };
    const cap_cases = [_]CapViolationCase{
        .{
            .label = "cap_deny_fs_e0324",
            .source = "use cx.fs.File;\npub fn touch_fs() {\n    if File.open(\"x.txt\") is .Ok(file) { file.close(); }\n}\n",
            .denied_cap_bit = (mir_sast.EffectCapabilityMask{ .fs = true }).asBits(),
        },
        .{
            .label = "cap_deny_env_e0324",
            .source = "use cx.env.get_var;\npub fn touch_env() -> bool { get_var(\"PATH\") is .Ok(_) }\n",
            .denied_cap_bit = (mir_sast.EffectCapabilityMask{ .env = true }).asBits(),
        },
        .{
            .label = "cap_deny_process_e0324",
            .source = "use cx.process.Command;\npub fn touch_proc() { if Command.new(\"corex\").status() is .Ok(_) {} }\n",
            .denied_cap_bit = (mir_sast.EffectCapabilityMask{ .process = true }).asBits(),
        },
        .{
            .label = "cap_deny_clock_e0324",
            .source = "use cx.time.Instant;\npub fn touch_clock() -> u64 { Instant.now().elapsed().as_nanos() }\n",
            .denied_cap_bit = (mir_sast.EffectCapabilityMask{ .clock = true }).asBits(),
        },
    };

    db.setPackageGraphMounted(true);
    const sandbox_pkg = PackageId.fromInt(2);
    const sandbox_fid = FileId.fromInt(900);
    try db.registerPackageRootFile(sandbox_pkg, sandbox_fid);

    for (cap_cases) |cap_case| {
        _ = try db.setInput(sandbox_fid, cap_case.source, .low);
        const allow_bits: u16 = 0x0FFF & ~cap_case.denied_cap_bit;
        try db.setPackageCapPolicy(sandbox_pkg, .{
            .package_name = "sandboxed-dep@1.0.0",
            .policy_span = Span.init(sandbox_fid, 0, 12),
            .allowed_caps = mir_sast.EffectCapabilityMask.fromBits(allow_bits),
            .is_third_party_dependency = true,
            .enforcement_scope = .surface,
        });

        var files_map: std.AutoHashMapUnmanaged(PackageId, []const FileId) = .empty;
        defer files_map.deinit(allocator);
        try files_map.put(allocator, sandbox_pkg, &.{sandbox_fid});

        var cap_sink = DiagnosticSink.init(allocator);
        defer cap_sink.deinit();
        const cap_reports = try db.verifyWorkspaceCapabilitySandbox(
            allocator,
            &.{sandbox_pkg},
            &files_map,
            &.{},
            &cap_sink,
        );
        defer allocator.free(cap_reports);
        if (!sinkHasCode(&cap_sink, .e0324_package_capability_violation)) {
            dumpDiagnostics(cap_case.label, &cap_sink);
        }
        try std.testing.expect(sinkHasCode(&cap_sink, .e0324_package_capability_violation));
    }
}

test "test_std02_cross_module_from_error_fserror_to_ioerror_upcast_4tier" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const upcast_src =
        "use cx.fs.{Dir, File};\n" ++
        "use cx.io.IoError;\n\n" ++
        "fn try_open_missing_file() -> usize!IoError {\n" ++
        "    let handle = File.open(\"__cx_std02_missing_from_error_probe__.bin\")?;\n" ++
        "    handle.close();\n" ++
        "    .Ok(1_usize)\n" ++
        "}\n\n" ++
        "fn try_open_missing_dir() -> usize!IoError {\n" ++
        "    Dir.open(\"__cx_std02_missing_from_error_dir__\")?.close();\n" ++
        "    .Ok(2_usize)\n" ++
        "}\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    var score = 0;\n" ++
        "    if try_open_missing_file() is .Err(file_err) and\n" ++
        "        file_err.kind() == .NotFound and file_err.op() == .Open\n" ++
        "    {\n" ++
        "        score += 10;\n" ++
        "    }\n" ++
        "    if try_open_missing_dir() is .Err(dir_err) and\n" ++
        "        dir_err.kind() == .NotFound and dir_err.op() == .Open\n" ++
        "    {\n" ++
        "        score += 21;\n" ++
        "    }\n" ++
        "    score\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    const std_bundle = try mountStdCoreAndCxIntoDb(allocator, io, &db, 1, null);
    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, upcast_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpDiagnostics("from_error_fserror_to_ioerror", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try runOracleDiagnosed(
        allocator,
        "from_error_fserror_to_ioerror",
        &db,
        app_fid,
        .{ .io = io, .extra_file_ids = std_bundle.asSlice() },
    );
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 31), report.outcomes[0].return_scalar_i64);
}

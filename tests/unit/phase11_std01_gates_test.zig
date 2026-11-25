//! Phase 11.1 (`STD-01` §3.3) Five-Gate Verification & Red-Team Regression Suite
//!
//! Proves all five mandatory `STD-01.md` §3.3 architectural verification gates alongside Stage-4
//! red-team regressions and Stage-0 SAST/LLVM seam fixes:
//! - Stage-4 red-team regressions (`CRITICAL-01`, `CRITICAL-02`, `CRITICAL-05`, `CRITICAL-06`,
//!   `HIGH-01`..`HIGH-05`) and Stage-0 `Pool.free`, `OwnPtr[T]` provenance, and scalar `const` load,
//! - Gate 1: Zero pre-`main` static initializers across ELF64, Mach-O 64, PE32+/COFF, and Wasm,
//! - Gate 2: Pointer-shape ICF deduplication across 50 nominal `Map[u64, *T_0..*T_49]` types,
//! - Gate 3: Scratch exclusivity (`E0328`) compile-fail guards and `--sim --seed` determinism/OOM,
//! - Gate 4: Pentagon `< 2 MB` RAM and `0` residual inner-loop traps across all 10 hot functions,
//! - Gate 5: 4-tier `GraphemeBreakTest` (1,675 UCD 16.0 vectors) + IEEE-754 float/math parity and
//!   `< 10,240 B` freestanding `wasm32` Profiles A, B, and C with `0` host imports and `0` `start`.
//!
//! All temporary native/cross-target artifacts are isolated inside `.zig-cache/` and cleaned up.

const std = @import("std");
const corex = @import("corex");
const grapheme_ucd16 = @import("grapheme_ucd16_vectors.zig");

const FileId = corex.FileId;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const DiagnosticCode = corex.DiagnosticCode;
const TargetSpec = corex.TargetSpec;

// ---------------------------------------- TYPES ----------------------------------------

/// Parsed summary of a `.wasm` binary inspected by Gate 1 and Gate 5.
const WasmBinarySummary = struct {
    /// Total `.wasm` file size in bytes.
    byte_size: usize,
    /// Total count of imported host functions/globals/memories/tables in Section 2 (`Import`).
    import_count: u32,
    /// `true` if Section 8 (`Start`) is present anywhere in the module.
    has_start_section: bool,
    /// `true` if `__wasm_call_ctors` is exported and contains any `call` / `call_indirect` opcode.
    has_nonempty_wasm_call_ctors: bool,
};

/// Unique `.text` virtual-address counts for the four `RawTableInner` polymorphic kernels in Gate 2.
const IcfKernelCounts = struct {
    /// Unique `.text` addresses for `RawTableInner.find_raw`.
    find_raw_addrs: usize,
    /// Unique `.text` addresses for `RawTableInner.find_or_prepare_insert_raw`.
    find_or_prepare_addrs: usize,
    /// Unique `.text` addresses for `RawTableInner.erase_slot_ctrl`.
    erase_slot_addrs: usize,
    /// Unique `.text` addresses for `RawTableInner.rehash_or_grow_raw`.
    rehash_or_grow_addrs: usize,
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

/// Canonical Phase 11.1 (`STD-01`) `stdlib/cx/` source file paths (`5` files).
const CX_STDLIB_PATHS = [_][]const u8{
    "stdlib/cx/mod.cx",
    "stdlib/cx/mem.cx",
    "stdlib/cx/math.cx",
    "stdlib/cx/col.cx",
    "stdlib/cx/str.cx",
};

/// All 10 mandatory Gate-4 hot functions from `STD-01.md` §3.3 #4.
const GATE4_HOT_FUNCTIONS = [_][]const u8{
    "alloc_raw",
    "find_raw",
    "partition_lomuto_branchless_cyclic",
    "partition_point",
    "is_valid_utf8",
    "char_width",
    "grapheme_class",
    "schubfach_to_decimal_f64",
    "eisel_lemire_f64",
    "format_u32_jeaiii",
};

// -------------------------------------- INTERNALS --------------------------------------

// --------------- CompilerDb Mounting & Helpers ----------------

/// Normalizes CRLF line endings in `raw_bytes` to LF for OS-agnostic source loading.
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

/// Mounts all `core/**/*.cx` and `stdlib/cx/*.cx` files into `db` as `.std_core`.
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

/// Collects all frontend, typecheck, and SAST diagnostics for `fid` into `out_sink`.
fn collectAllDiagnostics(db: *CompilerDb, fid: FileId, out_sink: *DiagnosticSink) !void {
    const parsed = try db.parseCst(fid);
    for (parsed.diagnostics.diagnostics.items) |diag_item| try out_sink.emit(diag_item);

    _ = try db.resolveSignatures(fid);
    if (db.getSignatureDiagnostics(fid)) |sig_sink| {
        for (sig_sink.diagnostics.items) |diag_item| try out_sink.emit(diag_item);
    }

    const tree = try db.extractItemTree(fid);
    var def_ids = try db.allocator.alloc(corex.DefId, tree.entries.len);
    defer db.allocator.free(def_ids);
    for (tree.entries, 0..) |entry, i| def_ids[i] = entry.def_id;

    for (def_ids) |def_id| {
        _ = try db.typecheckBody(def_id);
        if (db.getBodyDiagnostics(def_id)) |body_sink| {
            for (body_sink.diagnostics.items) |diag_item| try out_sink.emit(diag_item);
        }
        _ = try db.verifySastMir(def_id);
        if (db.getSastDiagnostics(def_id)) |sast_sink| {
            for (sast_sink.diagnostics.items) |diag_item| try out_sink.emit(diag_item);
        }
    }
}

/// Returns `true` if `sink` contains at least one diagnostic with `expected_code`.
fn sinkHasCode(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == expected_code) return true;
    }
    return false;
}

/// Prints unexpected diagnostics to debug output for clear failure triage.
fn dumpDiagnostics(label: []const u8, sink: *const DiagnosticSink) void {
    for (sink.diagnostics.items) |diag_item| {
        std.debug.print(
            "[{s}] {s}: {s}\n",
            .{ label, @tagName(diag_item.code), diag_item.message },
        );
    }
}

// --------------- Binary Format Section Parsers ----------------

/// Decodes an unsigned 32-bit LEB128 integer at `bytes[cursor.*..]` and advances `cursor`.
fn readUleb128(bytes: []const u8, cursor: *usize) !u32 {
    var result: u32 = 0;
    var shift: u5 = 0;
    var count: usize = 0;
    while (cursor.* < bytes.len and count < 5) : (count += 1) {
        const byte_val = bytes[cursor.*];
        cursor.* += 1;
        result |= @as(u32, byte_val & 0x7F) << shift;
        if ((byte_val & 0x80) == 0) return result;
        if (shift <= 21) shift += 7;
    }
    return error.InvalidLeb128;
}

/// Asserts that an ELF64 object or executable contains zero `.init_array`, `.ctors`, or `SHT_INIT_ARRAY`.
fn verifyElf64ZeroStaticInitializers(elf_bytes: []const u8) !void {
    try std.testing.expect(elf_bytes.len >= 64);
    try std.testing.expectEqualSlices(u8, "\x7FELF", elf_bytes[0..4]);
    try std.testing.expectEqual(@as(u8, 2), elf_bytes[4]);
    try std.testing.expectEqual(@as(u8, 1), elf_bytes[5]);

    const shoff: usize = @intCast(std.mem.readInt(u64, elf_bytes[0x28..0x30], .little));
    const shentsize: usize = std.mem.readInt(u16, elf_bytes[0x3A..0x3C], .little);
    const shnum: usize = std.mem.readInt(u16, elf_bytes[0x3C..0x3E], .little);
    const shstrndx: usize = std.mem.readInt(u16, elf_bytes[0x3E..0x40], .little);

    try std.testing.expect(shentsize >= 64);
    try std.testing.expect(shoff + shnum * shentsize <= elf_bytes.len);
    try std.testing.expect(shstrndx < shnum);

    const str_hdr_off = shoff + shstrndx * shentsize;
    const str_off: usize = @intCast(
        std.mem.readInt(u64, elf_bytes[str_hdr_off + 24 ..][0..8], .little),
    );
    const str_size: usize = @intCast(
        std.mem.readInt(u64, elf_bytes[str_hdr_off + 32 ..][0..8], .little),
    );
    try std.testing.expect(str_off + str_size <= elf_bytes.len);
    const shstrtab = elf_bytes[str_off .. str_off + str_size];

    for (0..shnum) |sec_i| {
        const hdr_off = shoff + sec_i * shentsize;
        const name_idx: usize = std.mem.readInt(u32, elf_bytes[hdr_off..][0..4], .little);
        const sh_type = std.mem.readInt(u32, elf_bytes[hdr_off + 4 ..][0..4], .little);
        const sh_size = std.mem.readInt(u64, elf_bytes[hdr_off + 32 ..][0..8], .little);

        // `SHT_INIT_ARRAY = 14`, `SHT_PREINIT_ARRAY = 16`:
        if (sh_type == 14 or sh_type == 16) {
            try std.testing.expectEqual(@as(u64, 0), sh_size);
        }
        if (name_idx < shstrtab.len) {
            const rem = shstrtab[name_idx..];
            const nul_pos = std.mem.indexOfScalar(u8, rem, 0) orelse rem.len;
            const sec_name = rem[0..nul_pos];
            const is_init_sec = std.mem.eql(u8, sec_name, ".init_array") or
                std.mem.startsWith(u8, sec_name, ".init_array.") or
                std.mem.eql(u8, sec_name, ".ctors") or
                std.mem.startsWith(u8, sec_name, ".ctors.");
            if (is_init_sec) {
                try std.testing.expectEqual(@as(u64, 0), sh_size);
            }
        }
    }
}

/// Counts unique `.text` virtual addresses for the four `RawTableInner` kernels in an ELF64 binary.
fn countElf64UniqueTextSymbols(
    allocator: std.mem.Allocator,
    elf_bytes: []const u8,
) !IcfKernelCounts {
    try std.testing.expect(elf_bytes.len >= 64);
    try std.testing.expectEqualSlices(u8, "\x7FELF", elf_bytes[0..4]);

    const shoff: usize = @intCast(std.mem.readInt(u64, elf_bytes[0x28..0x30], .little));
    const shentsize: usize = std.mem.readInt(u16, elf_bytes[0x3A..0x3C], .little);
    const shnum: usize = std.mem.readInt(u16, elf_bytes[0x3C..0x3E], .little);

    var find_addrs: std.AutoHashMapUnmanaged(u64, void) = .empty;
    defer find_addrs.deinit(allocator);
    var prep_addrs: std.AutoHashMapUnmanaged(u64, void) = .empty;
    defer prep_addrs.deinit(allocator);
    var erase_addrs: std.AutoHashMapUnmanaged(u64, void) = .empty;
    defer erase_addrs.deinit(allocator);
    var rehash_addrs: std.AutoHashMapUnmanaged(u64, void) = .empty;
    defer rehash_addrs.deinit(allocator);

    for (0..shnum) |sec_i| {
        const hdr_off = shoff + sec_i * shentsize;
        const sh_type = std.mem.readInt(u32, elf_bytes[hdr_off + 4 ..][0..4], .little);
        // `SHT_SYMTAB = 2`:
        if (sh_type != 2) continue;

        const sym_off: usize = @intCast(
            std.mem.readInt(u64, elf_bytes[hdr_off + 24 ..][0..8], .little),
        );
        const sym_size: usize = @intCast(
            std.mem.readInt(u64, elf_bytes[hdr_off + 32 ..][0..8], .little),
        );
        const link_sec: usize = std.mem.readInt(u32, elf_bytes[hdr_off + 40 ..][0..4], .little);
        const entsize: usize = @intCast(
            std.mem.readInt(u64, elf_bytes[hdr_off + 56 ..][0..8], .little),
        );
        if (entsize < 24 or link_sec >= shnum) continue;

        const str_hdr = shoff + link_sec * shentsize;
        const str_off: usize = @intCast(
            std.mem.readInt(u64, elf_bytes[str_hdr + 24 ..][0..8], .little),
        );
        const str_size: usize = @intCast(
            std.mem.readInt(u64, elf_bytes[str_hdr + 32 ..][0..8], .little),
        );
        const strtab = elf_bytes[str_off .. str_off + str_size];

        const sym_count = sym_size / entsize;
        for (0..sym_count) |sym_i| {
            const entry_off = sym_off + sym_i * entsize;
            const st_name: usize = std.mem.readInt(u32, elf_bytes[entry_off..][0..4], .little);
            const st_info = elf_bytes[entry_off + 4];
            const st_shndx = std.mem.readInt(u16, elf_bytes[entry_off + 6 ..][0..2], .little);
            const st_value = std.mem.readInt(u64, elf_bytes[entry_off + 8 ..][0..8], .little);
            // Only defined `STT_FUNC` (`2`) symbols in allocated sections:
            if ((st_info & 0x0F) != 2 or st_shndx == 0 or st_name >= strtab.len) continue;

            const rem = strtab[st_name..];
            const nul_pos = std.mem.indexOfScalar(u8, rem, 0) orelse rem.len;
            const sym_name = rem[0..nul_pos];

            if (std.mem.indexOf(u8, sym_name, "find_or_prepare_insert_raw") != null) {
                try prep_addrs.put(allocator, st_value, {});
            } else if (std.mem.indexOf(u8, sym_name, "find_raw") != null) {
                try find_addrs.put(allocator, st_value, {});
            } else if (std.mem.indexOf(u8, sym_name, "erase_slot_ctrl") != null) {
                try erase_addrs.put(allocator, st_value, {});
            } else if (std.mem.indexOf(u8, sym_name, "rehash_or_grow_raw") != null) {
                try rehash_addrs.put(allocator, st_value, {});
            }
        }
    }

    return .{
        .find_raw_addrs = find_addrs.count(),
        .find_or_prepare_addrs = prep_addrs.count(),
        .erase_slot_addrs = erase_addrs.count(),
        .rehash_or_grow_addrs = rehash_addrs.count(),
    };
}

/// Asserts that a Mach-O 64 image or object contains zero `__mod_init_func` (`0x09`) sections.
fn verifyMachO64ZeroStaticInitializers(macho_bytes: []const u8) !void {
    try std.testing.expect(macho_bytes.len >= 32);
    const magic = std.mem.readInt(u32, macho_bytes[0..4], .little);
    try std.testing.expectEqual(@as(u32, 0xFEED_FACF), magic);

    const ncmds: usize = std.mem.readInt(u32, macho_bytes[16..20], .little);
    var cmd_off: usize = 32;
    for (0..ncmds) |_| {
        try std.testing.expect(cmd_off + 8 <= macho_bytes.len);
        const cmd = std.mem.readInt(u32, macho_bytes[cmd_off..][0..4], .little);
        const cmdsize: usize = std.mem.readInt(u32, macho_bytes[cmd_off + 4 ..][0..4], .little);
        try std.testing.expect(cmdsize >= 8 and cmd_off + cmdsize <= macho_bytes.len);

        // `LC_SEGMENT_64 = 0x19`:
        if (cmd == 0x19) {
            try std.testing.expect(cmdsize >= 72);
            const nsects: usize = std.mem.readInt(u32, macho_bytes[cmd_off + 64 ..][0..4], .little);
            try std.testing.expect(72 + nsects * 80 <= cmdsize);
            for (0..nsects) |sec_i| {
                const sec_off = cmd_off + 72 + sec_i * 80;
                const raw_sectname = macho_bytes[sec_off .. sec_off + 16];
                const nul_pos = std.mem.indexOfScalar(u8, raw_sectname, 0) orelse 16;
                const sectname = raw_sectname[0..nul_pos];
                const sec_size = std.mem.readInt(u64, macho_bytes[sec_off + 40 ..][0..8], .little);
                const sec_flags = std.mem.readInt(u32, macho_bytes[sec_off + 64 ..][0..4], .little);

                // `S_MOD_INIT_FUNC_POINTERS = 0x09`:
                if ((sec_flags & 0xFF) == 0x09 or std.mem.eql(u8, sectname, "__mod_init_func")) {
                    try std.testing.expectEqual(@as(u64, 0), sec_size);
                }
            }
        }
        cmd_off += cmdsize;
    }
}

/// Asserts that a COFF `.obj` or PE32+ `.exe` contains zero `.CRT$XCU` static constructor sections.
fn verifyCoffOrPeZeroStaticInitializers(bin_bytes: []const u8) !void {
    try std.testing.expect(bin_bytes.len >= 20);
    var coff_off: usize = 0;
    if (bin_bytes.len >= 0x40 and std.mem.eql(u8, bin_bytes[0..2], "MZ")) {
        const pe_off: usize = std.mem.readInt(u32, bin_bytes[0x3C..0x40], .little);
        try std.testing.expect(pe_off + 24 <= bin_bytes.len);
        try std.testing.expectEqualSlices(u8, "PE\x00\x00", bin_bytes[pe_off .. pe_off + 4]);
        coff_off = pe_off + 4;
    }

    const num_sections: usize = std.mem.readInt(u16, bin_bytes[coff_off + 2 ..][0..2], .little);
    const symtab_off: usize = std.mem.readInt(u32, bin_bytes[coff_off + 8 ..][0..4], .little);
    const num_syms: usize = std.mem.readInt(u32, bin_bytes[coff_off + 12 ..][0..4], .little);
    const opt_hdr_sz: usize = std.mem.readInt(u16, bin_bytes[coff_off + 16 ..][0..2], .little);

    const sec_table_off = coff_off + 20 + opt_hdr_sz;
    try std.testing.expect(sec_table_off + num_sections * 40 <= bin_bytes.len);

    const strtab_off: usize = if (symtab_off != 0) symtab_off + num_syms * 18 else 0;

    for (0..num_sections) |sec_i| {
        const sh_off = sec_table_off + sec_i * 40;
        const raw_name = bin_bytes[sh_off .. sh_off + 8];
        const virt_sz = std.mem.readInt(u32, bin_bytes[sh_off + 8 ..][0..4], .little);
        const raw_sz = std.mem.readInt(u32, bin_bytes[sh_off + 16 ..][0..4], .little);
        const eff_sz = @max(virt_sz, raw_sz);

        var sec_name: []const u8 = raw_name[0 .. std.mem.indexOfScalar(u8, raw_name, 0) orelse 8];
        if (raw_name[0] == '/' and strtab_off > 0 and strtab_off < bin_bytes.len) {
            if (std.fmt.parseInt(usize, sec_name[1..], 10)) |str_rel| {
                const abs_str = strtab_off + str_rel;
                if (abs_str < bin_bytes.len) {
                    const rem = bin_bytes[abs_str..];
                    const end_nul = std.mem.indexOfScalar(u8, rem, 0) orelse rem.len;
                    sec_name = rem[0..end_nul];
                }
            } else |_| {}
        }

        const is_ctor = std.mem.startsWith(u8, sec_name, ".CRT$XC") or
            std.mem.startsWith(u8, sec_name, ".ctors") or
            std.mem.startsWith(u8, sec_name, ".init_array");
        if (is_ctor) {
            try std.testing.expectEqual(@as(u32, 0), eff_sz);
        }
    }
}

/// Parses a `.wasm` binary to verify header validity, import count, `start` section, and ctors.
fn inspectWasmBinary(wasm_bytes: []const u8) !WasmBinarySummary {
    try std.testing.expect(wasm_bytes.len >= 8);
    try std.testing.expectEqualSlices(u8, "\x00asm\x01\x00\x00\x00", wasm_bytes[0..8]);

    var cursor: usize = 8;
    var import_count: u32 = 0;
    var imported_fn_count: u32 = 0;
    var has_start_section = false;
    var exported_ctors_fn_idx: ?u32 = null;
    var has_nonempty_ctors = false;

    while (cursor < wasm_bytes.len) {
        const section_id = wasm_bytes[cursor];
        cursor += 1;
        const payload_len: usize = @intCast(try readUleb128(wasm_bytes, &cursor));
        try std.testing.expect(cursor + payload_len <= wasm_bytes.len);
        const sec_end = cursor + payload_len;

        if (section_id == 2) {
            // Section 2 (`Import`):
            var imp_cur = cursor;
            const vec_n = try readUleb128(wasm_bytes, &imp_cur);
            import_count += vec_n;
            for (0..vec_n) |_| {
                const mod_len: usize = @intCast(try readUleb128(wasm_bytes, &imp_cur));
                imp_cur += mod_len;
                const name_len: usize = @intCast(try readUleb128(wasm_bytes, &imp_cur));
                imp_cur += name_len;
                const kind = wasm_bytes[imp_cur];
                imp_cur += 1;
                if (kind == 0) {
                    _ = try readUleb128(wasm_bytes, &imp_cur);
                    imported_fn_count += 1;
                } else {
                    break;
                }
            }
        } else if (section_id == 7) {
            // Section 7 (`Export`):
            var exp_cur = cursor;
            const exp_n = try readUleb128(wasm_bytes, &exp_cur);
            for (0..exp_n) |_| {
                const name_len: usize = @intCast(try readUleb128(wasm_bytes, &exp_cur));
                const exp_name = wasm_bytes[exp_cur .. exp_cur + name_len];
                exp_cur += name_len;
                const exp_kind = wasm_bytes[exp_cur];
                exp_cur += 1;
                const exp_idx = try readUleb128(wasm_bytes, &exp_cur);
                if (exp_kind == 0 and std.mem.eql(u8, exp_name, "__wasm_call_ctors")) {
                    exported_ctors_fn_idx = exp_idx;
                }
            }
        } else if (section_id == 8) {
            has_start_section = true;
        } else if (section_id == 10) {
            // Section 10 (`Code`): if `__wasm_call_ctors` was exported, verify its body has 0 calls:
            if (exported_ctors_fn_idx) |ctors_idx| {
                if (ctors_idx >= imported_fn_count) {
                    const local_fn_ord = ctors_idx - imported_fn_count;
                    var code_cur = cursor;
                    const body_n = try readUleb128(wasm_bytes, &code_cur);
                    for (0..body_n) |body_i| {
                        const body_sz: usize = @intCast(try readUleb128(wasm_bytes, &code_cur));
                        const body_slice = wasm_bytes[code_cur .. code_cur + body_sz];
                        if (body_i == local_fn_ord) {
                            // Empty Wasm function body is `0x00 0x0B` (`0` locals + `end`):
                            if (body_slice.len > 2) has_nonempty_ctors = true;
                        }
                        code_cur += body_sz;
                    }
                }
            }
        }
        cursor = sec_end;
    }

    return .{
        .byte_size = wasm_bytes.len,
        .import_count = import_count,
        .has_start_section = has_start_section,
        .has_nonempty_wasm_call_ctors = has_nonempty_ctors,
    };
}

/// Counts residual bounds-check, checked-subtraction, or trap ops inside a post-SAST `MirBody`.
fn countResidualTrapsInBody(body_ptr: *const corex.MirBody) usize {
    var residual_traps: usize = 0;
    for (0..body_ptr.insts.len) |inst_i| {
        const inst = body_ptr.insts.get(inst_i);
        switch (inst.op) {
            .intrinsic_op => {
                const ikind: corex.mir.MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                if (ikind == .bounds_check or ikind == .slice_range_check or
                    ikind == .narrow_check or ikind == .trap or ikind == .panic)
                {
                    residual_traps += 1;
                }
            },
            .bin_op => {
                const bkind: corex.BinOpKind = @fromBackingInt(
                    @intCast(@as(u8, @truncate(inst.aux_u16))),
                );
                if (bkind == .ssub_checked or bkind == .usub_checked) {
                    residual_traps += 1;
                }
            },
            else => {},
        }
    }
    for (body_ptr.blocks.items) |blk| {
        if (blk.terminator.kind == .trap) {
            residual_traps += 1;
        }
    }
    return residual_traps;
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------ Red-Team & Stage-0 Seam Regressions -------------

test "test_phase11_std01_red_team_stage4_regressions_and_stage0_seams" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

    // Build `"0." ++ 400 zeros ++ "1e401"` literal for `HIGH-04` extreme canceled-exponent parse:
    const zeros_400: [400]u8 = @splat('0');
    const reg_src =
        "use cx.math;\n" ++
        "use cx.mem.{Arena, FixedBuffer, Layout, OwnPtr, Pool, System};\n" ++
        "use cx.str;\n" ++
        "\n" ++
        "comptime fn compute_scalar_const() -> f64 {\n" ++
        "    var total: f64 = 1.25;\n" ++
        "    var step = 0_usize;\n" ++
        "    while step < 3_usize {\n" ++
        "        total += 0.25;\n" ++
        "        step += 1_usize;\n" ++
        "    }\n" ++
        "    total\n" ++
        "}\n" ++
        "\n" ++
        "const GLOBAL_MAGIC_SCALE: f64 = compute_scalar_const();\n" ++
        "\n" ++
        "pub struct BadRawUtf8 {}\n" ++
        "impl Display for BadRawUtf8 {\n" ++
        "    pub fn fmt(&self, out: &mut FmtWriter, spec: FmtSpec, /) -> unit!FmtError {\n" ++
        "        _ = spec;\n" ++
        "        out.write_bytes(&[0xFF_u8])\n" ++
        "    }\n" ++
        "}\n" ++
        "\n" ++
        "pub struct SplitFourByteUtf8 {}\n" ++
        "impl Display for SplitFourByteUtf8 {\n" ++
        "    pub fn fmt(&self, out: &mut FmtWriter, spec: FmtSpec, /) -> unit!FmtError {\n" ++
        "        _ = spec;\n" ++
        "        out.write_bytes(&[0xF0_u8, 0x9F_u8])?;\n" ++
        "        out.write_bytes(&[0x98_u8, 0x80_u8])\n" ++
        "    }\n" ++
        "}\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    // [1] Seam 3: scalar `const` lowered through comptime evaluation (`GLOBAL_MAGIC_SCALE == 2.0`):\n" ++
        "    if GLOBAL_MAGIC_SCALE != 2.0 { return 1; }\n" ++
        "\n" ++
        // [2] Seam 1 & 2 + CRITICAL-02: `Pool[u64]` multi-slot checkout without E0305/UAF:
        "    var pool_err: i32 = 0;\n" ++
        "    var pool = Pool[u64].new(items_per_slab: 8_u32);\n" ++
        "    let item_a = pool.alloc(10_u64);\n" ++
        "    let item_b = pool.alloc(20_u64);\n" ++
        "    if item_a.as_ref().* + item_b.as_ref().* != 30_u64 { pool_err = 2; }\n" ++
        "    if pool.live_len() != 2_usize { pool_err = 3; }\n" ++
        "    pool.free(own item_a);\n" ++
        "    pool.free(own item_b);\n" ++
        "    if pool.live_len() != 0_usize { pool_err = 4; }\n" ++
        "    own pool.release();\n" ++
        "    if pool_err != 0 { return pool_err; }\n" ++
        "\n" ++
        "    // [3] CRITICAL-02b: `OwnPtr.new` inside `with context.allocator = arena.as_handle()` freed outside:\n" ++
        "    var temp_arena = Arena.with_capacity(4096_usize) catch { return 5; };\n" ++
        "    let escaped_box = with context.allocator = temp_arena.as_handle() {\n" ++
        "        OwnPtr[u64].new(777_u64)\n" ++
        "    };\n" ++
        "    own temp_arena.release();\n" ++
        "    if (own escaped_box).into_inner() != 777_u64 { return 6; }\n" ++
        "\n" ++
        "    // [4] CRITICAL-05: `String.in_arena(&mut arena)` empty `\"\"` + `.push_str(> 64 B)` stays in `arena`:\n" ++
        "    var str_arena = Arena.with_capacity(16384_usize) catch { return 7; };\n" ++
        "    var tiny_ctx_bytes: [u8; 8] = [0_u8; 8];\n" ++
        "    var tiny_ctx_fb = FixedBuffer.init(&mut tiny_ctx_bytes);\n" ++
        "    var arena_str_ok = false;\n" ++
        "    {\n" ++
        "        with context.allocator = tiny_ctx_fb.as_handle() {\n" ++
        "            var arena_text = String.in_arena(&mut str_arena);\n" ++
        "            let expected_payload = \"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_arena_growth_payload!\";\n" ++
        "            arena_text.push_str(expected_payload);\n" ++
        "            arena_str_ok = arena_text.len() == 84_usize and arena_text.as_str() == expected_payload;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    own str_arena.release();\n" ++
        "    if tiny_ctx_fb.remaining() != 8_usize or not arena_str_ok { return 8; }\n" ++
        "\n" ++
        "    // [5] CRITICAL-06: `format_into` rejects invalid UTF-8 (`0xFF`) and accepts split 4-byte UTF-8:\n" ++
        "    var fmt_buf: [u8; 32] = [0_u8; 32];\n" ++
        "    let bad_val = BadRawUtf8 {};\n" ++
        "    match str.format_into(&mut fmt_buf, f\"{bad_val}\") {\n" ++
        "        .Ok(_) => return 10,\n" ++
        "        .Err(err_kind) => if err_kind != .IoFailure { return 11; },\n" ++
        "    }\n" ++
        "    let split_val = SplitFourByteUtf8 {};\n" ++
        "    let ok_utf8 = str.format_into(&mut fmt_buf, f\"{split_val}\") catch { return 12; };\n" ++
        "    let ok_bytes = ok_utf8.as_bytes();\n" ++
        "    if ok_bytes.len() != 4_usize or ok_bytes[0] != 0xF0_u8 or ok_bytes[3] != 0x80_u8 { return 13; }\n" ++
        "\n" ++
        "    // [6] CRITICAL-01: normal `str.join` and `str.join_in`:\n" ++
        "    var join_ok = false;\n" ++
        "    var join_arena = Arena.new();\n" ++
        "    {\n" ++
        "        let joined_arena = str.join_in(&mut join_arena, &[\"cx\", \"std\", \"01\"], \"::\");\n" ++
        "        let joined_heap = str.join(&[\"cx\", \"std\", \"01\"], \"::\");\n" ++
        "        join_ok = joined_arena == \"cx::std::01\" and joined_heap.as_str() == \"cx::std::01\";\n" ++
        "    }\n" ++
        "    own join_arena.release();\n" ++
        "    if not join_ok { return 14; }\n" ++
        "\n" ++
        "    // [7] HIGH-01..HIGH-05: math & float boundary edge cases + `System` 64K/128K align + `FixedBuffer` TLS:\n" ++
        "    let max_f64 = @bit_cast[f64](0x7FEF_FFFF_FFFF_FFFF_u64);\n" ++
        "    let inf_f64 = @bit_cast[f64](0x7FF0_0000_0000_0000_u64);\n" ++
        "    if math.approx_eq_ulp(max_f64, inf_f64) { return 15; }\n" ++
        "    if @bit_cast[u64](math.powf(2.0, 1.0e301)) != 0x7FF0_0000_0000_0000_u64 { return 16; }\n" ++
        "    let neg_zero_rad: f64 = math.degrees_to_radians(-0.0);\n" ++
        "    if @bit_cast[u64](neg_zero_rad) != 0x8000_0000_0000_0000_u64 { return 17; }\n" ++
        "    if not math.is_finite(math.degrees_to_radians(1.0e302)) { return 18; }\n" ++
        "    if math.approx_eq_rel(-1.0e308, 0.9e308, rel_tol: 1.85) { return 19; }\n" ++
        "    let canceled_exp: f64 = str.parse_float[f64](\"0." ++ (&zeros_400) ++ "1e401\") catch { return 20; };\n" ++
        "    if canceled_exp != 1.0 { return 21; }\n" ++
        "\n" ++
        "    let lay64k = Layout { size: 256_usize, alignment: 65_536_usize };\n" ++
        "    let ptr64k = System.handle().alloc(lay64k) catch { return 22; };\n" ++
        "    if ((ptr64k as usize) & 65_535_usize) != 0_usize { return 23; }\n" ++
        "    System.handle().dealloc(ptr64k, lay64k);\n" ++
        "\n" ++
        "    let lay128k = Layout { size: 256_usize, alignment: 131_072_usize };\n" ++
        "    let ptr128k = System.handle().alloc(lay128k) catch { return 24; };\n" ++
        "    if ((ptr128k as usize) & 131_071_usize) != 0_usize { return 25; }\n" ++
        "    System.handle().dealloc(ptr128k, lay128k);\n" ++
        "\n" ++
        "    let tls_ptr = @tls_alloc_state() as *u8;\n" ++
        "    var tls_before: [u8; 256] = [0_u8; 256];\n" ++
        "    var byte_i = 0_usize;\n" ++
        "    while byte_i < 256_usize {\n" ++
        "        tls_before[byte_i] = unsafe { tls_ptr.add(byte_i).read() };\n" ++
        "        byte_i += 1_usize;\n" ++
        "    }\n" ++
        "    var stack_backing: [u8; 256] = [0_u8; 256];\n" ++
        "    var fixed_buf = FixedBuffer.init(&mut stack_backing);\n" ++
        "    let fb_handle = fixed_buf.as_handle();\n" ++
        "    let fb_lay = Layout { size: 32_usize, alignment: 8_usize };\n" ++
        "    let fb_ptr = fb_handle.alloc(fb_lay) catch { return 26; };\n" ++
        "    let _resized = fb_handle.resize_in_place(fb_ptr, fb_lay, 64_usize);\n" ++
        "    fb_handle.dealloc(fb_ptr, Layout { size: 64_usize, alignment: 8_usize });\n" ++
        "    byte_i = 0_usize;\n" ++
        "    while byte_i < 256_usize {\n" ++
        "        if tls_before[byte_i] != unsafe { tls_ptr.add(byte_i).read() } { return 27; }\n" ++
        "        byte_i += 1_usize;\n" ++
        "    }\n" ++
        "    0\n" ++
        "}\n";

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, reg_src, .low);
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpDiagnostics("red_team_reg", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, app_fid, .{ .io = io });
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 0), report.outcomes[0].return_scalar_i64);

    // Also verify CRITICAL-01 `cx.str.join` overflow guard deterministically traps across all 4 tiers:
    const join_ovf_src =
        "use cx.str;\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    let sample: [str; 1] = [\"abcd\"];\n" ++
        "    let huge_count: usize = ((isize.MAX as usize) / 4_usize) + 8_usize;\n" ++
        "    let fake_parts: &[str] = unsafe {\n" ++
        "        @slice_from_raw_parts(&raw sample[0], huge_count)\n" ++
        "    };\n" ++
        "    let joined = str.join(fake_parts, \"abcd\");\n" ++
        "    return joined.len() as i32;\n" ++
        "}\n";
    const ovf_fid = FileId.fromInt(1);
    _ = try db.setInput(ovf_fid, join_ovf_src, .low);
    var ovf_report = try corex.runFourTierDiffOracleOnDb(allocator, &db, ovf_fid, .{ .io = io });
    defer ovf_report.deinit(allocator);
    try std.testing.expect(ovf_report.is_all_matching);
    try std.testing.expect(ovf_report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i32, 101), ovf_report.outcomes[0].exit_code);
}

// ------- Gate 1: Zero Pre-main Static Initializers Gate -------

test "test_phase11_std01_gate1_zero_pre_main_static_initializers" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const scratch_dir = ".zig-cache/test_std01_gate1";
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, scratch_dir);

    const gate1_free_src =
        "use cx.math;\n" ++
        "use cx.mem.{Arena, System};\n" ++
        "use cx.str;\n" ++
        "\n" ++
        "@export\n" ++
        "@link(name: \"cx_gate1_entry\")\n" ++
        "pub fn cx_gate1_entry() -> u64 {\n" ++
        "    var arena = Arena.new();\n" ++
        "    var looked_up: u64 = 0_u64;\n" ++
        "    var text_len: usize = 0_usize;\n" ++
        "    {\n" ++
        "        var items = Vec[u64].in_arena(&mut arena);\n" ++
        "        items.push(42_u64);\n" ++
        "        let first_item = items[0];\n" ++
        "        var table = Map[u64, u64].in_arena(&mut arena);\n" ++
        "        _ = table.insert(7_u64, first_item);\n" ++
        "        if table.get(&7_u64) is .Some(found_ptr) { looked_up = found_ptr.*; }\n" ++
        "        var text = String.in_arena(&mut arena, \"hello\");\n" ++
        "        text.push_str(\"_world\");\n" ++
        "        text_len = text.len();\n" ++
        "    }\n" ++
        "    own arena.release();\n" ++
        "    var fbuf: [u8; 32] = [0_u8; 32];\n" ++
        "    let rendered = str.format_float(&mut fbuf, math.sin(0.5) + math.exp(1.0)) catch { return 0_u64; };\n" ++
        "    var gcount: usize = 0_usize;\n" ++
        "    for _ in rendered.graphemes() { gcount += 1_usize; }\n" ++
        "    let width_val: usize = (str.char_width('A') as usize) + gcount;\n" ++
        "    let _sys = System.handle();\n" ++
        "    return looked_up + (text_len as u64) + (width_val as u64);\n" ++
        "}\n";
    const gate1_src =
        "use cx.math;\n" ++
        "use cx.mem.{Arena, System, with_scratch};\n" ++
        "use cx.str;\n" ++
        "\n" ++
        "@export\n" ++
        "@link(name: \"cx_gate1_entry\")\n" ++
        "pub fn cx_gate1_entry() -> u64 {\n" ++
        "    var first_item: u64 = 0_u64;\n" ++
        "    var arena = Arena.new();\n" ++
        "    {\n" ++
        "        var items = Vec[u64].in_arena(&mut arena);\n" ++
        "        items.push(42_u64);\n" ++
        "        first_item = items[0];\n" ++
        "    }\n" ++
        "    own arena.release();\n" ++
        "    var table = Map[u64, u64].new();\n" ++
        "    _ = table.insert(7_u64, first_item);\n" ++
        "    let scratch_len: usize = with_scratch(|scratch: &mut Arena| {\n" ++
        "        scratch.dupe_str(\"corex\").len()\n" ++
        "    });\n" ++
        "    var text = String.from_str(\"hello\");\n" ++
        "    text.push_str(\"_world\");\n" ++
        "    var fbuf: [u8; 32] = [0_u8; 32];\n" ++
        "    let rendered = str.format_float(&mut fbuf, math.sin(0.5) + math.exp(1.0)) catch { return 0_u64; };\n" ++
        "    var gcount: usize = 0_usize;\n" ++
        "    for _ in rendered.graphemes() { gcount += 1_usize; }\n" ++
        "    let width_val: usize = (str.char_width('A') as usize) + gcount + scratch_len;\n" ++
        "    let _sys = System.handle();\n" ++
        "    let looked_up: u64 = if table.get(&7_u64) is .Some(found_ptr) { found_ptr.* } else { 0_u64 };\n" ++
        "    return looked_up + (text.len() as u64) + (width_val as u64);\n" ++
        "}\n";
    const gate1_wasi_src = gate1_src ++
        "\npub fn main() -> i32 {\n" ++
        "    return (cx_gate1_entry() & 0x7F_u64) as i32;\n" ++
        "}\n";

    const app_fid = FileId.fromInt(0);

    // [1] ELF64 (`x86_64-linux-musl` object + linked ELF64 image):
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.X86_64_LINUX_MUSL);
        _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);
        _ = try db.setInput(app_fid, gate1_src, .low);

        const elf_obj_path = scratch_dir ++ "/gate1_linux.o";
        const elf_bin_path = scratch_dir ++ "/gate1_linux.elf";
        var art = try db.compileModuleArtifact(app_fid, .{
            .tier_b_llvm = .{
                .target = TargetSpec.X86_64_LINUX_MUSL,
                .opt_level = .release_fast_o2,
                .is_release_mode = true,
            },
        }, .{
            .module_name = "gate1_linux",
            .artifact_kind = .object_file,
            .output_path = elf_obj_path,
            .io = io,
        });
        defer art.deinit(allocator);

        const obj_bytes = try std.Io.Dir.cwd().readFileAlloc(io, elf_obj_path, allocator, .limited(16 * 1024 * 1024));
        defer allocator.free(obj_bytes);
        try verifyElf64ZeroStaticInitializers(obj_bytes);

        var exe_art = try db.compileModuleArtifact(app_fid, .{
            .tier_b_llvm = .{
                .target = TargetSpec.X86_64_LINUX_MUSL,
                .opt_level = .release_fast_o2,
                .is_release_mode = true,
            },
        }, .{
            .module_name = "gate1_linux_so",
            .artifact_kind = .shared_library,
            .output_path = elf_bin_path,
            .io = io,
        });
        defer exe_art.deinit(allocator);
        const bin_bytes = try std.Io.Dir.cwd().readFileAlloc(io, elf_bin_path, allocator, .limited(16 * 1024 * 1024));
        defer allocator.free(bin_bytes);
        try verifyElf64ZeroStaticInitializers(bin_bytes);
    }

    // [2] Mach-O 64 (`aarch64-apple-darwin` object):
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.AARCH64_APPLE_DARWIN);
        _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);
        _ = try db.setInput(app_fid, gate1_src, .low);

        const macho_obj_path = scratch_dir ++ "/gate1_darwin.o";
        var art = try db.compileModuleArtifact(app_fid, .{
            .tier_b_llvm = .{
                .target = TargetSpec.AARCH64_APPLE_DARWIN,
                .opt_level = .release_fast_o2,
                .is_release_mode = true,
            },
        }, .{
            .module_name = "gate1_darwin",
            .artifact_kind = .object_file,
            .output_path = macho_obj_path,
            .io = io,
        });
        defer art.deinit(allocator);

        const macho_bytes = try std.Io.Dir.cwd().readFileAlloc(
            io,
            macho_obj_path,
            allocator,
            .limited(16 * 1024 * 1024),
        );
        defer allocator.free(macho_bytes);
        try verifyMachO64ZeroStaticInitializers(macho_bytes);
    }

    // [3] PE32+ / COFF (`x86_64-windows-msvc` `.obj` + linked `x86_64-windows-gnu` PE32+ `.dll`):
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.X86_64_WINDOWS_MSVC);
        _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);
        _ = try db.setInput(app_fid, gate1_src, .low);

        const coff_obj_path = scratch_dir ++ "/gate1_win.obj";
        var art = try db.compileModuleArtifact(app_fid, .{
            .tier_b_llvm = .{
                .target = TargetSpec.X86_64_WINDOWS_MSVC,
                .opt_level = .release_fast_o2,
                .is_release_mode = true,
            },
        }, .{
            .module_name = "gate1_win",
            .artifact_kind = .object_file,
            .output_path = coff_obj_path,
            .io = io,
        });
        defer art.deinit(allocator);

        const coff_bytes = try std.Io.Dir.cwd().readFileAlloc(io, coff_obj_path, allocator, .limited(16 * 1024 * 1024));
        defer allocator.free(coff_bytes);
        try verifyCoffOrPeZeroStaticInitializers(coff_bytes);

        var gnu_db = try CompilerDb.init(allocator);
        defer gnu_db.deinit();
        gnu_db.setTargetSpec(TargetSpec.X86_64_WINDOWS_GNU);
        _ = try mountStdCoreAndCxIntoDb(allocator, io, &gnu_db, 10);
        _ = try gnu_db.setInput(app_fid, gate1_src, .low);

        const pe_dll_path = scratch_dir ++ "/gate1_win.dll";
        var pe_art = try gnu_db.compileModuleArtifact(app_fid, .{
            .tier_b_llvm = .{
                .target = TargetSpec.X86_64_WINDOWS_GNU,
                .opt_level = .release_fast_o2,
                .is_release_mode = true,
            },
        }, .{
            .module_name = "gate1_win_dll",
            .artifact_kind = .shared_library,
            .output_path = pe_dll_path,
            .io = io,
        });
        defer pe_art.deinit(allocator);
        const pe_bytes = try std.Io.Dir.cwd().readFileAlloc(io, pe_dll_path, allocator, .limited(16 * 1024 * 1024));
        defer allocator.free(pe_bytes);
        try verifyCoffOrPeZeroStaticInitializers(pe_bytes);
    }

    // [4] WebAssembly (`wasm32-unknown-freestanding` & `wasm32-unknown-wasi`):
    {
        var free_db = try CompilerDb.init(allocator);
        defer free_db.deinit();
        free_db.setTargetSpec(TargetSpec.WASM32_UNKNOWN_FREESTANDING);
        _ = try mountStdCoreAndCxIntoDb(allocator, io, &free_db, 10);
        _ = try free_db.setInput(app_fid, gate1_free_src, .low);

        const wasm_free_path = scratch_dir ++ "/gate1_free.wasm";
        var free_art = try free_db.compileModuleArtifact(app_fid, .{
            .tier_b_llvm = .{
                .target = TargetSpec.WASM32_UNKNOWN_FREESTANDING,
                .opt_level = .release_small_oz,
                .is_release_mode = true,
            },
        }, .{
            .module_name = "gate1_free",
            .artifact_kind = .executable,
            .output_path = wasm_free_path,
            .io = io,
        });
        defer free_art.deinit(allocator);

        const free_bytes = try std.Io.Dir.cwd().readFileAlloc(
            io,
            wasm_free_path,
            allocator,
            .limited(16 * 1024 * 1024),
        );
        defer allocator.free(free_bytes);
        const free_sum = try inspectWasmBinary(free_bytes);
        try std.testing.expectEqual(@as(u32, 0), free_sum.import_count);
        try std.testing.expect(!free_sum.has_start_section);
        try std.testing.expect(!free_sum.has_nonempty_wasm_call_ctors);

        var wasi_db = try CompilerDb.init(allocator);
        defer wasi_db.deinit();
        wasi_db.setTargetSpec(TargetSpec.WASM32_UNKNOWN_WASI);
        _ = try mountStdCoreAndCxIntoDb(allocator, io, &wasi_db, 10);
        _ = try wasi_db.setInput(app_fid, gate1_wasi_src, .low);

        const wasm_wasi_path = scratch_dir ++ "/gate1_wasi.wasm";
        var wasi_art = try wasi_db.compileModuleArtifact(app_fid, .{
            .tier_b_llvm = .{
                .target = TargetSpec.WASM32_UNKNOWN_WASI,
                .opt_level = .release_small_oz,
                .is_release_mode = true,
            },
        }, .{
            .module_name = "gate1_wasi",
            .artifact_kind = .executable,
            .output_path = wasm_wasi_path,
            .io = io,
        });
        defer wasi_art.deinit(allocator);

        const wasi_bytes = try std.Io.Dir.cwd().readFileAlloc(
            io,
            wasm_wasi_path,
            allocator,
            .limited(16 * 1024 * 1024),
        );
        defer allocator.free(wasi_bytes);
        const wasi_sum = try inspectWasmBinary(wasi_bytes);
        try std.testing.expect(!wasi_sum.has_start_section);
        try std.testing.expect(!wasi_sum.has_nonempty_wasm_call_ctors);
    }
}

// -------- Gate 2: Pointer-Shape ICF Deduplication Gate --------

test "test_phase11_std01_gate2_pointer_shape_icf_deduplication" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const scratch_dir = ".zig-cache/test_std01_gate2";
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, scratch_dir);

    // Generate 50 distinct nominal struct types `Node0..Node49` and 50 `Map[u64, *Node_i]` instances:
    var src_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer src_buf.deinit(allocator);
    for (0..50) |i| {
        try src_buf.print(
            allocator,
            "pub struct Node{d} {{ pub val: u64 }}\n",
            .{i},
        );
    }
    try src_buf.appendSlice(allocator, "\npub fn main() -> i32 {\n    var acc: u64 = 0_u64;\n");
    for (0..50) |i| {
        try src_buf.print(
            allocator,
            "    let item_{d} = Node{d} {{ val: {d}_u64 }};\n" ++
                "    var map_{d} = Map[u64, *Node{d}].new();\n" ++
                "    _ = map_{d}.insert({d}_u64, &raw item_{d});\n" ++
                "    _ = map_{d}.insert({d}_u64, &raw item_{d});\n" ++
                "    _ = map_{d}.remove(&{d}_u64);\n" ++
                "    if map_{d}.get(&{d}_u64) is .Some(found_ptr) {{\n" ++
                "        acc = acc +% unsafe {{ found_ptr.*.*.val }};\n" ++
                "    }}\n",
            .{ i, i, i + 1, i, i, i, i, i, i, i + 100, i, i, i + 100, i, i },
        );
    }
    try src_buf.appendSlice(allocator, "    return if acc == 1275_u64 { 0 } else { 1 };\n}\n");

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.X86_64_LINUX_MUSL);
    _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, src_buf.items, .low);

    const elf_exe_path = scratch_dir ++ "/gate2_icf50.elf";
    var art = try db.compileModuleArtifact(app_fid, .{
        .tier_b_llvm = .{
            .target = TargetSpec.X86_64_LINUX_MUSL,
            .opt_level = .release_fast_o2,
            .is_release_mode = true,
        },
    }, .{
        .module_name = "gate2_icf50",
        .artifact_kind = .executable,
        .output_path = elf_exe_path,
        .io = io,
    });
    defer art.deinit(allocator);

    const elf_bytes = try std.Io.Dir.cwd().readFileAlloc(io, elf_exe_path, allocator, .limited(32 * 1024 * 1024));
    defer allocator.free(elf_bytes);
    const icf_counts = try countElf64UniqueTextSymbols(allocator, elf_bytes);

    if (icf_counts.find_raw_addrs > 1 or
        icf_counts.find_or_prepare_addrs > 1 or
        icf_counts.erase_slot_addrs > 1 or
        icf_counts.rehash_or_grow_addrs > 1)
    {
        std.debug.print(
            "[STD-01 Gate 2] 50-Map ICF unique .text bodies: find_raw={d}, " ++
                "find_or_prepare={d}, erase_slot={d}, rehash_or_grow={d}\n",
            .{
                icf_counts.find_raw_addrs,
                icf_counts.find_or_prepare_addrs,
                icf_counts.erase_slot_addrs,
                icf_counts.rehash_or_grow_addrs,
            },
        );
    }

    try std.testing.expect(icf_counts.find_raw_addrs <= 1);
    try std.testing.expect(icf_counts.find_or_prepare_addrs <= 1);
    try std.testing.expect(icf_counts.erase_slot_addrs <= 1);
    try std.testing.expect(icf_counts.rehash_or_grow_addrs <= 1);
}

// ------ Gate 3: Scratch Exclusivity & --sim Determinism -------

test "test_phase11_std01_gate3_scratch_exclusivity_e0328_and_sim_determinism" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const scratch_dir = ".zig-cache/test_std01_gate3";
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, scratch_dir);

    // [1] Negative `compile_fail` checks for `E0328` (unguarded nested same-slot `with_scratch` & escaping slice):
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

        const nested_conflict_src =
            "use cx.mem.{Arena, with_scratch};\n" ++
            "\n" ++
            "fn inner_rewind_slot0() -> usize {\n" ++
            "    return with_scratch(|inner: &mut Arena| -> usize {\n" ++
            "        return inner.dupe_str(\"clobbers_slot_0\").len();\n" ++
            "    });\n" ++
            "}\n" ++
            "\n" ++
            "pub fn bad_nested_same_slot() -> usize {\n" ++
            "    return with_scratch(|outer: &mut Arena| -> usize {\n" ++
            "        let outer_view = outer.dupe_str(\"outer_live\");\n" ++
            "        let inner_len = inner_rewind_slot0();\n" ++
            "        return outer_view.len() + inner_len;\n" ++
            "    });\n" ++
            "}\n";
        const fid_nested = FileId.fromInt(0);
        _ = try db.setInput(fid_nested, nested_conflict_src, .low);
        var sink_nested = DiagnosticSink.init(allocator);
        defer sink_nested.deinit();
        try collectAllDiagnostics(&db, fid_nested, &sink_nested);
        if (!sinkHasCode(&sink_nested, .e0328_scratch_arena_ping_pong_conflict)) {
            dumpDiagnostics("gate3_nested", &sink_nested);
        }
        try std.testing.expect(sinkHasCode(&sink_nested, .e0328_scratch_arena_ping_pong_conflict));

        const escape_slice_src =
            "use cx.mem.{Arena, with_scratch};\n" ++
            "\n" ++
            "pub fn bad_escape_scratch_slice() -> &[u64] {\n" ++
            "    return with_scratch(|scratch: &mut Arena| -> &[u64] {\n" ++
            "        return scratch.alloc_slice[u64](8_usize);\n" ++
            "    });\n" ++
            "}\n";
        const fid_escape = FileId.fromInt(1);
        _ = try db.setInput(fid_escape, escape_slice_src, .low);
        var sink_escape = DiagnosticSink.init(allocator);
        defer sink_escape.deinit();
        try collectAllDiagnostics(&db, fid_escape, &sink_escape);
        if (!sinkHasCode(&sink_escape, .e0328_scratch_arena_ping_pong_conflict)) {
            dumpDiagnostics("gate3_escape", &sink_escape);
        }
        try std.testing.expect(sinkHasCode(&sink_escape, .e0328_scratch_arena_ping_pong_conflict));

        const ok_ping_pong_src =
            "use cx.mem.{Arena, with_scratch};\n" ++
            "\n" ++
            "pub fn ok_nested_complement_slot() -> usize {\n" ++
            "    with_scratch(|outer: &mut Arena| -> usize {\n" ++
            "        let outer_view = outer.dupe_str(\"outer_live\");\n" ++
            "        let inner_len = with_scratch(outer.as_handle(), |inner: &mut Arena| -> usize {\n" ++
            "            inner.dupe_str(\"complement_slot_1\").len()\n" ++
            "        });\n" ++
            "        outer_view.len() + inner_len\n" ++
            "    })\n" ++
            "}\n";
        const fid_ok = FileId.fromInt(2);
        _ = try db.setInput(fid_ok, ok_ping_pong_src, .low);
        var sink_ok = DiagnosticSink.init(allocator);
        defer sink_ok.deinit();
        try collectAllDiagnostics(&db, fid_ok, &sink_ok);
        if (sink_ok.diagnostics.items.len > 0) dumpDiagnostics("gate3_ok_ping_pong", &sink_ok);
        try std.testing.expectEqual(@as(usize, 0), sink_ok.diagnostics.items.len);
    }

    // [2] CLI `corex test --sim --seed=0x5EED_CAFE` determinism across `Map`/`Set` iteration + OOM cleanup:
    const sim_cx_path = scratch_dir ++ "/sim_determinism.cx";
    const sim_src =
        "use cx.mem.FixedBuffer;\n" ++
        "use cx.str;\n" ++
        "\n" ++
        "pub struct TrackedBox {\n" ++
        "    pub id: i32,\n" ++
        "}\n" ++
        "impl AutoDrop for TrackedBox {\n" ++
        "    pub fn drop(&mut self) {\n" ++
        "        @drop_trace(self.id as u64);\n" ++
        "    }\n" ++
        "}\n" ++
        "\n" ++
        "@repr(align: 16)\n" ++
        "pub struct AlignedBacking512 {\n" ++
        "    pub bytes: [u8; 512],\n" ++
        "}\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    // [a] Record `Map` & `Set` seeded iteration order to stdout:\n" ++
        "    var map = Map[u64, u64].new();\n" ++
        "    var set = Set[u64].new();\n" ++
        "    var idx: u64 = 0_u64;\n" ++
        "    while idx < 16_u64 {\n" ++
        "        let key: u64 = idx *% 1315423911_u64 +% 7_u64;\n" ++
        "        _ = map.insert(key, idx);\n" ++
        "        _ = set.insert(key);\n" ++
        "        idx += 1_u64;\n" ++
        "    }\n" ++
        "    var order_digest: u64 = 0xcbf29ce484222325_u64;\n" ++
        "    var map_it = map.iter();\n" ++
        "    while map_it.next() is .Some((key_ref, val_ref)) {\n" ++
        "        order_digest = (order_digest *% 0x100000001b3_u64) +% (key_ref.* ^ (val_ref.* << 16_u64));\n" ++
        "    }\n" ++
        "    var set_it = set.iter();\n" ++
        "    while set_it.next() is .Some(elem_ref) {\n" ++
        "        order_digest = (order_digest *% 0x100000001b3_u64) +% elem_ref.*;\n" ++
        "    }\n" ++
        "    var dig_buf: [u8; 32] = [0_u8; 32];\n" ++
        "    let dig_str = str.format_int(&mut dig_buf, order_digest, radix: 16) catch { return 1; };\n" ++
        "    _ = @sys_write(1, dig_str.as_bytes());\n" ++
        "    _ = @sys_write(1, \"\\n\".as_bytes());\n" ++
        "\n" ++
        "    // [b] OOM fault-injection countdown sweep (`budget_bytes = 0, 32, ..., 384`) with 0 leaks:\n" ++
        "    var oom_backing = AlignedBacking512 { bytes: [0_u8; 512] };\n" ++
        "    var budget_bytes: usize = 0_usize;\n" ++
        "    while budget_bytes <= 384_usize {\n" ++
        "        var lim_fb = FixedBuffer.init(oom_backing.bytes[0..budget_bytes]);\n" ++
        "        with context.allocator = lim_fb.as_handle() {\n" ++
        "            var vec_items = Vec[TrackedBox].new();\n" ++
        "            var map_items = Map[u64, TrackedBox].new();\n" ++
        "            var step: i32 = 1;\n" ++
        "            while step <= 6 {\n" ++
        "                vec_items.try_push(TrackedBox { id: step }) catch {};\n" ++
        "                _ = map_items.try_insert(step as u64, TrackedBox { id: step + 100 }) catch { .None };\n" ++
        "                step += 1;\n" ++
        "            }\n" ++
        "        }\n" ++
        "        budget_bytes += 32_usize;\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";
    try corex.codegen_abi.writeArtifactAtomic(io, allocator, sim_cx_path, sim_src);

    var out_a: [4096]u8 = undefined;
    var err_a: [4096]u8 = undefined;
    var writer_a = std.Io.Writer.fixed(&out_a);
    var err_writer_a = std.Io.Writer.fixed(&err_a);
    const exit_a = try corex.router.runCli(
        allocator,
        io,
        null,
        &.{ "--color=never", "test", "--sim", "--seed=0x5EED_CAFE", sim_cx_path },
        &writer_a,
        &err_writer_a,
    );
    try std.testing.expectEqual(@as(u8, 0), exit_a);

    var out_b: [4096]u8 = undefined;
    var err_b: [4096]u8 = undefined;
    var writer_b = std.Io.Writer.fixed(&out_b);
    var err_writer_b = std.Io.Writer.fixed(&err_b);
    const exit_b = try corex.router.runCli(
        allocator,
        io,
        null,
        &.{ "--color=never", "test", "--sim", "--seed=0x5EED_CAFE", sim_cx_path },
        &writer_b,
        &err_writer_b,
    );
    try std.testing.expectEqual(@as(u8, 0), exit_b);
    try std.testing.expectEqualStrings(writer_a.buffered(), writer_b.buffered());

    var out_diff_seed: [4096]u8 = undefined;
    var err_diff_seed: [4096]u8 = undefined;
    var writer_diff = std.Io.Writer.fixed(&out_diff_seed);
    var err_writer_diff = std.Io.Writer.fixed(&err_diff_seed);
    const exit_diff = try corex.router.runCli(
        allocator,
        io,
        null,
        &.{ "--color=never", "test", "--sim", "--seed=0x1234_5678", sim_cx_path },
        &writer_diff,
        &err_writer_diff,
    );
    try std.testing.expectEqual(@as(u8, 0), exit_diff);
    try std.testing.expect(!std.mem.eql(u8, writer_a.buffered(), writer_diff.buffered()));

    // Also verify 4-tier `--diff-backends --sim --seed=0x5EED_CAFE` agreement:
    var out_4t: [4096]u8 = undefined;
    var err_4t: [4096]u8 = undefined;
    var writer_4t = std.Io.Writer.fixed(&out_4t);
    var err_writer_4t = std.Io.Writer.fixed(&err_4t);
    const exit_4t = try corex.router.runCli(
        allocator,
        io,
        null,
        &.{ "--color=never", "test", "--diff-backends", "--sim", "--seed=0x5EED_CAFE", sim_cx_path },
        &writer_4t,
        &err_writer_4t,
    );
    try std.testing.expectEqual(@as(u8, 0), exit_4t);
}

// ------- Gate 4: Pentagon Zero-Trap & < 2 MB RAM Budget -------

test "test_phase11_std01_gate4_pentagon_zero_trap_and_ram_budget" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    db.setSastStrict(true);
    const cx_fids = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

    // Instantiate generic `partition_lomuto_branchless_cyclic` (`sort_unstable[u64]`) & `partition_point[u64]`,
    // plus unswapped `.in_arena(&mut arena)` `Vec[u64]` / `Map[u64, u64]` / `String`:
    const probe_src =
        "use cx.col;\n" ++
        "use cx.mem.Arena;\n" ++
        "use cx.str;\n" ++
        "\n" ++
        "@inline(never)\n" ++
        "pub fn arena_no_drop_probe() -> usize {\n" ++
        "    var arena = Arena.new();\n" ++
        "    var total: usize = 0_usize;\n" ++
        "    {\n" ++
        "        var vec_u64 = Vec[u64].in_arena(&mut arena);\n" ++
        "        vec_u64.push(11_u64);\n" ++
        "        total += vec_u64.len();\n" ++
        "        var map_u64 = Map[u64, u64].in_arena(&mut arena);\n" ++
        "        _ = map_u64.insert(1_u64, 22_u64);\n" ++
        "        total += map_u64.len();\n" ++
        "        var str_arena = String.in_arena(&mut arena, \"arena_zero_drop\");\n" ++
        "        str_arena.push_str(\"_ok\");\n" ++
        "        total += str_arena.len();\n" ++
        "    }\n" ++
        "    own arena.release();\n" ++
        "    return total;\n" ++
        "}\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    var data: [u64; 8] = [9_u64, 3_u64, 7_u64, 1_u64, 8_u64, 2_u64, 6_u64, 4_u64];\n" ++
        "    col.sort_unstable[u64](&mut data);\n" ++
        "    let split_idx: usize = col.partition_point[u64](&data, |elem: &u64| elem.* < 5_u64);\n" ++
        "    var fbuf: [u8; 32] = [0_u8; 32];\n" ++
        "    let ftxt = str.format_float(&mut fbuf, 3.141592653589793) catch { return 1; };\n" ++
        "    let parsed = str.parse_float[f64](ftxt) catch { return 2; };\n" ++
        "    var ibuf: [u8; 16] = [0_u8; 16];\n" ++
        "    let itxt = str.format_int(&mut ibuf, 123456_u32) catch { return 3; };\n" ++
        "    let valid = str.is_valid_utf8(itxt.as_bytes());\n" ++
        "    let width = str.char_width('W');\n" ++
        "    var gcount: usize = 0_usize;\n" ++
        "    for _ in itxt.graphemes() { gcount += 1_usize; }\n" ++
        "    if not valid or parsed < 3.0 or width != 1_i8 { return 4; }\n" ++
        "    return (split_idx + gcount + arena_no_drop_probe()) as i32;\n" ++
        "}\n";

    const probe_fid = FileId.fromInt(0);
    _ = try db.setInput(probe_fid, probe_src, .low);

    // Collect unelaborated MIR across `probe_fid` + all 5 `stdlib/cx/*.cx` files and run `mir_sast` directly
    // to measure exact `peak_pentagon_bytes` AND inspect post-SAST MIR of all 10 hot functions:
    const target_files = [_]FileId{
        cx_fids[0],
        cx_fids[1],
        cx_fids[2],
        cx_fids[3],
        cx_fids[4],
        probe_fid,
    };
    for (target_files) |fid| {
        _ = try db.resolveSignatures(fid);
    }

    var all_bodies: std.ArrayListUnmanaged(corex.MirBody) = .empty;
    defer {
        for (all_bodies.items) |*body_item| body_item.deinit();
        all_bodies.deinit(allocator);
    }

    for (target_files) |fid| {
        const tree = try db.extractItemTree(fid);
        for (tree.entries) |entry| {
            if (entry.kind == .extern_static or entry.kind == .ffi_extern_block) continue;
            _ = try db.typecheckBody(entry.def_id);
            const def_mir = try db.buildDefMirArtifact(entry.def_id);
            if (def_mir.is_comptime_initializer_only) continue;
            for (def_mir.bundle.bodies.items) |*src_body| {
                var cloned = try src_body.clone(allocator);
                errdefer cloned.deinit();
                try all_bodies.append(allocator, cloned);
            }
        }
    }

    // Also include monomorphized bodies (`partition_lomuto_branchless_cyclic[u64]`, `partition_point[u64]`):
    var opt_bodies: std.ArrayListUnmanaged(corex.MirBody) = .empty;
    defer {
        for (opt_bodies.items) |*body_item| body_item.deinit();
        opt_bodies.deinit(allocator);
    }
    var reachable: std.ArrayListUnmanaged(FileId) = .empty;
    defer reachable.deinit(allocator);
    try db.collectReachableModuleFiles(probe_fid, &.{}, &reachable);
    try db.collectOptimizedModuleBodies(allocator, probe_fid, reachable.items, false, null, &opt_bodies);

    var sast_sink = DiagnosticSink.init(allocator);
    defer sast_sink.deinit();
    var sast_res = try corex.mir_sast.analyzeAndElaborateMirModule(
        allocator,
        all_bodies.items,
        &db.type_pool,
        &db.symbol_table,
        &db.interner,
        .{
            .diagnostic_sink = &sast_sink,
            .is_sast_strict = true,
        },
    );
    defer sast_res.deinit();

    if (sast_sink.diagnostics.items.len > 0) dumpDiagnostics("gate4_sast", &sast_sink);
    try std.testing.expectEqual(@as(usize, 0), sast_sink.diagnostics.items.len);

    if (sast_res.peak_pentagon_bytes >= 2 * 1024 * 1024) {
        std.debug.print(
            "[STD-01 Gate 4] Pentagon peak_pentagon_bytes = {d} B (limit < 2,097,152 B), " ++
                "eliminated_bounds_checks = {d}\n",
            .{ sast_res.peak_pentagon_bytes, sast_res.eliminated_bounds_checks },
        );
    }
    try std.testing.expect(sast_res.peak_pentagon_bytes < 2 * 1024 * 1024);

    // Verify all 10 hot functions (plus `is_valid_utf8_fast`!) have 0 residual traps:
    for (GATE4_HOT_FUNCTIONS) |hot_name| {
        var matched_count: usize = 0;
        for (all_bodies.items) |*body_ptr| {
            const fn_name = db.interner.get(body_ptr.name);
            if (std.mem.eql(u8, fn_name, hot_name) or
                (std.mem.startsWith(u8, fn_name, hot_name) and
                    fn_name.len > hot_name.len and fn_name[hot_name.len] == '['))
            {
                matched_count += 1;
                const traps = countResidualTrapsInBody(body_ptr);
                if (traps != 0) {
                    const mir_txt = try corex.renderMir(allocator, body_ptr, &db.interner);
                    defer allocator.free(mir_txt);
                    std.debug.print("[Gate 4 Trap Failure] {s}:\n{s}\n", .{ fn_name, mir_txt });
                }
                try std.testing.expectEqual(@as(usize, 0), traps);
            }
        }
        for (opt_bodies.items) |*body_ptr| {
            const fn_name = db.interner.get(body_ptr.name);
            if (std.mem.eql(u8, fn_name, hot_name) or
                (std.mem.startsWith(u8, fn_name, hot_name) and
                    fn_name.len > hot_name.len and fn_name[hot_name.len] == '['))
            {
                matched_count += 1;
                const traps = countResidualTrapsInBody(body_ptr);
                if (traps != 0) {
                    const mir_txt = try corex.renderMir(allocator, body_ptr, &db.interner);
                    defer allocator.free(mir_txt);
                    std.debug.print("[Gate 4 Opt Trap Failure] {s}:\n{s}\n", .{ fn_name, mir_txt });
                }
                try std.testing.expectEqual(@as(usize, 0), traps);
            }
        }
        try std.testing.expect(matched_count >= 1);
    }

    // Also check inner `is_valid_utf8_fast` explicitly:
    var seen_utf8_fast = false;
    for (all_bodies.items) |*body_ptr| {
        if (std.mem.eql(u8, db.interner.get(body_ptr.name), "is_valid_utf8_fast")) {
            seen_utf8_fast = true;
            try std.testing.expectEqual(@as(usize, 0), countResidualTrapsInBody(body_ptr));
        }
    }
    try std.testing.expect(seen_utf8_fast);

    // Verify `0` destructor instructions (`drop_in_place` / `drop_if_live`) on unswapped `.in_arena(&mut arena)`
    // `Vec[u64]`, `Map[u64, u64]`, and `String` in `arena_no_drop_probe`:
    var found_probe = false;
    for (all_bodies.items) |*body_ptr| {
        if (std.mem.eql(u8, db.interner.get(body_ptr.name), "arena_no_drop_probe")) {
            found_probe = true;
            for (0..body_ptr.insts.len) |inst_i| {
                const inst = body_ptr.insts.get(inst_i);
                if (inst.op == .intrinsic_op) {
                    const ikind: corex.mir.MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                    try std.testing.expect(ikind != .drop_in_place and ikind != .drop_if_live);
                }
            }
        }
    }
    try std.testing.expect(found_probe);
}

// ---- Gate 5: 4-Tier Parity & < 10,240 B Freestanding Wasm ----

test "test_phase11_std01_gate5_four_tier_ucd16_float_math_and_wasm_profiles" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const scratch_dir = ".zig-cache/test_std01_gate5";
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, scratch_dir);

    // [1] 4-Tier Differential Parity over all 1,675 Unicode 16.0 `GraphemeBreakTest` conformance vectors
    //     + IEEE-754 `f32`/`f64` `format_float` <-> `parse_float` round-trip + `cx.math` transcendentals:
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.host());
        _ = try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

        var vfs_files: std.StringHashMapUnmanaged([]const u8) = .empty;
        defer vfs_files.deinit(allocator);
        try vfs_files.put(allocator, "grapheme_ucd16.bin", &grapheme_ucd16.PACKED_VECTORS);
        db.setEmbedSandbox(null, &vfs_files);

        const diff_src =
            "use cx.math;\n" ++
            "use cx.str;\n" ++
            "\n" ++
            "fn verify_f64_roundtrip(bits: u64, /) -> bool {\n" ++
            "    if ((bits >> 52_u64) & 0x7FF_u64) == 0x7FF_u64 { return true; }\n" ++
            "    let val: f64 = @bit_cast[f64](bits);\n" ++
            "    var buf: [u8; 40] = [0_u8; 40];\n" ++
            "    let formatted = str.format_float(&mut buf, val) catch { return false; };\n" ++
            "    let parsed = str.parse_float[f64](formatted) catch { return false; };\n" ++
            "    return @bit_cast[u64](parsed) == bits;\n" ++
            "}\n" ++
            "\n" ++
            "fn verify_f32_roundtrip(bits: u32, /) -> bool {\n" ++
            "    if ((bits >> 23_u32) & 0xFF_u32) == 0xFF_u32 { return true; }\n" ++
            "    let val: f32 = @bit_cast[f32](bits);\n" ++
            "    var buf: [u8; 32] = [0_u8; 32];\n" ++
            "    let formatted = str.format_float(&mut buf, val) catch { return false; };\n" ++
            "    let parsed = str.parse_float[f32](formatted) catch { return false; };\n" ++
            "    return @bit_cast[u32](parsed) == bits;\n" ++
            "}\n" ++
            "\n" ++
            "pub fn main() -> i32 {\n" ++
            "    // [a] Verify all 1,675 Unicode 16.0 `GraphemeBreakTest` cases:\n" ++
            "    let packed_ucd16: &[u8] = @embed_bytes(\"grapheme_ucd16.bin\");\n" ++
            "    var pos: usize = 0_usize;\n" ++
            "    var verified_vectors: usize = 0_usize;\n" ++
            "    let total_blob: usize = packed_ucd16.len();\n" ++
            "    while pos < total_blob {\n" ++
            "        let utf8_len: usize = packed_ucd16[pos] as usize;\n" ++
            "        if utf8_len == 0_usize { break; }\n" ++
            "        let exp_clusters: usize = packed_ucd16[pos + 1_usize] as usize;\n" ++
            "        let lens_off: usize = pos + 2_usize;\n" ++
            "        let str_off: usize = lens_off + exp_clusters;\n" ++
            "        let text = str.from_utf8(packed_ucd16[str_off .. str_off + utf8_len]) catch { return 1; };\n" ++
            "        var seg_idx: usize = 0_usize;\n" ++
            "        var byte_sum: usize = 0_usize;\n" ++
            "        for seg in text.graphemes() {\n" ++
            "            if seg_idx >= exp_clusters { return 2; }\n" ++
            "            if seg.len() != (packed_ucd16[lens_off + seg_idx] as usize) { return 3; }\n" ++
            "            byte_sum += seg.len();\n" ++
            "            seg_idx += 1_usize;\n" ++
            "        }\n" ++
            "        if seg_idx != exp_clusters or byte_sum != utf8_len { return 4; }\n" ++
            "        verified_vectors += 1_usize;\n" ++
            "        pos = str_off + utf8_len;\n" ++
            "    }\n" ++
            "    if verified_vectors != 1675_usize { return 5; }\n" ++
            "\n" ++
            "    // [b] Verify IEEE-754 `f64` & `f32` boundary + PRNG round-trips across all 4 tiers:\n" ++
            "    let edge_f64: [u64; 12] = [\n" ++
            "        0x0000_0000_0000_0000_u64, 0x8000_0000_0000_0000_u64,\n" ++
            "        0x0000_0000_0000_0001_u64, 0x000F_FFFF_FFFF_FFFF_u64,\n" ++
            "        0x0010_0000_0000_0000_u64, 0x0010_0000_0000_0001_u64,\n" ++
            "        0x3FF0_0000_0000_0000_u64, 0x3FF0_0000_0000_0001_u64,\n" ++
            "        0x7FEF_FFFF_FFFF_FFFE_u64, 0x7FEF_FFFF_FFFF_FFFF_u64,\n" ++
            "        0xFFE0_0000_0000_0000_u64, 0x2B2B_FF2E_48E0_5300_u64,\n" ++
            "    ];\n" ++
            "    for bits64 in edge_f64 {\n" ++
            "        if not verify_f64_roundtrip(bits64) { return 6; }\n" ++
            "    }\n" ++
            "    let edge_f32: [u32; 10] = [\n" ++
            "        0x0000_0000_u32, 0x8000_0000_u32, 0x0000_0001_u32, 0x007F_FFFF_u32,\n" ++
            "        0x0080_0000_u32, 0x3F80_0000_u32, 0x3F80_0001_u32, 0x7F7F_FFFF_u32,\n" ++
            "        0xFF7F_FFFF_u32, 0x33D6_BF95_u32,\n" ++
            "    ];\n" ++
            "    for bits32 in edge_f32 {\n" ++
            "        if not verify_f32_roundtrip(bits32) { return 7; }\n" ++
            "    }\n" ++
            "    var rng_state: u64 = 0x5EED_CAFE_1234_5678_u64;\n" ++
            "    var sample_i: usize = 0_usize;\n" ++
            "    while sample_i < 256_usize {\n" ++
            "        rng_state = rng_state +% 0x9E37_79B9_7F4A_7C15_u64;\n" ++
            "        var z: u64 = rng_state;\n" ++
            "        z = (z ^ (z >> 30_u64)) *% 0xBF58_476D_1CE4_E5B9_u64;\n" ++
            "        z = (z ^ (z >> 27_u64)) *% 0x94D0_49BB_1331_11EB_u64;\n" ++
            "        z = z ^ (z >> 31_u64);\n" ++
            "        if not verify_f64_roundtrip(z) { return 8; }\n" ++
            "        if not verify_f32_roundtrip((z >> 16_u64) as u32) { return 9; }\n" ++
            "        sample_i += 1_usize;\n" ++
            "    }\n" ++
            "\n" ++
            "    // [c] Verify deterministic `cx.math` transcendentals across all 4 tiers:\n" ++
            "    var math_digest: u64 = 0_u64;\n" ++
            "    let angles: [f64; 5] = [-3.14159265, -0.5, 0.0, 0.75, 123456.789];\n" ++
            "    for ang in angles {\n" ++
            "        let s_val = math.sin(ang);\n" ++
            "        let c_val = math.cos(ang);\n" ++
            "        let t_val = math.tan(ang * 0.1);\n" ++
            "        let e_val = math.exp(ang * 0.001);\n" ++
            "        let l_val = math.ln_1p(math.abs(ang));\n" ++
            "        let h_val = math.hypot(s_val, c_val);\n" ++
            "        let cb_val = math.cbrt(ang);\n" ++
            "        let at_val = math.atan2(s_val, c_val);\n" ++
            "        math_digest = (math_digest *% 131_u64) ^ @bit_cast[u64](t_val + e_val + l_val + h_val + cb_val + at_val);\n" ++
            "    }\n" ++
            "    if math_digest == 0_u64 { return 10; }\n" ++
            "    return verified_vectors as i32;\n" ++
            "}\n";

        const diff_fid = FileId.fromInt(0);
        _ = try db.setInput(diff_fid, diff_src, .low);
        var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, diff_fid, .{
            .io = io,
            .virtual_files = &vfs_files,
            .comptime_step_limit = 50_000_000,
        });
        defer report.deinit(allocator);
        if (!report.is_all_matching) {
            std.debug.print(
                "{s}\n[Tier 3 stderr]: {s}\n[Tier 4 stderr]: {s}\n",
                .{ report.rendered_diff_table, report.outcomes[2].stderr_bytes, report.outcomes[3].stderr_bytes },
            );
        }
        try std.testing.expect(report.is_all_matching);
        try std.testing.expect(!report.outcomes[0].has_trapped);
        try std.testing.expectEqual(@as(i64, 1675), report.outcomes[0].return_scalar_i64);
    }

    // [2] Freestanding `wasm32` (`wasm32-unknown-freestanding`, `--release` `-Oz`) Profiles A, B, and C:
    var wasm_db = try CompilerDb.init(allocator);
    defer wasm_db.deinit();
    wasm_db.setTargetSpec(TargetSpec.WASM32_UNKNOWN_FREESTANDING);
    _ = try mountStdCoreAndCxIntoDb(allocator, io, &wasm_db, 10);

    // Profile A: `Arena` + `Vec[u32]` + `Map[u64, u32]`:
    const profile_a_src =
        "use cx.mem.Arena;\n" ++
        "\n" ++
        "@export\n" ++
        "pub fn run_profile_a(seed: u32) -> u32 {\n" ++
        "    var arena = Arena.new();\n" ++
        "    var out_val: u32 = 0_u32;\n" ++
        "    {\n" ++
        "        var items = Vec[u32].in_arena(&mut arena);\n" ++
        "        items.push(seed);\n" ++
        "        items.push(seed +% 1_u32);\n" ++
        "        let pair_sum: u32 = items[0] +% items[1];\n" ++
        "        var lookup = Map[u64, u32].in_arena(&mut arena);\n" ++
        "        _ = lookup.insert(seed as u64, pair_sum);\n" ++
        "        if lookup.get(&(seed as u64)) is .Some(val_ptr) {\n" ++
        "            out_val = val_ptr.*;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    own arena.release();\n" ++
        "    return out_val;\n" ++
        "}\n";

    // Profile B: `@no_alloc` `format_into` + `{val:#06x}` / `jeaiii` integer formatting:
    const profile_b_src =
        "use cx.str;\n" ++
        "\n" ++
        "@export\n" ++
        "pub fn run_profile_b(val: u32, dst_ptr: *mut u8, cap: usize) -> usize {\n" ++
        "    let dst: &mut [u8] = unsafe { @slice_from_raw_parts_mut(dst_ptr, cap) };\n" ++
        "    let hex_out = str.format_into(dst, f\"{val:#06x}\") catch { return 0_usize; };\n" ++
        "    var dec_buf: [u8; 16] = [0_u8; 16];\n" ++
        "    let dec_out = str.format_int(&mut dec_buf, val) catch { return 0_usize; };\n" ++
        "    return hex_out.len() +% dec_out.len();\n" ++
        "}\n";

    // Profile C: `str` + `char_width` + `display_width` (`WCWIDTH_TRIE` linked, `GRAPHEME_TRIE` stripped!):
    const profile_c_src =
        "use cx.str;\n" ++
        "\n" ++
        "@export\n" ++
        "pub fn run_profile_c(ptr: *u8, len: usize) -> usize {\n" ++
        "    let raw_slice: &[u8] = unsafe { @slice_from_raw_parts(ptr, len) };\n" ++
        "    let valid = str.from_utf8(raw_slice) catch { return 0_usize; };\n" ++
        "    let cjk_w: usize = str.char_width('中') as usize;\n" ++
        "    return valid.display_width() +% cjk_w;\n" ++
        "}\n";

    const profiles = [_]struct {
        label: []const u8,
        source: []const u8,
        file_id: u32,
        out_name: []const u8,
    }{
        .{ .label = "Profile A", .source = profile_a_src, .file_id = 0, .out_name = "profile_a.wasm" },
        .{ .label = "Profile B", .source = profile_b_src, .file_id = 1, .out_name = "profile_b.wasm" },
        .{ .label = "Profile C", .source = profile_c_src, .file_id = 2, .out_name = "profile_c.wasm" },
    };

    for (profiles) |prof| {
        const fid = FileId.fromInt(prof.file_id);
        _ = try wasm_db.setInput(fid, prof.source, .low);
        const wasm_out = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ scratch_dir, prof.out_name });
        defer allocator.free(wasm_out);

        var art = try wasm_db.compileModuleArtifact(fid, .{
            .tier_b_llvm = .{
                .target = TargetSpec.WASM32_UNKNOWN_FREESTANDING,
                .opt_level = .release_small_oz,
                .is_release_mode = true,
            },
        }, .{
            .module_name = prof.label,
            .artifact_kind = .executable,
            .output_path = wasm_out,
            .io = io,
        });
        defer art.deinit(allocator);

        const wasm_bytes = try std.Io.Dir.cwd().readFileAlloc(io, wasm_out, allocator, .limited(4 * 1024 * 1024));
        defer allocator.free(wasm_bytes);
        const summary = try inspectWasmBinary(wasm_bytes);

        if (summary.byte_size >= 10_240 or
            summary.import_count != 0 or
            summary.has_start_section or
            summary.has_nonempty_wasm_call_ctors)
        {
            std.debug.print(
                "[STD-01 Gate 5] {s}: size = {d} B (limit < 10,240 B), imports = {d}, start = {}\n",
                .{ prof.label, summary.byte_size, summary.import_count, summary.has_start_section },
            );
        }

        try std.testing.expectEqual(@as(u32, 0), summary.import_count);
        try std.testing.expect(!summary.has_start_section);
        try std.testing.expect(!summary.has_nonempty_wasm_call_ctors);
        try std.testing.expect(summary.byte_size < 10_240);
    }
}

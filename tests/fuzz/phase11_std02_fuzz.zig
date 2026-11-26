//! Phase 11.2a (`STD-02`) Deterministic Structure-Aware Property Fuzzing Suite
//!
//! Exercises deterministic SplitMix64 state-machine equivalence, round-trip fidelity, and adversarial
//! rejection invariants across `stdlib/cx/{io,path,env,process}.cx` over all 4 backend tiers:
//! - `cx.path`: 300+ POSIX, Windows drive, drive-relative, UNC, verbatim `\\?\`, `.`/`..`, trailing-sep,
//!   and DOS-stem paths verifying `ComponentsIter` `next` vs `next_back` reversal equivalence and
//!   `normalize_lexical` idempotency across `.Posix` and `.Windows` flavors,
//! - `cx.path` WTF-8/16: 350+ mutated `[u16]` arrays (lone high/low surrogates, swapped surrogates, BMP,
//!   valid pairs) round-tripping bit-for-bit plus 250+ adversarial CESU-8 / overlong / NUL rejections,
//! - `cx.io`: `BufReader.over_uninit` (`7 B` & `17 B` buffers) over a short-read + `EINTR` chaos reader
//!   and `@linear BufWriter.over_uninit` (`11 B` buffer) chunked + vectored writes vs flat slice oracles,
//! - `cx.env`: 250+ MSVCRT `2n`/`2n+1` backslash-quoted Win32 command lines (spaces, tabs, `\"`, trailing `\`,
//!   empty `""`, and lone surrogates) round-tripping through `parse_win32_cmdline_in`.
//!
//! Every PRNG stream uses a fixed deterministic SplitMix64 seed so any divergence reproduces 100%.

const std = @import("std");
const corex = @import("corex");

const FileId = corex.FileId;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;

// ---------------------------------------- TYPES ----------------------------------------

/// Mounted `FileId` handles for `core/**/*.cx`, `stdlib/cx/*.cx`, and `cx.__std02_fuzz_probe`.
const FuzzStdBundle = struct {
    /// Fixed storage for `26` mounted `FileId`s (`14` `core` + `11` `cx` + `1` probe).
    storage: [CORE_MODULE_PATHS.len + CX_STDLIB_PATHS.len + 1]FileId = undefined,
    /// Active `FileId` count (`26`).
    count: usize = 0,
    /// `FileId` of `stdlib/cx/__std02_fuzz_probe.cx`.
    probe_fid: FileId = .none,

    /// Returns the active slice of mounted `FileId`s for `extra_file_ids`.
    fn asSlice(self: *const FuzzStdBundle) []const FileId {
        return self.storage[0..self.count];
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical Stage-1 `core` source file paths (`14` files).
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

// --------------- CompilerDb Mounting & Helpers ----------------

/// Normalizes CRLF line endings in `raw_bytes` to LF.
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

/// Mounts `core`, `stdlib/cx`, and `probe_src` (`cx.__std02_fuzz_probe`) into `db`.
fn mountStdAndFuzzProbeIntoDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    db: *CompilerDb,
    base_file_id: u32,
    probe_src: []const u8,
) !FuzzStdBundle {
    var bundle: FuzzStdBundle = .{};
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

        if (i == 0) {
            const augmented_mod = try std.fmt.allocPrint(
                allocator,
                "{s}\npub mod __std02_fuzz_probe;\n",
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

    const probe_idx = CORE_MODULE_PATHS.len + CX_STDLIB_PATHS.len;
    const probe_fid = FileId.fromInt(base_file_id + @as(u32, @intCast(probe_idx)));
    bundle.storage[probe_idx] = probe_fid;
    bundle.probe_fid = probe_fid;
    bundle.count = probe_idx + 1;
    try db.setFilePackageId(probe_fid, .std_core);
    try db.setFilePath(probe_fid, "stdlib/cx/__std02_fuzz_probe.cx");
    _ = try db.setInput(probe_fid, probe_src, .low);
    try db.bindExternalModule(cx_mod_fid, "__std02_fuzz_probe", probe_fid);
    return bundle;
}

/// Runs `probe_src` across all 4 `diff_oracle` tiers and expects `expected_rc` with zero diagnostics.
fn runFuzzProbeFourTier(
    allocator: std.mem.Allocator,
    io: std.Io,
    label: []const u8,
    probe_src: []const u8,
    expected_rc: i64,
) !void {
    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    const bundle = try mountStdAndFuzzProbeIntoDb(allocator, io, &db, 10, probe_src);

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(
        app_fid,
        "pub fn main() -> i32 {\n    cx.__std02_fuzz_probe.run_fuzz()\n}\n",
        .low,
    );

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    for ([_]FileId{ app_fid, bundle.probe_fid }) |check_fid| {
        const parsed = try db.parseCst(check_fid);
        for (parsed.diagnostics.diagnostics.items) |diag_item| _ = try sink.emit(diag_item);
        _ = try db.resolveSignatures(check_fid);
        if (db.getSignatureDiagnostics(check_fid)) |sig_sink| {
            for (sig_sink.diagnostics.items) |diag_item| _ = try sink.emit(diag_item);
        }
        const tree = try db.extractItemTree(check_fid);
        const def_ids = try db.allocator.alloc(corex.DefId, tree.entries.len);
        defer db.allocator.free(def_ids);
        for (tree.entries, 0..) |entry, i| def_ids[i] = entry.def_id;
        for (def_ids) |def_id| {
            _ = try db.typecheckBody(def_id);
            if (db.getBodyDiagnostics(def_id)) |body_sink| {
                for (body_sink.diagnostics.items) |diag_item| _ = try sink.emit(diag_item);
            }
            _ = try db.verifySastMir(def_id);
            if (db.getSastDiagnostics(def_id)) |sast_sink| {
                for (sast_sink.diagnostics.items) |diag_item| _ = try sink.emit(diag_item);
            }
        }
    }
    if (sink.diagnostics.items.len > 0) {
        for (sink.diagnostics.items) |diag_item| {
            std.debug.print("[{s}] {s}: {s}\n", .{ label, @tagName(diag_item.code), diag_item.message });
        }
    }
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var vm_sink = DiagnosticSink.init(allocator);
    defer vm_sink.deinit();
    var report = try corex.runFourTierDiffOracleOnDb(
        allocator,
        &db,
        app_fid,
        .{
            .io = io,
            .extra_file_ids = bundle.asSlice(),
            .comptime_step_limit = 50_000_000,
            .diagnostic_sink = &vm_sink,
        },
    );
    defer report.deinit(allocator);
    if (vm_sink.diagnostics.items.len > 0) {
        for (vm_sink.diagnostics.items) |diag_item| {
            std.debug.print("[{s}:vm] {s}: {s}\n", .{ label, @tagName(diag_item.code), diag_item.message });
        }
    }
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(expected_rc, report.outcomes[0].return_scalar_i64);
}

// ------------------------------------- PUBLIC API --------------------------------------

// ---------------- Fuzz 1: Path & Normalization ----------------

test "test_std02_fuzz_path_components_reversal_and_normalize_idempotency" {
    const fuzz_path_src =
        "use cx.col.Vec;\n" ++
        "use cx.path.{\n" ++
        "    Component,\n" ++
        "    ComponentsIter,\n" ++
        "    Path,\n" ++
        "    PathBuf,\n" ++
        "    PathFlavor,\n" ++
        "    components_with_flavor,\n" ++
        "    normalize_lexical_with_flavor,\n" ++
        "};\n\n" ++
        "fn next_rng(state: &mut u64, /) -> u64 {\n" ++
        "    state.* = state.* +% 0x9E37_79B9_7F4A_7C15_u64;\n" ++
        "    var z_val: u64 = state.*;\n" ++
        "    z_val = (z_val ^ (z_val >> 30_u64)) *% 0xBF58_476D_1CE4_E5B9_u64;\n" ++
        "    z_val = (z_val ^ (z_val >> 27_u64)) *% 0x94D0_49BB_1331_11EB_u64;\n" ++
        "    z_val ^ (z_val >> 31_u64)\n" ++
        "}\n\n" ++
        "fn verify_flavor_invariants(raw: &[u8], flavor: PathFlavor, /) -> bool {\n" ++
        "    let path_view = Path.from_bytes(raw);\n" ++
        "    var fwd = Vec[Component].new();\n" ++
        "    var it_fwd: ComponentsIter = components_with_flavor(path_view, flavor);\n" ++
        "    while it_fwd.next() is .Some(comp_f) {\n" ++
        "        fwd.push(comp_f);\n" ++
        "    }\n" ++
        "    var bwd = Vec[Component].new();\n" ++
        "    var it_bwd: ComponentsIter = components_with_flavor(path_view, flavor);\n" ++
        "    while it_bwd.next_back() is .Some(comp_b) {\n" ++
        "        bwd.push(comp_b);\n" ++
        "    }\n" ++
        "    if fwd.len() != bwd.len() {\n" ++
        "        return false;\n" ++
        "    }\n" ++
        "    let total_c: usize = fwd.len();\n" ++
        "    var idx = 0_usize;\n" ++
        "    while idx < total_c {\n" ++
        "        if fwd.as_slice()[idx] != bwd.as_slice()[total_c - 1_usize - idx] {\n" ++
        "            return false;\n" ++
        "        }\n" ++
        "        idx += 1_usize;\n" ++
        "    }\n" ++
        "    let norm1: PathBuf = normalize_lexical_with_flavor(path_view, flavor);\n" ++
        "    let norm2: PathBuf = normalize_lexical_with_flavor(norm1.as_path(), flavor);\n" ++
        "    norm1.as_bytes() == norm2.as_bytes()\n" ++
        "}\n\n" ++
        "pub fn run_fuzz() -> i32 {\n" ++
        "    var rng = 0x1102_57D0_2FA7_0001_u64;\n" ++
        "    let prefixes = [\n" ++
        "        \"\",\n" ++
        "        \"/\",\n" ++
        "        \"C:\\\\\",\n" ++
        "        \"C:\",\n" ++
        "        \"\\\\\\\\srv\\\\shr\\\\\",\n" ++
        "        \"\\\\\\\\?\\\\C:\\\\\",\n" ++
        "        \"\\\\\\\\?\\\\UNC\\\\srv\\\\shr\\\\\",\n" ++
        "        \"./\",\n" ++
        "    ];\n" ++
        "    let segments = [\n" ++
        "        \"a\",\n" ++
        "        \"dir_long_name\",\n" ++
        "        \".\",\n" ++
        "        \"..\",\n" ++
        "        \"CON\",\n" ++
        "        \"NUL.txt\",\n" ++
        "        \"LPT1\",\n" ++
        "        \"conin$\",\n" ++
        "        \"file.cx\",\n" ++
        "        \"trailing. \",\n" ++
        "        \"sub\",\n" ++
        "        \"..\",\n" ++
        "    ];\n" ++
        "    var buf = Vec[u8].with_capacity(256_usize);\n" ++
        "    var case_i = 0_usize;\n" ++
        "    while case_i < 320_usize {\n" ++
        "        buf.clear();\n" ++
        "        let p_word: u64 = next_rng(&mut rng);\n" ++
        "        buf.extend_from_slice(prefixes[(p_word as usize) % 8_usize].as_bytes());\n" ++
        "        let seg_count: usize = ((p_word >> 8_u64) as usize) % 7_usize;\n" ++
        "        var seg_i = 0_usize;\n" ++
        "        while seg_i < seg_count {\n" ++
        "            let s_word: u64 = next_rng(&mut rng);\n" ++
        "            buf.extend_from_slice(segments[(s_word as usize) % 12_usize].as_bytes());\n" ++
        "            let sep_mode: u64 = (s_word >> 12_u64) & 3_u64;\n" ++
        "            if sep_mode == 0_u64 {\n" ++
        "                buf.push(b'/');\n" ++
        "            } else if sep_mode == 1_u64 {\n" ++
        "                buf.push(b'\\\\');\n" ++
        "            } else if sep_mode == 2_u64 {\n" ++
        "                buf.extend_from_slice(\"//\\\\\".as_bytes());\n" ++
        "            }\n" ++
        "            seg_i += 1_usize;\n" ++
        "        }\n" ++
        "        if not verify_flavor_invariants(buf.as_slice(), .Posix) {\n" ++
        "            return 1000 + (case_i as i32);\n" ++
        "        }\n" ++
        "        if not verify_flavor_invariants(buf.as_slice(), .Windows) {\n" ++
        "            return 2000 + (case_i as i32);\n" ++
        "        }\n" ++
        "        case_i += 1_usize;\n" ++
        "    }\n" ++
        "    0\n" ++
        "}\n";

    try runFuzzProbeFourTier(
        std.testing.allocator,
        std.testing.io,
        "fuzz1_path_components_and_normalize",
        fuzz_path_src,
        0,
    );
}

// ---------------- Fuzz 2: WTF-8/16 Surrogates -----------------

test "test_std02_fuzz_wtf8_wtf16_surrogate_roundtrip_and_cesu8_rejection" {
    const fuzz_wtf8_src =
        "use cx.path.{\n" ++
        "    PathBuf,\n" ++
        "    Wtf8Error,\n" ++
        "    decode_wtf16_to_path_buf,\n" ++
        "    decode_wtf16_to_wtf8,\n" ++
        "    encode_wtf8_to_wtf16,\n" ++
        "    wtf8_len_for_wtf16,\n" ++
        "};\n\n" ++
        "fn next_rng(state: &mut u64, /) -> u64 {\n" ++
        "    state.* = state.* +% 0x9E37_79B9_7F4A_7C15_u64;\n" ++
        "    var z_val: u64 = state.*;\n" ++
        "    z_val = (z_val ^ (z_val >> 30_u64)) *% 0xBF58_476D_1CE4_E5B9_u64;\n" ++
        "    z_val = (z_val ^ (z_val >> 27_u64)) *% 0x94D0_49BB_1331_11EB_u64;\n" ++
        "    z_val ^ (z_val >> 31_u64)\n" ++
        "}\n\n" ++
        "pub fn run_fuzz() -> i32 {\n" ++
        "    var rng = 0x1102_57D0_2FA7_0002_u64;\n" ++
        "    var u16_in = [0_u16; 24];\n" ++
        "    var wtf8_buf = [0_u8; 96];\n" ++
        "    var u16_out = [0_u16; 32];\n\n" ++
        "    // [1] 350 randomized `[u16]` sequences (ASCII, BMP, valid pairs, lone high/low, swapped, & NUL):\n" ++
        "    var round_i = 0_usize;\n" ++
        "    while round_i < 350_usize {\n" ++
        "        let len_u16: usize = (next_rng(&mut rng) as usize) % 21_usize;\n" ++
        "        var has_nul = false;\n" ++
        "        var pos = 0_usize;\n" ++
        "        while pos < len_u16 {\n" ++
        "            let word: u64 = next_rng(&mut rng);\n" ++
        "            let kind: u64 = word % 7_u64;\n" ++
        "            let code_unit: u16 = if kind == 0_u64 {\n" ++
        "                1_u16 + (((word >> 8_u64) as u16) % 126_u16)\n" ++
        "            } else if kind == 1_u64 {\n" ++
        "                0x0080_u16 + (((word >> 8_u64) as u16) % 0x0700_u16)\n" ++
        "            } else if kind == 2_u64 {\n" ++
        "                0x0800_u16 + (((word >> 8_u64) as u16) % 0x4F00_u16)\n" ++
        "            } else if kind == 3_u64 {\n" ++
        "                0xD800_u16 + (((word >> 8_u64) as u16) & 0x03FF_u16)\n" ++
        "            } else if kind == 4_u64 {\n" ++
        "                0xDC00_u16 + (((word >> 8_u64) as u16) & 0x03FF_u16)\n" ++
        "            } else if kind == 5_u64 and pos + 1_usize < len_u16 {\n" ++
        "                u16_in[pos] = 0xD800_u16 + (((word >> 8_u64) as u16) & 0x03FF_u16);\n" ++
        "                pos += 1_usize;\n" ++
        "                0xDC00_u16 + (((word >> 20_u64) as u16) & 0x03FF_u16)\n" ++
        "            } else {\n" ++
        "                has_nul = true;\n" ++
        "                0_u16\n" ++
        "            };\n" ++
        "            u16_in[pos] = code_unit;\n" ++
        "            pos += 1_usize;\n" ++
        "        }\n" ++
        "        let in_view: &[u16] = &u16_in;\n" ++
        "        let src_slice: &[u16] = in_view[0..len_u16];\n" ++
        "        let exp_bytes: usize = wtf8_len_for_wtf16(src_slice);\n" ++
        "        let dec_bytes: usize = decode_wtf16_to_wtf8(src_slice, &mut wtf8_buf);\n" ++
        "        let pb: PathBuf = decode_wtf16_to_path_buf(src_slice);\n" ++
        "        let wtf8_view: &[u8] = &wtf8_buf;\n" ++
        "        if exp_bytes != dec_bytes or pb.as_bytes() != wtf8_view[0..dec_bytes] {\n" ++
        "            return 1000 + (round_i as i32);\n" ++
        "        }\n" ++
        "        let enc_res: usize!Wtf8Error = encode_wtf8_to_wtf16(wtf8_view[0..dec_bytes], &mut u16_out);\n" ++
        "        if has_nul {\n" ++
        "            if enc_res != .Err(.InteriorNulByte) {\n" ++
        "                return 2000 + (round_i as i32);\n" ++
        "            }\n" ++
        "        } else {\n" ++
        "            let got_u16: usize = enc_res catch return 3000 + (round_i as i32);\n" ++
        "            let out_view: &[u16] = &u16_out;\n" ++
        "            if got_u16 != len_u16 or out_view[0..got_u16] != src_slice {\n" ++
        "                return 4000 + (round_i as i32);\n" ++
        "            }\n" ++
        "        }\n" ++
        "        round_i += 1_usize;\n" ++
        "    }\n\n" ++
        "    // [2] 250 adversarial paired 6-byte CESU-8 surrogates, overlongs, & truncated sequences:\n" ++
        "    var adv_i = 0_usize;\n" ++
        "    while adv_i < 250_usize {\n" ++
        "        let word: u64 = next_rng(&mut rng);\n" ++
        "        let high_b1: u8 = 0xA0_u8 + (((word >> 0_u64) as u8) % 0x10_u8);\n" ++
        "        let high_b2: u8 = 0x80_u8 + (((word >> 8_u64) as u8) & 0x3F_u8);\n" ++
        "        let low_b1: u8 = 0xB0_u8 + (((word >> 16_u64) as u8) % 0x10_u8);\n" ++
        "        let low_b2: u8 = 0x80_u8 + (((word >> 24_u64) as u8) & 0x3F_u8);\n" ++
        "        let cesu8 = [\n" ++
        "            b'x',\n" ++
        "            0xED_u8,\n" ++
        "            high_b1,\n" ++
        "            high_b2,\n" ++
        "            0xED_u8,\n" ++
        "            low_b1,\n" ++
        "            low_b2,\n" ++
        "            b'y',\n" ++
        "        ];\n" ++
        "        if encode_wtf8_to_wtf16(&cesu8, &mut u16_out) != .Err(.InvalidWtf8) {\n" ++
        "            return 5000 + (adv_i as i32);\n" ++
        "        }\n" ++
        "        let overlong2 = [0xC0_u8 | (((word >> 32_u64) as u8) & 1_u8), 0x80_u8 | (high_b2 & 0x3F_u8)];\n" ++
        "        if encode_wtf8_to_wtf16(&overlong2, &mut u16_out) != .Err(.InvalidWtf8) {\n" ++
        "            return 6000 + (adv_i as i32);\n" ++
        "        }\n" ++
        "        adv_i += 1_usize;\n" ++
        "    }\n" ++
        "    0\n" ++
        "}\n";

    try runFuzzProbeFourTier(
        std.testing.allocator,
        std.testing.io,
        "fuzz2_wtf8_wtf16_surrogates",
        fuzz_wtf8_src,
        0,
    );
}

// --------------- Fuzz 3: Buffered Chaos Streams ---------------

test "test_std02_fuzz_io_bufreader_short_reads_eintr_and_bufwriter_vectored" {
    const fuzz_io_src =
        "use cx.col.Vec;\n" ++
        "use cx.io.{\n" ++
        "    BufReader,\n" ++
        "    BufWriter,\n" ++
        "    IoError,\n" ++
        "    IoSlice,\n" ++
        "    OutBuf,\n" ++
        "    Reader,\n" ++
        "    ReaderVTable,\n" ++
        "    Writer,\n" ++
        "    WriterVTable,\n" ++
        "};\n\n" ++
        "fn next_rng(state: &mut u64, /) -> u64 {\n" ++
        "    state.* = state.* +% 0x9E37_79B9_7F4A_7C15_u64;\n" ++
        "    var z_val: u64 = state.*;\n" ++
        "    z_val = (z_val ^ (z_val >> 30_u64)) *% 0xBF58_476D_1CE4_E5B9_u64;\n" ++
        "    z_val = (z_val ^ (z_val >> 27_u64)) *% 0x94D0_49BB_1331_11EB_u64;\n" ++
        "    z_val ^ (z_val >> 31_u64)\n" ++
        "}\n\n" ++
        "struct ChaosReadState {\n" ++
        "    data_ptr: *u8,\n" ++
        "    data_len: usize,\n" ++
        "    pos: usize,\n" ++
        "    rng: u64,\n" ++
        "}\n\n" ++
        "fn chaos_read_out(ctx: *mut opaque, out: &mut OutBuf) -> usize!IoError {\n" ++
        "    let st_ptr = ctx as *mut ChaosReadState;\n" ++
        "    if st_ptr.is_null() {\n" ++
        "        return .Ok(0_usize);\n" ++
        "    }\n" ++
        "    let st: &mut ChaosReadState = unsafe { &mut st_ptr.* };\n" ++
        "    if st.pos >= st.data_len or st.data_ptr.is_null() {\n" ++
        "        return .Ok(0_usize);\n" ++
        "    }\n" ++
        "    let word: u64 = next_rng(&mut st.rng);\n" ++
        "    if (word & 3_u64) == 0_u64 {\n" ++
        "        return .Err(IoError.from_kind(.Interrupted, op: .Read));\n" ++
        "    }\n" ++
        "    let max_step: usize = 1_usize + (((word >> 4_u64) as usize) % 5_usize);\n" ++
        "    let avail: usize = st.data_len - st.pos;\n" ++
        "    let step: usize = if avail < max_step => avail else max_step;\n" ++
        "    let base_ptr: *u8 = st.data_ptr;\n" ++
        "    if base_ptr.is_null() {\n" ++
        "        return .Ok(0_usize);\n" ++
        "    }\n" ++
        "    let slice: &[u8] = unsafe { @slice_from_raw_parts(base_ptr.add(st.pos), step) };\n" ++
        "    let wrote: usize = out.append(slice);\n" ++
        "    st.pos += wrote;\n" ++
        "    .Ok(wrote)\n" ++
        "}\n\n" ++
        "struct ChaosWriteState {\n" ++
        "    out_vec: Vec[u8],\n" ++
        "    rng: u64,\n" ++
        "}\n\n" ++
        "fn chaos_write(ctx: *mut opaque, data: &[u8]) -> usize!IoError {\n" ++
        "    let st_ptr = ctx as *mut ChaosWriteState;\n" ++
        "    if st_ptr.is_null() {\n" ++
        "        return .Ok(0_usize);\n" ++
        "    }\n" ++
        "    if data.is_empty() {\n" ++
        "        return .Ok(0_usize);\n" ++
        "    }\n" ++
        "    let st: &mut ChaosWriteState = unsafe { &mut st_ptr.* };\n" ++
        "    let word: u64 = next_rng(&mut st.rng);\n" ++
        "    if (word & 3_u64) == 0_u64 {\n" ++
        "        return .Err(IoError.from_kind(.Interrupted, op: .Write));\n" ++
        "    }\n" ++
        "    let max_step: usize = 1_usize + (((word >> 4_u64) as usize) % 6_usize);\n" ++
        "    let step: usize = if data.len() < max_step => data.len() else max_step;\n" ++
        "    st.out_vec.extend_from_slice(data[0..step]);\n" ++
        "    .Ok(step)\n" ++
        "}\n\n" ++
        "pub fn run_fuzz() -> i32 {\n" ++
        "    var rng = 0x1102_57D0_2FA7_0003_u64;\n" ++
        "    let chaos_read_vt = ReaderVTable {\n" ++
        "        read_out: chaos_read_out,\n" ++
        "        read_vectored: .None,\n" ++
        "        discard: .None,\n" ++
        "    };\n" ++
        "    let chaos_write_vt = WriterVTable {\n" ++
        "        write: chaos_write,\n" ++
        "        write_vectored: .None,\n" ++
        "        flush: .None,\n" ++
        "    };\n\n" ++
        "    var raw_stream = Vec[u8].with_capacity(2_048_usize);\n" ++
        "    var exp_concat = Vec[u8].with_capacity(2_048_usize);\n" ++
        "    var line_idx = 0_usize;\n" ++
        "    while line_idx < 120_usize {\n" ++
        "        let word: u64 = next_rng(&mut rng);\n" ++
        "        let line_len: usize = (word as usize) % 13_usize;\n" ++
        "        var ch_i = 0_usize;\n" ++
        "        while ch_i < line_len {\n" ++
        "            let shift_amt = ((ch_i % 6_usize) * 4_usize) as u64;\n" ++
        "            let ch_b: u8 = b'a' + ((((word >> shift_amt) as usize) % 26_usize) as u8);\n" ++
        "            raw_stream.push(ch_b);\n" ++
        "            exp_concat.push(ch_b);\n" ++
        "            ch_i += 1_usize;\n" ++
        "        }\n" ++
        "        if (word & 0x1000_u64) != 0_u64 {\n" ++
        "            raw_stream.push(b'\\r');\n" ++
        "        }\n" ++
        "        raw_stream.push(b'\\n');\n" ++
        "        exp_concat.push(b'|');\n" ++
        "        line_idx += 1_usize;\n" ++
        "    }\n\n" ++
        "    var rd_state = ChaosReadState {\n" ++
        "        data_ptr: raw_stream.as_slice().as_ptr(),\n" ++
        "        data_len: raw_stream.len(),\n" ++
        "        pos: 0_usize,\n" ++
        "        rng: 0xABCD_EF01_2345_6789_u64,\n" ++
        "    };\n" ++
        "    let chaos_rd = unsafe {\n" ++
        "        Reader.from_raw((&raw mut rd_state) as *mut opaque, &raw chaos_read_vt)\n" ++
        "    };\n" ++
        "    var tiny_rd_buf: [u8; 17];\n" ++
        "    var buf_rd = BufReader.over_uninit(chaos_rd, &out tiny_rd_buf);\n" ++
        "    var got_concat = Vec[u8].with_capacity(2_048_usize);\n" ++
        "    var got_lines = 0_usize;\n" ++
        "    while true {\n" ++
        "        let opt_line: str? = buf_rd.next_line() catch return 10;\n" ++
        "        if opt_line is .Some(line_str) {\n" ++
        "            got_concat.extend_from_slice(line_str.as_bytes());\n" ++
        "            got_concat.push(b'|');\n" ++
        "            got_lines += 1_usize;\n" ++
        "        } else {\n" ++
        "            break;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    if got_lines != 120_usize or got_concat.as_slice() != exp_concat.as_slice() {\n" ++
        "        return 11;\n" ++
        "    }\n\n" ++
        "    rd_state.pos = 0_usize;\n" ++
        "    let chaos_rd2 = unsafe {\n" ++
        "        Reader.from_raw((&raw mut rd_state) as *mut opaque, &raw chaos_read_vt)\n" ++
        "    };\n" ++
        "    var micro_buf: [u8; 7];\n" ++
        "    var micro_rd = BufReader.over_uninit(chaos_rd2, &out micro_buf);\n" ++
        "    var rebuilt = Vec[u8].with_capacity(2_048_usize);\n" ++
        "    while true {\n" ++
        "        let step_n: usize = micro_rd.read_until_into(b'\\n', &mut rebuilt) catch return 12;\n" ++
        "        if step_n == 0_usize {\n" ++
        "            break;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    if rebuilt.as_slice() != raw_stream.as_slice() {\n" ++
        "        return 13;\n" ++
        "    }\n\n" ++
        "    var wr_state = ChaosWriteState {\n" ++
        "        out_vec: Vec[u8].with_capacity(4_096_usize),\n" ++
        "        rng: 0x7777_8888_9999_AAAA_u64,\n" ++
        "    };\n" ++
        "    let chaos_wr = unsafe {\n" ++
        "        Writer.from_raw((&raw mut wr_state) as *mut opaque, &raw chaos_write_vt)\n" ++
        "    };\n" ++
        "    var tiny_wr_buf: [u8; 11];\n" ++
        "    var buf_wr = BufWriter.over_uninit(chaos_wr, &out tiny_wr_buf);\n" ++
        "    var ref_out = Vec[u8].with_capacity(4_096_usize);\n" ++
        "    var op_i = 0_usize;\n" ++
        "    while op_i < 220_usize {\n" ++
        "        let word: u64 = next_rng(&mut rng);\n" ++
        "        let mode: u64 = word % 3_u64;\n" ++
        "        if mode == 0_u64 {\n" ++
        "            let b_val = (word & 0xFF_u64) as u8;\n" ++
        "            buf_wr.write_byte(b_val) catch { buf_wr.discard(); return 20; };\n" ++
        "            ref_out.push(b_val);\n" ++
        "        } else if mode == 1_u64 {\n" ++
        "            let chunk_len: usize = ((word >> 8_u64) as usize) % 19_usize;\n" ++
        "            let sample: &[u8] = raw_stream.as_slice()[0..chunk_len];\n" ++
        "            buf_wr.write_all(sample) catch { buf_wr.discard(); return 21; };\n" ++
        "            ref_out.extend_from_slice(sample);\n" ++
        "        } else {\n" ++
        "            let len_a: usize = ((word >> 8_u64) as usize) % 9_usize;\n" ++
        "            let len_b: usize = ((word >> 16_u64) as usize) % 15_usize;\n" ++
        "            let sl_a: &[u8] = raw_stream.as_slice()[0..len_a];\n" ++
        "            let sl_b: &[u8] = raw_stream.as_slice()[len_a..(len_a + len_b)];\n" ++
        "            let iovs = [IoSlice.new(sl_a), IoSlice.new(\"\".as_bytes()), IoSlice.new(sl_b)];\n" ++
        "            buf_wr.write_all_vectored(&iovs) catch { buf_wr.discard(); return 22; };\n" ++
        "            ref_out.extend_from_slice(sl_a);\n" ++
        "            ref_out.extend_from_slice(sl_b);\n" ++
        "        }\n" ++
        "        op_i += 1_usize;\n" ++
        "    }\n" ++
        "    buf_wr.close() catch return 23;\n" ++
        "    if wr_state.out_vec.as_slice() != ref_out.as_slice() {\n" ++
        "        return 24;\n" ++
        "    }\n" ++
        "    0\n" ++
        "}\n";

    try runFuzzProbeFourTier(
        std.testing.allocator,
        std.testing.io,
        "fuzz3_io_chaos_streams",
        fuzz_io_src,
        0,
    );
}

// ---------------- Fuzz 4: Win32 MSVCRT Quoting ----------------

test "test_std02_fuzz_env_win32_cmdline_msvcrt_quoting_roundtrip" {
    const fuzz_cmdline_src =
        "use cx.col.Vec;\n" ++
        "use cx.env.parse_win32_cmdline_in;\n" ++
        "use cx.mem.Arena;\n" ++
        "use cx.path.{Path, PathBuf, decode_wtf16_to_path_buf};\n\n" ++
        "fn next_rng(state: &mut u64, /) -> u64 {\n" ++
        "    state.* = state.* +% 0x9E37_79B9_7F4A_7C15_u64;\n" ++
        "    var z_val: u64 = state.*;\n" ++
        "    z_val = (z_val ^ (z_val >> 30_u64)) *% 0xBF58_476D_1CE4_E5B9_u64;\n" ++
        "    z_val = (z_val ^ (z_val >> 27_u64)) *% 0x94D0_49BB_1331_11EB_u64;\n" ++
        "    z_val ^ (z_val >> 31_u64)\n" ++
        "}\n\n" ++
        "fn append_msvcrt_quoted_arg(arg_u16: &[u16], dst_cmd: &mut Vec[u16], /) {\n" ++
        "    var needs_quotes: bool = arg_u16.is_empty();\n" ++
        "    var idx = 0_usize;\n" ++
        "    while idx < arg_u16.len() {\n" ++
        "        let code_unit: u16 = arg_u16[idx];\n" ++
        "        if code_unit == 0x0020_u16 or code_unit == 0x0009_u16 or code_unit == 0x0022_u16 {\n" ++
        "            needs_quotes = true;\n" ++
        "            break;\n" ++
        "        }\n" ++
        "        idx += 1_usize;\n" ++
        "    }\n" ++
        "    if not needs_quotes {\n" ++
        "        dst_cmd.extend_from_slice(arg_u16);\n" ++
        "        return;\n" ++
        "    }\n" ++
        "    dst_cmd.push(0x0022_u16);\n" ++
        "    var slash_run = 0_usize;\n" ++
        "    var pos = 0_usize;\n" ++
        "    while pos < arg_u16.len() {\n" ++
        "        let code_unit: u16 = arg_u16[pos];\n" ++
        "        if code_unit == 0x005C_u16 {\n" ++
        "            slash_run += 1_usize;\n" ++
        "        } else if code_unit == 0x0022_u16 {\n" ++
        "            var rep = 0_usize;\n" ++
        "            while rep < (slash_run * 2_usize + 1_usize) {\n" ++
        "                dst_cmd.push(0x005C_u16);\n" ++
        "                rep += 1_usize;\n" ++
        "            }\n" ++
        "            dst_cmd.push(0x0022_u16);\n" ++
        "            slash_run = 0_usize;\n" ++
        "        } else {\n" ++
        "            var rep_s = 0_usize;\n" ++
        "            while rep_s < slash_run {\n" ++
        "                dst_cmd.push(0x005C_u16);\n" ++
        "                rep_s += 1_usize;\n" ++
        "            }\n" ++
        "            slash_run = 0_usize;\n" ++
        "            dst_cmd.push(code_unit);\n" ++
        "        }\n" ++
        "        pos += 1_usize;\n" ++
        "    }\n" ++
        "    var tail_s = 0_usize;\n" ++
        "    while tail_s < (slash_run * 2_usize) {\n" ++
        "        dst_cmd.push(0x005C_u16);\n" ++
        "        tail_s += 1_usize;\n" ++
        "    }\n" ++
        "    dst_cmd.push(0x0022_u16);\n" ++
        "}\n\n" ++
        "pub fn run_fuzz() -> i32 {\n" ++
        "    var rng = 0x1102_57D0_2FA7_0004_u64;\n" ++
        "    var arena = Arena.new(slab_bytes: 16_384_usize);\n" ++
        "    var cmd_u16 = Vec[u16].with_capacity(256_usize);\n" ++
        "    var expected_pbs = Vec[PathBuf].with_capacity(8_usize);\n" ++
        "    var single_arg = [0_u16; 20];\n" ++
        "    var failure_code = 0;\n\n" ++
        "    var iter_i = 0_usize;\n" ++
        "    while iter_i < 250_usize {\n" ++
        "        arena.reset();\n" ++
        "        cmd_u16.clear();\n" ++
        "        expected_pbs.clear();\n\n" ++
        "        let exe_u16 = [0x0063_u16, 0x006F_u16, 0x0072_u16, 0x0065_u16, 0x0078_u16, 0x002E_u16, 0x0065_u16, 0x0078_u16, 0x0065_u16];\n" ++
        "        if (iter_i & 1_usize) == 0_usize {\n" ++
        "            cmd_u16.push(0x0022_u16);\n" ++
        "            cmd_u16.extend_from_slice(&exe_u16);\n" ++
        "            cmd_u16.push(0x0022_u16);\n" ++
        "        } else {\n" ++
        "            cmd_u16.extend_from_slice(&exe_u16);\n" ++
        "        }\n" ++
        "        expected_pbs.push(decode_wtf16_to_path_buf(&exe_u16));\n\n" ++
        "        let extra_argc: usize = (next_rng(&mut rng) as usize) % 7_usize;\n" ++
        "        var arg_idx = 0_usize;\n" ++
        "        while arg_idx < extra_argc {\n" ++
        "            let sep_w: u64 = next_rng(&mut rng);\n" ++
        "            cmd_u16.push(if (sep_w & 1_u64) == 0_u64 => 0x0020_u16 else 0x0009_u16);\n" ++
        "            if (sep_w & 2_u64) != 0_u64 {\n" ++
        "                cmd_u16.push(0x0020_u16);\n" ++
        "            }\n" ++
        "            let arg_len: usize = ((sep_w >> 8_u64) as usize) % 15_usize;\n" ++
        "            var char_i = 0_usize;\n" ++
        "            while char_i < arg_len {\n" ++
        "                let c_word: u64 = next_rng(&mut rng);\n" ++
        "                let kind: u64 = c_word % 7_u64;\n" ++
        "                let picked_u16: u16 = if kind == 0_u64 {\n" ++
        "                    0x005C_u16\n" ++
        "                } else if kind == 1_u64 {\n" ++
        "                    0x0022_u16\n" ++
        "                } else if kind == 2_u64 {\n" ++
        "                    0x0020_u16\n" ++
        "                } else if kind == 3_u64 {\n" ++
        "                    0x0009_u16\n" ++
        "                } else if kind == 4_u64 {\n" ++
        "                    0xD800_u16 + (((c_word >> 8_u64) as u16) & 0x03FF_u16)\n" ++
        "                } else if kind == 5_u64 {\n" ++
        "                    0xDC00_u16 + (((c_word >> 8_u64) as u16) & 0x03FF_u16)\n" ++
        "                } else {\n" ++
        "                    0x0061_u16 + (((c_word >> 8_u64) as u16) % 26_u16)\n" ++
        "                };\n" ++
        "                single_arg[char_i] = picked_u16;\n" ++
        "                char_i += 1_usize;\n" ++
        "            }\n" ++
        "            let arg_view: &[u16] = &single_arg;\n" ++
        "            let arg_slice: &[u16] = arg_view[0..arg_len];\n" ++
        "            append_msvcrt_quoted_arg(arg_slice, &mut cmd_u16);\n" ++
        "            expected_pbs.push(decode_wtf16_to_path_buf(arg_slice));\n" ++
        "            arg_idx += 1_usize;\n" ++
        "        }\n\n" ++
        "        {\n" ++
        "            let parsed: &[Path] = parse_win32_cmdline_in(&mut arena, cmd_u16.as_slice());\n" ++
        "            if parsed.len() != expected_pbs.len() {\n" ++
        "                failure_code = 1000 + (iter_i as i32);\n" ++
        "            } else {\n" ++
        "                var chk_i = 0_usize;\n" ++
        "                while chk_i < parsed.len() {\n" ++
        "                    if parsed[chk_i].as_bytes() != expected_pbs.as_slice()[chk_i].as_bytes() {\n" ++
        "                        failure_code = 2000 + (iter_i as i32);\n" ++
        "                        break;\n" ++
        "                    }\n" ++
        "                    chk_i += 1_usize;\n" ++
        "                }\n" ++
        "            }\n" ++
        "        }\n" ++
        "        if failure_code != 0 {\n" ++
        "            break;\n" ++
        "        }\n" ++
        "        iter_i += 1_usize;\n" ++
        "    }\n" ++
        "    arena.release();\n" ++
        "    failure_code\n" ++
        "}\n";

    try runFuzzProbeFourTier(
        std.testing.allocator,
        std.testing.io,
        "fuzz4_win32_cmdline_msvcrt_roundtrip",
        fuzz_cmdline_src,
        0,
    );
}

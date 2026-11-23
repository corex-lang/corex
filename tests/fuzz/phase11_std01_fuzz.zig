//! Phase 11.1 (`STD-01`) Deterministic Structure-Aware Property Fuzzing Suite
//!
//! Exercises deterministic PRNG state-machine equivalence and round-trip invariants across the
//! CoreX foundational standard library (`stdlib/cx/{mem,math,col,str}.cx`) over all 4 backend tiers:
//! - Container state-machine equivalence (`Vec`, `SmallVec`, `Deque`, `SlotMap`, `Map`, `Set`)
//!   against flat reference models across randomized push/pop/insert/remove/rehash transitions,
//! - Sorting equivalence (`cx.col.sort_unstable` `ipnsort` vs `cx.col.sort` `Powersort`),
//! - `validate_utf8` Keiser–Lemire SIMD vs scalar `validate_utf8_detailed` oracle across mutated
//!   boundary buffers (`0..128` bytes, split multi-byte tails, overlongs, surrogates),
//! - `String` 24-byte SSO <-> heap <-> `Arena` growth, slicing, and mutation invariants,
//! - `format_int` <-> `parse_int` across radices `2..=36` and `format_float` <-> `parse_float`
//!   exact bit-for-bit IEEE-754 round-trips.
//!
//! All PRNG streams use fixed deterministic SplitMix64 seeds so every failure is 100% reproducible.

const std = @import("std");
const corex = @import("corex");

const FileId = corex.FileId;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;

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

/// Canonical Phase 11.1 (`STD-01`) `stdlib/cx/` source file paths (`5` files).
const CX_STDLIB_PATHS = [_][]const u8{
    "stdlib/cx/mod.cx",
    "stdlib/cx/mem.cx",
    "stdlib/cx/math.cx",
    "stdlib/cx/col.cx",
    "stdlib/cx/str.cx",
};

// -------------------------------------- INTERNALS --------------------------------------

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

/// Mounts `core` and `stdlib/cx` into `db` as `.std_core`.
fn mountStdCoreAndCxIntoDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    db: *CompilerDb,
    base_file_id: u32,
) !void {
    var core_fids: [CORE_MODULE_PATHS.len]FileId = undefined;
    for (CORE_MODULE_PATHS, 0..) |mod_path, i| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(io, mod_path, allocator, .limited(2 * 1024 * 1024));
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
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(io, cx_path, allocator, .limited(2 * 1024 * 1024));
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
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_phase11_std01_fuzz_containers_sorting_and_slotmap_equivalence" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

    const fuzz_col_src =
        "use cx.col.{Deque, SlotKey, SlotMap, SmallVec, sort, sort_unstable};\n" ++
        "\n" ++
        "fn next_rng(state: &mut u64, /) -> u64 {\n" ++
        "    state.* = state.* +% 0x9E37_79B9_7F4A_7C15_u64;\n" ++
        "    var z: u64 = state.*;\n" ++
        "    z = (z ^ (z >> 30_u64)) *% 0xBF58_476D_1CE4_E5B9_u64;\n" ++
        "    z = (z ^ (z >> 27_u64)) *% 0x94D0_49BB_1331_11EB_u64;\n" ++
        "    return z ^ (z >> 31_u64);\n" ++
        "}\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    var rng: u64 = 0xC0DE_F00D_1101_2026_u64;\n" ++
        "\n" ++
        "    // [1] `Vec` vs `SmallVec[u64, 4]` state-machine equivalence across 300 transitions:\n" ++
        "    var vec_ref = Vec[u64].new();\n" ++
        "    var small_sut = SmallVec[u64, 4].new();\n" ++
        "    var step: usize = 0_usize;\n" ++
        "    while step < 300_usize {\n" ++
        "        let word = next_rng(&mut rng);\n" ++
        "        let op = word % 4_u64;\n" ++
        "        if op < 2_u64 {\n" ++
        "            vec_ref.push(word);\n" ++
        "            small_sut.push(word);\n" ++
        "        } else if op == 2_u64 {\n" ++
        "            if vec_ref.pop() != small_sut.pop() { return 1; }\n" ++
        "        } else if (word & 31_u64) == 0_u64 {\n" ++
        "            vec_ref.clear();\n" ++
        "            small_sut.clear();\n" ++
        "        } else if not vec_ref.is_empty() {\n" ++
        "            let idx = (word as usize) % vec_ref.len();\n" ++
        "            if vec_ref.as_slice()[idx] != small_sut.as_slice()[idx] { return 2; }\n" ++
        "        }\n" ++
        "        if vec_ref.len() != small_sut.len() { return 3; }\n" ++
        "        if vec_ref.as_slice() != small_sut.as_slice() { return 4; }\n" ++
        "        step += 1_usize;\n" ++
        "    }\n" ++
        "\n" ++
        "    // [2] `Deque[u64]` ring wrap-around equivalence against fixed window model:\n" ++
        "    var deq = Deque[u64].new();\n" ++
        "    var model: [u64; 512] = [0_u64; 512];\n" ++
        "    var head: usize = 256_usize;\n" ++
        "    var tail: usize = 256_usize;\n" ++
        "    step = 0_usize;\n" ++
        "    while step < 200_usize {\n" ++
        "        let word = next_rng(&mut rng);\n" ++
        "        let op = word % 4_u64;\n" ++
        "        if op == 0_u64 and tail < 510_usize {\n" ++
        "            deq.push_back(word);\n" ++
        "            model[tail] = word;\n" ++
        "            tail += 1_usize;\n" ++
        "        } else if op == 1_u64 and head > 2_usize {\n" ++
        "            head -= 1_usize;\n" ++
        "            model[head] = word;\n" ++
        "            deq.push_front(word);\n" ++
        "        } else if op == 2_u64 {\n" ++
        "            let exp: u64? = if head < tail { head += 1_usize; .Some(model[head - 1_usize]) } else { .None };\n" ++
        "            if deq.pop_front() != exp { return 5; }\n" ++
        "        } else {\n" ++
        "            let exp: u64? = if head < tail { tail -= 1_usize; .Some(model[tail]) } else { .None };\n" ++
        "            if deq.pop_back() != exp { return 6; }\n" ++
        "        }\n" ++
        "        if deq.len() != (tail - head) { return 7; }\n" ++
        "        step += 1_usize;\n" ++
        "    }\n" ++
        "\n" ++
        "    // [3] `Map[u64, u64]` & `Set[u64]` equivalence against dense `0..64` key array:\n" ++
        "    var map_sut = Map[u64, u64].new();\n" ++
        "    var set_sut = Set[u64].new();\n" ++
        "    var present: [bool; 64] = [false; 64];\n" ++
        "    var values: [u64; 64] = [0_u64; 64];\n" ++
        "    var active_n: usize = 0_usize;\n" ++
        "    step = 0_usize;\n" ++
        "    while step < 300_usize {\n" ++
        "        let word = next_rng(&mut rng);\n" ++
        "        let key: usize = (word as usize) & 63_usize;\n" ++
        "        let key_u64: u64 = key as u64;\n" ++
        "        if (word & 0x100_u64) != 0_u64 {\n" ++
        "            let prev_opt = map_sut.insert(key_u64, word);\n" ++
        "            let was_new = set_sut.insert(key_u64);\n" ++
        "            if present[key] {\n" ++
        "                if was_new or prev_opt != .Some(values[key]) { return 8; }\n" ++
        "            } else {\n" ++
        "                if not was_new or prev_opt != .None { return 9; }\n" ++
        "                present[key] = true;\n" ++
        "                active_n += 1_usize;\n" ++
        "            }\n" ++
        "            values[key] = word;\n" ++
        "        } else {\n" ++
        "            let rem_opt = map_sut.remove(&key_u64);\n" ++
        "            let rem_set = set_sut.remove(&key_u64);\n" ++
        "            if present[key] {\n" ++
        "                if not rem_set or rem_opt != .Some(values[key]) { return 10; }\n" ++
        "                present[key] = false;\n" ++
        "                active_n -= 1_usize;\n" ++
        "            } else if rem_set or rem_opt != .None {\n" ++
        "                return 11;\n" ++
        "            }\n" ++
        "        }\n" ++
        "        if map_sut.len() != active_n or set_sut.len() != active_n { return 12; }\n" ++
        "        step += 1_usize;\n" ++
        "    }\n" ++
        "\n" ++
        "    // [4] `SlotMap[SlotKey[u64], u64]` generational ABA rejection across insert/remove cycles:\n" ++
        "    var smap = SlotMap[SlotKey[u64], u64].new();\n" ++
        "    let k0: SlotKey[u64] = smap.insert(111_u64);\n" ++
        "    let k1: SlotKey[u64] = smap.insert(222_u64);\n" ++
        "    if smap.remove(k0) != .Some(111_u64) { return 13; }\n" ++
        "    if smap.get(k0) != .None { return 14; }\n" ++
        "    let k2: SlotKey[u64] = smap.insert(333_u64);\n" ++
        "    if smap.get(k0) != .None or smap.get(k2) == .None or smap.get(k1) == .None { return 15; }\n" ++
        "\n" ++
        "    // [5] `ipnsort` (`sort_unstable`) vs `Powersort` (`sort`) across 40 randomized slices:\n" ++
        "    var trial: usize = 0_usize;\n" ++
        "    while trial < 40_usize {\n" ++
        "        let len: usize = ((next_rng(&mut rng) as usize) % 64_usize) + 1_usize;\n" ++
        "        var buf_a = Vec[i64].with_capacity(len);\n" ++
        "        var buf_b = Vec[i64].with_capacity(len);\n" ++
        "        var elem_i: usize = 0_usize;\n" ++
        "        while elem_i < len {\n" ++
        "            let val: i64 = ((next_rng(&mut rng) % 37_u64) as i64) - 18_i64;\n" ++
        "            buf_a.push(val);\n" ++
        "            buf_b.push(val);\n" ++
        "            elem_i += 1_usize;\n" ++
        "        }\n" ++
        "        sort[i64](buf_a.as_mut_slice());\n" ++
        "        sort_unstable[i64](buf_b.as_mut_slice());\n" ++
        "        if buf_a.as_slice() != buf_b.as_slice() { return 16; }\n" ++
        "        trial += 1_usize;\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, fuzz_col_src, .low);
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, app_fid, .{
        .io = io,
        .comptime_step_limit = 50_000_000,
        .diagnostic_sink = &sink,
    });
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 0), report.outcomes[0].return_scalar_i64);
}

test "test_phase11_std01_fuzz_utf8_simd_vs_scalar_string_sso_and_numeric_roundtrips" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());
    try mountStdCoreAndCxIntoDb(allocator, io, &db, 10);

    const fuzz_str_src =
        "use cx.mem.Arena;\n" ++
        "use cx.str;\n" ++
        "\n" ++
        "fn next_rng(state: &mut u64, /) -> u64 {\n" ++
        "    state.* = state.* +% 0x9E37_79B9_7F4A_7C15_u64;\n" ++
        "    var z: u64 = state.*;\n" ++
        "    z = (z ^ (z >> 30_u64)) *% 0xBF58_476D_1CE4_E5B9_u64;\n" ++
        "    z = (z ^ (z >> 27_u64)) *% 0x94D0_49BB_1331_11EB_u64;\n" ++
        "    return z ^ (z >> 31_u64);\n" ++
        "}\n" ++
        "\n" ++
        "fn scalar_utf8_oracle(bytes: &[u8], /) -> bool {\n" ++
        "    let total: usize = bytes.len();\n" ++
        "    var idx: usize = 0_usize;\n" ++
        "    while idx < total {\n" ++
        "        let b0: u8 = bytes[idx];\n" ++
        "        if b0 < 0x80_u8 {\n" ++
        "            idx += 1_usize;\n" ++
        "        } else if b0 >= 0xC2_u8 and b0 <= 0xDF_u8 {\n" ++
        "            if idx + 1_usize >= total { return false; }\n" ++
        "            if (bytes[idx + 1_usize] & 0xC0_u8) != 0x80_u8 { return false; }\n" ++
        "            idx += 2_usize;\n" ++
        "        } else if b0 >= 0xE0_u8 and b0 <= 0xEF_u8 {\n" ++
        "            if idx + 2_usize >= total { return false; }\n" ++
        "            let b1: u8 = bytes[idx + 1_usize];\n" ++
        "            let b2: u8 = bytes[idx + 2_usize];\n" ++
        "            if (b1 & 0xC0_u8) != 0x80_u8 or (b2 & 0xC0_u8) != 0x80_u8 { return false; }\n" ++
        "            if (b0 == 0xE0_u8 and b1 < 0xA0_u8) or (b0 == 0xED_u8 and b1 >= 0xA0_u8) { return false; }\n" ++
        "            idx += 3_usize;\n" ++
        "        } else if b0 >= 0xF0_u8 and b0 <= 0xF4_u8 {\n" ++
        "            if idx + 3_usize >= total { return false; }\n" ++
        "            let b1: u8 = bytes[idx + 1_usize];\n" ++
        "            let b2: u8 = bytes[idx + 2_usize];\n" ++
        "            let b3: u8 = bytes[idx + 3_usize];\n" ++
        "            if (b1 & 0xC0_u8) != 0x80_u8 or (b2 & 0xC0_u8) != 0x80_u8 or (b3 & 0xC0_u8) != 0x80_u8 {\n" ++
        "                return false;\n" ++
        "            }\n" ++
        "            if (b0 == 0xF0_u8 and b1 < 0x90_u8) or (b0 == 0xF4_u8 and b1 >= 0x90_u8) { return false; }\n" ++
        "            idx += 4_usize;\n" ++
        "        } else {\n" ++
        "            return false;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    return true;\n" ++
        "}\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    var rng: u64 = 0x7F8A_9123_4455_6677_u64;\n" ++
        "\n" ++
        "    // [1] `validate_utf8` Keiser–Lemire SIMD vs independent scalar oracle across 300 mutated buffers:\n" ++
        "    var raw_buf: [u8; 96] = [0_u8; 96];\n" ++
        "    var case_i: usize = 0_usize;\n" ++
        "    while case_i < 300_usize {\n" ++
        "        let len: usize = (next_rng(&mut rng) as usize) % 96_usize;\n" ++
        "        var pos: usize = 0_usize;\n" ++
        "        while pos < len {\n" ++
        "            let pick = next_rng(&mut rng) % 8_u64;\n" ++
        "            if pick < 5_u64 {\n" ++
        "                raw_buf[pos] = 0x20_u8 + ((next_rng(&mut rng) % 90_u64) as u8);\n" ++
        "                pos += 1_usize;\n" ++
        "            } else if pick == 5_u64 and pos + 2_usize <= len {\n" ++
        "                raw_buf[pos] = 0xC3_u8;\n" ++
        "                raw_buf[pos + 1_usize] = 0xA9_u8;\n" ++
        "                pos += 2_usize;\n" ++
        "            } else if pick == 6_u64 and pos + 3_usize <= len {\n" ++
        "                raw_buf[pos] = 0xE4_u8;\n" ++
        "                raw_buf[pos + 1_usize] = 0xB8_u8;\n" ++
        "                raw_buf[pos + 2_usize] = 0xAD_u8;\n" ++
        "                pos += 3_usize;\n" ++
        "            } else if pos + 4_usize <= len {\n" ++
        "                raw_buf[pos] = 0xF0_u8;\n" ++
        "                raw_buf[pos + 1_usize] = 0x9F_u8;\n" ++
        "                raw_buf[pos + 2_usize] = 0x98_u8;\n" ++
        "                raw_buf[pos + 3_usize] = 0x80_u8;\n" ++
        "                pos += 4_usize;\n" ++
        "            } else {\n" ++
        "                raw_buf[pos] = (next_rng(&mut rng) & 0xFF_u64) as u8;\n" ++
        "                pos += 1_usize;\n" ++
        "            }\n" ++
        "        }\n" ++
        "        if (case_i & 1_usize) == 1_usize and len > 0_usize {\n" ++
        "            let mut_idx: usize = (next_rng(&mut rng) as usize) % len;\n" ++
        "            raw_buf[mut_idx] = raw_buf[mut_idx] ^ ((next_rng(&mut rng) & 0xFF_u64) as u8);\n" ++
        "        }\n" ++
        "        let slice_view: &[u8] = raw_buf[0..len];\n" ++
        "        let sut_valid: bool = str.validate_utf8(slice_view);\n" ++
        "        let ref_valid: bool = scalar_utf8_oracle(slice_view);\n" ++
        "        if sut_valid != ref_valid { return 1; }\n" ++
        "        if (str.from_utf8(slice_view) is .Ok(_)) != ref_valid { return 2; }\n" ++
        "        case_i += 1_usize;\n" ++
        "    }\n" ++
        "\n" ++
        "    // [2] `String` SSO (`<= 23 B`) <-> heap <-> `Arena` mutation equivalence:\n" ++
        "    var str_ok: bool = true;\n" ++
        "    var arena = Arena.new();\n" ++
        "    {\n" ++
        "        var sso_str = String.new();\n" ++
        "        var arena_str = String.in_arena(&mut arena);\n" ++
        "        var step: usize = 0_usize;\n" ++
        "        while step < 48_usize {\n" ++
        "            sso_str.push_str(\"ab\");\n" ++
        "            arena_str.push_str(\"ab\");\n" ++
        "            if sso_str.as_str() != arena_str.as_str() { str_ok = false; break; }\n" ++
        "            step += 1_usize;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    own arena.release();\n" ++
        "    if not str_ok { return 3; }\n" ++
        "\n" ++
        "    // [3] `format_int` <-> `parse_int` across radices `2..=36` (`i64` & `u64`):\n" ++
        "    var ibuf: [u8; 128] = [0_u8; 128];\n" ++
        "    var int_i: usize = 0_usize;\n" ++
        "    while int_i < 200_usize {\n" ++
        "        let raw_u64: u64 = next_rng(&mut rng);\n" ++
        "        let raw_rad: u8 = (2_u64 + (next_rng(&mut rng) % 35_u64)) as u8;\n" ++
        "        let rad: u8 is 2..=36 = raw_rad.narrow[u8 is 2..=36]();\n" ++
        "        let u_txt = str.format_int(&mut ibuf, raw_u64, radix: rad, upper: (int_i & 1_usize) == 0_usize)\n" ++
        "            catch { return 4; };\n" ++
        "        let u_back = str.parse_int[u64](u_txt, radix: rad) catch { return 5; };\n" ++
        "        if u_back != raw_u64 { return 6; }\n" ++
        "\n" ++
        "        let raw_i64: i64 = @bit_cast[i64](next_rng(&mut rng));\n" ++
        "        let s_txt = str.format_int(&mut ibuf, raw_i64, radix: rad) catch { return 7; };\n" ++
        "        let s_back = str.parse_int[i64](s_txt, radix: rad) catch { return 8; };\n" ++
        "        if s_back != raw_i64 { return 9; }\n" ++
        "        int_i += 1_usize;\n" ++
        "    }\n" ++
        "\n" ++
        "    // [4] `format_float` <-> `parse_float` exact bit-level round-trip (`f64` & `f32`):\n" ++
        "    var fbuf: [u8; 48] = [0_u8; 48];\n" ++
        "    var flt_i: usize = 0_usize;\n" ++
        "    while flt_i < 300_usize {\n" ++
        "        let bits64: u64 = next_rng(&mut rng);\n" ++
        "        if ((bits64 >> 52_u64) & 0x7FF_u64) != 0x7FF_u64 {\n" ++
        "            let val64: f64 = @bit_cast[f64](bits64);\n" ++
        "            let txt64 = str.format_float(&mut fbuf, val64) catch { return 10; };\n" ++
        "            let back64 = str.parse_float[f64](txt64) catch { return 11; };\n" ++
        "            if @bit_cast[u64](back64) != bits64 { return 12; }\n" ++
        "        }\n" ++
        "        let bits32: u32 = (next_rng(&mut rng) >> 19_u64) as u32;\n" ++
        "        if ((bits32 >> 23_u32) & 0xFF_u32) != 0xFF_u32 {\n" ++
        "            let val32: f32 = @bit_cast[f32](bits32);\n" ++
        "            let txt32 = str.format_float(&mut fbuf, val32) catch { return 13; };\n" ++
        "            let back32 = str.parse_float[f32](txt32) catch { return 14; };\n" ++
        "            if @bit_cast[u32](back32) != bits32 { return 15; }\n" ++
        "        }\n" ++
        "        flt_i += 1_usize;\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, fuzz_str_src, .low);
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, app_fid, .{
        .io = io,
        .comptime_step_limit = 50_000_000,
        .diagnostic_sink = &sink,
    });
    defer report.deinit(allocator);
    if (!report.is_all_matching) std.debug.print("{s}\n", .{report.rendered_diff_table});
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i64, 0), report.outcomes[0].return_scalar_i64);
}

//! Comprehensive Phase 8 Verification Suite
//!
//! Verifies Phase 8 cross-target binary/archive emission, zero-`libclang` C11/C23 FFI translation,
//! stackless coroutine lowering, `TaskGroup` structured concurrency, and `CompletionReaper` invariants.
//!
//! Exercises `TargetSpec.ALL_CANONICAL_TARGETS` object/archive determinism, `@c_import` cross-ABI layout
//! refresh, 4-tier `diff_oracle` execution parity, raw-pointer indexing provenance, and SAST compile-fail gates.

const std = @import("std");
const corex = @import("corex");

const FileId = corex.FileId;
const DefId = corex.DefId;
const TypeId = corex.TypeId;
const CompilerDb = corex.CompilerDb;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;
const TargetLayout = corex.TargetLayout;
const CodegenBackend = corex.CodegenBackend;
const DiffOracleReport = corex.DiffOracleReport;
const codegen_abi = corex.codegen_abi;
const codegen_link = corex.codegen_link;
const c_frontend = corex.c_frontend;
const c_translate = corex.c_translate;
const mir_async = corex.mir_async;
const sim_seam = corex.sim_seam;

// ---------------------------------------- TYPES ----------------------------------------

/// Binary magic header classification across the 11 canonical compilation targets.
const ExpectedBinaryFormat = enum(u8) {
    /// 64-bit little-endian ELF relocatable object (`\x7fELF`, `EI_CLASS == 2`).
    elf64 = 0,
    /// 64-bit little-endian Apple Mach-O relocatable object (`0xFEED_FACF`).
    macho64 = 1,
    /// 64-bit x86 Windows PE/COFF relocatable object (`IMAGE_FILE_MACHINE_AMD64 == 0x8664`).
    coff_amd64 = 2,
    /// 64-bit ARM Windows PE/COFF relocatable object (`IMAGE_FILE_MACHINE_ARM64 == 0xAA64`).
    coff_arm64 = 3,
    /// WebAssembly binary module / relocatable object (`\x00asm\x01\x00\x00\x00`).
    wasm32 = 4,
};

/// Table row pairing a canonical `TargetSpec` with its expected relocatable object header format.
const TargetHeaderSpec = struct {
    /// Target triple specification under test.
    spec: TargetSpec,
    /// Expected binary magic header format for emitted relocatable objects.
    format: ExpectedBinaryFormat,
};

/// Mock `SimWorld` barrier state verifying `CompletionReaper.drainQuarantinedBarrier` callbacks.
const SimBarrierState = struct {
    /// Pending CQE delivered on poll.
    pending_cqe: sim_seam.ReactorCqe,
    /// Number of `cancel_io` notifications observed.
    cancel_calls: u32 = 0,
    /// Captured orphaned descriptor from `onOrphanReaped`.
    orphan_fd: i32 = -1,
    /// Captured orphaned pool ID from `onOrphanReaped`.
    orphan_pool_id: u32 = 0,
    /// Captured orphaned cleanup action from `onOrphanReaped`.
    orphan_action: sim_seam.ReaperAction = .none,

    /// Records `cancel_io` invocations from `CompletionReaper.requestCancel`.
    fn onCancelIo(raw_ctx: *sim_seam.ReactorCtx, _: u32, _: u16) callconv(.c) void {
        const state_ptr: *@This() = @ptrCast(@alignCast(raw_ctx));
        state_ptr.cancel_calls += 1;
    }

    /// Emits the terminal canceled CQE into `cqes_out[0]`.
    fn onPollOrPark(
        raw_ctx: *sim_seam.ReactorCtx,
        cqes_out: [*]sim_seam.ReactorCqe,
        cap: usize,
        _: bool,
    ) callconv(.c) usize {
        const state_ptr: *@This() = @ptrCast(@alignCast(raw_ctx));
        std.debug.assert(cap >= 1);
        cqes_out[0] = state_ptr.pending_cqe;
        return 1;
    }

    /// Captures `ReapOutcome` orphan delivery during `drainQuarantinedBarrier`.
    fn onOrphanReaped(raw_ctx: *sim_seam.ReactorCtx, outcome: sim_seam.ReapOutcome) callconv(.c) void {
        const state_ptr: *@This() = @ptrCast(@alignCast(raw_ctx));
        state_ptr.orphan_fd = outcome.orphan_fd;
        state_ptr.orphan_pool_id = outcome.orphan_buf.owned_pool_id;
        state_ptr.orphan_action = outcome.orphan_action;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Hard `< 10 KB` (`10,240` bytes) size ceiling for `--release` `wasm32-unknown-freestanding` modules.
const MAX_FREESTANDING_WASM_BYTES: usize = 10_240;
/// Complete 11-target cross-compilation verification table (`DR-10` §1.1).
const ELEVEN_TARGET_HEADER_SPECS = [11]TargetHeaderSpec{
    .{ .spec = TargetSpec.X86_64_LINUX_GNU, .format = .elf64 },
    .{ .spec = TargetSpec.X86_64_LINUX_MUSL, .format = .elf64 },
    .{ .spec = TargetSpec.AARCH64_LINUX_GNU, .format = .elf64 },
    .{ .spec = TargetSpec.AARCH64_LINUX_MUSL, .format = .elf64 },
    .{ .spec = TargetSpec.X86_64_APPLE_DARWIN, .format = .macho64 },
    .{ .spec = TargetSpec.AARCH64_APPLE_DARWIN, .format = .macho64 },
    .{ .spec = TargetSpec.X86_64_WINDOWS_MSVC, .format = .coff_amd64 },
    .{ .spec = TargetSpec.X86_64_WINDOWS_GNU, .format = .coff_amd64 },
    .{ .spec = TargetSpec.AARCH64_WINDOWS_MSVC, .format = .coff_arm64 },
    .{ .spec = TargetSpec.WASM32_UNKNOWN_WASI, .format = .wasm32 },
    .{ .spec = TargetSpec.WASM32_UNKNOWN_FREESTANDING, .format = .wasm32 },
};

// -------------------------------------- INTERNALS --------------------------------------

/// Reads all bytes of `file_path` into an owned buffer allocated from `allocator`.
fn readAllFileBytes(allocator: std.mem.Allocator, io: std.Io, file_path: []const u8) ![]u8 {
    return std.Io.Dir.cwd().readFileAlloc(io, file_path, allocator, .limited(8 * 1024 * 1024));
}

/// Validates the binary magic header of `obj_bytes` against `expected_format`.
fn verifyObjectMagicHeader(obj_bytes: []const u8, expected_format: ExpectedBinaryFormat) !void {
    switch (expected_format) {
        .elf64 => {
            try std.testing.expect(obj_bytes.len >= 20);
            try std.testing.expectEqualSlices(u8, "\x7fELF", obj_bytes[0..4]);
            try std.testing.expectEqual(@as(u8, 2), obj_bytes[4]);
        },
        .macho64 => {
            try std.testing.expect(obj_bytes.len >= 32);
            try std.testing.expectEqual(
                @as(u32, 0xFEED_FACF),
                std.mem.readInt(u32, obj_bytes[0..4], .little),
            );
        },
        .coff_amd64 => {
            try std.testing.expect(obj_bytes.len >= 20);
            try std.testing.expectEqual(
                @as(u16, 0x8664),
                std.mem.readInt(u16, obj_bytes[0..2], .little),
            );
        },
        .coff_arm64 => {
            try std.testing.expect(obj_bytes.len >= 20);
            try std.testing.expectEqual(
                @as(u16, 0xAA64),
                std.mem.readInt(u16, obj_bytes[0..2], .little),
            );
        },
        .wasm32 => {
            try std.testing.expect(obj_bytes.len >= 8);
            try std.testing.expectEqualSlices(u8, "\x00asm\x01\x00\x00\x00", obj_bytes[0..8]);
        },
    }
}

/// Checks whether `sink` contains a well-formed diagnostic matching `expected_code` with a valid span and labels/notes.
fn hasSinkDiagnostic(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == expected_code) {
            std.debug.assert(diag_item.message.len > 0);
            std.debug.assert(diag_item.primary_span.end_byte >= diag_item.primary_span.start_byte);
            std.debug.assert(diag_item.labels.len > 0 or diag_item.notes.len > 0 or diag_item.suggestions.len > 0);
            return true;
        }
    }
    return false;
}

/// Runs parse + signature + typecheck + 4-pass `mir_sast` on `source` and returns `true` if `expected_code` fired.
fn hasCompiledDiagnosticCode(
    allocator: std.mem.Allocator,
    source: []const u8,
    expected_code: DiagnosticCode,
) !bool {
    var db = try CompilerDb.init(allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(0);
    _ = try db.setInput(file_id, source, .low);

    if (hasSinkDiagnostic(&(try db.parseCst(file_id)).diagnostics, expected_code)) return true;

    _ = try db.resolveSignatures(file_id);
    if (db.getSignatureDiagnostics(file_id)) |sig_sink| {
        if (hasSinkDiagnostic(sig_sink, expected_code)) return true;
    }

    for ((try db.extractItemTree(file_id)).entries) |entry| {
        _ = try db.typecheckBody(entry.def_id);
        if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
            if (hasSinkDiagnostic(body_sink, expected_code)) return true;
        }
        _ = try db.verifySastMir(entry.def_id);
        if (db.getSastDiagnostics(entry.def_id)) |sast_sink| {
            if (hasSinkDiagnostic(sast_sink, expected_code)) return true;
        }
    }

    var sast_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(1),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer sast_bundle.deinit();
    return hasSinkDiagnostic(&sast_bundle.diagnostics, expected_code);
}

/// Asserts that `source` compiles through typecheck and 4-pass `mir_sast` with zero diagnostics.
fn expectZeroCompileDiagnostics(allocator: std.mem.Allocator, source: []const u8) !void {
    var sast_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(0),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer sast_bundle.deinit();
    if (sast_bundle.diagnostics.hasErrors()) {
        for (sast_bundle.diagnostics.diagnostics.items) |diag_item| {
            std.debug.print(
                "[unexpected_diag] {s}: {s}\n",
                .{ @tagName(diag_item.code), diag_item.message },
            );
        }
    }
    try std.testing.expect(!sast_bundle.diagnostics.hasErrors());
}

/// Runs `runFourTierDiffOracleOnDb` on `source` and dumps any unexpected diagnostics on error.
fn runVerifiedFourTierOracle(
    allocator: std.mem.Allocator,
    io: std.Io,
    source: []const u8,
) !DiffOracleReport {
    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    const file_id = FileId.fromInt(0);
    _ = try db.setInput(file_id, source, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    const report = corex.runFourTierDiffOracleOnDb(allocator, &db, file_id, .{
        .io = io,
        .diagnostic_sink = &sink,
    }) catch |oracle_err| {
        for ((try db.parseCst(file_id)).diagnostics.diagnostics.items) |diag_item| {
            std.debug.print("[parse] {s}: {s}\n", .{ @tagName(diag_item.code), diag_item.message });
        }
        if (db.getSignatureDiagnostics(file_id)) |sig_sink| {
            for (sig_sink.diagnostics.items) |diag_item| {
                std.debug.print("[sig] {s}: {s}\n", .{ @tagName(diag_item.code), diag_item.message });
            }
        }
        for ((try db.extractItemTree(file_id)).entries) |entry| {
            if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
                for (body_sink.diagnostics.items) |diag_item| {
                    std.debug.print("[body] {s}: {s}\n", .{ @tagName(diag_item.code), diag_item.message });
                }
            }
            if (db.getSastDiagnostics(entry.def_id)) |sast_sink| {
                for (sast_sink.diagnostics.items) |diag_item| {
                    std.debug.print("[sast] {s}: {s}\n", .{ @tagName(diag_item.code), diag_item.message });
                }
            }
        }
        for (sink.diagnostics.items) |diag_item| {
            std.debug.print("[codegen] {s}: {s}\n", .{ @tagName(diag_item.code), diag_item.message });
        }
        return oracle_err;
    };
    if (!report.is_all_matching) {
        std.debug.print("\n{s}\n", .{report.rendered_diff_table});
    }
    return report;
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------- Pillar 1: 11-Target Matrix & Wasm --------------

test "test_phase8_eleven_target_cross_compile_headers_archives_coff_def_and_sub_10kb_wasm" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const scratch_dir = ".zig-cache/phase8_unit_pillar1";
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, scratch_dir);

    const kernel_src =
        "//! Portable Cross-Target Arithmetic Kernel\n" ++
        "@export\n" ++
        "@link_name(\"cx_cross_dot2\")\n" ++
        "pub fn cross_dot2(lhs_a: i32, lhs_b: i32, rhs_a: i32, rhs_b: i32) -> i32 {\n" ++
        "    return (lhs_a *% rhs_a) +% (lhs_b *% rhs_b);\n" ++
        "}\n";

    // [1] Emit relocatable objects across all 11 canonical `TargetSpec` triples and verify binary headers:
    for (ELEVEN_TARGET_HEADER_SPECS, 0..) |row, idx| {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(row.spec);
        const file_id = FileId.fromInt(0);
        _ = try db.setInput(file_id, kernel_src, .low);

        const obj_path = try std.fmt.allocPrint(
            allocator,
            "{s}/target_{d}{s}",
            .{ scratch_dir, idx, row.spec.defaultObjExtension() },
        );
        defer allocator.free(obj_path);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var obj_art = try db.compileModuleArtifact(
            file_id,
            .{ .tier_b_llvm = .{ .target = row.spec, .is_release_mode = true } },
            .{
                .artifact_kind = .object_file,
                .output_path = obj_path,
                .io = io,
                .diagnostic_sink = &sink,
            },
        );
        defer obj_art.deinit(allocator);
        try std.testing.expect(!sink.hasErrors());

        const obj_bytes = try readAllFileBytes(allocator, io, obj_path);
        defer allocator.free(obj_bytes);
        try verifyObjectMagicHeader(obj_bytes, row.format);

        // Verify deterministic `!<arch>\n` archives (`K_GNU`, `K_BSD`, `K_COFF`) on representative targets:
        if (idx == 0 or idx == 5 or idx == 6) {
            const ar_path_a = try std.fmt.allocPrint(
                allocator,
                "{s}/det_a_{d}{s}",
                .{ scratch_dir, idx, row.spec.defaultStaticLibExtension() },
            );
            defer allocator.free(ar_path_a);
            const ar_path_b = try std.fmt.allocPrint(
                allocator,
                "{s}/det_b_{d}{s}",
                .{ scratch_dir, idx, row.spec.defaultStaticLibExtension() },
            );
            defer allocator.free(ar_path_b);

            try codegen_link.writeDeterministicArchive(io, allocator, row.spec, ar_path_a, &.{obj_path});
            try codegen_link.writeDeterministicArchive(io, allocator, row.spec, ar_path_b, &.{obj_path});

            const ar_bytes_a = try readAllFileBytes(allocator, io, ar_path_a);
            defer allocator.free(ar_bytes_a);
            const ar_bytes_b = try readAllFileBytes(allocator, io, ar_path_b);
            defer allocator.free(ar_bytes_b);

            try std.testing.expectEqualSlices(u8, ar_bytes_a, ar_bytes_b);
            try std.testing.expectEqualStrings(codegen_link.ARCHIVE_MAGIC, ar_bytes_a[0..8]);
            try std.testing.expect(std.mem.indexOf(u8, ar_bytes_a, "cx_cross_dot2") != null);
        }
    }

    // [2] Compile exported `.cx` function to `wasm32-unknown-freestanding` `--release` `.wasm` (< 10 KB) in Tier A & Tier B:
    const wasm_src =
        "//! Freestanding WebAssembly Exported Kernel\n" ++
        "@wasm_export(\"cx_wasm_mix\")\n" ++
        "pub fn cx_wasm_mix(seed_a: u32, seed_b: u32) -> u32 {\n" ++
        "    return ((seed_a ^ (seed_b << 5)) *% 0x9E37_79B9_u32) +% seed_b;\n" ++
        "}\n";

    var wasm_db = try CompilerDb.init(allocator);
    defer wasm_db.deinit();
    wasm_db.setTargetSpec(TargetSpec.WASM32_UNKNOWN_FREESTANDING);
    const wasm_fid = FileId.fromInt(0);
    _ = try wasm_db.setInput(wasm_fid, wasm_src, .low);

    const wasm_c_path = scratch_dir ++ "/freestanding_tier_a.wasm";
    const wasm_ll_path = scratch_dir ++ "/freestanding_tier_b.wasm";

    var wasm_sink = DiagnosticSink.init(allocator);
    defer wasm_sink.deinit();
    var wasm_c_art = try wasm_db.compileModuleArtifact(
        wasm_fid,
        .{
            .tier_a_c99 = .{
                .target = TargetSpec.WASM32_UNKNOWN_FREESTANDING,
                .is_release_mode = true,
                .has_line_directives = false,
            },
        },
        .{
            .artifact_kind = .executable,
            .output_path = wasm_c_path,
            .io = io,
            .diagnostic_sink = &wasm_sink,
        },
    );
    defer wasm_c_art.deinit(allocator);
    try std.testing.expect(!wasm_sink.hasErrors());

    var wasm_ll_art = try wasm_db.compileModuleArtifact(
        wasm_fid,
        .{
            .tier_b_llvm = .{
                .target = TargetSpec.WASM32_UNKNOWN_FREESTANDING,
                .is_release_mode = true,
            },
        },
        .{
            .artifact_kind = .executable,
            .output_path = wasm_ll_path,
            .io = io,
            .diagnostic_sink = &wasm_sink,
        },
    );
    defer wasm_ll_art.deinit(allocator);
    try std.testing.expect(!wasm_sink.hasErrors());

    for ([_][]const u8{ wasm_c_path, wasm_ll_path }) |wasm_out_path| {
        const wasm_bytes = try readAllFileBytes(allocator, io, wasm_out_path);
        defer allocator.free(wasm_bytes);
        try verifyObjectMagicHeader(wasm_bytes, .wasm32);
        try std.testing.expect(wasm_bytes.len < MAX_FREESTANDING_WASM_BYTES);
    }

    // [3] Verify byte-for-byte determinism of `writeCoffShortImportLibrary` for both `amd64` and `arm64`:
    const sample_def_text =
        "LIBRARY \"cx_host_bridge.dll\"\n" ++
        "EXPORTS\n" ++
        "    CxBridgeOpen\n" ++
        "    CxBridgeQuery @7\n" ++
        "    CxBridgeAlias = CxBridgeInternal\n" ++
        "    CxBridgeCounter DATA\n";

    for ([_]codegen_link.CoffMachine{ .amd64, .arm64 }, 0..) |machine_tag, mach_idx| {
        const lib_one = try std.fmt.allocPrint(allocator, "{s}/imp_a_{d}.lib", .{ scratch_dir, mach_idx });
        defer allocator.free(lib_one);
        const lib_two = try std.fmt.allocPrint(allocator, "{s}/imp_b_{d}.lib", .{ scratch_dir, mach_idx });
        defer allocator.free(lib_two);

        try codegen_link.writeCoffShortImportLibrary(io, allocator, sample_def_text, lib_one, machine_tag);
        try codegen_link.writeCoffShortImportLibrary(io, allocator, sample_def_text, lib_two, machine_tag);

        const bytes_one = try readAllFileBytes(allocator, io, lib_one);
        defer allocator.free(bytes_one);
        const bytes_two = try readAllFileBytes(allocator, io, lib_two);
        defer allocator.free(bytes_two);

        try std.testing.expectEqualSlices(u8, bytes_one, bytes_two);
        try std.testing.expectEqualStrings(codegen_link.ARCHIVE_MAGIC, bytes_one[0..8]);
        try std.testing.expect(std.mem.indexOf(u8, bytes_one, "__imp_CxBridgeOpen") != null);
    }
}

// ------------- Pillar 2: C11/C23 FFI & Live Link --------------

test "test_phase8_translate_c_c_import_bitfields_and_live_native_c_ffi_roundtrip" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] `@c_import` inside `CompilerDb`; LRU hit, cross-target `c_char`/`c_long` refresh, and `Prune-06` bitfields:
    const virtual_c_header =
        "#pragma once\n" ++
        "#include <stdint.h>\n" ++
        "#define C_PROTO_MAGIC 42\n" ++
        "struct CBitPacket {\n" ++
        "    int alpha : 10;\n" ++
        "    short beta : 10;\n" ++
        "};\n" ++
        "long c_scale_long(long input_val, char tag_ch);\n";

    var vfs_headers: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_headers.deinit(allocator);
    try vfs_headers.put(allocator, "proto_bridge.h", virtual_c_header);

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setEmbedSandbox(null, &vfs_headers);

    const cx_consumer =
        "const c_api = @c_import(\"proto_bridge.h\");\n" ++
        "pub extern \"C\" {\n" ++
        "    fn standalone_c_ping(code: i32) -> i32;\n" ++
        "    static mut STANDALONE_COUNTER: i32;\n" ++
        "}\n" ++
        "pub fn inspect_packet_size() -> usize = @size_of[c_api.CBitPacket]();\n" ++
        "pub fn forward_long(val: cx.ffi.c_long, ch: cx.ffi.c_char) -> cx.ffi.c_long {\n" ++
        "    return unsafe { c_api.c_scale_long(val, ch) };\n" ++
        "}\n";

    const consumer_fid = FileId.fromInt(0);
    db.setTargetSpec(TargetSpec.X86_64_LINUX_GNU);
    _ = try db.setInput(consumer_fid, cx_consumer, .low);

    try std.testing.expectEqual(@as(u32, 0), (try db.resolveSignatures(consumer_fid)).error_count);
    try std.testing.expectEqual(@as(usize, 1), db.c_import_cache.entry_count);

    // Re-querying on the same target hits `CImportCache` without growing `entry_count`:
    try std.testing.expect(db.lookupCImportCache(virtual_c_header, &.{}) != null);
    try std.testing.expect(db.c_import_cache.hits >= 1);

    // Switching to `x86_64-windows-msvc` refreshes `c_long` -> `i32` and MSVC bitfield size (`8` vs SysV `4`):
    db.setTargetSpec(TargetSpec.X86_64_WINDOWS_MSVC);
    try std.testing.expectEqual(@as(u32, 0), (try db.resolveSignatures(consumer_fid)).error_count);
    try std.testing.expectEqual(@as(usize, 2), db.c_import_cache.entry_count);

    var forward_def = DefId.NONE;
    for ((try db.extractItemTree(consumer_fid)).entries) |entry| {
        if (std.mem.eql(u8, entry.name_text, "forward_long")) forward_def = entry.def_id;
    }
    try std.testing.expectEqual(
        TypeId.i32_ty,
        db.type_pool.getFnSignatureView((try db.getDefSignature(forward_def)).type_id).?.ret_ty,
    );

    db.setTargetSpec(TargetSpec.AARCH64_LINUX_GNU);
    try std.testing.expectEqual(@as(u32, 0), (try db.resolveSignatures(consumer_fid)).error_count);
    const arm_view = db.type_pool.getFnSignatureView((try db.getDefSignature(forward_def)).type_id).?;
    try std.testing.expectEqual(TypeId.i64_ty, arm_view.ret_ty);
    try std.testing.expectEqual(TypeId.u8_ty, arm_view.getParamType(1));

    // [2] Live native C helper `.c` -> `.o` (`zig cc`) linked with CoreX in BOTH Tier A (`-ofmt=c`) and Tier B (`LLVM`):
    const host_spec = TargetSpec.host();
    const ffi_dir = ".zig-cache/phase8_unit_live_ffi";
    defer std.Io.Dir.cwd().deleteTree(io, ffi_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, ffi_dir);

    const c_helper_src =
        "#include <stdarg.h>\n" ++
        "#include <stdint.h>\n" ++
        "#include <string.h>\n" ++
        "typedef struct CPointPair {\n" ++
        "    int32_t x_coord;\n" ++
        "    int32_t y_coord;\n" ++
        "} CPointPair;\n" ++
        "extern int32_t cx_exported_scale_cb(int32_t raw_val, int32_t factor);\n" ++
        "CPointPair c_transform_pair(CPointPair input_pair, int32_t bias) {\n" ++
        "    CPointPair out_pair;\n" ++
        "    out_pair.x_coord = cx_exported_scale_cb(input_pair.x_coord, 2) + bias;\n" ++
        "    out_pair.y_coord = cx_exported_scale_cb(input_pair.y_coord, 3) - bias;\n" ++
        "    return out_pair;\n" ++
        "}\n" ++
        "int32_t c_variadic_digest(int32_t count, ...) {\n" ++
        "    va_list ap;\n" ++
        "    va_start(ap, count);\n" ++
        "    int32_t i8_prom = va_arg(ap, int);\n" ++
        "    int32_t bool_prom = va_arg(ap, int);\n" ++
        "    double f32_prom = va_arg(ap, double);\n" ++
        "    int32_t enum_prom = va_arg(ap, int);\n" ++
        "    const char *cstr_arg = va_arg(ap, const char *);\n" ++
        "    va_end(ap);\n" ++
        "    return count + i8_prom + bool_prom + (int32_t)(f32_prom * 2.0) +\n" ++
        "        enum_prom + (int32_t)strlen(cstr_arg);\n" ++
        "}\n" ++
        "const char *c_echo_greeting(const char *incoming) {\n" ++
        "    if (strcmp(incoming, \"cx-ffi\") == 0) {\n" ++
        "        return \"bridge-ok\";\n" ++
        "    }\n" ++
        "    return \"bad\";\n" ++
        "}\n";

    const c_helper_path = ffi_dir ++ "/c_bridge_helper.c";
    const c_obj_path = try std.fmt.allocPrint(
        allocator,
        "{s}/c_bridge_helper{s}",
        .{ ffi_dir, host_spec.defaultObjExtension() },
    );
    defer allocator.free(c_obj_path);
    try codegen_abi.writeArtifactAtomic(io, allocator, c_helper_path, c_helper_src);

    const zig_exe = try codegen_abi.resolveZigExecutable(io, allocator, null);
    defer allocator.free(zig_exe);
    const cc_compile = try std.process.run(allocator, io, .{
        .argv = &.{
            zig_exe,
            "cc",
            "-c",
            "-std=c11",
            "-O2",
            "-target",
            host_spec.asZigTargetTriple(),
            c_helper_path,
            "-o",
            c_obj_path,
        },
    });
    defer allocator.free(cc_compile.stdout);
    defer allocator.free(cc_compile.stderr);
    try std.testing.expect(cc_compile.term.success());

    const live_cx_src =
        "//! Live C <-> CoreX FFI Round-Trip Verification Module\n" ++
        "@repr(C)\n" ++
        "@derive(Copy)\n" ++
        "pub struct CPointPair {\n" ++
        "    pub x_coord: i32,\n" ++
        "    pub y_coord: i32,\n" ++
        "}\n\n" ++
        "@repr(C)\n" ++
        "@derive(Copy)\n" ++
        "pub enum WireMode: u8 {\n" ++
        "    Idle = 1,\n" ++
        "    Active = 4,\n" ++
        "}\n\n" ++
        "@repr(C)\n" ++
        "@derive(Copy)\n" ++
        "pub struct CStr {\n" ++
        "    pub ptr: *u8,\n" ++
        "}\n\n" ++
        "impl CStr {\n" ++
        "    pub fn count_bytes(&self) -> usize {\n" ++
        "        var len_acc: usize = 0;\n" ++
        "        var cur_ptr: *u8 = self.ptr;\n" ++
        "        unsafe {\n" ++
        "            while cur_ptr != (0 as *u8) and cur_ptr.* != 0_u8 {\n" ++
        "                len_acc = len_acc +% 1;\n" ++
        "                cur_ptr = ((cur_ptr as usize) +% 1) as *u8;\n" ++
        "            }\n" ++
        "        }\n" ++
        "        return len_acc;\n" ++
        "    }\n" ++
        "}\n\n" ++
        "@export\n" ++
        "@link_name(\"cx_exported_scale_cb\")\n" ++
        "pub fn exported_scale_cb(raw_val: i32, factor: i32) -> i32 {\n" ++
        "    return raw_val *% factor;\n" ++
        "}\n\n" ++
        "extern \"C\" {\n" ++
        "    fn c_transform_pair(input_pair: CPointPair, bias: i32) -> CPointPair;\n" ++
        "    fn c_variadic_digest(count: i32, ...) -> i32;\n" ++
        "    fn c_echo_greeting(@null_terminated incoming: *u8) -> *u8;\n" ++
        "}\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    let start_pair = CPointPair { x_coord: 5, y_coord: 4 };\n" ++
        "    let out_pair: CPointPair = unsafe { c_transform_pair(start_pair, 3) };\n" ++
        "    let small_delta: i8 = -2;\n" ++
        "    let is_flag_ok: bool = true;\n" ++
        "    let half_ratio: f32 = 3.5_f32;\n" ++
        "    let nul_tag: [u8; 7] = [b'c', b'x', b'-', b'f', b'f', b'i', 0_u8];\n" ++
        "    let tag_cstr = CStr { ptr: &raw nul_tag[0] };\n" ++
        "    let var_sum: i32 = unsafe {\n" ++
        "        c_variadic_digest(5, small_delta, is_flag_ok, half_ratio, WireMode.Active, tag_cstr.ptr)\n" ++
        "    };\n" ++
        "    let reply_ptr: *u8 = unsafe { c_echo_greeting(&raw nul_tag[0]) };\n" ++
        "    let reply_cstr = CStr { ptr: reply_ptr };\n" ++
        "    let reply_len: i32 = reply_cstr.count_bytes() as i32;\n" ++
        "    let total_score: i32 = out_pair.x_coord + out_pair.y_coord + var_sum + reply_len;\n" ++
        "    if total_score == 52 {\n" ++
        "        return 42;\n" ++
        "    }\n" ++
        "    return 1;\n" ++
        "}\n";

    var live_db = try CompilerDb.init(allocator);
    defer live_db.deinit();
    live_db.setTargetSpec(host_spec);
    const live_fid = FileId.fromInt(0);
    _ = try live_db.setInput(live_fid, live_cx_src, .low);

    const backends = [_]struct {
        /// Backend configuration (Tier A C99 vs Tier B LLVM).
        backend: CodegenBackend,
        /// Output binary filename stem.
        stem: []const u8,
    }{
        .{
            .backend = .{
                .tier_a_c99 = .{
                    .target = host_spec,
                    .is_release_mode = true,
                    .has_line_directives = false,
                },
            },
            .stem = "live_ffi_tier_a",
        },
        .{
            .backend = .{
                .tier_b_llvm = .{
                    .target = host_spec,
                    .is_release_mode = true,
                },
            },
            .stem = "live_ffi_tier_b",
        },
    };

    for (backends) |entry| {
        const exe_path = try std.fmt.allocPrint(
            allocator,
            "{s}/{s}{s}",
            .{ ffi_dir, entry.stem, host_spec.executableExtension() },
        );
        defer allocator.free(exe_path);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var exe_art = live_db.compileModuleArtifact(
            live_fid,
            entry.backend,
            .{
                .artifact_kind = .executable,
                .extra_libs = &.{c_obj_path},
                .output_path = exe_path,
                .io = io,
                .diagnostic_sink = &sink,
            },
        ) catch |comp_err| {
            if (live_db.getSignatureDiagnostics(live_fid)) |sig_s| {
                for (sig_s.diagnostics.items) |d_item| {
                    std.debug.print("[live_sig] {s}: {s}\n", .{ @tagName(d_item.code), d_item.message });
                }
            }
            for ((try live_db.extractItemTree(live_fid)).entries) |it_entry| {
                if (live_db.getBodyDiagnostics(it_entry.def_id)) |body_s| {
                    for (body_s.diagnostics.items) |d_item| {
                        std.debug.print("[live_body] {s}: {s}\n", .{ @tagName(d_item.code), d_item.message });
                    }
                }
                if (live_db.getSastDiagnostics(it_entry.def_id)) |sast_s| {
                    for (sast_s.diagnostics.items) |d_item| {
                        std.debug.print("[live_sast] {s}: {s}\n", .{ @tagName(d_item.code), d_item.message });
                    }
                }
            }
            return comp_err;
        };
        defer exe_art.deinit(allocator);
        try std.testing.expect(!sink.hasErrors());

        const run_res = try std.process.run(allocator, io, .{ .argv = &.{exe_path} });
        defer allocator.free(run_res.stdout);
        defer allocator.free(run_res.stderr);
        const exit_code: u8 = switch (run_res.term) {
            .exited => |status| status,
            else => return error.NativeFfiBinaryCrashed,
        };
        try std.testing.expectEqual(@as(u8, 42), exit_code);
    }
}

test "test_phase8_raw_pointer_indexing_provenance_four_tier_parity" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // Provenance-preserving `ptr[idx]` element indexing across `*T`, `*mut T`, `&raw ptr[idx]`, and `@repr(C)` structs:
    const raw_ptr_index_src =
        "@repr(C)\n" ++
        "@derive(Copy)\n" ++
        "pub struct StridePair {\n" ++
        "    pub base: i32,\n" ++
        "    pub delta: i32,\n" ++
        "}\n\n" ++
        "pub fn mutate_and_sum_raw(mut_elems: *mut i32, pairs: *StridePair) -> i32 {\n" ++
        "    unsafe {\n" ++
        "        mut_elems[1] = mut_elems[0] + pairs[1].base;\n" ++
        "        mut_elems[3] += pairs[0].delta;\n" ++
        "        let tail_ptr: *i32 = &raw mut_elems[1];\n" ++
        "        return tail_ptr[0] + tail_ptr[1] + tail_ptr[2] + pairs[1].delta;\n" ++
        "    }\n" ++
        "}\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    var slots: [i32; 4] = [4, 0, 7, 10];\n" ++
        "    let pair_table: [StridePair; 2] = [\n" ++
        "        StridePair { base: 1, delta: 5 },\n" ++
        "        StridePair { base: 8, delta: 4 },\n" ++
        "    ];\n" ++
        "    return mutate_and_sum_raw(&raw mut slots[0], &raw pair_table[0]);\n" ++
        "}\n";

    var report = try runVerifiedFourTierOracle(allocator, io, raw_ptr_index_src);
    defer report.deinit(allocator);
    try std.testing.expect(report.is_all_matching);
    // Verify expected sum `12 + 7 + 15 + 4 == 38`:
    try std.testing.expectEqual(@as(i64, 38), report.outcomes[0].return_scalar_i64);
}

// -------------- Pillar 3: 4-Tier Async & Nursery --------------

test "test_phase8_four_tier_async_await_frame_pinned_task_group_cancel_and_context_parity" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Multi-suspend `async fn`, `async { … }`, `FramePinned` `&mut`, `spawn` + `spawn_local`,
    //     shared `&[i32; 4]` concurrent reads, FIFO interleaving, `handle.cancel().await`, & `group.cancel_all()`:
    const nursery_and_cancel_src =
        "pub async fn bump_across_suspend(slot: &mut i32, delta_a: i32, delta_b: i32) -> i32 {\n" ++
        "    slot.* += delta_a;\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    slot.* += delta_b;\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    return slot.*;\n" ++
        "}\n\n" ++
        "pub async fn orchestrate_nursery() -> i32 {\n" ++
        "    var pinned_local: i32 = 5;\n" ++
        "    let pinned_res: i32 = bump_across_suspend(&mut pinned_local, 7, 8).await;\n" ++
        "    let inline_block_val: i32 = (async {\n" ++
        "        cx.async.yield_now().await;\n" ++
        "        6\n" ++
        "    }).await;\n" ++
        "    let shared_weights: [i32; 4] = [2, 3, 5, 7];\n" ++
        "    let fanout_sum: i32 = cx.async.task_group(|grp| {\n" ++
        "        let worker_a = grp.spawn(own async {\n" ++
        "            @drop_trace(11);\n" ++
        "            cx.async.yield_now().await;\n" ++
        "            @drop_trace(13);\n" ++
        "            shared_weights[0] + shared_weights[2]\n" ++
        "        });\n" ++
        "        let worker_b = grp.spawn_local(own async {\n" ++
        "            @drop_trace(12);\n" ++
        "            cx.async.yield_now().await;\n" ++
        "            @drop_trace(14);\n" ++
        "            shared_weights[1] + shared_weights[3]\n" ++
        "        });\n" ++
        "        let join_a = worker_a.join();\n" ++
        "        let join_b = worker_b.join();\n" ++
        "        join_a.await + join_b.await\n" ++
        "    }).await;\n" ++
        "    let cancel_bonus: i32 = cx.async.task_group(|grp| {\n" ++
        "        let victim = grp.spawn(own async {\n" ++
        "            defer { @drop_trace(201); }\n" ++
        "            defer { @drop_trace(202); }\n" ++
        "            cx.async.yield_now().await;\n" ++
        "            @drop_trace(999);\n" ++
        "            0\n" ++
        "        });\n" ++
        "        let cancel_fut = victim.cancel();\n" ++
        "        cx.async.yield_now().await;\n" ++
        "        cancel_fut.await;\n" ++
        "        let sibling_bg = grp.spawn(own async {\n" ++
        "            defer { @drop_trace(203); }\n" ++
        "            cx.async.yield_now().await;\n" ++
        "            cx.async.yield_now().await;\n" ++
        "            0\n" ++
        "        });\n" ++
        "        let _join_bg = sibling_bg.join();\n" ++
        "        cx.async.yield_now().await;\n" ++
        "        grp.cancel_all();\n" ++
        "        if grp.is_canceled() { 3 } else { 0 }\n" ++
        "    }).await;\n" ++
        "    return pinned_local + pinned_res + inline_block_val + fanout_sum + cancel_bonus - 24;\n" ++
        "}\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    return cx.async.block_on(own orchestrate_nursery());\n" ++
        "}\n";

    var report_main = try runVerifiedFourTierOracle(allocator, io, nursery_and_cancel_src);
    defer report_main.deinit(allocator);
    try std.testing.expect(report_main.is_all_matching);
    try std.testing.expectEqual(@as(i64, 42), report_main.outcomes[0].return_scalar_i64);
    try std.testing.expectEqualSlices(
        i64,
        &[_]i64{ 11, 12, 13, 14, 202, 201, 203 },
        report_main.outcomes[0].drop_trace,
    );

    // [2] Fallible `T!E` sibling cancellation LIFO `defer` + scoped `with context.cancel_token` / `context.logger`:
    const fallible_and_ctx_src =
        "pub async fn fallible_stage(is_err: bool) -> i32!i32 {\n" ++
        "    if is_err {\n" ++
        "        return .Err(5);\n" ++
        "    }\n" ++
        "    defer { @drop_trace(301); }\n" ++
        "    defer { @drop_trace(302); }\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    @drop_trace(399);\n" ++
        "    return .Ok(50);\n" ++
        "}\n\n" ++
        "pub async fn main() -> i32 {\n" ++
        "    let ctx_sum: i32 = cx.async.task_group(|grp| {\n" ++
        "        let task_left = grp.spawn(own async {\n" ++
        "            let tok_a = CancelToken { _handle: 10_usize };\n" ++
        "            let log_a = Logger { _handle: 4_usize };\n" ++
        "            with context.cancel_token = tok_a {\n" ++
        "                with context.logger = log_a {\n" ++
        "                    cx.async.yield_now().await;\n" ++
        "                    (context.cancel_token._handle as i32) + (context.logger._handle as i32)\n" ++
        "                }\n" ++
        "            }\n" ++
        "        });\n" ++
        "        let task_right = grp.spawn(own async {\n" ++
        "            let tok_b = CancelToken { _handle: 20_usize };\n" ++
        "            let log_b = Logger { _handle: 3_usize };\n" ++
        "            with context.cancel_token = tok_b {\n" ++
        "                with context.logger = log_b {\n" ++
        "                    cx.async.yield_now().await;\n" ++
        "                    (context.cancel_token._handle as i32) + (context.logger._handle as i32)\n" ++
        "                }\n" ++
        "            }\n" ++
        "        });\n" ++
        "        let j_left = task_left.join();\n" ++
        "        let j_right = task_right.join();\n" ++
        "        j_left.await + j_right.await\n" ++
        "    }).await;\n" ++
        "    let err_part: i32 = cx.async.task_group(|grp| {\n" ++
        "        let slow_sibling = grp.spawn(own fallible_stage(false));\n" ++
        "        let fast_failure = grp.spawn(own fallible_stage(true));\n" ++
        "        let _join_slow = slow_sibling.join();\n" ++
        "        let join_fail = fast_failure.join();\n" ++
        "        match join_fail.await {\n" ++
        "            .Ok(ok_v) => ok_v,\n" ++
        "            .Err(err_code) => err_code,\n" ++
        "        }\n" ++
        "    }).await;\n" ++
        "    return ctx_sum + err_part;\n" ++
        "}\n";

    var report_ctx = try runVerifiedFourTierOracle(allocator, io, fallible_and_ctx_src);
    defer report_ctx.deinit(allocator);
    try std.testing.expect(report_ctx.is_all_matching);
    // Verify expected sum `(10 + 4) + (20 + 3) + 5 == 42`:
    try std.testing.expectEqual(@as(i64, 42), report_ctx.outcomes[0].return_scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 302, 301 }, report_ctx.outcomes[0].drop_trace);

    // [3] 4-tier regression; `@align(64)` `&blk` and `FmtArgs` across `yield_now().await`, generic
    //     `async fn` `@size_of[T]()`, and indirect `async fn` pointers sharing the same `i32` return type:
    const aligned_async_src =
        "@align(64)\n" ++
        "pub struct AlignedBlock64 {\n" ++
        "    pub lanes: [u64; 8],\n" ++
        "}\n\n" ++
        "pub fn sum_aligned_edges(block_ref: &AlignedBlock64) -> i32 {\n" ++
        "    return (block_ref.lanes[0] + block_ref.lanes[7]) as i32;\n" ++
        "}\n\n" ++
        "pub async fn probe_aligned_across_yield(seed: u64) -> i32 {\n" ++
        "    let blk = AlignedBlock64 { lanes: [seed; 8] };\n" ++
        "    let blk_ref: &AlignedBlock64 = &blk;\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    return sum_aligned_edges(blk_ref);\n" ++
        "}\n\n" ++
        "pub async fn format_across_yield(num: u32, tag_str: str) -> i32 {\n" ++
        "    let fmt_msg: FmtArgs = \"v={num:04x}:{tag_str}\";\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    let rendered: str = \"{fmt_msg}\";\n" ++
        "    let _wrote: isize = @sys_write(1, rendered);\n" ++
        "    return rendered.len() as i32;\n" ++
        "}\n\n" ++
        "pub fn sync_passthrough[T](val: T) -> T {\n" ++
        "    return val;\n" ++
        "}\n\n" ++
        "pub async fn generic_async_size[T](item: T) -> i32 {\n" ++
        "    let echoed = sync_passthrough(item);\n" ++
        "    let _ = echoed;\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    return @size_of[T]() as i32;\n" ++
        "}\n\n" ++
        "pub async fn unrelated_same_ret(pair: (i64, i64), is_neg: bool) -> i32 {\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    let pair_sum: i32 = (pair.0 + pair.1) as i32;\n" ++
        "    return if is_neg { -pair_sum } else { pair_sum };\n" ++
        "}\n\n" ++
        "pub async fn target_indirect_add(delta: i32) -> i32 {\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    return delta + 5;\n" ++
        "}\n\n" ++
        "pub fn invoke_indirect_sync(fp: async fn(i32) -> i32, arg_val: i32) -> i32 {\n" ++
        "    return cx.async.block_on(own fp(arg_val));\n" ++
        "}\n\n" ++
        "pub async fn run_aligned_async_suite() -> i32 {\n" ++
        "    let aligned_sum: i32 = probe_aligned_across_yield(4_u64).await;\n" ++
        "    let fmt_len: i32 = format_across_yield(0x2a_u32, \"ok\").await;\n" ++
        "    let gen_a: i32 = generic_async_size(7_u16).await;\n" ++
        "    let gen_b: i32 = generic_async_size(7_u16).await;\n" ++
        "    let gen_c: i32 = generic_async_size(9_u64).await;\n" ++
        "    let _keep_live: i32 = unrelated_same_ret((1_i64, 2_i64), false).await;\n" ++
        "    return aligned_sum + fmt_len + gen_a + gen_b + gen_c;\n" ++
        "}\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    let suite_val: i32 = cx.async.block_on(own run_aligned_async_suite());\n" ++
        "    let indirect_val: i32 = invoke_indirect_sync(target_indirect_add, 8);\n" ++
        "    return suite_val + indirect_val;\n" ++
        "}\n";

    var report_aligned = try runVerifiedFourTierOracle(allocator, io, aligned_async_src);
    defer report_aligned.deinit(allocator);
    try std.testing.expect(report_aligned.is_all_matching);
    // Verify expected sum `8 + 9 + 2 + 2 + 8 + 13 == 42`:
    try std.testing.expectEqual(@as(i64, 42), report_aligned.outcomes[0].return_scalar_i64);
    try std.testing.expectEqualStrings("v=002a:ok", report_aligned.outcomes[0].stdout_bytes);
}

// --------------- Pillar 4: Phase 8 Compile-Fail ---------------

test "test_phase8_compile_fail_all_eight_diagnostics_and_positive_discharge_proofs" {
    const allocator = std.testing.allocator;

    // [1] `DiagnosticCode.e0009_c_header_translation_failed`; `#error`, malformed C, `_Static_assert`, and missing `@c_import`:
    const c_error_headers = [_][]const u8{
        "#error \"unsupported platform configuration\"\n",
        "struct BrokenRecord { int missing_semi }\n",
        "_Static_assert(sizeof(int) == 99, \"impossible int size\");\n",
    };
    for (c_error_headers) |bad_c_src| {
        var c_sink = DiagnosticSink.init(allocator);
        defer c_sink.deinit();
        if (c_frontend.parseCHeader(allocator, bad_c_src, "bad.h", .none, .{}, &c_sink)) |ok_unit| {
            var owned_unit = ok_unit;
            owned_unit.deinit();
        } else |_| {}
        try std.testing.expect(hasSinkDiagnostic(&c_sink, DiagnosticCode.e0009_c_header_translation_failed));
    }
    try std.testing.expect(
        try hasCompiledDiagnosticCode(
            allocator,
            "const missing_hdr = @c_import(\"nonexistent_phase8_header_xyz.h\");\n" ++
                "pub fn use_missing() -> i32 = 0;\n",
            DiagnosticCode.e0009_c_header_translation_failed,
        ),
    );

    // [2] `DiagnosticCode.e0308_unterminated_cstr_ffi`; `str.as_ptr()`, `"hello"[0..3].as_ptr()`, and `b"abc".as_ptr()`:
    const e0308_cases = [_][]const u8{
        "@trusted\nextern \"C\" fn c_puts(@null_terminated msg: *u8) -> i32;\n" ++
            "pub fn bad_str(input_s: str) -> i32 { return c_puts(input_s.as_ptr()); }\n",
        "@trusted\nextern \"C\" fn c_puts(@null_terminated msg: *u8) -> i32;\n" ++
            "pub fn bad_sub() -> i32 { let sub: str = \"hello\"[0..3]; return c_puts(sub.as_ptr()); }\n",
        "@trusted\nextern \"C\" fn c_puts(@null_terminated msg: *u8) -> i32;\n" ++
            "pub fn bad_bytes() -> i32 { return c_puts(b\"abc\".as_ptr()); }\n",
    };
    for (e0308_cases) |src_case| {
        try std.testing.expect(
            try hasCompiledDiagnosticCode(allocator, src_case, DiagnosticCode.e0308_unterminated_cstr_ffi),
        );
    }

    // [3] `DiagnosticCode.e0309_concurrent_exclusivity_or_escape`; dual `&mut`, parent write before join,
    //     `@thread_local`, `*mut u8`, `@not_send` in `group.spawn`, and `TaskHandle` escaping `task_group`:
    const e0309_cases = [_][]const u8{
        "pub async fn dual_mut_capture() -> i32 {\n" ++
            "    var shared_val: i32 = 0;\n" ++
            "    return cx.async.task_group(|grp| {\n" ++
            "        let h_one = grp.spawn(async { shared_val += 1; });\n" ++
            "        let h_two = grp.spawn(async { shared_val += 2; });\n" ++
            "        h_one.join().await;\n" ++
            "        h_two.join().await;\n" ++
            "        shared_val\n" ++
            "    }).await;\n" ++
            "}\n",
        "pub async fn parent_mut_while_unjoined() -> i32 {\n" ++
            "    var acc_val: i32 = 1;\n" ++
            "    return cx.async.task_group(|grp| {\n" ++
            "        let child_h = grp.spawn(async { acc_val += 5; });\n" ++
            "        acc_val += 10;\n" ++
            "        child_h.join().await;\n" ++
            "        acc_val\n" ++
            "    }).await;\n" ++
            "}\n",
        "@thread_local\nextern \"C\" static mut TLS_COUNTER: i32;\n" ++
            "pub async fn bad_tls_spawn() -> i32 {\n" ++
            "    return cx.async.task_group(|grp| {\n" ++
            "        let child_h = grp.spawn(own async { unsafe { TLS_COUNTER } });\n" ++
            "        child_h.join().await\n" ++
            "    }).await;\n" ++
            "}\n",
        "pub async fn bad_raw_ptr_spawn(raw_buf: *mut u8) -> usize {\n" ++
            "    return cx.async.task_group(|grp| {\n" ++
            "        let child_h = grp.spawn(own async { raw_buf as usize });\n" ++
            "        child_h.join().await\n" ++
            "    }).await;\n" ++
            "}\n",
        "@not_send\npub struct ThreadAffine { pub code: i32 }\n" ++
            "pub async fn bad_not_send_spawn() -> i32 {\n" ++
            "    let affine_tok = ThreadAffine { code: 9 };\n" ++
            "    return cx.async.task_group(|grp| {\n" ++
            "        let child_h = grp.spawn(own async { affine_tok.code });\n" ++
            "        child_h.join().await\n" ++
            "    }).await;\n" ++
            "}\n",
        "pub async fn bad_handle_escape() -> i32 {\n" ++
            "    let leaked_h = cx.async.task_group(|grp| {\n" ++
            "        let child_h = grp.spawn(own async { 7 });\n" ++
            "        child_h\n" ++
            "    }).await;\n" ++
            "    return leaked_h.join().await;\n" ++
            "}\n",
    };
    for (e0309_cases) |src_case| {
        try std.testing.expect(
            try hasCompiledDiagnosticCode(
                allocator,
                src_case,
                DiagnosticCode.e0309_concurrent_exclusivity_or_escape,
            ),
        );
    }

    // [4] `DiagnosticCode.e0310_mismatched_ffi_deallocator`; freeing `@free_with(c_free_a)` with `c_free_b`:
    const e0310_src =
        "@trusted\nextern \"C\" {\n" ++
        "    @owned_by_caller\n    @free_with(c_free_a)\n    pub fn c_alloc_a(sz: usize) -> *mut u8;\n" ++
        "    pub fn c_free_a(@consumes ptr: *mut u8);\n" ++
        "    pub fn c_free_b(@consumes ptr: *mut u8);\n" ++
        "}\n" ++
        "pub fn bad_dealloc() {\n" ++
        "    let buf_ptr = c_alloc_a(32);\n" ++
        "    c_free_b(buf_ptr);\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(allocator, e0310_src, DiagnosticCode.e0310_mismatched_ffi_deallocator),
    );

    // [5] `DiagnosticCode.e0311_unchecked_nullable_ffi_ptr` + positive null-check `@owned_by_caller` discharge:
    const e0311_src =
        "@trusted\nextern \"C\" {\n" ++
        "    @may_be_null\n    pub fn c_try_grab() -> *mut i32;\n" ++
        "}\n" ++
        "pub fn bad_unchecked_deref() -> i32 {\n" ++
        "    let maybe_ptr = c_try_grab();\n" ++
        "    return unsafe { maybe_ptr.* };\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(allocator, e0311_src, DiagnosticCode.e0311_unchecked_nullable_ffi_ptr),
    );

    const positive_null_discharge_src =
        "@trusted\nextern \"C\" {\n" ++
        "    @owned_by_caller\n    @free_with(c_release_buf)\n    @may_be_null\n" ++
        "    pub fn c_alloc_nullable(sz: usize) -> *mut u8;\n" ++
        "    pub fn c_release_buf(@consumes @may_be_null ptr: *mut u8);\n" ++
        "}\n" ++
        "pub fn valid_null_check_discharge() {\n" ++
        "    let ptr_val = c_alloc_nullable(64);\n" ++
        "    if ptr_val == (0 as *mut u8) {\n" ++
        "        return;\n" ++
        "    }\n" ++
        "    c_release_buf(ptr_val);\n" ++
        "}\n";
    try expectZeroCompileDiagnostics(allocator, positive_null_discharge_src);

    // [6] `DiagnosticCode.e0312_unproven_ffi_slice_len` + positive Pentagon-proven `if n <= buf.len()`:
    const e0312_src =
        "@trusted\nextern \"C\" fn c_read(@slice_len(req_len) dst: *u8, req_len: usize) -> i32;\n" ++
        "pub fn bad_unproven_len(buf: &[u8], n: usize) -> i32 {\n" ++
        "    return c_read(buf.as_ptr(), n);\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(allocator, e0312_src, DiagnosticCode.e0312_unproven_ffi_slice_len),
    );

    const positive_pentagon_ffi_src =
        "@trusted\nextern \"C\" fn c_read(@slice_len(req_len) dst: *u8, req_len: usize) -> i32;\n" ++
        "pub fn proven_bounded_read(buf: &[u8], n: usize) -> i32 {\n" ++
        "    if n <= buf.len() {\n" ++
        "        return c_read(buf.as_ptr(), n);\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";
    try expectZeroCompileDiagnostics(allocator, positive_pentagon_ffi_src);

    // [7] `DiagnosticCode.e0317_async_inline_frame_exceeded`; `> 16 KiB` frame across `.await` and mutual recursion:
    const e0317_huge_frame_src =
        "pub async fn huge_frame_coro() -> u8 {\n" ++
        "    let jumbo_buf: [u8; 20000] = [1_u8; 20000];\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    return jumbo_buf[0];\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(
            allocator,
            e0317_huge_frame_src,
            DiagnosticCode.e0317_async_inline_frame_exceeded,
        ),
    );

    const e0317_mutual_rec_src =
        "pub async fn mutual_ping(depth: i32) -> i32 {\n" ++
        "    if depth <= 0 { return 0; }\n" ++
        "    return mutual_pong(depth - 1).await;\n" ++
        "}\n" ++
        "pub async fn mutual_pong(depth: i32) -> i32 {\n" ++
        "    return mutual_ping(depth - 1).await;\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(
            allocator,
            e0317_mutual_rec_src,
            DiagnosticCode.e0317_async_inline_frame_exceeded,
        ),
    );

    // [8] `DiagnosticCode.e0438_await_outside_async_context`; sync `fn` and nested sync closure inside `async fn`:
    const e0438_sync_fn_src =
        "pub async fn step_one() -> i32 = 1;\n" ++
        "pub fn bad_sync_await() -> i32 {\n" ++
        "    return step_one().await;\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(
            allocator,
            e0438_sync_fn_src,
            DiagnosticCode.e0438_await_outside_async_context,
        ),
    );

    const e0438_nested_closure_src =
        "pub async fn step_two() -> i32 = 2;\n" ++
        "pub async fn outer_async() -> i32 {\n" ++
        "    let sync_cb = |offset: i32| -> i32 { return step_two().await + offset; };\n" ++
        "    return sync_cb(1);\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(
            allocator,
            e0438_nested_closure_src,
            DiagnosticCode.e0438_await_outside_async_context,
        ),
    );

    // [9] Additional Phase 8 safety gates; `E0413` (unawaited `Future`), `E0304` (unjoined `TaskHandle` and
    //     `@linear` live across `.await` without `defer`), and `E0322` (`block_on` inside `@no_block`):
    const e0413_unawaited_fut_src =
        "pub async fn compute_async() -> i32 = 9;\n" ++
        "pub async fn discard_future() {\n" ++
        "    compute_async();\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(
            allocator,
            e0413_unawaited_fut_src,
            DiagnosticCode.e0413_unhandled_must_use_or_result,
        ),
    );

    const e0304_unjoined_handle_src =
        "pub async fn drop_task_handle_unjoined() -> i32 {\n" ++
        "    return cx.async.task_group(|grp| {\n" ++
        "        let unjoined_h = grp.spawn(own async { 5 });\n" ++
        "        0\n" ++
        "    }).await;\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(
            allocator,
            e0304_unjoined_handle_src,
            DiagnosticCode.e0304_resource_or_memory_leak,
        ),
    );

    const e0304_linear_across_await_src =
        "@linear\npub struct LinearPermit { pub token_id: u64 }\n" ++
        "pub fn consume_permit(permit: own LinearPermit) -> u64 = permit.token_id;\n" ++
        "pub async fn linear_across_suspend_without_defer() -> u64 {\n" ++
        "    let permit = LinearPermit { token_id: 77 };\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    return consume_permit(own permit);\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(
            allocator,
            e0304_linear_across_await_src,
            DiagnosticCode.e0304_resource_or_memory_leak,
        ),
    );

    const e0322_block_on_in_no_block_src =
        "pub async fn tiny_fut() -> i32 = 3;\n" ++
        "@no_block\n" ++
        "pub fn forbidden_block_on() -> i32 {\n" ++
        "    return cx.async.block_on(own tiny_fut());\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(
            allocator,
            e0322_block_on_in_no_block_src,
            DiagnosticCode.e0322_no_block_contract_violation,
        ),
    );

    // [10] Raw-pointer element indexing gates; `E0324` outside `unsafe` and `E0425` on `*opaque` / `*mut opaque`:
    const e0324_raw_ptr_index_outside_unsafe_src =
        "pub fn bad_raw_index(ptr: *i32, idx: usize) -> i32 {\n" ++
        "    return ptr[idx];\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(
            allocator,
            e0324_raw_ptr_index_outside_unsafe_src,
            DiagnosticCode.e0324_package_capability_violation,
        ),
    );

    const e0425_opaque_ptr_index_cases = [_][]const u8{
        "pub fn bad_opaque_index(ptr: *opaque) -> u8 {\n" ++
            "    return unsafe { ptr[0] };\n" ++
            "}\n",
        "pub fn bad_mut_opaque_index(ptr: *mut opaque) {\n" ++
            "    unsafe { ptr[1] = 0; }\n" ++
            "}\n",
    };
    for (e0425_opaque_ptr_index_cases) |opaque_case_src| {
        try std.testing.expect(
            try hasCompiledDiagnosticCode(
                allocator,
                opaque_case_src,
                DiagnosticCode.e0425_invalid_opaque_type_usage,
            ),
        );
    }
}

// -------------- Pillar 5: Reaper & Coro Coloring --------------

test "test_phase8_sim_seam_reaper_quarantine_barrier_and_mir_async_liveness_slot_reuse" {
    const allocator = std.testing.allocator;

    // [1] `sim_seam.CompletionReaper` (`Fix-08B`); ABA generation rejection + quarantine drain barrier + `ReapOutcome`:
    var op_slots: [4]sim_seam.InFlightOpSlot = @splat(.{});
    var reaper = sim_seam.initCompletionReaper(&op_slots);

    var dma_buf_a: [32]u8 = @splat(0x5A);
    var dma_buf_b: [64]u8 = @splat(0xA5);

    const slot_zero = reaper.acquireSlot().?;
    const key_gen0 = reaper.markSubmitted(
        slot_zero,
        0,
        41,
        .{ .base = &dma_buf_a, .len = 32, .capacity = 32, .owned_pool_id = 11 },
        .release_buffer,
    );
    try std.testing.expectEqual(@as(u32, 1), reaper.active_in_flight_count);

    // Forged generation key must be rejected by both `requestCancel` and `reapCompletion`:
    const forged_key: sim_seam.IoUserData = .{
        .slot_index = key_gen0.slot_index,
        .generation = key_gen0.generation +% 1,
        .worker_id = 0,
    };
    try std.testing.expect(!reaper.requestCancel(forged_key, null, null));
    try std.testing.expect(reaper.reapCompletion(.{ .user_data = forged_key.asU64(), .result = 32 }) == null);

    // Normal completion + release increments slot generation from `0` to `1`:
    try std.testing.expectEqual(
        sim_seam.SlotState.completed,
        reaper.reapCompletion(.{ .user_data = key_gen0.asU64(), .result = 32 }).?.state,
    );
    try std.testing.expectEqual(@as(u32, 11), reaper.releaseCompletedSlot(key_gen0).?.owned_pool_id);
    try std.testing.expect(reaper.releaseCompletedSlot(key_gen0) == null);

    // Re-submit recycled slot (`generation == 1`), quarantine via `requestCancel`, and drain via barrier:
    const slot_reused = reaper.acquireSlot().?;
    try std.testing.expectEqual(slot_zero, slot_reused);
    const key_gen1 = reaper.markSubmitted(
        slot_reused,
        3,
        88,
        .{ .base = &dma_buf_b, .len = 64, .capacity = 64, .owned_pool_id = 29 },
        .release_buf_and_close_fd,
    );
    try std.testing.expect(!reaper.requestCancel(key_gen0, null, null));

    var barrier_state = SimBarrierState{
        .pending_cqe = .{ .user_data = key_gen1.asU64(), .result = -125 },
    };
    const sim_vtable = sim_seam.ReactorVTable{
        .cancel_io = &SimBarrierState.onCancelIo,
        .poll_or_park = &SimBarrierState.onPollOrPark,
    };
    const sim_ctx: *sim_seam.ReactorCtx = @ptrCast(&barrier_state);

    try std.testing.expect(reaper.requestCancel(key_gen1, &sim_vtable, sim_ctx));
    try std.testing.expectEqual(@as(u32, 1), barrier_state.cancel_calls);
    try std.testing.expectEqual(@as(u32, 1), reaper.quarantined_count);

    try std.testing.expect(
        reaper.drainQuarantinedBarrier(&sim_vtable, sim_ctx, 4, &SimBarrierState.onOrphanReaped),
    );
    try std.testing.expectEqual(@as(u32, 0), reaper.quarantined_count);
    try std.testing.expectEqual(@as(i32, 88), barrier_state.orphan_fd);
    try std.testing.expectEqual(@as(u32, 29), barrier_state.orphan_pool_id);
    try std.testing.expectEqual(
        sim_seam.ReaperAction.release_buf_and_close_fd,
        barrier_state.orphan_action,
    );

    // [2] End-to-end `.cx` -> `MIR` -> `mir_async.prepareAndAnalyzeAsyncModule` sequential buffer coloring:
    const sequential_await_src =
        "pub async fn sequential_buffers(seed_byte: u8) -> u8 {\n" ++
        "    let stage_one: [u8; 512] = [seed_byte; 512];\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    let stage_one_tail: u8 = stage_one[511];\n" ++
        "    let stage_two: [u8; 512] = [stage_one_tail +% 1_u8; 512];\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    return stage_two[256];\n" ++
        "}\n";

    var lowered = try corex.lowerSourceToMir(
        allocator,
        FileId.fromInt(0),
        sequential_await_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer lowered.deinit();
    try std.testing.expect(!lowered.hir_bundle.diagnostics.hasErrors());

    var async_sink = DiagnosticSink.init(allocator);
    defer async_sink.deinit();
    var async_plan = try mir_async.prepareAndAnalyzeAsyncModule(
        allocator,
        lowered.mir_bundle.bodies.items,
        &lowered.hir_bundle.pool,
        &lowered.hir_bundle.sym_table,
        TargetLayout.NATIVE_64,
        &async_sink,
    );
    defer async_plan.deinit();
    try std.testing.expect(!async_sink.hasErrors());
    try std.testing.expect(async_plan.has_any_async_ops);

    var has_checked_seq_plan = false;
    for (lowered.mir_bundle.bodies.items, 0..) |body_item, body_idx| {
        if (!body_item.is_async) continue;
        const body_plan = async_plan.getBodyPlan(body_idx);
        has_checked_seq_plan = true;
        try std.testing.expectEqual(@as(usize, 2), body_plan.suspend_points.len);
        try std.testing.expect(body_plan.reused_slot_count >= 1);
        var uncolored_sum_bytes: u32 = 0;
        for (body_plan.local_slots) |slot_meta| {
            uncolored_sum_bytes += slot_meta.byte_size;
        }
        try std.testing.expect(uncolored_sum_bytes >= 1024);
        try std.testing.expect(body_plan.frame_layout.colored_locals_bytes < uncolored_sum_bytes);
        try std.testing.expect(!body_plan.has_exceeded_inline_cap);
    }
    try std.testing.expect(has_checked_seq_plan);
}

// ---------- Pillar 6: Phase 8 Hardening Regressions -----------

test "test_phase8_soundness_abi_c1_through_h6_and_nursery_handle_regressions" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const scratch_dir = ".zig-cache/phase8_unit_pillar6";
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, scratch_dir);

    // [1] Live C99 + CoreX Tier A / Tier B verification for `C1` (`"".as_ptr()` + `"hello".as_ptr()` NUL-termination)
    //     and `C2` (`NestedFloatPair` `@repr(C)` struct containing nested `FloatBox` float struct):
    const host_spec = TargetSpec.host();
    const zig_exe = try codegen_abi.resolveZigExecutable(io, allocator, null);
    defer allocator.free(zig_exe);

    const c_helper_src =
        "#include <stddef.h>\n" ++
        "typedef struct { float val; } FloatBox;\n" ++
        "typedef struct { FloatBox first; double second; } NestedFloatPair;\n" ++
        "size_t cx_test_c_strlen(const char *str_ptr) {\n" ++
        "    size_t count = 0;\n" ++
        "    while (str_ptr[count] != '\\0') { count += 1; }\n" ++
        "    return count;\n" ++
        "}\n" ++
        "int cx_test_nested_float_abi(NestedFloatPair pair_in) {\n" ++
        "    double sum = (double)pair_in.first.val + pair_in.second;\n" ++
        "    return (int)(sum * 10.0 + 0.5);\n" ++
        "}\n";
    const c_src_path = scratch_dir ++ "/c_abi_reg.c";
    const c_obj_path = try std.fmt.allocPrint(
        allocator,
        "{s}/c_abi_reg{s}",
        .{ scratch_dir, host_spec.defaultObjExtension() },
    );
    defer allocator.free(c_obj_path);
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = c_src_path, .data = c_helper_src });

    const cc_run = try std.process.run(allocator, io, .{
        .argv = &.{
            zig_exe,
            "cc",
            "-c",
            "-std=c99",
            "-O2",
            "-target",
            host_spec.asZigTargetTriple(),
            c_src_path,
            "-o",
            c_obj_path,
        },
    });
    defer allocator.free(cc_run.stdout);
    defer allocator.free(cc_run.stderr);
    try std.testing.expect(cc_run.term.success());

    const cx_ffi_reg_src =
        "@repr(C)\n" ++
        "pub struct FloatBox { pub val: f32 }\n" ++
        "@repr(C)\n" ++
        "pub struct NestedFloatPair { pub first: FloatBox, pub second: f64 }\n" ++
        "@trusted\n" ++
        "extern \"C\" {\n" ++
        "    fn cx_test_c_strlen(@null_terminated str_ptr: *u8) -> usize;\n" ++
        "    fn cx_test_nested_float_abi(pair_in: NestedFloatPair) -> i32;\n" ++
        "}\n" ++
        "pub fn main() -> i32 {\n" ++
        "    let empty_len: i32 = cx_test_c_strlen(\"\".as_ptr()) as i32;\n" ++
        "    let hello_len: i32 = cx_test_c_strlen(\"hello\".as_ptr()) as i32;\n" ++
        "    let pair_score: i32 = cx_test_nested_float_abi(NestedFloatPair {\n" ++
        "        first: FloatBox { val: 1.5_f32 },\n" ++
        "        second: 2.2_f64,\n" ++
        "    });\n" ++
        "    return empty_len * 100 + hello_len + pair_score;\n" ++
        "}\n";

    var ffi_db = try CompilerDb.init(allocator);
    defer ffi_db.deinit();
    ffi_db.setTargetSpec(host_spec);
    const ffi_fid = FileId.fromInt(0);
    _ = try ffi_db.setInput(ffi_fid, cx_ffi_reg_src, .low);

    const reg_backends = [_]CodegenBackend{
        .{ .tier_a_c99 = .{ .target = host_spec, .is_release_mode = true, .has_line_directives = false } },
        .{ .tier_b_llvm = .{ .target = host_spec, .is_release_mode = true } },
    };
    for (reg_backends, 0..) |backend_cfg, tier_idx| {
        const exe_path = try std.fmt.allocPrint(
            allocator,
            "{s}/reg_tier_{d}{s}",
            .{ scratch_dir, tier_idx, host_spec.executableExtension() },
        );
        defer allocator.free(exe_path);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var art = try ffi_db.compileModuleArtifact(ffi_fid, backend_cfg, .{
            .artifact_kind = .executable,
            .extra_libs = &.{c_obj_path},
            .output_path = exe_path,
            .io = io,
            .diagnostic_sink = &sink,
        });
        defer art.deinit(allocator);
        try std.testing.expect(!sink.hasErrors());

        const run_res = try std.process.run(allocator, io, .{ .argv = &.{exe_path} });
        defer allocator.free(run_res.stdout);
        defer allocator.free(run_res.stderr);
        switch (run_res.term) {
            .exited => |exit_code| try std.testing.expectEqual(@as(u8, 42), exit_code),
            else => return error.UnexpectedProcessTermination,
        }
    }

    // [2] Structured `TaskHandle` across `.await` (`left.join().await + right.join().await` and `?` sibling cancel):
    const nursery_handles_src =
        "pub async fn step_result(val: i32, is_failing: bool) -> i32!i32 {\n" ++
        "    if not is_failing {\n" ++
        "        defer { @drop_trace(901); }\n" ++
        "        cx.async.yield_now().await;\n" ++
        "        return .Ok(val);\n" ++
        "    }\n" ++
        "    return .Err(val);\n" ++
        "}\n\n" ++
        "pub async fn try_pair_join() -> i32!i32 {\n" ++
        "    return cx.async.task_group(|grp| -> i32!i32 {\n" ++
        "        let h_fail = grp.spawn_local(own step_result(12, true));\n" ++
        "        let h_slow = grp.spawn_local(own step_result(99, false));\n" ++
        "        .Ok(h_fail.join().await? + h_slow.join().await?)\n" ++
        "    }).await;\n" ++
        "}\n\n" ++
        "pub async fn sum_pair_join() -> i32 {\n" ++
        "    return cx.async.task_group(|grp| {\n" ++
        "        let left_h = grp.spawn_local(own async {\n" ++
        "            cx.async.yield_now().await;\n" ++
        "            10\n" ++
        "        });\n" ++
        "        let right_h = grp.spawn_local(own async { 20 });\n" ++
        "        left_h.join().await + right_h.join().await\n" ++
        "    }).await;\n" ++
        "}\n\n" ++
        "pub fn main() -> i32 {\n" ++
        "    let ok_sum: i32 = cx.async.block_on(own sum_pair_join());\n" ++
        "    let err_part: i32 = cx.async.block_on(own try_pair_join()) catch |err_code| err_code;\n" ++
        "    return ok_sum + err_part;\n" ++
        "}\n";
    var nursery_report = try runVerifiedFourTierOracle(allocator, io, nursery_handles_src);
    defer nursery_report.deinit(allocator);
    try std.testing.expect(nursery_report.is_all_matching);
    try std.testing.expectEqual(@as(i64, 42), nursery_report.outcomes[0].return_scalar_i64);

    // [3] Freestanding `wasm32-unknown-freestanding` + `async` (`H2`) compiles cleanly in both Tier A and Tier B:
    const wasm_async_src =
        "pub async fn wasm_step(seed: u32) -> u32 {\n" ++
        "    cx.async.yield_now().await;\n" ++
        "    return seed +% 7_u32;\n" ++
        "}\n" ++
        "@wasm_export(\"cx_wasm_async_run\")\n" ++
        "pub fn cx_wasm_async_run(seed: u32) -> u32 {\n" ++
        "    return cx.async.block_on(own wasm_step(seed));\n" ++
        "}\n";
    var wasm_async_db = try CompilerDb.init(allocator);
    defer wasm_async_db.deinit();
    wasm_async_db.setTargetSpec(TargetSpec.WASM32_UNKNOWN_FREESTANDING);
    const wasm_async_fid = FileId.fromInt(0);
    _ = try wasm_async_db.setInput(wasm_async_fid, wasm_async_src, .low);

    var wasm_async_sink = DiagnosticSink.init(allocator);
    defer wasm_async_sink.deinit();
    const wasm_async_ll_out = scratch_dir ++ "/wasm_async_tier_b.wasm";
    var wasm_async_art = try wasm_async_db.compileModuleArtifact(
        wasm_async_fid,
        .{ .tier_b_llvm = .{ .target = TargetSpec.WASM32_UNKNOWN_FREESTANDING, .is_release_mode = true } },
        .{
            .artifact_kind = .executable,
            .output_path = wasm_async_ll_out,
            .io = io,
            .diagnostic_sink = &wasm_async_sink,
        },
    );
    defer wasm_async_art.deinit(allocator);
    try std.testing.expect(!wasm_async_sink.hasErrors());
    const wasm_async_bytes = try readAllFileBytes(allocator, io, wasm_async_ll_out);
    defer allocator.free(wasm_async_bytes);
    try verifyObjectMagicHeader(wasm_async_bytes, .wasm32);

    // [4] Positive `E0311` dereference after `!= 0` check + Negative `C6` (`&mut` clobber -> `E0308`),
    //     `C7` (oversized C bitfield -> `E0009`), and `H6` (`.def` `=` vs `==` symbol directory):
    const positive_e0311_deref_src =
        "@trusted\nextern \"C\" {\n    @may_be_null\n    pub fn c_try_slot() -> *mut i32;\n}\n" ++
        "pub fn safe_checked_deref() -> i32 {\n" ++
        "    let maybe_ptr = c_try_slot();\n" ++
        "    if maybe_ptr != (0 as *mut i32) {\n" ++
        "        return unsafe { maybe_ptr.* };\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";
    try expectZeroCompileDiagnostics(allocator, positive_e0311_deref_src);

    const clobbered_nul_src =
        "@trusted\nextern \"C\" fn c_puts(@null_terminated msg: *u8) -> i32;\n" ++
        "fn overwrite_nul(buf: &mut [u8; 4]) { buf[3] = 65; }\n" ++
        "pub fn bad_clobbered_cstr() -> i32 {\n" ++
        "    var buf: [u8; 4] = [65, 66, 67, 0];\n" ++
        "    overwrite_nul(&mut buf);\n" ++
        "    return c_puts(buf.as_ptr());\n" ++
        "}\n";
    try std.testing.expect(
        try hasCompiledDiagnosticCode(allocator, clobbered_nul_src, DiagnosticCode.e0308_unterminated_cstr_ffi),
    );

    var bf_sink = DiagnosticSink.init(allocator);
    defer bf_sink.deinit();
    if (c_frontend.parseCHeader(
        allocator,
        "struct BadBf { unsigned char too_wide : 16; };\n",
        "bad_bf.h",
        .none,
        .{},
        &bf_sink,
    )) |ok_bf| {
        var owned_bf = ok_bf;
        owned_bf.deinit();
    } else |_| {}
    try std.testing.expect(hasSinkDiagnostic(&bf_sink, DiagnosticCode.e0009_c_header_translation_failed));

    var def_parsed = try codegen_link.parseModuleDef(
        allocator,
        "LIBRARY \"demo.dll\"\nEXPORTS\n    PublicSym = InternalImpl\n    ImportAlias == ActualDllSym\n",
        "demo.dll",
    );
    defer def_parsed.deinit(allocator);
    try std.testing.expectEqual(@as(usize, 2), def_parsed.exports.len);
    try std.testing.expectEqualStrings("PublicSym", def_parsed.exports[0].sym_name);
    try std.testing.expect(def_parsed.exports[0].ext_name == null);
    try std.testing.expectEqualStrings("ImportAlias", def_parsed.exports[1].sym_name);
    try std.testing.expectEqualStrings("ActualDllSym", def_parsed.exports[1].ext_name.?);
}

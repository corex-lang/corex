//! Unit & Native-Execution Tests for Tier A (`stage0/src/codegen_c.zig`)
//!
//! Verifies all Phase 7 Wave 3B Tier A (`-ofmt=c`) invariants (`DR-01`, `phase7_spec.md` §3–§4):
//! - Byte-for-byte deterministic ISO C99 emission (`Run 1 == Run 2`) across all 7 targets with
//!   zero `void*` untyped escape hatches, topological `TypeId` struct/union ordering, physical
//!   field layout (`_f<decl_ord>`), explicit `_pad_<k>` padding arrays, `@packed`, and
//!   `@cache_aligned` (`aligned(64)` vs `aligned(128)` on `aarch64-macos`).
//! - Exact sum-type representations (`transparent_ok`, `niche_single` at `niche.byte_offset`,
//!   `explicit_tag`), non-null dangling pointers on empty slices/strings (`[CRITICAL-04]`),
//!   `#soa [S; C]` & `#soa [S]` SIMD-aligned column offsets (`[CRITICAL-03]`), cycle-safe `_phi_<k>`
//!   parallel block-argument moves (`[CRITICAL-05]`), `MirConst.raw_blob` chunked arrays (`D-03`),
//!   and `--dev` GOT indirection (`_cx_dev_got` + `.cx_dev_meta`).
//! - Cross-target `.o` object compilation via `zig cc` (`x86_64-linux`, `aarch64-macos`,
//!   `wasm32-wasi`) and native host executable execution + `COREX_ORACLE_TRACE_FILE` parity.

const std = @import("std");
const corex = @import("corex");

const codegen_abi = corex.codegen_abi;
const codegen_dev_seam = corex.codegen_dev_seam;
const mir_sast = corex.mir_sast;
const mir_vm = corex.mir_vm;
const vfs_sourcemap = corex.vfs_sourcemap;

const FileId = corex.FileId;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;
const CodegenBackend = corex.CodegenBackend;
const CodegenArtifact = corex.CodegenArtifact;
const OutputArtifactKind = corex.OutputArtifactKind;

// -------------------------------------- INTERNALS --------------------------------------

/// Prints all diagnostics in `sink` to `stderr` when a test unexpectedly fails.
fn dumpDiagnosticsOnFailure(label: []const u8, sink: *const DiagnosticSink) void {
    for (sink.diagnostics.items) |diag_item| {
        std.debug.print("[{s}] {s}: {s}\n", .{ label, @tagName(diag_item.code), diag_item.message });
    }
}

/// Lowers `source_text` through `mir_sast`, optional `@embed_bytes`, and Tier A (`-ofmt=c`).
fn emitCModuleFromSource(
    allocator: std.mem.Allocator,
    source_text: []const u8,
    target_spec: TargetSpec,
    is_release: bool,
    is_fuzz: bool,
    is_dev_got: bool,
    artifact_kind: OutputArtifactKind,
    output_path: ?[]const u8,
    virtual_files: ?*const std.StringHashMapUnmanaged([]const u8),
) !CodegenArtifact {
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    var sast_bundle = try mir_sast.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(0),
        source_text,
        target_spec.asTargetLayout(),
        .{ .diagnostic_sink = &sink },
    );
    defer sast_bundle.deinit();
    if (sink.hasErrors()) dumpDiagnosticsOnFailure("tier_a_sink", &sink);
    if (sast_bundle.diagnostics.hasErrors()) {
        dumpDiagnosticsOnFailure("tier_a_sast", &sast_bundle.diagnostics);
    }
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(!sast_bundle.diagnostics.hasErrors());

    var blob_store = corex.MirBlobStore.init(allocator);
    defer blob_store.deinit();
    if (virtual_files) |vfiles| {
        const ok_mat = try corex.materializeModuleEmbedBytes(
            sast_bundle.mir_module.bodies.items,
            &sast_bundle.interner,
            &sast_bundle.token_buffer,
            &blob_store,
            .{ .virtual_files = vfiles },
            &sink,
        );
        if (sink.hasErrors()) dumpDiagnosticsOnFailure("tier_a_blob", &sink);
        try std.testing.expect(ok_mat);
        try std.testing.expect(!sink.hasErrors());
    }

    var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &sast_bundle.interner);
    defer vfs.deinit(std.testing.io);
    const vfs_fid = try vfs.setOverlay("src/tier_a_case.cx", source_text, .root);
    try std.testing.expectEqual(@as(u32, 0), vfs_fid.asInt());

    var tok_map: std.AutoHashMapUnmanaged(u32, *const corex.TokenBuffer) = .empty;
    defer tok_map.deinit(allocator);
    try tok_map.put(allocator, 0, &sast_bundle.token_buffer);

    const backend = CodegenBackend{
        .tier_a_c99 = .{
            .target = target_spec,
            .is_release_mode = is_release,
            .is_fuzz_instrumented = is_fuzz,
            .has_line_directives = true,
        },
    };
    return backend.emitModule(allocator, .{
        .bodies = sast_bundle.mir_module.bodies.items,
        .pool = &sast_bundle.pool,
        .sym_table = &sast_bundle.sym_table,
        .interner = &sast_bundle.interner,
        .module_name = "tier_a_test",
        .vfs_source_map = &vfs,
        .file_tokens = &tok_map,
        .blob_store = if (virtual_files != null) &blob_store else null,
        .summary_store = &sast_bundle.sast_result.summary_store,
        .is_dev_got_enabled = is_dev_got,
        .is_oracle_trace_enabled = true,
        .artifact_kind = artifact_kind,
        .output_path = output_path,
        .io = std.testing.io,
        .diagnostic_sink = &sink,
    }) catch |err| {
        dumpDiagnosticsOnFailure("tier_a_driver", &sink);
        return err;
    };
}

/// Evaluates `main` inside `MirVm` oracle mode and returns `(ret_slot, stdout_bytes)`.
fn runSourceInMirVmOracle(
    allocator: std.mem.Allocator,
    source_text: []const u8,
    target_spec: TargetSpec,
    stdout_out: *std.ArrayListUnmanaged(u8),
) !i64 {
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    var sast_bundle = try mir_sast.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(0),
        source_text,
        target_spec.asTargetLayout(),
        .{ .diagnostic_sink = &sink },
    );
    defer sast_bundle.deinit();
    if (sink.hasErrors()) dumpDiagnosticsOnFailure("tier_a_vm_sink", &sink);
    if (sast_bundle.diagnostics.hasErrors()) {
        dumpDiagnosticsOnFailure("tier_a_vm_sast", &sast_bundle.diagnostics);
    }
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(!sast_bundle.diagnostics.hasErrors());

    var rodata_pool = mir_vm.RodataPool.init(allocator);
    defer rodata_pool.deinit();

    var vm_engine = try mir_vm.MirVm.init(
        allocator,
        &sast_bundle.interner,
        &sast_bundle.pool,
        &sast_bundle.sym_table,
        &rodata_pool,
        null,
        &sink,
        .{
            .target_layout = target_spec.asTargetLayout(),
            .stdout_capture = stdout_out,
            .is_oracle_runtime_mode = true,
        },
    );
    defer vm_engine.deinit();

    var main_body: ?*const corex.MirBody = null;
    for (sast_bundle.mir_module.bodies.items) |*body_ptr| {
        const sym_idx = sast_bundle.sym_table.def_to_symbol.get(body_ptr.def_id.asInt()) orelse .none;
        _ = try vm_engine.registerBody(body_ptr, sym_idx);
        if (std.mem.eql(u8, sast_bundle.interner.get(body_ptr.name), "main")) {
            main_body = body_ptr;
        }
    }
    const eval_res = try vm_engine.evalBody(main_body.?, &.{});
    return eval_res.slot.scalar_i64;
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_codegen_c_determinism_layouts_dev_got_and_7_targets" {
    const showcase_src =
        \\@zero_pad
        \\pub struct PaddedHeader {
        \\    pub tag: u8,
        \\    pub count: u64,
        \\    pub flags: u16,
        \\}
        \\@packed
        \\pub struct WirePacket {
        \\    pub magic: u8,
        \\    pub seq: u32,
        \\}
        \\@cache_aligned
        \\pub struct HotCounter {
        \\    pub hits: u64,
        \\}
        \\pub struct Particle {
        \\    pub pos_x: f32,
        \\    pub mass: u8,
        \\}
        \\pub bit_field RegCtrl : u16 {
        \\    pub enable: bool | 1,
        \\    pub mode: u8 | 3,
        \\    pub rest: u16 | 12,
        \\}
        \\pub fn compute_blob_and_soa(particles: #soa [Particle; 4]) -> i32 {
        \\    let raw_magic = @embed_bytes("assets/header.bin");
        \\    let hdr = PaddedHeader { tag: raw_magic[0], count: 99, flags: 7 };
        \\    let pkt = WirePacket { magic: 3, seq: 100 };
        \\    let cnt = HotCounter { hits: 5 };
        \\    var ctrl = RegCtrl { enable: true, mode: 5, rest: 0 };
        \\    ctrl.mode = 6;
        \\    return (hdr.tag as i32) + (pkt.seq as i32) + (cnt.hits as i32) +
        \\        (particles[0].mass as i32) + (ctrl.mode as i32);
        \\}
    ;

    var vfs_blobs: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_blobs.deinit(std.testing.allocator);
    try vfs_blobs.put(std.testing.allocator, "assets/header.bin", &[_]u8{ 11, 22, 33, 44 });

    for (codegen_abi.ALL_CANONICAL_TARGETS) |spec| {
        var run_1 = try emitCModuleFromSource(
            std.testing.allocator,
            showcase_src,
            spec,
            false,
            false,
            true,
            .source_text,
            null,
            &vfs_blobs,
        );
        defer run_1.deinit(std.testing.allocator);

        var run_2 = try emitCModuleFromSource(
            std.testing.allocator,
            showcase_src,
            spec,
            false,
            false,
            true,
            .source_text,
            null,
            &vfs_blobs,
        );
        defer run_2.deinit(std.testing.allocator);

        // Byte-for-byte determinism (`DR-01`) + strict zero-`void*` rule (`AGENTS.md` §1):
        try std.testing.expectEqualStrings(run_1.emitted_text, run_2.emitted_text);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "void *") == null);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "void*") == null);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "_pad_") != null);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "__attribute__((packed))") != null);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "_cx_blob_") != null);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "_cx_dev_got") != null);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "_cx_reload_ctrl") != null);

        if (spec.arch == .aarch64 and spec.os == .macos) {
            try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "aligned(128)") != null);
        } else {
            try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "aligned(64)") != null);
        }

        // Verify `.cx_dev_meta` binary seam round-trips cleanly (`DR-19`):
        try std.testing.expect(run_1.dev_seam_bytes != null);
        const decoded_seam = try codegen_dev_seam.deserializeDevSeamMeta(run_1.dev_seam_bytes.?);
        try std.testing.expectEqual(@as(u32, 1), decoded_seam.header.got_slot_count);
        try std.testing.expectEqual(spec.archOsTag(), decoded_seam.header.arch_os_tag);
    }
}

test "test_codegen_c_cross_target_object_compilation_linux_macos_wasm" {
    const cross_src =
        \\pub fn fib_swap(steps: i32) -> i32 {
        \\    var prev: i32 = 0;
        \\    var curr: i32 = 1;
        \\    var idx: i32 = 0;
        \\    while idx < steps {
        \\        let next_v = prev +% curr;
        \\        prev = curr;
        \\        curr = next_v;
        \\        idx = idx + 1;
        \\    }
        \\    return prev;
        \\}
    ;

    const cross_targets = [_]TargetSpec{
        TargetSpec.X86_64_LINUX,
        TargetSpec.AARCH64_MACOS,
        TargetSpec.WASM32_WASI,
    };

    for (cross_targets) |spec| {
        const obj_path = try std.fmt.allocPrint(
            std.testing.allocator,
            ".zig-cache/test_tier_a_{s}{s}",
            .{ spec.canonicalName(), spec.objectExtension() },
        );
        defer std.testing.allocator.free(obj_path);
        defer std.Io.Dir.cwd().deleteFile(std.testing.io, obj_path) catch {};

        var artifact = try emitCModuleFromSource(
            std.testing.allocator,
            cross_src,
            spec,
            true,
            false,
            false,
            .object_file,
            obj_path,
            null,
        );
        defer artifact.deinit(std.testing.allocator);

        try std.testing.expect(artifact.written_output_path != null);
        const obj_bytes = try std.Io.Dir.cwd().readFileAlloc(
            std.testing.io,
            obj_path,
            std.testing.allocator,
            .limited(4 * 1024 * 1024),
        );
        defer std.testing.allocator.free(obj_bytes);
        try std.testing.expect(obj_bytes.len > 64);
    }
}

test "test_codegen_c_native_executable_execution_and_oracle_trace_parity" {
    const host_spec = TargetSpec.host();
    const exec_src =
        \\@zero_pad
        \\@repr(C)
        \\pub struct ZeroPadProbe {
        \\    pub head: u8,
        \\    pub tail: u64,
        \\}
        \\pub struct Vec2Col {
        \\    pub px: i32,
        \\    pub py: i32,
        \\}
        \\pub struct DropProbe {
        \\    pub tag: i64,
        \\}
        \\impl DropProbe {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag);
        \\    }
        \\}
        \\pub fn try_step(code: i32) -> Result[i32, i32] {
        \\    if code == 0 {
        \\        return .Err(0);
        \\    }
        \\    return .Ok(code * 3);
        \\}
        \\pub fn propagate_sum(flag: i32) -> Result[i32, i32] {
        \\    let v1 = try_step(flag)?;
        \\    return .Ok(v1 + 4);
        \\}
        \\pub fn cyclic_fib(limit: i32) -> i32 {
        \\    var left_v: i32 = 1;
        \\    var right_v: i32 = 2;
        \\    var step_i: i32 = 0;
        \\    while step_i < limit {
        \\        let sum_v = left_v +% right_v;
        \\        left_v = right_v;
        \\        right_v = sum_v;
        \\        step_i = step_i + 1;
        \\    }
        \\    return left_v;
        \\}
        \\pub fn bump_inout(mut slot: inout i32, delta: i32) {
        \\    slot = slot + delta;
        \\}
        \\pub fn main() -> i32 {
        \\    // [1] `@zero_pad` padding bytes must be strictly `0x00`:
        \\    let zp = ZeroPadProbe { head: 7, tail: 99 };
        \\    let zp_bytes: &[u8] = zp.as_bytes();
        \\    var pad_or: u8 = 0;
        \\    var bi: usize = 1;
        \\    while bi < 8 {
        \\        pad_or = pad_or | zp_bytes[bi];
        \\        bi = bi + 1;
        \\    }
        \\    if pad_or != 0 {
        \\        @trap();
        \\    }
        \\    // [2] Empty-slice non-null niche (`Option[str]::Some("") != .None`):
        \\    let opt_e: str? = .Some("");
        \\    let opt_n: str? = .None;
        \\    if opt_e == opt_n {
        \\        @trap();
        \\    }
        \\    match opt_e {
        \\        .Some(empty_s) => {
        \\            if empty_s.len != 0 { @trap(); }
        \\        },
        \\        .None => @trap(),
        \\    }
        \\    // [3] `Result[i32, i32]` `Err(0)` vs `Ok` `?` propagation:
        \\    let err_zero = propagate_sum(0);
        \\    let ok_ten = propagate_sum(5);
        \\    var res_acc: i32 = 0;
        \\    match err_zero {
        \\        .Ok(_) => @trap(),
        \\        .Err(ec) => { res_acc = res_acc + ec + 2; },
        \\    }
        \\    match ok_ten {
        \\        .Ok(ov) => { res_acc = res_acc + ov; },
        \\        .Err(_) => @trap(),
        \\    }
        \\    // [4] `#soa` array column writes & reads + `inout` mutation:
        \\    var pts: #soa [Vec2Col; 4] = @default_init[#soa [Vec2Col; 4]]();
        \\    pts[0].px = 1;
        \\    pts[0].py = 10;
        \\    pts[1].px = 2;
        \\    pts[1].py = 20;
        \\    pts[2].px = 9;
        \\    pts[2].py = 30;
        \\    pts[3].px = 4;
        \\    pts[3].py = 40;
        \\    bump_inout(res_acc, pts[2].px + pts[1].py);
        \\    // [5] Atomics, SIMD, 128-bit integer ops, `DropProbe` `@drop_trace`, and `@sys_write`:
        \\    var atom_v: i32 = 4;
        \\    let prev_atom = @atomic_rmw_add(&mut atom_v, 6);
        \\    let simd_v = @simd_mul(@simd_splat[[i32; 4]](2), [1, 2, 3, 4]);
        \\    let simd_sum = @simd_reduce_add(simd_v);
        \\    let big_a: i128 = 1000000000000;
        \\    let big_q: i32 = ((big_a * 3) / 1000000000000) as i32;
        \\    {
        \\        let guard = DropProbe { tag: 42 };
        \\        let _ = guard.tag;
        \\    }
        \\    let wrote_n = @sys_write(1, "C99_OK");
        \\    let fib_v = cyclic_fib(5);
        \\    return res_acc + prev_atom + atom_v + simd_sum + big_q + fib_v + (wrote_n as i32) - 80;
        \\}
    ;

    var vm_stdout: std.ArrayListUnmanaged(u8) = .empty;
    defer vm_stdout.deinit(std.testing.allocator);
    const vm_ret = try runSourceInMirVmOracle(
        std.testing.allocator,
        exec_src,
        host_spec,
        &vm_stdout,
    );

    const exe_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/test_tier_a_host_run{s}",
        .{host_spec.executableExtension()},
    );
    defer std.testing.allocator.free(exe_path);
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, exe_path) catch {};

    const trace_path = ".zig-cache/test_tier_a_oracle.trace";
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, trace_path) catch {};

    var artifact = try emitCModuleFromSource(
        std.testing.allocator,
        exec_src,
        host_spec,
        false,
        false,
        true,
        .executable,
        exe_path,
        null,
    );
    defer artifact.deinit(std.testing.allocator);

    var child_env = std.process.Environ.Map.init(std.testing.allocator);
    defer child_env.deinit();
    try child_env.put("COREX_ORACLE_TRACE_FILE", trace_path);

    const run_res = try std.process.run(std.testing.allocator, std.testing.io, .{
        .argv = &.{exe_path},
        .environ_map = &child_env,
    });
    defer std.testing.allocator.free(run_res.stdout);
    defer std.testing.allocator.free(run_res.stderr);

    const host_exit_code: i64 = switch (run_res.term) {
        .exited => |code| @intCast(code),
        else => -1,
    };
    try std.testing.expectEqual(vm_ret, host_exit_code);
    try std.testing.expectEqualStrings(vm_stdout.items, run_res.stdout);

    const trace_bytes = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        trace_path,
        std.testing.allocator,
        .limited(4096),
    );
    defer std.testing.allocator.free(trace_bytes);
    try std.testing.expect(std.mem.indexOf(u8, trace_bytes, "DROP:42\n") != null);
    const expected_ret_line = try std.fmt.allocPrint(std.testing.allocator, "RET:{d}\n", .{vm_ret});
    defer std.testing.allocator.free(expected_ret_line);
    try std.testing.expect(std.mem.indexOf(u8, trace_bytes, expected_ret_line) != null);

    // Also verify runtime arithmetic overflow trap records `TRAP:1\n` and exits cleanly with `101`:
    const trap_src =
        \\pub fn add_checked(lhs_v: i32, rhs_v: i32) -> i32 {
        \\    return lhs_v + rhs_v;
        \\}
        \\pub fn main() -> i32 {
        \\    return add_checked(2000000000, 1000000000);
        \\}
    ;
    const trap_exe = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/test_tier_a_trap_run{s}",
        .{host_spec.executableExtension()},
    );
    defer std.testing.allocator.free(trap_exe);
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, trap_exe) catch {};

    const trap_trace = ".zig-cache/test_tier_a_trap.trace";
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, trap_trace) catch {};

    var trap_art = try emitCModuleFromSource(
        std.testing.allocator,
        trap_src,
        host_spec,
        true,
        false,
        false,
        .executable,
        trap_exe,
        null,
    );
    defer trap_art.deinit(std.testing.allocator);

    var trap_env = std.process.Environ.Map.init(std.testing.allocator);
    defer trap_env.deinit();
    try trap_env.put("COREX_ORACLE_TRACE_FILE", trap_trace);

    const trap_run = try std.process.run(std.testing.allocator, std.testing.io, .{
        .argv = &.{trap_exe},
        .environ_map = &trap_env,
    });
    defer std.testing.allocator.free(trap_run.stdout);
    defer std.testing.allocator.free(trap_run.stderr);

    const trap_code: u8 = switch (trap_run.term) {
        .exited => |code| code,
        else => 0,
    };
    try std.testing.expectEqual(@as(u8, 101), trap_code);
    const trap_log = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        trap_trace,
        std.testing.allocator,
        .limited(1024),
    );
    defer std.testing.allocator.free(trap_log);
    try std.testing.expectEqualStrings("TRAP:1\n", trap_log);
}

test "test_regression_codegen_c_extern_write_exit_dedup_and_trigraph_escape" {
    const ext_src =
        \\@derive(Debug)
        \\pub struct DbgTag {
        \\    pub val: i32,
        \\}
        \\@extern("C")
        \\@link_name("write")
        \\pub fn posix_write_a(fd: i32, buf: *u8, count: usize) -> isize;
        \\@extern("C")
        \\@link_name("write")
        \\pub fn posix_write_b(fd: i32, buf: *u8, count: usize) -> isize;
        \\@extern("C")
        \\@link_name("_exit")
        \\pub fn posix_exit_now(status: i32) -> never;
        \\pub fn probe_entry(val: i32) -> i32 {
        \\    if val == -999 {
        \\        unsafe { posix_exit_now(1); }
        \\    }
        \\    let wr_a: isize = unsafe { posix_write_a(1, 0 as *u8, 0) };
        \\    let wr_b: isize = unsafe { posix_write_b(1, 0 as *u8, 0) };
        \\    let dbg_s: str = (DbgTag { val: val }).debug();
        \\    return val + (wr_a as i32) + (wr_b as i32) + (dbg_s.len as i32);
        \\}
    ;

    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var sast_bundle = try mir_sast.lowerAndVerifySourceMirSast(
        std.testing.allocator,
        FileId.fromInt(0),
        ext_src,
        TargetSpec.X86_64_LINUX.asTargetLayout(),
        .{ .diagnostic_sink = &sink },
    );
    defer sast_bundle.deinit();
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(!sast_bundle.diagnostics.hasErrors());

    var vfs = vfs_sourcemap.VfsSourceMap.init(std.testing.allocator, &sast_bundle.interner);
    defer vfs.deinit(std.testing.io);
    _ = try vfs.setOverlay("src/trigraph??/probe.cx", ext_src, .root);

    var tok_map: std.AutoHashMapUnmanaged(u32, *const corex.TokenBuffer) = .empty;
    defer tok_map.deinit(std.testing.allocator);
    try tok_map.put(std.testing.allocator, 0, &sast_bundle.token_buffer);

    const backend = CodegenBackend{
        .tier_a_c99 = .{
            .target = TargetSpec.X86_64_LINUX,
            .is_release_mode = true,
            .has_line_directives = true,
        },
    };
    const obj_path = ".zig-cache/test_tier_a_ext_dedup.o";
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, obj_path) catch {};

    var src_art = try backend.emitModule(std.testing.allocator, .{
        .bodies = sast_bundle.mir_module.bodies.items,
        .pool = &sast_bundle.pool,
        .sym_table = &sast_bundle.sym_table,
        .interner = &sast_bundle.interner,
        .module_name = "tier_a_ext_dedup",
        .vfs_source_map = &vfs,
        .file_tokens = &tok_map,
        .artifact_kind = .source_text,
        .io = std.testing.io,
        .diagnostic_sink = &sink,
    });
    defer src_art.deinit(std.testing.allocator);

    try std.testing.expect(std.mem.indexOf(u8, src_art.emitted_text, "src/trigraph?\\?/probe.cx") != null);
    try std.testing.expect(std.mem.indexOf(u8, src_art.emitted_text, "static const uint8_t _cx_str_bytes_") != null);
    try std.testing.expect(std.mem.indexOf(u8, src_art.emitted_text, "void *") == null);
    try std.testing.expect(std.mem.indexOf(u8, src_art.emitted_text, "void*") == null);

    var obj_art = try backend.emitModule(std.testing.allocator, .{
        .bodies = sast_bundle.mir_module.bodies.items,
        .pool = &sast_bundle.pool,
        .sym_table = &sast_bundle.sym_table,
        .interner = &sast_bundle.interner,
        .module_name = "tier_a_ext_dedup",
        .vfs_source_map = &vfs,
        .file_tokens = &tok_map,
        .artifact_kind = .object_file,
        .output_path = obj_path,
        .io = std.testing.io,
        .diagnostic_sink = &sink,
    });
    defer obj_art.deinit(std.testing.allocator);
    try std.testing.expect(!sink.hasErrors());
}

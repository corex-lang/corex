//! Phase 11.1 (`STD-01` Mandatory Step 1) Compiler Seam & Intrinsics Verification Suite
//!
//! Verifies all Phase 11.1 Mandatory Step 1 compiler prerequisites before `stdlib/cx/*.cx`:
//! - Retirement of `Eq` / `Ord` aliases (`E0403` suggesting `Equatable` / `Comparable`),
//!   `@std_cap_boundary` compile-time key/tag validation (`E0327`), and raw-pointer `+`/`-` (`E0401`).
//! - Niche layouts (`OwnPtr[T]? == 8B/4B`, `String? == 24B` & `String?? == 32B` on 64-bit & `wasm32`,
//!   `SlotKey[T]? == 8B`) and pointer-sized `SwifterrorKind` on 64-bit vs `wasm32`.
//! - `mir_sast` `E0328` on `with_scratch`/`restore` escape, 4-condition `ElaborateDrops` `0`-drop
//!   arena elision vs `swap` non-elision, and Pentagon `dst < lhs` on `udiv_checked` / `lshr_checked`.
//! - `CompilerDb.registerCxStdlibPreludeRoot` auto-imported `cx` prelude isolation and 4-tier
//!   (`MirVm`, `--dev` C99, `--release` C99 `-O2`, `LLVM`) differential parity across `#soa Vec[S]`,
//!   `@derive(Comparable, Default)`, `@implements[T, TrivialDrop]()`, inline `Type is low..=high`,
//!   `for` `.next()`/`.as_slice()`, inherent `impl str`, streaming `@fmt_write`, `@ctx_next_rng_seed`,
//!   `@tls_scratch_ptr`, `@tls_alloc_state`, `@inline(never)`, scalar/ptr/slice methods, and SIMD intrinsics.

const std = @import("std");
const corex = @import("corex");

const FileId = corex.FileId;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const DiagnosticCode = corex.DiagnosticCode;
const TargetSpec = corex.TargetSpec;
const TypeLayoutResolver = corex.TypeLayoutResolver;
const AbiClassifier = corex.AbiClassifier;

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `sink` contains at least one diagnostic matching `code`.
fn sinkHasCode(sink: *const DiagnosticSink, code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == code) return true;
    }
    return false;
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
        const lbl = if (diag_item.labels.len > 0) diag_item.labels[0].label else "";
        std.debug.print(
            "[{s}] fid={d} {d}..{d} {s}: {s} ({s})\n",
            .{
                label,
                diag_item.primary_span.file_id.asInt(),
                diag_item.primary_span.start_byte,
                diag_item.primary_span.end_byte,
                @tagName(diag_item.code),
                diag_item.message,
                lbl,
            },
        );
    }
}

// ---------------------------------------- TESTS ----------------------------------------

test "test_step1_eq_ord_retired_e0403_std_cap_boundary_e0327_and_raw_ptr_arith_e0401" {
    const allocator = std.testing.allocator;

    // [1] Retired `Eq` and `Ord` emit `E0403` with `Equatable` / `Comparable` suggestions:
    {
        const retired_src =
            "pub fn bad_eq[T: Eq](lhs: T, rhs: T) -> bool { return lhs == rhs; }\n" ++
            "pub fn bad_ord[T: Ord](lhs: T, rhs: T) -> bool { return lhs < rhs; }\n";
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        const fid = FileId.fromInt(0);
        _ = try db.setInput(fid, retired_src, .low);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, fid, &sink);
        try std.testing.expect(sinkHasCode(&sink, .e0403_unresolved_symbol));
        var saw_equatable_hint = false;
        var saw_comparable_hint = false;
        for (sink.diagnostics.items) |diag_item| {
            if (std.mem.indexOf(u8, diag_item.message, "Equatable") != null) saw_equatable_hint = true;
            if (std.mem.indexOf(u8, diag_item.message, "Comparable") != null) saw_comparable_hint = true;
        }
        try std.testing.expect(saw_equatable_hint);
        try std.testing.expect(saw_comparable_hint);
    }

    // [2] Invalid `@std_cap_boundary` key or capability identifier emits `E0327`:
    {
        const bad_cap_src =
            "@std_cap_boundary(unknown_key: [unsafe_op])\n" ++
            "pub fn bad_boundary_a() {}\n" ++
            "@std_cap_boundary(clears: [not_a_real_capability])\n" ++
            "pub fn bad_boundary_b() {}\n";
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        try db.setInternalCore(true);
        const fid = FileId.fromInt(0);
        try db.setFilePackageId(fid, .std_core);
        _ = try db.setInput(fid, bad_cap_src, .high);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, fid, &sink);
        try std.testing.expect(sinkHasCode(&sink, .e0327_forbidden_sandbox_bypass_attribute));
        try std.testing.expect(sink.diagnostics.items.len >= 2);
    }

    // [3] Raw pointer `+` / `-` emits `E0401` directing callers to `.add(n)` / `.sub(n)`:
    {
        const ptr_arith_src =
            "pub fn bad_ptr_plus(ptr: *u8) -> *u8 {\n" ++
            "    return unsafe { ptr + 1 };\n" ++
            "}\n";
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        const fid = FileId.fromInt(0);
        _ = try db.setInput(fid, ptr_arith_src, .low);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, fid, &sink);
        try std.testing.expect(sinkHasCode(&sink, .e0401_type_mismatch));
    }
}

test "test_step1_niche_layouts_ownptr_string_slotkey_and_swifterror_64_vs_wasm32" {
    const allocator = std.testing.allocator;

    const layout_src =
        "@linear\n" ++
        "pub struct OwnPtr[T] {\n" ++
        "    @non_null\n" ++
        "    ptr: *mut T,\n" ++
        "}\n" ++
        "pub struct String {\n" ++
        "    bytes_a: u64,\n" ++
        "    bytes_b: u64,\n" ++
        "    bytes_c: u64,\n" ++
        "}\n" ++
        "@derive(Copy, Equatable)\n" ++
        "pub struct SlotKey[V] {\n" ++
        "    pub index: u32,\n" ++
        "    pub generation: u32 is 1..=u32.MAX,\n" ++
        "}\n" ++
        "pub type NonZeroU64 = u64 is 1..=u64.MAX;\n" ++
        "pub type NonZeroUsize = usize is 1..=usize.MAX;\n" ++
        "pub fn probe_own_opt() -> OwnPtr[u64]? { return .None; }\n" ++
        "pub fn probe_str_opt() -> String? { return .None; }\n" ++
        "pub fn probe_str_opt_opt() -> String?? { return .None; }\n" ++
        "pub fn probe_slot_opt() -> SlotKey[u64]? { return .None; }\n" ++
        "pub fn fallible_u64(val: u32) -> u32!NonZeroU64 { return .Ok(val); }\n" ++
        "pub fn fallible_usize(val: u32) -> u32!NonZeroUsize { return .Ok(val); }\n";

    const targets = [_]struct {
        spec: TargetSpec,
        expected_own_opt_bytes: u64,
        expect_u64_nonnull_swifterror: bool,
    }{
        .{
            .spec = TargetSpec.X86_64_LINUX,
            .expected_own_opt_bytes = 8,
            .expect_u64_nonnull_swifterror = true,
        },
        .{
            .spec = TargetSpec.WASM32_WASI,
            .expected_own_opt_bytes = 4,
            .expect_u64_nonnull_swifterror = false,
        },
    };

    for (targets) |t_case| {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(t_case.spec);
        try db.setInternalCore(true);
        const fid = FileId.fromInt(0);
        try db.setFilePackageId(fid, .std_core);
        _ = try db.setInput(fid, layout_src, .high);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try collectAllDiagnostics(&db, fid, &sink);
        if (sink.hasErrors()) dumpUnexpectedDiagnostics("niche_layouts", &sink);
        try std.testing.expect(!sink.hasErrors());

        var resolver = TypeLayoutResolver.init(allocator, &db.type_pool, &db.symbol_table, t_case.spec);
        defer resolver.deinit();

        const opt_mod = try db.optimizeMirModule(fid, false);
        const own_ty = opt_mod.findBodyByName(&db.interner, "probe_own_opt").?.ret_ty;
        const str_opt_ty = opt_mod.findBodyByName(&db.interner, "probe_str_opt").?.ret_ty;
        const str_opt2_ty = opt_mod.findBodyByName(&db.interner, "probe_str_opt_opt").?.ret_ty;
        const slot_opt_ty = opt_mod.findBodyByName(&db.interner, "probe_slot_opt").?.ret_ty;

        try std.testing.expectEqual(t_case.expected_own_opt_bytes, (try resolver.resolveType(own_ty)).size_bytes);
        try std.testing.expectEqual(@as(u64, 24), (try resolver.resolveType(str_opt_ty)).size_bytes);
        try std.testing.expectEqual(@as(u64, 32), (try resolver.resolveType(str_opt2_ty)).size_bytes);
        try std.testing.expectEqual(@as(u64, 8), (try resolver.resolveType(slot_opt_ty)).size_bytes);

        const u64_body = opt_mod.findBodyByName(&db.interner, "fallible_u64").?;
        var u64_abi = try AbiClassifier.classifyFn(allocator, &resolver, .{
            .params = &.{},
            .ret_ty = u64_body.ret_ty,
        });
        defer u64_abi.deinit(allocator);
        if (t_case.expect_u64_nonnull_swifterror) {
            try std.testing.expectEqual(corex.codegen_abi.SwifterrorKind.nonnull_ptr, u64_abi.swifterror_kind);
        } else {
            try std.testing.expect(u64_abi.swifterror_kind != .nonnull_ptr);
        }

        const usz_body = opt_mod.findBodyByName(&db.interner, "fallible_usize").?;
        var usz_abi = try AbiClassifier.classifyFn(allocator, &resolver, .{
            .params = &.{},
            .ret_ty = usz_body.ret_ty,
        });
        defer usz_abi.deinit(allocator);
        if (!t_case.spec.isWasm()) {
            try std.testing.expectEqual(corex.codegen_abi.SwifterrorKind.nonnull_ptr, usz_abi.swifterror_kind);
        }
    }
}

test "test_step1_sast_e0328_restore_escape_and_4_condition_arena_drop_elision" {
    const allocator = std.testing.allocator;

    // [1] Passing `Context.scratch[0]` slice into a callee that calls `.restore(cp)` emits `E0328`:
    {
        const restore_escape_src =
            "@derive(Copy)\n" ++
            "pub struct ArenaCheckpoint { pub pos: usize }\n" ++
            "pub struct ScratchArena {\n" ++
            "    pub backing: [u8; 8],\n" ++
            "    pub pos: usize,\n" ++
            "}\n" ++
            "impl ScratchArena {\n" ++
            "    pub fn save(&self) -> ArenaCheckpoint { return ArenaCheckpoint { pos: self.pos }; }\n" ++
            "    pub fn restore(&mut self, cp: ArenaCheckpoint) { self.pos = cp.pos; }\n" ++
            "    pub fn alloc_slice(&mut self) -> &[u8] { return &self.backing; }\n" ++
            "}\n" ++
            "pub struct Context {\n" ++
            "    pub allocator: usize,\n" ++
            "    pub scratch: [ScratchArena; 2],\n" ++
            "}\n" ++
            "pub fn restore_and_read(ctx: &mut Context, borrowed: &[u8]) -> usize {\n" ++
            "    let cp = ctx.scratch[0].save();\n" ++
            "    ctx.scratch[0].restore(cp);\n" ++
            "    return borrowed.len();\n" ++
            "}\n" ++
            "pub fn caller_scratch_conflict(ctx: &mut Context) -> usize {\n" ++
            "    let view = ctx.scratch[0].alloc_slice();\n" ++
            "    return restore_and_read(ctx, view);\n" ++
            "}\n";
        var sast_bundle = try corex.lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(0),
            restore_escape_src,
            corex.TargetLayout.NATIVE_64,
            .{},
        );
        defer sast_bundle.deinit();
        try std.testing.expect(sinkHasCode(&sast_bundle.diagnostics, .e0328_scratch_arena_ping_pong_conflict));
    }

    // [2] 4-condition `ElaborateDrops`: unswapped `Vec[u64].in_arena(&mut arena)` emits 0 drops,
    //     while `swap(&mut arena_vec, &mut heap_vec)` preserves drop elaboration:
    {
        const arena_drop_src =
            "@linear\n" ++
            "pub struct Arena { pub pos: usize }\n" ++
            "impl Arena {\n" ++
            "    pub fn destroy(own self) {\n" ++
            "        let Arena { pos } = self;\n" ++
            "        if pos == 0 { return; }\n" ++
            "    }\n" ++
            "}\n" ++
            "pub trait Drop { fn drop(&mut self); }\n" ++
            "pub struct Vec[T] {\n" ++
            "    pub ptr: usize,\n" ++
            "    pub len: usize,\n" ++
            "}\n" ++
            "impl[T] Drop for Vec[T] {\n" ++
            "    pub fn drop(&mut self) { @drop_trace(77); }\n" ++
            "}\n" ++
            "impl[T] Vec[T] {\n" ++
            "    pub fn new() -> Vec[T] { return Vec[T] { ptr: 1, len: 0 }; }\n" ++
            "    pub fn in_arena(arena: &mut Arena) -> Vec[T] {\n" ++
            "        arena.pos = arena.pos +% 1;\n" ++
            "        return Vec[T] { ptr: 2, len: 0 };\n" ++
            "    }\n" ++
            "}\n" ++
            "pub fn swap_vecs(lhs: &mut Vec[u64], rhs: &mut Vec[u64]) {\n" ++
            "    let tmp_p = lhs.ptr;\n" ++
            "    lhs.ptr = rhs.ptr;\n" ++
            "    rhs.ptr = tmp_p;\n" ++
            "}\n" ++
            "pub fn clean_arena_only() -> usize {\n" ++
            "    var arena = Arena { pos: 0 };\n" ++
            "    let items = Vec[u64].in_arena(&mut arena);\n" ++
            "    let out = items.len;\n" ++
            "    (own arena).destroy();\n" ++
            "    return out;\n" ++
            "}\n" ++
            "pub fn swapped_arena_and_heap() -> usize {\n" ++
            "    var arena = Arena { pos: 0 };\n" ++
            "    var arena_items = Vec[u64].in_arena(&mut arena);\n" ++
            "    var heap_items = Vec[u64].new();\n" ++
            "    swap_vecs(&mut arena_items, &mut heap_items);\n" ++
            "    (own arena).destroy();\n" ++
            "    return arena_items.ptr;\n" ++
            "}\n";
        var sast_bundle = try corex.lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(0),
            arena_drop_src,
            corex.TargetLayout.NATIVE_64,
            .{},
        );
        defer sast_bundle.deinit();
        if (sast_bundle.diagnostics.diagnostics.items.len > 0) {
            dumpUnexpectedDiagnostics("arena_drop", &sast_bundle.diagnostics);
        }
        try std.testing.expectEqual(@as(usize, 0), sast_bundle.diagnostics.diagnostics.items.len);

        const clean_body = sast_bundle.mir_module.findBodyByName(&sast_bundle.interner, "clean_arena_only").?;
        const clean_mir = try corex.renderMir(allocator, clean_body, &sast_bundle.interner);
        defer allocator.free(clean_mir);
        try std.testing.expect(std.mem.indexOf(u8, clean_mir, "drop_in_place") == null);
        try std.testing.expect(std.mem.indexOf(u8, clean_mir, "drop_if_live") == null);

        const swapped_body = sast_bundle.mir_module.findBodyByName(&sast_bundle.interner, "swapped_arena_and_heap").?;
        const swapped_mir = try corex.renderMir(allocator, swapped_body, &sast_bundle.interner);
        defer allocator.free(swapped_mir);
        try std.testing.expect(std.mem.indexOf(u8, swapped_mir, "drop_in_place") != null);
    }
}

test "test_step1_cx_prelude_auto_mount_and_4_tier_differential_parity" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const cx_prelude_src =
        "/# Synthetic `cx` Prelude Root for Step 1 Seam Verification\n" ++
        "@derive(Copy, Equatable, Comparable, Default, Clone, Debug)\n" ++
        "pub struct PairKey {\n" ++
        "    pub major: u32 = 1,\n" ++
        "    pub minor: u32 = 2,\n" ++
        "}\n" ++
        "@derive(Copy, Equatable)\n" ++
        "pub enum FmtError {\n" ++
        "    BufferFull,\n" ++
        "}\n" ++
        "@derive(Copy)\n" ++
        "pub struct FmtWriter {\n" ++
        "    pub ctx: *mut opaque,\n" ++
        "    pub write_fn: fn(*mut opaque, &[u8]) -> unit!FmtError,\n" ++
        "}\n" ++
        "impl FmtWriter {\n" ++
        "    pub fn write_str(&mut self, text: str) -> unit!FmtError {\n" ++
        "        return (self.write_fn)(self.ctx, text.as_bytes());\n" ++
        "    }\n" ++
        "}\n" ++
        "impl FmtSpec {\n" ++
        "    pub fn has_alt(&self) -> bool {\n" ++
        "        return (self.flags_and_fill & (1_u32 << 25)) != 0;\n" ++
        "    }\n" ++
        "}\n" ++
        "impl str {\n" ++
        "    pub fn byte_at_or_zero(&self, idx: usize) -> u8 {\n" ++
        "        let raw = self.as_bytes();\n" ++
        "        if idx < raw.len() { return raw[idx]; }\n" ++
        "        return 0;\n" ++
        "    }\n" ++
        "}\n";

    const app_src =
        "/# Step 1 End-to-End 4-Tier Differential Verification App\n" ++
        "@soa\n" ++
        "@derive(Copy, Equatable)\n" ++
        "pub struct Particle {\n" ++
        "    pub x: i32,\n" ++
        "    pub y: i32,\n" ++
        "}\n" ++
        "pub struct RangeIter {\n" ++
        "    pub cur: i32,\n" ++
        "    pub stop: i32,\n" ++
        "}\n" ++
        "impl RangeIter {\n" ++
        "    pub fn next(&mut self) -> i32? {\n" ++
        "        if self.cur >= self.stop { return .None; }\n" ++
        "        let out = self.cur;\n" ++
        "        self.cur = self.cur + 1;\n" ++
        "        return .Some(out);\n" ++
        "    }\n" ++
        "}\n" ++
        "pub struct TagVal {\n" ++
        "    pub code: u32,\n" ++
        "}\n" ++
        "impl TagVal {\n" ++
        "    pub fn fmt(&self, out: &mut FmtWriter, spec: FmtSpec) -> unit!FmtError {\n" ++
        "        if spec.has_alt() { out.write_str(\"#\")?; }\n" ++
        "        out.write_str(\"T=\")?;\n" ++
        "        return @fmt_write(out, f\"{self.code}\");\n" ++
        "    }\n" ++
        "}\n" ++
        "pub struct FixedSink {\n" ++
        "    pub buf: [u8; 16],\n" ++
        "    pub len: usize,\n" ++
        "}\n" ++
        "pub fn sink_write_cb(ctx: *mut opaque, chunk: &[u8]) -> unit!FmtError {\n" ++
        "    if ctx.is_null() { return .Ok(()); }\n" ++
        "    let sink_ptr: *mut FixedSink = ctx as *mut FixedSink;\n" ++
        "    if sink_ptr.is_null() { return .Ok(()); }\n" ++
        "    let sink: &mut FixedSink = unsafe { &mut sink_ptr.* };\n" ++
        "    if chunk.len() > 16 - sink.len { return .Err(.BufferFull); }\n" ++
        "    var idx: usize = 0;\n" ++
        "    while idx < chunk.len() {\n" ++
        "        sink.buf[sink.len + idx] = chunk[idx];\n" ++
        "        idx += 1;\n" ++
        "    }\n" ++
        "    sink.len = sink.len + chunk.len();\n" ++
        "    return .Ok(());\n" ++
        "}\n" ++
        "@inline(never)\n" ++
        "pub fn unwrap_nonzero[T: Unsigned](val: T is 1..=T.MAX) -> T {\n" ++
        "    return val;\n" ++
        "}\n" ++
        "pub fn add_explicit_group(lhs: Integer, rhs: Integer) -> i32 {\n" ++
        "    return (lhs as i32) + (rhs as i32);\n" ++
        "}\n" ++
        "pub fn add_any_group(lhs: any Integer, rhs: any Integer) -> i32 {\n" ++
        "    return (lhs as i32) + (rhs as i32);\n" ++
        "}\n" ++
        "pub fn main() -> i32 {\n" ++
        "    // [1] Prelude auto-import (`PairKey`), `@derive(Comparable, Default)`, `<` / `>`:\n" ++
        "    let def_k = PairKey.default();\n" ++
        "    let hi_k = PairKey { major: 1, minor: 9 };\n" ++
        "    let cmp_score: i32 = if def_k < hi_k and hi_k > def_k => 10 else 0;\n" ++
        "\n" ++
        "    // [2] `@implements[T, TrivialDrop]()`, inline refinement, explicit `[TypeArgs]`:\n" ++
        "    let td_ok: i32 = if comptime @implements[u64, TrivialDrop]() => 5 else 0;\n" ++
        "    let nz_v: u32 is 1..=u32.MAX = 7;\n" ++
        "    let nz_u: i32 = unwrap_nonzero[u32](nz_v) as i32;\n" ++
        "    let grp_sum: i32 = add_explicit_group[u16](10_u16, 2_u16) + add_any_group[u16, u8](2_u16, 1_u8);\n" ++
        "\n" ++
        "    // [3] `#soa Vec[Particle]` push, element read, column slices, pop:\n" ++
        "    var pvec: #soa Vec[Particle] = #soa Vec[Particle].new();\n" ++
        "    pvec.push(Particle { x: 4, y: 10 });\n" ++
        "    pvec.push(Particle { x: 6, y: 20 });\n" ++
        "    pvec.x_mut()[0] = 8;\n" ++
        "    var x_sum: i32 = 0;\n" ++
        "    for px in pvec.x {\n" ++
        "        x_sum = x_sum + px;\n" ++
        "    }\n" ++
        "    let popped_y: i32 = match pvec.pop() {\n" ++
        "        .Some(pt) => pt.y,\n" ++
        "        .None => 0,\n" ++
        "    };\n" ++
        "\n" ++
        "    // [4] `for` over custom `.next()` iterator + inherent `impl str`:\n" ++
        "    var iter_sum: i32 = 0;\n" ++
        "    for step in (RangeIter { cur: 1, stop: 4 }) {\n" ++
        "        iter_sum = iter_sum + step;\n" ++
        "    }\n" ++
        "    let ch_b: i32 = \"AB\".byte_at_or_zero(1) as i32;\n" ++
        "\n" ++
        "    // [5] Scalar, slice, raw-ptr, SIMD, TLS, `@ctx_next_rng_seed`, streaming `@fmt_write`:\n" ++
        "    let bit_score: i32 = ((8_u32.trailing_zeros() + 7_u32.count_ones()) as i32) +\n" ++
        "        ((@from_le_bytes[u32](@to_le_bytes(5_u32))) as i32) +\n" ++
        "        (9.0_f64.sqrt() as i32);\n" ++
        "    var arr4: [i32; 4] = [1, 2, 3, 4];\n" ++
        "    let sl_mut: &mut [i32] = &mut arr4;\n" ++
        "    sl_mut.reverse();\n" ++
        "    let (left_half, right_half) = sl_mut.split_at(2);\n" ++
        "    let raw_second: i32 = unsafe { left_half.as_ptr().add(1).read() } + right_half[0];\n" ++
        "    let v_a: [u8; 16] = @simd_splat[[u8; 16]](0x81_u8);\n" ++
        "    let v_b: [u8; 16] = @simd_splat[[u8; 16]](0x81_u8);\n" ++
        "    let eq_mask: u16 = @simd_bitmask(@simd_eq(v_a, v_b));\n" ++
        "    let simd_ok: i32 = if eq_mask == 0xFFFF_u16 => 4 else 0;\n" ++
        "    let s1: u64 = @ctx_next_rng_seed();\n" ++
        "    let s2: u64 = @ctx_next_rng_seed();\n" ++
        "    let tls_ok: i32 = if not @tls_scratch_ptr().is_null() and " ++
        "not @tls_alloc_state().is_null() and s1 != s2 => 3 else 0;\n" ++
        "\n" ++
        "    var sink = FixedSink { buf: [0; 16], len: 0 };\n" ++
        "    var writer = FmtWriter { ctx: (&raw mut sink) as *mut opaque, write_fn: sink_write_cb };\n" ++
        "    let tag = TagVal { code: 42 };\n" ++
        "    let manual_spec = FmtSpec {\n" ++
        "        flags_and_fill: 1_u32 << 25,\n" ++
        "        width_or_none: 0xFFFF_u16,\n" ++
        "        precision_or_none: 0xFFFF_u16,\n" ++
        "    };\n" ++
        "    let ok_res = @fmt_write(&mut writer, f\"{tag:#}!\");\n" ++
        "    let ovf_res = @fmt_write(&mut writer, \"0123456789ABCDEF\");\n" ++
        "    let fmt_ok: i32 = if manual_spec.has_alt() and ok_res is .Ok(()) and\n" ++
        "        ovf_res is .Err(.BufferFull) and sink.len == 6 {\n" ++
        "        9\n" ++
        "    } else {\n" ++
        "        0\n" ++
        "    };\n" ++
        "\n" ++
        "    return cmp_score + td_ok + nz_u + grp_sum + x_sum + popped_y + iter_sum +\n" ++
        "        ch_b + bit_score + raw_second + simd_ok + tls_ok + fmt_ok;\n" ++
        "}\n";

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(TargetSpec.host());

    const cx_fid = FileId.fromInt(1);
    try db.setFilePackageId(cx_fid, .std_core);
    _ = try db.setInput(cx_fid, cx_prelude_src, .high);
    try db.registerCxStdlibPreludeRoot(cx_fid);

    const app_fid = FileId.fromInt(0);
    _ = try db.setInput(app_fid, app_src, .low);

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectAllDiagnostics(&db, cx_fid, &sink);
    try collectAllDiagnostics(&db, app_fid, &sink);
    if (sink.diagnostics.items.len > 0) dumpUnexpectedDiagnostics("step1_4tier_app", &sink);
    try std.testing.expectEqual(@as(usize, 0), sink.diagnostics.items.len);

    var report = try corex.runFourTierDiffOracleOnDb(allocator, &db, app_fid, .{ .io = io });
    defer report.deinit(allocator);
    if (!report.is_all_matching) {
        std.debug.print("{s}\n", .{report.rendered_diff_table});
    }
    try std.testing.expect(report.is_all_matching);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // 10 + 5 + 7 + 15 + 14 + 20 + 6 + 66 + (6 + 5 + 3) + (3 + 2) + 4 + 3 + 9 = 178:
    try std.testing.expectEqual(@as(i64, 178), report.outcomes[0].return_scalar_i64);
}

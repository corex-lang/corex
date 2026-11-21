//! Unit Tests for Mid-Level SSA + Place IR (`mir.zig`)
//!
//! Covers exact cache-line byte layouts, Braun et al. single-pass forward `MirSsaBuilder`,
//! Maranget + Jacobs `switch_int` decision trees, LIFO `defer`/`errdefer` cleanup pads,
//! zero-overhead `subscript … yield` CFG splicing, `MirVerifier` (`V1`–`V6` positive and
//! negative synthetic mutations), and deterministic `renderMir` output.

const std = @import("std");
const corex = @import("corex");

const mir = corex.mir;
const mir_vm = corex.mir_vm;
const type_system = corex.type_system;
const symbol_resolver = corex.symbol_resolver;

const MirBody = mir.MirBody;
const MirInst = mir.MirInst;
const MirOp = mir.MirOp;
const InstFlags = mir.InstFlags;
const LocalDecl = mir.LocalDecl;
const MirPlace = mir.MirPlace;
const MirProjection = mir.MirProjection;
const MirTerminator = mir.MirTerminator;
const MirBasicBlock = mir.MirBasicBlock;
const MirOutgoingEdge = mir.MirOutgoingEdge;
const MirSsaBuilder = mir.MirSsaBuilder;
const PlaceId = mir.PlaceId;
const LocalId = mir.LocalId;
const MirBlockId = corex.MirBlockId;
const MirValueId = corex.MirValueId;
const TokenIndex = corex.TokenIndex;
const DefId = corex.DefId;
const FileId = corex.FileId;
const StringInterner = corex.StringInterner;
const TypeId = corex.TypeId;
const TargetLayout = type_system.TargetLayout;
const InternPool = type_system.InternPool;
const SymbolTable = symbol_resolver.SymbolTable;

// -------------------------------------- INTERNALS --------------------------------------

/// Appends a `LocalDecl` to `body.locals` and returns its `LocalId`.
fn pushLocal(body: *MirBody, decl: LocalDecl) !LocalId {
    const idx: u32 = @intCast(body.locals.items.len);
    try body.locals.append(body.allocator, decl);
    return LocalId.fromInt(idx);
}

/// Appends a `MirPlace` (with optional `projs`) to `body.places` and returns its `PlaceId`.
fn pushPlace(body: *MirBody, base_local: LocalId, projs: []const MirProjection) !PlaceId {
    const proj_start: u24 = @intCast(body.projections.items.len);
    if (projs.len > 0) {
        try body.projections.appendSlice(body.allocator, projs);
    }
    const idx: u32 = @intCast(body.places.items.len);
    try body.places.append(body.allocator, .{
        .base = base_local.asInt(),
        .proj_start = proj_start,
        .proj_len = @intCast(projs.len),
    });
    return PlaceId.fromInt(idx);
}

/// Emits an integer `MirOp.const_scalar` inside `ssa` at `bb_id`.
fn emitIntConst(
    body: *MirBody,
    ssa: *MirSsaBuilder,
    bb_id: MirBlockId,
    ty: TypeId,
    int_val: i128,
) !MirValueId {
    const c_idx = try body.appendConst(.{ .int_val = int_val });
    return ssa.emitInst(bb_id, .{
        .op = .const_scalar,
        .type_id = ty,
        .operands = .{ .lhs = c_idx, .rhs = 0 },
    }, TokenIndex.fromInt(0));
}

/// Emits a boolean `MirOp.const_scalar` inside `ssa` at `bb_id`.
fn emitBoolConst(
    body: *MirBody,
    ssa: *MirSsaBuilder,
    bb_id: MirBlockId,
    is_enabled: bool,
) !MirValueId {
    const c_idx = try body.appendConst(.{ .bool_val = is_enabled });
    return ssa.emitInst(bb_id, .{
        .op = .const_scalar,
        .type_id = .bool_ty,
        .operands = .{ .lhs = c_idx, .rhs = 0 },
    }, TokenIndex.fromInt(0));
}

/// Builds a minimal valid baseline `MirBody` returning `42i32` for synthetic `V1`–`V6` mutation tests.
fn buildValidBaselineMirBody(allocator: std.mem.Allocator) !MirBody {
    var body = MirBody.init(allocator, FileId.fromInt(1), DefId.init(FileId.fromInt(1), 0));
    errdefer body.deinit();
    body.ret_ty = .i32_ty;
    body.has_ghost_instructions = true;

    const ret_local = try pushLocal(
        &body,
        LocalDecl.init(
            .empty,
            .i32_ty,
            TokenIndex.fromInt(0),
            0,
            .let_mode,
            .{ .is_return_slot = true },
        ),
    );
    const ret_place = try pushPlace(&body, ret_local, &.{});

    var builder = MirSsaBuilder.init(allocator, &body, &.{}, null);
    defer builder.deinit();

    const entry_bb = try builder.createBlock(true, false);
    _ = try builder.emitInst(entry_bb, .{
        .op = .ghost_storage_init,
        .type_id = .unit_ty,
        .operands = .{ .lhs = ret_local.asInt(), .rhs = 0 },
    }, TokenIndex.fromInt(0));
    const c42 = try emitIntConst(&body, &builder, entry_bb, .i32_ty, 42);
    _ = try builder.emitInst(entry_bb, .{
        .op = .place_store,
        .type_id = .unit_ty,
        .operands = .{ .lhs = ret_place.asInt(), .rhs = c42.asInt() },
    }, TokenIndex.fromInt(0));
    const loaded_ret = try builder.emitInst(entry_bb, .{
        .op = .place_load,
        .type_id = .i32_ty,
        .operands = .{ .lhs = ret_place.asInt(), .rhs = 0 },
    }, TokenIndex.fromInt(0));
    builder.setTerminator(entry_bb, .{
        .kind = .ret,
        .cond_or_val = loaded_ret.asInt(),
    });
    try builder.finish();
    return body;
}

/// Compiles `source` to `MIR`, verifies all bodies (`V1`–`V6`), and executes `entry_name` in `MirVm`.
fn lowerVerifyAndEvalI64(
    allocator: std.mem.Allocator,
    source: []const u8,
    target_layout: TargetLayout,
    entry_name: []const u8,
    arg_slots: []const mir_vm.RegSlot,
) !i64 {
    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(1),
        source,
        target_layout,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    for (bundle.mir_bundle.bodies.items) |*mir_body| {
        try mir.verifyMirBody(
            allocator,
            mir_body,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &bundle.hir_bundle.diagnostics,
        );
    }

    var rodata_pool = mir_vm.RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var memo_cache = mir_vm.PureCallMemoCache.init(allocator);
    defer memo_cache.deinit();

    var vm_engine = try mir_vm.MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        &memo_cache,
        &bundle.hir_bundle.diagnostics,
        .{ .target_layout = target_layout, .step_budget = 100_000 },
    );
    defer vm_engine.deinit();

    for (bundle.mir_bundle.bodies.items) |*mir_body| {
        var sym_idx = bundle.hir_bundle.sym_table.def_to_symbol.get(
            mir_body.def_id.asInt(),
        ) orelse symbol_resolver.SymbolIndex.none;
        if (sym_idx.isNone()) {
            for (bundle.hir_bundle.hir_store.functions.items) |fn_meta| {
                if (fn_meta.name == mir_body.name and !fn_meta.symbol_index.isNone()) {
                    sym_idx = fn_meta.symbol_index;
                    break;
                }
            }
        }
        _ = try vm_engine.registerBody(mir_body, sym_idx);
    }

    const entry_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        entry_name,
    ) orelse return error.MissingEntryBody;
    const eval_res = try vm_engine.evalBody(entry_body, arg_slots);
    return eval_res.slot.scalar_i64;
}

// ------------------------------------- PUBLIC API --------------------------------------

// Cache-line byte layout assertions (`DR-13` §3.1):

test "test_mir_exact_cache_line_byte_layout_invariants" {
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(LocalDecl));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(MirPlace));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(MirProjection));

    const mir_inst_soa_bytes = @sizeOf(MirOp) +
        @sizeOf(InstFlags) +
        @sizeOf(u16) +
        @sizeOf(TypeId) +
        @sizeOf(MirInst.Operands);
    try std.testing.expectEqual(@as(usize, 16), mir_inst_soa_bytes);

    try std.testing.expectEqual(@as(usize, 12), @sizeOf(MirTerminator));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(MirBasicBlock));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(MirOutgoingEdge));
}

// Braun et al. single-pass forward `MirSsaBuilder` invariants:

test "test_mir_ssa_builder_diamond_nested_loops_trivial_cascade_and_duplicate_edges" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(std.testing.allocator, &interner);
    defer sym_table.deinit();

    var body = MirBody.init(
        std.testing.allocator,
        FileId.fromInt(1),
        DefId.init(FileId.fromInt(1), 0),
    );
    defer body.deinit();
    body.ret_ty = .i32_ty;
    body.has_ghost_instructions = false;
    body.is_ghost_stripped = true;

    _ = try pushLocal(
        &body,
        LocalDecl.init(
            .empty,
            .i32_ty,
            TokenIndex.fromInt(0),
            0,
            .let_mode,
            .{ .is_return_slot = true },
        ),
    );

    // Variable 0 = mutable accumulator (`acc`), Variable 1 = loop-invariant scalar (`inv`):
    const var_types = [_]TypeId{ .i32_ty, .i32_ty };
    var ssa = MirSsaBuilder.init(std.testing.allocator, &body, &var_types, null);
    defer ssa.deinit();

    const entry_bb = try ssa.createBlock(true, false);
    const then_bb = try ssa.createBlock(true, false);
    const else_bb = try ssa.createBlock(true, false);
    const diamond_join_bb = try ssa.createBlock(true, false);
    const outer_hdr_bb = try ssa.createBlock(false, false);
    const inner_hdr_bb = try ssa.createBlock(false, false);
    const inner_exit_bb = try ssa.createBlock(true, false);
    const dup_merge_bb = try ssa.createBlock(true, false);
    const final_bb = try ssa.createBlock(true, false);

    // [1] Straight-line definitions in `entry_bb` + diamond `cond_br`:
    const cond_true = try emitBoolConst(&body, &ssa, entry_bb, true);
    const inv_seven = try emitIntConst(&body, &ssa, entry_bb, .i32_ty, 7);
    try ssa.writeVariable(1, entry_bb, inv_seven);

    const e_then = try ssa.addOutgoingEdge(entry_bb, then_bb, &.{}, 1);
    const e_else = try ssa.addOutgoingEdge(entry_bb, else_bb, &.{}, 0);
    std.debug.assert(e_else.asInt() == e_then.asInt() + 1);
    ssa.setTerminator(entry_bb, .{
        .kind = .cond_br,
        .cond_or_val = cond_true.asInt(),
        .edge_start = e_then.asInt(),
        .edge_len = 2,
    });

    const val_ten = try emitIntConst(&body, &ssa, then_bb, .i32_ty, 10);
    try ssa.writeVariable(0, then_bb, val_ten);
    const then_to_join = try ssa.addOutgoingEdge(then_bb, diamond_join_bb, &.{}, 0);
    ssa.setTerminator(then_bb, .{
        .kind = .br,
        .edge_start = then_to_join.asInt(),
        .edge_len = 1,
    });

    const val_twenty = try emitIntConst(&body, &ssa, else_bb, .i32_ty, 20);
    try ssa.writeVariable(0, else_bb, val_twenty);
    const else_to_join = try ssa.addOutgoingEdge(else_bb, diamond_join_bb, &.{}, 0);
    ssa.setTerminator(else_bb, .{
        .kind = .br,
        .edge_start = else_to_join.asInt(),
        .edge_len = 1,
    });

    // Reading `var 0` in `diamond_join_bb` synthesizes a join block-parameter:
    const joined_acc = try ssa.readVariable(0, diamond_join_bb);
    try ssa.writeVariable(0, diamond_join_bb, joined_acc);
    const join_to_outer = try ssa.addOutgoingEdge(diamond_join_bb, outer_hdr_bb, &.{}, 0);
    ssa.setTerminator(diamond_join_bb, .{
        .kind = .br,
        .edge_start = join_to_outer.asInt(),
        .edge_len = 1,
    });

    // [2] Unsealed nested loop headers (`outer_hdr_bb` -> `inner_hdr_bb`): reading invariant `var 1`
    // creates speculative params that cascade away via `tryRemoveTrivialBlockParam` when sealed:
    const outer_to_inner = try ssa.addOutgoingEdge(outer_hdr_bb, inner_hdr_bb, &.{}, 0);
    ssa.setTerminator(outer_hdr_bb, .{
        .kind = .br,
        .edge_start = outer_to_inner.asInt(),
        .edge_len = 1,
    });

    const inner_acc = try ssa.readVariable(0, inner_hdr_bb);
    const inner_inv = try ssa.readVariable(1, inner_hdr_bb);
    const next_acc = try ssa.emitInst(inner_hdr_bb, .{
        .op = .bin_op,
        .type_id = .i32_ty,
        .aux_u16 = @backingInt(mir.BinOpKind.sadd_checked),
        .operands = .{ .lhs = inner_acc.asInt(), .rhs = inner_inv.asInt() },
    }, TokenIndex.fromInt(0));
    try ssa.writeVariable(0, inner_hdr_bb, next_acc);

    const cond_false = try emitBoolConst(&body, &ssa, inner_hdr_bb, false);
    const inner_backedge = try ssa.addOutgoingEdge(inner_hdr_bb, inner_hdr_bb, &.{}, 1);
    const inner_to_exit = try ssa.addOutgoingEdge(inner_hdr_bb, inner_exit_bb, &.{}, 0);
    std.debug.assert(inner_to_exit.asInt() == inner_backedge.asInt() + 1);
    ssa.setTerminator(inner_hdr_bb, .{
        .kind = .cond_br,
        .cond_or_val = cond_false.asInt(),
        .edge_start = inner_backedge.asInt(),
        .edge_len = 2,
    });

    const outer_backedge = try ssa.addOutgoingEdge(inner_exit_bb, outer_hdr_bb, &.{}, 1);
    const outer_to_dup = try ssa.addOutgoingEdge(inner_exit_bb, dup_merge_bb, &.{}, 0);
    std.debug.assert(outer_to_dup.asInt() == outer_backedge.asInt() + 1);
    ssa.setTerminator(inner_exit_bb, .{
        .kind = .cond_br,
        .cond_or_val = cond_false.asInt(),
        .edge_start = outer_backedge.asInt(),
        .edge_len = 2,
    });

    try ssa.sealBlock(inner_hdr_bb);
    try ssa.sealBlock(outer_hdr_bb);

    // [3] Duplicate-target `cond_br` (`dup_merge_bb` -> `final_bb` on BOTH true and false edges!):
    const explicit_p = try ssa.addExplicitBlockParam(
        final_bb,
        .i32_ty,
        TokenIndex.fromInt(0),
        false,
    );
    const post_loop_acc = try ssa.readVariable(0, dup_merge_bb);
    const dup_true_edge = try ssa.addOutgoingEdge(
        dup_merge_bb,
        final_bb,
        &[_]MirValueId{post_loop_acc},
        1,
    );
    const dup_false_edge = try ssa.addOutgoingEdge(
        dup_merge_bb,
        final_bb,
        &[_]MirValueId{inv_seven},
        0,
    );
    try std.testing.expect(dup_true_edge != dup_false_edge);
    ssa.setTerminator(dup_merge_bb, .{
        .kind = .cond_br,
        .cond_or_val = cond_true.asInt(),
        .edge_start = dup_true_edge.asInt(),
        .edge_len = 2,
    });

    ssa.setTerminator(final_bb, .{
        .kind = .ret,
        .cond_or_val = explicit_p.asInt(),
    });
    try ssa.finish();

    // Cascading trivial block-param elimination left only `acc` (1 param, not 2!) on loop headers:
    try std.testing.expectEqual(@as(u16, 1), body.blocks.items[diamond_join_bb.asInt()].paramLen());
    try std.testing.expectEqual(@as(u16, 1), body.blocks.items[outer_hdr_bb.asInt()].paramLen());
    try std.testing.expectEqual(@as(u16, 1), body.blocks.items[inner_hdr_bb.asInt()].paramLen());
    try std.testing.expectEqual(@as(u32, 2), body.blocks.items[final_bb.asInt()].pred_len);

    // Must pass `MirVerifier` (`V1`–`V6`) cleanly:
    try mir.verifyMirBody(std.testing.allocator, &body, &pool, &sym_table, null);
}

// Maranget + Jacobs `switch_int` decision trees (`or_pat` sharing, destructuring, 128-bit ranges, guards):

test "test_mir_maranget_switch_int_or_pat_sharing_destructuring_128bit_ranges_and_guards" {
    const match_src =
        "pub struct PairPayload {\n" ++
        "    pub px: i32,\n" ++
        "    pub py: i32,\n" ++
        "}\n" ++
        "pub enum Event {\n" ++
        "    Idle,\n" ++
        "    Pair(PairPayload),\n" ++
        "    Big(u128),\n" ++
        "}\n" ++
        "pub fn heavy_arm_calc(seed: i32) -> i32 {\n" ++
        "    return seed * 3 + 1;\n" ++
        "}\n" ++
        "pub fn classify_event(tag: i32, lhs: i32, rhs: i32) -> i32 {\n" ++
        "    let high_u128: u128 = 170141183460469231731687303715884105729;\n" ++
        "    let ev: Event = if tag == 0 {\n" ++
        "        .Idle\n" ++
        "    } else if tag == 1 {\n" ++
        "        .Pair(PairPayload { px: lhs, py: rhs })\n" ++
        "    } else {\n" ++
        "        .Big(high_u128)\n" ++
        "    };\n" ++
        "    let ev_score: i32 = match ev {\n" ++
        "        .Pair(PairPayload { px, py }) if px > py => px * 10 + py,\n" ++
        "        .Pair(PairPayload { px, py }) => px + py + 100,\n" ++
        "        .Big(0..100) => 5,\n" ++
        "        .Big(170141183460469231731687303715884105728..=" ++
        "170141183460469231731687303715884105730) => 77,\n" ++
        "        .Idle | .Big(_) => 9,\n" ++
        "    };\n" ++
        "    let tup_pair: (i32, i32) = (lhs, rhs);\n" ++
        "    let tup_bonus: i32 = match tup_pair {\n" ++
        "        (0, 0) => 0,\n" ++
        "        (first_v, second_v) => first_v - first_v + second_v - second_v,\n" ++
        "    };\n" ++
        "    let or_score: i32 = match tag {\n" ++
        "        (10 | 11) | (12 | 13) => heavy_arm_calc(tag),\n" ++
        "        _ => 0,\n" ++
        "    };\n" ++
        "    let scale_128: i128 = 100;\n" ++
        "    let signed_128: i128 = (lhs as i128) * scale_128;\n" ++
        "    let i128_bonus: i32 = match signed_128 {\n" ++
        "        -500..=-100 => 50,\n" ++
        "        _ => 0,\n" ++
        "    };\n" ++
        "    return ev_score + tup_bonus + or_score + i128_bonus;\n" ++
        "}\n";

    // Verify `or_pat` `(10 | 11) | (12 | 13) => heavy_arm_calc(tag)` emits only ONE `.call` to `heavy_arm_calc`:
    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        match_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    const classify_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "classify_event",
    ).?;
    try std.testing.expectEqual(@as(usize, 1), classify_body.calls.items.len);

    // Guard true (`px > py`: `8 > 3` -> `83`):
    try std.testing.expectEqual(
        @as(i64, 83),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            match_src,
            TargetLayout.NATIVE_64,
            "classify_event",
            &[_]mir_vm.RegSlot{
                .{ .scalar_i64 = 1 },
                .{ .scalar_i64 = 8 },
                .{ .scalar_i64 = 3 },
            },
        ),
    );
    // Guard false (`px <= py`: `-2 <= 5` -> `.Pair(px, py) => 103`, plus `i128` range `+50` = `153`):
    try std.testing.expectEqual(
        @as(i64, 153),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            match_src,
            TargetLayout.WASM32,
            "classify_event",
            &[_]mir_vm.RegSlot{
                .{ .scalar_i64 = 1 },
                .{ .scalar_i64 = -2 },
                .{ .scalar_i64 = 5 },
            },
        ),
    );
    // High-bit `u128` inclusive range (`tag = 12` -> `Big(2^127 + 1) => 77`, `or_score = 37` -> `114`):
    try std.testing.expectEqual(
        @as(i64, 114),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            match_src,
            TargetLayout.NATIVE_64,
            "classify_event",
            &[_]mir_vm.RegSlot{
                .{ .scalar_i64 = 12 },
                .{ .scalar_i64 = 0 },
                .{ .scalar_i64 = 0 },
            },
        ),
    );
}

// LIFO `defer` & `errdefer |err|` cleanup pads + loop-interior `break`/`continue` unwind:

test "test_mir_lifo_defer_errdefer_payload_and_loop_scoped_unwind" {
    const defer_src =
        "pub fn fallible_work(should_fail: bool, trace: &mut i64) -> i64!i64 {\n" ++
        "    defer {\n" ++
        "        trace.* = trace.* * 10 + 1;\n" ++
        "    }\n" ++
        "    errdefer |err_code| {\n" ++
        "        trace.* = trace.* * 10 + err_code;\n" ++
        "    }\n" ++
        "    defer {\n" ++
        "        trace.* = trace.* * 10 + 3;\n" ++
        "    }\n" ++
        "    if should_fail {\n" ++
        "        return .Err(7);\n" ++
        "    }\n" ++
        "    return .Ok(9);\n" ++
        "}\n" ++
        "pub fn run_defer_suite(should_fail: bool) -> i64 {\n" ++
        "    var trace: i64 = 0;\n" ++
        "    let res = fallible_work(should_fail, &mut trace);\n" ++
        "    let _payload = res catch 0;\n" ++
        "    var loop_trace: i64 = 0;\n" ++
        "    defer {\n" ++
        "        loop_trace = loop_trace * 10 + 9;\n" ++
        "    }\n" ++
        "    for idx in 0..4 {\n" ++
        "        defer {\n" ++
        "            loop_trace = loop_trace * 10 + 5;\n" ++
        "        }\n" ++
        "        if idx == 0 {\n" ++
        "            continue;\n" ++
        "        }\n" ++
        "        if idx == 2 {\n" ++
        "            break;\n" ++
        "        }\n" ++
        "    }\n" ++
        "    return trace * 1000 + loop_trace;\n" ++
        "}\n";

    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        defer_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    // Confirm `errdefer` block is marked `.isCleanupPad()` (`DR-13` §3.4):
    const work_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "fallible_work",
    ).?;
    var has_cleanup_pad = false;
    for (work_body.blocks.items) |bb| {
        if (bb.isCleanupPad()) has_cleanup_pad = true;
    }
    try std.testing.expect(has_cleanup_pad);

    // Normal exit (`should_fail = false`): `defer #3` then `defer #1` (`trace = 31`), loop runs
    // `idx = 0..2` (`loop_trace = 555`), and outer `defer` runs after return capture -> `31555`:
    try std.testing.expectEqual(
        @as(i64, 31555),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            defer_src,
            TargetLayout.NATIVE_64,
            "run_defer_suite",
            &[_]mir_vm.RegSlot{.{ .scalar_u64 = 0 }},
        ),
    );

    // Error exit (`should_fail = true`): `defer #3` (`3`) -> `errdefer |7|` (`7`) -> `defer #1` (`1`) -> `371555`:
    try std.testing.expectEqual(
        @as(i64, 371555),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            defer_src,
            TargetLayout.NATIVE_64,
            "run_defer_suite",
            &[_]mir_vm.RegSlot{.{ .scalar_u64 = 1 }},
        ),
    );
}

// Zero-overhead `subscript … yield` CFG splicing (`let` read + `inout` write):

test "test_mir_subscript_yield_let_read_and_inout_write_zero_call_splicing" {
    const sub_src =
        "pub struct RingPair {\n" ++
        "    pub slots: [i32; 2],\n" ++
        "}\n" ++
        "impl RingPair {\n" ++
        "    pub subscript(events: &mut i32, idx: usize) -> i32 {\n" ++
        "        let {\n" ++
        "            events.* = events.* * 10 + 1;\n" ++
        "            yield self.slots[idx];\n" ++
        "            events.* = events.* * 10 + 2;\n" ++
        "        }\n" ++
        "        inout {\n" ++
        "            events.* = events.* * 10 + 1;\n" ++
        "            yield &mut self.slots[idx];\n" ++
        "            events.* = events.* * 10 + 2;\n" ++
        "        }\n" ++
        "    }\n" ++
        "}\n" ++
        "pub fn use_ring_subscript() -> i32 {\n" ++
        "    var ring = RingPair { slots: [10, 20] };\n" ++
        "    var events: i32 = 0;\n" ++
        "    ring[&mut events, 1] += 15;\n" ++
        "    let read_back: i32 = ring[&mut events, 1];\n" ++
        "    return events * 100 + read_back;\n" ++
        "}\n";

    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        sub_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    // Caller `use_ring_subscript` MUST splice both `subscript` uses inline with ZERO `.call` terminators:
    const caller_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "use_ring_subscript",
    ).?;
    try std.testing.expectEqual(@as(usize, 0), caller_body.calls.items.len);

    // Two `subscript` accesses (`+=` then read): `events = 1212`, `read_back = 35` -> `121235`:
    try std.testing.expectEqual(
        @as(i64, 121235),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            sub_src,
            TargetLayout.NATIVE_64,
            "use_ring_subscript",
            &.{},
        ),
    );
}

// `MirVerifier` positive & synthetic negative mutation suite covering all `V1`–`V6` invariants:

test "test_mir_verifier_positive_and_synthetic_negative_v1_through_v6" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(std.testing.allocator, &interner);
    defer sym_table.deinit();

    // [0] Positive baseline passes `verifyMirBody`:
    {
        var ok_body = try buildValidBaselineMirBody(std.testing.allocator);
        defer ok_body.deinit();
        try mir.verifyMirBody(std.testing.allocator, &ok_body, &pool, &sym_table, null);
    }

    // [V1a] Duplicate SSA definition (`error.V1DuplicateSsaDefinition`):
    {
        var dup_def_body = try buildValidBaselineMirBody(std.testing.allocator);
        defer dup_def_body.deinit();
        const first_inst = dup_def_body.getBlockInsts(MirBlockId.fromInt(0))[0];
        try dup_def_body.block_insts.append(std.testing.allocator, first_inst);
        dup_def_body.blocks.items[0].inst_len += 1;
        try std.testing.expectError(
            error.V1DuplicateSsaDefinition,
            mir.verifyMirBody(std.testing.allocator, &dup_def_body, &pool, &sym_table, null),
        );
    }

    // [V1b] Cooper-Harvey-Kennedy SSA dominance violation (`error.V1DominanceViolation`):
    {
        var dom_bad_body = try buildValidBaselineMirBody(std.testing.allocator);
        defer dom_bad_body.deinit();
        dom_bad_body.blocks.items[0].terminator.cond_or_val = 999;
        try std.testing.expectError(
            error.V1DominanceViolation,
            mir.verifyMirBody(std.testing.allocator, &dom_bad_body, &pool, &sym_table, null),
        );
    }

    // [V2a] Invalid terminator outgoing-edge count (`error.V2InvalidTerminatorOrEdge`):
    {
        var term_bad_body = try buildValidBaselineMirBody(std.testing.allocator);
        defer term_bad_body.deinit();
        term_bad_body.blocks.items[0].terminator = .{
            .kind = .cond_br,
            .cond_or_val = 0,
            .edge_start = 0,
            .edge_len = 1,
        };
        try std.testing.expectError(
            error.V2InvalidTerminatorOrEdge,
            mir.verifyMirBody(std.testing.allocator, &term_bad_body, &pool, &sym_table, null),
        );
    }

    // [V2b] Predecessor/outgoing-edge bijection mismatch (`error.V2PredEdgeBijectionMismatch`):
    {
        var bij_body = MirBody.init(
            std.testing.allocator,
            FileId.fromInt(1),
            DefId.init(FileId.fromInt(1), 0),
        );
        defer bij_body.deinit();
        bij_body.ret_ty = .i32_ty;
        bij_body.is_ghost_stripped = true;
        bij_body.has_ghost_instructions = false;
        _ = try pushLocal(
            &bij_body,
            LocalDecl.init(
                .empty,
                .i32_ty,
                TokenIndex.fromInt(0),
                0,
                .let_mode,
                .{ .is_return_slot = true },
            ),
        );
        var ssa = MirSsaBuilder.init(std.testing.allocator, &bij_body, &.{}, null);
        defer ssa.deinit();
        const bb0 = try ssa.createBlock(true, false);
        const bb1 = try ssa.createBlock(true, false);
        const edge0 = try ssa.addOutgoingEdge(bb0, bb1, &.{}, 0);
        ssa.setTerminator(bb0, .{ .kind = .br, .edge_start = edge0.asInt(), .edge_len = 1 });
        const c1 = try emitIntConst(&bij_body, &ssa, bb1, .i32_ty, 1);
        ssa.setTerminator(bb1, .{ .kind = .ret, .cond_or_val = c1.asInt() });
        try ssa.finish();
        bij_body.blocks.items[bb1.asInt()].pred_len = 0;
        try std.testing.expectError(
            error.V2PredEdgeBijectionMismatch,
            mir.verifyMirBody(std.testing.allocator, &bij_body, &pool, &sym_table, null),
        );
    }

    // [V2c] Block-argument arity mismatch (`error.V2EdgeArgCountMismatch`):
    {
        var arity_body = MirBody.init(
            std.testing.allocator,
            FileId.fromInt(1),
            DefId.init(FileId.fromInt(1), 0),
        );
        defer arity_body.deinit();
        arity_body.ret_ty = .i32_ty;
        arity_body.is_ghost_stripped = true;
        arity_body.has_ghost_instructions = false;
        _ = try pushLocal(
            &arity_body,
            LocalDecl.init(
                .empty,
                .i32_ty,
                TokenIndex.fromInt(0),
                0,
                .let_mode,
                .{ .is_return_slot = true },
            ),
        );
        var ssa = MirSsaBuilder.init(std.testing.allocator, &arity_body, &.{}, null);
        defer ssa.deinit();
        const bb0 = try ssa.createBlock(true, false);
        const bb1 = try ssa.createBlock(true, false);
        const c_arg = try emitIntConst(&arity_body, &ssa, bb0, .i32_ty, 5);
        const param_v = try ssa.addExplicitBlockParam(bb1, .i32_ty, TokenIndex.fromInt(0), false);
        const edge0 = try ssa.addOutgoingEdge(bb0, bb1, &[_]MirValueId{c_arg}, 0);
        ssa.setTerminator(bb0, .{ .kind = .br, .edge_start = edge0.asInt(), .edge_len = 1 });
        ssa.setTerminator(bb1, .{ .kind = .ret, .cond_or_val = param_v.asInt() });
        try ssa.finish();
        arity_body.extra_edges.items[edge0.asInt()].args_len = 0;
        try std.testing.expectError(
            error.V2EdgeArgCountMismatch,
            mir.verifyMirBody(std.testing.allocator, &arity_body, &pool, &sym_table, null),
        );
    }

    // [V2d] Call continuation split-edge violation (`error.V2CallContinuationSplitViolation`):
    {
        var call_split_body = MirBody.init(
            std.testing.allocator,
            FileId.fromInt(1),
            DefId.init(FileId.fromInt(1), 0),
        );
        defer call_split_body.deinit();
        call_split_body.ret_ty = .i32_ty;
        call_split_body.is_ghost_stripped = true;
        call_split_body.has_ghost_instructions = false;
        _ = try pushLocal(
            &call_split_body,
            LocalDecl.init(
                .empty,
                .i32_ty,
                TokenIndex.fromInt(0),
                0,
                .let_mode,
                .{ .is_return_slot = true },
            ),
        );
        var ssa = MirSsaBuilder.init(std.testing.allocator, &call_split_body, &.{}, null);
        defer ssa.deinit();
        const bb0 = try ssa.createBlock(true, false);
        const cont_bb = try ssa.createBlock(true, false);
        const fn_v = try ssa.emitInst(bb0, .{
            .op = .fn_addr,
            .type_id = .i32_ty,
            .operands = .{ .lhs = 1, .rhs = 0 },
        }, TokenIndex.fromInt(0));
        try call_split_body.calls.append(std.testing.allocator, .{
            .callee_val = fn_v,
            .ret_ty = .i32_ty,
            .args_start = 0,
            .args_len = 0,
            .modes_start = 0,
            .call_borrows_start = 0,
            .call_borrows_len = 0,
            .is_callee_contextless = true,
            .origin_token = TokenIndex.fromInt(0),
        });
        const call_edge = try ssa.addOutgoingEdge(bb0, cont_bb, &.{}, 0);
        ssa.setTerminator(bb0, .{
            .kind = .call,
            .cond_or_val = 0,
            .edge_start = call_edge.asInt(),
            .edge_len = 1,
        });
        const c0 = try emitIntConst(&call_split_body, &ssa, cont_bb, .i32_ty, 0);
        ssa.setTerminator(cont_bb, .{ .kind = .ret, .cond_or_val = c0.asInt() });
        try ssa.finish();
        try std.testing.expectError(
            error.V2CallContinuationSplitViolation,
            mir.verifyMirBody(std.testing.allocator, &call_split_body, &pool, &sym_table, null),
        );
    }

    // [V3] Invalid `MirPlace` projection (`error.V3InvalidPlaceProjection` dereferencing scalar `i32`):
    {
        var proj_bad_body = try buildValidBaselineMirBody(std.testing.allocator);
        defer proj_bad_body.deinit();
        _ = try pushPlace(
            &proj_bad_body,
            LocalId.fromInt(0),
            &[_]MirProjection{.{ .kind = .deref, .payload = 0 }},
        );
        try std.testing.expectError(
            error.V3InvalidPlaceProjection,
            mir.verifyMirBody(std.testing.allocator, &proj_bad_body, &pool, &sym_table, null),
        );
    }

    // [V4a] Unbalanced Ghost access stack (`error.V4UnbalancedGhostStack`):
    {
        var unbal_body = MirBody.init(
            std.testing.allocator,
            FileId.fromInt(1),
            DefId.init(FileId.fromInt(1), 0),
        );
        defer unbal_body.deinit();
        unbal_body.ret_ty = .i32_ty;
        const ret_loc = try pushLocal(
            &unbal_body,
            LocalDecl.init(
                .empty,
                .i32_ty,
                TokenIndex.fromInt(0),
                0,
                .let_mode,
                .{ .is_return_slot = true },
            ),
        );
        const ret_pl = try pushPlace(&unbal_body, ret_loc, &.{});
        var ssa = MirSsaBuilder.init(std.testing.allocator, &unbal_body, &.{}, null);
        defer ssa.deinit();
        const bb0 = try ssa.createBlock(true, false);
        _ = try ssa.emitInst(bb0, .{
            .op = .ghost_storage_init,
            .type_id = .unit_ty,
            .operands = .{ .lhs = ret_loc.asInt(), .rhs = 0 },
        }, TokenIndex.fromInt(0));
        const c5 = try emitIntConst(&unbal_body, &ssa, bb0, .i32_ty, 5);
        _ = try ssa.emitInst(bb0, .{
            .op = .place_store,
            .type_id = .unit_ty,
            .operands = .{ .lhs = ret_pl.asInt(), .rhs = c5.asInt() },
        }, TokenIndex.fromInt(0));
        _ = try ssa.emitInst(bb0, .{
            .op = .ghost_access_let,
            .type_id = .unit_ty,
            .operands = .{ .lhs = ret_pl.asInt(), .rhs = 0 },
        }, TokenIndex.fromInt(0));
        ssa.setTerminator(bb0, .{ .kind = .ret, .cond_or_val = c5.asInt() });
        try ssa.finish();
        try std.testing.expectError(
            error.V4UnbalancedGhostStack,
            mir.verifyMirBody(std.testing.allocator, &unbal_body, &pool, &sym_table, null),
        );
    }

    // [V4b] Law of Exclusivity overlap (`error.V4GhostExclusivityConflict`) + [V4c] Post-strip Ghost (`error.V4PostStripGhostPresent`):
    {
        var excl_body = MirBody.init(
            std.testing.allocator,
            FileId.fromInt(1),
            DefId.init(FileId.fromInt(1), 0),
        );
        defer excl_body.deinit();
        excl_body.ret_ty = .i32_ty;
        const ret_loc = try pushLocal(
            &excl_body,
            LocalDecl.init(
                .empty,
                .i32_ty,
                TokenIndex.fromInt(0),
                0,
                .let_mode,
                .{ .is_return_slot = true },
            ),
        );
        const ret_pl = try pushPlace(&excl_body, ret_loc, &.{});
        var ssa = MirSsaBuilder.init(std.testing.allocator, &excl_body, &.{}, null);
        defer ssa.deinit();
        const bb0 = try ssa.createBlock(true, false);
        _ = try ssa.emitInst(bb0, .{
            .op = .ghost_storage_init,
            .type_id = .unit_ty,
            .operands = .{ .lhs = ret_loc.asInt(), .rhs = 0 },
        }, TokenIndex.fromInt(0));
        const c5 = try emitIntConst(&excl_body, &ssa, bb0, .i32_ty, 5);
        _ = try ssa.emitInst(bb0, .{
            .op = .place_store,
            .type_id = .unit_ty,
            .operands = .{ .lhs = ret_pl.asInt(), .rhs = c5.asInt() },
        }, TokenIndex.fromInt(0));
        const tok_let = try ssa.emitInst(bb0, .{
            .op = .ghost_access_let,
            .type_id = .unit_ty,
            .operands = .{ .lhs = ret_pl.asInt(), .rhs = 0 },
        }, TokenIndex.fromInt(0));
        const tok_inout = try ssa.emitInst(bb0, .{
            .op = .ghost_access_inout,
            .type_id = .unit_ty,
            .operands = .{ .lhs = ret_pl.asInt(), .rhs = 0 },
        }, TokenIndex.fromInt(0));
        _ = try ssa.emitInst(bb0, .{
            .op = .ghost_access_end,
            .type_id = .unit_ty,
            .operands = .{ .lhs = tok_inout.asInt(), .rhs = 0 },
        }, TokenIndex.fromInt(0));
        _ = try ssa.emitInst(bb0, .{
            .op = .ghost_access_end,
            .type_id = .unit_ty,
            .operands = .{ .lhs = tok_let.asInt(), .rhs = 0 },
        }, TokenIndex.fromInt(0));
        ssa.setTerminator(bb0, .{ .kind = .ret, .cond_or_val = c5.asInt() });
        try ssa.finish();
        try std.testing.expectError(
            error.V4GhostExclusivityConflict,
            mir.verifyMirBody(std.testing.allocator, &excl_body, &pool, &sym_table, null),
        );

        excl_body.is_ghost_stripped = true;
        try std.testing.expectError(
            error.V4PostStripGhostPresent,
            mir.verifyMirBody(std.testing.allocator, &excl_body, &pool, &sym_table, null),
        );
    }

    // [V5a] Read of uninitialized local (`error.V5ReadUninitializedOrMoved`) & [V5b] Incomplete `_0` exit (`error.V5IncompleteExitInitialization`):
    {
        var uninit_body = MirBody.init(
            std.testing.allocator,
            FileId.fromInt(1),
            DefId.init(FileId.fromInt(1), 0),
        );
        defer uninit_body.deinit();
        uninit_body.ret_ty = .i32_ty;
        const ret_loc = try pushLocal(
            &uninit_body,
            LocalDecl.init(
                .empty,
                .i32_ty,
                TokenIndex.fromInt(0),
                0,
                .let_mode,
                .{ .is_return_slot = true },
            ),
        );
        const ret_pl = try pushPlace(&uninit_body, ret_loc, &.{});
        const c_idx = try uninit_body.appendConst(.{ .int_val = 1 });
        var ssa = MirSsaBuilder.init(std.testing.allocator, &uninit_body, &.{}, null);
        defer ssa.deinit();
        const bb0 = try ssa.createBlock(true, false);
        const bad_load = try ssa.emitInst(bb0, .{
            .op = .place_load,
            .type_id = .i32_ty,
            .operands = .{ .lhs = ret_pl.asInt(), .rhs = 0 },
        }, TokenIndex.fromInt(0));
        ssa.setTerminator(bb0, .{ .kind = .ret, .cond_or_val = bad_load.asInt() });
        try ssa.finish();
        try std.testing.expectError(
            error.V5ReadUninitializedOrMoved,
            mir.verifyMirBody(std.testing.allocator, &uninit_body, &pool, &sym_table, null),
        );

        uninit_body.insts.items(.op)[bad_load.asInt()] = .const_scalar;
        uninit_body.insts.items(.operands)[bad_load.asInt()] = .{ .lhs = c_idx, .rhs = 0 };
        try std.testing.expectError(
            error.V5IncompleteExitInitialization,
            mir.verifyMirBody(std.testing.allocator, &uninit_body, &pool, &sym_table, null),
        );
    }

    // [V6a] `@local` closure escape (`error.V6LocalClosureEscape`) & [V6b] `contextless` impurity (`error.V6ContextlessCallViolation`):
    {
        var esc_body = try buildValidBaselineMirBody(std.testing.allocator);
        defer esc_body.deinit();
        esc_body.insts.items(.flags)[1] = .{ .is_local_closure = true };
        try std.testing.expectError(
            error.V6LocalClosureEscape,
            mir.verifyMirBody(std.testing.allocator, &esc_body, &pool, &sym_table, null),
        );

        var ctx_body = MirBody.init(
            std.testing.allocator,
            FileId.fromInt(1),
            DefId.init(FileId.fromInt(1), 0),
        );
        defer ctx_body.deinit();
        ctx_body.ret_ty = .i32_ty;
        ctx_body.is_contextless = true;
        ctx_body.is_ghost_stripped = true;
        ctx_body.has_ghost_instructions = false;
        _ = try pushLocal(
            &ctx_body,
            LocalDecl.init(
                .empty,
                .i32_ty,
                TokenIndex.fromInt(0),
                0,
                .let_mode,
                .{ .is_return_slot = true },
            ),
        );
        var ssa = MirSsaBuilder.init(std.testing.allocator, &ctx_body, &.{}, null);
        defer ssa.deinit();
        const bb0 = try ssa.createBlock(true, false);
        const cont_bb = try ssa.createBlock(true, false);
        const ret_param = try ssa.addExplicitBlockParam(
            cont_bb,
            .i32_ty,
            TokenIndex.fromInt(0),
            true,
        );
        const fn_v = try ssa.emitInst(bb0, .{
            .op = .fn_addr,
            .type_id = .i32_ty,
            .operands = .{ .lhs = 1, .rhs = 0 },
        }, TokenIndex.fromInt(0));
        try ctx_body.calls.append(std.testing.allocator, .{
            .callee_val = fn_v,
            .ret_ty = .i32_ty,
            .args_start = 0,
            .args_len = 0,
            .modes_start = 0,
            .call_borrows_start = 0,
            .call_borrows_len = 0,
            .is_callee_contextless = false,
            .origin_token = TokenIndex.fromInt(0),
        });
        const call_edge = try ssa.addOutgoingEdge(bb0, cont_bb, &.{}, 0);
        ssa.setTerminator(bb0, .{
            .kind = .call,
            .cond_or_val = 0,
            .edge_start = call_edge.asInt(),
            .edge_len = 1,
        });
        ssa.setTerminator(cont_bb, .{ .kind = .ret, .cond_or_val = ret_param.asInt() });
        try ssa.finish();
        try std.testing.expectError(
            error.V6ContextlessCallViolation,
            mir.verifyMirBody(std.testing.allocator, &ctx_body, &pool, &sym_table, null),
        );
    }
}

// Deterministic `renderMir` formatting:

test "test_mir_render_deterministic_monochrome_formatting" {
    const render_src =
        "pub fn clamp_positive(val: i32) -> i32 {\n" ++
        "    if val < 0 {\n" ++
        "        return 0;\n" ++
        "    }\n" ++
        "    return val;\n" ++
        "}\n";

    var bundle_a = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        render_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle_a.deinit();
    var bundle_b = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        render_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle_b.deinit();

    const body_a = bundle_a.mir_bundle.findBodyByName(
        &bundle_a.hir_bundle.interner,
        "clamp_positive",
    ).?;
    const body_b = bundle_b.mir_bundle.findBodyByName(
        &bundle_b.hir_bundle.interner,
        "clamp_positive",
    ).?;

    const dump_a = try mir.renderMir(
        std.testing.allocator,
        body_a,
        &bundle_a.hir_bundle.interner,
    );
    defer std.testing.allocator.free(dump_a);
    const dump_b = try mir.renderMir(
        std.testing.allocator,
        body_b,
        &bundle_b.hir_bundle.interner,
    );
    defer std.testing.allocator.free(dump_b);

    try std.testing.expectEqualStrings(dump_a, dump_b);
    try std.testing.expect(std.mem.indexOf(u8, dump_a, "mir fn @clamp_positive") != null);
    try std.testing.expect(std.mem.indexOf(u8, dump_a, "^bb0(") != null);
}

test "test_mir_poison_projection_recovery_preserves_v3_place_soundness" {
    const poisoned_proj_src =
        "pub fn broken_projections(scalar_val: i32) -> i32 {\n" ++
        "    let bad_idx = scalar_val[0];\n" ++
        "    let bad_field = scalar_val.missing_member;\n" ++
        "    let bad_len = scalar_val.len;\n" ++
        "    let bad_deref = scalar_val.*;\n" ++
        "    let .Some(bad_variant) = scalar_val else { return 0; };\n" ++
        "    let _ignore_len = bad_len;\n" ++
        "    let _ignore_deref = bad_deref;\n" ++
        "    return bad_idx + bad_field + bad_variant;\n" ++
        "}\n";

    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        poisoned_proj_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(bundle.hir_bundle.diagnostics.hasErrors());
    for (bundle.mir_bundle.bodies.items) |*body_item| {
        try mir.verifyMirBody(
            std.testing.allocator,
            body_item,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            null,
        );
    }
}

// Phase 7.5 (`DR-21` `SE-01`–`SE-08`) MIR Lowering, Verifier & `MirVm` Tests:

test "test_phase75_mir_cond_scope_se01_se02_orelse_se03_dollar_slice_se04_se05_and_pats_se06" {
    // [1] `SE-01` (`is`) + `SE-02` (`:=` walrus) conjunctive `if` / `else if` / `while` & `SE-03` `orelse`:
    const cond_and_orelse_src =
        \\pub fn maybe_double(input_val: i64) -> i64? {
        \\    if input_val > 0 {
        \\        return .Some(input_val * 2);
        \\    }
        \\    return .None;
        \\}
        \\pub fn bump_counter(counter: &mut i64, delta: i64) -> i64 {
        \\    counter.* = counter.* + delta;
        \\    return counter.*;
        \\}
        \\pub fn check_orelse_skips_errdefer(opt_in: i64?) -> i64!i64 {
        \\    var trace_log: i64 = 10;
        \\    errdefer {
        \\        trace_log = 999;
        \\    }
        \\    let resolved_val: i64 = opt_in orelse bump_counter(&mut trace_log, 5);
        \\    return .Ok(resolved_val * 100 + trace_log);
        \\}
        \\pub fn eval_cond_scope(seed_val: i64) -> i64 {
        \\    var step_acc: i64 = 0;
        \\    let branch_score: i64 = if maybe_double(seed_val) is .Some(doubled) and (shifted := doubled + 3) > 10 {
        \\        shifted
        \\    } else if (fallback_v := seed_val + 7) > 8 {
        \\        fallback_v * 10
        \\    } else {
        \\        1
        \\    };
        \\    var cursor_opt: i64? = .Some(3);
        \\    while cursor_opt is .Some(rem_val) and (next_rem := rem_val - 1) >= 0 {
        \\        step_acc = step_acc + rem_val;
        \\        cursor_opt = if next_rem > 0 { .Some(next_rem) } else { .None };
        \\    }
        \\    let ok_some: i64 = match check_orelse_skips_errdefer(.Some(4)) {
        \\        .Ok(score_a) => score_a,
        \\        .Err(_) => -1,
        \\    };
        \\    let ok_none: i64 = match check_orelse_skips_errdefer(.None) {
        \\        .Ok(score_b) => score_b,
        \\        .Err(_) => -1,
        \\    };
        \\    return branch_score + step_acc + ok_some + ok_none;
        \\}
    ;

    // `seed_val = 5` yields `shifted = 13`, `step_acc = 6`, `ok_some = 410`, and `ok_none = 1515`;
    // expected sum `13 + 6 + 410 + 1515 = 1944`:
    try std.testing.expectEqual(
        @as(i64, 1944),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            cond_and_orelse_src,
            TargetLayout.NATIVE_64,
            "eval_cond_scope",
            &[_]mir_vm.RegSlot{.{ .scalar_i64 = 5 }},
        ),
    );

    // `seed_val = 2` takes `else if` `fallback_v = 9 > 8` (`90`); expected sum `90 + 6 + 410 + 1515 = 2021`:
    try std.testing.expectEqual(
        @as(i64, 2021),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            cond_and_orelse_src,
            TargetLayout.NATIVE_64,
            "eval_cond_scope",
            &[_]mir_vm.RegSlot{.{ .scalar_i64 = 2 }},
        ),
    );

    // [2] `SE-04` (`$` `is_dollar_sub`), `SE-05` (`..` / `..=` subslice), `SE-06` (`at_pat` + `slice_pat`), `SE-07`:
    const slice_and_pat_src =
        \\pub fn weighted_add(lhs_num: i64, scale: i64 = 2, bias: i64 = 5) -> i64 {
        \\    return lhs_num * scale + bias;
        \\}
        \\pub fn classify_slice(window: &[i64], tag_opt: i64?) -> i64 {
        \\    let pat_score: i64 = match window {
        \\        [] => 0,
        \\        [only_elem] => only_elem,
        \\        [head_elem, ..middle_rest, tail_elem] => head_elem * 100 + (middle_rest.len() as i64) * 10 + tail_elem,
        \\    };
        \\    let at_score: i64 = match tag_opt {
        \\        whole_opt @ .Some(inner_v) => if whole_opt is .Some(check_v) { inner_v + check_v } else { 0 },
        \\        .None => 0,
        \\    };
        \\    return pat_score + at_score;
        \\}
        \\pub fn run_dollar_and_patterns() -> i64 {
        \\    let outer_arr: [i64; 6] = [10, 20, 30, 40, 50, 60];
        \\    let inner_arr: [usize; 3] = [4, 2, 1];
        \\    let nested_sub: &[i64] = outer_arr[inner_arr[$ - 1]..$ - 1];
        \\    let incl_sub: &[i64] = outer_arr[1..=3];
        \\    let word_mid: str = "corex"[1..$ - 1];
        \\    let piped_val: i64 = (nested_sub[$ - 1] + incl_sub[$ - 1] + (word_mid.len() as i64))
        \\        |> weighted_add(bias: 7, scale: 3);
        \\    return piped_val + classify_slice(nested_sub, .Some(6));
        \\}
    ;

    var sp_bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(2),
        slice_and_pat_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer sp_bundle.deinit();
    try std.testing.expect(!sp_bundle.hir_bundle.diagnostics.hasErrors());
    const run_body = sp_bundle.mir_bundle.findBodyByName(
        &sp_bundle.hir_bundle.interner,
        "run_dollar_and_patterns",
    ).?;
    var has_dollar_sub_inst = false;
    for (0..run_body.insts.len) |inst_i| {
        const inst = run_body.insts.get(inst_i);
        if (inst.op == .bin_op and inst.flags.is_dollar_sub and
            inst.aux_u16 == @backingInt(mir.BinOpKind.usub_checked))
        {
            has_dollar_sub_inst = true;
            break;
        }
    }
    try std.testing.expect(has_dollar_sub_inst);

    // `nested_sub = [20, 30, 40, 50]`, `incl_sub = [20, 30, 40]`, `word_mid = "ore"` (`piped_val = 286`);
    // `classify_slice(nested_sub, .Some(6)) = 2082`, yielding `286 + 2082 = 2368`:
    try std.testing.expectEqual(
        @as(i64, 2368),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            slice_and_pat_src,
            TargetLayout.NATIVE_64,
            "run_dollar_and_patterns",
            &.{},
        ),
    );
}

test "test_phase75_mir_v6_contextless_ctx_intrinsic_and_vm_with_context_se08" {
    // [1] `SE-08` `V6`: `is_contextless` `MirBody` containing `MirIntrinsicKind.ctx_get` fails verification:
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(std.testing.allocator, &interner);
    defer sym_table.deinit();

    var bad_ctx_body = MirBody.init(
        std.testing.allocator,
        FileId.fromInt(3),
        DefId.init(FileId.fromInt(3), 0),
    );
    defer bad_ctx_body.deinit();
    bad_ctx_body.ret_ty = .u64_ty;
    bad_ctx_body.is_contextless = true;
    bad_ctx_body.is_ghost_stripped = true;
    bad_ctx_body.has_ghost_instructions = false;
    _ = try pushLocal(
        &bad_ctx_body,
        LocalDecl.init(
            .empty,
            .u64_ty,
            TokenIndex.fromInt(0),
            0,
            .let_mode,
            .{ .is_return_slot = true },
        ),
    );
    var ssa = MirSsaBuilder.init(std.testing.allocator, &bad_ctx_body, &.{}, null);
    defer ssa.deinit();
    const entry_bb = try ssa.createBlock(true, false);
    const slot_ord_v = try emitIntConst(&bad_ctx_body, &ssa, entry_bb, .u32_ty, 5);
    const args_start: u32 = @intCast(bad_ctx_body.extra_args.items.len);
    try bad_ctx_body.extra_args.append(std.testing.allocator, slot_ord_v.asInt());
    const ctx_val = try ssa.emitInst(entry_bb, .{
        .op = .intrinsic_op,
        .flags = .{ .has_side_effects = true },
        .aux_u16 = @backingInt(mir.MirIntrinsicKind.ctx_get),
        .type_id = .u64_ty,
        .operands = .{ .lhs = args_start, .rhs = 1 },
    }, TokenIndex.fromInt(0));
    ssa.setTerminator(entry_bb, .{ .kind = .ret, .cond_or_val = ctx_val.asInt() });
    try ssa.finish();

    try std.testing.expectError(
        error.V6ContextlessCallViolation,
        mir.verifyMirBody(std.testing.allocator, &bad_ctx_body, &pool, &sym_table, null),
    );

    // [2] `SE-08` `with context.cancel_token`: `MirVm` `PureCallMemoCache` never caches stale `context` reads:
    const with_ctx_src =
        \\pub fn read_token_plus(offset: u64) -> u64 {
        \\    return (context.cancel_token._handle as u64) + offset;
        \\}
        \\pub fn run_scoped_tokens() -> i64 {
        \\    let outer_tok = CancelToken { _handle: 40 };
        \\    let inner_tok = CancelToken { _handle: 100 };
        \\    let first_read: u64 = with context.cancel_token = outer_tok {
        \\        let inner_read: u64 = with context.cancel_token = inner_tok {
        \\            read_token_plus(5)
        \\        };
        \\        inner_read + read_token_plus(5)
        \\    };
        \\    let restored_read: u64 = read_token_plus(5);
        \\    return (first_read + restored_read) as i64;
        \\}
    ;
    // `inner_read = 105`, outer `read_token_plus(5)` after inner restore = `45`, `restored_read = 5` -> `155`:
    try std.testing.expectEqual(
        @as(i64, 155),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            with_ctx_src,
            TargetLayout.NATIVE_64,
            "run_scoped_tokens",
            &.{},
        ),
    );
}

test "test_regression_comptime_with_context_allocator_synthetic_ptr_cast" {
    const comptime_ctx_src =
        \\pub struct Arena {
        \\    pub cap: usize,
        \\}
        \\impl Arena {
        \\    pub fn release(&mut self) {}
        \\}
        \\pub struct LocalLog {
        \\    pub level: u32,
        \\}
        \\impl LocalLog {
        \\    pub fn as_handle(&self) -> usize = 0;
        \\}
        \\pub fn run_ctx_arena_and_log() -> i64 {
        \\    _ = context.allocator;
        \\    _ = context.logger;
        \\    var arena = Arena { cap: 56 };
        \\    defer arena.release();
        \\    let local_log = LocalLog { level: 3 };
        \\    let scoped_val: i64 = with context.allocator = &mut arena, context.logger = &local_log {
        \\        (if context.allocator._handle != 0 { 200 } else { 0 }) + (local_log.level as i64)
        \\    };
        \\    return scoped_val + (arena.cap as i64);
        \\}
        \\pub const CT_ARENA_RES: i64 = run_ctx_arena_and_log();
    ;

    try std.testing.expectEqual(
        @as(i64, 259),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            comptime_ctx_src,
            TargetLayout.NATIVE_64,
            "run_ctx_arena_and_log",
            &.{},
        ),
    );

    var db = try corex.CompilerDb.init(std.testing.allocator);
    defer db.deinit();
    const ok_file = FileId.fromInt(40);
    _ = try db.setInput(ok_file, comptime_ctx_src, .low);
    const ok_tree = try db.extractItemTree(ok_file);
    var ct_def: ?DefId = null;
    for (ok_tree.entries) |entry| {
        if (std.mem.eql(u8, entry.name_text, "CT_ARENA_RES")) {
            ct_def = entry.def_id;
            break;
        }
    }
    const ct_art = try db.evalComptimeDef(ct_def.?);
    try std.testing.expect(!ct_art.has_errors);
    try std.testing.expectEqual(@as(i128, 259), ct_art.value.int_val);

    // User-written pointer-to-integer cast at `comptime` (`is_synthetic == false`) still emits `E0503`:
    const bad_ptr_cast_src =
        \\pub fn cast_user_ptr() -> usize {
        \\    let local_num: i64 = 7;
        \\    let raw_ptr: *i64 = &raw local_num;
        \\    return unsafe { raw_ptr as usize };
        \\}
        \\pub const BAD_PTR_INT: usize = cast_user_ptr();
    ;
    const bad_file = FileId.fromInt(41);
    _ = try db.setInput(bad_file, bad_ptr_cast_src, .low);
    const bad_tree = try db.extractItemTree(bad_file);
    var bad_def: ?DefId = null;
    for (bad_tree.entries) |entry| {
        if (std.mem.eql(u8, entry.name_text, "BAD_PTR_INT")) {
            bad_def = entry.def_id;
            break;
        }
    }
    const bad_art = try db.evalComptimeDef(bad_def.?);
    try std.testing.expect(bad_art.has_errors);
    var has_e0503 = false;
    for (db.getComptimeDiagnostics(bad_def.?).?.diagnostics.items) |diag_item| {
        if (diag_item.code == .e0503_forbidden_comptime_operation) {
            has_e0503 = true;
            break;
        }
    }
    try std.testing.expect(has_e0503);
}

// ----------- Phase 7.6 (DR-22) FSM, Swap & Zext MIR -----------

test "test_phase76_mir_labeled_fsm_parallel_swap_and_bool_int_zext" {
    const dr22_mir_src =
        \\pub enum FsmStep {
        \\    Start(i64),
        \\    Accum(i64, i64),
        \\    Done(i64),
        \\}
        \\pub fn swap_pair(left: &mut i64, right: &mut i64) {
        \\    (left.*, right.*) = (right.*, left.*);
        \\}
        \\pub fn run_dr22_mir(flag: bool) -> i64 {
        \\    var first_v: i64 = 12;
        \\    var second_v: i64 = 30;
        \\    swap_pair(&mut first_v, &mut second_v);
        \\    let zext_bit: i64 = flag as i64;
        \\    let fsm_val: i64 = fsm: match FsmStep.Start(first_v) {
        \\        .Start(init_v) => continue :fsm .Accum(init_v, 3),
        \\        .Accum(cur_v, rem_steps) => if rem_steps > 0 {
        \\            continue :fsm .Accum(cur_v + second_v, rem_steps - 1);
        \\        } else {
        \\            continue :fsm .Done(cur_v);
        \\        },
        \\        .Done(final_v) => final_v,
        \\    };
        \\    return fsm_val * 10 + zext_bit;
        \\}
    ;

    // `first_v` becomes `30`, `second_v` becomes `12`; `30 + 3 * 12 = 66`; `66 * 10 + 1 = 661`:
    try std.testing.expectEqual(
        @as(i64, 661),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            dr22_mir_src,
            TargetLayout.NATIVE_64,
            "run_dr22_mir",
            &[_]mir_vm.RegSlot{.{ .scalar_u64 = 1 }},
        ),
    );
    try std.testing.expectEqual(
        @as(i64, 660),
        try lowerVerifyAndEvalI64(
            std.testing.allocator,
            dr22_mir_src,
            TargetLayout.NATIVE_64,
            "run_dr22_mir",
            &[_]mir_vm.RegSlot{.{ .scalar_u64 = 0 }},
        ),
    );
}

// ----------- Phase 10.6 (DR-23) Immediate AutoDrop ------------

test "test_phase106_mir_discard_stmt_immediate_autodrop_before_next_statement" {
    const discard_drop_src =
        \\pub struct ScopedGuard {
        \\    pub tag: i64,
        \\}
        \\impl ScopedGuard {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag);
        \\    }
        \\}
        \\@must_use
        \\pub fn make_guard(tag: i64) -> ScopedGuard = ScopedGuard { tag: tag };
        \\pub fn verify_immediate_discard_drop() -> i64 {
        \\    let block_guard = make_guard(10);
        \\    _ = make_guard(20);
        \\    @drop_trace(30);
        \\    return block_guard.tag;
        \\}
    ;

    var bundle = try corex.lowerAndVerifySourceMirSast(
        std.testing.allocator,
        FileId.fromInt(90),
        discard_drop_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.diagnostics.hasErrors());

    const entry_body = bundle.mir_module.findBodyByName(
        &bundle.interner,
        "verify_immediate_discard_drop",
    ).?;

    var rodata = mir_vm.RodataPool.init(std.testing.allocator);
    defer rodata.deinit();
    var vm = try mir_vm.MirVm.init(
        std.testing.allocator,
        &bundle.interner,
        &bundle.pool,
        &bundle.sym_table,
        &rodata,
        null,
        null,
        .{ .target_layout = TargetLayout.NATIVE_64 },
    );
    defer vm.deinit();
    for (bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, body_ptr.symbol_index);
    }

    const eval_res = try vm.evalBody(entry_body, &.{});
    try std.testing.expectEqual(@as(i64, 10), eval_res.slot.scalar_i64);
    // `_ = make_guard(20);` drops `20` immediately before `@drop_trace(30);`, while `block_guard` (`10`) drops at `}`:
    try std.testing.expectEqualSlices(i64, &[_]i64{ 20, 30, 10 }, vm.asDropTraceSlice());
    try std.testing.expectEqual(@as(u32, 0), vm.countUnfreedHeapAllocations());
}

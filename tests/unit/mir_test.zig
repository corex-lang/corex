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
        "pub fn fallible_work(should_fail: bool, trace: &mut i64) -> Result[i64, i64] {\n" ++
        "    defer {\n" ++
        "        *trace = *trace * 10 + 1;\n" ++
        "    }\n" ++
        "    errdefer |err_code| {\n" ++
        "        *trace = *trace * 10 + err_code;\n" ++
        "    }\n" ++
        "    defer {\n" ++
        "        *trace = *trace * 10 + 3;\n" ++
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
        "    pub events: i32,\n" ++
        "}\n" ++
        "pub subscript ring_slot(mut ring: inout RingPair, idx: usize) -> i32 {\n" ++
        "    ring.events = ring.events * 10 + 1;\n" ++
        "    yield ring.slots[idx];\n" ++
        "    ring.events = ring.events * 10 + 2;\n" ++
        "}\n" ++
        "pub fn use_ring_subscript() -> i32 {\n" ++
        "    var ring = RingPair { slots: [10, 20], events: 0 };\n" ++
        "    ring_slot(ring, 1) += 15;\n" ++
        "    let read_back: i32 = ring_slot(ring, 1);\n" ++
        "    return ring.events * 100 + read_back;\n" ++
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
        "    let bad_deref = *scalar_val;\n" ++
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

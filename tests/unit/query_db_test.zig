//! Unit Tests for Demand-Driven Incremental Query Engine (`tests/unit/query_db_test.zig`)
//!
//! Exercises `Revision`, `Durability`, `Fingerprint128`, `StructuralHasher`, `DefId`, `QueryStage`,
//! `QueryKey`, `MemoHeader`, and the 10-stage `CompilerDb` pipeline (`DR-12` Section 3).
//!
//! - Verifies `setInput` same-value no-ops, durability promotion/demotion, and multi-file revisions.
//! - Verifies `lower_ast` Early Cutoff on comment/whitespace edits and `ItemTree` signature firewalls
//!   isolating sibling definitions shifted by 50+ lines.
//! - Verifies 3-tier `Durability` fast-paths, green-path `min_durability` recomputation, cycle
//!   detection (`error.DependencyCycle`), cooperative cancellation (`error.Cancelled`), and all 11
//!   `ItemKind` variants in `extractItemTree`.

const std = @import("std");
const corex = @import("corex");

const query_db = corex.query_db;
const FileId = corex.FileId;
const Revision = corex.Revision;
const Durability = corex.Durability;
const Fingerprint128 = corex.Fingerprint128;
const StructuralHasher = corex.StructuralHasher;
const DefId = corex.DefId;
const QueryStage = corex.QueryStage;
const QueryKey = corex.QueryKey;
const MemoHeader = corex.MemoHeader;
const QueryError = corex.QueryError;
const ItemKind = corex.ItemKind;
const CompilerDb = corex.CompilerDb;

// -------------------------------------- INTERNALS --------------------------------------

/// Test hook that injects a synthetic 2-node dependency cycle on `.def_signature` queries.
fn injectDefSignatureCycleHook(db: *CompilerDb, key: QueryKey) QueryError!void {
    if (key.stage == .def_signature) {
        const current_def = DefId.fromInt(key.entity_index);
        const peer_ordinal: u12 = if (current_def.itemIndex() == 0) 1 else 0;
        _ = try db.getDefSignature(DefId.init(current_def.fileId(), peer_ordinal));
    }
}

/// Test hook that requests cooperative cancellation midway through `.typecheck_body`.
fn cancelDuringTypecheckHook(db: *CompilerDb, key: QueryKey) QueryError!void {
    if (key.stage == .typecheck_body) {
        db.requestCancellation();
        try db.unwindIfCancelled();
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------ Revisions, Durability & Fingerprints ------------

test "test_query_db_revision_durability_fingerprint_and_def_id_invariants" {
    // [1] `Revision` monotonic operations:
    const rev_one = Revision.initial;
    const rev_two = rev_one.next();
    const rev_ten = Revision.fromInt(10);
    try std.testing.expectEqual(@as(u32, 1), rev_one.asInt());
    try std.testing.expectEqual(@as(u32, 2), rev_two.asInt());
    try std.testing.expect(rev_two.isAfter(rev_one));
    try std.testing.expect(!rev_one.isAfter(rev_two));
    try std.testing.expect(!rev_one.isAfter(rev_one));
    try std.testing.expect(rev_ten.isAfter(rev_two));

    // [2] `Durability.minTier` lattice laws:
    try std.testing.expectEqual(Durability.low, Durability.minTier(.low, .high));
    try std.testing.expectEqual(Durability.low, Durability.minTier(.medium, .low));
    try std.testing.expectEqual(Durability.medium, Durability.minTier(.medium, .high));
    try std.testing.expectEqual(Durability.high, Durability.minTier(.high, .high));

    // [3] `Fingerprint128` (`hashBytes`, `hashBlake3`, `ZERO`, `eql`) and `StructuralHasher`:
    const bytes_alpha = "pub fn compute(val: i64) -> i64 { return val + 1; }";
    const bytes_beta = "pub fn compute(val: i64) -> i64 { return val + 2; }";
    const wy_alpha_1 = Fingerprint128.hashBytes(bytes_alpha);
    const wy_alpha_2 = Fingerprint128.hashBytes(bytes_alpha);
    const wy_beta = Fingerprint128.hashBytes(bytes_beta);
    try std.testing.expect(Fingerprint128.eql(wy_alpha_1, wy_alpha_2));
    try std.testing.expect(!Fingerprint128.eql(wy_alpha_1, wy_beta));
    try std.testing.expect(!Fingerprint128.eql(wy_alpha_1, Fingerprint128.ZERO));

    const b3_alpha_1 = Fingerprint128.hashBlake3(bytes_alpha);
    const b3_alpha_2 = Fingerprint128.hashBlake3(bytes_alpha);
    const b3_beta = Fingerprint128.hashBlake3(bytes_beta);
    try std.testing.expect(Fingerprint128.eql(b3_alpha_1, b3_alpha_2));
    try std.testing.expect(!Fingerprint128.eql(b3_alpha_1, b3_beta));
    try std.testing.expect(!Fingerprint128.eql(wy_alpha_1, b3_alpha_1));

    var hasher_a = StructuralHasher.init();
    hasher_a.updateU8(0x7F);
    hasher_a.updateU16(0x1234);
    hasher_a.updateU32(0x89AB_CDEF);
    hasher_a.updateU64(0x0123_4567_89AB_CDEF);
    hasher_a.updateBytes("structural_payload");
    hasher_a.updateFingerprint(wy_alpha_1);

    var hasher_b = StructuralHasher.init();
    hasher_b.updateU8(0x7F);
    hasher_b.updateU16(0x1234);
    hasher_b.updateU32(0x89AB_CDEF);
    hasher_b.updateU64(0x0123_4567_89AB_CDEF);
    hasher_b.updateBytes("structural_payload");
    hasher_b.updateFingerprint(wy_alpha_2);

    const struct_fp_a = hasher_a.final();
    try std.testing.expect(Fingerprint128.eql(struct_fp_a, hasher_b.final()));

    hasher_b.updateU8(0x01);
    try std.testing.expect(!Fingerprint128.eql(struct_fp_a, hasher_b.final()));

    // [4] `DefId` packing, `asU64`, `NONE` sentinel, and boundary clamping:
    try std.testing.expect(DefId.NONE.isNone());
    try std.testing.expectEqual(FileId.none, DefId.NONE.fileId());
    try std.testing.expectEqual(@as(u64, std.math.maxInt(u32)), DefId.NONE.asU64());

    const normal_def = DefId.init(FileId.fromInt(77), 19);
    try std.testing.expect(!normal_def.isNone());
    try std.testing.expectEqual(FileId.fromInt(77), normal_def.fileId());
    try std.testing.expectEqual(@as(u12, 19), normal_def.itemIndex());
    try std.testing.expectEqual(normal_def, DefId.fromInt(normal_def.asInt()));
    try std.testing.expectEqual(@as(u64, normal_def.asInt()), normal_def.asU64());

    const clamped_def = DefId.init(FileId.fromInt(0xF_FFFF), 0xFFF);
    try std.testing.expect(!clamped_def.isNone());
    try std.testing.expectEqual(FileId.fromInt(0xF_FFFF), clamped_def.fileId());
    try std.testing.expectEqual(@as(u12, 0xFFE), clamped_def.itemIndex());

    // [5] `QueryKey` and `MemoHeader` size and key uniqueness:
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(QueryKey));
    try std.testing.expectEqual(@as(usize, 40), @sizeOf(MemoHeader));
    const file_key = QueryKey.forFile(.lower_ast, FileId.fromInt(5));
    const def_key = QueryKey.forDef(.typecheck_body, normal_def);
    try std.testing.expect(file_key.asU64() != def_key.asU64());
}

// ---------- 10-Stage Pipeline & Input Mutation Rules ----------

test "test_query_db_full_10_stage_pipeline_and_input_mutation_semantics" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const missing_file = FileId.fromInt(999);
    try std.testing.expectError(error.MissingSourceInput, db.getSourceText(missing_file));
    try std.testing.expectError(error.InvalidDefId, db.getItemTreeSigProj(DefId.NONE));
    try std.testing.expectError(error.InvalidDefId, db.getBodyAstProj(DefId.NONE));
    try std.testing.expectError(error.InvalidDefId, db.getDefSignature(DefId.NONE));
    try std.testing.expectError(error.InvalidDefId, db.typecheckBody(DefId.NONE));
    try std.testing.expectError(error.InvalidDefId, db.verifySastMir(DefId.NONE));

    const file_id = FileId.fromInt(1);
    const source_v1 =
        "pub const SCALE_FACTOR: i64 = 10;\n" ++
        "pub fn scale_value(input_val: i64) -> i64 {\n" ++
        "    return input_val * SCALE_FACTOR;\n" ++
        "}\n";

    // [1] Initial registration stays at `Revision.initial` (`1`):
    const rev1 = try db.setInput(file_id, source_v1, .low);
    try std.testing.expectEqual(Revision.initial, rev1);

    // [2] Calling `setInput` with identical text and durability is a no-op:
    try std.testing.expectEqual(rev1, try db.setInput(file_id, source_v1, .low));

    // [3] Execute all 10 query stages on `file_id` and its definitions:
    const fetched_text = try db.getSourceText(file_id);
    try std.testing.expectEqualStrings(source_v1, fetched_text);

    const parsed_cst = try db.parseCst(file_id);
    try std.testing.expect(!parsed_cst.has_parse_errors);
    try std.testing.expect(parsed_cst.cst_arena.countNodes() > 0);

    const lowered_ast = try db.lowerAst(file_id);
    try std.testing.expectEqual(file_id, lowered_ast.file_id);
    try std.testing.expect(!lowered_ast.has_parse_errors);
    try std.testing.expect(Fingerprint128.eql(parsed_cst.ast_fingerprint, lowered_ast.ast_fingerprint));

    const item_tree = try db.extractItemTree(file_id);
    try std.testing.expectEqual(@as(usize, 2), item_tree.entries.len);
    const const_def = item_tree.entries[0].def_id;
    const fn_def = item_tree.entries[1].def_id;

    // Out-of-bounds `DefId` ordinal for `file_id` returns `error.InvalidDefId`:
    try std.testing.expectError(error.InvalidDefId, db.getDefSignature(DefId.init(file_id, 99)));

    const fn_sig_proj = try db.getItemTreeSigProj(fn_def);
    try std.testing.expect(Fingerprint128.eql(item_tree.entries[1].signature_fingerprint, fn_sig_proj));

    const fn_body_proj = try db.getBodyAstProj(fn_def);
    try std.testing.expectEqual(fn_def, fn_body_proj.def_id);
    try std.testing.expect(Fingerprint128.eql(item_tree.entries[1].body_fingerprint, fn_body_proj.body_fingerprint));

    const resolved_sigs = try db.resolveSignatures(file_id);
    try std.testing.expectEqual(@as(u32, 2), resolved_sigs.item_count);
    try std.testing.expectEqual(@as(u32, 2), resolved_sigs.public_item_count);

    const def_sig = try db.getDefSignature(fn_def);
    try std.testing.expectEqual(ItemKind.fn_decl, def_sig.kind);
    try std.testing.expect(def_sig.is_pub);

    const typed_body = try db.typecheckBody(fn_def);
    try std.testing.expectEqual(fn_def, typed_body.def_id);
    try std.testing.expect(Fingerprint128.eql(def_sig.signature_fingerprint, typed_body.signature_fingerprint));

    const sast_res = try db.verifySastMir(fn_def);
    try std.testing.expect(sast_res.is_verified_sound);

    const const_sast = try db.verifySastMir(const_def);
    try std.testing.expect(const_sast.is_verified_sound);
}

// --------- Early Cutoff on Whitespace & Comment Edits ---------

test "test_query_db_early_cutoff_at_lower_ast_on_whitespace_and_comment_edits" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(3);
    const source_clean =
        "pub fn add_pair(lhs: i32, rhs: i32) -> i32 {\n" ++
        "    return lhs + rhs;\n" ++
        "}\n";

    const rev1 = try db.setInput(file_id, source_clean, .low);
    const tree_r1 = try db.extractItemTree(file_id);
    const fn_def = tree_r1.entries[0].def_id;
    _ = try db.verifySastMir(fn_def);

    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.parse_cst));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.lower_ast));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.item_tree));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.typecheck_body));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.verify_sast_mir));

    // Inject module doc comments, doc comments, block comments, line comments, and extra blank lines:
    const source_commented =
        "//! Module documentation header\n\n" ++
        "/// Doc comment on add_pair\n" ++
        "pub fn add_pair(   lhs: i32 , /* inline block */ rhs: i32   ) -> i32 {\n\n\n" ++
        "    // Explaining addition step:\n" ++
        "    return lhs + rhs; // trailing comment\n" ++
        "}\n";

    const rev2 = try db.setInput(file_id, source_commented, .low);
    try std.testing.expect(rev2.isAfter(rev1));

    _ = try db.verifySastMir(fn_def);

    // `parse_cst` and `lower_ast` re-ran, `lower_ast` backdated `changed_at` to `rev1`,
    // so `item_tree`, `resolve_signatures`, `def_signature`, `body_ast_proj`, `typecheck_body`,
    // and `verify_sast_mir` all verified green without re-executing!
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.parse_cst));
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.lower_ast));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.item_tree));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.resolve_signatures));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.def_signature));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.body_ast_proj));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.typecheck_body));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.verify_sast_mir));

    const lower_memo = db.getMemoHeader(QueryKey.forFile(.lower_ast, file_id)).?;
    try std.testing.expectEqual(rev1, lower_memo.changed_at);
    try std.testing.expectEqual(rev2, lower_memo.verified_at);
}

// ---- ItemTree Firewall & 50-Line Sibling Shift Isolation -----

test "test_query_db_item_tree_firewall_and_50_line_sibling_shift_isolation" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(4);
    const source_r1 =
        "pub fn first_fn(alpha: i64) -> i64 {\n" ++
        "    let base = alpha + 1;\n" ++
        "    return base;\n" ++
        "}\n\n" ++
        "pub fn second_fn(beta: i64) -> i64 {\n" ++
        "    let doubled = beta * 2;\n" ++
        "    return doubled - 1;\n" ++
        "}\n\n" ++
        "impl Counter {\n" ++
        "    pub fn step(&mut self) -> i64 {\n" ++
        "        return 1;\n" ++
        "    }\n" ++
        "}\n";

    const rev1 = try db.setInput(file_id, source_r1, .low);
    const tree_r1 = try db.extractItemTree(file_id);
    try std.testing.expectEqual(@as(usize, 3), tree_r1.entries.len);

    const def_first = tree_r1.entries[0].def_id;
    const def_second = tree_r1.entries[1].def_id;
    const def_impl = tree_r1.entries[2].def_id;

    _ = try db.verifySastMir(def_first);
    _ = try db.verifySastMir(def_second);
    _ = try db.verifySastMir(def_impl);
    try std.testing.expectEqual(@as(u64, 3), db.telemetry.countExecutions(.typecheck_body));

    // Edit `first_fn`'s body and `impl Counter`'s method body, plus insert 50 lines so `second_fn` shifts by 50 lines:
    const fifty_newlines: *const [50]u8 = &@splat('\n');
    const source_r2 =
        "pub fn first_fn(alpha: i64) -> i64 {\n" ++
        "    let base = alpha + 999;\n" ++
        "    let extra = base * 7;\n" ++
        fifty_newlines ++
        "    return extra;\n" ++
        "}\n\n" ++
        "pub fn second_fn(beta: i64) -> i64 {\n" ++
        "    let doubled = beta * 2;\n" ++
        "    return doubled - 1;\n" ++
        "}\n\n" ++
        "impl Counter {\n" ++
        "    pub fn step(&mut self) -> i64 {\n" ++
        "        return 42;\n" ++
        "    }\n" ++
        "}\n";

    const rev2 = try db.setInput(file_id, source_r2, .low);
    try std.testing.expect(rev2.isAfter(rev1));

    // [1] Query `second_fn`: despite shifting down by > 50 lines and `item_tree` changing,
    // `second_fn`'s `def_signature` and `body_ast_proj` both backdate to `rev1`, so `typecheckBody` does NOT run!
    _ = try db.verifySastMir(def_second);
    try std.testing.expectEqual(@as(u64, 3), db.telemetry.countExecutions(.typecheck_body));
    try std.testing.expectEqual(@as(u64, 3), db.telemetry.countExecutions(.verify_sast_mir));

    // [2] Query `first_fn`: `def_signature` backdates to `rev1`, while `body_ast_proj` changes at `rev2`,
    // triggering `typecheckBody(def_first)`:
    _ = try db.verifySastMir(def_first);
    try std.testing.expectEqual(@as(u64, 4), db.telemetry.countExecutions(.typecheck_body));
    try std.testing.expectEqual(@as(u64, 4), db.telemetry.countExecutions(.verify_sast_mir));

    // [3] Query `def_impl`: its method signature is unchanged (`item_tree_sig_proj` backdates to `rev1`),
    // while its method body changed (`body_ast_proj` changes at `rev2`):
    _ = try db.verifySastMir(def_impl);
    try std.testing.expectEqual(@as(u64, 5), db.telemetry.countExecutions(.typecheck_body));
    try std.testing.expectEqual(@as(u64, 5), db.telemetry.countExecutions(.verify_sast_mir));

    try std.testing.expectEqual(
        rev1,
        db.getMemoHeader(QueryKey.forDef(.def_signature, def_first)).?.changed_at,
    );
    try std.testing.expectEqual(
        rev1,
        db.getMemoHeader(QueryKey.forDef(.def_signature, def_second)).?.changed_at,
    );
    try std.testing.expectEqual(
        rev1,
        db.getMemoHeader(QueryKey.forDef(.def_signature, def_impl)).?.changed_at,
    );
    try std.testing.expectEqual(
        rev1,
        db.getMemoHeader(QueryKey.forDef(.body_ast_proj, def_second)).?.changed_at,
    );
    try std.testing.expectEqual(
        rev2,
        db.getMemoHeader(QueryKey.forDef(.body_ast_proj, def_first)).?.changed_at,
    );
    try std.testing.expectEqual(
        rev2,
        db.getMemoHeader(QueryKey.forDef(.body_ast_proj, def_impl)).?.changed_at,
    );
}

// ------- Durability Fast-Path & Demotion Recomputation --------

test "test_query_db_durability_fast_path_and_green_path_durability_demotion" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const stdlib_file = FileId.fromInt(10);
    const workspace_file = FileId.fromInt(11);
    const stdlib_src = "pub fn min_i32(first_val: i32, second_val: i32) -> i32 { return first_val; }\n";

    _ = try db.setInput(stdlib_file, stdlib_src, .high);
    _ = try db.setInput(workspace_file, "pub fn main_entry() -> i32 { return 1; }\n", .low);

    const stdlib_tree = try db.extractItemTree(stdlib_file);
    const stdlib_def = stdlib_tree.entries[0].def_id;
    _ = try db.verifySastMir(stdlib_def);

    const memo_r2 = db.getMemoHeader(QueryKey.forDef(.verify_sast_mir, stdlib_def)).?;
    try std.testing.expectEqual(Durability.high, memo_r2.min_durability);
    try std.testing.expect(memo_r2.is_pure_high_durability);

    // [1] Mutating `.low` durability `workspace_file` allows `stdlib_def` to skip edge traversal via fast-path:
    _ = try db.setInput(workspace_file, "pub fn main_entry() -> i32 { return 2; }\n", .low);
    const fast_hits_before = db.telemetry.durability_fast_path_hits;
    _ = try db.verifySastMir(stdlib_def);
    try std.testing.expectEqual(fast_hits_before + 1, db.telemetry.durability_fast_path_hits);

    // [2] Demoting `stdlib_file` from `.high` to `.low` (with identical source text) forces Green Path walk
    // and updates `stdlib_def`'s `min_durability` from `.high` down to `.low`!
    const rev_demoted = try db.setInput(stdlib_file, stdlib_src, .low);
    _ = try db.verifySastMir(stdlib_def);

    const memo_demoted = db.getMemoHeader(QueryKey.forDef(.verify_sast_mir, stdlib_def)).?;
    try std.testing.expectEqual(rev_demoted, memo_demoted.verified_at);
    try std.testing.expectEqual(Durability.low, memo_demoted.min_durability);
    try std.testing.expect(!memo_demoted.is_pure_high_durability);

    // [3] Resetting telemetry zeroes all counters:
    db.telemetry.reset();
    try std.testing.expectEqual(@as(u64, 0), db.telemetry.green_hits);
    try std.testing.expectEqual(@as(u64, 0), db.telemetry.durability_fast_path_hits);
    try std.testing.expectEqual(@as(u64, 0), db.telemetry.early_cutoff_hits);
}

// --------- Cycle Recovery & Cooperative Cancellation ----------

test "test_query_db_dependency_cycle_detection_and_cooperative_cancellation" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(20);
    _ = try db.setInput(
        file_id,
        "pub fn alpha(val: i32) -> i32 { return val; }\npub fn beta(val: i32) -> i32 { return val; }\n",
        .low,
    );
    const tree = try db.extractItemTree(file_id);
    const def_alpha = tree.entries[0].def_id;

    // [1] Inject a mutual `.def_signature` cycle and verify clean stack unwinding:
    db.setCustomStageHook(injectDefSignatureCycleHook);
    try std.testing.expectError(error.DependencyCycle, db.verifySastMir(def_alpha));
    try std.testing.expectEqual(@as(usize, 0), db.active_stack.items.len);
    try std.testing.expectEqual(@as(usize, 0), db.in_flight_keys.count());
    try std.testing.expectEqual(@as(usize, 0), db.scratch_dep_edges.items.len);
    db.setCustomStageHook(null);

    // [2] Inject mid-query cancellation via `cancelDuringTypecheckHook`:
    db.setCustomStageHook(cancelDuringTypecheckHook);
    try std.testing.expectError(error.Cancelled, db.verifySastMir(def_alpha));
    try std.testing.expect(db.isCancelled());
    try std.testing.expectError(error.Cancelled, db.unwindIfCancelled());
    try std.testing.expectEqual(@as(usize, 0), db.active_stack.items.len);
    db.setCustomStageHook(null);

    // [3] Clear cancellation and verify full query completion:
    db.clearCancellation();
    try std.testing.expect(!db.isCancelled());
    try db.unwindIfCancelled();
    const sast_res = try db.verifySastMir(def_alpha);
    try std.testing.expect(sast_res.is_verified_sound);
}

// --------- Comprehensive ItemTree Extraction Coverage ---------

test "test_query_db_extract_item_tree_all_item_kinds_and_lookup_helpers" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(30);
    const all_items_src =
        "pub mod network;\n" ++
        "use std::io::{Read, Write};\n" ++
        "pub const MAX_RETRY: usize = (16 + 4);\n" ++
        "pub type PortNum = u16;\n" ++
        "pub struct PacketHeader {\n    pub length: u32,\n}\n" ++
        "pub enum ConnectionState {\n    Idle,\n    Active(u32),\n}\n" ++
        "pub union PayloadWord {\n    raw_u64: u64,\n    raw_f64: f64,\n}\n" ++
        "pub trait Serializable {\n    fn encode(&self) -> u32;\n}\n" ++
        "impl Serializable for PacketHeader {\n    fn encode(&self) -> u32 {\n        return self.length;\n    }\n}\n" ++
        "impl Serializable for PortNum {\n    fn encode(&self) -> u32 {\n        return 0;\n    }\n}\n" ++
        "pub fn dispatch_packet(hdr: PacketHeader) -> u32 {\n    return hdr.length;\n}\n" ++
        "comptime {\n    let check_size = 1;\n}\n";

    _ = try db.setInput(file_id, all_items_src, .medium);
    const tree = try db.extractItemTree(file_id);
    try std.testing.expectEqual(@as(usize, 12), tree.entries.len);

    // Verify all 11 `ItemKind` categories and extracted symbol names:
    try std.testing.expectEqual(ItemKind.mod_decl, tree.entries[0].kind);
    try std.testing.expectEqualStrings("network", tree.entries[0].name_text);
    try std.testing.expect(tree.entries[0].is_pub);

    try std.testing.expectEqual(ItemKind.use_decl, tree.entries[1].kind);
    try std.testing.expectEqualStrings("Write", tree.entries[1].name_text);
    try std.testing.expect(!tree.entries[1].is_pub);

    try std.testing.expectEqual(ItemKind.const_decl, tree.entries[2].kind);
    try std.testing.expectEqualStrings("MAX_RETRY", tree.entries[2].name_text);
    try std.testing.expect(tree.entries[2].is_pub);

    try std.testing.expectEqual(ItemKind.type_alias_decl, tree.entries[3].kind);
    try std.testing.expectEqualStrings("PortNum", tree.entries[3].name_text);

    try std.testing.expectEqual(ItemKind.struct_decl, tree.entries[4].kind);
    try std.testing.expectEqualStrings("PacketHeader", tree.entries[4].name_text);

    try std.testing.expectEqual(ItemKind.enum_decl, tree.entries[5].kind);
    try std.testing.expectEqualStrings("ConnectionState", tree.entries[5].name_text);

    try std.testing.expectEqual(ItemKind.union_decl, tree.entries[6].kind);
    try std.testing.expectEqualStrings("PayloadWord", tree.entries[6].name_text);

    try std.testing.expectEqual(ItemKind.trait_decl, tree.entries[7].kind);
    try std.testing.expectEqualStrings("Serializable", tree.entries[7].name_text);

    try std.testing.expectEqual(ItemKind.impl_decl, tree.entries[8].kind);
    try std.testing.expectEqualStrings("Serializable for PacketHeader", tree.entries[8].name_text);

    try std.testing.expectEqual(ItemKind.impl_decl, tree.entries[9].kind);
    try std.testing.expectEqualStrings("Serializable for PortNum", tree.entries[9].name_text);

    try std.testing.expectEqual(ItemKind.fn_decl, tree.entries[10].kind);
    try std.testing.expectEqualStrings("dispatch_packet", tree.entries[10].name_text);

    try std.testing.expectEqual(ItemKind.extern_block, tree.entries[11].kind);
    try std.testing.expectEqualStrings("comptime", tree.entries[11].name_text);

    // Verify `ItemTree.findByName` and `ItemTree.getEntry`:
    const found_fn = tree.findByName("dispatch_packet").?;
    try std.testing.expectEqual(tree.entries[10].def_id, found_fn.def_id);
    try std.testing.expect(tree.findByName("non_existent_symbol") == null);
    try std.testing.expect(tree.getEntry(DefId.init(FileId.fromInt(99), 0)) == null);
}

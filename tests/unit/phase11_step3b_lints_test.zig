//! Phase 11.1c (`RDG-25` Step 3B) – All 27 `TypeChecker`, Idiom Audit & `MIR` Single-Pass Lint Rules
//!
//! End-to-end verification suite covering the remaining 27 built-in lint rules completing all 44
//! `RuleId`s (`0..43`), including MVS & exclusivity soundness guards (`Ruling 4.2 #1`–`#5`),
//! overlap priorities (`Ruling 4.1 #1`–`#5`), cross-file intra-package call-site rewrites
//! (`W0206`, `W0207`, `W0413`), and four-scope `@expect` / `@allow` integration.

const std = @import("std");
const stage0 = @import("corex");
const mem = stage0.mem_foundation;
const diag = stage0.diagnostic;
const query_db = stage0.query_db;
const check_audit = stage0.check_audit;
const mir_sast = stage0.mir_sast;
const codegen_abi = stage0.codegen_abi;
const type_system = stage0.type_system;

const FileId = mem.FileId;
const Span = mem.Span;
const DiagnosticCode = diag.DiagnosticCode;
const DiagnosticSink = diag.DiagnosticSink;
const CompilerDb = query_db.CompilerDb;

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `sink` contains at least one diagnostic with `target_code`.
fn hasDiagCode(sink: *const DiagnosticSink, target_code: DiagnosticCode) bool {
    for (sink.asSlice()) |diag_item| {
        if (diag_item.code == target_code) return true;
    }
    return false;
}

/// Counts how many diagnostics in `sink` match `target_code`.
fn countDiagCode(sink: *const DiagnosticSink, target_code: DiagnosticCode) usize {
    var total: usize = 0;
    for (sink.asSlice()) |diag_item| {
        if (diag_item.code == target_code) total += 1;
    }
    return total;
}

/// Sets up a single-file `CompilerDb` root fixture and returns projected diagnostics.
fn initSingleFileDb(
    allocator: std.mem.Allocator,
    file_id: FileId,
    source: []const u8,
) !CompilerDb {
    var db = try CompilerDb.init(allocator);
    errdefer db.deinit();
    try db.setFilePackageId(file_id, .root);
    try db.setFilePath(file_id, "D:/ws/src/main.cx");
    _ = try db.setInput(file_id, source, .low);
    try db.setPackageLintSemanticSettings(.root, .{}, null);
    try db.setPackageLintFilterConfig(.root, "D:/ws", .{}, null);
    return db;
}

// ---------------------------------------- TESTS ----------------------------------------

test "test_dr25_typecheck_lints_w0120_fmt_braces_w0204_shadow_w0205_bool_and_w0208_types" {
    const allocator = std.testing.allocator;

    // [1] `W0120` fires in `FmtArgs` context (including multiline), NEVER on plain `let text: str = "{val}";`:
    {
        const fid = FileId.fromInt(801);
        const src =
            \\fn write_msg(args: FmtArgs) {
            \\    _ = args;
            \\}
            \\fn keep_str(text: str) -> str {
            \\    text
            \\}
            \\pub fn log_msg(val: i32) -> str {
            \\    _ = val;
            \\    write_msg("value is {val}");
            \\    write_msg("
            \\        line1
            \\        line2 {val}
            \\        ");
            \\    keep_str("{val}")
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        try std.testing.expectEqual(@as(usize, 2), countDiagCode(sink, .w0120_uninterpolated_fmt_placeholder));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = true,
        });
        const fixed_src = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed_src, "f\"value is {val}\"") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed_src, "keep_str(\"{val}\")") != null);
        const post_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post_sink.error_count);
    }

    // [2] `W0204` (`shadowed-binding`) flags live outer bindings & loop back-edges, allows dead rebinding:
    {
        const fid = FileId.fromInt(802);
        const src =
            \\pub fn shadow_cases(raw_in: i32, maybe_num: i32?) -> i32 {
            \\    let raw_in = raw_in + 1;
            \\    let mut_step = if maybe_num is .Some(maybe_num) { maybe_num } else { 0 };
            \\    let outer_live = 10;
            \\    if mut_step > 0 {
            \\        let outer_live = 20;
            \\        _ = outer_live;
            \\    }
            \\    var loop_idx: i32 = 0;
            \\    let loop_bound = 3;
            \\    while loop_idx < loop_bound {
            \\        let loop_bound = 99;
            \\        _ = loop_bound;
            \\        loop_idx += 1;
            \\    }
            \\    raw_in + outer_live
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        try std.testing.expectEqual(@as(usize, 2), countDiagCode(sink, .w0204_shadowed_binding));
    }

    // [3] `W0205` (`bool-predicate-naming`) rejects `validate_*` & non-predicates, allows `is_valid_*` & mutators:
    {
        const fid = FileId.fromInt(803);
        const src =
            \\pub fn validate_utf8(input: str) -> bool {
            \\    input.len() > 0
            \\}
            \\pub fn is_valid_utf8(input: str) -> bool {
            \\    input.len() > 0
            \\}
            \\pub fn advance_slot(slot: &mut i32) -> bool {
            \\    slot.* += 1;
            \\    slot.* > 0
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(sink, .w0205_bool_predicate_naming));
    }

    // [4] `W0208` (`redundant-literal-type`) strips redundant `: T` on self-identifying RHS, preserves unsuffixed:
    {
        const fid = FileId.fromInt(804);
        const src =
            \\pub struct Pair {
            \\    pub lhs: i32,
            \\    pub rhs: i32,
            \\}
            \\pub fn demo_types(raw_val: i32) -> u32 {
            \\    let explicit_unsuffixed: u32 = 27;
            \\    let suffixed_num: u32 = 10_u32;
            \\    let ready_flag: bool = true;
            \\    let pair_val: Pair = Pair { lhs: 1, rhs: 2 };
            \\    let casted_num: u32 = raw_val as u32;
            \\    _ = ready_flag;
            \\    _ = pair_val;
            \\    explicit_unsuffixed + suffixed_num + casted_num
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        try std.testing.expectEqual(@as(usize, 4), countDiagCode(sink, .w0208_redundant_literal_type));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "let explicit_unsuffixed: u32 = 27;") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "let suffixed_num = 10_u32;") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "let ready_flag = true;") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "let pair_val = Pair { lhs: 1, rhs: 2 };") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "let casted_num = raw_val as u32;") != null);
    }
}

test "test_dr25_mvs_exclusivity_soundness_w0210_swap_aliasing_w0412_copy_and_w0414_nan" {
    const allocator = std.testing.allocator;

    // [1] `W0210` (`Ruling 4.2 #1`): rewrites disjoint swap + compound assign, SKIPS `items[i]`/`items[j]` aliasing!
    {
        const fid = FileId.fromInt(805);
        const src =
            \\pub fn swap_and_compound(items: &mut [i32], i: usize, j: usize, delta: i32) -> i32 {
            \\    var left_val = 1;
            \\    var right_val = 2;
            \\    let temp_disjoint = left_val;
            \\    left_val = right_val;
            \\    right_val = temp_disjoint;
            \\    left_val = left_val + delta;
            \\
            \\    if i < items.len() and j < items.len() {
            \\        let temp_elem = items[i];
            \\        items[i] = items[j];
            \\        items[j] = temp_elem;
            \\    }
            \\    left_val + right_val
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        try std.testing.expectEqual(@as(usize, 2), countDiagCode(sink, .w0210_manual_assign_or_swap));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "(left_val, right_val) = (right_val, left_val);") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "left_val += delta;") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "let temp_elem = items[i];") != null);
        const post_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post_sink.error_count);
    }

    // [2] `W0412` (`Ruling 4.2 #3`): `val.clone()` -> `val` and `ref_val.clone()` -> `ref_val.*` on `T: Copy`:
    {
        const fid = FileId.fromInt(806);
        const src =
            \\@derive(Copy, Clone)
            \\pub struct TagId {
            \\    pub raw: u32,
            \\}
            \\pub fn copy_clones(owned_tag: TagId, borrowed_tag: &TagId) -> u32 {
            \\    let first_tag: TagId = owned_tag.clone();
            \\    let second_tag: TagId = borrowed_tag.clone();
            \\    first_tag.raw + second_tag.raw
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 2), countDiagCode(sink, .w0412_clone_on_copy));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "owned_tag;") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "borrowed_tag.*;") != null);
        const post_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post_sink.error_count);
    }

    // [3] `W0414` (`identical-operands`) + `W0401` (`unreachable-pattern` on `match` & `if is` chain):
    {
        const fid = FileId.fromInt(807);
        const src =
            \\fn next_tick(state: &mut i32) -> i32 {
            \\    state.* += 1;
            \\    state.*
            \\}
            \\pub fn check_ident_and_patterns(val: i32, flt: f64, maybe_x: i32?, state: &mut i32) -> bool {
            \\    let impure_ok = next_tick(state) == next_tick(state);
            \\    let nan_probe = flt != flt;
            \\    let same_cmp = val == val;
            \\    let matched = match maybe_x {
            \\        .Some(num) => num,
            \\        .Some(_) => 0,
            \\        .None => -1,
            \\    };
            \\    var chain_out: i32 = 0;
            \\    if maybe_x is .Some(num_a) {
            \\        chain_out = num_a;
            \\    } else if maybe_x is .Some(num_b) {
            \\        chain_out = num_b;
            \\    }
            \\    _ = matched;
            \\    _ = chain_out;
            \\    impure_ok and nan_probe and same_cmp
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        try std.testing.expectEqual(@as(usize, 2), countDiagCode(sink, .w0414_identical_operands));
        try std.testing.expectEqual(@as(usize, 2), countDiagCode(sink, .w0401_unreachable_pattern_arm));
    }
}

test "test_dr25_overlap_priorities_and_fusions_w0407_to_w0411_w0209_w0405_and_w0402" {
    const allocator = std.testing.allocator;

    // [1] `W0407` > `W0408`, `W0410` > `W0409` > `W0407`, and `W0411` + `W0209` 1-pass convergence (`Ruling 4.1`):
    {
        const fid = FileId.fromInt(808);
        const src =
            \\@derive(Copy, Clone)
            \\pub enum StepErr {
            \\    BadInput,
            \\}
            \\fn wrap_ok(val: i32) -> i32!StepErr {
            \\    .Ok(val)
            \\}
            \\pub fn simplify_all(
            \\    flag_a: bool,
            \\    flag_b: bool,
            \\    maybe_val: i32?,
            \\    res_val: i32!StepErr,
            \\) -> i32!StepErr {
            \\    var acc: i32 = 0;
            \\    if flag_a {
            \\        if flag_b {
            \\            acc += 1;
            \\        }
            \\    }
            \\    let unwrapped = match maybe_val {
            \\        .Some(inner_v) => inner_v,
            \\        .None => 5,
            \\    };
            \\    let propagated = match res_val {
            \\        .Ok(ok_v) => ok_v,
            \\        .Err(err_v) => return .Err(err_v),
            \\    };
            \\    let inv_eq = not (acc == unwrapped);
            \\    if inv_eq {
            \\        acc += propagated;
            \\    }
            \\    let single_out = wrap_ok(acc);
            \\    return single_out;
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        try std.testing.expect(hasDiagCode(sink, .w0408_collapsible_if));
        try std.testing.expectEqual(@as(usize, 2), countDiagCode(sink, .w0410_manual_orelse_or_try));
        try std.testing.expect(hasDiagCode(sink, .w0407_needless_bool_branch));
        try std.testing.expect(hasDiagCode(sink, .w0411_single_use_temp));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "if flag_a and flag_b") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "maybe_val orelse 5") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "res_val?") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "acc != unwrapped") != null);
        // `W0411` + `W0209` fused in a single pass directly to tail `wrap_ok(acc)`:
        try std.testing.expect(std.mem.indexOf(u8, fixed, "single_out") == null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "return wrap_ok(acc)") == null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "wrap_ok(acc)\n}") != null);

        const post_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post_sink.error_count);
    }

    // [2] `W0405` (`unused-mut-binding`) + `W0402` struct-shorthand 1-pass `--fix-unsafe` fusion (`Ruling 4.1 #5`):
    {
        const fid = FileId.fromInt(809);
        const src =
            \\pub struct Coord {
            \\    pub x_pos: i32,
            \\    pub y_pos: i32,
            \\}
            \\pub fn test_unused_mut(var unmut_param: i32, coord: Coord, out_ref: &mut i32) -> i32 {
            \\    out_ref.* = unmut_param;
            \\    var unread_local = 10;
            \\    let Coord { var x_pos, y_pos } = coord;
            \\    y_pos
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        // `unmut_param`, `unread_local`, and `var x_pos` trigger `W0405`; `out_ref: &mut i32` does NOT!
        try std.testing.expectEqual(@as(usize, 3), countDiagCode(sink, .w0405_unused_mut_binding));
        try std.testing.expectEqual(@as(usize, 2), countDiagCode(sink, .w0402_unused_binding));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = true,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "(unmut_param: i32") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "let _unread_local = 10;") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "x_pos: _x_pos") != null);

        const post_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post_sink.error_count);
        try std.testing.expectEqual(@as(usize, 0), post_sink.warning_count);
    }
}

test "test_dr25_mir_single_pass_lints_w0334_move_w0335_loop_str_w0329_w0332_and_w0501" {
    const allocator = std.testing.allocator;

    // [1] `W0334` (`Ruling 4.2 #2`): `consume(buf.clone())` -> `consume(own buf)`, `let y = buf.clone()` -> `let y = buf`:
    {
        const fid = FileId.fromInt(810);
        const src =
            \\pub struct OwnedBuf {
            \\    pub tag: i32,
            \\}
            \\impl Drop for OwnedBuf {
            \\    fn drop(&mut self) {
            \\        self.tag = 0;
            \\    }
            \\}
            \\impl OwnedBuf {
            \\    pub fn clone(&self) -> OwnedBuf {
            \\        OwnedBuf { tag: self.tag }
            \\    }
            \\}
            \\fn sink_buf(item: own OwnedBuf) -> i32 {
            \\    item.tag
            \\}
            \\pub fn move_instead_of_clone(flag: bool) -> i32 {
            \\    let first_buf = OwnedBuf { tag: 7 };
            \\    let second_buf = OwnedBuf { tag: 9 };
            \\    let loop_buf = OwnedBuf { tag: 3 };
            \\    var sum: i32 = 0;
            \\    var idx: i32 = 0;
            \\    while idx < 2 {
            \\        let iter_copy = loop_buf.clone();
            \\        sum += iter_copy.tag;
            \\        idx += 1;
            \\    }
            \\    if flag {
            \\        let rebound = second_buf.clone();
            \\        sum += rebound.tag;
            \\    }
            \\    sum + sink_buf(first_buf.clone())
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        // `first_buf.clone()` and `second_buf.clone()` fire `W0334`; loop-carried `loop_buf.clone()` does NOT!
        try std.testing.expectEqual(@as(usize, 2), countDiagCode(sink, .w0334_redundant_move_clone));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "sink_buf(own first_buf)") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "let rebound = second_buf;") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "loop_buf.clone()") != null);

        const post_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post_sink.error_count);
    }

    // [2] `W0335` (`string-concat-in-loop`): flags unreserved `String.new()` `.push_str`, exempts `with_capacity`:
    {
        const fid = FileId.fromInt(811);
        const src =
            \\pub struct String {
            \\    pub len_val: usize,
            \\}
            \\impl String {
            \\    pub fn new() -> String {
            \\        String { len_val: 0 }
            \\    }
            \\    pub fn with_capacity(cap: usize) -> String {
            \\        String { len_val: cap }
            \\    }
            \\    pub fn push_str(&mut self, piece: str) {
            \\        self.len_val += piece.len();
            \\    }
            \\}
            \\pub fn build_strings(items: &[str]) -> usize {
            \\    var bad_str = String.new();
            \\    var good_str = String.with_capacity(64);
            \\    for chunk in items {
            \\        bad_str.push_str(chunk);
            \\        good_str.push_str(chunk);
            \\    }
            \\    bad_str.len_val + good_str.len_val
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(sink, .w0335_string_concat_in_loop));
    }

    // [3] `W0329` (`Ruling 4.2 #5`): `@allow(W0329)` hides warning while STILL inserting `abort_vacated_panic`:
    {
        const fid = FileId.fromInt(812);
        const src =
            \\pub struct Vec[T] {
            \\    pub len: usize,
            \\}
            \\pub struct NonCopySlot {
            \\    pub buf: Vec[i64],
            \\}
            \\pub struct SlotPair {
            \\    pub items: [NonCopySlot; 2],
            \\}
            \\impl SlotPair {
            \\    pub subscript(idx: usize) -> NonCopySlot {
            \\        inout {
            \\            yield &mut self.items[idx];
            \\        }
            \\    }
            \\}
            \\@allow(W0329, reason: "guarded vacated window test")
            \\pub fn write_through_vacated_branch(
            \\    use_branch_a: bool,
            \\    lookup_idx: usize,
            \\) -> usize {
            \\    var slots = SlotPair {
            \\        items: [
            \\            NonCopySlot { buf: Vec { len: 1 } },
            \\            NonCopySlot { buf: Vec { len: 2 } },
            \\        ],
            \\    };
            \\    let table: [usize; 2] = [10, 20];
            \\    slots[0] = if use_branch_a {
            \\        NonCopySlot { buf: Vec { len: table[lookup_idx] } }
            \\    } else {
            \\        NonCopySlot { buf: Vec { len: 99 } }
            \\    };
            \\    slots.items[0].buf.len
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const proj_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), proj_sink.error_count);
        try std.testing.expect(!hasDiagCode(proj_sink, .w0329_vacated_projection_panic_abort));

        var bundle = try mir_sast.lowerAndVerifySourceMirSast(
            allocator,
            fid,
            src,
            type_system.TargetLayout.NATIVE_64,
            .{},
        );
        defer bundle.deinit();
        var saw_abort_guard = false;
        for (bundle.mir_module.bodies.items) |body_item| {
            for (0..body_item.insts.len) |inst_i| {
                const inst = body_item.insts.get(inst_i);
                if (inst.op == .intrinsic_op and
                    @as(stage0.mir.MirIntrinsicKind, @fromBackingInt(inst.aux_u16)) == .abort_vacated_panic)
                {
                    saw_abort_guard = true;
                }
            }
        }
        try std.testing.expect(saw_abort_guard);
    }

    // [4] `W0332` (`nondeterministic-sim-source`) & `W0501` (`inlining-budget-exceeded`) via `projectFileDiagnostics`:
    {
        const fid = FileId.fromInt(813);
        const src =
            \\extern "C" fn getrandom(buf: *mut u8, len: usize, flags: u32) -> isize;
            \\@inline(always)
            \\pub fn rec_always(n: i32) -> i32 {
            \\    if n <= 0 {
            \\        0
            \\    } else {
            \\        rec_always(n - 1) + 1
            \\    }
            \\}
            \\pub fn probe_rng(ptr: *mut u8) -> isize {
            \\    unsafe { getrandom(ptr, 0, 0) }
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(sink, .w0501_inlining_budget_exceeded));

        const sim_src =
            \\extern "C" fn clock_gettime(clk_id: i32, tp: *mut u8) -> i32;
            \\pub fn run_sim_step(tp: *mut u8) -> i32 {
            \\    unsafe { clock_gettime(0, tp) }
            \\}
            \\test "sim_bypass" {
            \\    let raw_ptr = 0 as *mut u8;
            \\    _ = run_sim_step(raw_ptr);
            \\}
        ;
        var sim_bundle = try mir_sast.lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(814),
            sim_src,
            type_system.TargetLayout.NATIVE_64,
            .{ .is_sim_mode = true },
        );
        defer sim_bundle.deinit();
        try std.testing.expect(hasDiagCode(&sim_bundle.diagnostics, .w0332_nondeterministic_sim_source));
    }
}

test "test_dr25_cross_file_call_site_rewrites_and_target_word_width_w0206_w0207_w0413" {
    const allocator = std.testing.allocator;

    const fid_api = FileId.fromInt(820);
    const fid_use = FileId.fromInt(821);
    const api_src =
        \\@derive(Copy, Clone)
        \\pub struct Span8 {
        \\    pub lo: u32,
        \\    pub hi: u32,
        \\}
        \\impl Span8 {
        \\    pub fn get_width(&self) -> u32 {
        \\        self.hi - self.lo
        \\    }
        \\    pub fn to_bounds(&self) -> &Span8 {
        \\        self
        \\    }
        \\}
        \\pub(super) fn span_sum(target: &Span8) -> u32 {
        \\    target.*.lo + target.hi
        \\}
    ;
    const use_src =
        \\pub mod api;
        \\pub fn compute_total(item: api.Span8) -> u32 {
        \\    let view = item.to_bounds();
        \\    view.get_width() + api.span_sum(&item) + item.lo + item.hi
        \\}
    ;

    // [1] On `wasm32` (`ptr_byte_size == 4`), `Span8` (`8 B > 4 B`) does NOT trigger `W0413`:
    {
        var wasm_db = try CompilerDb.init(allocator);
        defer wasm_db.deinit();
        wasm_db.setTargetSpec(codegen_abi.TargetSpec.WASM32_FREESTANDING);
        try wasm_db.setFilePackageId(fid_api, .root);
        try wasm_db.setFilePath(fid_api, "D:/ws/src/api.cx");
        _ = try wasm_db.setInput(fid_api, api_src, .low);
        try wasm_db.setPackageLintSemanticSettings(.root, .{}, null);
        try wasm_db.setPackageLintFilterConfig(.root, "D:/ws", .{}, null);

        const wasm_sink = try wasm_db.projectFileDiagnostics(fid_api);
        try std.testing.expect(!hasDiagCode(wasm_sink, .w0413_trivially_copy_pass_by_ref));
    }

    // [2] On 64-bit (`ptr_byte_size == 8`), `W0206`, `W0207`, and `W0413` fire and rewrite BOTH files cleanly:
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_GNU);
        try db.setFilePackageId(fid_api, .root);
        try db.setFilePackageId(fid_use, .root);
        try db.setFilePath(fid_api, "D:/ws/src/api.cx");
        try db.setFilePath(fid_use, "D:/ws/src/main.cx");
        _ = try db.setInput(fid_api, api_src, .low);
        _ = try db.setInput(fid_use, use_src, .low);
        try db.bindExternalModule(fid_use, "api", fid_api);
        try db.setPackageLintSemanticSettings(.root, .{}, null);
        try db.setPackageLintFilterConfig(.root, "D:/ws", .{}, null);

        const api_sink = try db.projectFileDiagnostics(fid_api);
        try std.testing.expectEqual(@as(usize, 0), api_sink.error_count);
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(api_sink, .w0206_getter_prefix_noise));
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(api_sink, .w0207_conversion_prefix_mismatch));
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(api_sink, .w0413_trivially_copy_pass_by_ref));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{ fid_api, fid_use },
            .allow_unsafe_fixes = true,
        });
        const fixed_api = try db.getSourceText(fid_api);
        const fixed_use = try db.getSourceText(fid_use);

        try std.testing.expect(std.mem.indexOf(u8, fixed_api, "pub fn width(&self) -> u32") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed_api, "pub fn as_bounds(&self) -> &Span8") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed_api, "pub(super) fn span_sum(target: Span8) -> u32") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed_api, "target.lo + target.hi") != null);

        try std.testing.expect(std.mem.indexOf(u8, fixed_use, "item.as_bounds()") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed_use, "view.width()") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed_use, "api.span_sum(item)") != null);

        const post_api = try db.projectFileDiagnostics(fid_api);
        const post_use = try db.projectFileDiagnostics(fid_use);
        try std.testing.expectEqual(@as(usize, 0), post_api.error_count);
        try std.testing.expectEqual(@as(usize, 0), post_use.error_count);
        try std.testing.expectEqual(@as(usize, 0), post_api.warning_count);
        try std.testing.expectEqual(@as(usize, 0), post_use.warning_count);
    }
}

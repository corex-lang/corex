//! Phase 8 Deterministic C11/C23 FFI, Archive/COFF & Async Concurrency Fuzz Suite
//!
//! Exercises the zero-`libclang` C11/C23 frontend, PE/COFF `.def` / `!<arch>\n` archive serializers,
//! and stackless coroutine / `TaskGroup` execution pipelines under seeded `Xoroshiro128` mutation.
//!
//! Enforces `corex fmt` idempotency on translated headers, bounded recovery on adversarial C/`.def`
//! inputs, byte-identical archive output, and 4-tier `diff_oracle` parity on generated `async` programs.

const std = @import("std");
const corex = @import("corex");

const FileId = corex.FileId;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;
const c_frontend = corex.c_frontend;
const c_translate = corex.c_translate;
const codegen_link = corex.codegen_link;
const mir_vm = corex.mir_vm;

// --------------------------------------- CONSTS ----------------------------------------

/// Number of structured valid C11/C23 headers translated and checked for `corex fmt` idempotency.
const STRUCTURED_C_HEADER_SEEDS: usize = 48;
/// Number of adversarial / byte-mutated C11/C23 buffers fed into `parseCHeader`.
const ADVERSARIAL_C_HEADER_SEEDS: usize = 96;
/// Number of randomized valid `.def` module definitions serialized to COFF `.lib` archives.
const VALID_MODULE_DEF_SEEDS: usize = 48;
/// Number of adversarial / corrupted `.def` buffers fed into `parseModuleDef`.
const ADVERSARIAL_MODULE_DEF_SEEDS: usize = 64;
/// Number of randomized multi-member static archives verified across `K_GNU`, `K_BSD`, and `K_COFF`.
const MULTI_MEMBER_ARCHIVE_SEEDS: usize = 36;
/// Number of generated `.cx` async programs compared across `Pre-Opt MirVm` vs `Post-Opt MirVm`.
const ASYNC_VM_DIFF_SEEDS: usize = 24;
/// Number of generated `.cx` async programs executed across all 4 native + VM tiers via `diff_oracle`.
const ASYNC_FOUR_TIER_NATIVE_SEEDS: usize = 6;
/// Adversarial C11/C23 seed corpus mutated during fault-tolerance fuzzing.
const ADVERSARIAL_C_CORPUS = [_][]const u8{
    "#define LOOP_A LOOP_B\n#define LOOP_B LOOP_A\nint x = LOOP_A;\n",
    "#if (1 + (2 * (3 - \nint unclosed_if;\n",
    "#error \"deliberate fuzz preprocessor trap\"\n",
    "struct BadBitfield { int width_zero : 0; int neg_w : -3; int huge_w : 999; };\n",
    "#pragma pack(push, 3)\nstruct OddPack { char a; int b; };\n#pragma pack(pop)\n",
    "_Static_assert(1 == 2, \"fuzz static assert fail\");\n",
    "#define PASTE(a, b) a ## b\nint PASTE(fuzz_, 99)(const char *p, ...);\n",
    "typedef struct Node Node;\nstruct Node { Node *next; unsigned flags : 5; };\n",
};

// -------------------------------------- INTERNALS --------------------------------------

// ---------------- C11/C23 Header Fuzz Helpers -----------------

/// Synthesizes a valid C11/C23 header exercising macros, enums, `Prune-06` bitfields, and variadics.
fn buildRandomValidCHeader(allocator: std.mem.Allocator, rng: std.Random, seed_idx: usize) ![]u8 {
    var out_buf: std.ArrayList(u8) = .empty;
    errdefer out_buf.deinit(allocator);

    const macro_const = rng.intRangeAtMost(i32, 1, 4096);
    const bit_w1 = rng.intRangeAtMost(u8, 1, 12);
    const bit_w2 = rng.intRangeAtMost(u8, 1, 15);
    const enum_base = rng.intRangeAtMost(i32, 0, 20);
    const array_len = rng.intRangeAtMost(usize, 1, 16);
    const is_packed = rng.boolean();

    var text_buf: [1536]u8 = undefined;
    const header_slice = try std.fmt.bufPrint(
        &text_buf,
        "#pragma once\n" ++
            "#include <stdint.h>\n" ++
            "#include <stdbool.h>\n" ++
            "#define FUZZ_MAGIC_{d} {d}\n" ++
            "#define FUZZ_TAG_{d} \"hdr-ok\"\n" ++
            "enum FuzzState_{d} {{\n" ++
            "    FUZZ_IDLE_{d} = {d},\n" ++
            "    FUZZ_BUSY_{d} = {d}\n" ++
            "}};\n" ++
            "{s}" ++
            "typedef struct FuzzFrame_{d} {{\n" ++
            "    uint32_t seq_no;\n" ++
            "    unsigned int bf_lo : {d};\n" ++
            "    int bf_hi : {d};\n" ++
            "    uint8_t payload[{d}];\n" ++
            "}} FuzzFrame_{d};\n" ++
            "{s}" ++
            "extern int fuzz_globals_{d};\n" ++
            "int32_t fuzz_step_{d}(const FuzzFrame_{d} *frame_ptr, long delta_v);\n" ++
            "int32_t fuzz_var_log_{d}(const char *fmt_str, ...);\n",
        .{
            seed_idx,
            macro_const,
            seed_idx,
            seed_idx,
            seed_idx,
            enum_base,
            seed_idx,
            enum_base + 5,
            if (is_packed) "#pragma pack(push, 1)\n" else "",
            seed_idx,
            bit_w1,
            bit_w2,
            array_len,
            seed_idx,
            if (is_packed) "#pragma pack(pop)\n" else "",
            seed_idx,
            seed_idx,
            seed_idx,
            seed_idx,
        },
    );
    try out_buf.appendSlice(allocator, header_slice);
    return out_buf.toOwnedSlice(allocator);
}

/// Mutates a base C snippet with random byte flips, slices, or synthetic nesting for fault-tolerance fuzzing.
fn buildMutatedAdversarialCHeader(allocator: std.mem.Allocator, rng: std.Random, seed_idx: usize) ![]u8 {
    const base_text = ADVERSARIAL_C_CORPUS[seed_idx % ADVERSARIAL_C_CORPUS.len];
    const mode = rng.uintLessThan(u8, 4);

    if (mode == 0) {
        return allocator.dupe(u8, base_text[0..rng.uintLessThan(usize, base_text.len)]);
    } else if (mode == 1) {
        const mutated = try allocator.dupe(u8, base_text);
        const flip_count = rng.intRangeAtMost(usize, 1, 4);
        var flip_i: usize = 0;
        while (flip_i < flip_count and mutated.len > 0) : (flip_i += 1) {
            const pos = rng.uintLessThan(usize, mutated.len);
            mutated[pos] = rng.intRangeAtMost(u8, 0x20, 0x7E);
        }
        return mutated;
    } else if (mode == 2) {
        const depth = rng.intRangeAtMost(usize, 4, 40);
        var nested: std.ArrayList(u8) = .empty;
        errdefer nested.deinit(allocator);
        try nested.appendSlice(allocator, "int deep_val = ");
        var i: usize = 0;
        while (i < depth) : (i += 1) try nested.append(allocator, '(');
        try nested.appendSlice(allocator, "1");
        i = 0;
        while (i < depth - 1) : (i += 1) try nested.append(allocator, ')');
        try nested.appendSlice(allocator, ";\n");
        return nested.toOwnedSlice(allocator);
    } else {
        const scratch = try allocator.alloc(u8, rng.intRangeAtMost(usize, 8, 96));
        for (scratch) |*byte_slot| {
            byte_slot.* = rng.int(u8);
        }
        return scratch;
    }
}

// ---------------- Archive & .def Fuzz Helpers -----------------

/// Generates a valid `.def` module definition text buffer from `rng`.
fn buildRandomValidModuleDef(allocator: std.mem.Allocator, rng: std.Random, seed_idx: usize) ![]u8 {
    var out_buf: std.ArrayList(u8) = .empty;
    errdefer out_buf.deinit(allocator);

    var line_buf: [256]u8 = undefined;
    try out_buf.appendSlice(
        allocator,
        try std.fmt.bufPrint(&line_buf, "; Generated fuzz module def #{d}\nLIBRARY \"fuzz_mod_{d}.dll\"\nEXPORTS\n", .{
            seed_idx,
            seed_idx,
        }),
    );

    const export_count = rng.intRangeAtMost(usize, 1, 8);
    var exp_idx: usize = 0;
    while (exp_idx < export_count) : (exp_idx += 1) {
        const ord_num = rng.intRangeAtMost(u16, 1, 500);
        const export_line = switch (rng.uintLessThan(u8, 5)) {
            0 => try std.fmt.bufPrint(&line_buf, "    FuzzSym_{d}_{d}\n", .{ seed_idx, exp_idx }),
            1 => try std.fmt.bufPrint(&line_buf, "    FuzzOrd_{d}_{d} @{d}\n", .{ seed_idx, exp_idx, ord_num }),
            2 => try std.fmt.bufPrint(
                &line_buf,
                "    FuzzAlias_{d}_{d} = InternalTarget_{d} @{d} NONAME\n",
                .{ seed_idx, exp_idx, exp_idx, ord_num },
            ),
            3 => try std.fmt.bufPrint(&line_buf, "    FuzzGlobal_{d}_{d} DATA\n", .{ seed_idx, exp_idx }),
            else => try std.fmt.bufPrint(&line_buf, "    FuzzPrivate_{d}_{d} PRIVATE\n", .{ seed_idx, exp_idx }),
        };
        try out_buf.appendSlice(allocator, export_line);
    }
    return out_buf.toOwnedSlice(allocator);
}

// ---------------- Async & Nursery Fuzz Helpers ----------------

/// Generates a deterministic, type-safe `.cx` `async`/`await` + `task_group` program from `rng`.
fn buildRandomAsyncCxProgram(allocator: std.mem.Allocator, rng: std.Random) ![]u8 {
    const base_seed = rng.intRangeAtMost(i32, 3, 30);
    const step_delta_a = rng.intRangeAtMost(i32, 1, 15);
    const step_delta_b = rng.intRangeAtMost(i32, 2, 18);
    const task_val_left = rng.intRangeAtMost(i32, 5, 25);
    const task_val_right = rng.intRangeAtMost(i32, 4, 22);
    const ctx_tok_handle = rng.intRangeAtMost(usize, 1, 31);
    const trace_base = rng.intRangeAtMost(i64, 100, 400);
    const is_canceling_extra = rng.boolean();

    return std.fmt.allocPrint(
        allocator,
        "/# Generated Phase 8 Async Coroutine & Nursery Differential Fuzz Program\n\n" ++
            "pub async fn pinned_accum(slot: &mut i32, first_add: i32, second_add: i32) -> i32 {{\n" ++
            "    slot.* = slot.* +% first_add;\n" ++
            "    cx.async.yield_now().await;\n" ++
            "    slot.* = slot.* +% second_add;\n" ++
            "    return slot.*;\n" ++
            "}}\n\n" ++
            "pub async fn run_async_fuzz_kernel() -> i32 {{\n" ++
            "    var local_state: i32 = {d};\n" ++
            "    let after_pin: i32 = pinned_accum(&mut local_state, {d}, {d}).await;\n" ++
            "    let nursery_sum: i32 = cx.async.task_group(|grp| {{\n" ++
            "        let left_h = grp.spawn(own async {{\n" ++
            "            @drop_trace({d});\n" ++
            "            let tok_item = CancelToken {{ _handle: {d}_usize }};\n" ++
            "            with context.cancel_token = tok_item {{\n" ++
            "                cx.async.yield_now().await;\n" ++
            "                {d} +% (context.cancel_token._handle as i32)\n" ++
            "            }}\n" ++
            "        }});\n" ++
            "        let right_h = grp.spawn_local(own async {{\n" ++
            "            @drop_trace({d});\n" ++
            "            cx.async.yield_now().await;\n" ++
            "            {d}\n" ++
            "        }});\n" ++
            "        let join_l = left_h.join();\n" ++
            "        let join_r = right_h.join();\n" ++
            "        if {s} {{\n" ++
            "            let doomed = grp.spawn(own async {{\n" ++
            "                defer {{ @drop_trace({d}); }}\n" ++
            "                cx.async.yield_now().await;\n" ++
            "                99\n" ++
            "            }});\n" ++
            "            let cancel_fut = doomed.cancel();\n" ++
            "            cx.async.yield_now().await;\n" ++
            "            cancel_fut.await;\n" ++
            "        }}\n" ++
            "        join_l.await +% join_r.await\n" ++
            "    }}).await;\n" ++
            "    return (local_state +% after_pin +% nursery_sum) & 127;\n" ++
            "}}\n\n" ++
            "pub fn main() -> i32 {{\n" ++
            "    return cx.async.block_on(own run_async_fuzz_kernel());\n" ++
            "}}\n",
        .{
            base_seed,
            step_delta_a,
            step_delta_b,
            trace_base,
            ctx_tok_handle,
            task_val_left,
            trace_base + 1,
            task_val_right,
            if (is_canceling_extra) "true" else "false",
            trace_base + 50,
        },
    );
}

/// Evaluates `main` on `db` via `MirVm` under `is_release_mode`, returning `(scalar_i64, owned_drop_trace)`.
fn evalMainOnMirVm(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    file_id: FileId,
    is_release_mode: bool,
) !struct { ret_val: i64, drops: []i64 } {
    const opt_mod = try db.optimizeMirModule(file_id, is_release_mode);
    const main_body = opt_mod.findBodyByName(&db.interner, "main").?;

    var vm_sink = DiagnosticSink.init(allocator);
    defer vm_sink.deinit();
    var vm_engine = try mir_vm.MirVm.init(
        allocator,
        &db.interner,
        &db.type_pool,
        &db.symbol_table,
        &db.rodata_pool,
        null,
        &vm_sink,
        .{
            .compiler_db = db,
            .is_oracle_runtime_mode = true,
        },
    );
    defer vm_engine.deinit();

    for (opt_mod.bodies.items) |*body_ptr| {
        const sym_idx = if (!body_ptr.symbol_index.isNone())
            body_ptr.symbol_index
        else
            db.symbol_table.def_to_symbol.get(body_ptr.def_id.asInt()) orelse .none;
        _ = try vm_engine.registerBody(body_ptr, sym_idx);
    }

    const eval_res = try vm_engine.evalBody(main_body, &.{});
    const scalar_i64: i64 = switch (try vm_engine.slotToComptimeValue(eval_res.type_id, eval_res.repr, eval_res.slot, null)) {
        .int_val => |iv| @bitCast(@as(u64, @truncate(@as(u128, @bitCast(iv))))),
        else => 0,
    };
    return .{ .ret_val = scalar_i64, .drops = try allocator.dupe(i64, vm_engine.asDropTraceSlice()) };
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_fuzz_phase8_c_frontend_translate_c_idempotency_and_adversarial_headers" {
    const allocator = std.testing.allocator;
    var prng = std.Random.Xoroshiro128.init(0xC0DE_8F01_2026_A11C);
    const rng = prng.random();

    // [1] Structured C11/C23 headers across all 11 targets -> `c_translate` + `corex fmt` idempotency:
    var seed_idx: usize = 0;
    while (seed_idx < STRUCTURED_C_HEADER_SEEDS) : (seed_idx += 1) {
        const target_spec = TargetSpec.ALL_CANONICAL_TARGETS[seed_idx % TargetSpec.ALL_CANONICAL_TARGETS.len];
        const c_header = try buildRandomValidCHeader(allocator, rng, seed_idx);
        defer allocator.free(c_header);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var unit = try c_frontend.parseCHeader(
            allocator,
            c_header,
            "fuzz_valid.h",
            .none,
            .{ .target = target_spec },
            &sink,
        );
        defer unit.deinit();
        try std.testing.expect(!sink.hasErrors());

        const translated_cx = try c_translate.translateUnit(allocator, &unit, .{});
        defer allocator.free(translated_cx);

        var fmt_check = try corex.formatSourceWithOptions(
            allocator,
            translated_cx,
            FileId.fromInt(0),
            .{},
        );
        defer fmt_check.deinit(allocator);
        try std.testing.expect(!fmt_check.has_syntax_errors);
        try std.testing.expect(!fmt_check.is_changed);
    }

    // [2] Mutated & adversarial C11/C23 headers -> zero panics, zero leaks, bounded steps/tokens:
    var adv_idx: usize = 0;
    while (adv_idx < ADVERSARIAL_C_HEADER_SEEDS) : (adv_idx += 1) {
        const mutated_c = try buildMutatedAdversarialCHeader(allocator, rng, adv_idx);
        defer allocator.free(mutated_c);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        if (c_frontend.parseCHeader(
            allocator,
            mutated_c,
            "fuzz_adv.h",
            .none,
            .{
                .target = TargetSpec.ALL_CANONICAL_TARGETS[adv_idx % TargetSpec.ALL_CANONICAL_TARGETS.len],
                .max_tokens = 2048,
                .max_macro_steps = 512,
                .max_include_depth = 8,
                .max_parse_depth = 32,
            },
            &sink,
        )) |parsed_unit| {
            var owned_unit = parsed_unit;
            defer owned_unit.deinit();
            allocator.free(try c_translate.translateUnit(allocator, &owned_unit, .{}));
        } else |parse_err| switch (parse_err) {
            error.TranslationFailed => try std.testing.expect(sink.hasErrors()),
            error.OutOfMemory => return error.OutOfMemory,
        }
    }
}

test "test_fuzz_phase8_module_def_and_multi_member_archive_determinism" {
    const allocator = std.testing.allocator;
    var prng = std.Random.Xoroshiro128.init(0xDEFA_8C0F_2026_B22D);
    const rng = prng.random();

    // [1] Valid randomized `.def` -> deterministic COFF Short-Import `.lib` (`amd64` & `arm64`):
    var def_idx: usize = 0;
    while (def_idx < VALID_MODULE_DEF_SEEDS) : (def_idx += 1) {
        const def_text = try buildRandomValidModuleDef(allocator, rng, def_idx);
        defer allocator.free(def_text);

        var parsed = try codegen_link.parseModuleDef(allocator, def_text, "fallback_fuzz");
        defer parsed.deinit(allocator);

        const machine: codegen_link.CoffMachine = if ((def_idx & 1) == 0) .amd64 else .arm64;
        const lib_run_1 = try codegen_link.serializeCoffShortImportLibrary(allocator, parsed, machine);
        defer allocator.free(lib_run_1);
        const lib_run_2 = try codegen_link.serializeCoffShortImportLibrary(allocator, parsed, machine);
        defer allocator.free(lib_run_2);

        try std.testing.expectEqualSlices(u8, lib_run_1, lib_run_2);
        try std.testing.expectEqualStrings(codegen_link.ARCHIVE_MAGIC, lib_run_1[0..8]);
    }

    // [2] Adversarial / corrupted `.def` strings -> zero panics, zero leaks:
    const bad_def_templates = [_][]const u8{
        "LIBRARY \"\"\nEXPORTS\n    Foo\n",
        "EXPORTS\n    = MissingName\n",
        "LIBRARY test.dll\nEXPORTS\n    BadZeroOrd @0\n",
        "LIBRARY test.dll\nEXPORTS\n    OrphanNoname NONAME\n",
        "LIBRARY test.dll\nEXPORTS\n    Sym = \n",
        "LIBRARY test.dll\nEXPORTS\n    Sym UNKNOWN_FLAG\n",
    };
    var bad_i: usize = 0;
    while (bad_i < ADVERSARIAL_MODULE_DEF_SEEDS) : (bad_i += 1) {
        const buf = try allocator.dupe(u8, bad_def_templates[bad_i % bad_def_templates.len]);
        defer allocator.free(buf);
        if (bad_i >= bad_def_templates.len and buf.len > 0) {
            buf[rng.uintLessThan(usize, buf.len)] = rng.int(u8);
        }
        if (codegen_link.parseModuleDef(allocator, buf, "fb.dll")) |ok_def| {
            var mut_def = ok_def;
            mut_def.deinit(allocator);
        } else |def_err| switch (def_err) {
            error.InvalidModuleDef => {},
            else => return def_err,
        }
    }

    // [3] Multi-member `!<arch>\n` serialization determinism across `.gnu`, `.darwin_bsd`, and `.coff`:
    const archive_kinds = [_]codegen_link.ArchiveKind{ .gnu, .darwin_bsd, .coff };
    var ar_seed: usize = 0;
    while (ar_seed < MULTI_MEMBER_ARCHIVE_SEEDS) : (ar_seed += 1) {
        const ar_kind = archive_kinds[ar_seed % archive_kinds.len];
        const member_count = rng.intRangeAtMost(usize, 2, 5);

        var payloads = try allocator.alloc([]u8, member_count);
        var names = try allocator.alloc([]u8, member_count);
        var sym_names = try allocator.alloc([]u8, member_count);
        var sym_lists = try allocator.alloc([1][]const u8, member_count);
        var members = try allocator.alloc(codegen_link.ArchiveMemberInput, member_count);
        var init_n: usize = 0;
        defer {
            for (0..init_n) |i| {
                allocator.free(payloads[i]);
                allocator.free(names[i]);
                allocator.free(sym_names[i]);
            }
            allocator.free(payloads);
            allocator.free(names);
            allocator.free(sym_names);
            allocator.free(sym_lists);
            allocator.free(members);
        }

        while (init_n < member_count) : (init_n += 1) {
            payloads[init_n] = try allocator.alloc(u8, rng.intRangeAtMost(usize, 17, 93));
            for (payloads[init_n]) |*byte_p| byte_p.* = rng.int(u8);

            names[init_n] = if (rng.boolean())
                try std.fmt.allocPrint(allocator, "very_long_archive_member_{d}_{d}.o", .{ ar_seed, init_n })
            else
                try std.fmt.allocPrint(allocator, "m_{d}_{d}.o", .{ ar_seed, init_n });

            sym_names[init_n] = try std.fmt.allocPrint(allocator, "fuzz_ar_sym_{d}_{d}", .{ ar_seed, init_n });
            sym_lists[init_n] = .{sym_names[init_n]};
            members[init_n] = .{
                .name = names[init_n],
                .data = payloads[init_n],
                .explicit_symbols = &sym_lists[init_n],
            };
        }

        const bytes_first = try codegen_link.serializeDeterministicArchiveBytes(allocator, ar_kind, members);
        defer allocator.free(bytes_first);
        const bytes_second = try codegen_link.serializeDeterministicArchiveBytes(allocator, ar_kind, members);
        defer allocator.free(bytes_second);

        try std.testing.expectEqualSlices(u8, bytes_first, bytes_second);
        try std.testing.expectEqualStrings(codegen_link.ARCHIVE_MAGIC, bytes_first[0..8]);
    }
}

test "test_fuzz_phase8_async_yield_task_group_vm_and_four_tier_differential_parity" {
    const allocator = std.testing.allocator;
    var prng = std.Random.Xoroshiro128.init(0xA59C_8F1F_2026_C33E);
    const rng = prng.random();

    var seed_idx: usize = 0;
    while (seed_idx < ASYNC_VM_DIFF_SEEDS) : (seed_idx += 1) {
        const cx_program = try buildRandomAsyncCxProgram(allocator, rng);
        defer allocator.free(cx_program);

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        const file_id = FileId.fromInt(0);
        _ = try db.setInput(file_id, cx_program, .low);

        const dev_outcome = try evalMainOnMirVm(allocator, &db, file_id, false);
        defer allocator.free(dev_outcome.drops);
        const rel_outcome = try evalMainOnMirVm(allocator, &db, file_id, true);
        defer allocator.free(rel_outcome.drops);

        try std.testing.expectEqual(dev_outcome.ret_val, rel_outcome.ret_val);
        try std.testing.expectEqualSlices(i64, dev_outcome.drops, rel_outcome.drops);

        // Sampled full 4-tier native + VM oracle execution (`Pre-Opt MirVm`, `Post-Opt MirVm`, `-ofmt=c`, `LLVM`):
        if (seed_idx < ASYNC_FOUR_TIER_NATIVE_SEEDS) {
            var report = try corex.runFourTierDiffOracle(
                allocator,
                cx_program,
                .{ .io = std.testing.io },
            );
            defer report.deinit(allocator);
            if (!report.is_all_matching) {
                std.debug.print(
                    "Phase 8 async 4-tier fuzz divergence at seed {d}:\n{s}\n",
                    .{ seed_idx, report.rendered_diff_table },
                );
            }
            try std.testing.expect(report.is_all_matching);
            try std.testing.expect(!report.outcomes[0].has_trapped);
            try std.testing.expectEqual(dev_outcome.ret_val, report.outcomes[0].return_scalar_i64);
        }
    }
}

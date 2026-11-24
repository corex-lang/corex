//! Phase 3 Deterministic Formatter Idempotency, Zero Comment Loss & Query Engine Fuzzing Suite (`tests/fuzz/phase3_fmt_fuzz.zig`)
//!
//! Executes structure-aware and mutated `DR-24` `.cx` programs with random comments (`//`, `/|`, `/#`,
//! `///|`, `///#`), arbitrary whitespace/newlines, trailing commas, `@repr` / `@link` horizontal packing,
//! `f"…"` / `"<newline> … "` dedented strings, `if cond => a else b` inline conditionals,
//! `// corex fmt: off` / `on` directives, and `--fix` mode through `corex.fmt_engine`, plus random
//! multi-revision edit sequences through `corex.CompilerDb`.
//!
//! - Asserts 100% second-pass idempotency (`fmt(fmt(x)) == fmt(x)`), 100% comment preservation
//!   (zero comment loss), and syntax error freedom on valid inputs.
//! - Asserts 100% fingerprint parity between an incrementally mutated `CompilerDb` and a fresh
//!   scratch `CompilerDb` across all 10 query stages.

const std = @import("std");
const corex = @import("corex");

const syntax = corex.syntax_arenas;
const fmt_engine = corex.fmt_engine;
const FileId = corex.FileId;
const DefId = corex.DefId;
const Durability = corex.Durability;
const Fingerprint128 = corex.Fingerprint128;
const TokenBuffer = corex.TokenBuffer;
const TriviaKind = syntax.TriviaKind;
const FormatOptions = corex.FormatOptions;
const CompilerDb = corex.CompilerDb;

// --------------------------------------- CONSTS ----------------------------------------

/// Number of generated/mutated `.cx` programs verified in `test_fuzz_fmt_idempotency_and_comment_preservation`.
const FMT_FUZZ_ITERATIONS: usize = 500;
/// Number of incremental `CompilerDb` mutation steps verified in `test_fuzz_query_db_early_cutoff_and_firewall_invariants`.
const QUERY_DB_FUZZ_ITERATIONS: usize = 300;

/// Syntactic item and statement building blocks for Phase 3 formatter fuzzing.
const FMT_SEED_ITEMS = [_][]const u8{
    "use cx.io.{Write, self, Read, BufReader as Br};\n",
    "use cx.mem.{size_of, align_of,};\n",
    "const MAX_LIMIT: usize = 0x1000u64;\n",
    "const MIN_LIMIT: usize = 16_usize;\n",
    "pub(pkg) type Port = u16;\n",
    "pub struct Point[T = i32] { pub(super) x: T = 0, pub y: T, }\n",
    "pub enum Status { Idle, Active(u32), Failed { code: i32, }, }\n",
    "pub enum WireOrder: u8 { Relaxed = 0, SeqCst = 5, }\n",
    "pub bit_field PacketBits: u16 { pub ready: bool | 1, pub tag: u16 | 15, }\n",
    "pub trait Measurable { fn measure(&self) -> i32; }\n",
    "unsafe impl Send for Point[i32] {}\n",
    "impl Point[i32] { pub subscript(idx: usize, /) -> i32 { let { yield self.x; } inout { yield &mut self.x; } } }\n",
    "@no_panic @must_use @no_alloc\npub fn scale_val(val: i32, /, *, factor: i32 = 2) -> i32 = val * factor;\n",
    "@derive(Copy, Equatable, Debug)\n@repr(zero_pad: true, align: .CacheLine, packed: 4, C)\n@cfg(target.ptr_width == 64)\n" ++
        "pub struct DmaSlot { /| Physical address.\n pub dma_addr: u64, }\n",
    "@link(section: \".text.hot\", name: \"cx_fast_hook\")\nextern \"C\" fn fast_hook(code: i32) -> i32;\n",
    "pub fn normalize_sigs[Data: str | &[u8]](\n" ++
        "    opt_in: Option[Data], out_slot: &out i32, owned_pt: own Point[i32],\n" ++
        ") -> Result[i32, IoError] {\n" ++
        "    out_slot.* = owned_pt.x + (b'A' as i32) + (b\"ok\".len() as i32);\n" ++
        "    let copy_pt = Point { y: 9, ..owned_pt };\n" ++
        "    let moved_pt = Point { x: 1, ..own copy_pt };\n" ++
        "    var left_v: i32 = moved_pt.x;\n" ++
        "    var right_v: i32 = out_slot.*;\n" ++
        "    (left_v, right_v) = (right_v, left_v);\n" ++
        "    let raw_p: *i32 = &raw left_v;\n" ++
        "    return .Ok(unsafe { raw_p.* });\n" ++
        "}\n",
    "pub fn multiline_interp_showcase(flag: bool, port: u16, mask: u32) -> str {\n" ++
        "    if flag {\n" ++
        "        let nested_banner = f\"\n" ++
        "            ╭─ Wire {{v1.0}} ────────────────╮\n" ++
        "            │ {port=} mask={mask:#010x} {if flag => \"inner\" else f\"\n" ++
        "                deep {port}\n" ++
        "                \"}\n" ++
        "            ╰────────────────────────────────╯\n" ++
        "            \";\n" ++
        "        let guarded_json = f#\"\n" ++
        "            {\"port\": {port:04}, \"raw\": \"{r#\"ok\"#}\"}\n" ++
        "            \"#;\n" ++
        "        _ = guarded_json;\n" ++
        "        return nested_banner;\n" ++
        "    }\n" ++
        "    let raw_dedent = r#\"\n" ++
        "        raw \"quoted\" {brace}\n" ++
        "        \"#;\n" ++
        "    let byte_dedent = b\"\n" ++
        "        HTTP/1.1 200 OK\n" ++
        "        \";\n" ++
        "    _ = (raw_dedent, byte_dedent);\n" ++
        "    return \"\n" ++
        "        plain {literal} line one\n" ++
        "          indented line two\n" ++
        "        \";\n" ++
        "}\n",
    "pub fn inline_if_and_braced_normalization(level: i32, compact: bool) -> i32 {\n" ++
        "    let pad = if compact => 8_i32 else 16_i32;\n" ++
        "    let normalized = if compact { 1_i32 } else { 2_i32 };\n" ++
        "    let tier = if level > 90 => 3_i32\n" ++
        "        else if level > 50 => 2_i32\n" ++
        "        else 1_i32;\n" ++
        "    return pad + normalized + tier;\n" ++
        "}\n",
    "pub fn compute_pipeline(val: i32, flag: bool) -> i32 {\n" ++
        "    ;\n" ++
        "    let neg = - -val;\n" ++
        "    let inv = not flag;\n" ++
        "    let comp = ~0xFF_i32;\n" ++
        "    let grid = [ 1, 20, 300, 4, 50, 600, 7, 80, 900, 10 ];\n" ++
        "    let tail = grid[..$-2];\n" ++
        "    let piped = val |> step_one() |> step_two();\n" ++
        "    let chained = tail.iter().count_all() + comp;\n" ++
        "    if (rem := piped) > 0 { while (neg < rem) { break; }; };\n" ++
        "    with context.allocator = &mut scratch { _ = opt_v orelse 0; }\n" ++
        "    return fsm: match (piped) { 0 => continue :fsm 1, 1 => chained, _ => neg, };\n" ++
        "}\n",
    "test \"formatter prose test\" (raw: &[u8]) -> unit { _ = raw.len(); }\n",
    "bench \"formatter bench\" (bencher: &mut Bencher) -> unit { _ = bencher; }\n",
    "// corex fmt: off\nconst   RAW_UNTOUCHED:   i32  =   777;\n// corex fmt: on\n",
    "@fmt_off\nconst   ATTR_UNTOUCHED:  i32  =   888;\n",
    "const unfixed_const: i32 = 42\nstruct bad_struct { FieldOne: i32 }\nfn BadFunc( ArgVal: i32 ) -> i32 { return ArgVal }\n",
};

/// Comment snippets injected at valid positions between seed items.
const RANDOM_COMMENT_SNIPPETS = [_][]const u8{
    "/# module doc comment snippet\n\n",
    "/| item doc comment snippet\n",
    "// standalone line comment snippet:\n",
    "///| commented-out item docstring snippet\n",
    "///# commented-out module docstring snippet\n",
    "pub fn empty_holder(\n    // comment in params:\n) {\n    // comment in empty body.\n}\n",
};

/// Function body variants for `CompilerDb` incremental firewall fuzzing.
const QUERY_BODY_VARIANTS = [_][]const u8{
    "    let step = input_val + 1;\n    return step;\n",
    "    // Comment-only change inside body\n    let step = input_val + 1;\n\n    return step;\n",
    "    let step = (input_val * 3) + 42;\n    return step - 7;\n",
    "    let first = input_val + 10;\n    let second = first * 2;\n\n\n\n    return second;\n",
    "    return match input_val { 0 => 100, _ => input_val };\n",
};

/// Function signature variants for `CompilerDb` incremental firewall fuzzing.
const QUERY_SIG_VARIANTS = [_][]const u8{
    "pub fn item_fn_",
    "fn item_fn_",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Returns whether `kind` is a comment or shebang trivia piece.
inline fn isCommentTrivia(kind: TriviaKind) bool {
    return switch (kind) {
        .line_comment,
        .doc_comment,
        .module_doc_comment,
        .shebang,
        => true,
        else => false,
    };
}

/// Asserts that every comment trivia lexeme in `source` appears intact in `formatted_text`.
fn verifyZeroCommentLoss(
    allocator: std.mem.Allocator,
    source: []const u8,
    formatted_text: []const u8,
) !void {
    var token_buf = TokenBuffer.init(allocator);
    defer token_buf.deinit();

    try corex.tokenize(source, FileId.fromInt(0), &token_buf, null, null);
    for (token_buf.trivia.items) |piece| {
        if (!isCommentTrivia(piece.kind)) continue;
        const start: usize = piece.byte_offset;
        const end: usize = @min(source.len, start + piece.byte_len);
        const trimmed = std.mem.trim(u8, source[start..end], " \t\r\n");
        if (trimmed.len == 0) continue;
        if ((piece.kind == .doc_comment or piece.kind == .module_doc_comment) and trimmed.len > 2) {
            // `corex fmt` normalizes `/|Text` -> `/| Text`, and `fmt --fix` repairs misplaced/dangling
            // `/#` or `/|` prefixes to `//` (`ADR-24A` §4.1) while preserving the comment body:
            try std.testing.expect(
                std.mem.indexOf(u8, formatted_text, std.mem.trimStart(u8, trimmed[2..], " ")) != null,
            );
        } else {
            try std.testing.expect(std.mem.indexOf(u8, formatted_text, trimmed) != null);
        }
    }
}

/// Assembles a multi-item `.cx` module from 4 function slots and optional header trivia.
fn buildMultiItemModule(
    allocator: std.mem.Allocator,
    has_extra_header_comments: bool,
    sig_choices: [4]usize,
    body_choices: [4]usize,
) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);

    if (has_extra_header_comments) {
        try builder.appendSlice(allocator, "/# Fuzz header doc comment\n\n// Extra banner comment:\n\n");
    }
    try builder.appendSlice(allocator, "pub const MODULE_BASE: i32 = (100);\n\n");

    var fn_idx: usize = 0;
    while (fn_idx < 4) : (fn_idx += 1) {
        var header_buf: [128]u8 = undefined;
        const header_slice = try std.fmt.bufPrint(
            &header_buf,
            "{s}{d}(input_val: i32) -> i32 {{\n",
            .{ QUERY_SIG_VARIANTS[sig_choices[fn_idx]], fn_idx },
        );
        try builder.appendSlice(allocator, header_slice);
        try builder.appendSlice(allocator, QUERY_BODY_VARIANTS[body_choices[fn_idx]]);
        try builder.appendSlice(allocator, "}\n\n");
    }
    return builder.toOwnedSlice(allocator);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_fuzz_fmt_idempotency_and_comment_preservation" {
    var prng = std.Random.DefaultPrng.init(0xF003_C0DE_2026_0003);
    const random = prng.random();

    var source_buf: [4096]u8 = undefined;
    var iter_idx: usize = 0;
    while (iter_idx < FMT_FUZZ_ITERATIONS) : (iter_idx += 1) {
        var byte_len: usize = 0;
        const frag_count = random.intRangeAtMost(usize, 1, 6);
        var frag_i: usize = 0;
        while (frag_i < frag_count) : (frag_i += 1) {
            const item = FMT_SEED_ITEMS[random.uintLessThan(usize, FMT_SEED_ITEMS.len)];
            if (random.boolean()) {
                const raw_cmt_idx = random.uintLessThan(usize, RANDOM_COMMENT_SNIPPETS.len);
                const is_doc_attachable = !std.mem.startsWith(u8, item, "use ") and
                    !std.mem.startsWith(u8, item, "//");
                const cmt_idx: usize = switch (raw_cmt_idx) {
                    0 => if (frag_i == 0 and byte_len == 0) 0 else 2,
                    1 => if (is_doc_attachable) 1 else 2,
                    else => raw_cmt_idx,
                };
                const cmt = RANDOM_COMMENT_SNIPPETS[cmt_idx];
                if (byte_len + cmt.len + item.len <= source_buf.len) {
                    @memcpy(source_buf[byte_len .. byte_len + cmt.len], cmt);
                    byte_len += cmt.len;
                }
            }
            if (byte_len + item.len <= source_buf.len) {
                @memcpy(source_buf[byte_len .. byte_len + item.len], item);
                byte_len += item.len;
            }
            if (random.boolean() and byte_len + 2 <= source_buf.len) {
                source_buf[byte_len] = '\n';
                source_buf[byte_len + 1] = '\n';
                byte_len += 2;
            }
        }

        // Periodically apply random byte mutations on 20% of iterations to stress fault tolerance:
        if (iter_idx % 5 == 0 and byte_len > 0) {
            const mut_pos = random.uintLessThan(usize, byte_len);
            source_buf[mut_pos] = switch (random.uintLessThan(u8, 6)) {
                0 => ';',
                1 => ' ',
                2 => '\n',
                3 => '(',
                4 => '}',
                else => source_buf[mut_pos],
            };
        }

        const source_slice = source_buf[0..byte_len];
        const options = FormatOptions{
            .is_fix_mode = (iter_idx % 2 == 1),
            .max_line_width = if (iter_idx % 7 == 0) 60 else fmt_engine.MAX_LINE_WIDTH,
        };

        var pass1 = try fmt_engine.formatSourceWithOptions(
            std.testing.allocator,
            source_slice,
            FileId.fromInt(@intCast(iter_idx & 0xFF)),
            options,
        );
        defer pass1.deinit(std.testing.allocator);

        var pass2 = try fmt_engine.formatSourceWithOptions(
            std.testing.allocator,
            pass1.formatted_text,
            FileId.fromInt(@intCast(iter_idx & 0xFF)),
            options,
        );
        defer pass2.deinit(std.testing.allocator);

        // [1] 100% Idempotency (`fmt(fmt(x)) == fmt(x)`):
        try std.testing.expectEqualStrings(pass1.formatted_text, pass2.formatted_text);
        try std.testing.expect(!pass2.is_changed);

        // [2] 100% Zero Comment Loss:
        try verifyZeroCommentLoss(std.testing.allocator, source_slice, pass1.formatted_text);

        // [3] If `source_slice` had zero syntax errors, `pass1.formatted_text` also has zero syntax errors:
        if (!pass1.has_syntax_errors) {
            try std.testing.expect(!pass2.has_syntax_errors);
        }
    }
}

test "test_fuzz_query_db_early_cutoff_and_firewall_invariants" {
    var prng = std.Random.DefaultPrng.init(0xDB03_FA5E_2026_1109);
    const random = prng.random();

    var inc_db = try CompilerDb.init(std.testing.allocator);
    defer inc_db.deinit();

    const file_a = FileId.fromInt(1);
    const file_b = FileId.fromInt(2);

    var sig_a = [4]usize{ 0, 0, 0, 0 };
    var body_a = [4]usize{ 0, 1, 2, 3 };
    var dur_a: Durability = .low;
    var has_header_a = false;

    const sig_b = [4]usize{ 0, 1, 0, 1 };
    var body_b = [4]usize{ 1, 2, 3, 4 };
    var dur_b: Durability = .high;
    var has_header_b = false;

    const init_src_a = try buildMultiItemModule(std.testing.allocator, has_header_a, sig_a, body_a);
    defer std.testing.allocator.free(init_src_a);
    const init_src_b = try buildMultiItemModule(std.testing.allocator, has_header_b, sig_b, body_b);
    defer std.testing.allocator.free(init_src_b);

    _ = try inc_db.setInput(file_a, init_src_a, dur_a);
    _ = try inc_db.setInput(file_b, init_src_b, dur_b);

    var iter_idx: usize = 0;
    while (iter_idx < QUERY_DB_FUZZ_ITERATIONS) : (iter_idx += 1) {
        if (random.uintLessThan(u8, 4) != 0) {
            switch (random.uintLessThan(u8, 4)) {
                0 => has_header_a = !has_header_a,
                1 => {
                    const slot = random.uintLessThan(usize, 4);
                    body_a[slot] = random.uintLessThan(usize, QUERY_BODY_VARIANTS.len);
                },
                2 => {
                    const slot = random.uintLessThan(usize, 4);
                    sig_a[slot] = random.uintLessThan(usize, QUERY_SIG_VARIANTS.len);
                },
                else => {
                    dur_a = switch (random.uintLessThan(u8, 3)) {
                        0 => .low,
                        1 => .medium,
                        else => .high,
                    };
                },
            }
        } else {
            switch (random.uintLessThan(u8, 3)) {
                0 => has_header_b = !has_header_b,
                1 => {
                    const slot = random.uintLessThan(usize, 4);
                    body_b[slot] = random.uintLessThan(usize, QUERY_BODY_VARIANTS.len);
                },
                else => {
                    dur_b = if (dur_b == .high) .medium else .high;
                },
            }
        }

        const next_src_a = try buildMultiItemModule(std.testing.allocator, has_header_a, sig_a, body_a);
        defer std.testing.allocator.free(next_src_a);
        const next_src_b = try buildMultiItemModule(std.testing.allocator, has_header_b, sig_b, body_b);
        defer std.testing.allocator.free(next_src_b);

        _ = try inc_db.setInput(file_a, next_src_a, dur_a);
        _ = try inc_db.setInput(file_b, next_src_b, dur_b);

        // Compare incremental `inc_db` against a fresh `scratch_db` every 10 steps:
        if (iter_idx % 10 == 9) {
            var scratch_db = try CompilerDb.init(std.testing.allocator);
            defer scratch_db.deinit();

            _ = try scratch_db.setInput(file_a, next_src_a, dur_a);
            _ = try scratch_db.setInput(file_b, next_src_b, dur_b);

            for ([_]FileId{ file_a, file_b }) |target_file| {
                const inc_lower = try inc_db.lowerAst(target_file);
                const scr_lower = try scratch_db.lowerAst(target_file);
                try std.testing.expect(Fingerprint128.eql(inc_lower.ast_fingerprint, scr_lower.ast_fingerprint));

                const inc_tree = try inc_db.extractItemTree(target_file);
                const scr_tree = try scratch_db.extractItemTree(target_file);
                try std.testing.expect(Fingerprint128.eql(inc_tree.tree_fingerprint, scr_tree.tree_fingerprint));
                try std.testing.expect(
                    Fingerprint128.eql(inc_tree.combined_fingerprint, scr_tree.combined_fingerprint),
                );

                const inc_sigs = try inc_db.resolveSignatures(target_file);
                const scr_sigs = try scratch_db.resolveSignatures(target_file);
                try std.testing.expect(
                    Fingerprint128.eql(inc_sigs.signatures_fingerprint, scr_sigs.signatures_fingerprint),
                );

                var item_ordinal: u12 = 0;
                while (item_ordinal < 5) : (item_ordinal += 1) {
                    const def_id = DefId.init(target_file, item_ordinal);
                    const inc_sig_proj = try inc_db.getItemTreeSigProj(def_id);
                    const scr_sig_proj = try scratch_db.getItemTreeSigProj(def_id);
                    try std.testing.expect(Fingerprint128.eql(inc_sig_proj, scr_sig_proj));

                    const inc_body_proj = try inc_db.getBodyAstProj(def_id);
                    const scr_body_proj = try scratch_db.getBodyAstProj(def_id);
                    try std.testing.expect(
                        Fingerprint128.eql(inc_body_proj.body_fingerprint, scr_body_proj.body_fingerprint),
                    );

                    const inc_typed = try inc_db.typecheckBody(def_id);
                    const scr_typed = try scratch_db.typecheckBody(def_id);
                    try std.testing.expect(
                        Fingerprint128.eql(inc_typed.typed_fingerprint, scr_typed.typed_fingerprint),
                    );

                    const inc_sast = try inc_db.verifySastMir(def_id);
                    const scr_sast = try scratch_db.verifySastMir(def_id);
                    try std.testing.expect(
                        Fingerprint128.eql(inc_sast.sast_fingerprint, scr_sast.sast_fingerprint),
                    );
                }
            }
        } else {
            // Query a random subset of definitions to exercise demand-driven partial evaluation:
            const target_file = if (random.boolean()) file_a else file_b;
            const target_def = DefId.init(target_file, random.uintLessThan(u12, 5));
            _ = try inc_db.verifySastMir(target_def);
        }
    }

    try std.testing.expect(inc_db.telemetry.early_cutoff_hits > 0);
    try std.testing.expect(inc_db.telemetry.green_hits > 0);
}

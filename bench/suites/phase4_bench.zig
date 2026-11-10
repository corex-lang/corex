//! Phase 4 Name Resolution, `InternPool` & Bidirectional Type Checker Benchmark Suite (`bench/suites/phase4_bench.zig`)
//!
//! Benchmarks `symbol_resolver.resolveModuleSignatures` (top-level item collection, `mod` / `use`
//! import resolution, and scope construction) on a pre-parsed 64 KiB (`2,048` LOC) `.cx` module,
//! `type_system.typecheckModule` (14-byte SoA `InternPool` interning, Constrained Type Group
//! unification, `Result[T, E]` `?` propagation, and Maranget `match` exhaustiveness) on 64 KiB,
//! and incremental `CompilerDb.typecheckBody` on a single-function body edit across 128 functions.
//!
//! Executed via `zig build bench` or `zig build bench-phase4`, enforcing 5 warmup iterations and
//! 30 timed iterations per workload and rendering the canonical monochrome Unicode report table.

const std = @import("std");
const corex = @import("corex");

const symbol_resolver = corex.symbol_resolver;
const type_system = corex.type_system;
const FileId = corex.FileId;
const DefId = corex.DefId;
const StringInterner = corex.StringInterner;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const AstArena = corex.AstArena;
const CompilerDb = corex.CompilerDb;
const StyleConfig = corex.StyleConfig;
const SymbolTable = symbol_resolver.SymbolTable;
const InternPool = type_system.InternPool;
const BenchCase = corex.bench_harness.BenchCase;

// ---------------------------------------- TYPES ----------------------------------------

/// Pre-tokenized and pre-parsed 64 KiB `.cx` syntax state for isolated Phase 4 benchmarks.
const PreParsedTypecheckState = struct {
    /// Shared string interner.
    interner: StringInterner,
    /// Shared type intern pool.
    pool: InternPool,
    /// Shared symbol table and scope arena.
    sym_table: SymbolTable,
    /// Pre-populated token and trivia buffer.
    token_buf: TokenBuffer,
    /// Pre-populated lossless CST arena.
    cst_arena: LosslessCstArena,
    /// Pre-populated AST arena.
    ast_arena: AstArena,

    /// Releases all backing buffers owned by `self`.
    fn deinit(self: *PreParsedTypecheckState) void {
        self.ast_arena.deinit();
        self.cst_arena.deinit();
        self.token_buf.deinit();
        self.sym_table.deinit();
        self.pool.deinit();
        self.interner.deinit();
    }
};

/// Persistent `CompilerDb` benchmark state toggling between two 64 KiB source revisions.
const IncrementalTypecheckState = struct {
    /// Persistent incremental query database.
    db: CompilerDb,
    /// `true` when the edited buffer variant is currently active in `db`.
    is_edited_active: bool,

    /// Releases `self.db`.
    fn deinit(self: *IncrementalTypecheckState) void {
        self.db.deinit();
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Representative 16-line `.cx` function block repeated 128 times to form a 64 KiB (`2,048` LOC) module.
const SYNTHETIC_TYPED_BLOCK_16_LOC =
    "/// Computes bounded frame score with Constrained Type Groups, `Result` `?`, and `match`.\n" ++
    "pub fn evaluate_frame_metric(seed_val: u64, flag_byte: u8) -> Result[u64, u32] {\n" ++
    "    let base_offset: u64 = 1_000_000;\n" ++
    "    let combined: u64 = seed_val + base_offset;\n" ++
    "    let tier_bonus: u64 = match flag_byte {\n" ++
    "        0..=63 => 10,\n" ++
    "        64..=127 => 20,\n" ++
    "        128..=255 => 40,\n" ++
    "    };\n" ++
    "    let opt_extra: u64? = .Some(tier_bonus);\n" ++
    "    let unwrapped = opt_extra catch 0;\n" ++
    "    let total_val: u64 = combined + unwrapped;\n" ++
    "    if total_val == 0 {\n" ++
    "        return .Err(1);\n" ++
    "    }\n" ++
    "    return .Ok(total_val);\n" ++
    "}\n";

/// Complete 64 KiB (`2,048` LOC, `128` functions) synthetic `.cx` module with unique function names.
const SYNTHETIC_TYPED_MODULE_64K: [SYNTHETIC_TYPED_BLOCK_16_LOC.len * 128]u8 = blk: {
    @setEvalBranchQuota(500_000);
    var buf: [SYNTHETIC_TYPED_BLOCK_16_LOC.len * 128]u8 = undefined;
    var i: usize = 0;
    while (i < 128) : (i += 1) {
        const start = i * SYNTHETIC_TYPED_BLOCK_16_LOC.len;
        @memcpy(buf[start .. start + SYNTHETIC_TYPED_BLOCK_16_LOC.len], SYNTHETIC_TYPED_BLOCK_16_LOC);
        // Stamp a unique 3-character suffix into `evaluate_frame_metric` -> `evaluate_frame_metXXX`:
        const name_end = start +
            ("/// Computes bounded frame score with Constrained Type Groups, `Result` `?`, and `match`.\n" ++
                "pub fn evaluate_frame_met").len;
        buf[name_end + 0] = '0' + @as(u8, @intCast((i / 100) % 10));
        buf[name_end + 1] = '0' + @as(u8, @intCast((i / 10) % 10));
        buf[name_end + 2] = '0' + @as(u8, @intCast(i % 10));
    }
    break :blk buf;
};

/// Byte offset of `1_000_000` inside function #64 of `SYNTHETIC_TYPED_MODULE_64K`.
const FN_64_LITERAL_OFFSET: usize = 64 * SYNTHETIC_TYPED_BLOCK_16_LOC.len +
    ("/// Computes bounded frame score with Constrained Type Groups, `Result` `?`, and `match`.\n" ++
        "pub fn evaluate_frame_metric(seed_val: u64, flag_byte: u8) -> Result[u64, u32] {\n" ++
        "    let base_offset: u64 = ").len;

/// Body-edited 64 KiB module where function #64's `1_000_000` literal is modified to `2_000_000`.
const SYNTHETIC_TYPED_MODULE_64K_EDITED: [SYNTHETIC_TYPED_MODULE_64K.len]u8 = blk: {
    @setEvalBranchQuota(500_000);
    var buf = SYNTHETIC_TYPED_MODULE_64K;
    buf[FN_64_LITERAL_OFFSET] = '2';
    break :blk buf;
};

// -------------------------------------- INTERNALS --------------------------------------

/// Cached pre-parsed syntax state for `benchResolveSignatures64k` and `benchTypecheckModule64k`.
var shared_pre_parsed_tc: ?PreParsedTypecheckState = null;
/// Cached `CompilerDb` state for `benchIncrementalTypecheckSingleFn64k`.
var shared_inc_tc_state: ?IncrementalTypecheckState = null;

/// Returns the pre-tokenized and pre-parsed 64 KiB syntax state, initializing once on first use.
fn getOrInitPreParsedState(allocator: std.mem.Allocator) !*PreParsedTypecheckState {
    if (shared_pre_parsed_tc == null) {
        var interner = try StringInterner.init(allocator);
        errdefer interner.deinit();
        var pool = try InternPool.init(allocator);
        errdefer pool.deinit();
        var sym_table = try SymbolTable.init(allocator, &interner);
        errdefer sym_table.deinit();
        var state = PreParsedTypecheckState{
            .interner = interner,
            .pool = pool,
            .sym_table = sym_table,
            .token_buf = TokenBuffer.init(allocator),
            .cst_arena = LosslessCstArena.init(allocator),
            .ast_arena = AstArena.init(allocator),
        };
        _ = try corex.parseSource(
            &SYNTHETIC_TYPED_MODULE_64K,
            FileId.fromInt(0),
            &state.token_buf,
            &state.cst_arena,
            &state.ast_arena,
            null,
            &state.interner,
        );
        shared_pre_parsed_tc = state;
    }
    return &shared_pre_parsed_tc.?;
}

/// Benchmarks `symbol_resolver` item collection & import resolution on a pre-parsed 64 KiB (`2,048` LOC) `.cx` module.
fn benchResolveSignatures64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitPreParsedState(allocator);
    try state.sym_table.reset(&state.interner);
    const root_scope = try symbol_resolver.collectFileModuleItems(
        &state.sym_table,
        &state.interner,
        FileId.fromInt(0),
        &SYNTHETIC_TYPED_MODULE_64K,
        &state.token_buf,
        &state.cst_arena,
        &state.ast_arena,
        null,
    );
    try symbol_resolver.resolveFileUseImports(
        &state.sym_table,
        &state.interner,
        FileId.fromInt(0),
        &SYNTHETIC_TYPED_MODULE_64K,
        &state.token_buf,
        &state.cst_arena,
        null,
    );
    std.mem.doNotOptimizeAway(root_scope.asInt());
    std.mem.doNotOptimizeAway(state.sym_table.countSymbols());
    return SYNTHETIC_TYPED_MODULE_64K.len;
}

/// Benchmarks full signature resolution + body type-checking on a pre-parsed 64 KiB (`2,048` LOC) `.cx` module.
fn benchTypecheckModule64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitPreParsedState(allocator);
    try state.sym_table.reset(&state.interner);
    try state.pool.resetDynamic();
    _ = try symbol_resolver.collectFileModuleItems(
        &state.sym_table,
        &state.interner,
        FileId.fromInt(0),
        &SYNTHETIC_TYPED_MODULE_64K,
        &state.token_buf,
        &state.cst_arena,
        &state.ast_arena,
        null,
    );
    try symbol_resolver.resolveFileUseImports(
        &state.sym_table,
        &state.interner,
        FileId.fromInt(0),
        &SYNTHETIC_TYPED_MODULE_64K,
        &state.token_buf,
        &state.cst_arena,
        null,
    );
    var checker = try type_system.TypeChecker.init(
        allocator,
        &state.interner,
        &state.pool,
        &state.sym_table,
        FileId.fromInt(0),
        &SYNTHETIC_TYPED_MODULE_64K,
        &state.token_buf,
        &state.cst_arena,
        &state.ast_arena,
        null,
    );
    defer checker.deinit();
    try checker.resolveModuleSignatures();
    try checker.checkFileBodies();
    std.mem.doNotOptimizeAway(state.pool.countTypes());
    return SYNTHETIC_TYPED_MODULE_64K.len;
}

/// Benchmarks incremental `CompilerDb.typecheckBody` on a 1-function edit in a 128-function (`64` KiB) module.
fn benchIncrementalTypecheckSingleFn64k(allocator: std.mem.Allocator) !usize {
    if (shared_inc_tc_state == null) {
        var db = try CompilerDb.init(allocator);
        errdefer db.deinit();
        const file_id = FileId.fromInt(0);
        _ = try db.setInput(file_id, &SYNTHETIC_TYPED_MODULE_64K, .low);
        const tree = try db.extractItemTree(file_id);
        for (tree.entries) |entry| {
            _ = try db.typecheckBody(entry.def_id);
        }
        shared_inc_tc_state = .{
            .db = db,
            .is_edited_active = false,
        };
    }
    const state = &shared_inc_tc_state.?;
    const next_src: []const u8 = if (state.is_edited_active)
        &SYNTHETIC_TYPED_MODULE_64K
    else
        &SYNTHETIC_TYPED_MODULE_64K_EDITED;
    state.is_edited_active = !state.is_edited_active;

    const file_id = FileId.fromInt(0);
    _ = try state.db.setInput(file_id, next_src, .low);
    const edited_body = try state.db.typecheckBody(DefId.init(file_id, 64));
    const sibling_body = try state.db.typecheckBody(DefId.init(file_id, 65));
    std.mem.doNotOptimizeAway(edited_body.typed_fingerprint.low ^ sibling_body.typed_fingerprint.low);
    return SYNTHETIC_TYPED_MODULE_64K.len;
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 4 name resolution & type checker benchmark suite and prints the monochrome Unicode table.
pub fn main(init: std.process.Init) !void {
    defer {
        if (shared_pre_parsed_tc) |*tc_ref| {
            tc_ref.deinit();
            shared_pre_parsed_tc = null;
        }
        if (shared_inc_tc_state) |*inc_ref| {
            inc_ref.deinit();
            shared_inc_tc_state = null;
        }
    }

    const results = try corex.bench_harness.runSuite(
        init.gpa,
        init.io,
        &[_]BenchCase{
            .{
                .name = "resolveModuleSignatures (64 KiB / 2,048 LOC .cx)",
                .run_fn = benchResolveSignatures64k,
            },
            .{
                .name = "typecheckModule (64 KiB / 2,048 LOC .cx)",
                .run_fn = benchTypecheckModule64k,
            },
            .{
                .name = "CompilerDb typecheckBody (1-fn edit / 128 fns)",
                .run_fn = benchIncrementalTypecheckSingleFn64k,
            },
        },
    );
    defer init.gpa.free(results);

    var stdout_buf: [4096]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writerStreaming(init.io, &stdout_buf);
    const style_config: StyleConfig = .{
        .is_color_enabled = corex.style.isColorEnabled(.auto, init.io, std.Io.File.stdout(), init.environ_map),
    };

    try style_config.writeStatusHeader(
        &stdout_writer.interface,
        .success,
        corex.Glyphs.POINTER_SOLID,
        "corex bench",
        "Phase 4 Name Resolution, InternPool & Type Checker Benchmark Suite (5 warmup, 30 measured iterations)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, results);
    try stdout_writer.interface.flush();
}

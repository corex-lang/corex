//! CoreX Stage-0 Tier A Backend (`-ofmt=c` Deterministic ISO C99 Emitter & `zig cc` Driver)
//!
//! Lowers canonical Block-Argument SSA `MirBody` modules (`DR-01`, `DR-20` `Prune-01`–`Prune-02`,
//! `D-01`, `D-03`, `D-07A`, `D-10A`, and `phase7_spec.md` §3–§4) into byte-for-byte deterministic,
//! UB-free ISO C99 source text and compiles `.o`/`.obj`/`.wasm` objects or executables via `zig cc`.
//!
//! Key Invariants:
//! - Zero hashmap iteration nondeterminism: composite `TypeId` typedefs are topologically ordered
//!   with ties broken by `TypeId.toU32()`, struct/tuple fields emit in `TypeLayoutResolver`
//!   physical offset order (`_f<decl_ordinal>`) interleaved with explicit `uint8_t _pad_<k>[N]`
//!   padding arrays, and every composite type carries a compile-time `sizeof` static assertion.
//! - Zero C99 undefined behavior: wrapping arithmetic runs in exact-width unsigned domains,
//!   checked `+`/`-`/`*` use `__builtin_*_overflow` with portable widening fallbacks, `/` and `%`
//!   guard `rhs == 0` and `MIN / -1` prior to evaluation, shifts bounds-check/mask counts,
//!   float-to-int casts trap on `NaN`/`Inf`/out-of-range values, and `@bit_cast` uses `memcpy`.
//! - Cycle-safe parallel block-argument moves stage outgoing values into scoped `_phi_<k>` locals
//!   inside every branch/switch arm.

const std = @import("std");
const builtin = @import("builtin");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const diagnostic = @import("diag/diagnostic.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const query_db = @import("query_db.zig");
const hir = @import("hir.zig");
const mir = @import("mir.zig");
const codegen_abi = @import("codegen_abi.zig");
const codegen_link = @import("codegen_link.zig");
const codegen_dev_seam = @import("codegen_dev_seam.zig");
const mir_async = @import("mir_async.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const MirBlockId = mem_foundation.MirBlockId;
const MirValueId = mem_foundation.MirValueId;
const TypeId = mem_foundation.TypeId;
const DefId = query_db.DefId;

const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolTable = symbol_resolver.SymbolTable;
const InternPool = type_system.InternPool;
const TypeTag = type_system.TypeTag;
const ParamMode = type_system.ParamMode;
const TargetLayout = type_system.TargetLayout;
const BitSpec = hir.BitSpec;

const PlaceId = mir.PlaceId;
const ProjKind = mir.ProjKind;
const MirOp = mir.MirOp;
const BinOpKind = mir.BinOpKind;
const UnaryOpKind = mir.UnaryOpKind;
const AggregateKind = mir.AggregateKind;
const MirIntrinsicKind = mir.MirIntrinsicKind;
const MirBody = mir.MirBody;

const TargetSpec = codegen_abi.TargetSpec;
const CBackendConfig = codegen_abi.CBackendConfig;
const CodegenModuleInput = codegen_abi.CodegenModuleInput;
const CodegenArtifact = codegen_abi.CodegenArtifact;
const OutputArtifactKind = codegen_abi.OutputArtifactKind;
const TypeLayoutResolver = codegen_abi.TypeLayoutResolver;
const ResolvedTypeLayout = codegen_abi.ResolvedTypeLayout;
const ResolvedSumDetail = codegen_abi.ResolvedSumDetail;
const SumReprKind = codegen_abi.SumReprKind;
const NicheEncoding = codegen_abi.NicheEncoding;

// ---------------------------------------- TYPES ----------------------------------------

/// Errors surfaced during Tier A C99 source emission or `zig cc` invocation.
pub const CCodegenError = error{
    /// `artifact_kind` requested disk compilation without `output_path` or `io`.
    MissingOutputConfig,
    /// `zig cc` subprocess exited with non-zero status (`E0008`).
    CompilerDriverFailed,
    /// Underlying layout, process, or filesystem failure.
    BackendFailure,
    /// Host allocator ran out of memory.
    OutOfMemory,
};

/// Resolved integer width and signedness descriptor for C99 lowering.
const CIntInfo = struct {
    /// Exact integer bit-width (`1`, `8`, `16`, `32`, `64`, or `128`).
    bits: u16,
    /// `true` for signed two's-complement types (`i8..i128`, `isize`), `false` for unsigned.
    is_signed: bool,
};

/// Synthesized closure wrapper descriptor pairing a `closure_make` site with its target `MirBody`.
const ClosureThunkSpec = struct {
    /// Zero-based index into `ClosureThunkSpec` table (`_cx_cthunk_<thunk_idx>`).
    thunk_idx: u32,
    /// Closure signature `TypeId` (`.closure_ty`).
    closure_ty: TypeId,
    /// Index into `CodegenModuleInput.bodies` for the synthesized closure body.
    target_body_idx: u32,
    /// Captured variable `TypeId`s stored sequentially inside `_cx_cenv_<thunk_idx>`.
    capture_types: []TypeId,
    /// `true` for 3-word escaping Tier-2 closures carrying `drop_fn`, `false` for 2-word `@local` closures.
    is_three_word: bool,
};

/// Evaluated C expression or addressable lvalue produced by `MirPlace` projection lowering.
const LoweredPlaceC = union(enum) {
    /// Addressable C99 lvalue expression of `pointee_ty` (may be taken by `&(…)` or assigned).
    lvalue_expr: struct {
        expr_str: []u8,
        pointee_ty: TypeId,
    },
    /// Compile-time constant `.len` read from a fixed `[T; N]` or `#soa [S; N]` array.
    const_len: u64,
};

/// Resolved FFI, linker-section, TLS, and WebAssembly import/export metadata for a `SymbolIndex`.
const SymFfiMeta = struct {
    /// `true` when declared with `extern` (`flags.is_extern`).
    is_extern: bool = false,
    /// `true` when annotated with `@export` (`contract_flags.is_export`).
    is_export: bool = false,
    /// `true` when declared `static mut` (`flags.is_mut`).
    is_mut: bool = false,
    /// `true` when annotated with `@thread_local`.
    is_thread_local: bool = false,
    /// Explicit `@link_name("…")` override (`""` when absent).
    link_name: []const u8 = "",
    /// Explicit `@link_section("…")` override (`""` when absent).
    link_section: []const u8 = "",
    /// Explicit `@wasm_import("module", …)` host module (`""` when absent).
    wasm_import_module: []const u8 = "",
    /// Explicit `@wasm_import(…, "name")` host symbol (`""` when absent).
    wasm_import_name: []const u8 = "",
    /// Explicit `@wasm_export("name")` symbol (`""` when absent).
    wasm_export_name: []const u8 = "",
    /// Optional `@link_lib("name")` native library directive (`""` when absent).
    link_lib_name: []const u8 = "",
};

/// Stateful deterministic Tier A C99 module emitter.
const CModuleEmitter = struct {
    /// Backing allocator for transient tables and output buffers.
    allocator: std.mem.Allocator,
    /// Active Tier A configuration (`target`, `is_release_mode`, `is_fuzz_instrumented`).
    cfg: CBackendConfig,
    /// Canonical module input bundle.
    input: CodegenModuleInput,
    /// Shared target-aware `TypeLayoutResolver`.
    resolver: TypeLayoutResolver,
    /// Target pointer layout (`NATIVE_64`, `AARCH64_MACOS`, or `WASM32`).
    target_layout: TargetLayout,
    /// Accumulated C99 output byte buffer.
    out: std.ArrayListUnmanaged(u8) = .empty,
    /// Set of `TypeId.toU32()` handles discovered across the module.
    discovered_type_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Deterministic sorted list of discovered composite `TypeId`s.
    sorted_candidates: std.ArrayListUnmanaged(TypeId) = .empty,
    /// DFS visitation state (`0` = unvisited, `1` = visiting, `2` = emitted) keyed by `TypeId.toU32()`.
    topo_state: std.AutoHashMapUnmanaged(u32, u8) = .empty,
    /// Final topologically ordered composite `TypeId`s for `typedef` emission.
    ordered_types: std.ArrayListUnmanaged(TypeId) = .empty,
    /// Set of `TypeId.toU32()` handles requiring synthesized `_cx_drop_ty_<id>` helpers.
    drop_type_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Topologically ordered `TypeId`s for synthesized `_cx_drop_ty_<id>` helpers.
    ordered_drop_types: std.ArrayListUnmanaged(TypeId) = .empty,
    /// Set of `TypeId.toU32()` handles requiring synthesized `_cx_eq_ty_<id>` structural equality helpers.
    eq_type_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Topologically ordered `TypeId`s for synthesized `_cx_eq_ty_<id>` structural equality helpers.
    ordered_eq_types: std.ArrayListUnmanaged(TypeId) = .empty,
    /// Set of `TypeId.toU32()` handles requiring synthesized `_cx_fmt_fn_ty_<id>` formatting thunks (`SE-12`).
    fmt_type_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Topologically ordered `TypeId`s for synthesized `_cx_fmt_fn_ty_<id>` formatting thunks (`SE-12`).
    ordered_fmt_types: std.ArrayListUnmanaged(TypeId) = .empty,
    /// Deduplicated `MirConst.source_loc` descriptors (`SE-17`) emitted as `_cx_loc_<k>`.
    source_loc_consts: std.ArrayListUnmanaged(mir.SourceLocConst) = .empty,
    /// Map packing `(file_sym, fn_sym, line, col)` into `u128 -> loc_idx`.
    source_loc_map: std.AutoHashMapUnmanaged(u128, u32) = .empty,
    /// Map `DefId.asInt() -> body index` in `input.bodies`.
    def_to_body_idx: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// Map `SymbolIndex.asInt() -> body index` in `input.bodies`.
    sym_to_body_idx: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// C identifier assigned to each `MirBody` (`0 .. input.bodies.len - 1`).
    body_c_names: std.ArrayListUnmanaged([]u8) = .empty,
    /// Externally referenced `SymbolIndex` prototypes without a `MirBody` in `input.bodies`.
    extern_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty,
    /// Set deduplicating `extern_syms` by `SymbolIndex.asInt()`.
    extern_sym_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Externally referenced `extern static` global `SymbolIndex` declarations.
    extern_global_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty,
    /// Set deduplicating `extern_global_syms` by `SymbolIndex.asInt()`.
    extern_global_sym_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Deduplicated `@link_lib("…")` library names collected across referenced FFI symbols.
    collected_link_libs: std.ArrayListUnmanaged([]const u8) = .empty,
    /// Interned string/byte `SymbolId.asInt()` literals referenced in `MirConst`, sorted deterministically.
    string_const_ids: std.ArrayListUnmanaged(u32) = .empty,
    /// Set deduplicating `string_const_ids`.
    string_const_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Referenced `(blob_id, align_log2)` `MirConst.raw_blob` entries, sorted by `blob_id`.
    raw_blob_ids: std.ArrayListUnmanaged(mir.RawBlobConst) = .empty,
    /// Set deduplicating `raw_blob_ids` by `blob_id`.
    raw_blob_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Reflected `TypeId.toU32()` handles referenced by `@type_name[T]()`, sorted deterministically.
    type_name_ids: std.ArrayListUnmanaged(u32) = .empty,
    /// Set deduplicating `type_name_ids`.
    type_name_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Synthesized closure thunks keyed by `(body_idx << 32) | inst_raw`.
    closure_thunk_map: std.AutoHashMapUnmanaged(u64, u32) = .empty,
    /// Ordered list of synthesized closure thunks.
    closure_thunks: std.ArrayListUnmanaged(ClosureThunkSpec) = .empty,
    /// Index of CoreX `main` in `input.bodies` if present (`null` for libraries).
    entry_main_body_idx: ?u32 = null,
    /// Whether any `MirBody` executes `ctx_get` or `ctx_set` (`SE-08`).
    has_context_ops: bool = false,
    /// Aligned per-slot byte stride for `_cx_tls_ctx` (`>= 8`, expanded for wide nominal slots).
    ctx_slot_stride_bytes: u64 = 8,
    /// Cloned `MirBody` array when `Pass D5.5` SSA demotion is prepared locally by `emitModule`.
    owned_async_bodies: ?[]MirBody = null,
    /// Computed stackless coroutine frame layout & state-machine plan (`mir_async`).
    async_plan: ?mir_async.AsyncModulePlan = null,
    /// `true` when at least one `is_async` body or async intrinsic (`44..51`) is present.
    has_async_ops: bool = false,
    /// Active coroutine `body_idx` while emitting `_cx_coro_poll_<idx>` (`null` in sync functions).
    active_coro_body_idx: ?u32 = null,
    /// Active basic block `MirBlockId` while emitting instructions inside a basic block.
    active_bb_id: MirBlockId = .none,
    /// Set of `Result` `TypeId.toU32()` handles requiring `_cx_is_err_ty_<id>` sibling-cascade helpers.
    res_err_check_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Deterministic ordered list of `Result` `TypeId`s for `_cx_is_err_ty_<id>` emission.
    ordered_res_err_types: std.ArrayListUnmanaged(TypeId) = .empty,
    /// `true` while emitting an `@export`, `@wasm_export`, or `extern "C"` C-ABI function body.
    is_in_c_abi_body: bool = false,
    /// Monotonic per-function temporary counter reset at the start of each `MirBody`.
    temp_counter: u32 = 0,

    /// Initializes `CModuleEmitter` for `(cfg, input)`.
    fn init(
        allocator: std.mem.Allocator,
        cfg: CBackendConfig,
        input: CodegenModuleInput,
    ) CModuleEmitter {
        return .{
            .allocator = allocator,
            .cfg = cfg,
            .input = input,
            .resolver = TypeLayoutResolver.init(allocator, input.pool, input.sym_table, cfg.target),
            .target_layout = cfg.target.asTargetLayout(),
        };
    }

    /// Releases all transient emitter state (`out` is transferred to caller when taken).
    fn deinit(self: *CModuleEmitter) void {
        if (self.async_plan) |*plan| {
            plan.deinit();
            self.async_plan = null;
        }
        if (self.owned_async_bodies) |owned_slice| {
            for (owned_slice) |*owned_body| {
                owned_body.deinit();
            }
            self.allocator.free(owned_slice);
            self.owned_async_bodies = null;
        }
        self.res_err_check_set.deinit(self.allocator);
        self.ordered_res_err_types.deinit(self.allocator);
        self.resolver.deinit();
        self.out.deinit(self.allocator);
        self.discovered_type_set.deinit(self.allocator);
        self.sorted_candidates.deinit(self.allocator);
        self.topo_state.deinit(self.allocator);
        self.ordered_types.deinit(self.allocator);
        self.drop_type_set.deinit(self.allocator);
        self.ordered_drop_types.deinit(self.allocator);
        self.eq_type_set.deinit(self.allocator);
        self.ordered_eq_types.deinit(self.allocator);
        self.fmt_type_set.deinit(self.allocator);
        self.ordered_fmt_types.deinit(self.allocator);
        self.source_loc_consts.deinit(self.allocator);
        self.source_loc_map.deinit(self.allocator);
        self.def_to_body_idx.deinit(self.allocator);
        self.sym_to_body_idx.deinit(self.allocator);
        for (self.body_c_names.items) |owned_name| {
            self.allocator.free(owned_name);
        }
        self.body_c_names.deinit(self.allocator);
        self.extern_syms.deinit(self.allocator);
        self.extern_sym_set.deinit(self.allocator);
        self.extern_global_syms.deinit(self.allocator);
        self.extern_global_sym_set.deinit(self.allocator);
        self.collected_link_libs.deinit(self.allocator);
        self.string_const_ids.deinit(self.allocator);
        self.string_const_set.deinit(self.allocator);
        self.raw_blob_ids.deinit(self.allocator);
        self.raw_blob_set.deinit(self.allocator);
        self.type_name_ids.deinit(self.allocator);
        self.type_name_set.deinit(self.allocator);
        self.closure_thunk_map.deinit(self.allocator);
        for (self.closure_thunks.items) |thunk_item| {
            if (thunk_item.capture_types.len > 0) {
                self.allocator.free(thunk_item.capture_types);
            }
        }
        self.closure_thunks.deinit(self.allocator);
    }

    /// Appends raw `text` to `self.out`.
    fn writeAll(self: *CModuleEmitter, text: []const u8) !void {
        try self.out.appendSlice(self.allocator, text);
    }

    /// Appends formatted text to `self.out`.
    fn print(self: *CModuleEmitter, comptime fmt_str: []const u8, args: anytype) !void {
        const formatted = try std.fmt.allocPrint(self.allocator, fmt_str, args);
        defer self.allocator.free(formatted);
        try self.out.appendSlice(self.allocator, formatted);
    }

    /// Allocates a fresh function-local temporary identifier `_t<n>`.
    fn nextTempId(self: *CModuleEmitter) u32 {
        const cur_id = self.temp_counter;
        self.temp_counter += 1;
        return cur_id;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Number of hex bytes emitted per line inside chunked `MirConst.raw_blob` static arrays (`D-03`).
const RAW_BLOB_BYTES_PER_LINE: usize = 16;

/// Maximum pointer indirection / composite DFS depth enforced in Tier A emission.
const MAX_C_TYPE_DEPTH: u32 = 64;

/// Canonical WASI Preview 1 import symbol set routed to `"wasi_snapshot_preview1"` on `wasm32-wasi`.
const WASI_PREVIEW1_IMPORT_SET = std.StaticStringMap(void).initComptime(.{
    .{ "args_get", {} },
    .{ "args_sizes_get", {} },
    .{ "clock_res_get", {} },
    .{ "clock_time_get", {} },
    .{ "environ_get", {} },
    .{ "environ_sizes_get", {} },
    .{ "fd_close", {} },
    .{ "fd_fdstat_get", {} },
    .{ "fd_prestat_dir_name", {} },
    .{ "fd_prestat_get", {} },
    .{ "fd_read", {} },
    .{ "fd_seek", {} },
    .{ "fd_write", {} },
    .{ "path_open", {} },
    .{ "poll_oneoff", {} },
    .{ "proc_exit", {} },
    .{ "random_get", {} },
    .{ "sched_yield", {} },
});

/// Static runtime C99 preamble providing UB-free arithmetic, 128-bit fallbacks, and oracle tracing.
const C99_RUNTIME_PREAMBLE: []const u8 =
    \\#include <stdint.h>
    \\#include <stdbool.h>
    \\#include <stddef.h>
    \\#include <string.h>
    \\#include <stdlib.h>
    \\#include <stdio.h>
    \\#include <math.h>
    \\#if defined(_WIN32)
    \\#include <io.h>
    \\#include <fcntl.h>
    \\#else
    \\#include <unistd.h>
    \\#endif
    \\
    \\#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L && !defined(__wasm__)
    \\#define CX_THREAD_LOCAL _Thread_local
    \\#elif defined(_MSC_VER)
    \\#define CX_THREAD_LOCAL __declspec(thread)
    \\#elif (defined(__GNUC__) || defined(__clang__)) && !defined(__wasm__)
    \\#define CX_THREAD_LOCAL __thread
    \\#else
    \\#define CX_THREAD_LOCAL
    \\#endif
    \\
    \\typedef void (*_cx_fn_slot_t)(void);
    \\typedef struct cx_str_s { uint8_t *ptr; uintptr_t len; } cx_str_t;
    \\typedef struct cx_source_loc_data_s {
    \\    cx_str_t file;
    \\    cx_str_t fn_name;
    \\    uint32_t line;
    \\    uint32_t col;
    \\} cx_source_loc_data_t;
    \\typedef const cx_source_loc_data_t *cx_source_loc_t;
    \\typedef struct cx_fmt_spec_s {
    \\    uint32_t flags_and_fill;
    \\    uint16_t width_or_none;
    \\    uint16_t precision_or_none;
    \\} cx_fmt_spec_t;
    \\typedef struct _cx_rt_buf_s {
    \\    uint8_t *data;
    \\    size_t len;
    \\    size_t cap;
    \\} _cx_rt_buf_t;
    \\typedef void (*cx_fmt_fn_t)(_cx_rt_buf_t *, const void *, uint32_t, uint32_t);
    \\typedef struct cx_fmt_arg_s {
    \\    const void *data;
    \\    cx_fmt_fn_t fmt_fn;
    \\    cx_fmt_spec_t spec;
    \\} cx_fmt_arg_t;
    \\typedef struct cx_fmt_args_s {
    \\    const cx_str_t *pieces_ptr;
    \\    uintptr_t pieces_len;
    \\    const cx_fmt_arg_t *args_ptr;
    \\    uintptr_t args_len;
    \\} cx_fmt_args_t;
    \\typedef struct cx_bencher_s {
    \\    void *state_ptr;
    \\    uintptr_t iters;
    \\} cx_bencher_t;
    \\typedef char _cx_sz_assert_fmt_spec[(sizeof(cx_fmt_spec_t) == 8u) ? 1 : -1];
    \\typedef char _cx_sz_assert_fmt_args[(sizeof(cx_fmt_args_t) == (4u * sizeof(uintptr_t))) ? 1 : -1];
    \\typedef char _cx_sz_assert_sloc_data[(sizeof(cx_source_loc_data_t) == (4u * sizeof(uintptr_t) + 8u)) ? 1 : -1];
    \\
    \\static void _cx_rt_init(void) {
    \\#if defined(_WIN32)
    \\    (void)_setmode(1, _O_BINARY);
    \\    (void)_setmode(2, _O_BINARY);
    \\#endif
    \\}
    \\
    \\static void _cx_rt_trace_append(const char *line_text) {
    \\    const char *trace_path = getenv("COREX_ORACLE_TRACE_FILE");
    \\    if (trace_path != NULL && trace_path[0] != '\0') {
    \\        FILE *trace_fp = fopen(trace_path, "ab");
    \\        if (trace_fp != NULL) {
    \\            size_t line_len = strlen(line_text);
    \\            if (line_len > 0) {
    \\                (void)fwrite(line_text, 1, line_len, trace_fp);
    \\            }
    \\            (void)fflush(trace_fp);
    \\            (void)fclose(trace_fp);
    \\        }
    \\    }
    \\}
    \\
    \\static void _cx_rt_drop_trace(int64_t drop_id) {
    \\    char msg_buf[64];
    \\    (void)snprintf(msg_buf, sizeof(msg_buf), "DROP:%lld\n", (long long)drop_id);
    \\    _cx_rt_trace_append(msg_buf);
    \\}
    \\
    \\#if defined(__GNUC__) || defined(__clang__)
    \\__attribute__((noreturn))
    \\#endif
    \\static void _cx_rt_trap(uint32_t trap_reason) {
    \\    (void)trap_reason;
    \\    const char *trace_path = getenv("COREX_ORACLE_TRACE_FILE");
    \\    if (trace_path != NULL && trace_path[0] != '\0') {
    \\        _cx_rt_trace_append("TRAP:1\n");
    \\        (void)fflush(stdout);
    \\        (void)fflush(stderr);
    \\        _exit(101);
    \\    }
    \\#if defined(__GNUC__) || defined(__clang__)
    \\    __builtin_trap();
    \\#else
    \\    abort();
    \\#endif
    \\}
    \\
    \\static intptr_t _cx_rt_sys_write(int32_t fd_num, const uint8_t *buf_ptr, size_t buf_len) {
    \\    if (fd_num != 1 && fd_num != 2) {
    \\        return (intptr_t)(-1);
    \\    }
    \\    if (buf_len == 0) {
    \\        return 0;
    \\    }
    \\    size_t total_written = 0;
    \\    while (total_written < buf_len) {
    \\#if defined(_WIN32)
    \\        size_t rem_len = buf_len - total_written;
    \\        unsigned int chunk_len = rem_len > 0x7FFFFFFFu ? 0x7FFFFFFFu : (unsigned int)rem_len;
    \\        int wrote_now = _write((int)fd_num, buf_ptr + total_written, chunk_len);
    \\#else
    \\        ssize_t wrote_now = write((int)fd_num, buf_ptr + total_written, buf_len - total_written);
    \\#endif
    \\        if (wrote_now <= 0) {
    \\            return total_written > 0 ? (intptr_t)total_written : (intptr_t)(-1);
    \\        }
    \\        total_written += (size_t)wrote_now;
    \\    }
    \\    return (intptr_t)total_written;
    \\}
    \\
    \\#if defined(__GNUC__) || defined(__clang__)
    \\__attribute__((noreturn))
    \\#endif
    \\static void _cx_rt_sys_exit(int32_t status_code) {
    \\    char exit_buf[64];
    \\    (void)snprintf(exit_buf, sizeof(exit_buf), "EXIT:%d\n", (int)status_code);
    \\    _cx_rt_trace_append(exit_buf);
    \\    (void)fflush(stdout);
    \\    (void)fflush(stderr);
    \\    _exit((int)status_code);
    \\}
    \\
    \\#if defined(__GNUC__) || defined(__clang__)
    \\__attribute__((noreturn))
    \\#endif
    \\static void _cx_rt_panic(const uint8_t *msg_ptr, size_t msg_len) {
    \\    static const uint8_t prefix_bytes[7] = { 'p', 'a', 'n', 'i', 'c', ':', ' ' };
    \\    static const uint8_t nl_byte[1] = { '\n' };
    \\    (void)_cx_rt_sys_write(2, prefix_bytes, 7);
    \\    if (msg_ptr != NULL && msg_len > 0) {
    \\        (void)_cx_rt_sys_write(2, msg_ptr, msg_len);
    \\    }
    \\    (void)_cx_rt_sys_write(2, nl_byte, 1);
    \\    _cx_rt_trap(0);
    \\}
    \\
    \\static inline uint8_t _cx_str_eq(
    \\    const uint8_t *lhs_ptr,
    \\    size_t lhs_len,
    \\    const uint8_t *rhs_ptr,
    \\    size_t rhs_len
    \\) {
    \\    if (lhs_len != rhs_len) return 0u;
    \\    if (lhs_len == 0) return 1u;
    \\    return memcmp(lhs_ptr, rhs_ptr, lhs_len) == 0 ? 1u : 0u;
    \\}
    \\
    \\static inline uint8_t _cx_source_loc_eq(cx_source_loc_t lhs_loc, cx_source_loc_t rhs_loc) {
    \\    if (lhs_loc == rhs_loc) return 1u;
    \\    if (lhs_loc == NULL || rhs_loc == NULL) return 0u;
    \\    if (lhs_loc->line != rhs_loc->line || lhs_loc->col != rhs_loc->col) return 0u;
    \\    if (!_cx_str_eq(lhs_loc->file.ptr, (size_t)lhs_loc->file.len, rhs_loc->file.ptr, (size_t)rhs_loc->file.len)) return 0u;
    \\    return _cx_str_eq(lhs_loc->fn_name.ptr, (size_t)lhs_loc->fn_name.len, rhs_loc->fn_name.ptr, (size_t)rhs_loc->fn_name.len);
    \\}
    \\
    \\static inline uint8_t _cx_fmt_spec_eq(cx_fmt_spec_t lhs_s, cx_fmt_spec_t rhs_s) {
    \\    return (lhs_s.flags_and_fill == rhs_s.flags_and_fill &&
    \\        lhs_s.width_or_none == rhs_s.width_or_none &&
    \\        lhs_s.precision_or_none == rhs_s.precision_or_none) ? 1u : 0u;
    \\}
    \\
    \\static const uint8_t __attribute__((aligned(16))) _cx_empty_rodata[1u] = { 0x00u };
    \\
    \\static inline uint8_t _cx_read_u8(const uint8_t *base_p, size_t off_b) {
    \\    return base_p[off_b];
    \\}
    \\static inline uint16_t _cx_read_u16(const uint8_t *base_p, size_t off_b) {
    \\    uint16_t out_v = 0u;
    \\    memcpy(&out_v, base_p + off_b, sizeof(out_v));
    \\    return out_v;
    \\}
    \\static inline uint32_t _cx_read_u32(const uint8_t *base_p, size_t off_b) {
    \\    uint32_t out_v = 0u;
    \\    memcpy(&out_v, base_p + off_b, sizeof(out_v));
    \\    return out_v;
    \\}
    \\static inline uint64_t _cx_read_u64(const uint8_t *base_p, size_t off_b) {
    \\    uint64_t out_v = 0u;
    \\    memcpy(&out_v, base_p + off_b, sizeof(out_v));
    \\    return out_v;
    \\}
    \\static inline void _cx_write_u8(uint8_t *base_p, size_t off_b, uint8_t val) {
    \\    base_p[off_b] = val;
    \\}
    \\static inline void _cx_write_u16(uint8_t *base_p, size_t off_b, uint16_t val) {
    \\    memcpy(base_p + off_b, &val, sizeof(val));
    \\}
    \\static inline void _cx_write_u32(uint8_t *base_p, size_t off_b, uint32_t val) {
    \\    memcpy(base_p + off_b, &val, sizeof(val));
    \\}
    \\static inline void _cx_write_u64(uint8_t *base_p, size_t off_b, uint64_t val) {
    \\    memcpy(base_p + off_b, &val, sizeof(val));
    \\}
    \\
;

/// Standalone C99 `SanitizerCoverage` runtime shim (`RDG-18`, Windows COFF `.SCOV$*` anchors + edge stats).
pub const SANCOV_SHIM_C_SOURCE: []const u8 =
    \\#include <stdint.h>
    \\#include <stddef.h>
    \\#include <stdlib.h>
    \\#include <stdio.h>
    \\
    \\#if defined(_WIN32)
    \\__attribute__((section(".SCOV$CA"), aligned(8))) uint64_t __start___sancov_cntrs = 0u;
    \\__attribute__((section(".SCOV$CZ"), aligned(1))) uint8_t __stop___sancov_cntrs = 0u;
    \\__attribute__((section(".SCOVP$A"), aligned(8))) uint64_t __start___sancov_pcs = 0u;
    \\__attribute__((section(".SCOVP$Z"), aligned(1))) uint8_t __stop___sancov_pcs = 0u;
    \\#endif
    \\
    \\static uint8_t *_cx_sancov_start = NULL;
    \\static uint8_t *_cx_sancov_stop = NULL;
    \\static uint64_t _cx_sancov_cmp_events = 0u;
    \\
    \\void __sanitizer_cov_8bit_counters_init(uint8_t *start_p, uint8_t *stop_p) {
    \\    if (start_p == NULL || stop_p == NULL || start_p >= stop_p) return;
    \\    if (_cx_sancov_start == NULL || start_p < _cx_sancov_start) _cx_sancov_start = start_p;
    \\    if (_cx_sancov_stop == NULL || stop_p > _cx_sancov_stop) _cx_sancov_stop = stop_p;
    \\}
    \\
    \\void __sanitizer_cov_pcs_init(const uintptr_t *pcs_beg, const uintptr_t *pcs_end) {
    \\    (void)pcs_beg;
    \\    (void)pcs_end;
    \\}
    \\
    \\void __sanitizer_cov_trace_cmp1(uint8_t arg1, uint8_t arg2) { (void)arg1; (void)arg2; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_cmp2(uint16_t arg1, uint16_t arg2) { (void)arg1; (void)arg2; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_cmp4(uint32_t arg1, uint32_t arg2) { (void)arg1; (void)arg2; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_cmp8(uint64_t arg1, uint64_t arg2) { (void)arg1; (void)arg2; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_const_cmp1(uint8_t arg1, uint8_t arg2) { (void)arg1; (void)arg2; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_const_cmp2(uint16_t arg1, uint16_t arg2) { (void)arg1; (void)arg2; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_const_cmp4(uint32_t arg1, uint32_t arg2) { (void)arg1; (void)arg2; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_const_cmp8(uint64_t arg1, uint64_t arg2) { (void)arg1; (void)arg2; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_switch(uint64_t val, uint64_t *cases) { (void)val; (void)cases; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_div4(uint32_t val) { (void)val; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_div8(uint64_t val) { (void)val; _cx_sancov_cmp_events += 1u; }
    \\void __sanitizer_cov_trace_gep(uintptr_t idx) { (void)idx; _cx_sancov_cmp_events += 1u; }
    \\
    \\#if defined(__GNUC__) || defined(__clang__)
    \\__attribute__((destructor))
    \\#endif
    \\static void _cx_sancov_report_atexit(void) {
    \\    const char *stats_env = getenv("COREX_FUZZ_STATS");
    \\    if (stats_env == NULL || stats_env[0] == '\0' || stats_env[0] == '0') return;
    \\    size_t hit_edges = 0u;
    \\    size_t total_edges = 0u;
    \\    if (_cx_sancov_start != NULL && _cx_sancov_stop != NULL && _cx_sancov_start < _cx_sancov_stop) {
    \\        uint8_t *cur_p = _cx_sancov_start;
    \\        while (cur_p < _cx_sancov_stop) {
    \\            if (*cur_p != 0u) hit_edges += 1u;
    \\            total_edges += 1u;
    \\            cur_p += 1;
    \\        }
    \\    }
    \\    fprintf(
    \\        stderr,
    \\        "SANCOV_EDGES:%zu/%zu CMPS:%llu\n",
    \\        hit_edges,
    \\        total_edges,
    \\        (unsigned long long)_cx_sancov_cmp_events
    \\    );
    \\    fflush(stderr);
    \\}
    \\
;

/// Static 128-bit integer and UB-free scalar arithmetic helpers for Tier A C99.
const C99_ARITH_HELPERS: []const u8 =
    \\#if defined(__SIZEOF_INT128__)
    \\typedef __int128 cx_i128;
    \\typedef unsigned __int128 cx_u128;
    \\static inline cx_u128 _cx_u128_make(uint64_t lo_w, uint64_t hi_w) {
    \\    return ((cx_u128)hi_w << 64) | (cx_u128)lo_w;
    \\}
    \\static inline cx_i128 _cx_i128_make(uint64_t lo_w, uint64_t hi_w) {
    \\    return (cx_i128)_cx_u128_make(lo_w, hi_w);
    \\}
    \\static inline uint64_t _cx_u128_lo(cx_u128 val) { return (uint64_t)val; }
    \\static inline uint64_t _cx_u128_hi(cx_u128 val) { return (uint64_t)(val >> 64); }
    \\static inline cx_u128 _cx_as_u128(cx_i128 val) { return (cx_u128)val; }
    \\static inline cx_i128 _cx_as_i128(cx_u128 val) { return (cx_i128)val; }
    \\static inline cx_u128 _cx_u128_add_wrap(cx_u128 lhs_v, cx_u128 rhs_v) { return lhs_v + rhs_v; }
    \\static inline cx_u128 _cx_u128_sub_wrap(cx_u128 lhs_v, cx_u128 rhs_v) { return lhs_v - rhs_v; }
    \\static inline cx_u128 _cx_u128_mul_wrap(cx_u128 lhs_v, cx_u128 rhs_v) { return lhs_v * rhs_v; }
    \\static inline cx_u128 _cx_u128_and(cx_u128 lhs_v, cx_u128 rhs_v) { return lhs_v & rhs_v; }
    \\static inline cx_u128 _cx_u128_or(cx_u128 lhs_v, cx_u128 rhs_v) { return lhs_v | rhs_v; }
    \\static inline cx_u128 _cx_u128_xor(cx_u128 lhs_v, cx_u128 rhs_v) { return lhs_v ^ rhs_v; }
    \\static inline cx_u128 _cx_u128_not(cx_u128 val) { return ~val; }
    \\static inline cx_u128 _cx_u128_shl(cx_u128 val, uint32_t amt) { return val << (amt & 127u); }
    \\static inline cx_u128 _cx_u128_lshr(cx_u128 val, uint32_t amt) { return val >> (amt & 127u); }
    \\static inline cx_i128 _cx_i128_ashr(cx_i128 val, uint32_t amt) { return val >> (amt & 127u); }
    \\static inline uint8_t _cx_u128_eq(cx_u128 lhs_v, cx_u128 rhs_v) { return lhs_v == rhs_v ? 1u : 0u; }
    \\static inline uint8_t _cx_u128_ult(cx_u128 lhs_v, cx_u128 rhs_v) { return lhs_v < rhs_v ? 1u : 0u; }
    \\static inline uint8_t _cx_i128_slt(cx_i128 lhs_v, cx_i128 rhs_v) { return lhs_v < rhs_v ? 1u : 0u; }
    \\static inline cx_u128 _cx_u128_add_chk(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    cx_u128 res_v = lhs_v + rhs_v;
    \\    if (res_v < lhs_v) _cx_rt_trap(2);
    \\    return res_v;
    \\}
    \\static inline cx_u128 _cx_u128_sub_chk(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    if (lhs_v < rhs_v) _cx_rt_trap(2);
    \\    return lhs_v - rhs_v;
    \\}
    \\static inline cx_u128 _cx_u128_mul_chk(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    cx_u128 res_v = 0;
    \\    if (__builtin_mul_overflow(lhs_v, rhs_v, &res_v)) _cx_rt_trap(2);
    \\    return res_v;
    \\}
    \\static inline cx_i128 _cx_i128_add_chk(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    cx_i128 res_v = 0;
    \\    if (__builtin_add_overflow(lhs_v, rhs_v, &res_v)) _cx_rt_trap(2);
    \\    return res_v;
    \\}
    \\static inline cx_i128 _cx_i128_sub_chk(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    cx_i128 res_v = 0;
    \\    if (__builtin_sub_overflow(lhs_v, rhs_v, &res_v)) _cx_rt_trap(2);
    \\    return res_v;
    \\}
    \\static inline cx_i128 _cx_i128_mul_chk(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    cx_i128 res_v = 0;
    \\    if (__builtin_mul_overflow(lhs_v, rhs_v, &res_v)) _cx_rt_trap(2);
    \\    return res_v;
    \\}
    \\static inline cx_u128 _cx_u128_div_chk(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    if (rhs_v == 0) _cx_rt_trap(2);
    \\    return lhs_v / rhs_v;
    \\}
    \\static inline cx_u128 _cx_u128_rem_chk(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    if (rhs_v == 0) _cx_rt_trap(2);
    \\    return lhs_v % rhs_v;
    \\}
    \\static inline cx_i128 _cx_i128_div_chk(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    cx_i128 min_v = (cx_i128)((cx_u128)1 << 127);
    \\    if (rhs_v == 0 || (lhs_v == min_v && rhs_v == (cx_i128)(-1))) _cx_rt_trap(2);
    \\    return lhs_v / rhs_v;
    \\}
    \\static inline cx_i128 _cx_i128_rem_chk(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    cx_i128 min_v = (cx_i128)((cx_u128)1 << 127);
    \\    if (rhs_v == 0 || (lhs_v == min_v && rhs_v == (cx_i128)(-1))) _cx_rt_trap(2);
    \\    return lhs_v % rhs_v;
    \\}
    \\#else
    \\typedef struct __attribute__((aligned(8))) cx_u128 { uint64_t lo; uint64_t hi; } cx_u128;
    \\typedef cx_u128 cx_i128;
    \\static inline cx_u128 _cx_u128_make(uint64_t lo_w, uint64_t hi_w) {
    \\    cx_u128 out_v; out_v.lo = lo_w; out_v.hi = hi_w; return out_v;
    \\}
    \\static inline cx_i128 _cx_i128_make(uint64_t lo_w, uint64_t hi_w) {
    \\    return _cx_u128_make(lo_w, hi_w);
    \\}
    \\static inline uint64_t _cx_u128_lo(cx_u128 val) { return val.lo; }
    \\static inline uint64_t _cx_u128_hi(cx_u128 val) { return val.hi; }
    \\static inline cx_u128 _cx_as_u128(cx_i128 val) { return val; }
    \\static inline cx_i128 _cx_as_i128(cx_u128 val) { return val; }
    \\static inline cx_u128 _cx_u128_add_wrap(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    uint64_t lo_s = lhs_v.lo + rhs_v.lo;
    \\    uint64_t carry_b = lo_s < lhs_v.lo ? 1ull : 0ull;
    \\    return _cx_u128_make(lo_s, lhs_v.hi + rhs_v.hi + carry_b);
    \\}
    \\static inline cx_u128 _cx_u128_sub_wrap(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    uint64_t borrow_b = lhs_v.lo < rhs_v.lo ? 1ull : 0ull;
    \\    return _cx_u128_make(lhs_v.lo - rhs_v.lo, lhs_v.hi - rhs_v.hi - borrow_b);
    \\}
    \\static inline cx_u128 _cx_u128_mul_wrap(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    uint64_t a_lo = lhs_v.lo & 0xFFFFFFFFull, a_hi = lhs_v.lo >> 32;
    \\    uint64_t b_lo = rhs_v.lo & 0xFFFFFFFFull, b_hi = rhs_v.lo >> 32;
    \\    uint64_t p0 = a_lo * b_lo;
    \\    uint64_t p1 = a_lo * b_hi;
    \\    uint64_t p2 = a_hi * b_lo;
    \\    uint64_t p3 = a_hi * b_hi;
    \\    uint64_t mid_c = ((p0 >> 32) + (p1 & 0xFFFFFFFFull) + (p2 & 0xFFFFFFFFull)) >> 32;
    \\    uint64_t hi_w = p3 + (p1 >> 32) + (p2 >> 32) + mid_c + lhs_v.lo * rhs_v.hi + lhs_v.hi * rhs_v.lo;
    \\    return _cx_u128_make(lhs_v.lo * rhs_v.lo, hi_w);
    \\}
    \\static inline cx_u128 _cx_u128_and(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    return _cx_u128_make(lhs_v.lo & rhs_v.lo, lhs_v.hi & rhs_v.hi);
    \\}
    \\static inline cx_u128 _cx_u128_or(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    return _cx_u128_make(lhs_v.lo | rhs_v.lo, lhs_v.hi | rhs_v.hi);
    \\}
    \\static inline cx_u128 _cx_u128_xor(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    return _cx_u128_make(lhs_v.lo ^ rhs_v.lo, lhs_v.hi ^ rhs_v.hi);
    \\}
    \\static inline cx_u128 _cx_u128_not(cx_u128 val) { return _cx_u128_make(~val.lo, ~val.hi); }
    \\static inline cx_u128 _cx_u128_shl(cx_u128 val, uint32_t amt) {
    \\    uint32_t sh = amt & 127u;
    \\    if (sh == 0) return val;
    \\    if (sh >= 64) return _cx_u128_make(0, val.lo << (sh - 64));
    \\    return _cx_u128_make(val.lo << sh, (val.hi << sh) | (val.lo >> (64 - sh)));
    \\}
    \\static inline cx_u128 _cx_u128_lshr(cx_u128 val, uint32_t amt) {
    \\    uint32_t sh = amt & 127u;
    \\    if (sh == 0) return val;
    \\    if (sh >= 64) return _cx_u128_make(val.hi >> (sh - 64), 0);
    \\    return _cx_u128_make((val.lo >> sh) | (val.hi << (64 - sh)), val.hi >> sh);
    \\}
    \\static inline cx_i128 _cx_i128_ashr(cx_i128 val, uint32_t amt) {
    \\    uint32_t sh = amt & 127u;
    \\    if (sh == 0) return val;
    \\    int64_t s_hi = (int64_t)val.hi;
    \\    if (sh >= 64) {
    \\        uint64_t new_lo = (uint64_t)(s_hi >> (sh - 64));
    \\        uint64_t sign_fill = s_hi < 0 ? 0xFFFFFFFFFFFFFFFFull : 0ull;
    \\        return _cx_u128_make(new_lo, sign_fill);
    \\    }
    \\    return _cx_u128_make((val.lo >> sh) | (val.hi << (64 - sh)), (uint64_t)(s_hi >> sh));
    \\}
    \\static inline uint8_t _cx_u128_eq(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    return (lhs_v.lo == rhs_v.lo && lhs_v.hi == rhs_v.hi) ? 1u : 0u;
    \\}
    \\static inline uint8_t _cx_u128_ult(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    return (lhs_v.hi < rhs_v.hi || (lhs_v.hi == rhs_v.hi && lhs_v.lo < rhs_v.lo)) ? 1u : 0u;
    \\}
    \\static inline uint8_t _cx_i128_slt(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    int64_t l_hi = (int64_t)lhs_v.hi, r_hi = (int64_t)rhs_v.hi;
    \\    return (l_hi < r_hi || (l_hi == r_hi && lhs_v.lo < rhs_v.lo)) ? 1u : 0u;
    \\}
    \\static inline cx_u128 _cx_u128_add_chk(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    cx_u128 res_v = _cx_u128_add_wrap(lhs_v, rhs_v);
    \\    if (_cx_u128_ult(res_v, lhs_v)) _cx_rt_trap(2);
    \\    return res_v;
    \\}
    \\static inline cx_u128 _cx_u128_sub_chk(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    if (_cx_u128_ult(lhs_v, rhs_v)) _cx_rt_trap(2);
    \\    return _cx_u128_sub_wrap(lhs_v, rhs_v);
    \\}
    \\static inline cx_u128 _cx_u128_divrem(cx_u128 num_v, cx_u128 den_v, cx_u128 *rem_out) {
    \\    if (den_v.lo == 0 && den_v.hi == 0) _cx_rt_trap(2);
    \\    cx_u128 quot_v = _cx_u128_make(0, 0);
    \\    cx_u128 rem_v = _cx_u128_make(0, 0);
    \\    int bit_i = 127;
    \\    while (bit_i >= 0) {
    \\        rem_v = _cx_u128_shl(rem_v, 1);
    \\        uint64_t bit_b = (bit_i >= 64) ? ((num_v.hi >> (bit_i - 64)) & 1ull) : ((num_v.lo >> bit_i) & 1ull);
    \\        rem_v.lo |= bit_b;
    \\        if (!_cx_u128_ult(rem_v, den_v)) {
    \\            rem_v = _cx_u128_sub_wrap(rem_v, den_v);
    \\            if (bit_i >= 64) quot_v.hi |= (1ull << (bit_i - 64));
    \\            else quot_v.lo |= (1ull << bit_i);
    \\        }
    \\        bit_i -= 1;
    \\    }
    \\    if (rem_out != NULL) *rem_out = rem_v;
    \\    return quot_v;
    \\}
    \\static inline cx_u128 _cx_u128_mul_chk(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    cx_u128 prod_v = _cx_u128_mul_wrap(lhs_v, rhs_v);
    \\    if ((lhs_v.lo != 0 || lhs_v.hi != 0) && !_cx_u128_eq(_cx_u128_divrem(prod_v, lhs_v, NULL), rhs_v)) {
    \\        _cx_rt_trap(2);
    \\    }
    \\    return prod_v;
    \\}
    \\static inline cx_i128 _cx_i128_add_chk(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    cx_i128 res_v = _cx_u128_add_wrap(lhs_v, rhs_v);
    \\    uint64_t l_s = lhs_v.hi >> 63, r_s = rhs_v.hi >> 63, o_s = res_v.hi >> 63;
    \\    if (l_s == r_s && o_s != l_s) _cx_rt_trap(2);
    \\    return res_v;
    \\}
    \\static inline cx_i128 _cx_i128_sub_chk(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    cx_i128 res_v = _cx_u128_sub_wrap(lhs_v, rhs_v);
    \\    uint64_t l_s = lhs_v.hi >> 63, r_s = rhs_v.hi >> 63, o_s = res_v.hi >> 63;
    \\    if (l_s != r_s && o_s != l_s) _cx_rt_trap(2);
    \\    return res_v;
    \\}
    \\static inline cx_u128 _cx_i128_abs(cx_i128 val) {
    \\    return ((int64_t)val.hi < 0) ? _cx_u128_sub_wrap(_cx_u128_make(0, 0), val) : val;
    \\}
    \\static inline cx_i128 _cx_i128_mul_chk(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    int is_neg = (((int64_t)lhs_v.hi < 0) != ((int64_t)rhs_v.hi < 0));
    \\    cx_u128 mag_l = _cx_i128_abs(lhs_v), mag_r = _cx_i128_abs(rhs_v);
    \\    cx_u128 prod_u = _cx_u128_mul_chk(mag_l, mag_r);
    \\    cx_u128 lim_u = _cx_u128_make(is_neg ? 0ull : 0xFFFFFFFFFFFFFFFFull, is_neg ? 0x8000000000000000ull : 0x7FFFFFFFFFFFFFFFull);
    \\    if (_cx_u128_ult(lim_u, prod_u)) _cx_rt_trap(2);
    \\    return is_neg ? _cx_u128_sub_wrap(_cx_u128_make(0, 0), prod_u) : prod_u;
    \\}
    \\static inline cx_u128 _cx_u128_div_chk(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    return _cx_u128_divrem(lhs_v, rhs_v, NULL);
    \\}
    \\static inline cx_u128 _cx_u128_rem_chk(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    cx_u128 rem_v; (void)_cx_u128_divrem(lhs_v, rhs_v, &rem_v); return rem_v;
    \\}
    \\static inline cx_i128 _cx_i128_div_chk(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    if (rhs_v.lo == 0 && rhs_v.hi == 0) _cx_rt_trap(2);
    \\    if (lhs_v.lo == 0 && lhs_v.hi == 0x8000000000000000ull &&
    \\        rhs_v.lo == 0xFFFFFFFFFFFFFFFFull && rhs_v.hi == 0xFFFFFFFFFFFFFFFFull) _cx_rt_trap(2);
    \\    int is_neg = (((int64_t)lhs_v.hi < 0) != ((int64_t)rhs_v.hi < 0));
    \\    cx_u128 quot_u = _cx_u128_divrem(_cx_i128_abs(lhs_v), _cx_i128_abs(rhs_v), NULL);
    \\    return is_neg ? _cx_u128_sub_wrap(_cx_u128_make(0, 0), quot_u) : quot_u;
    \\}
    \\static inline cx_i128 _cx_i128_rem_chk(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    if (rhs_v.lo == 0 && rhs_v.hi == 0) _cx_rt_trap(2);
    \\    if (lhs_v.lo == 0 && lhs_v.hi == 0x8000000000000000ull &&
    \\        rhs_v.lo == 0xFFFFFFFFFFFFFFFFull && rhs_v.hi == 0xFFFFFFFFFFFFFFFFull) _cx_rt_trap(2);
    \\    cx_u128 rem_u; (void)_cx_u128_divrem(_cx_i128_abs(lhs_v), _cx_i128_abs(rhs_v), &rem_u);
    \\    return ((int64_t)lhs_v.hi < 0) ? _cx_u128_sub_wrap(_cx_u128_make(0, 0), rem_u) : rem_u;
    \\}
    \\#endif
    \\
    \\static inline uint32_t _cx_clz64(uint64_t val) {
    \\    uint32_t cnt = 0u;
    \\    while ((val & 0x8000000000000000ull) == 0ull) { cnt += 1u; val <<= 1u; }
    \\    return cnt;
    \\}
    \\static inline cx_u128 _cx_u128_add_sat(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    cx_u128 res_v = _cx_u128_add_wrap(lhs_v, rhs_v);
    \\    return _cx_u128_ult(res_v, lhs_v) ? _cx_u128_make(0xFFFFFFFFFFFFFFFFull, 0xFFFFFFFFFFFFFFFFull) : res_v;
    \\}
    \\static inline cx_u128 _cx_u128_sub_sat(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    return _cx_u128_ult(lhs_v, rhs_v) ? _cx_u128_make(0ull, 0ull) : _cx_u128_sub_wrap(lhs_v, rhs_v);
    \\}
    \\static inline cx_u128 _cx_u128_mul_sat(cx_u128 lhs_v, cx_u128 rhs_v) {
    \\    cx_u128 prod_v = _cx_u128_mul_wrap(lhs_v, rhs_v);
    \\    if ((_cx_u128_lo(lhs_v) != 0ull || _cx_u128_hi(lhs_v) != 0ull) &&
    \\        !_cx_u128_eq(_cx_u128_div_chk(prod_v, lhs_v), rhs_v)) {
    \\        return _cx_u128_make(0xFFFFFFFFFFFFFFFFull, 0xFFFFFFFFFFFFFFFFull);
    \\    }
    \\    return prod_v;
    \\}
    \\static inline cx_i128 _cx_i128_add_sat(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    cx_u128 lu_v = _cx_as_u128(lhs_v), ru_v = _cx_as_u128(rhs_v);
    \\    cx_u128 res_v = _cx_u128_add_wrap(lu_v, ru_v);
    \\    uint64_t l_s = _cx_u128_hi(lu_v) >> 63, r_s = _cx_u128_hi(ru_v) >> 63, o_s = _cx_u128_hi(res_v) >> 63;
    \\    if (l_s == r_s && o_s != l_s) {
    \\        return _cx_as_i128(l_s ? _cx_u128_make(0ull, 0x8000000000000000ull) : _cx_u128_make(0xFFFFFFFFFFFFFFFFull, 0x7FFFFFFFFFFFFFFFull));
    \\    }
    \\    return _cx_as_i128(res_v);
    \\}
    \\static inline cx_i128 _cx_i128_sub_sat(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    cx_u128 lu_v = _cx_as_u128(lhs_v), ru_v = _cx_as_u128(rhs_v);
    \\    cx_u128 res_v = _cx_u128_sub_wrap(lu_v, ru_v);
    \\    uint64_t l_s = _cx_u128_hi(lu_v) >> 63, r_s = _cx_u128_hi(ru_v) >> 63, o_s = _cx_u128_hi(res_v) >> 63;
    \\    if (l_s != r_s && o_s != l_s) {
    \\        return _cx_as_i128(l_s ? _cx_u128_make(0ull, 0x8000000000000000ull) : _cx_u128_make(0xFFFFFFFFFFFFFFFFull, 0x7FFFFFFFFFFFFFFFull));
    \\    }
    \\    return _cx_as_i128(res_v);
    \\}
    \\static inline cx_i128 _cx_i128_mul_sat(cx_i128 lhs_v, cx_i128 rhs_v) {
    \\    cx_u128 lu_v = _cx_as_u128(lhs_v), ru_v = _cx_as_u128(rhs_v);
    \\    int is_neg = (((int64_t)_cx_u128_hi(lu_v) < 0) != ((int64_t)_cx_u128_hi(ru_v) < 0));
    \\    cx_u128 mag_l = ((int64_t)_cx_u128_hi(lu_v) < 0) ? _cx_u128_sub_wrap(_cx_u128_make(0ull, 0ull), lu_v) : lu_v;
    \\    cx_u128 mag_r = ((int64_t)_cx_u128_hi(ru_v) < 0) ? _cx_u128_sub_wrap(_cx_u128_make(0ull, 0ull), ru_v) : ru_v;
    \\    cx_u128 prod_u = _cx_u128_mul_sat(mag_l, mag_r);
    \\    cx_u128 lim_u = _cx_u128_make(is_neg ? 0ull : 0xFFFFFFFFFFFFFFFFull, is_neg ? 0x8000000000000000ull : 0x7FFFFFFFFFFFFFFFull);
    \\    if (_cx_u128_ult(lim_u, prod_u)) return _cx_as_i128(lim_u);
    \\    return _cx_as_i128(is_neg ? _cx_u128_sub_wrap(_cx_u128_make(0ull, 0ull), prod_u) : prod_u);
    \\}
    \\static inline double _cx_u128_to_f64(cx_u128 val) {
    \\    uint64_t hi_w = _cx_u128_hi(val), lo_w = _cx_u128_lo(val);
    \\    if (hi_w == 0ull) return (double)lo_w;
    \\    uint32_t bit_len = 128u - _cx_clz64(hi_w);
    \\    uint32_t sh_amt = bit_len - 55u;
    \\    cx_u128 top_u = _cx_u128_lshr(val, sh_amt);
    \\    cx_u128 rem_u = _cx_u128_sub_wrap(val, _cx_u128_shl(top_u, sh_amt));
    \\    uint64_t sticky_b = (_cx_u128_lo(rem_u) != 0ull || _cx_u128_hi(rem_u) != 0ull) ? 1ull : 0ull;
    \\    uint64_t sig55 = _cx_u128_lo(top_u) | sticky_b;
    \\    uint32_t s1 = sh_amt > 52u ? 52u : sh_amt;
    \\    uint32_t s2 = sh_amt - s1;
    \\    return ((double)sig55 * (double)(1ull << s1)) * (double)(1ull << s2);
    \\}
    \\static inline float _cx_u128_to_f32(cx_u128 val) {
    \\    uint64_t hi_w = _cx_u128_hi(val), lo_w = _cx_u128_lo(val);
    \\    if (hi_w == 0ull) return (float)lo_w;
    \\    uint32_t bit_len = 128u - _cx_clz64(hi_w);
    \\    uint32_t sh_amt = bit_len - 26u;
    \\    cx_u128 top_u = _cx_u128_lshr(val, sh_amt);
    \\    cx_u128 rem_u = _cx_u128_sub_wrap(val, _cx_u128_shl(top_u, sh_amt));
    \\    uint64_t sticky_b = (_cx_u128_lo(rem_u) != 0ull || _cx_u128_hi(rem_u) != 0ull) ? 1ull : 0ull;
    \\    uint64_t sig26 = _cx_u128_lo(top_u) | sticky_b;
    \\    uint32_t s1 = sh_amt > 62u ? 62u : sh_amt;
    \\    uint32_t s2 = sh_amt - s1;
    \\    return ((float)sig26 * (float)(1ull << s1)) * (float)(1ull << s2);
    \\}
    \\static inline double _cx_i128_to_f64(cx_i128 val) {
    \\    cx_u128 u_val = _cx_as_u128(val);
    \\    if (((int64_t)_cx_u128_hi(u_val)) < 0) {
    \\        return -_cx_u128_to_f64(_cx_u128_sub_wrap(_cx_u128_make(0ull, 0ull), u_val));
    \\    }
    \\    return _cx_u128_to_f64(u_val);
    \\}
    \\static inline float _cx_i128_to_f32(cx_i128 val) {
    \\    cx_u128 u_val = _cx_as_u128(val);
    \\    if (((int64_t)_cx_u128_hi(u_val)) < 0) {
    \\        return -_cx_u128_to_f32(_cx_u128_sub_wrap(_cx_u128_make(0ull, 0ull), u_val));
    \\    }
    \\    return _cx_u128_to_f32(u_val);
    \\}
    \\static inline int64_t _cx_f64_to_i64(double val, double min_incl, double max_excl) {
    \\    if (isnan(val) || isinf(val)) _cx_rt_trap(2);
    \\    double tr_v = trunc(val);
    \\    if (tr_v < min_incl || tr_v >= max_excl) _cx_rt_trap(2);
    \\    return (int64_t)tr_v;
    \\}
    \\static inline uint64_t _cx_f64_to_u64(double val, double max_excl) {
    \\    if (isnan(val) || isinf(val)) _cx_rt_trap(2);
    \\    double tr_v = trunc(val);
    \\    if (tr_v < 0.0 || tr_v >= max_excl) _cx_rt_trap(2);
    \\    return (uint64_t)tr_v;
    \\}
    \\static inline cx_u128 _cx_f64_to_u128(double val) {
    \\    if (isnan(val) || isinf(val)) _cx_rt_trap(2);
    \\    double tr_v = trunc(val);
    \\    if (tr_v < 0.0 || tr_v >= 340282366920938463463374607431768211456.0) _cx_rt_trap(2);
    \\    double two64 = 18446744073709551616.0;
    \\    uint64_t hi_w = (uint64_t)(tr_v / two64);
    \\    uint64_t lo_w = (uint64_t)(tr_v - (double)hi_w * two64);
    \\    return _cx_u128_make(lo_w, hi_w);
    \\}
    \\static inline cx_i128 _cx_f64_to_i128(double val) {
    \\    if (isnan(val) || isinf(val)) _cx_rt_trap(2);
    \\    double tr_v = trunc(val);
    \\    if (tr_v < -170141183460469231731687303715884105728.0 ||
    \\        tr_v >= 170141183460469231731687303715884105728.0) _cx_rt_trap(2);
    \\    if (tr_v < 0.0) {
    \\        cx_u128 mag_u = _cx_f64_to_u128(-tr_v);
    \\        return _cx_as_i128(_cx_u128_sub_wrap(_cx_u128_make(0ull, 0ull), mag_u));
    \\    }
    \\    return _cx_as_i128(_cx_f64_to_u128(tr_v));
    \\}
    \\
;

/// Hosted 128-bit integer decimal formatting helpers (`snprintf`-backed, omitted in `-nostdlib` freestanding mode).
const C99_HOSTED_ARITH_FMT: []const u8 =
    \\static size_t _cx_fmt_u128(char *out_buf, cx_u128 val) {
    \\    if (_cx_u128_hi(val) == 0ull) {
    \\        int len_n = snprintf(out_buf, 64u, "%llu", (unsigned long long)_cx_u128_lo(val));
    \\        return len_n > 0 ? (size_t)len_n : 0u;
    \\    }
    \\    char rev_buf[48];
    \\    size_t rev_n = 0u;
    \\    cx_u128 cur_v = val;
    \\    cx_u128 ten_v = _cx_u128_make(10ull, 0ull);
    \\    while (_cx_u128_lo(cur_v) != 0ull || _cx_u128_hi(cur_v) != 0ull) {
    \\        cx_u128 rem_v = _cx_u128_rem_chk(cur_v, ten_v);
    \\        rev_buf[rev_n] = (char)('0' + (int)_cx_u128_lo(rem_v));
    \\        rev_n += 1u;
    \\        cur_v = _cx_u128_div_chk(cur_v, ten_v);
    \\    }
    \\    size_t idx_i = 0u;
    \\    while (idx_i < rev_n) {
    \\        out_buf[idx_i] = rev_buf[rev_n - 1u - idx_i];
    \\        idx_i += 1u;
    \\    }
    \\    out_buf[rev_n] = '\0';
    \\    return rev_n;
    \\}
    \\static size_t _cx_fmt_i128(char *out_buf, cx_i128 val) {
    \\    cx_u128 u_val = _cx_as_u128(val);
    \\    if (((int64_t)_cx_u128_hi(u_val)) < 0) {
    \\        out_buf[0] = '-';
    \\        return 1u + _cx_fmt_u128(out_buf + 1, _cx_u128_sub_wrap(_cx_u128_make(0ull, 0ull), u_val));
    \\    }
    \\    return _cx_fmt_u128(out_buf, u_val);
    \\}
    \\
;

/// Minimal zero-libc freestanding C99 preamble (`<stdint.h>`, `<stddef.h>`, `<stdbool.h>`, `<float.h>` only).
const C99_FREESTANDING_PREAMBLE: []const u8 =
    \\#include <stdint.h>
    \\#include <stddef.h>
    \\#include <stdbool.h>
    \\#include <float.h>
    \\
    \\#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L && !defined(__wasm__)
    \\#define CX_THREAD_LOCAL _Thread_local
    \\#elif defined(_MSC_VER)
    \\#define CX_THREAD_LOCAL __declspec(thread)
    \\#elif (defined(__GNUC__) || defined(__clang__)) && !defined(__wasm__)
    \\#define CX_THREAD_LOCAL __thread
    \\#else
    \\#define CX_THREAD_LOCAL
    \\#endif
    \\
    \\static inline void _cx_fs_memcpy(uint8_t *dst_p, const uint8_t *src_p, size_t byte_n) {
    \\    size_t idx_i = 0u;
    \\    while (idx_i < byte_n) { dst_p[idx_i] = src_p[idx_i]; idx_i += 1u; }
    \\}
    \\static inline void _cx_fs_memset(uint8_t *dst_p, uint8_t fill_b, size_t byte_n) {
    \\    size_t idx_i = 0u;
    \\    while (idx_i < byte_n) { dst_p[idx_i] = fill_b; idx_i += 1u; }
    \\}
    \\static inline int _cx_fs_memcmp(const uint8_t *lhs_p, const uint8_t *rhs_p, size_t byte_n) {
    \\    size_t idx_i = 0u;
    \\    while (idx_i < byte_n) {
    \\        if (lhs_p[idx_i] != rhs_p[idx_i]) return (int)lhs_p[idx_i] - (int)rhs_p[idx_i];
    \\        idx_i += 1u;
    \\    }
    \\    return 0;
    \\}
    \\#define memcpy(dst_p, src_p, byte_n) _cx_fs_memcpy((uint8_t *)(dst_p), (const uint8_t *)(src_p), (size_t)(byte_n))
    \\#define memset(dst_p, fill_b, byte_n) _cx_fs_memset((uint8_t *)(dst_p), (uint8_t)(fill_b), (size_t)(byte_n))
    \\#define memcmp(lhs_p, rhs_p, byte_n) _cx_fs_memcmp((const uint8_t *)(lhs_p), (const uint8_t *)(rhs_p), (size_t)(byte_n))
    \\
    \\static inline int _cx_fs_isnan(double val) {
    \\    uint64_t bits_u = 0ull;
    \\    _cx_fs_memcpy((uint8_t *)&bits_u, (const uint8_t *)&val, 8u);
    \\    return ((bits_u & 0x7FF0000000000000ull) == 0x7FF0000000000000ull) && ((bits_u & 0x000FFFFFFFFFFFFFull) != 0ull);
    \\}
    \\static inline int _cx_fs_isinf(double val) {
    \\    uint64_t bits_u = 0ull;
    \\    _cx_fs_memcpy((uint8_t *)&bits_u, (const uint8_t *)&val, 8u);
    \\    return ((bits_u & 0x7FFFFFFFFFFFFFFFull) == 0x7FF0000000000000ull);
    \\}
    \\static inline double _cx_fs_trunc(double val) {
    \\    uint64_t bits_u = 0ull;
    \\    _cx_fs_memcpy((uint8_t *)&bits_u, (const uint8_t *)&val, 8u);
    \\    int32_t exp_e = (int32_t)((bits_u >> 52u) & 0x7FFull) - 1023;
    \\    if (exp_e < 0) {
    \\        uint64_t zero_s = bits_u & 0x8000000000000000ull;
    \\        double out_z = 0.0;
    \\        _cx_fs_memcpy((uint8_t *)&out_z, (const uint8_t *)&zero_s, 8u);
    \\        return out_z;
    \\    }
    \\    if (exp_e >= 52) return val;
    \\    uint64_t frac_mask = (1ull << (uint32_t)(52 - exp_e)) - 1ull;
    \\    uint64_t masked_u = bits_u & ~frac_mask;
    \\    double out_v = 0.0;
    \\    _cx_fs_memcpy((uint8_t *)&out_v, (const uint8_t *)&masked_u, 8u);
    \\    return out_v;
    \\}
    \\#define isnan _cx_fs_isnan
    \\#define isinf _cx_fs_isinf
    \\#define trunc _cx_fs_trunc
    \\
    \\typedef void (*_cx_fn_slot_t)(void);
    \\typedef struct cx_str_s { uint8_t *ptr; uintptr_t len; } cx_str_t;
    \\typedef struct cx_source_loc_data_s {
    \\    cx_str_t file;
    \\    cx_str_t fn_name;
    \\    uint32_t line;
    \\    uint32_t col;
    \\} cx_source_loc_data_t;
    \\typedef const cx_source_loc_data_t *cx_source_loc_t;
    \\typedef struct cx_fmt_spec_s {
    \\    uint32_t flags_and_fill;
    \\    uint16_t width_or_none;
    \\    uint16_t precision_or_none;
    \\} cx_fmt_spec_t;
    \\typedef struct _cx_rt_buf_s {
    \\    uint8_t *data;
    \\    size_t len;
    \\    size_t cap;
    \\} _cx_rt_buf_t;
    \\typedef void (*cx_fmt_fn_t)(_cx_rt_buf_t *, const uint8_t *, uint32_t, uint32_t);
    \\typedef struct cx_fmt_arg_s {
    \\    const uint8_t *data;
    \\    cx_fmt_fn_t fmt_fn;
    \\    cx_fmt_spec_t spec;
    \\} cx_fmt_arg_t;
    \\typedef struct cx_fmt_args_s {
    \\    const cx_str_t *pieces_ptr;
    \\    uintptr_t pieces_len;
    \\    const cx_fmt_arg_t *args_ptr;
    \\    uintptr_t args_len;
    \\} cx_fmt_args_t;
    \\typedef struct cx_bencher_s {
    \\    uint8_t *state_ptr;
    \\    uintptr_t iters;
    \\} cx_bencher_t;
    \\
    \\static inline void _cx_rt_drop_trace(int64_t drop_id) { (void)drop_id; }
    \\#if defined(__GNUC__) || defined(__clang__)
    \\__attribute__((noreturn))
    \\#endif
    \\static void _cx_rt_trap(uint32_t trap_reason) {
    \\    (void)trap_reason;
    \\    __builtin_trap();
    \\}
    \\static inline intptr_t _cx_rt_sys_write(int32_t fd_num, const uint8_t *buf_ptr, size_t buf_len) {
    \\    (void)fd_num; (void)buf_ptr; (void)buf_len;
    \\    return (intptr_t)(-1);
    \\}
    \\#if defined(__GNUC__) || defined(__clang__)
    \\__attribute__((noreturn))
    \\#endif
    \\static void _cx_rt_sys_exit(int32_t status_code) {
    \\    (void)status_code;
    \\    __builtin_trap();
    \\}
    \\#if defined(__GNUC__) || defined(__clang__)
    \\__attribute__((noreturn))
    \\#endif
    \\static void _cx_rt_panic(const uint8_t *msg_ptr, size_t msg_len) {
    \\    (void)msg_ptr; (void)msg_len;
    \\    __builtin_trap();
    \\}
    \\static inline uint8_t _cx_str_eq(
    \\    const uint8_t *lhs_ptr,
    \\    size_t lhs_len,
    \\    const uint8_t *rhs_ptr,
    \\    size_t rhs_len
    \\) {
    \\    if (lhs_len != rhs_len) return 0u;
    \\    if (lhs_len == 0u) return 1u;
    \\    return _cx_fs_memcmp(lhs_ptr, rhs_ptr, lhs_len) == 0 ? 1u : 0u;
    \\}
    \\static inline uint8_t _cx_source_loc_eq(cx_source_loc_t lhs_loc, cx_source_loc_t rhs_loc) {
    \\    if (lhs_loc == rhs_loc) return 1u;
    \\    if (lhs_loc == NULL || rhs_loc == NULL) return 0u;
    \\    if (lhs_loc->line != rhs_loc->line || lhs_loc->col != rhs_loc->col) return 0u;
    \\    if (!_cx_str_eq(lhs_loc->file.ptr, (size_t)lhs_loc->file.len, rhs_loc->file.ptr, (size_t)rhs_loc->file.len)) return 0u;
    \\    return _cx_str_eq(lhs_loc->fn_name.ptr, (size_t)lhs_loc->fn_name.len, rhs_loc->fn_name.ptr, (size_t)rhs_loc->fn_name.len);
    \\}
    \\static inline uint8_t _cx_fmt_spec_eq(cx_fmt_spec_t lhs_s, cx_fmt_spec_t rhs_s) {
    \\    return (lhs_s.flags_and_fill == rhs_s.flags_and_fill &&
    \\        lhs_s.width_or_none == rhs_s.width_or_none &&
    \\        lhs_s.precision_or_none == rhs_s.precision_or_none) ? 1u : 0u;
    \\}
    \\static const uint8_t __attribute__((aligned(16))) _cx_empty_rodata[1u] = { 0x00u };
    \\static inline uint8_t _cx_read_u8(const uint8_t *base_p, size_t off_b) { return base_p[off_b]; }
    \\static inline uint16_t _cx_read_u16(const uint8_t *base_p, size_t off_b) {
    \\    uint16_t out_v = 0u; _cx_fs_memcpy((uint8_t *)&out_v, base_p + off_b, sizeof(out_v)); return out_v;
    \\}
    \\static inline uint32_t _cx_read_u32(const uint8_t *base_p, size_t off_b) {
    \\    uint32_t out_v = 0u; _cx_fs_memcpy((uint8_t *)&out_v, base_p + off_b, sizeof(out_v)); return out_v;
    \\}
    \\static inline uint64_t _cx_read_u64(const uint8_t *base_p, size_t off_b) {
    \\    uint64_t out_v = 0u; _cx_fs_memcpy((uint8_t *)&out_v, base_p + off_b, sizeof(out_v)); return out_v;
    \\}
    \\static inline void _cx_write_u8(uint8_t *base_p, size_t off_b, uint8_t val) { base_p[off_b] = val; }
    \\static inline void _cx_write_u16(uint8_t *base_p, size_t off_b, uint16_t val) {
    \\    _cx_fs_memcpy(base_p + off_b, (const uint8_t *)&val, sizeof(val));
    \\}
    \\static inline void _cx_write_u32(uint8_t *base_p, size_t off_b, uint32_t val) {
    \\    _cx_fs_memcpy(base_p + off_b, (const uint8_t *)&val, sizeof(val));
    \\}
    \\static inline void _cx_write_u64(uint8_t *base_p, size_t off_b, uint64_t val) {
    \\    _cx_fs_memcpy(base_p + off_b, (const uint8_t *)&val, sizeof(val));
    \\}
    \\
;

/// Freestanding tail closing the runtime prelude after `C99_ARITH_HELPERS`.
const C99_FREESTANDING_TAIL: []const u8 =
    \\static inline cx_str_t _cx_rt_buf_finish_str(_cx_rt_buf_t *out_b) {
    \\    (void)out_b;
    \\    cx_str_t res_s = { (uint8_t *)_cx_empty_rodata, 0u };
    \\    return res_s;
    \\}
    \\#if defined(__GNUC__) || defined(__clang__)
    \\__attribute__((noreturn))
    \\#endif
    \\static void _cx_rt_panic_fmt_args(const cx_fmt_args_t *fargs) {
    \\    _cx_rt_buf_t msg_b = { NULL, 0u, 0u };
    \\    (void)fargs;
    \\    _cx_rt_panic(msg_b.data, msg_b.len);
    \\}
    \\
;

/// Static C99 formatting helpers for `FmtSpec`, `FmtArgs`, `MirIntrinsicKind.fmt_value`, and `@panic(FmtArgs)`.
const C99_FMT_HELPERS: []const u8 =
    \\static void _cx_rt_buf_reserve(_cx_rt_buf_t *out_b, size_t extra_n) {
    \\    if (extra_n == 0u) return;
    \\    if (extra_n > ((size_t)-1) - out_b->len) _cx_rt_trap(1u);
    \\    size_t needed_cap = out_b->len + extra_n;
    \\    if (needed_cap <= out_b->cap) return;
    \\    size_t next_cap = out_b->cap == 0u ? 64u : out_b->cap;
    \\    while (next_cap < needed_cap) {
    \\        if (next_cap > (((size_t)-1) >> 1)) { next_cap = needed_cap; break; }
    \\        next_cap <<= 1;
    \\    }
    \\    uint8_t *new_p = (uint8_t *)realloc(out_b->data, next_cap);
    \\    if (new_p == NULL) _cx_rt_trap(0u);
    \\    out_b->data = new_p;
    \\    out_b->cap = next_cap;
    \\}
    \\static inline void _cx_rt_buf_push_bytes(_cx_rt_buf_t *out_b, const uint8_t *src_p, size_t src_n) {
    \\    if (src_n == 0u || src_p == NULL) return;
    \\    _cx_rt_buf_reserve(out_b, src_n);
    \\    memcpy(out_b->data + out_b->len, src_p, src_n);
    \\    out_b->len += src_n;
    \\}
    \\static inline void _cx_rt_buf_push_cstr(_cx_rt_buf_t *out_b, const char *c_str) {
    \\    _cx_rt_buf_push_bytes(out_b, (const uint8_t *)c_str, strlen(c_str));
    \\}
    \\static inline void _cx_rt_buf_push_byte(_cx_rt_buf_t *out_b, uint8_t ch_b) {
    \\    _cx_rt_buf_reserve(out_b, 1u);
    \\    out_b->data[out_b->len] = ch_b;
    \\    out_b->len += 1u;
    \\}
    \\static size_t _cx_rt_encode_utf8(uint32_t cp_v, uint8_t out_u8[4]) {
    \\    if (cp_v > 0x10FFFFu || (cp_v >= 0xD800u && cp_v <= 0xDFFFu)) cp_v = 0xFFFDu;
    \\    if (cp_v < 0x80u) { out_u8[0] = (uint8_t)cp_v; return 1u; }
    \\    if (cp_v < 0x800u) {
    \\        out_u8[0] = (uint8_t)(0xC0u | (cp_v >> 6));
    \\        out_u8[1] = (uint8_t)(0x80u | (cp_v & 0x3Fu));
    \\        return 2u;
    \\    }
    \\    if (cp_v < 0x10000u) {
    \\        out_u8[0] = (uint8_t)(0xE0u | (cp_v >> 12));
    \\        out_u8[1] = (uint8_t)(0x80u | ((cp_v >> 6) & 0x3Fu));
    \\        out_u8[2] = (uint8_t)(0x80u | (cp_v & 0x3Fu));
    \\        return 3u;
    \\    }
    \\    out_u8[0] = (uint8_t)(0xF0u | (cp_v >> 18));
    \\    out_u8[1] = (uint8_t)(0x80u | ((cp_v >> 12) & 0x3Fu));
    \\    out_u8[2] = (uint8_t)(0x80u | ((cp_v >> 6) & 0x3Fu));
    \\    out_u8[3] = (uint8_t)(0x80u | (cp_v & 0x3Fu));
    \\    return 4u;
    \\}
    \\static void _cx_rt_buf_push_cp_rep(_cx_rt_buf_t *out_b, uint32_t cp_v, size_t rep_n) {
    \\    if (rep_n == 0u) return;
    \\    if (cp_v == 0u || cp_v > 0x10FFFFu) cp_v = 0x20u;
    \\    uint8_t u8_seq[4];
    \\    size_t seq_n = _cx_rt_encode_utf8(cp_v, u8_seq);
    \\    while (rep_n > 0u) {
    \\        _cx_rt_buf_push_bytes(out_b, u8_seq, seq_n);
    \\        rep_n -= 1u;
    \\    }
    \\}
    \\static inline size_t _cx_rt_utf8_seq_len(uint8_t lead_b) {
    \\    if ((lead_b & 0x80u) == 0u) return 1u;
    \\    if ((lead_b & 0xE0u) == 0xC0u) return 2u;
    \\    if ((lead_b & 0xF0u) == 0xE0u) return 3u;
    \\    if ((lead_b & 0xF8u) == 0xF0u) return 4u;
    \\    return 1u;
    \\}
    \\static size_t _cx_rt_count_utf8_cps(const uint8_t *txt_p, size_t txt_n) {
    \\    size_t idx_i = 0u, cnt_n = 0u;
    \\    while (idx_i < txt_n) {
    \\        size_t step_n = _cx_rt_utf8_seq_len(txt_p[idx_i]);
    \\        if (idx_i + step_n > txt_n) step_n = txt_n - idx_i;
    \\        idx_i += step_n;
    \\        cnt_n += 1u;
    \\    }
    \\    return cnt_n;
    \\}
    \\static size_t _cx_rt_trunc_utf8_cps(const uint8_t *txt_p, size_t txt_n, size_t max_cps) {
    \\    size_t idx_i = 0u, seen_n = 0u;
    \\    while (idx_i < txt_n && seen_n < max_cps) {
    \\        size_t step_n = _cx_rt_utf8_seq_len(txt_p[idx_i]);
    \\        if (idx_i + step_n > txt_n) break;
    \\        idx_i += step_n;
    \\        seen_n += 1u;
    \\    }
    \\    return idx_i;
    \\}
    \\static void _cx_rt_buf_pad_str(
    \\    _cx_rt_buf_t *out_b,
    \\    const uint8_t *body_p,
    \\    size_t body_n,
    \\    uint32_t spec_lo,
    \\    uint32_t spec_hi,
    \\    uint8_t def_right
    \\) {
    \\    uint32_t width_u16 = spec_hi & 0xFFFFu;
    \\    if (width_u16 == 0xFFFFu) {
    \\        _cx_rt_buf_push_bytes(out_b, body_p, body_n);
    \\        return;
    \\    }
    \\    size_t cols_n = _cx_rt_count_utf8_cps(body_p, body_n);
    \\    if (cols_n >= (size_t)width_u16) {
    \\        _cx_rt_buf_push_bytes(out_b, body_p, body_n);
    \\        return;
    \\    }
    \\    size_t pad_n = (size_t)width_u16 - cols_n;
    \\    uint32_t fill_cp = spec_lo & 0x1FFFFFu;
    \\    if (fill_cp == 0u || fill_cp > 0x10FFFFu) fill_cp = 0x20u;
    \\    uint32_t align_m = (spec_lo >> 21) & 3u;
    \\    if (align_m == 0u) align_m = def_right ? 3u : 1u;
    \\    if (align_m == 1u) {
    \\        _cx_rt_buf_push_bytes(out_b, body_p, body_n);
    \\        _cx_rt_buf_push_cp_rep(out_b, fill_cp, pad_n);
    \\    } else if (align_m == 2u) {
    \\        size_t pad_l = pad_n / 2u;
    \\        _cx_rt_buf_push_cp_rep(out_b, fill_cp, pad_l);
    \\        _cx_rt_buf_push_bytes(out_b, body_p, body_n);
    \\        _cx_rt_buf_push_cp_rep(out_b, fill_cp, pad_n - pad_l);
    \\    } else {
    \\        _cx_rt_buf_push_cp_rep(out_b, fill_cp, pad_n);
    \\        _cx_rt_buf_push_bytes(out_b, body_p, body_n);
    \\    }
    \\}
    \\static void _cx_rt_fmt_u128_spec(
    \\    _cx_rt_buf_t *out_b,
    \\    cx_u128 mag_v,
    \\    uint8_t is_neg,
    \\    uint32_t spec_lo,
    \\    uint32_t spec_hi
    \\) {
    \\    uint32_t align_m = (spec_lo >> 21) & 3u;
    \\    uint32_t sign_m = (spec_lo >> 23) & 3u;
    \\    uint8_t is_alt = (uint8_t)((spec_lo >> 25) & 1u);
    \\    uint8_t is_zpad = (uint8_t)((spec_lo >> 26) & 1u);
    \\    uint32_t verb_c = (spec_lo >> 27) & 0xFu;
    \\    uint32_t radix_n = 10u;
    \\    uint8_t is_upper = 0u;
    \\    const char *alt_pfx = "";
    \\    if (verb_c == 2u || verb_c == 9u) { radix_n = 16u; if (is_alt || verb_c == 9u) alt_pfx = "0x"; }
    \\    else if (verb_c == 3u) { radix_n = 16u; is_upper = 1u; if (is_alt) alt_pfx = "0X"; }
    \\    else if (verb_c == 4u) { radix_n = 2u; if (is_alt) alt_pfx = "0b"; }
    \\    else if (verb_c == 5u) { radix_n = 8u; if (is_alt) alt_pfx = "0o"; }
    \\    const char *sign_pfx = is_neg ? "-" : (sign_m == 1u ? "+" : "");
    \\    uint8_t rev_digs[136];
    \\    size_t dig_n = 0u;
    \\    if (_cx_u128_lo(mag_v) == 0ull && _cx_u128_hi(mag_v) == 0ull) {
    \\        rev_digs[0] = '0';
    \\        dig_n = 1u;
    \\    } else {
    \\        cx_u128 cur_v = mag_v;
    \\        cx_u128 rad_v = _cx_u128_make((uint64_t)radix_n, 0ull);
    \\        const char *hex_tab = is_upper ? "0123456789ABCDEF" : "0123456789abcdef";
    \\        while (_cx_u128_lo(cur_v) != 0ull || _cx_u128_hi(cur_v) != 0ull) {
    \\            cx_u128 rem_v = _cx_u128_rem_chk(cur_v, rad_v);
    \\            rev_digs[dig_n] = (uint8_t)hex_tab[_cx_u128_lo(rem_v) & 0xFull];
    \\            dig_n += 1u;
    \\            cur_v = _cx_u128_div_chk(cur_v, rad_v);
    \\        }
    \\    }
    \\    size_t sign_len = strlen(sign_pfx);
    \\    size_t alt_len = strlen(alt_pfx);
    \\    uint32_t width_u16 = spec_hi & 0xFFFFu;
    \\    if (is_zpad && align_m == 0u && width_u16 != 0xFFFFu) {
    \\        size_t cur_tot = sign_len + alt_len + dig_n;
    \\        _cx_rt_buf_push_bytes(out_b, (const uint8_t *)sign_pfx, sign_len);
    \\        _cx_rt_buf_push_bytes(out_b, (const uint8_t *)alt_pfx, alt_len);
    \\        if ((size_t)width_u16 > cur_tot) _cx_rt_buf_push_cp_rep(out_b, '0', (size_t)width_u16 - cur_tot);
    \\        while (dig_n > 0u) { dig_n -= 1u; _cx_rt_buf_push_byte(out_b, rev_digs[dig_n]); }
    \\        return;
    \\    }
    \\    uint8_t num_tmp[160];
    \\    size_t pos_n = 0u;
    \\    if (sign_len > 0u) { memcpy(num_tmp + pos_n, sign_pfx, sign_len); pos_n += sign_len; }
    \\    if (alt_len > 0u) { memcpy(num_tmp + pos_n, alt_pfx, alt_len); pos_n += alt_len; }
    \\    while (dig_n > 0u) { dig_n -= 1u; num_tmp[pos_n] = rev_digs[dig_n]; pos_n += 1u; }
    \\    _cx_rt_buf_pad_str(out_b, num_tmp, pos_n, spec_lo, spec_hi, 1u);
    \\}
    \\static void _cx_rt_fmt_i128_spec(_cx_rt_buf_t *out_b, cx_i128 sval, uint32_t spec_lo, uint32_t spec_hi) {
    \\    uint32_t verb_c = (spec_lo >> 27) & 0xFu;
    \\    cx_u128 uval = _cx_as_u128(sval);
    \\    if (verb_c >= 2u && verb_c <= 5u) {
    \\        _cx_rt_fmt_u128_spec(out_b, uval, 0u, spec_lo, spec_hi);
    \\        return;
    \\    }
    \\    if (((int64_t)_cx_u128_hi(uval)) < 0) {
    \\        _cx_rt_fmt_u128_spec(out_b, _cx_u128_sub_wrap(_cx_u128_make(0ull, 0ull), uval), 1u, spec_lo, spec_hi);
    \\    } else {
    \\        _cx_rt_fmt_u128_spec(out_b, uval, 0u, spec_lo, spec_hi);
    \\    }
    \\}
    \\static void _cx_rt_fmt_f64_spec(_cx_rt_buf_t *out_b, double fval, uint32_t spec_lo, uint32_t spec_hi) {
    \\    uint32_t align_m = (spec_lo >> 21) & 3u;
    \\    uint32_t sign_m = (spec_lo >> 23) & 3u;
    \\    uint8_t is_zpad = (uint8_t)((spec_lo >> 26) & 1u);
    \\    uint32_t verb_c = (spec_lo >> 27) & 0xFu;
    \\    uint32_t width_u16 = spec_hi & 0xFFFFu;
    \\    uint32_t prec_u16 = (spec_hi >> 16) & 0xFFFFu;
    \\    if (isnan(fval)) {
    \\        const char *nan_s = verb_c == 7u ? "NAN" : "nan";
    \\        _cx_rt_buf_pad_str(out_b, (const uint8_t *)nan_s, 3u, spec_lo, spec_hi, 1u);
    \\        return;
    \\    }
    \\    uint64_t fbits = 0ull;
    \\    memcpy(&fbits, &fval, 8u);
    \\    uint8_t is_neg = (uint8_t)((fbits >> 63) & 1ull);
    \\    const char *sign_pfx = is_neg ? "-" : (sign_m == 1u ? "+" : "");
    \\    size_t sign_len = strlen(sign_pfx);
    \\    if (isinf(fval)) {
    \\        char inf_b[8];
    \\        int inf_n = snprintf(inf_b, sizeof(inf_b), verb_c == 7u ? "%sINF" : "%sinf", sign_pfx);
    \\        _cx_rt_buf_pad_str(out_b, (const uint8_t *)inf_b, inf_n > 0 ? (size_t)inf_n : 0u, spec_lo, spec_hi, 1u);
    \\        return;
    \\    }
    \\    double abs_v = is_neg ? -fval : fval;
    \\    char body_b[160];
    \\    int body_i = 0;
    \\    if (verb_c == 6u || verb_c == 7u) {
    \\        int eff_p = prec_u16 == 0xFFFFu ? 6 : (prec_u16 > 32u ? 32 : (int)prec_u16);
    \\        body_i = snprintf(body_b, sizeof(body_b), verb_c == 7u ? "%.*E" : "%.*e", eff_p, abs_v);
    \\        if (body_i >= 5) {
    \\            int exp_pos = body_i - 5;
    \\            while (exp_pos > 0 && body_b[exp_pos] != 'e' && body_b[exp_pos] != 'E') exp_pos -= 1;
    \\            if ((body_b[exp_pos] == 'e' || body_b[exp_pos] == 'E') &&
    \\                (body_b[exp_pos + 1] == '+' || body_b[exp_pos + 1] == '-') &&
    \\                body_b[exp_pos + 2] == '0' && (body_i - (exp_pos + 2)) >= 3) {
    \\                memmove(&body_b[exp_pos + 2], &body_b[exp_pos + 3], (size_t)(body_i - (exp_pos + 2)));
    \\                body_i -= 1;
    \\            }
    \\        }
    \\    } else if (verb_c == 8u || prec_u16 != 0xFFFFu) {
    \\        int eff_p = prec_u16 == 0xFFFFu ? 6 : (prec_u16 > 32u ? 32 : (int)prec_u16);
    \\        body_i = snprintf(body_b, sizeof(body_b), "%.*f", eff_p, abs_v);
    \\    } else {
    \\        body_i = snprintf(body_b, sizeof(body_b), "%.15g", abs_v);
    \\        if (body_i > 0) {
    \\            int ep = 0;
    \\            while (ep < body_i && body_b[ep] != 'e' && body_b[ep] != 'E') ep += 1;
    \\            if (ep < body_i) {
    \\                int rd = ep + 1;
    \\                int wr = ep + 1;
    \\                if (rd < body_i && body_b[rd] == '-') { body_b[wr] = '-'; wr += 1; rd += 1; }
    \\                else if (rd < body_i && body_b[rd] == '+') { rd += 1; }
    \\                while (rd + 1 < body_i && body_b[rd] == '0') rd += 1;
    \\                while (rd < body_i) { body_b[wr] = body_b[rd]; wr += 1; rd += 1; }
    \\                body_i = wr;
    \\                body_b[body_i] = '\0';
    \\            }
    \\        }
    \\    }
    \\    size_t body_len = body_i > 0 ? (size_t)body_i : 0u;
    \\    if (is_zpad && align_m == 0u && width_u16 != 0xFFFFu) {
    \\        size_t cur_tot = sign_len + body_len;
    \\        _cx_rt_buf_push_bytes(out_b, (const uint8_t *)sign_pfx, sign_len);
    \\        if ((size_t)width_u16 > cur_tot) _cx_rt_buf_push_cp_rep(out_b, '0', (size_t)width_u16 - cur_tot);
    \\        _cx_rt_buf_push_bytes(out_b, (const uint8_t *)body_b, body_len);
    \\        return;
    \\    }
    \\    uint8_t full_b[176];
    \\    if (sign_len > 0u) memcpy(full_b, sign_pfx, sign_len);
    \\    if (body_len > 0u) memcpy(full_b + sign_len, body_b, body_len);
    \\    _cx_rt_buf_pad_str(out_b, full_b, sign_len + body_len, spec_lo, spec_hi, 1u);
    \\}
    \\static void _cx_rt_push_escaped_cp(_cx_rt_buf_t *out_b, uint32_t cp_v, uint8_t is_str_ctx) {
    \\    if (cp_v == '\n') { _cx_rt_buf_push_cstr(out_b, "\\n"); return; }
    \\    if (cp_v == '\r') { _cx_rt_buf_push_cstr(out_b, "\\r"); return; }
    \\    if (cp_v == '\t') { _cx_rt_buf_push_cstr(out_b, "\\t"); return; }
    \\    if (cp_v == '\\') { _cx_rt_buf_push_cstr(out_b, "\\\\"); return; }
    \\    if (cp_v == 0u) { _cx_rt_buf_push_cstr(out_b, "\\0"); return; }
    \\    if (cp_v == '"') { _cx_rt_buf_push_cstr(out_b, is_str_ctx ? "\\\"" : "\""); return; }
    \\    if (cp_v == '\'') { _cx_rt_buf_push_cstr(out_b, is_str_ctx ? "'" : "\\'"); return; }
    \\    if (cp_v < 0x20u || cp_v == 0x7Fu) {
    \\        char esc_b[16];
    \\        int esc_n = snprintf(esc_b, sizeof(esc_b), "\\u{%x}", (unsigned int)cp_v);
    \\        if (esc_n > 0) _cx_rt_buf_push_bytes(out_b, (const uint8_t *)esc_b, (size_t)esc_n);
    \\        return;
    \\    }
    \\    uint8_t u8_b[4];
    \\    size_t u8_n = _cx_rt_encode_utf8(cp_v, u8_b);
    \\    _cx_rt_buf_push_bytes(out_b, u8_b, u8_n);
    \\}
    \\static uint32_t _cx_rt_decode_utf8_at(const uint8_t *src_p, size_t rem_n, size_t *step_out) {
    \\    uint8_t b0 = src_p[0];
    \\    if ((b0 & 0x80u) == 0u) { *step_out = 1u; return (uint32_t)b0; }
    \\    if ((b0 & 0xE0u) == 0xC0u && rem_n >= 2u && (src_p[1] & 0xC0u) == 0x80u) {
    \\        uint32_t cp = ((uint32_t)(b0 & 0x1Fu) << 6) | (uint32_t)(src_p[1] & 0x3Fu);
    \\        if (cp >= 0x80u) { *step_out = 2u; return cp; }
    \\    } else if ((b0 & 0xF0u) == 0xE0u && rem_n >= 3u &&
    \\        (src_p[1] & 0xC0u) == 0x80u && (src_p[2] & 0xC0u) == 0x80u) {
    \\        uint32_t cp = ((uint32_t)(b0 & 0x0Fu) << 12) |
    \\            ((uint32_t)(src_p[1] & 0x3Fu) << 6) | (uint32_t)(src_p[2] & 0x3Fu);
    \\        if (cp >= 0x800u && (cp < 0xD800u || cp > 0xDFFFu)) { *step_out = 3u; return cp; }
    \\    } else if ((b0 & 0xF8u) == 0xF0u && rem_n >= 4u &&
    \\        (src_p[1] & 0xC0u) == 0x80u && (src_p[2] & 0xC0u) == 0x80u && (src_p[3] & 0xC0u) == 0x80u) {
    \\        uint32_t cp = ((uint32_t)(b0 & 0x07u) << 18) | ((uint32_t)(src_p[1] & 0x3Fu) << 12) |
    \\            ((uint32_t)(src_p[2] & 0x3Fu) << 6) | (uint32_t)(src_p[3] & 0x3Fu);
    \\        if (cp >= 0x10000u && cp <= 0x10FFFFu) { *step_out = 4u; return cp; }
    \\    }
    \\    *step_out = 1u;
    \\    return 0xFFFDu;
    \\}
    \\static uint32_t _cx_rt_eff_verb(uint32_t spec_lo) {
    \\    uint32_t raw_v = (spec_lo >> 27) & 0xFu;
    \\    if (raw_v == 0u && ((spec_lo >> 31) & 1u) != 0u) return 1u;
    \\    return raw_v;
    \\}
    \\static void _cx_rt_fmt_str_spec(_cx_rt_buf_t *out_b, cx_str_t str_v, uint32_t spec_lo, uint32_t spec_hi) {
    \\    uint32_t verb_c = _cx_rt_eff_verb(spec_lo);
    \\    const uint8_t *raw_p = str_v.ptr;
    \\    size_t raw_n = (size_t)str_v.len;
    \\    if (verb_c == 1u) {
    \\        _cx_rt_buf_t q_buf = { NULL, 0u, 0u };
    \\        _cx_rt_buf_push_byte(&q_buf, '"');
    \\        size_t idx_i = 0u;
    \\        while (idx_i < raw_n) {
    \\            size_t step_n = 1u;
    \\            uint32_t cp_v = _cx_rt_decode_utf8_at(raw_p + idx_i, raw_n - idx_i, &step_n);
    \\            _cx_rt_push_escaped_cp(&q_buf, cp_v, 1u);
    \\            idx_i += step_n;
    \\        }
    \\        _cx_rt_buf_push_byte(&q_buf, '"');
    \\        _cx_rt_buf_pad_str(out_b, q_buf.data, q_buf.len, spec_lo, spec_hi, 0u);
    \\        free(q_buf.data);
    \\        return;
    \\    }
    \\    uint32_t prec_u16 = (spec_hi >> 16) & 0xFFFFu;
    \\    size_t sl_n = prec_u16 == 0xFFFFu ? raw_n : _cx_rt_trunc_utf8_cps(raw_p, raw_n, (size_t)prec_u16);
    \\    _cx_rt_buf_pad_str(out_b, raw_p, sl_n, spec_lo, spec_hi, 0u);
    \\}
    \\static void _cx_rt_fmt_char_spec(_cx_rt_buf_t *out_b, uint32_t cp_v, uint32_t spec_lo, uint32_t spec_hi) {
    \\    uint32_t verb_c = _cx_rt_eff_verb(spec_lo);
    \\    if (verb_c >= 2u) {
    \\        _cx_rt_fmt_u128_spec(out_b, _cx_u128_make((uint64_t)cp_v, 0ull), 0u, spec_lo, spec_hi);
    \\        return;
    \\    }
    \\    if (cp_v > 0x10FFFFu) cp_v = 0xFFFDu;
    \\    _cx_rt_buf_t c_buf = { NULL, 0u, 0u };
    \\    if (verb_c == 1u) {
    \\        _cx_rt_buf_push_byte(&c_buf, '\'');
    \\        _cx_rt_push_escaped_cp(&c_buf, cp_v, 0u);
    \\        _cx_rt_buf_push_byte(&c_buf, '\'');
    \\    } else {
    \\        uint8_t u8_b[4];
    \\        size_t u8_n = _cx_rt_encode_utf8(cp_v, u8_b);
    \\        _cx_rt_buf_push_bytes(&c_buf, u8_b, u8_n);
    \\    }
    \\    _cx_rt_buf_pad_str(out_b, c_buf.data, c_buf.len, spec_lo, spec_hi, 0u);
    \\    free(c_buf.data);
    \\}
    \\static void _cx_rt_fmt_bool_spec(_cx_rt_buf_t *out_b, uint8_t bval, uint32_t spec_lo, uint32_t spec_hi) {
    \\    const char *txt_s = (bval & 1u) ? "true" : "false";
    \\    _cx_rt_buf_pad_str(out_b, (const uint8_t *)txt_s, strlen(txt_s), spec_lo, spec_hi, 0u);
    \\}
    \\static void _cx_rt_fmt_ptr_spec(_cx_rt_buf_t *out_b, uintptr_t pval, uint32_t spec_lo, uint32_t spec_hi) {
    \\    uint32_t ptr_spec_lo = (spec_lo & ~(0xFu << 27)) | (9u << 27) | (1u << 25);
    \\    _cx_rt_fmt_u128_spec(out_b, _cx_u128_make((uint64_t)pval, 0ull), 0u, ptr_spec_lo, spec_hi);
    \\}
    \\static void _cx_rt_fmt_source_loc_spec(
    \\    _cx_rt_buf_t *out_b,
    \\    cx_source_loc_t sloc,
    \\    uint32_t spec_lo,
    \\    uint32_t spec_hi
    \\) {
    \\    uint32_t verb_c = _cx_rt_eff_verb(spec_lo);
    \\    _cx_rt_buf_t loc_b = { NULL, 0u, 0u };
    \\    if (sloc == NULL) {
    \\        _cx_rt_buf_push_cstr(&loc_b, "<null SourceLoc>");
    \\    } else if (verb_c == 1u) {
    \\        _cx_rt_buf_push_cstr(&loc_b, "SourceLoc { file: ");
    \\        _cx_rt_fmt_str_spec(&loc_b, sloc->file, 1u << 27, 0xFFFFFFFFu);
    \\        _cx_rt_buf_push_cstr(&loc_b, ", fn_name: ");
    \\        _cx_rt_fmt_str_spec(&loc_b, sloc->fn_name, 1u << 27, 0xFFFFFFFFu);
    \\        char lc_b[64];
    \\        int lc_n = snprintf(lc_b, sizeof(lc_b), ", line: %u, col: %u }", sloc->line, sloc->col);
    \\        if (lc_n > 0) _cx_rt_buf_push_bytes(&loc_b, (const uint8_t *)lc_b, (size_t)lc_n);
    \\    } else {
    \\        _cx_rt_buf_push_bytes(&loc_b, sloc->file.ptr, (size_t)sloc->file.len);
    \\        char lc_b[48];
    \\        int lc_n = snprintf(lc_b, sizeof(lc_b), ":%u:%u", sloc->line, sloc->col);
    \\        if (lc_n > 0) _cx_rt_buf_push_bytes(&loc_b, (const uint8_t *)lc_b, (size_t)lc_n);
    \\    }
    \\    _cx_rt_buf_pad_str(out_b, loc_b.data, loc_b.len, spec_lo, spec_hi, 0u);
    \\    free(loc_b.data);
    \\}
    \\static void _cx_rt_fmt_args_into(_cx_rt_buf_t *out_b, const cx_fmt_args_t *fargs) {
    \\    if (fargs == NULL) return;
    \\    size_t piece_n = (size_t)fargs->pieces_len;
    \\    size_t arg_n = (size_t)fargs->args_len;
    \\    size_t idx_i = 0u;
    \\    while (idx_i < piece_n) {
    \\        cx_str_t piece_s = fargs->pieces_ptr[idx_i];
    \\        _cx_rt_buf_push_bytes(out_b, piece_s.ptr, (size_t)piece_s.len);
    \\        if (idx_i < arg_n) {
    \\            cx_fmt_arg_t h_arg = fargs->args_ptr[idx_i];
    \\            if (h_arg.fmt_fn != NULL) {
    \\                uint32_t s_hi = ((uint32_t)h_arg.spec.width_or_none) |
    \\                    (((uint32_t)h_arg.spec.precision_or_none) << 16);
    \\                h_arg.fmt_fn(out_b, h_arg.data, h_arg.spec.flags_and_fill, s_hi);
    \\            }
    \\        }
    \\        idx_i += 1u;
    \\    }
    \\}
    \\static void _cx_rt_fmt_args_spec(
    \\    _cx_rt_buf_t *out_b,
    \\    const cx_fmt_args_t *fargs,
    \\    uint32_t spec_lo,
    \\    uint32_t spec_hi
    \\) {
    \\    if ((spec_hi & 0xFFFFu) == 0xFFFFu) {
    \\        _cx_rt_fmt_args_into(out_b, fargs);
    \\        return;
    \\    }
    \\    _cx_rt_buf_t sub_b = { NULL, 0u, 0u };
    \\    _cx_rt_fmt_args_into(&sub_b, fargs);
    \\    _cx_rt_buf_pad_str(out_b, sub_b.data, sub_b.len, spec_lo, spec_hi, 0u);
    \\    free(sub_b.data);
    \\}
    \\static inline cx_str_t _cx_rt_buf_finish_str(_cx_rt_buf_t *out_b) {
    \\    cx_str_t res_s;
    \\    if (out_b->len == 0u) {
    \\        free(out_b->data);
    \\        res_s.ptr = (uint8_t *)_cx_empty_rodata;
    \\        res_s.len = 0u;
    \\    } else {
    \\        _cx_rt_buf_push_byte(out_b, 0u);
    \\        res_s.ptr = out_b->data;
    \\        res_s.len = (uintptr_t)(out_b->len - 1u);
    \\    }
    \\    return res_s;
    \\}
    \\#if defined(__GNUC__) || defined(__clang__)
    \\__attribute__((noreturn))
    \\#endif
    \\static void _cx_rt_panic_fmt_args(const cx_fmt_args_t *fargs) {
    \\    _cx_rt_buf_t msg_b = { NULL, 0u, 0u };
    \\    _cx_rt_fmt_args_into(&msg_b, fargs);
    \\    _cx_rt_panic(msg_b.data, msg_b.len);
    \\}
    \\
;

// -------------------------------------- INTERNALS --------------------------------------

// ------------ Type Classification & C99 Formatting ------------

/// Returns `true` when `raw_ty` is a Phase 7.6 built-in runtime `TypeId` (`45..50` or `TaskGroup`/`TaskHandle`).
fn isBuiltInRuntimeType(pool: *const InternPool, raw_ty: TypeId) bool {
    return switch (raw_ty) {
        .source_loc_ty,
        .fmt_spec_ty,
        .fmt_args_ty,
        .bencher_ty,
        .task_group_base_ty,
        .task_handle_base_ty,
        => true,
        else => pool.isTaskGroupType(raw_ty) or pool.isTaskHandleType(raw_ty),
    };
}

/// Returns `true` if `raw_ty` has zero byte size (`unit`, `never`, or empty composite; never `.opaque_ty`).
fn isZeroSizedType(emitter: *CModuleEmitter, raw_ty: TypeId) !bool {
    const unwrapped = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped == .opaque_ty) return false;
    if (unwrapped == .unit_ty or unwrapped == .never_ty or unwrapped.isError()) return true;
    return (try emitter.resolver.resolveType(unwrapped)).size_bytes == 0;
}

/// Returns integer `(bits, is_signed)` metadata for integer, `bool`, `char`, `bit_field`, or C-like/backed `enum`.
fn resolveIntegerInfo(
    emitter: *CModuleEmitter,
    raw_ty: TypeId,
) !?CIntInfo {
    var cur_ty = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    const cur_node = emitter.input.pool.getNode(cur_ty);
    if (cur_node.tag == .bit_field_ty) {
        cur_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(cur_node.lhs));
    } else if (cur_node.tag == .enum_ty) {
        if (emitter.input.pool.getEnumBackingIntType(cur_ty)) |backing_ty| {
            cur_ty = emitter.input.pool.unwrapUnderlyingType(backing_ty);
        } else if ((try emitter.resolver.getSumDetail(cur_ty)) == null) {
            const enum_lay = try emitter.resolver.resolveType(cur_ty);
            if (enum_lay.size_bytes == 0) return null;
            return .{ .bits = @intCast(enum_lay.size_bytes * 8), .is_signed = false };
        }
    }
    const ptr_bits: u16 = @as(u16, emitter.cfg.target.ptrBytes()) * 8;
    return switch (cur_ty) {
        .bool_ty => .{ .bits = 1, .is_signed = false },
        .i8_ty => .{ .bits = 8, .is_signed = true },
        .u8_ty => .{ .bits = 8, .is_signed = false },
        .i16_ty => .{ .bits = 16, .is_signed = true },
        .u16_ty => .{ .bits = 16, .is_signed = false },
        .i32_ty, .untyped_int_ty => .{ .bits = 32, .is_signed = true },
        .u32_ty, .char_ty => .{ .bits = 32, .is_signed = false },
        .i64_ty => .{ .bits = 64, .is_signed = true },
        .u64_ty => .{ .bits = 64, .is_signed = false },
        .i128_ty => .{ .bits = 128, .is_signed = true },
        .u128_ty => .{ .bits = 128, .is_signed = false },
        .isize_ty => .{ .bits = ptr_bits, .is_signed = true },
        .usize_ty => .{ .bits = ptr_bits, .is_signed = false },
        else => null,
    };
}

/// Returns the C99 scalar unsigned type string for exact bit width `bits` (`8`, `16`, `32`, `64`, `128`).
fn resolveUnsignedCTypeForBits(bits: u16) []const u8 {
    return switch (bits) {
        1, 8 => "uint8_t",
        16 => "uint16_t",
        32 => "uint32_t",
        64 => "uint64_t",
        128 => "cx_u128",
        else => "uint64_t",
    };
}

/// Returns the C99 scalar signed type string for exact bit width `bits` (`8`, `16`, `32`, `64`, `128`).
fn resolveSignedCTypeForBits(bits: u16) []const u8 {
    return switch (bits) {
        8 => "int8_t",
        16 => "int16_t",
        32 => "int32_t",
        64 => "int64_t",
        128 => "cx_i128",
        else => "int64_t",
    };
}

/// Returns `true` if `unwrapped` requires a `_cx_ty_<id>` composite or function-pointer `typedef`.
fn needsCompositeTypedef(emitter: *CModuleEmitter, unwrapped: TypeId) !bool {
    if (unwrapped == .str_ty) return true;
    if (unwrapped.isPrimitiveOrSentinel() or
        unwrapped.isBuiltinGroup() or
        isBuiltInRuntimeType(emitter.input.pool, unwrapped)) return false;
    const node = emitter.input.pool.getNode(unwrapped);
    return switch (node.tag) {
        .struct_ty,
        .tuple_ty,
        .union_ty,
        .array_ty,
        .soa_array_ty,
        .slice_ty,
        .soa_slice_ty,
        .optional_ty,
        .result_ty,
        .fn_ty,
        .closure_ty,
        .future_ty,
        => !(try isZeroSizedType(emitter, unwrapped)) or node.tag == .fn_ty,
        .enum_ty => (try emitter.resolver.getSumDetail(unwrapped)) != null and
            !(try isZeroSizedType(emitter, unwrapped)),
        else => false,
    };
}

/// Formats the canonical C99 type spelling of `raw_ty` iteratively (allocating once in `emitter.allocator`).
fn formatCType(emitter: *CModuleEmitter, raw_ty: TypeId) ![]u8 {
    var unwrapped = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    var ptr_indirections: u32 = 0;
    var is_innermost_ptr_mut = false;

    while (ptr_indirections < MAX_C_TYPE_DEPTH and
        !unwrapped.isError() and
        !unwrapped.isPrimitiveOrSentinel() and
        !unwrapped.isBuiltinGroup() and
        !isBuiltInRuntimeType(emitter.input.pool, unwrapped))
    {
        const cur_node = emitter.input.pool.getNode(unwrapped);
        if (cur_node.tag != .ref_ty and cur_node.tag != .mut_ref_ty and cur_node.tag != .raw_ptr_ty) break;
        is_innermost_ptr_mut = cur_node.tag == .mut_ref_ty or
            (cur_node.tag == .raw_ptr_ty and cur_node.rhs != 0);
        const pointee_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(cur_node.lhs));
        ptr_indirections += 1;
        if (try isZeroSizedType(emitter, pointee_ty)) {
            unwrapped = .unit_ty;
            break;
        }
        unwrapped = pointee_ty;
    }

    var base_buf: [64]u8 = undefined;
    const base_str: []const u8 = blk: {
        if (ptr_indirections >= MAX_C_TYPE_DEPTH or
            unwrapped.isError() or
            unwrapped == .unit_ty or
            unwrapped == .never_ty)
        {
            break :blk "uint8_t";
        }
        if (unwrapped == .opaque_ty) {
            if (ptr_indirections > 0) {
                break :blk if (is_innermost_ptr_mut) "void" else "const void";
            }
            break :blk "uint8_t";
        }
        if (unwrapped == .str_ty) {
            break :blk try std.fmt.bufPrint(&base_buf, "_cx_ty_{d}", .{TypeId.str_ty.toU32()});
        }
        switch (unwrapped) {
            .source_loc_ty => break :blk "cx_source_loc_t",
            .fmt_spec_ty => break :blk "cx_fmt_spec_t",
            .fmt_args_ty => break :blk "cx_fmt_args_t",
            .bencher_ty => break :blk "cx_bencher_t",
            .task_group_base_ty, .task_handle_base_ty => break :blk "void *",
            else => {
                if (emitter.input.pool.isTaskGroupType(unwrapped) or
                    emitter.input.pool.isTaskHandleType(unwrapped))
                {
                    break :blk "void *";
                }
            },
        }
        const node = emitter.input.pool.getNode(unwrapped);
        if (node.tag == .bit_field_ty) {
            unwrapped = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
        }
        switch (unwrapped) {
            .bool_ty, .u8_ty => break :blk "uint8_t",
            .i8_ty => break :blk "int8_t",
            .i16_ty => break :blk "int16_t",
            .u16_ty => break :blk "uint16_t",
            .i32_ty, .untyped_int_ty => break :blk "int32_t",
            .u32_ty, .char_ty => break :blk "uint32_t",
            .i64_ty => break :blk "int64_t",
            .u64_ty => break :blk "uint64_t",
            .i128_ty => break :blk "cx_i128",
            .u128_ty => break :blk "cx_u128",
            .isize_ty => break :blk if (emitter.cfg.target.ptrBytes() == 4) "int32_t" else "int64_t",
            .usize_ty => break :blk if (emitter.cfg.target.ptrBytes() == 4) "uint32_t" else "uint64_t",
            .f32_ty => break :blk "float",
            .f64_ty, .untyped_float_ty => break :blk "double",
            else => {},
        }
        const inner_node = emitter.input.pool.getNode(unwrapped);
        if (inner_node.tag == .enum_ty) {
            if (emitter.input.pool.getEnumBackingIntType(unwrapped)) |backing_ty| {
                const backing_info = (try resolveIntegerInfo(emitter, backing_ty)) orelse break :blk "uint8_t";
                break :blk if (backing_info.is_signed)
                    resolveSignedCTypeForBits(backing_info.bits)
                else
                    resolveUnsignedCTypeForBits(backing_info.bits);
            }
            if ((try emitter.resolver.getSumDetail(unwrapped)) == null) {
                const lay = try emitter.resolver.resolveType(unwrapped);
                if (lay.size_bytes == 0) break :blk "uint8_t";
                break :blk resolveUnsignedCTypeForBits(@intCast(lay.size_bytes * 8));
            }
            if (try isZeroSizedType(emitter, unwrapped)) break :blk "uint8_t";
            break :blk try std.fmt.bufPrint(&base_buf, "_cx_ty_{d}", .{unwrapped.toU32()});
        }
        if (try needsCompositeTypedef(emitter, unwrapped)) {
            break :blk try std.fmt.bufPrint(&base_buf, "_cx_ty_{d}", .{unwrapped.toU32()});
        }
        break :blk "uint8_t";
    };

    if (ptr_indirections == 0) return emitter.allocator.dupe(u8, base_str);
    const total_len = base_str.len + @as(usize, ptr_indirections) * 2;
    var out_buf = try emitter.allocator.alloc(u8, total_len);
    @memcpy(out_buf[0..base_str.len], base_str);
    var pos: usize = base_str.len;
    var ind_i: u32 = 0;
    while (ind_i < ptr_indirections) : (ind_i += 1) {
        out_buf[pos] = ' ';
        out_buf[pos + 1] = '*';
        pos += 2;
    }
    return out_buf;
}

/// Sanitizes an arbitrary CoreX symbol name into a valid ASCII C99 identifier suffix.
fn sanitizeIdentifierAlloc(allocator: std.mem.Allocator, raw_name: []const u8) ![]u8 {
    if (raw_name.len == 0) return allocator.dupe(u8, "anon");
    var buf = try allocator.alloc(u8, raw_name.len);
    for (raw_name, 0..) |ch_byte, i| {
        const is_alnum = (ch_byte >= 'a' and ch_byte <= 'z') or
            (ch_byte >= 'A' and ch_byte <= 'Z') or
            (ch_byte >= '0' and ch_byte <= '9');
        buf[i] = if (is_alnum or ch_byte == '_') ch_byte else '_';
    }
    return buf;
}

// ----------- Type Discovery & Topological Ordering ------------

/// Recursively registers `raw_ty` and all transitively referenced child types into `discovered_type_set`.
fn discoverTypeRecursive(emitter: *CModuleEmitter, raw_ty: TypeId, depth: u32) !void {
    if (depth >= MAX_C_TYPE_DEPTH) return;
    const unwrapped = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped.isError() or unwrapped == .unit_ty or unwrapped == .never_ty) return;
    if (unwrapped == .str_ty) {
        if (!(try emitter.discovered_type_set.getOrPut(emitter.allocator, TypeId.str_ty.toU32())).found_existing) {
            try emitter.sorted_candidates.append(emitter.allocator, .str_ty);
        }
        return;
    }
    if (unwrapped.isPrimitiveOrSentinel() or
        unwrapped.isBuiltinGroup() or
        isBuiltInRuntimeType(emitter.input.pool, unwrapped)) return;

    if ((try emitter.discovered_type_set.getOrPut(emitter.allocator, unwrapped.toU32())).found_existing) return;

    const node = emitter.input.pool.getNode(unwrapped);
    if (try needsCompositeTypedef(emitter, unwrapped)) {
        try emitter.sorted_candidates.append(emitter.allocator, unwrapped);
    }

    switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty => {
            try discoverTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
        },
        .slice_ty, .soa_slice_ty => {
            try discoverTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
        },
        .array_ty, .soa_array_ty => {
            try discoverTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
            if (node.tag == .soa_array_ty) {
                const elem_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const elem_lay = try emitter.resolver.resolveType(elem_ty);
                const fld_start = elem_lay.aux_start;
                const fld_len = elem_lay.aux_len;
                var fld_i: u32 = 0;
                while (fld_i < fld_len) : (fld_i += 1) {
                    const fld_ty = emitter.resolver.fields_by_decl.items[fld_start + fld_i].field_ty;
                    try discoverTypeRecursive(emitter, fld_ty, depth + 1);
                }
            }
        },
        .struct_ty, .tuple_ty, .union_ty => {
            const lay = try emitter.resolver.resolveType(unwrapped);
            const fld_start = lay.aux_start;
            const fld_len = lay.aux_len;
            var fld_i: u32 = 0;
            while (fld_i < fld_len) : (fld_i += 1) {
                const fld_ty = emitter.resolver.fields_by_decl.items[fld_start + fld_i].field_ty;
                try discoverTypeRecursive(emitter, fld_ty, depth + 1);
            }
        },
        .optional_ty => {
            try discoverTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
        },
        .result_ty => {
            try discoverTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
            try discoverTypeRecursive(emitter, TypeId.fromInt(node.rhs), depth + 1);
        },
        .enum_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < emitter.input.sym_table.symbols.items.len) {
                const enum_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
                if (!enum_sym.target_scope.isNone()) {
                    var var_ord: u32 = 0;
                    for (emitter.input.sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
                        if (emitter.input.sym_table.getSymbol(mem_idx).kind != .enum_variant_sym) continue;
                        const var_pay = resolveEnumVariantPayloadType(emitter, unwrapped, var_ord);
                        if (var_pay != .unit_ty and !var_pay.isError()) {
                            try discoverTypeRecursive(emitter, var_pay, depth + 1);
                        }
                        var_ord += 1;
                    }
                }
            }
        },
        .fn_ty, .closure_ty => {
            if (emitter.input.pool.getFnSignatureView(unwrapped)) |sig| {
                try discoverTypeRecursive(emitter, sig.ret_ty, depth + 1);
                var param_i: usize = 0;
                while (param_i < sig.paramCount()) : (param_i += 1) {
                    try discoverTypeRecursive(emitter, sig.getParamType(param_i), depth + 1);
                }
            }
        },
        .bit_field_ty => {
            try discoverTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
        },
        .future_ty => {
            try discoverTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
            if (emitter.has_async_ops) {
                try registerDropTypeRecursive(emitter, unwrapped, 0);
            }
        },
        else => {},
    }
}

/// Resolves the instantiated payload `TypeId` of variant `tag_ord` on `sum_ty` (`Option`, `Result`, `enum`).
fn resolveEnumVariantPayloadType(emitter: *CModuleEmitter, raw_sum_ty: TypeId, tag_ord: u32) TypeId {
    const sum_ty = emitter.input.pool.unwrapUnderlyingType(raw_sum_ty);
    const node = emitter.input.pool.getNode(sum_ty);
    switch (node.tag) {
        .optional_ty => return if (tag_ord == 1)
            emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs))
        else
            .unit_ty,
        .result_ty => return if (tag_ord == 0)
            emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs))
        else
            emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.rhs)),
        .enum_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (sym_idx.isNone() or sym_idx.asInt() >= emitter.input.sym_table.symbols.items.len) {
                return .unit_ty;
            }
            const enum_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
            if (enum_sym.target_scope.isNone()) return .unit_ty;
            const subst = type_system.NominalTypeSubst.init(
                emitter.input.pool,
                emitter.input.sym_table,
                sum_ty,
            );
            var cur_ord: u32 = 0;
            for (emitter.input.sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
                const mem_sym = emitter.input.sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .enum_variant_sym) continue;
                if (cur_ord == tag_ord) {
                    const raw_pay = mem_sym.type_id;
                    if (raw_pay.isError() or raw_pay == .unit_ty or raw_pay == sum_ty) return .unit_ty;
                    return emitter.input.pool.unwrapUnderlyingType(subst.resolve(raw_pay));
                }
                cur_ord += 1;
            }
            return .unit_ty;
        },
        else => return .unit_ty,
    }
}

/// Visits `ty` and its value-embedded dependencies in postorder so `typedef` dependencies precede users.
fn visitTypeTopoDfs(emitter: *CModuleEmitter, ty: TypeId, depth: u32) !void {
    if (depth >= MAX_C_TYPE_DEPTH) return;
    const raw_id = ty.toU32();
    if (emitter.topo_state.get(raw_id)) |state_val| {
        if (state_val != 0) return;
    }
    try emitter.topo_state.put(emitter.allocator, raw_id, 1);

    if (ty != .str_ty) {
        const node = emitter.input.pool.getNode(ty);
        switch (node.tag) {
            .struct_ty, .tuple_ty, .union_ty => {
                const lay = try emitter.resolver.resolveType(ty);
                const fld_start = lay.aux_start;
                const fld_len = lay.aux_len;
                var fld_i: u32 = 0;
                while (fld_i < fld_len) : (fld_i += 1) {
                    const fld_raw = emitter.resolver.fields_by_decl.items[fld_start + fld_i].field_ty;
                    const fld_unwrapped = emitter.input.pool.unwrapUnderlyingType(fld_raw);
                    if (try needsCompositeTypedef(emitter, fld_unwrapped)) {
                        try visitTypeTopoDfs(emitter, fld_unwrapped, depth + 1);
                    }
                }
            },
            .array_ty => {
                const elem_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                if (try needsCompositeTypedef(emitter, elem_ty)) {
                    try visitTypeTopoDfs(emitter, elem_ty, depth + 1);
                }
            },
            .optional_ty => {
                const pay_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                if (try needsCompositeTypedef(emitter, pay_ty)) {
                    try visitTypeTopoDfs(emitter, pay_ty, depth + 1);
                }
            },
            .result_ty => {
                const ok_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const err_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.rhs));
                if (try needsCompositeTypedef(emitter, ok_ty)) try visitTypeTopoDfs(emitter, ok_ty, depth + 1);
                if (try needsCompositeTypedef(emitter, err_ty)) try visitTypeTopoDfs(emitter, err_ty, depth + 1);
            },
            .enum_ty => {
                const sym_idx = SymbolIndex.fromInt(node.rhs);
                if (!sym_idx.isNone() and sym_idx.asInt() < emitter.input.sym_table.symbols.items.len) {
                    const enum_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
                    if (!enum_sym.target_scope.isNone()) {
                        var var_ord: u32 = 0;
                        for (emitter.input.sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
                            if (emitter.input.sym_table.getSymbol(mem_idx).kind != .enum_variant_sym) continue;
                            const var_pay = resolveEnumVariantPayloadType(emitter, ty, var_ord);
                            if (try needsCompositeTypedef(emitter, var_pay)) {
                                try visitTypeTopoDfs(emitter, var_pay, depth + 1);
                            }
                            var_ord += 1;
                        }
                    }
                }
            },
            .fn_ty, .closure_ty => {
                if (emitter.input.pool.getFnSignatureView(ty)) |sig| {
                    const ret_unwrapped = emitter.input.pool.unwrapUnderlyingType(sig.ret_ty);
                    if (try needsCompositeTypedef(emitter, ret_unwrapped)) {
                        try visitTypeTopoDfs(emitter, ret_unwrapped, depth + 1);
                    }
                    var param_i: usize = 0;
                    while (param_i < sig.paramCount()) : (param_i += 1) {
                        const param_unwrapped = emitter.input.pool.unwrapUnderlyingType(sig.getParamType(param_i));
                        if (try needsCompositeTypedef(emitter, param_unwrapped)) {
                            try visitTypeTopoDfs(emitter, param_unwrapped, depth + 1);
                        }
                    }
                }
            },
            .future_ty => {
                const out_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                if (try needsCompositeTypedef(emitter, out_ty)) {
                    try visitTypeTopoDfs(emitter, out_ty, depth + 1);
                }
            },
            else => {},
        }
    }

    try emitter.topo_state.put(emitter.allocator, raw_id, 2);
    try emitter.ordered_types.append(emitter.allocator, ty);
}

/// Registers `.result_ty` `raw_ty` for a synthesized `_cx_is_err_ty_<id>` helper when non-ZST.
fn maybeRegisterResultErrCheckType(emitter: *CModuleEmitter, raw_ty: TypeId) !void {
    const unwrapped = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped.isError() or unwrapped.isPrimitiveOrSentinel()) return;
    if (emitter.input.pool.getNode(unwrapped).tag != .result_ty) return;
    if (try isZeroSizedType(emitter, unwrapped)) return;
    if (!(try emitter.res_err_check_set.getOrPut(emitter.allocator, unwrapped.toU32())).found_existing) {
        try emitter.ordered_res_err_types.append(emitter.allocator, unwrapped);
    }
}

/// Registers `raw_ty` and its constituent field/element/variant types for synthesized `_cx_drop_ty_<id>`.
fn registerDropTypeRecursive(emitter: *CModuleEmitter, raw_ty: TypeId, depth: u32) !void {
    if (depth >= MAX_C_TYPE_DEPTH) return;
    const ty = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (ty.isError() or
        ty == .unit_ty or
        ty == .never_ty or
        ty.isPrimitive() or
        isBuiltInRuntimeType(emitter.input.pool, ty)) return;
    if ((try emitter.drop_type_set.getOrPut(emitter.allocator, ty.toU32())).found_existing) return;

    const node = emitter.input.pool.getNode(ty);
    switch (node.tag) {
        .struct_ty, .tuple_ty => {
            const lay = try emitter.resolver.resolveType(ty);
            const fld_start = lay.aux_start;
            const fld_len = lay.aux_len;
            var fld_i: u32 = 0;
            while (fld_i < fld_len) : (fld_i += 1) {
                const fld_ty = emitter.resolver.fields_by_decl.items[fld_start + fld_i].field_ty;
                try registerDropTypeRecursive(emitter, fld_ty, depth + 1);
            }
        },
        .array_ty => {
            try registerDropTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
        },
        .soa_array_ty => {
            const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const lay = try emitter.resolver.resolveType(elem_struct);
            const fld_start = lay.aux_start;
            const fld_len = lay.aux_len;
            var fld_i: u32 = 0;
            while (fld_i < fld_len) : (fld_i += 1) {
                const fld_ty = emitter.resolver.fields_by_decl.items[fld_start + fld_i].field_ty;
                try registerDropTypeRecursive(emitter, fld_ty, depth + 1);
            }
        },
        .optional_ty => {
            try registerDropTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
        },
        .result_ty => {
            try registerDropTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
            try registerDropTypeRecursive(emitter, TypeId.fromInt(node.rhs), depth + 1);
        },
        .enum_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < emitter.input.sym_table.symbols.items.len) {
                const enum_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
                if (!enum_sym.target_scope.isNone()) {
                    var var_ord: u32 = 0;
                    for (emitter.input.sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
                        if (emitter.input.sym_table.getSymbol(mem_idx).kind != .enum_variant_sym) continue;
                        const var_pay = resolveEnumVariantPayloadType(emitter, ty, var_ord);
                        try registerDropTypeRecursive(emitter, var_pay, depth + 1);
                        var_ord += 1;
                    }
                }
            }
        },
        .closure_ty => {},
        else => {},
    }
    try emitter.ordered_drop_types.append(emitter.allocator, ty);
}

/// Registers `raw_ty` and its constituent types in postorder for synthesized `_cx_eq_ty_<id>` helpers.
fn registerEqTypeRecursive(emitter: *CModuleEmitter, raw_ty: TypeId, depth: u32) !void {
    if (depth >= MAX_C_TYPE_DEPTH) return;
    const ty = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (try isZeroSizedType(emitter, ty)) return;
    if (ty.isPrimitiveOrSentinel() or
        ty == .str_ty or
        isBuiltInRuntimeType(emitter.input.pool, ty) or
        (try resolveIntegerInfo(emitter, ty)) != null) return;

    const node = emitter.input.pool.getNode(ty);
    switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .fn_ty => return,
        .bit_field_ty => try registerEqTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1),
        .struct_ty, .tuple_ty => {
            if ((try emitter.eq_type_set.getOrPut(emitter.allocator, ty.toU32())).found_existing) return;
            try discoverTypeRecursive(emitter, ty, depth);
            const lay = try emitter.resolver.resolveType(ty);
            const fld_start = lay.aux_start;
            const fld_len = lay.aux_len;
            var fld_i: u32 = 0;
            while (fld_i < fld_len) : (fld_i += 1) {
                const fld_ty = emitter.resolver.fields_by_decl.items[fld_start + fld_i].field_ty;
                try registerEqTypeRecursive(emitter, fld_ty, depth + 1);
            }
            try emitter.ordered_eq_types.append(emitter.allocator, ty);
        },
        .array_ty, .slice_ty => {
            if ((try emitter.eq_type_set.getOrPut(emitter.allocator, ty.toU32())).found_existing) return;
            try discoverTypeRecursive(emitter, ty, depth);
            try registerEqTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
            try emitter.ordered_eq_types.append(emitter.allocator, ty);
        },
        .soa_array_ty, .soa_slice_ty => {
            if ((try emitter.eq_type_set.getOrPut(emitter.allocator, ty.toU32())).found_existing) return;
            try discoverTypeRecursive(emitter, ty, depth);
            const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const lay = try emitter.resolver.resolveType(elem_struct);
            const fld_start = lay.aux_start;
            const fld_len = lay.aux_len;
            var fld_i: u32 = 0;
            while (fld_i < fld_len) : (fld_i += 1) {
                const fld_ty = emitter.resolver.fields_by_decl.items[fld_start + fld_i].field_ty;
                try registerEqTypeRecursive(emitter, fld_ty, depth + 1);
            }
            try emitter.ordered_eq_types.append(emitter.allocator, ty);
        },
        .optional_ty, .result_ty, .enum_ty => {
            if ((try emitter.eq_type_set.getOrPut(emitter.allocator, ty.toU32())).found_existing) return;
            try discoverTypeRecursive(emitter, ty, depth);
            const var_count: u32 = switch (node.tag) {
                .optional_ty, .result_ty => 2,
                .enum_ty => countEnumVariants(emitter, ty),
                else => 0,
            };
            var var_ord: u32 = 0;
            while (var_ord < var_count) : (var_ord += 1) {
                const var_pay = resolveEnumVariantPayloadType(emitter, ty, var_ord);
                try registerEqTypeRecursive(emitter, var_pay, depth + 1);
            }
            try emitter.ordered_eq_types.append(emitter.allocator, ty);
        },
        else => return,
    }
}

/// Registers `raw_ty` and its constituent types for synthesized `_cx_fmt_fn_ty_<id>` helpers (`SE-12`).
fn registerFmtTypeRecursive(emitter: *CModuleEmitter, raw_ty: TypeId, depth: u32) !void {
    if (depth >= MAX_C_TYPE_DEPTH) return;
    const ty = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (ty.isError() or ty == .never_ty) return;
    if ((try emitter.fmt_type_set.getOrPut(emitter.allocator, ty.toU32())).found_existing) return;
    try discoverTypeRecursive(emitter, ty, depth);

    if (!ty.isPrimitiveOrSentinel() and !isBuiltInRuntimeType(emitter.input.pool, ty)) {
        const node = emitter.input.pool.getNode(ty);
        switch (node.tag) {
            .ref_ty, .mut_ref_ty, .bit_field_ty, .array_ty, .slice_ty, .optional_ty => {
                try registerFmtTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
            },
            .result_ty => {
                try registerFmtTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
                try registerFmtTypeRecursive(emitter, TypeId.fromInt(node.rhs), depth + 1);
            },
            .struct_ty, .tuple_ty => {
                const lay = try emitter.resolver.resolveType(ty);
                var fld_i: u32 = 0;
                while (fld_i < lay.aux_len) : (fld_i += 1) {
                    const fld_ty = emitter.resolver.fields_by_decl.items[lay.aux_start + fld_i].field_ty;
                    try registerFmtTypeRecursive(emitter, fld_ty, depth + 1);
                }
            },
            .enum_ty => {
                const var_count = countEnumVariants(emitter, ty);
                var var_ord: u32 = 0;
                while (var_ord < var_count) : (var_ord += 1) {
                    const var_pay = resolveEnumVariantPayloadType(emitter, ty, var_ord);
                    if (var_pay != .unit_ty and !var_pay.isError()) {
                        try registerFmtTypeRecursive(emitter, var_pay, depth + 1);
                    }
                }
            },
            else => {},
        }
    }
    try emitter.ordered_fmt_types.append(emitter.allocator, ty);
}

/// Extracts a compile-time `usize` integer constant from SSA `val_raw` in `body` (`null` if dynamic).
fn extractConstUsizeFromBody(body: *const MirBody, val_raw: u32) ?usize {
    if (val_raw >= body.insts.len) return null;
    const inst = body.insts.get(val_raw);
    if (inst.op != .const_scalar or inst.operands.lhs >= body.consts.items.len) return null;
    return switch (body.consts.items[inst.operands.lhs]) {
        .int_val => |ival| if (ival >= 0) @intCast(@as(u128, @bitCast(ival))) else null,
        else => null,
    };
}

/// Extracts a compile-time boolean / non-zero `is_weak` flag from SSA `val_raw` (`null` if dynamic).
fn extractConstWeakFromBody(body: *const MirBody, val_raw: u32) ?bool {
    if (val_raw >= body.insts.len) return null;
    const inst = body.insts.get(val_raw);
    if (inst.op != .const_scalar or inst.operands.lhs >= body.consts.items.len) return null;
    return switch (body.consts.items[inst.operands.lhs]) {
        .bool_val => |bval| bval,
        .int_val => |ival| ival != 0,
        else => null,
    };
}

/// Extracts a compile-time `.str_val` `SymbolId` from SSA `val_raw` in `body` (`null` if non-literal).
fn extractConstStrSymFromBody(body: *const MirBody, val_raw: u32) ?SymbolId {
    if (val_raw >= body.insts.len) return null;
    const inst = body.insts.get(val_raw);
    if (inst.op != .const_scalar or inst.operands.lhs >= body.consts.items.len) return null;
    return switch (body.consts.items[inst.operands.lhs]) {
        .str_val => |sym_id| sym_id,
        else => null,
    };
}

/// Extracts resolved FFI, TLS, linker-section, and Wasm import/export metadata for `sym_idx`.
fn extractSymFfiMeta(emitter: *const CModuleEmitter, sym_idx: SymbolIndex) SymFfiMeta {
    if (sym_idx.isNone() or sym_idx.asInt() >= emitter.input.sym_table.symbols.items.len) return .{};
    const sym_rec = emitter.input.sym_table.getSymbol(sym_idx).*;
    var meta = SymFfiMeta{
        .is_extern = sym_rec.flags.is_extern,
        .is_export = sym_rec.contract_flags.is_export,
        .is_mut = sym_rec.flags.is_mut,
        .link_name = if (sym_rec.contract_flags.has_link_name) sym_rec.link_name_text else "",
        .link_section = if (sym_rec.contract_flags.has_link_section) sym_rec.link_section_name else "",
    };
    if (emitter.input.sym_table.getFfiContract(sym_idx)) |ffi_c| {
        meta.is_thread_local = ffi_c.is_thread_local;
        if (ffi_c.wasm_import_module != .empty and ffi_c.wasm_import_module != .none) {
            meta.wasm_import_module = emitter.input.interner.get(ffi_c.wasm_import_module);
        }
        if (ffi_c.wasm_import_name != .empty and ffi_c.wasm_import_name != .none) {
            meta.wasm_import_name = emitter.input.interner.get(ffi_c.wasm_import_name);
        }
        if (ffi_c.wasm_export_name != .empty and ffi_c.wasm_export_name != .none) {
            meta.wasm_export_name = emitter.input.interner.get(ffi_c.wasm_export_name);
        }
        if (ffi_c.link_lib_name != .empty and ffi_c.link_lib_name != .none) {
            meta.link_lib_name = emitter.input.interner.get(ffi_c.link_lib_name);
        }
    }
    return meta;
}

/// Records an `@link_lib("…")` library directive into `emitter.collected_link_libs` without duplicates.
fn recordCollectedLinkLib(emitter: *CModuleEmitter, lib_name: []const u8) !void {
    if (lib_name.len == 0) return;
    for (emitter.collected_link_libs.items) |existing| {
        if (std.mem.eql(u8, existing, lib_name)) return;
    }
    try emitter.collected_link_libs.append(emitter.allocator, lib_name);
}

/// Returns `true` if `body` is an `@export`, `@wasm_export`, or `extern "C"` C-ABI unwind-abort boundary.
fn isBodyCAbiBoundary(emitter: *const CModuleEmitter, body: *const MirBody) bool {
    if (body.symbol_index.isNone() or
        body.symbol_index.asInt() >= emitter.input.sym_table.symbols.items.len) return false;
    const sym_rec = emitter.input.sym_table.getSymbol(body.symbol_index).*;
    if (sym_rec.flags.is_extern or sym_rec.contract_flags.is_export) return true;
    const ffi_meta = extractSymFfiMeta(emitter, body.symbol_index);
    if (ffi_meta.wasm_export_name.len > 0) return true;
    if (emitter.input.pool.getFnSignatureView(sym_rec.type_id)) |sig_view| {
        if (sig_view.is_c_abi) return true;
    }
    return false;
}

/// Returns `true` if `raw_ty` (within `depth <= 16`) contains any floating-point leaf (`float`/`double`) for C ABI classification.
fn hasFloatFieldForCAbi(emitter: *CModuleEmitter, raw_ty: TypeId, depth: u32) !bool {
    if (depth > 16) return false;
    const unwrapped = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped == .f32_ty or unwrapped == .f64_ty) return true;
    if (unwrapped.isPrimitiveOrSentinel()) return false;
    const node = emitter.input.pool.getNode(unwrapped);
    switch (node.tag) {
        .array_ty => {
            if ((node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) != 0 or node.rhs == 0) return false;
            return hasFloatFieldForCAbi(emitter, TypeId.fromInt(node.lhs), depth + 1);
        },
        .struct_ty, .tuple_ty, .union_ty => {
            const sub_lay = try emitter.resolver.resolveTypeBounded(unwrapped, depth + 1);
            const sub_start = sub_lay.aux_start;
            const sub_len = sub_lay.aux_len;
            var fld_i: u32 = 0;
            while (fld_i < sub_len) : (fld_i += 1) {
                const fld = emitter.resolver.fields_by_decl.items[sub_start + fld_i];
                if (fld.size_bytes == 0) continue;
                if (try hasFloatFieldForCAbi(emitter, fld.field_ty, depth + 1)) return true;
            }
            return false;
        },
        else => return false,
    }
}

/// Formats the header-comment target identifier (`"x86_64-linux"` on default GNU Linux for golden parity).
fn formatC99BannerTargetName(target: TargetSpec) []const u8 {
    if (target.arch == .x86_64 and target.os == .linux and target.abi == .gnu) {
        return "x86_64-linux";
    }
    return target.asTripleStr();
}

/// Scans all `MirBody` items, indexing callables, C identifiers, constants, drops, and reachable `TypeId`s.
fn indexModuleEntities(emitter: *CModuleEmitter) !void {
    try discoverTypeRecursive(emitter, .str_ty, 0);

    var seen_c_exports: std.StringHashMapUnmanaged(SymbolIndex) = .empty;
    defer seen_c_exports.deinit(emitter.allocator);

    for (emitter.input.bodies, 0..) |*body_ptr, body_i| {
        const b_idx: u32 = @intCast(body_i);
        if (!body_ptr.def_id.isNone()) {
            try emitter.def_to_body_idx.put(emitter.allocator, body_ptr.def_id.asInt(), b_idx);
        }
        if (!body_ptr.symbol_index.isNone()) {
            try emitter.sym_to_body_idx.put(emitter.allocator, body_ptr.symbol_index.asInt(), b_idx);
        }

        const raw_name = emitter.input.interner.get(body_ptr.name);
        var is_export_sym = false;
        var has_wasm_export = false;
        var wasm_export_slice: []const u8 = "";
        var link_name_override: ?[]const u8 = null;
        if (!body_ptr.symbol_index.isNone() and
            body_ptr.symbol_index.asInt() < emitter.input.sym_table.symbols.items.len)
        {
            const ffi_meta = extractSymFfiMeta(emitter, body_ptr.symbol_index);
            try recordCollectedLinkLib(emitter, ffi_meta.link_lib_name);
            is_export_sym = ffi_meta.is_export;
            has_wasm_export = ffi_meta.wasm_export_name.len > 0;
            wasm_export_slice = ffi_meta.wasm_export_name;
            if (ffi_meta.link_name.len > 0) {
                link_name_override = ffi_meta.link_name;
            }
        }

        const is_exported_main = std.mem.eql(u8, raw_name, "main") and (is_export_sym or has_wasm_export);
        if (isRootEntryMainCandidateWithEntry(
            body_ptr,
            emitter.input.sym_table,
            raw_name,
            is_exported_main,
            emitter.input.entry_file_id,
        )) {
            emitter.entry_main_body_idx = b_idx;
        }

        var is_unmangled_linker_sym = false;
        const c_name = if (link_name_override) |lnk_str| blk_lnk: {
            is_unmangled_linker_sym = true;
            if (std.mem.eql(u8, lnk_str, "main") and !is_exported_main) {
                break :blk_lnk try emitter.allocator.dupe(u8, "_cx_user_main");
            }
            break :blk_lnk try emitter.allocator.dupe(u8, lnk_str);
        } else if ((is_export_sym or has_wasm_export) and
            (!std.mem.eql(u8, raw_name, "main") or emitter.cfg.target.isWasm()))
        blk_exp: {
            is_unmangled_linker_sym = true;
            break :blk_exp try sanitizeIdentifierAlloc(emitter.allocator, raw_name);
        } else blk: {
            const clean_suffix = try sanitizeIdentifierAlloc(emitter.allocator, raw_name);
            defer emitter.allocator.free(clean_suffix);
            break :blk try formatInternalBodySymbolAlloc(
                emitter.allocator,
                emitter.input.sym_table,
                emitter.input.interner,
                body_ptr,
                b_idx,
                clean_suffix,
            );
        };
        try emitter.body_c_names.append(emitter.allocator, c_name);
        if (is_unmangled_linker_sym) {
            try checkAndRecordExportedLinkerSymbol(
                emitter.allocator,
                &seen_c_exports,
                emitter.input.sym_table,
                emitter.input.diagnostic_sink,
                c_name,
                body_ptr,
            );
        }
        if (has_wasm_export and !std.mem.eql(u8, wasm_export_slice, c_name)) {
            try checkAndRecordExportedLinkerSymbol(
                emitter.allocator,
                &seen_c_exports,
                emitter.input.sym_table,
                emitter.input.diagnostic_sink,
                wasm_export_slice,
                body_ptr,
            );
        }
    }

    for (emitter.input.bodies, 0..) |*body_ptr, body_i| {
        const b_idx: u32 = @intCast(body_i);
        try discoverTypeRecursive(emitter, body_ptr.ret_ty, 0);
        if (emitter.has_async_ops and body_ptr.is_async) {
            try maybeRegisterResultErrCheckType(emitter, body_ptr.ret_ty);
        }
        for (body_ptr.locals.items, 0..) |loc_decl, loc_i| {
            try discoverTypeRecursive(emitter, loc_decl.type_id, 0);
            if (emitter.has_async_ops and body_ptr.is_async and loc_i >= 1 and loc_i <= body_ptr.param_count) {
                const p_mode = loc_decl.mode();
                if (p_mode != .inout_mode and p_mode != .set_mode) {
                    const unwrapped_p = emitter.input.pool.unwrapUnderlyingType(loc_decl.type_id);
                    if (!emitter.input.pool.getFlags(unwrapped_p).is_copy) {
                        try registerDropTypeRecursive(emitter, unwrapped_p, 0);
                    }
                }
            }
        }
        for (body_ptr.consts.items) |mir_const| {
            switch (mir_const) {
                .str_val, .bytes_val => |sym_id| {
                    if (!(try emitter.string_const_set.getOrPut(emitter.allocator, sym_id.asInt())).found_existing) {
                        try emitter.string_const_ids.append(emitter.allocator, sym_id.asInt());
                    }
                },
                .raw_blob => |rb_const| {
                    if (!(try emitter.raw_blob_set.getOrPut(emitter.allocator, rb_const.blob_id)).found_existing) {
                        try emitter.raw_blob_ids.append(emitter.allocator, rb_const);
                    }
                },
                .source_loc => |sloc| {
                    if (!(try emitter.string_const_set.getOrPut(emitter.allocator, sloc.file_sym.asInt())).found_existing) {
                        try emitter.string_const_ids.append(emitter.allocator, sloc.file_sym.asInt());
                    }
                    if (!(try emitter.string_const_set.getOrPut(emitter.allocator, sloc.fn_sym.asInt())).found_existing) {
                        try emitter.string_const_ids.append(emitter.allocator, sloc.fn_sym.asInt());
                    }
                    const sloc_key: u128 = (@as(u128, sloc.file_sym.asInt()) << 96) |
                        (@as(u128, sloc.fn_sym.asInt()) << 64) |
                        (@as(u128, sloc.line) << 32) |
                        @as(u128, sloc.col);
                    if (!emitter.source_loc_map.contains(sloc_key)) {
                        const loc_idx: u32 = @intCast(emitter.source_loc_consts.items.len);
                        try emitter.source_loc_consts.append(emitter.allocator, sloc);
                        try emitter.source_loc_map.put(emitter.allocator, sloc_key, loc_idx);
                    }
                },
                else => {},
            }
        }
        for (0..body_ptr.insts.len) |inst_raw| {
            const inst = body_ptr.insts.get(inst_raw);
            try discoverTypeRecursive(emitter, inst.type_id, 0);
            if (inst.op == .fn_addr) {
                const target_sym = SymbolIndex.fromInt(inst.operands.rhs);
                try maybeRegisterExternSymbol(emitter, DefId.fromInt(inst.operands.lhs), target_sym);
            } else if (inst.op == .bin_op) {
                const bkind: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                if (bkind == .eq or bkind == .ne) {
                    const op_ty = body_ptr.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id;
                    try registerEqTypeRecursive(emitter, op_ty, 0);
                }
            } else if (inst.op == .aggregate_make) {
                const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                if (agg_kind == .closure_make) {
                    try registerClosureThunk(emitter, b_idx, @intCast(inst_raw), inst);
                } else if (agg_kind == .fmt_args_make) {
                    const words = body_ptr.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
                    if (words.len >= 1) {
                        if (extractConstUsizeFromBody(body_ptr, words[0])) |piece_count| {
                            if (words.len >= 1 + piece_count) {
                                const hole_count = (words.len - 1 - piece_count) / 3;
                                var hole_j: usize = 0;
                                while (hole_j < hole_count) : (hole_j += 1) {
                                    const hole_ref_ty = emitter.input.pool.unwrapUnderlyingType(
                                        body_ptr.getInst(MirValueId.fromInt(words[1 + piece_count + hole_j * 3])).type_id,
                                    );
                                    const hole_node = emitter.input.pool.getNode(hole_ref_ty);
                                    const hole_ty = if (hole_node.tag == .ref_ty or
                                        hole_node.tag == .mut_ref_ty or
                                        hole_node.tag == .raw_ptr_ty)
                                        emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(hole_node.lhs))
                                    else
                                        hole_ref_ty;
                                    try registerFmtTypeRecursive(emitter, hole_ty, 0);
                                }
                            }
                        }
                    }
                }
            } else if (inst.op == .intrinsic_op) {
                const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                if (ikind == .drop_in_place or ikind == .drop_if_live) {
                    const place_ty = resolvePlaceResultType(emitter, body_ptr, PlaceId.fromInt(inst.operands.lhs));
                    const dropped_ty = if (inst.type_id != .unit_ty and !inst.type_id.isError())
                        inst.type_id
                    else
                        place_ty;
                    try registerDropTypeRecursive(emitter, dropped_ty, 0);
                } else if (ikind == .fmt_value or ikind == .derive_debug_fmt) {
                    const fmt_args = body_ptr.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
                    if (fmt_args.len >= 1) {
                        try registerFmtTypeRecursive(
                            emitter,
                            body_ptr.getInst(MirValueId.fromInt(fmt_args[0])).type_id,
                            0,
                        );
                    }
                } else if (ikind == .type_name) {
                    const refl_ty = TypeId.fromInt(inst.operands.lhs);
                    if (!(try emitter.type_name_set.getOrPut(emitter.allocator, refl_ty.toU32())).found_existing) {
                        try emitter.type_name_ids.append(emitter.allocator, refl_ty.toU32());
                    }
                } else if (ikind == .ctx_get or ikind == .ctx_set) {
                    emitter.has_context_ops = true;
                    const call_args = body_ptr.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
                    const slot_val_ty = if (ikind == .ctx_get)
                        inst.type_id
                    else if (call_args.len >= 2)
                        body_ptr.getInst(MirValueId.fromInt(call_args[1])).type_id
                    else
                        .unit_ty;
                    const slot_lay = try emitter.resolver.resolveType(slot_val_ty);
                    const aligned_sz = std.mem.alignForward(u64, @max(slot_lay.size_bytes, 8), 8);
                    if (aligned_sz > emitter.ctx_slot_stride_bytes) {
                        emitter.ctx_slot_stride_bytes = aligned_sz;
                    }
                } else if (ikind == .async_spawn) {
                    const sp_args = body_ptr.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
                    if (sp_args.len >= 3) {
                        const fut_ty = emitter.input.pool.unwrapUnderlyingType(
                            body_ptr.getInst(MirValueId.fromInt(sp_args[2])).type_id,
                        );
                        if (emitter.input.pool.getFutureOutputType(fut_ty)) |out_ty| {
                            try maybeRegisterResultErrCheckType(emitter, out_ty);
                        }
                    }
                }
            }
        }
        for (body_ptr.calls.items) |call_site| {
            try discoverTypeRecursive(emitter, call_site.ret_ty, 0);
            if (!call_site.direct_def_id.isNone() or !call_site.direct_symbol.isNone()) {
                try maybeRegisterExternSymbol(emitter, call_site.direct_def_id, call_site.direct_symbol);
            }
        }
    }

    // Sort all collected tables deterministically (`AGENTS.md` §6, `DR-01`):
    std.mem.sort(TypeId, emitter.sorted_candidates.items, {}, struct {
        /// Orders candidate `TypeId`s ascending by raw 32-bit index.
        fn lessThan(_: void, lhs_id: TypeId, rhs_id: TypeId) bool {
            return lhs_id.toU32() < rhs_id.toU32();
        }
    }.lessThan);

    for (emitter.sorted_candidates.items) |cand_ty| {
        try visitTypeTopoDfs(emitter, cand_ty, 0);
    }

    std.mem.sort(u32, emitter.string_const_ids.items, {}, std.sort.asc(u32));
    std.mem.sort(u32, emitter.type_name_ids.items, {}, std.sort.asc(u32));
    std.mem.sort(mir.RawBlobConst, emitter.raw_blob_ids.items, {}, struct {
        /// Orders `RawBlobConst` entries ascending by `blob_id`.
        fn lessThan(_: void, lhs_b: mir.RawBlobConst, rhs_b: mir.RawBlobConst) bool {
            return lhs_b.blob_id < rhs_b.blob_id;
        }
    }.lessThan);
}

/// Records an `extern` function or `extern static` global symbol when referenced without a local `MirBody`.
fn maybeRegisterExternSymbol(
    emitter: *CModuleEmitter,
    def_id: DefId,
    sym_idx: SymbolIndex,
) !void {
    if (resolveBodyIndex(emitter, def_id, sym_idx) != null) return;
    if (sym_idx.isNone() or sym_idx.asInt() >= emitter.input.sym_table.symbols.items.len) return;
    const sym_rec = emitter.input.sym_table.getSymbol(sym_idx).*;
    const ffi_meta = extractSymFfiMeta(emitter, sym_idx);
    try recordCollectedLinkLib(emitter, ffi_meta.link_lib_name);
    if (sym_rec.kind == .fn_sym) {
        if (!(try emitter.extern_sym_set.getOrPut(emitter.allocator, sym_idx.asInt())).found_existing) {
            try emitter.extern_syms.append(emitter.allocator, sym_idx);
            try discoverTypeRecursive(emitter, sym_rec.type_id, 0);
        }
        return;
    }
    if (sym_rec.kind == .extern_static_sym or sym_rec.flags.is_extern) {
        if (!(try emitter.extern_global_sym_set.getOrPut(emitter.allocator, sym_idx.asInt())).found_existing) {
            try emitter.extern_global_syms.append(emitter.allocator, sym_idx);
            try discoverTypeRecursive(emitter, sym_rec.type_id, 0);
        }
    }
}

/// Resolves `(def_id, sym_idx)` to a 0-based index in `emitter.input.bodies` (`null` if external).
fn resolveBodyIndex(
    emitter: *const CModuleEmitter,
    def_id: DefId,
    sym_idx: SymbolIndex,
) ?u32 {
    if (!sym_idx.isNone()) {
        if (emitter.sym_to_body_idx.get(sym_idx.asInt())) |found_sym| return found_sym;
        if (sym_idx.asInt() < emitter.input.sym_table.symbols.items.len) {
            const sym_rec = emitter.input.sym_table.getSymbol(sym_idx).*;
            if (!sym_rec.def_id.isNone()) {
                if (emitter.def_to_body_idx.get(sym_rec.def_id.asInt())) |found_def| return found_def;
            }
        }
    }
    if (!def_id.isNone()) {
        if (emitter.def_to_body_idx.get(def_id.asInt())) |found_by_def| return found_by_def;
    }
    return null;
}

/// Registers a synthesized closure thunk for `MirOp.aggregate_make(.closure_make)`.
fn registerClosureThunk(
    emitter: *CModuleEmitter,
    enclosing_body_idx: u32,
    inst_raw: u32,
    inst: mir.MirInst,
) !void {
    const target_def = DefId.fromInt(inst.operands.lhs);
    const target_body_idx = resolveBodyIndex(emitter, target_def, .none) orelse return;
    const key: u64 = (@as(u64, enclosing_body_idx) << 32) | @as(u64, inst_raw);
    if (emitter.closure_thunk_map.contains(key)) return;

    const closure_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
    const is_three_word = codegen_abi.isThreeWordClosureType(emitter.input.pool, closure_ty);
    const enclosing_body = &emitter.input.bodies[enclosing_body_idx];
    const cap_len: usize = if (inst.operands.rhs < enclosing_body.extra_args.items.len)
        enclosing_body.extra_args.items[inst.operands.rhs]
    else
        0;
    const cap_types = try emitter.allocator.alloc(TypeId, cap_len);
    var cap_i: usize = 0;
    while (cap_i < cap_len) : (cap_i += 1) {
        const cap_val = MirValueId.fromInt(enclosing_body.extra_args.items[inst.operands.rhs + 1 + cap_i]);
        cap_types[cap_i] = enclosing_body.getInst(cap_val).type_id;
        try discoverTypeRecursive(emitter, cap_types[cap_i], 0);
        if (is_three_word) {
            try registerDropTypeRecursive(emitter, cap_types[cap_i], 0);
        }
    }
    if (is_three_word) {
        try registerDropTypeRecursive(emitter, closure_ty, 0);
    }

    const thunk_idx: u32 = @intCast(emitter.closure_thunks.items.len);
    try emitter.closure_thunks.append(emitter.allocator, .{
        .thunk_idx = thunk_idx,
        .closure_ty = closure_ty,
        .target_body_idx = target_body_idx,
        .capture_types = cap_types,
        .is_three_word = is_three_word,
    });
    try emitter.closure_thunk_map.put(emitter.allocator, key, thunk_idx);
}

// ------------- Composite Typedef & Data Emission --------------

/// Emits forward struct/union tag typedefs followed by topologically sorted composite definitions.
fn emitTypeDeclarations(emitter: *CModuleEmitter) !void {
    const usize_c = if (emitter.cfg.target.ptrBytes() == 4) "uint32_t" else "uint64_t";

    for (emitter.ordered_types.items) |ty| {
        if (ty == .str_ty) {
            try emitter.print("typedef cx_str_t _cx_ty_{d};\n", .{ty.toU32()});
            continue;
        }
        if (emitter.input.pool.getNode(ty).tag == .fn_ty) continue;
        const kw = if (emitter.input.pool.getNode(ty).tag == .union_ty)
            "union"
        else
            "struct";
        try emitter.print("typedef {s} _cx_ty_{d} _cx_ty_{d};\n", .{ kw, ty.toU32(), ty.toU32() });
    }
    try emitter.writeAll("\n");

    for (emitter.ordered_types.items) |ty| {
        const ty_u32 = ty.toU32();
        if (ty == .str_ty) {
            const str_lay = try emitter.resolver.resolveType(.str_ty);
            try emitter.print(
                "typedef char _cx_sz_assert_{d}[(sizeof(_cx_ty_{d}) == {d}u) ? 1 : -1];\n",
                .{ ty_u32, ty_u32, str_lay.size_bytes },
            );
            continue;
        }

        const node = emitter.input.pool.getNode(ty);
        if (node.tag == .fn_ty) {
            const sig = emitter.input.pool.getFnSignatureView(ty) orelse continue;
            const ret_c = if (try isZeroSizedType(emitter, sig.ret_ty))
                try emitter.allocator.dupe(u8, "void")
            else
                try formatCType(emitter, sig.ret_ty);
            defer emitter.allocator.free(ret_c);

            try emitter.print("typedef {s} (*_cx_ty_{d})(", .{ ret_c, ty_u32 });
            var emitted_params: usize = 0;
            var param_i: usize = 0;
            while (param_i < sig.paramCount()) : (param_i += 1) {
                const param_ty = sig.getParamType(param_i);
                const param_mode = sig.getParamMode(param_i);
                if (param_mode == .inout_mode or param_mode == .set_mode) {
                    if (emitted_params > 0) try emitter.writeAll(", ");
                    if (try isZeroSizedType(emitter, param_ty)) {
                        try emitter.writeAll("uint8_t *");
                    } else {
                        const param_c = try formatCType(emitter, param_ty);
                        defer emitter.allocator.free(param_c);
                        try emitter.print("{s} *", .{param_c});
                    }
                    emitted_params += 1;
                } else if (!(try isZeroSizedType(emitter, param_ty))) {
                    if (emitted_params > 0) try emitter.writeAll(", ");
                    const param_c = try formatCType(emitter, param_ty);
                    defer emitter.allocator.free(param_c);
                    try emitter.writeAll(param_c);
                    emitted_params += 1;
                }
            }
            if (sig.is_variadic) {
                try emitter.writeAll(if (emitted_params > 0) ", ..." else "...");
            } else if (emitted_params == 0) {
                try emitter.writeAll("void");
            }
            try emitter.writeAll(");\n");
            continue;
        }

        const lay = try emitter.resolver.resolveType(ty);
        const rflags = lay.reprFlags();
        switch (node.tag) {
            .slice_ty => {
                const elem_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const elem_c = if (try isZeroSizedType(emitter, elem_ty))
                    try emitter.allocator.dupe(u8, "uint8_t")
                else
                    try formatCType(emitter, elem_ty);
                defer emitter.allocator.free(elem_c);
                try emitter.print(
                    "struct _cx_ty_{d} {{ {s} *ptr; {s} len; }};\n",
                    .{ ty_u32, elem_c, usize_c },
                );
            },
            .soa_slice_ty => {
                try emitter.print(
                    "struct _cx_ty_{d} {{ uint8_t *ptr; {s} len; }};\n",
                    .{ ty_u32, usize_c },
                );
            },
            .closure_ty => {
                const sig = emitter.input.pool.getFnSignatureView(ty) orelse continue;
                const ret_c = if (try isZeroSizedType(emitter, sig.ret_ty))
                    try emitter.allocator.dupe(u8, "void")
                else
                    try formatCType(emitter, sig.ret_ty);
                defer emitter.allocator.free(ret_c);
                try emitter.print(
                    "struct _cx_ty_{d} {{ uint8_t *env_ptr; {s} (*fn_ptr)(uint8_t *",
                    .{ ty_u32, ret_c },
                );
                var param_i: usize = 0;
                while (param_i < sig.paramCount()) : (param_i += 1) {
                    const param_ty = sig.getParamType(param_i);
                    const param_mode = sig.getParamMode(param_i);
                    if (param_mode == .inout_mode or param_mode == .set_mode) {
                        if (try isZeroSizedType(emitter, param_ty)) {
                            try emitter.writeAll(", uint8_t *");
                        } else {
                            const param_c = try formatCType(emitter, param_ty);
                            defer emitter.allocator.free(param_c);
                            try emitter.print(", {s} *", .{param_c});
                        }
                    } else if (!(try isZeroSizedType(emitter, param_ty))) {
                        const param_c = try formatCType(emitter, param_ty);
                        defer emitter.allocator.free(param_c);
                        try emitter.print(", {s}", .{param_c});
                    }
                }
                if (codegen_abi.isThreeWordClosureType(emitter.input.pool, ty)) {
                    try emitter.writeAll("); void (*drop_fn)(uint8_t *); };\n");
                } else {
                    try emitter.writeAll("); };\n");
                }
            },
            .array_ty => {
                const elem_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const elem_c = try formatCType(emitter, elem_ty);
                defer emitter.allocator.free(elem_c);
                const arr_len: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                try emitter.print(
                    "struct __attribute__((aligned({d}))) _cx_ty_{d} {{ {s} _elems[{d}u]; }};\n",
                    .{ lay.alignBytes(), ty_u32, elem_c, @max(arr_len, 1) },
                );
            },
            .soa_array_ty => {
                try emitter.print(
                    "struct __attribute__((aligned({d}))) _cx_ty_{d} {{ uint8_t _bytes[{d}u]; }};\n",
                    .{ lay.alignBytes(), ty_u32, @max(lay.size_bytes, 1) },
                );
            },
            .union_ty => {
                try emitter.print("union __attribute__((aligned({d}))) _cx_ty_{d} {{\n", .{
                    lay.alignBytes(),
                    ty_u32,
                });
                const is_natural_c_float = rflags.is_repr_c and !rflags.is_packed and
                    (try hasFloatFieldForCAbi(emitter, ty, 0));
                var max_emitted_bytes: u64 = 0;
                const sym_idx = SymbolIndex.fromInt(node.rhs);
                if (!sym_idx.isNone() and sym_idx.asInt() < emitter.input.sym_table.symbols.items.len) {
                    const un_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
                    if (!un_sym.target_scope.isNone()) {
                        const subst = type_system.NominalTypeSubst.init(
                            emitter.input.pool,
                            emitter.input.sym_table,
                            ty,
                        );
                        var fld_ord: u32 = 0;
                        for (emitter.input.sym_table.getScopeMembers(un_sym.target_scope)) |mem_idx| {
                            const mem_sym = emitter.input.sym_table.getSymbol(mem_idx).*;
                            if (mem_sym.kind != .field_sym) continue;
                            const fld_ty = emitter.input.pool.unwrapUnderlyingType(subst.resolve(mem_sym.type_id));
                            if (!(try isZeroSizedType(emitter, fld_ty))) {
                                const fld_lay = try emitter.resolver.resolveType(fld_ty);
                                if (fld_lay.size_bytes > max_emitted_bytes) max_emitted_bytes = fld_lay.size_bytes;
                                const fld_c = try formatCType(emitter, fld_ty);
                                defer emitter.allocator.free(fld_c);
                                try emitter.print("    {s} _f{d};\n", .{ fld_c, fld_ord });
                            }
                            fld_ord += 1;
                        }
                    }
                }
                if (max_emitted_bytes == 0 or
                    !(is_natural_c_float and
                        std.mem.alignForward(u64, max_emitted_bytes, lay.alignBytes()) == lay.size_bytes))
                {
                    try emitter.print("    uint8_t _raw[{d}u];\n", .{@max(lay.size_bytes, 1)});
                }
                try emitter.writeAll("};\n");
            },
            .struct_ty, .tuple_ty => {
                if (rflags.is_packed) {
                    try emitter.print("struct __attribute__((packed)) _cx_ty_{d} {{\n", .{ty_u32});
                } else {
                    try emitter.print("struct __attribute__((aligned({d}))) _cx_ty_{d} {{\n", .{
                        lay.alignBytes(),
                        ty_u32,
                    });
                }
                const fld_start = lay.aux_start;
                const fld_len = lay.aux_len;
                const is_natural_c_float = rflags.is_repr_c and !rflags.is_packed and
                    (try hasFloatFieldForCAbi(emitter, ty, 0));
                var cur_byte: u64 = 0;
                var pad_idx: u32 = 0;
                var phys_i: u32 = 0;
                while (phys_i < fld_len) : (phys_i += 1) {
                    const decl_ord = emitter.resolver.phys_to_decl.items[fld_start + phys_i];
                    const fld = emitter.resolver.fields_by_decl.items[fld_start + decl_ord];
                    if (fld.size_bytes == 0) continue;
                    const natural_off = std.mem.alignForward(
                        u64,
                        cur_byte,
                        @as(u64, 1) << @intCast(fld.align_log2),
                    );
                    if (fld.byte_offset > cur_byte and !(is_natural_c_float and natural_off == fld.byte_offset)) {
                        try emitter.print(
                            "    uint8_t _pad_{d}[{d}u];\n",
                            .{ pad_idx, fld.byte_offset - cur_byte },
                        );
                        pad_idx += 1;
                    }
                    const fld_c = try formatCType(emitter, fld.field_ty);
                    defer emitter.allocator.free(fld_c);
                    try emitter.print("    {s} _f{d};\n", .{ fld_c, decl_ord });
                    cur_byte = fld.byte_offset + fld.size_bytes;
                }
                const natural_end = std.mem.alignForward(u64, cur_byte, lay.alignBytes());
                if (lay.size_bytes > cur_byte and !(is_natural_c_float and natural_end == lay.size_bytes)) {
                    try emitter.print(
                        "    uint8_t _pad_{d}[{d}u];\n",
                        .{ pad_idx, lay.size_bytes - cur_byte },
                    );
                }
                try emitter.writeAll("};\n");
            },
            .optional_ty, .result_ty, .enum_ty => {
                const sum_detail = (try emitter.resolver.getSumDetail(ty)) orelse continue;
                try emitter.print("struct __attribute__((aligned({d}))) _cx_ty_{d} {{\n", .{
                    lay.alignBytes(),
                    ty_u32,
                });
                switch (sum_detail.repr) {
                    .transparent_ok, .niche_single => {
                        const pay_lay = try emitter.resolver.resolveType(sum_detail.payload_ty);
                        if (pay_lay.size_bytes > 0) {
                            const pay_c = try formatCType(emitter, sum_detail.payload_ty);
                            defer emitter.allocator.free(pay_c);
                            try emitter.print("    {s} _pay;\n", .{pay_c});
                        }
                        if (lay.size_bytes > pay_lay.size_bytes) {
                            try emitter.print(
                                "    uint8_t _pad_tail[{d}u];\n",
                                .{lay.size_bytes - pay_lay.size_bytes},
                            );
                        }
                    },
                    .explicit_tag => {
                        const tag_c = resolveUnsignedCTypeForBits(@as(u16, sum_detail.tag_bytes) * 8);
                        try emitter.print("    {s} _tag;\n", .{tag_c});
                        const union_bytes = lay.size_bytes -| sum_detail.payload_offset;
                        if (union_bytes > 0) {
                            if (sum_detail.payload_offset > sum_detail.tag_bytes) {
                                try emitter.print(
                                    "    uint8_t _pad_tag[{d}u];\n",
                                    .{sum_detail.payload_offset - sum_detail.tag_bytes},
                                );
                            }
                            try emitter.writeAll("    union {\n");
                            const variant_count: u32 = switch (node.tag) {
                                .optional_ty, .result_ty => 2,
                                .enum_ty => countEnumVariants(emitter, ty),
                                else => 0,
                            };
                            var var_ord: u32 = 0;
                            while (var_ord < variant_count) : (var_ord += 1) {
                                const var_pay = resolveEnumVariantPayloadType(emitter, ty, var_ord);
                                if (!(try isZeroSizedType(emitter, var_pay))) {
                                    const var_c = try formatCType(emitter, var_pay);
                                    defer emitter.allocator.free(var_c);
                                    try emitter.print("        {s} _v{d};\n", .{ var_c, var_ord });
                                }
                            }
                            try emitter.print("        uint8_t _raw[{d}u];\n    }} _u;\n", .{union_bytes});
                        } else if (lay.size_bytes > sum_detail.tag_bytes) {
                            try emitter.print(
                                "    uint8_t _pad_tail[{d}u];\n",
                                .{lay.size_bytes - sum_detail.tag_bytes},
                            );
                        }
                    },
                    .not_sum => {},
                }
                try emitter.writeAll("};\n");
            },
            .future_ty => {
                const hdr_bytes: u64 = @as(u64, emitter.cfg.target.ptrBytes()) * 4;
                try emitter.print(
                    "struct __attribute__((aligned({d}))) _cx_ty_{d} {{\n" ++
                        "    void *_handle;\n    uintptr_t _kind;\n    uintptr_t _aux;\n    uintptr_t _out_sz;\n",
                    .{ lay.alignBytes(), ty_u32 },
                );
                if (lay.size_bytes > hdr_bytes) {
                    try emitter.print("    uint8_t _out_pad[{d}u];\n", .{lay.size_bytes - hdr_bytes});
                }
                try emitter.writeAll("};\n");
            },
            else => continue,
        }
        try emitter.print(
            "typedef char _cx_sz_assert_{d}[(sizeof(_cx_ty_{d}) == {d}u) ? 1 : -1];\n",
            .{ ty_u32, ty_u32, lay.size_bytes },
        );
    }
    try emitter.writeAll("\n");
}

/// Returns the number of declared variants on `.enum_ty` `sum_ty`.
fn countEnumVariants(emitter: *const CModuleEmitter, sum_ty: TypeId) u32 {
    const node = emitter.input.pool.getNode(sum_ty);
    const sym_idx = SymbolIndex.fromInt(node.rhs);
    if (sym_idx.isNone() or sym_idx.asInt() >= emitter.input.sym_table.symbols.items.len) return 0;
    const enum_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
    if (enum_sym.target_scope.isNone()) return 0;
    var count: u32 = 0;
    for (emitter.input.sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
        if (emitter.input.sym_table.getSymbol(mem_idx).kind == .enum_variant_sym) count += 1;
    }
    return count;
}

/// Emits static `.rodata` string/blob arrays, `--dev` `ErrorReturnTrace`, and `.cx_dev_meta` seam.
fn emitRodataAndDevSeam(emitter: *CModuleEmitter, dev_seam_out: *?[]u8) !void {
    for (emitter.string_const_ids.items) |sym_raw| {
        const str_bytes = emitter.input.interner.get(SymbolId.fromInt(sym_raw));
        if (str_bytes.len == 0) continue;
        try emitter.print("static const uint8_t _cx_str_bytes_{d}[{d}u] = {{", .{ sym_raw, str_bytes.len + 1 });
        for (str_bytes, 0..) |byte_val, idx| {
            if (idx > 0) try emitter.writeAll(",");
            if (idx % RAW_BLOB_BYTES_PER_LINE == 0) try emitter.writeAll("\n   ");
            try emitter.print(" 0x{x:0>2}u", .{byte_val});
        }
        try emitter.writeAll(", 0x00u\n};\n");
    }

    for (emitter.type_name_ids.items) |ty_u32| {
        var name_buf: [512]u8 = undefined;
        const rendered = emitter.input.pool.formatType(
            TypeId.fromInt(ty_u32),
            emitter.input.sym_table,
            &name_buf,
        );
        if (rendered.len == 0) continue;
        try emitter.print("static const uint8_t _cx_tyname_{d}[{d}u] = {{", .{ ty_u32, rendered.len + 1 });
        for (rendered, 0..) |byte_val, idx| {
            if (idx > 0) try emitter.writeAll(",");
            if (idx % RAW_BLOB_BYTES_PER_LINE == 0) try emitter.writeAll("\n   ");
            try emitter.print(" 0x{x:0>2}u", .{byte_val});
        }
        try emitter.writeAll(", 0x00u\n};\n");
    }

    if (emitter.input.blob_store) |bstore| {
        const u8_slice_ty = findDiscoveredByteSliceType(emitter);
        for (emitter.raw_blob_ids.items) |rb_const| {
            const payload = bstore.getBytes(rb_const.blob_id) orelse &[_]u8{};
            if (payload.len > 0) {
                try emitter.print(
                    "static const uint8_t __attribute__((aligned({d}))) _cx_blob_{d}[{d}u] = {{",
                    .{ @as(u32, 1) << @intCast(rb_const.align_log2), rb_const.blob_id, payload.len },
                );
                for (payload, 0..) |byte_val, idx| {
                    if (idx > 0) try emitter.writeAll(",");
                    if (idx % RAW_BLOB_BYTES_PER_LINE == 0) try emitter.writeAll("\n   ");
                    try emitter.print(" 0x{x:0>2}u", .{byte_val});
                }
                try emitter.writeAll("\n};\n");
                if (u8_slice_ty) |sl_ty| {
                    try emitter.print(
                        "static const _cx_ty_{d} _cx_blob_slice_{d} = {{ (uint8_t *)_cx_blob_{d}, {d}u }};\n",
                        .{ sl_ty.toU32(), rb_const.blob_id, rb_const.blob_id, payload.len },
                    );
                }
            } else if (u8_slice_ty) |sl_ty| {
                try emitter.print(
                    "static const _cx_ty_{d} _cx_blob_slice_{d} = {{ (uint8_t *)_cx_empty_rodata, 0u }};\n",
                    .{ sl_ty.toU32(), rb_const.blob_id },
                );
            }
        }
    }

    if (emitter.input.rodata_pool) |rpool| {
        for (rpool.blobs.items, 0..) |rblob, r_idx| {
            try emitter.print(
                "static const uint8_t __attribute__((aligned({d}))) _cx_rodata_{d}[{d}u] = {{",
                .{ @as(u32, 1) << @intCast(rblob.align_log2), r_idx, @max(rblob.bytes.len, 1) },
            );
            if (rblob.bytes.len == 0) {
                try emitter.writeAll(" 0x00u };\n");
            } else {
                for (rblob.bytes, 0..) |byte_val, idx| {
                    if (idx > 0) try emitter.writeAll(",");
                    if (idx % RAW_BLOB_BYTES_PER_LINE == 0) try emitter.writeAll("\n   ");
                    try emitter.print(" 0x{x:0>2}u", .{byte_val});
                }
                try emitter.writeAll("\n};\n");
            }
        }
    }

    for (emitter.source_loc_consts.items, 0..) |sloc, loc_i| {
        const file_bytes = emitter.input.interner.get(sloc.file_sym);
        const fn_bytes = emitter.input.interner.get(sloc.fn_sym);
        try emitter.print("static const cx_source_loc_data_t _cx_loc_{d} = {{ {{ ", .{loc_i});
        if (file_bytes.len > 0) {
            try emitter.print("(uint8_t *)_cx_str_bytes_{d}, {d}u", .{ sloc.file_sym.asInt(), file_bytes.len });
        } else {
            try emitter.writeAll("(uint8_t *)_cx_empty_rodata, 0u");
        }
        try emitter.writeAll(" }, { ");
        if (fn_bytes.len > 0) {
            try emitter.print("(uint8_t *)_cx_str_bytes_{d}, {d}u", .{ sloc.fn_sym.asInt(), fn_bytes.len });
        } else {
            try emitter.writeAll("(uint8_t *)_cx_empty_rodata, 0u");
        }
        try emitter.print(" }}, {d}u, {d}u }};\n", .{ sloc.line, sloc.col });
    }

    if (!emitter.cfg.is_release_mode) {
        try emitter.writeAll(
            \\typedef struct _cx_err_trace_ring {
            \\    uintptr_t pcs[16];
            \\    uint32_t write_idx;
            \\    uint32_t count;
            \\} _cx_err_trace_ring;
            \\static CX_THREAD_LOCAL _cx_err_trace_ring _cx_err_trace = { {0}, 0u, 0u };
            \\static inline void _cx_record_err_ret(uintptr_t site_tag) {
            \\    uint32_t slot_i = _cx_err_trace.write_idx & 15u;
            \\    _cx_err_trace.pcs[slot_i] = site_tag;
            \\    _cx_err_trace.write_idx += 1u;
            \\    if (_cx_err_trace.count < 16u) _cx_err_trace.count += 1u;
            \\}
            \\
        );
    }

    if (emitter.has_context_ops) {
        try emitter.print(
            "static CX_THREAD_LOCAL uint8_t __attribute__((aligned(16))) _cx_tls_ctx[{d}u] = {{0}};\n",
            .{10 * emitter.ctx_slot_stride_bytes},
        );
    }

    if (emitter.has_async_ops) {
        try emitAsyncRuntimeHelpersC(emitter);
    }

    if (emitter.input.is_dev_got_enabled) {
        try emitter.writeAll(
            \\typedef struct __attribute__((aligned(64))) _cx_reload_ctrl_t {
            \\    uint64_t pending_patch_gen;
            \\    uint64_t applied_patch_gen;
            \\    uint64_t ipc_shm_offset;
            \\    uint32_t active_workers;
            \\    uint32_t arrived_workers;
            \\    uint32_t reload_action;
            \\    uint32_t status_flags;
            \\    uint64_t root_state_addr;
            \\    uint32_t root_type_id;
            \\    uint32_t patched_fn_count;
            \\    uint64_t root_field_hash64;
            \\} _cx_reload_ctrl_t;
            \\static _cx_reload_ctrl_t _cx_reload_ctrl = { 0u, 0u, 0u, 1u, 0u, 0u, 0u, 0u, 0xFFFFFFFFu, 0u, 0u };
            \\
        );
        dev_seam_out.* = try buildDevSeamBytes(emitter);
    }
    try emitter.writeAll("\n");
}

/// Emits the C99 stackless coroutine handle, FIFO `TaskGroup` scheduler, and `ReactorVTable` yield seam (`DR-08`).
fn emitAsyncRuntimeHelpersC(emitter: *CModuleEmitter) !void {
    const ctx_stride = emitter.ctx_slot_stride_bytes;
    const ctx_bytes = 10 * ctx_stride;
    try emitter.print(
        "#define _CX_CTX_STRIDE {d}u\n#define _CX_CTX_BYTES {d}u\n",
        .{ ctx_stride, ctx_bytes },
    );
    try emitter.writeAll(
        \\typedef struct _cx_fut_raw_s {
        \\    void *_handle;
        \\    uintptr_t _kind;
        \\    uintptr_t _aux;
        \\    uintptr_t _out_sz;
        \\} _cx_fut_raw_t;
        \\typedef uint8_t (*_cx_err_chk_fn_t)(const void *);
        \\struct _cx_task_group_s;
        \\typedef struct _cx_task_node_s {
        \\    struct _cx_task_group_s *group;
        \\    _cx_fut_raw_t fut;
        \\    uint8_t *res_buf;
        \\    size_t res_sz;
        \\    _cx_err_chk_fn_t err_chk;
        \\    uint8_t ctx_buf[_CX_CTX_BYTES];
        \\    uintptr_t join_waiter;
        \\    uint8_t is_completed;
        \\    uint8_t is_canceled;
        \\    uint8_t is_parked_on_join;
        \\} _cx_task_node_t;
        \\typedef struct _cx_task_group_s {
        \\    _cx_task_node_t **tasks;
        \\    size_t len;
        \\    size_t cap;
        \\    uint8_t is_canceled;
        \\    uint8_t is_exited;
        \\} _cx_task_group_t;
        \\static size_t _cx_coro_frame_size(uint32_t _b_idx);
        \\static size_t _cx_coro_frame_align(uint32_t _b_idx);
        \\static uint32_t _cx_coro_poll_dispatch(uint32_t _b_idx, uint8_t *_frame, void *_out_ptr, uint32_t _action, uint8_t *_parked_out);
        \\
    );
    if (emitter.cfg.target.isFreestanding()) {
        try emitter.writeAll(
            \\static uint8_t __attribute__((aligned(16))) _cx_wasm_async_heap[65536u];
            \\static size_t _cx_wasm_async_heap_off = 0u;
            \\static void *_cx_async_zalloc(size_t _byte_n) {
            \\    if (_byte_n == 0u) _byte_n = 16u;
            \\    size_t _aligned_off = (_cx_wasm_async_heap_off + 15u) & ~(size_t)15u;
            \\    if (_aligned_off > 65536u || _byte_n > 65536u - _aligned_off) __builtin_trap();
            \\    uint8_t *_out_p = &_cx_wasm_async_heap[_aligned_off];
            \\    memset(_out_p, 0, _byte_n);
            \\    _cx_wasm_async_heap_off = _aligned_off + _byte_n;
            \\    return (void *)_out_p;
            \\}
            \\static void *_cx_async_grow_buf(void *_old_p, size_t _old_bytes, size_t _new_bytes) {
            \\    void *_new_p = _cx_async_zalloc(_new_bytes);
            \\    if (_old_p != NULL && _old_bytes > 0u) {
            \\        memcpy(_new_p, _old_p, _old_bytes < _new_bytes ? _old_bytes : _new_bytes);
            \\    }
            \\    return _new_p;
            \\}
            \\static inline void _cx_async_free(void *_ptr) { (void)_ptr; }
            \\
        );
    } else {
        try emitter.writeAll(
            \\static void *_cx_async_zalloc(size_t _byte_n) {
            \\    void *_out_p = calloc(1u, _byte_n == 0u ? 1u : _byte_n);
            \\    if (_out_p == NULL) _cx_rt_trap(0u);
            \\    return _out_p;
            \\}
            \\static void *_cx_async_grow_buf(void *_old_p, size_t _old_bytes, size_t _new_bytes) {
            \\    (void)_old_bytes;
            \\    void *_new_p = realloc(_old_p, _new_bytes == 0u ? 1u : _new_bytes);
            \\    if (_new_p == NULL) _cx_rt_trap(0u);
            \\    return _new_p;
            \\}
            \\static inline void _cx_async_free(void *_ptr) { free(_ptr); }
            \\
        );
    }
    try emitter.writeAll(
        \\static CX_THREAD_LOCAL uintptr_t *_cx_exec_q = NULL;
        \\static CX_THREAD_LOCAL size_t _cx_exec_q_len = 0u;
        \\static CX_THREAD_LOCAL size_t _cx_exec_q_cap = 0u;
        \\static CX_THREAD_LOCAL uintptr_t _cx_active_poll_item = 1u;
        \\static CX_THREAD_LOCAL uint8_t _cx_coro_is_canceling = 0u;
        \\static void _cx_exec_push(uintptr_t _item) {
        \\    if (_cx_exec_q_len >= _cx_exec_q_cap) {
        \\        size_t _nc = _cx_exec_q_cap == 0u ? 64u : (_cx_exec_q_cap * 2u);
        \\        if (_nc <= _cx_exec_q_cap || _nc > (((size_t)-1) / sizeof(uintptr_t))) _cx_rt_trap(0u);
        \\        uintptr_t *_nq = (uintptr_t *)_cx_async_grow_buf(_cx_exec_q, _cx_exec_q_cap * sizeof(uintptr_t), _nc * sizeof(uintptr_t));
        \\        _cx_exec_q = _nq;
        \\        _cx_exec_q_cap = _nc;
        \\    }
        \\    _cx_exec_q[_cx_exec_q_len] = _item;
        \\    _cx_exec_q_len += 1u;
        \\}
        \\static inline void _cx_reactor_notify_yield(uint8_t _reason) {
        \\    const void *_vt = NULL;
        \\    void *_rctx = NULL;
        \\    memcpy(&_vt, &_cx_tls_ctx[8u * _CX_CTX_STRIDE], sizeof(void *));
        \\    memcpy(&_rctx, &_cx_tls_ctx[9u * _CX_CTX_STRIDE], sizeof(void *));
        \\    if (_vt != NULL) {
        \\        typedef void (*_cx_yield_fn_t)(void *, uint8_t);
        \\        _cx_yield_fn_t _yfn = NULL;
        \\        memcpy(&_yfn, ((const uint8_t *)_vt) + 6u * sizeof(void *), sizeof(_yfn));
        \\        if (_yfn != NULL) _yfn(_rctx, _reason);
        \\    }
        \\}
        \\static uint8_t *_cx_coro_alloc(uint32_t _b_idx) {
        \\    size_t _sz = _cx_coro_frame_size(_b_idx);
        \\    size_t _al = _cx_coro_frame_align(_b_idx);
        \\    if (_sz < 16u) _sz = 16u;
        \\    if (_al < 16u) _al = 16u;
        \\    if (_sz > (((size_t)-1) - _al)) _cx_rt_trap(0u);
        \\    uint8_t *_raw = (uint8_t *)_cx_async_zalloc(_sz + _al);
        \\    uintptr_t _raw_a = (uintptr_t)_raw;
        \\    uintptr_t _al_a = (_raw_a + ((uintptr_t)_al - 1u)) & ~((uintptr_t)_al - 1u);
        \\    uint16_t _delta = (uint16_t)(_al_a - _raw_a);
        \\    uint8_t *_fr = _raw + (size_t)_delta;
        \\    memcpy(_fr + 4u, &_b_idx, 4u);
        \\    memcpy(_fr + 12u, &_delta, 2u);
        \\    return _fr;
        \\}
        \\static void _cx_coro_free(uint8_t *_fr) {
        \\    if (_fr == NULL) return;
        \\    uint16_t _delta = 0u;
        \\    memcpy(&_delta, _fr + 12u, 2u);
        \\    _cx_async_free(_fr - (size_t)_delta);
        \\}
        \\static void _cx_async_cancel_node(_cx_task_node_t *_tn);
        \\static void _cx_async_fut_cancel(void *_raw_fut) {
        \\    if (_raw_fut == NULL) return;
        \\    _cx_fut_raw_t *_f = (_cx_fut_raw_t *)_raw_fut;
        \\    uintptr_t _k = _f->_kind;
        \\    void *_h = _f->_handle;
        \\    _f->_kind = 0u;
        \\    _f->_handle = NULL;
        \\    if (_k == 1u && _h != NULL) {
        \\        uint32_t _b_idx = 0u;
        \\        memcpy(&_b_idx, ((uint8_t *)_h) + 4u, 4u);
        \\        uint8_t _prev_c = _cx_coro_is_canceling;
        \\        _cx_coro_is_canceling = 1u;
        \\        (void)_cx_coro_poll_dispatch(_b_idx, (uint8_t *)_h, NULL, 1u, NULL);
        \\        _cx_coro_is_canceling = _prev_c;
        \\        _cx_coro_free((uint8_t *)_h);
        \\    }
        \\}
        \\static uint32_t _cx_async_fut_poll(void *_raw_fut, void *_out_ptr, uint8_t *_parked_out) {
        \\    _cx_fut_raw_t *_f = (_cx_fut_raw_t *)_raw_fut;
        \\    if (_f->_kind == 2u) {
        \\        if (_f->_aux == 0u) {
        \\            _f->_aux = 1u;
        \\            _cx_reactor_notify_yield(0u);
        \\            return 0u;
        \\        }
        \\        _f->_aux = 0xFFFFFFFEu;
        \\        _f->_kind = 0u;
        \\        return 1u;
        \\    }
        \\    if (_f->_kind == 3u) {
        \\        _cx_task_node_t *_tn = (_cx_task_node_t *)_f->_handle;
        \\        if (_tn == NULL) { _f->_kind = 0u; return 1u; }
        \\        if (_tn->is_completed) {
        \\            if (_out_ptr != NULL && _tn->res_sz > 0u && _tn->res_buf != NULL) {
        \\                memcpy(_out_ptr, _tn->res_buf, _tn->res_sz);
        \\            }
        \\            _f->_kind = 0u;
        \\            return 1u;
        \\        }
        \\        _tn->join_waiter = _cx_active_poll_item;
        \\        if (_parked_out != NULL) *_parked_out = 1u;
        \\        return 0u;
        \\    }
        \\    if (_f->_kind == 4u) {
        \\        _cx_task_node_t *_tn = (_cx_task_node_t *)_f->_handle;
        \\        if (_tn != NULL) _cx_async_cancel_node(_tn);
        \\        _f->_kind = 0u;
        \\        return 1u;
        \\    }
        \\    if (_f->_kind == 1u) {
        \\        uint8_t *_fr = (uint8_t *)_f->_handle;
        \\        if (_fr == NULL) { _f->_kind = 0u; return 1u; }
        \\        uint32_t _b_idx = 0u;
        \\        memcpy(&_b_idx, _fr + 4u, 4u);
        \\        if (_cx_coro_poll_dispatch(_b_idx, _fr, _out_ptr, 0u, _parked_out) != 0u) {
        \\            _f->_kind = 0u;
        \\            _f->_handle = NULL;
        \\            _cx_coro_free(_fr);
        \\            return 1u;
        \\        }
        \\        return 0u;
        \\    }
        \\    return 1u;
        \\}
        \\static void _cx_async_group_cancel_all(_cx_task_group_t *_grp) {
        \\    if (_grp == NULL) return;
        \\    _grp->is_canceled = 1u;
        \\    size_t _ri = _grp->len;
        \\    while (_ri > 0u) {
        \\        _ri -= 1u;
        \\        _cx_task_node_t *_tn = _grp->tasks[_ri];
        \\        if ((uintptr_t)_tn == _cx_active_poll_item) continue;
        \\        _cx_async_cancel_node(_tn);
        \\    }
        \\}
        \\static void _cx_async_cancel_node(_cx_task_node_t *_tn) {
        \\    if (_tn == NULL || _tn->is_completed || _tn->is_canceled) return;
        \\    _tn->is_canceled = 1u;
        \\    _tn->is_completed = 1u;
        \\    uint8_t _sctx[_CX_CTX_BYTES];
        \\    uintptr_t _spoll = _cx_active_poll_item;
        \\    memcpy(_sctx, _cx_tls_ctx, _CX_CTX_BYTES);
        \\    memcpy(_cx_tls_ctx, _tn->ctx_buf, _CX_CTX_BYTES);
        \\    _cx_active_poll_item = (uintptr_t)_tn;
        \\    _cx_async_fut_cancel(&_tn->fut);
        \\    _cx_active_poll_item = _spoll;
        \\    memcpy(_cx_tls_ctx, _sctx, _CX_CTX_BYTES);
        \\    if (_tn->join_waiter != 0u) {
        \\        uintptr_t _w = _tn->join_waiter;
        \\        _tn->join_waiter = 0u;
        \\        if (_w != 1u) ((_cx_task_node_t *)_w)->is_parked_on_join = 0u;
        \\        _cx_exec_push(_w);
        \\    }
        \\}
        \\static void _cx_exec_step_task(_cx_task_node_t *_tn) {
        \\    if (_tn == NULL || _tn->is_completed) return;
        \\    uint8_t _sctx[_CX_CTX_BYTES];
        \\    uintptr_t _spoll = _cx_active_poll_item;
        \\    memcpy(_sctx, _cx_tls_ctx, _CX_CTX_BYTES);
        \\    memcpy(_cx_tls_ctx, _tn->ctx_buf, _CX_CTX_BYTES);
        \\    _cx_active_poll_item = (uintptr_t)_tn;
        \\    _tn->is_parked_on_join = 0u;
        \\    uint8_t _parked = 0u;
        \\    uint32_t _rdy = _cx_async_fut_poll(&_tn->fut, _tn->res_buf, &_parked);
        \\    memcpy(_tn->ctx_buf, _cx_tls_ctx, _CX_CTX_BYTES);
        \\    _cx_active_poll_item = _spoll;
        \\    memcpy(_cx_tls_ctx, _sctx, _CX_CTX_BYTES);
        \\    if (_rdy == 0u) {
        \\        _tn->is_parked_on_join = _parked;
        \\        if (!_parked) _cx_exec_push((uintptr_t)_tn);
        \\    } else {
        \\        _tn->is_completed = 1u;
        \\        if (_tn->err_chk != NULL && _tn->res_buf != NULL && _tn->err_chk(_tn->res_buf) != 0u) {
        \\            _cx_async_group_cancel_all(_tn->group);
        \\        }
        \\        if (_tn->join_waiter != 0u) {
        \\            uintptr_t _w = _tn->join_waiter;
        \\            _tn->join_waiter = 0u;
        \\            if (_w != 1u) ((_cx_task_node_t *)_w)->is_parked_on_join = 0u;
        \\            _cx_exec_push(_w);
        \\        }
        \\    }
        \\}
        \\static void *_cx_async_group_enter(void) {
        \\    _cx_task_group_t *_g = (_cx_task_group_t *)_cx_async_zalloc(sizeof(_cx_task_group_t));
        \\    return (void *)_g;
        \\}
        \\static void *_cx_async_spawn(void *_grp_ptr, void *_raw_fut, size_t _out_sz, _cx_err_chk_fn_t _echk) {
        \\    _cx_task_group_t *_g = (_cx_task_group_t *)_grp_ptr;
        \\    _cx_task_node_t *_tn = (_cx_task_node_t *)_cx_async_zalloc(sizeof(_cx_task_node_t));
        \\    _tn->group = _g;
        \\    memcpy(&_tn->fut, _raw_fut, sizeof(_cx_fut_raw_t));
        \\    ((_cx_fut_raw_t *)_raw_fut)->_kind = 0u;
        \\    ((_cx_fut_raw_t *)_raw_fut)->_handle = NULL;
        \\    _tn->res_sz = _out_sz;
        \\    if (_out_sz > 0u) {
        \\        _tn->res_buf = (uint8_t *)_cx_async_zalloc(_out_sz);
        \\    }
        \\    _tn->err_chk = _echk;
        \\    memcpy(_tn->ctx_buf, _cx_tls_ctx, _CX_CTX_BYTES);
        \\    if (_g != NULL) {
        \\        if (_g->len >= _g->cap) {
        \\            size_t _nc = _g->cap == 0u ? 8u : (_g->cap * 2u);
        \\            if (_nc <= _g->cap || _nc > (((size_t)-1) / sizeof(_cx_task_node_t *))) _cx_rt_trap(0u);
        \\            _cx_task_node_t **_nt = (_cx_task_node_t **)_cx_async_grow_buf(
        \\                _g->tasks, _g->cap * sizeof(_cx_task_node_t *), _nc * sizeof(_cx_task_node_t *));
        \\            _g->tasks = _nt;
        \\            _g->cap = _nc;
        \\        }
        \\        _g->tasks[_g->len] = _tn;
        \\        _g->len += 1u;
        \\    }
        \\    _cx_exec_push((uintptr_t)_tn);
        \\    return (void *)_tn;
        \\}
        \\static void _cx_async_group_exit(void *_grp_ptr, uint8_t _is_err_or_cancel) {
        \\    _cx_task_group_t *_g = (_cx_task_group_t *)_grp_ptr;
        \\    if (_g == NULL || _g->is_exited) return;
        \\    if (_is_err_or_cancel || _cx_coro_is_canceling || _g->is_canceled) {
        \\        _cx_async_group_cancel_all(_g);
        \\    } else {
        \\        for (;;) {
        \\            uint8_t _pend = 0u;
        \\            uint8_t _prog = 0u;
        \\            size_t _ti = 0u;
        \\            while (_ti < _g->len) {
        \\                _cx_task_node_t *_tn = _g->tasks[_ti];
        \\                if (!_tn->is_completed) {
        \\                    _pend = 1u;
        \\                    if (!_tn->is_parked_on_join) {
        \\                        _prog = 1u;
        \\                        _cx_exec_step_task(_tn);
        \\                        if (_g->is_canceled) {
        \\                            _cx_async_group_cancel_all(_g);
        \\                            _pend = 0u;
        \\                            break;
        \\                        }
        \\                    }
        \\                }
        \\                _ti += 1u;
        \\            }
        \\            if (!_pend) break;
        \\            if (!_prog) {
        \\                uint8_t _stepped_q = 0u;
        \\                size_t _qi = 0u;
        \\                while (_qi < _cx_exec_q_len) {
        \\                    uintptr_t _qit = _cx_exec_q[_qi];
        \\                    if (_qit > 1u && _qit != _cx_active_poll_item) {
        \\                        _cx_task_node_t *_otn = (_cx_task_node_t *)_qit;
        \\                        if (!_otn->is_completed && !_otn->is_parked_on_join) {
        \\                            _cx_exec_q[_qi] = 0u;
        \\                            _stepped_q = 1u;
        \\                            _cx_exec_step_task(_otn);
        \\                            break;
        \\                        }
        \\                    }
        \\                    _qi += 1u;
        \\                }
        \\                if (!_stepped_q) _cx_rt_trap(0u);
        \\            }
        \\        }
        \\    }
        \\    _g->is_exited = 1u;
        \\    {
        \\        size_t _qi = 0u;
        \\        while (_qi < _cx_exec_q_len) {
        \\            uintptr_t _qit = _cx_exec_q[_qi];
        \\            if (_qit > 1u && ((_cx_task_node_t *)_qit)->group == _g) {
        \\                _cx_exec_q[_qi] = 0u;
        \\            }
        \\            _qi += 1u;
        \\        }
        \\        size_t _fi = 0u;
        \\        while (_fi < _g->len) {
        \\            _cx_task_node_t *_tn = _g->tasks[_fi];
        \\            if (_tn != NULL) {
        \\                _cx_async_fut_cancel(&_tn->fut);
        \\                if (_tn->res_buf != NULL) _cx_async_free(_tn->res_buf);
        \\                _cx_async_free(_tn);
        \\            }
        \\            _fi += 1u;
        \\        }
        \\        if (_g->tasks != NULL) _cx_async_free(_g->tasks);
        \\        _cx_async_free(_g);
        \\    }
        \\}
        \\static void _cx_async_block_on(void *_raw_fut, void *_out_ptr) {
        \\    _cx_fut_raw_t _rf;
        \\    memcpy(&_rf, _raw_fut, sizeof(_cx_fut_raw_t));
        \\    ((_cx_fut_raw_t *)_raw_fut)->_kind = 0u;
        \\    ((_cx_fut_raw_t *)_raw_fut)->_handle = NULL;
        \\    size_t _q_base = _cx_exec_q_len;
        \\    uintptr_t _spoll = _cx_active_poll_item;
        \\    uint8_t _base_ctx[_CX_CTX_BYTES];
        \\    uint8_t _root_ctx[_CX_CTX_BYTES];
        \\    memcpy(_base_ctx, _cx_tls_ctx, _CX_CTX_BYTES);
        \\    memcpy(_root_ctx, _cx_tls_ctx, _CX_CTX_BYTES);
        \\    uint8_t _root_parked = 0u;
        \\    _cx_exec_push(1u);
        \\    size_t _q_head = _q_base;
        \\    for (;;) {
        \\        while (_q_head < _cx_exec_q_len && _cx_exec_q[_q_head] == 0u) {
        \\            _q_head += 1u;
        \\        }
        \\        if (_q_head >= _cx_exec_q_len) {
        \\            _cx_rt_trap(0u);
        \\        }
        \\        uintptr_t _it = _cx_exec_q[_q_head];
        \\        _cx_exec_q[_q_head] = 0u;
        \\        _q_head += 1u;
        \\        if (_q_head == _cx_exec_q_len) {
        \\            _q_head = _q_base;
        \\            _cx_exec_q_len = _q_base;
        \\        }
        \\        if (_it == 1u) {
        \\            memcpy(_cx_tls_ctx, _root_ctx, _CX_CTX_BYTES);
        \\            _cx_active_poll_item = 1u;
        \\            _root_parked = 0u;
        \\            uint32_t _done = _cx_async_fut_poll(&_rf, _out_ptr, &_root_parked);
        \\            memcpy(_root_ctx, _cx_tls_ctx, _CX_CTX_BYTES);
        \\            memcpy(_cx_tls_ctx, _base_ctx, _CX_CTX_BYTES);
        \\            if (_done != 0u) {
        \\                memcpy(_cx_tls_ctx, _root_ctx, _CX_CTX_BYTES);
        \\                _cx_active_poll_item = _spoll;
        \\                _cx_exec_q_len = _q_base;
        \\                if (_q_base == 0u && _cx_exec_q != NULL) {
        \\                    _cx_async_free(_cx_exec_q);
        \\                    _cx_exec_q = NULL;
        \\                    _cx_exec_q_cap = 0u;
        \\                }
        \\                return;
        \\            }
        \\            if (!_root_parked) _cx_exec_push(1u);
        \\        } else if (_it != 0u) {
        \\            _cx_exec_step_task((_cx_task_node_t *)_it);
        \\            memcpy(_cx_tls_ctx, _base_ctx, _CX_CTX_BYTES);
        \\        }
        \\    }
        \\}
        \\
    );
}

/// Finds `[u8]` (`slice_ty` of `u8_ty`) in `ordered_types` if referenced in the module.
fn findDiscoveredByteSliceType(emitter: *const CModuleEmitter) ?TypeId {
    for (emitter.ordered_types.items) |cand_ty| {
        if (cand_ty == .str_ty) continue;
        const node = emitter.input.pool.getNode(cand_ty);
        if (node.tag == .slice_ty and TypeId.fromInt(node.lhs) == .u8_ty) {
            return cand_ty;
        }
    }
    return null;
}

/// Builds serialized `.cx_dev_meta` binary metadata (`DR-19` §1.2) for `--dev` GOT builds.
fn buildDevSeamBytes(emitter: *CModuleEmitter) ![]u8 {
    var got_slots = try emitter.allocator.alloc(
        codegen_dev_seam.CxGotSlotMeta,
        emitter.input.bodies.len,
    );
    defer emitter.allocator.free(got_slots);

    var classifier_params: std.ArrayListUnmanaged(codegen_abi.FnParamSpec) = .empty;
    defer classifier_params.deinit(emitter.allocator);

    var total_loop_contracts: u32 = 0;
    for (emitter.input.bodies, 0..) |*body_ptr, body_i| {
        total_loop_contracts +|= @intCast(body_ptr.loop_contracts.items.len);
        classifier_params.clearRetainingCapacity();
        var arg_i: u32 = 0;
        while (arg_i < body_ptr.param_count) : (arg_i += 1) {
            const p_decl = body_ptr.locals.items[1 + arg_i];
            try classifier_params.append(emitter.allocator, .{
                .type_id = p_decl.type_id,
                .mode = p_decl.mode(),
            });
        }
        var abi_recipe = try codegen_abi.AbiClassifier.classifyFn(
            emitter.allocator,
            &emitter.resolver,
            .{
                .params = classifier_params.items,
                .ret_ty = body_ptr.ret_ty,
                .is_contextless = body_ptr.is_contextless,
                .is_extern_c = isBodyExternallyVisible(emitter, body_ptr),
            },
        );
        defer abi_recipe.deinit(emitter.allocator);
        got_slots[body_i] = .{
            .def_id = body_ptr.def_id,
            .got_idx = @intCast(body_i),
            .abi_sig_hash64 = abi_recipe.abiSigHash64(),
            .slot_kind = .direct_fn,
        };
    }

    const type_records = try query_db.collectModuleDevTypeRecords(
        emitter.allocator,
        emitter.input.bodies,
        emitter.input.pool,
        emitter.input.sym_table,
        emitter.target_layout,
    );
    defer emitter.allocator.free(type_records);

    return codegen_dev_seam.serializeDevSeamMeta(
        emitter.allocator,
        .{
            .arch_os_tag = emitter.cfg.target.archOsTag(),
            .loop_contract_count = total_loop_contracts,
        },
        got_slots,
        type_records,
    );
}

// --------- Prototypes, Drop Helpers & Closure Thunks ----------

/// Finds the 0-based `MirBody` index implementing `Drop.drop` for unwrapped `ty` (`null` if none).
fn lookupDropBodyIndexForType(emitter: *const CModuleEmitter, ty: TypeId) ?u32 {
    const ty_node = emitter.input.pool.getNode(ty);
    if (ty_node.tag == .struct_ty or ty_node.tag == .enum_ty or ty_node.tag == .union_ty) {
        const sym_idx = SymbolIndex.fromInt(ty_node.rhs);
        if (!sym_idx.isNone() and sym_idx.asInt() < emitter.input.sym_table.symbols.items.len) {
            const nom_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
            if (!nom_sym.target_scope.isNone()) {
                for (emitter.input.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                    const mem_sym = emitter.input.sym_table.getSymbol(mem_idx).*;
                    if (mem_sym.kind == .fn_sym and std.mem.eql(u8, mem_sym.name_text, "drop")) {
                        if (resolveBodyIndex(emitter, mem_sym.def_id, mem_idx)) |found_b| {
                            return found_b;
                        }
                    }
                }
            }
        }
    }
    for (emitter.input.bodies, 0..) |*cand_body, b_idx| {
        if (cand_body.param_count != 1 or cand_body.locals.items.len < 2) continue;
        const fn_name = emitter.input.interner.get(cand_body.name);
        if (!std.mem.eql(u8, fn_name, "drop") and
            !std.mem.endsWith(u8, fn_name, ".drop")) continue;
        const raw_param_ty = emitter.input.pool.unwrapUnderlyingType(cand_body.locals.items[1].type_id);
        const param_node = emitter.input.pool.getNode(raw_param_ty);
        const self_ty = if (param_node.tag == .ref_ty or
            param_node.tag == .mut_ref_ty or
            param_node.tag == .raw_ptr_ty)
            emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(param_node.lhs))
        else
            raw_param_ty;
        if (self_ty == ty) return @intCast(b_idx);
    }
    return null;
}

/// Emits function signature parameter list `(Param0 _arg_1, …)` for `body` (`emit_names = false` for typedefs).
fn emitBodyParamList(emitter: *CModuleEmitter, body: *const MirBody, has_param_names: bool) !void {
    try emitter.writeAll("(");
    var emitted_count: u32 = 0;
    var arg_i: u32 = 0;
    while (arg_i < body.param_count) : (arg_i += 1) {
        const loc_idx = 1 + arg_i;
        const loc_decl = body.locals.items[loc_idx];
        const p_mode = loc_decl.mode();
        if (p_mode == .inout_mode or p_mode == .set_mode) {
            if (emitted_count > 0) try emitter.writeAll(", ");
            if (try isZeroSizedType(emitter, loc_decl.type_id)) {
                if (has_param_names) {
                    try emitter.print("uint8_t *_arg_{d}", .{loc_idx});
                } else {
                    try emitter.writeAll("uint8_t *");
                }
            } else {
                const param_c = try formatCType(emitter, loc_decl.type_id);
                defer emitter.allocator.free(param_c);
                if (has_param_names) {
                    try emitter.print("{s} *_arg_{d}", .{ param_c, loc_idx });
                } else {
                    try emitter.print("{s} *", .{param_c});
                }
            }
            emitted_count += 1;
        } else if (!(try isZeroSizedType(emitter, loc_decl.type_id))) {
            if (emitted_count > 0) try emitter.writeAll(", ");
            const param_c = try formatCType(emitter, loc_decl.type_id);
            defer emitter.allocator.free(param_c);
            if (has_param_names) {
                try emitter.print("{s} _arg_{d}", .{ param_c, loc_idx });
            } else {
                try emitter.writeAll(param_c);
            }
            emitted_count += 1;
        }
    }
    if (emitted_count == 0) try emitter.writeAll("void");
    try emitter.writeAll(")");
}

/// Returns `true` if `body` carries `@export`, `@wasm_export`, or `@link_name` external visibility.
fn isBodyExternallyVisible(emitter: *const CModuleEmitter, body: *const MirBody) bool {
    if (body.symbol_index.isNone() or
        body.symbol_index.asInt() >= emitter.input.sym_table.symbols.items.len) return false;
    const sym_rec = emitter.input.sym_table.getSymbol(body.symbol_index).*;
    if (sym_rec.contract_flags.is_export or sym_rec.contract_flags.has_link_name) return true;
    const ffi_meta = extractSymFfiMeta(emitter, body.symbol_index);
    return ffi_meta.wasm_export_name.len > 0;
}

/// Emits C99 function attributes (`export_name`, `section`, `nothrow`) for `body`.
fn emitBodyFunctionAttributesC(
    emitter: *CModuleEmitter,
    body: *const MirBody,
    is_definition: bool,
) !void {
    if (body.symbol_index.isNone() or
        body.symbol_index.asInt() >= emitter.input.sym_table.symbols.items.len) return;
    const sym_rec = emitter.input.sym_table.getSymbol(body.symbol_index).*;
    const ffi_meta = extractSymFfiMeta(emitter, body.symbol_index);

    if (emitter.cfg.target.isWasm()) {
        const exp_name = if (ffi_meta.wasm_export_name.len > 0)
            ffi_meta.wasm_export_name
        else if (ffi_meta.is_export)
            (if (ffi_meta.link_name.len > 0) ffi_meta.link_name else sym_rec.name_text)
        else
            "";
        if (exp_name.len > 0) {
            try emitter.writeAll("__attribute__((export_name(\"");
            try appendEscapedCStringContents(emitter, exp_name);
            try emitter.writeAll("\"))) ");
        }
    }

    if (is_definition and ffi_meta.link_section.len > 0 and !emitter.cfg.target.isWasm()) {
        try emitter.writeAll("__attribute__((section(\"");
        try appendEscapedCStringContents(emitter, ffi_meta.link_section);
        try emitter.writeAll("\"))) ");
    }

    if (isBodyCAbiBoundary(emitter, body)) {
        try emitter.writeAll("__attribute__((nothrow)) ");
    }
}

/// Appends `raw_text` as ISO C99 escaped string-literal contents (guarding `??` trigraphs).
fn appendEscapedCStringContents(emitter: *CModuleEmitter, raw_text: []const u8) !void {
    for (raw_text, 0..) |ch_b, idx| {
        if (ch_b == '\\' or ch_b == '"') {
            try emitter.writeAll("\\");
            try emitter.out.append(emitter.allocator, ch_b);
        } else if (ch_b == '?' and idx > 0 and raw_text[idx - 1] == '?') {
            try emitter.writeAll("\\?");
        } else if (ch_b >= 0x20 and ch_b <= 0x7E) {
            try emitter.out.append(emitter.allocator, ch_b);
        } else {
            try emitter.print("\\x{x:0>2}", .{ch_b});
        }
    }
}

/// Emits extern declarations, `MirBody` prototypes, `--dev` GOT table, closure thunks, drops, and eq helpers.
fn emitCallablePrototypesAndDrops(emitter: *CModuleEmitter) !void {
    for (emitter.extern_syms.items) |sym_idx| {
        const sym_rec = emitter.input.sym_table.getSymbol(sym_idx).*;
        const sig = emitter.input.pool.getFnSignatureView(sym_rec.type_id) orelse continue;
        const ffi_meta = extractSymFfiMeta(emitter, sym_idx);
        const ext_name = if (ffi_meta.link_name.len > 0) ffi_meta.link_name else sym_rec.name_text;
        const is_wasi_import = emitter.cfg.target.os == .wasi and WASI_PREVIEW1_IMPORT_SET.has(ext_name);
        const has_wasm_attr = emitter.cfg.target.isWasm() and
            (ffi_meta.wasm_import_module.len > 0 or
                ffi_meta.wasm_import_name.len > 0 or
                is_wasi_import or
                emitter.cfg.target.isFreestanding());
        const ret_c = if (try isZeroSizedType(emitter, sig.ret_ty))
            try emitter.allocator.dupe(u8, "void")
        else
            try formatCType(emitter, sig.ret_ty);
        defer emitter.allocator.free(ret_c);
        if (has_wasm_attr) {
            const mod_name = if (ffi_meta.wasm_import_module.len > 0)
                ffi_meta.wasm_import_module
            else if (is_wasi_import)
                "wasi_snapshot_preview1"
            else
                "env";
            const imp_name = if (ffi_meta.wasm_import_name.len > 0) ffi_meta.wasm_import_name else ext_name;
            try emitter.writeAll("__attribute__((import_module(\"");
            try appendEscapedCStringContents(emitter, mod_name);
            try emitter.writeAll("\"), import_name(\"");
            try appendEscapedCStringContents(emitter, imp_name);
            try emitter.writeAll("\"))) ");
        }
        try emitter.writeAll("__attribute__((nothrow)) ");
        try emitter.print("extern {s} _cx_ext_{d}(", .{ ret_c, sym_idx.asInt() });
        var emitted_p: usize = 0;
        var param_i: usize = 0;
        while (param_i < sig.paramCount()) : (param_i += 1) {
            const p_ty = sig.getParamType(param_i);
            const p_mode = sig.getParamMode(param_i);
            if (p_mode == .inout_mode or p_mode == .set_mode) {
                if (emitted_p > 0) try emitter.writeAll(", ");
                if (try isZeroSizedType(emitter, p_ty)) {
                    try emitter.writeAll("uint8_t *");
                } else {
                    const p_c = try formatCType(emitter, p_ty);
                    defer emitter.allocator.free(p_c);
                    try emitter.print("{s} *", .{p_c});
                }
                emitted_p += 1;
            } else if (!(try isZeroSizedType(emitter, p_ty))) {
                if (emitted_p > 0) try emitter.writeAll(", ");
                const p_c = try formatCType(emitter, p_ty);
                defer emitter.allocator.free(p_c);
                try emitter.writeAll(p_c);
                emitted_p += 1;
            }
        }
        if (sig.is_variadic) {
            try emitter.writeAll(if (emitted_p > 0) ", ..." else "...");
        } else if (emitted_p == 0) {
            try emitter.writeAll("void");
        }
        if (has_wasm_attr) {
            try emitter.writeAll(");\n");
        } else {
            try emitter.writeAll(") __asm__(\"");
            if (emitter.cfg.target.os == .macos and ext_name.len > 0 and ext_name[0] != 0x01) {
                try emitter.writeAll("_");
            }
            const raw_asm = if (ext_name.len > 0 and ext_name[0] == 0x01) ext_name[1..] else ext_name;
            try appendEscapedCStringContents(emitter, raw_asm);
            try emitter.writeAll("\");\n");
        }
    }

    for (emitter.extern_global_syms.items) |glob_sym_idx| {
        const glob_rec = emitter.input.sym_table.getSymbol(glob_sym_idx).*;
        const ffi_meta = extractSymFfiMeta(emitter, glob_sym_idx);
        const ext_name = if (ffi_meta.link_name.len > 0) ffi_meta.link_name else glob_rec.name_text;
        const glob_c = if (try isZeroSizedType(emitter, glob_rec.type_id))
            try emitter.allocator.dupe(u8, "uint8_t")
        else
            try formatCType(emitter, glob_rec.type_id);
        defer emitter.allocator.free(glob_c);

        try emitter.writeAll("extern ");
        if (ffi_meta.is_thread_local) {
            try emitter.writeAll("CX_THREAD_LOCAL ");
        }
        try emitter.print("{s} _cx_ext_glob_{d} __asm__(\"", .{ glob_c, glob_sym_idx.asInt() });
        if (emitter.cfg.target.os == .macos and ext_name.len > 0 and ext_name[0] != 0x01) {
            try emitter.writeAll("_");
        }
        const raw_asm = if (ext_name.len > 0 and ext_name[0] == 0x01) ext_name[1..] else ext_name;
        try appendEscapedCStringContents(emitter, raw_asm);
        try emitter.writeAll("\");\n");
    }

    for (emitter.input.bodies, 0..) |*body_ptr, b_idx| {
        const ret_c = if (try isZeroSizedType(emitter, body_ptr.ret_ty))
            try emitter.allocator.dupe(u8, "void")
        else
            try formatCType(emitter, body_ptr.ret_ty);
        defer emitter.allocator.free(ret_c);

        if (emitter.input.is_dev_got_enabled) {
            try emitter.print("typedef {s} (*_cx_body_fn_t_{d})", .{ ret_c, b_idx });
            try emitBodyParamList(emitter, body_ptr, false);
            try emitter.writeAll(";\n");
        }
        try emitBodyFunctionAttributesC(emitter, body_ptr, false);
        const storage_kw = if (isBodyExternallyVisible(emitter, body_ptr)) "" else "static ";
        try emitter.print("{s}{s} {s}", .{ storage_kw, ret_c, emitter.body_c_names.items[b_idx] });
        try emitBodyParamList(emitter, body_ptr, true);
        try emitter.writeAll(";\n");
    }

    if (emitter.input.is_dev_got_enabled) {
        const slot_len = @max(emitter.input.bodies.len, 1);
        try emitter.print("static _cx_fn_slot_t _cx_dev_got[{d}u] = {{\n", .{slot_len});
        if (emitter.input.bodies.len == 0) {
            try emitter.writeAll("    (_cx_fn_slot_t)0\n");
        } else {
            for (emitter.body_c_names.items, 0..) |c_name, b_idx| {
                const comma = if (b_idx + 1 < emitter.body_c_names.items.len) "," else "";
                try emitter.print("    (_cx_fn_slot_t){s}{s}\n", .{ c_name, comma });
            }
        }
        try emitter.writeAll("};\n");
    }

    for (emitter.ordered_drop_types.items) |drop_ty| {
        if (try isZeroSizedType(emitter, drop_ty)) continue;
        const drop_c = try formatCType(emitter, drop_ty);
        defer emitter.allocator.free(drop_c);
        try emitter.print("static void _cx_drop_ty_{d}({s} *_self_ptr);\n", .{ drop_ty.toU32(), drop_c });
    }

    for (emitter.ordered_eq_types.items) |eq_ty| {
        if (try isZeroSizedType(emitter, eq_ty)) continue;
        const eq_c = try formatCType(emitter, eq_ty);
        defer emitter.allocator.free(eq_c);
        try emitter.print(
            "static uint8_t _cx_eq_ty_{d}(const {s} *_lhs, const {s} *_rhs);\n",
            .{ eq_ty.toU32(), eq_c, eq_c },
        );
    }

    for (emitter.ordered_fmt_types.items) |fmt_ty| {
        try emitter.print(
            "static void _cx_fmt_fn_ty_{d}(_cx_rt_buf_t *_out_b, const void *_val_p, uint32_t _spec_lo, uint32_t _spec_hi);\n",
            .{fmt_ty.toU32()},
        );
    }

    for (emitter.closure_thunks.items) |thunk| {
        if (thunk.capture_types.len > 0) {
            try emitter.print("typedef struct _cx_cenv_{d} {{\n", .{thunk.thunk_idx});
            for (thunk.capture_types, 0..) |cap_ty, cap_i| {
                if (try isZeroSizedType(emitter, cap_ty)) continue;
                const cap_c = try formatCType(emitter, cap_ty);
                defer emitter.allocator.free(cap_c);
                try emitter.print("    {s} _c{d};\n", .{ cap_c, cap_i });
            }
            try emitter.print("    uint8_t _guard;\n}} _cx_cenv_{d};\n", .{thunk.thunk_idx});
        }
        try emitClosureThunkDefinition(emitter, thunk);
        if (thunk.is_three_word and thunk.capture_types.len > 0) {
            try emitClosureEnvDropDefinition(emitter, thunk);
        }
    }

    for (emitter.ordered_drop_types.items) |drop_ty| {
        if (try isZeroSizedType(emitter, drop_ty)) continue;
        try emitDropHelperDefinition(emitter, drop_ty);
    }

    for (emitter.ordered_eq_types.items) |eq_ty| {
        if (try isZeroSizedType(emitter, eq_ty)) continue;
        try emitEqHelperDefinition(emitter, eq_ty);
    }

    for (emitter.ordered_fmt_types.items) |fmt_ty| {
        try emitFmtHelperDefinition(emitter, fmt_ty);
    }

    if (emitter.has_async_ops) {
        try emitAsyncDispatchTablesC(emitter);
    }
    try emitter.writeAll("\n");
}

/// Computes total coroutine frame size and alignment including C99 `_fmt_*` / `_stmp_*` / `_ctx_snap_*` scratch slots.
fn computeCoroFrameTotalAndAlignC(
    emitter: *CModuleEmitter,
    body: *const MirBody,
    plan: *const mir_async.AsyncBodyPlan,
) !struct { final_bytes: u64, max_align: u32 } {
    var max_align: u32 = @max(plan.frame_align, 16);
    var cursor: u64 = std.mem.alignForward(
        u64,
        @max(@as(u64, plan.frame_layout.total_frame_bytes), 16),
        @as(u64, max_align),
    );
    const ptr_bytes: u64 = emitter.cfg.target.ptrBytes();
    const ptr_scratch_align: u64 = @max(ptr_bytes, 8);
    const piece_stride: u64 = 2 * ptr_bytes;
    const arg_stride: u64 = std.mem.alignForward(u64, 2 * ptr_bytes + 8, ptr_bytes);

    for (0..body.insts.len) |inst_i| {
        const inst = body.insts.get(inst_i);
        if (inst.op.isGhost()) continue;
        if (inst.op == .aggregate_make) {
            const agg_k: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            if (agg_k == .fmt_args_make and !isStaticConstFmtArgsMake(body, inst)) {
                const words = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
                if (words.len >= 1) {
                    if (extractConstUsizeFromBody(body, words[0])) |piece_count| {
                        if (piece_count > 0) {
                            cursor = std.mem.alignForward(u64, cursor, ptr_scratch_align);
                            cursor += @as(u64, piece_count) * piece_stride;
                        }
                        if (words.len >= 1 + piece_count) {
                            const hole_count = (words.len - 1 - piece_count) / 3;
                            if (hole_count > 0) {
                                cursor = std.mem.alignForward(u64, cursor, ptr_scratch_align);
                                cursor += @as(u64, hole_count) * arg_stride;
                                for (0..hole_count) |hole_j| {
                                    const hole_ref_raw = words[1 + piece_count + hole_j * 3];
                                    const hole_ref_ty = emitter.input.pool.unwrapUnderlyingType(
                                        body.getInst(MirValueId.fromInt(hole_ref_raw)).type_id,
                                    );
                                    const hole_node = emitter.input.pool.getNode(hole_ref_ty);
                                    const is_ptr_arg = hole_node.tag == .ref_ty or
                                        hole_node.tag == .mut_ref_ty or
                                        hole_node.tag == .raw_ptr_ty;
                                    if (!is_ptr_arg and !(try isZeroSizedType(emitter, hole_ref_ty))) {
                                        const h_lay = try emitter.resolver.resolveType(hole_ref_ty);
                                        const h_al = @max(h_lay.alignBytes(), 8);
                                        max_align = @max(max_align, h_al);
                                        cursor = std.mem.alignForward(u64, cursor, h_al);
                                        cursor += @max(h_lay.size_bytes, 1);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        if (inst.op == .place_addr or inst.op == .unary_op or inst.op == .intrinsic_op) {
            if (resolveSliceRefPointee(emitter, inst.type_id)) |sl_pointee| {
                const sl_lay = try emitter.resolver.resolveType(sl_pointee);
                const sl_al = @max(sl_lay.alignBytes(), 8);
                max_align = @max(max_align, sl_al);
                cursor = std.mem.alignForward(u64, cursor, sl_al);
                cursor += @max(sl_lay.size_bytes, 16);
            }
        }
        if (inst.op == .intrinsic_op and @as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)) == .ctx_get) {
            if (type_system.ContextFieldLayout.resolveRefPointee(
                emitter.input.pool,
                emitter.input.sym_table,
                inst.type_id,
            )) |ctx_pointee| {
                if (!(try isZeroSizedType(emitter, ctx_pointee))) {
                    const ctx_lay = try emitter.resolver.resolveType(ctx_pointee);
                    const ctx_al = @max(ctx_lay.alignBytes(), 8);
                    max_align = @max(max_align, ctx_al);
                    cursor = std.mem.alignForward(u64, cursor, ctx_al);
                    cursor += @max(ctx_lay.size_bytes, 8);
                }
            }
        }
    }
    return .{
        .final_bytes = std.mem.alignForward(u64, cursor, max_align),
        .max_align = max_align,
    };
}

/// Emits `_cx_coro_poll_<idx>` prototypes, `_cx_is_err_ty_<id>` helpers, and coroutine dispatch tables.
fn emitAsyncDispatchTablesC(emitter: *CModuleEmitter) !void {
    const plan_mod = &(emitter.async_plan orelse return);

    for (emitter.ordered_res_err_types.items) |res_ty| {
        const res_c = try formatCType(emitter, res_ty);
        defer emitter.allocator.free(res_c);
        const sum_detail = (try emitter.resolver.getSumDetail(res_ty)) orelse continue;
        const discr_expr = try formatSumDiscrReadExpr(emitter, res_ty, sum_detail, "_rv");
        defer emitter.allocator.free(discr_expr);
        try emitter.print(
            "static uint8_t _cx_is_err_ty_{d}(const void *_rp) {{\n" ++
                "    {s} _rv; memcpy(&_rv, _rp, sizeof(_rv));\n" ++
                "    return (({s}) == 1u) ? 1u : 0u;\n}}\n",
            .{ res_ty.toU32(), res_c, discr_expr },
        );
    }

    for (emitter.input.bodies, 0..) |*body_ptr, b_idx| {
        if (!body_ptr.is_async) continue;
        try emitter.print(
            "static uint32_t _cx_coro_poll_{d}(uint8_t *_frame, void *_out_ptr, uint32_t _action, uint8_t *_parked_out);\n",
            .{b_idx},
        );
    }

    try emitter.writeAll("static size_t _cx_coro_frame_size(uint32_t _b_idx) {\n    switch (_b_idx) {\n");
    for (emitter.input.bodies, 0..) |*body_ptr, b_idx| {
        if (!body_ptr.is_async) continue;
        const sizing = try computeCoroFrameTotalAndAlignC(emitter, body_ptr, plan_mod.getBodyPlan(b_idx));
        try emitter.print("    case {d}u: return {d}u;\n", .{ b_idx, sizing.final_bytes });
    }
    try emitter.writeAll("    default: return 64u;\n    }\n}\n");

    try emitter.writeAll("static size_t _cx_coro_frame_align(uint32_t _b_idx) {\n    switch (_b_idx) {\n");
    for (emitter.input.bodies, 0..) |*body_ptr, b_idx| {
        if (!body_ptr.is_async) continue;
        const sizing = try computeCoroFrameTotalAndAlignC(emitter, body_ptr, plan_mod.getBodyPlan(b_idx));
        try emitter.print("    case {d}u: return {d}u;\n", .{ b_idx, sizing.max_align });
    }
    try emitter.writeAll("    default: return 16u;\n    }\n}\n");

    try emitter.writeAll(
        "static uint32_t _cx_coro_poll_dispatch(uint32_t _b_idx, uint8_t *_frame, void *_out_ptr, uint32_t _action, uint8_t *_parked_out) {\n" ++
            "    switch (_b_idx) {\n",
    );
    for (emitter.input.bodies, 0..) |*body_ptr, b_idx| {
        if (!body_ptr.is_async) continue;
        try emitter.print(
            "    case {d}u: return _cx_coro_poll_{d}(_frame, _out_ptr, _action, _parked_out);\n",
            .{ b_idx, b_idx },
        );
    }
    try emitter.writeAll(
        "    default: (void)_frame; (void)_out_ptr; (void)_action; (void)_parked_out; return 1u;\n    }\n}\n",
    );

    try emitter.writeAll("static uint32_t _cx_coro_lookup_fn(const void *_fp) {\n");
    for (emitter.input.bodies, 0..) |*body_ptr, b_idx| {
        if (!body_ptr.is_async) continue;
        try emitter.print(
            "    if (_fp == (const void *)(uintptr_t){s}) return {d}u;\n",
            .{ emitter.body_c_names.items[b_idx], b_idx },
        );
    }
    for (emitter.closure_thunks.items) |thunk| {
        if (thunk.target_body_idx < emitter.input.bodies.len and
            emitter.input.bodies[thunk.target_body_idx].is_async)
        {
            try emitter.print(
                "    if (_fp == (const void *)(uintptr_t)_cx_cthunk_{d}) return {d}u;\n",
                .{ thunk.thunk_idx, thunk.target_body_idx },
            );
        }
    }
    try emitter.writeAll("    (void)_fp; return 0xFFFFFFFFu;\n}\n");
}

/// Emits a static closure thunk `_cx_cthunk_<idx>(uint8_t *_raw_env, …)` forwarding captures + args.
fn emitClosureThunkDefinition(emitter: *CModuleEmitter, thunk: ClosureThunkSpec) !void {
    const sig = emitter.input.pool.getFnSignatureView(thunk.closure_ty) orelse return;
    const target_body = &emitter.input.bodies[thunk.target_body_idx];
    const is_void_ret = try isZeroSizedType(emitter, sig.ret_ty);
    const ret_c = if (is_void_ret)
        try emitter.allocator.dupe(u8, "void")
    else
        try formatCType(emitter, sig.ret_ty);
    defer emitter.allocator.free(ret_c);

    try emitter.print("static {s} _cx_cthunk_{d}(uint8_t *_raw_env", .{ ret_c, thunk.thunk_idx });
    var param_i: usize = 0;
    while (param_i < sig.paramCount()) : (param_i += 1) {
        const p_ty = sig.getParamType(param_i);
        const p_mode = sig.getParamMode(param_i);
        if (p_mode == .inout_mode or p_mode == .set_mode) {
            if (try isZeroSizedType(emitter, p_ty)) {
                try emitter.print(", uint8_t *_p{d}", .{param_i});
            } else {
                const p_c = try formatCType(emitter, p_ty);
                defer emitter.allocator.free(p_c);
                try emitter.print(", {s} *_p{d}", .{ p_c, param_i });
            }
        } else if (!(try isZeroSizedType(emitter, p_ty))) {
            const p_c = try formatCType(emitter, p_ty);
            defer emitter.allocator.free(p_c);
            try emitter.print(", {s} _p{d}", .{ p_c, param_i });
        }
    }
    try emitter.writeAll(") {\n");
    if (thunk.capture_types.len > 0) {
        try emitter.print(
            "    _cx_cenv_{d} *_env = (_cx_cenv_{d} *)_raw_env;\n    (void)_env;\n",
            .{ thunk.thunk_idx, thunk.thunk_idx },
        );
    } else {
        try emitter.writeAll("    (void)_raw_env;\n");
    }

    try emitter.writeAll(if (is_void_ret) "    " else "    return ");
    if (emitter.input.is_dev_got_enabled) {
        try emitter.print("((_cx_body_fn_t_{d})_cx_dev_got[{d}u])(", .{
            thunk.target_body_idx,
            thunk.target_body_idx,
        });
    } else {
        try emitter.print("{s}(", .{emitter.body_c_names.items[thunk.target_body_idx]});
    }

    var call_emitted: usize = 0;
    var cap_i: usize = 0;
    while (cap_i < thunk.capture_types.len and cap_i < target_body.param_count) : (cap_i += 1) {
        const cap_decl = target_body.locals.items[1 + cap_i];
        const cap_ty = thunk.capture_types[cap_i];
        const cap_mode = cap_decl.mode();
        if (cap_mode == .inout_mode or cap_mode == .set_mode) {
            if (call_emitted > 0) try emitter.writeAll(", ");
            if (try isZeroSizedType(emitter, cap_ty)) {
                try emitter.writeAll("&_env->_guard");
            } else {
                try emitter.print("&_env->_c{d}", .{cap_i});
            }
            call_emitted += 1;
        } else if (!(try isZeroSizedType(emitter, cap_ty))) {
            if (call_emitted > 0) try emitter.writeAll(", ");
            try emitter.print("_env->_c{d}", .{cap_i});
            call_emitted += 1;
        }
    }

    var fwd_i: usize = 0;
    while (fwd_i < sig.paramCount()) : (fwd_i += 1) {
        const p_ty = sig.getParamType(fwd_i);
        const p_mode = sig.getParamMode(fwd_i);
        if (p_mode == .inout_mode or p_mode == .set_mode or !(try isZeroSizedType(emitter, p_ty))) {
            if (call_emitted > 0) try emitter.writeAll(", ");
            try emitter.print("_p{d}", .{fwd_i});
            call_emitted += 1;
        }
    }
    try emitter.writeAll(");\n}\n");
}

/// Emits `_cx_cdrop_<idx>` dropping reverse-order captured fields and freeing a Tier-2 closure environment.
fn emitClosureEnvDropDefinition(emitter: *CModuleEmitter, thunk: ClosureThunkSpec) !void {
    try emitter.print(
        "static void _cx_cdrop_{d}(uint8_t *_raw_env) {{\n" ++
            "    if (_raw_env == NULL) return;\n" ++
            "    _cx_cenv_{d} *_env = (_cx_cenv_{d} *)_raw_env;\n",
        .{ thunk.thunk_idx, thunk.thunk_idx, thunk.thunk_idx },
    );
    var rev_i: usize = thunk.capture_types.len;
    while (rev_i > 0) {
        rev_i -= 1;
        const cap_ty = emitter.input.pool.unwrapUnderlyingType(thunk.capture_types[rev_i]);
        if (emitter.drop_type_set.contains(cap_ty.toU32()) and !(try isZeroSizedType(emitter, cap_ty))) {
            try emitter.print("    _cx_drop_ty_{d}(&_env->_c{d});\n", .{ cap_ty.toU32(), rev_i });
        }
    }
    try emitter.writeAll("    free(_env);\n}\n");
}

/// Emits `_cx_drop_ty_<id>` executing outer `Drop.drop` followed by reverse-order member destructors.
fn emitDropHelperDefinition(emitter: *CModuleEmitter, drop_ty: TypeId) !void {
    const drop_c = try formatCType(emitter, drop_ty);
    defer emitter.allocator.free(drop_c);
    try emitter.print("static void _cx_drop_ty_{d}({s} *_self_ptr) {{\n", .{ drop_ty.toU32(), drop_c });
    try emitter.writeAll("    if (_self_ptr == NULL) return;\n");

    if (lookupDropBodyIndexForType(emitter, drop_ty)) |drop_body_idx| {
        const drop_body = &emitter.input.bodies[drop_body_idx];
        const p_decl = drop_body.locals.items[1];
        const p_mode = p_decl.mode();
        const p_unwrapped = emitter.input.pool.unwrapUnderlyingType(p_decl.type_id);
        const p_tag = emitter.input.pool.getNode(p_unwrapped).tag;
        const pass_by_ptr = p_mode == .inout_mode or p_mode == .set_mode or
            p_tag == .ref_ty or p_tag == .mut_ref_ty or p_tag == .raw_ptr_ty;
        if (emitter.input.is_dev_got_enabled) {
            try emitter.print("    ((_cx_body_fn_t_{d})_cx_dev_got[{d}u])({s});\n", .{
                drop_body_idx,
                drop_body_idx,
                if (pass_by_ptr) "_self_ptr" else "*_self_ptr",
            });
        } else {
            try emitter.print("    {s}({s});\n", .{
                emitter.body_c_names.items[drop_body_idx],
                if (pass_by_ptr) "_self_ptr" else "*_self_ptr",
            });
        }
    }

    const node = emitter.input.pool.getNode(drop_ty);
    switch (node.tag) {
        .struct_ty, .tuple_ty => {
            const lay = try emitter.resolver.resolveType(drop_ty);
            const is_packed = lay.reprFlags().is_packed;
            const fld_start = lay.aux_start;
            var rev_i: u32 = lay.aux_len;
            while (rev_i > 0) {
                rev_i -= 1;
                const fld_ty = emitter.input.pool.unwrapUnderlyingType(
                    emitter.resolver.fields_by_decl.items[fld_start + rev_i].field_ty,
                );
                if (emitter.drop_type_set.contains(fld_ty.toU32()) and !(try isZeroSizedType(emitter, fld_ty))) {
                    if (is_packed) {
                        const fld_c = try formatCType(emitter, fld_ty);
                        defer emitter.allocator.free(fld_c);
                        try emitter.print(
                            "    {{ {s} _df; memcpy(&_df, &_self_ptr->_f{d}, sizeof(_df)); " ++
                                "_cx_drop_ty_{d}(&_df); memcpy(&_self_ptr->_f{d}, &_df, sizeof(_df)); }}\n",
                            .{ fld_c, rev_i, fld_ty.toU32(), rev_i },
                        );
                    } else {
                        try emitter.print(
                            "    _cx_drop_ty_{d}(&_self_ptr->_f{d});\n",
                            .{ fld_ty.toU32(), rev_i },
                        );
                    }
                }
            }
        },
        .array_ty => {
            const elem_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const arr_len: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            if (arr_len > 0 and
                emitter.drop_type_set.contains(elem_ty.toU32()) and
                !(try isZeroSizedType(emitter, elem_ty)))
            {
                try emitter.print(
                    "    {{ size_t _di = {d}u; while (_di > 0u) {{ _di -= 1u; _cx_drop_ty_{d}(&_self_ptr->_elems[_di]); }} }}\n",
                    .{ arr_len, elem_ty.toU32() },
                );
            }
        },
        .optional_ty, .result_ty, .enum_ty => {
            if (try emitter.resolver.getSumDetail(drop_ty)) |sum_detail| {
                const discr_expr = try formatSumDiscrReadExpr(emitter, drop_ty, sum_detail, "(*_self_ptr)");
                defer emitter.allocator.free(discr_expr);
                const variant_count: u32 = switch (node.tag) {
                    .optional_ty, .result_ty => 2,
                    .enum_ty => countEnumVariants(emitter, drop_ty),
                    else => 0,
                };
                var var_ord: u32 = 0;
                while (var_ord < variant_count) : (var_ord += 1) {
                    const var_pay = resolveEnumVariantPayloadType(emitter, drop_ty, var_ord);
                    if (!emitter.drop_type_set.contains(var_pay.toU32()) or
                        (try isZeroSizedType(emitter, var_pay))) continue;
                    const pay_access = switch (sum_detail.repr) {
                        .transparent_ok, .niche_single => "_pay",
                        .explicit_tag => "",
                        .not_sum => continue,
                    };
                    if (sum_detail.repr == .explicit_tag) {
                        try emitter.print(
                            "    if ({s} == {d}u) {{ _cx_drop_ty_{d}(&_self_ptr->_u._v{d}); }}\n",
                            .{ discr_expr, var_ord, var_pay.toU32(), var_ord },
                        );
                    } else {
                        try emitter.print(
                            "    if ({s} == {d}u) {{ _cx_drop_ty_{d}(&_self_ptr->{s}); }}\n",
                            .{ discr_expr, var_ord, var_pay.toU32(), pay_access },
                        );
                    }
                }
            }
        },
        .closure_ty => {
            if (codegen_abi.isThreeWordClosureType(emitter.input.pool, drop_ty)) {
                try emitter.writeAll(
                    "    if (_self_ptr->drop_fn != NULL) { " ++
                        "_self_ptr->drop_fn(_self_ptr->env_ptr); " ++
                        "_self_ptr->drop_fn = NULL; _self_ptr->env_ptr = NULL; }\n",
                );
            }
        },
        .future_ty => {
            if (emitter.has_async_ops) {
                try emitter.writeAll("    _cx_async_fut_cancel((void *)_self_ptr);\n");
            }
        },
        else => {},
    }
    try emitter.writeAll("}\n");
}

/// Emits `_cx_eq_ty_<id>` performing UB-free, alignment-safe structural equality on `eq_ty`.
fn emitEqHelperDefinition(emitter: *CModuleEmitter, eq_ty: TypeId) !void {
    const eq_c = try formatCType(emitter, eq_ty);
    defer emitter.allocator.free(eq_c);
    try emitter.print(
        "static uint8_t _cx_eq_ty_{d}(const {s} *_lhs, const {s} *_rhs) {{\n    (void)_lhs; (void)_rhs;\n",
        .{ eq_ty.toU32(), eq_c, eq_c },
    );

    const node = emitter.input.pool.getNode(eq_ty);
    switch (node.tag) {
        .struct_ty, .tuple_ty => {
            const lay = try emitter.resolver.resolveType(eq_ty);
            const fld_start = lay.aux_start;
            const fld_len = lay.aux_len;
            var fld_i: u32 = 0;
            while (fld_i < fld_len) : (fld_i += 1) {
                const fld = emitter.resolver.fields_by_decl.items[fld_start + fld_i];
                if (fld.size_bytes == 0) continue;
                const fld_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                const fld_c = try formatCType(emitter, fld_ty);
                defer emitter.allocator.free(fld_c);
                const eq_e = try formatAlignedVarEqExprC(emitter, fld_ty, "_fl", "_fr");
                defer emitter.allocator.free(eq_e);
                try emitter.print(
                    "    {{ {s} _fl, _fr; memcpy(&_fl, &_lhs->_f{d}, sizeof(_fl)); " ++
                        "memcpy(&_fr, &_rhs->_f{d}, sizeof(_fr)); if (!({s})) return 0u; }}\n",
                    .{ fld_c, fld_i, fld_i, eq_e },
                );
            }
            try emitter.writeAll("    return 1u;\n");
        },
        .array_ty => {
            const elem_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const arr_len: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            if (arr_len > 0 and !(try isZeroSizedType(emitter, elem_ty))) {
                const elem_c = try formatCType(emitter, elem_ty);
                defer emitter.allocator.free(elem_c);
                const eq_e = try formatAlignedVarEqExprC(emitter, elem_ty, "_el", "_er");
                defer emitter.allocator.free(eq_e);
                try emitter.print(
                    "    {{ size_t _ei = 0u; while (_ei < {d}u) {{ {s} _el = _lhs->_elems[_ei], _er = _rhs->_elems[_ei]; " ++
                        "if (!({s})) return 0u; _ei += 1u; }} }}\n",
                    .{ arr_len, elem_c, eq_e },
                );
            }
            try emitter.writeAll("    return 1u;\n");
        },
        .slice_ty => {
            const elem_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            try emitter.writeAll("    if (_lhs->len != _rhs->len) return 0u;\n");
            if (!(try isZeroSizedType(emitter, elem_ty))) {
                const elem_c = try formatCType(emitter, elem_ty);
                defer emitter.allocator.free(elem_c);
                const eq_e = try formatAlignedVarEqExprC(emitter, elem_ty, "_el", "_er");
                defer emitter.allocator.free(eq_e);
                try emitter.print(
                    "    {{ size_t _ei = 0u; while (_ei < (size_t)_lhs->len) {{ " ++
                        "{s} _el = _lhs->ptr[_ei], _er = _rhs->ptr[_ei]; if (!({s})) return 0u; _ei += 1u; }} }}\n",
                    .{ elem_c, eq_e },
                );
            }
            try emitter.writeAll("    return 1u;\n");
        },
        .soa_array_ty => {
            const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const cap: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            if (cap > 0) {
                const lay = try emitter.resolver.resolveType(elem_struct);
                const fld_start = lay.aux_start;
                const fld_len = lay.aux_len;
                var fld_i: u32 = 0;
                while (fld_i < fld_len) : (fld_i += 1) {
                    const fld = emitter.resolver.fields_by_decl.items[fld_start + fld_i];
                    if (fld.size_bytes == 0) continue;
                    const fld_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                    const col = emitter.resolver.getSoaColumnOffset(elem_struct, fld_i, cap).?;
                    const fld_c = try formatCType(emitter, fld_ty);
                    defer emitter.allocator.free(fld_c);
                    const eq_e = try formatAlignedVarEqExprC(emitter, fld_ty, "_cl", "_cr");
                    defer emitter.allocator.free(eq_e);
                    try emitter.print(
                        "    {{ size_t _ei = 0u; while (_ei < {d}u) {{ {s} _cl, _cr; " ++
                            "memcpy(&_cl, &_lhs->_bytes[{d}u] + _ei * sizeof(_cl), sizeof(_cl)); " ++
                            "memcpy(&_cr, &_rhs->_bytes[{d}u] + _ei * sizeof(_cr), sizeof(_cr)); " ++
                            "if (!({s})) return 0u; _ei += 1u; }} }}\n",
                        .{ cap, fld_c, col.byte_offset, col.byte_offset, eq_e },
                    );
                }
            }
            try emitter.writeAll("    return 1u;\n");
        },
        .soa_slice_ty => {
            const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const lay = try emitter.resolver.resolveType(elem_struct);
            const fld_start = lay.aux_start;
            const fld_len = lay.aux_len;
            try emitter.writeAll("    if (_lhs->len != _rhs->len) return 0u;\n");
            try emitter.writeAll("    if (_lhs->len == 0u) return 1u;\n");
            var fld_i: u32 = 0;
            while (fld_i < fld_len) : (fld_i += 1) {
                const fld = emitter.resolver.fields_by_decl.items[fld_start + fld_i];
                if (fld.size_bytes == 0) continue;
                const fld_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                const off_e = try formatDynamicSoaColOffsetExpr(emitter, elem_struct, fld_i, "_lhs->len");
                defer emitter.allocator.free(off_e);
                const fld_c = try formatCType(emitter, fld_ty);
                defer emitter.allocator.free(fld_c);
                const eq_e = try formatAlignedVarEqExprC(emitter, fld_ty, "_cl", "_cr");
                defer emitter.allocator.free(eq_e);
                try emitter.print(
                    "    {{ size_t _off = {s}; size_t _ei = 0u; while (_ei < (size_t)_lhs->len) {{ {s} _cl, _cr; " ++
                        "memcpy(&_cl, _lhs->ptr + _off + _ei * sizeof(_cl), sizeof(_cl)); " ++
                        "memcpy(&_cr, _rhs->ptr + _off + _ei * sizeof(_cr), sizeof(_cr)); " ++
                        "if (!({s})) return 0u; _ei += 1u; }} }}\n",
                    .{ off_e, fld_c, eq_e },
                );
            }
            try emitter.writeAll("    return 1u;\n");
        },
        .optional_ty, .result_ty, .enum_ty => {
            if (try emitter.resolver.getSumDetail(eq_ty)) |sum_detail| {
                const disc_l = try formatSumDiscrReadExpr(emitter, eq_ty, sum_detail, "(*_lhs)");
                defer emitter.allocator.free(disc_l);
                const disc_r = try formatSumDiscrReadExpr(emitter, eq_ty, sum_detail, "(*_rhs)");
                defer emitter.allocator.free(disc_r);
                try emitter.print(
                    "    uint64_t _dl = {s};\n    uint64_t _dr = {s};\n    if (_dl != _dr) return 0u;\n",
                    .{ disc_l, disc_r },
                );
                const var_count: u32 = switch (node.tag) {
                    .optional_ty, .result_ty => 2,
                    .enum_ty => countEnumVariants(emitter, eq_ty),
                    else => 0,
                };
                var var_ord: u32 = 0;
                while (var_ord < var_count) : (var_ord += 1) {
                    const v_pay = resolveEnumVariantPayloadType(emitter, eq_ty, var_ord);
                    if (try isZeroSizedType(emitter, v_pay)) continue;
                    const pay_c = try formatCType(emitter, v_pay);
                    defer emitter.allocator.free(pay_c);
                    const eq_e = try formatAlignedVarEqExprC(emitter, v_pay, "_pl", "_pr");
                    defer emitter.allocator.free(eq_e);
                    try emitter.print(
                        "    if (_dl == {d}u) {{ {s} _pl, _pr; " ++
                            "memcpy(&_pl, ((const uint8_t *)_lhs) + {d}u, sizeof(_pl)); " ++
                            "memcpy(&_pr, ((const uint8_t *)_rhs) + {d}u, sizeof(_pr)); " ++
                            "return {s}; }}\n",
                        .{ var_ord, pay_c, sum_detail.payload_offset, sum_detail.payload_offset, eq_e },
                    );
                }
                try emitter.writeAll("    return 1u;\n");
            } else {
                try emitter.writeAll("    return 0u;\n");
            }
        },
        else => try emitter.writeAll("    return 0u;\n"),
    }
    try emitter.writeAll("}\n");
}

/// Resolves the declared identifier text of field `decl_ord` on nominal `.struct_ty` `struct_ty`.
fn resolveStructFieldName(emitter: *const CModuleEmitter, struct_ty: TypeId, decl_ord: u32) []const u8 {
    const sym_idx = SymbolIndex.fromInt(emitter.input.pool.getNode(struct_ty).rhs);
    if (sym_idx.isNone() or sym_idx.asInt() >= emitter.input.sym_table.symbols.items.len) return "_";
    const struct_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
    if (struct_sym.target_scope.isNone()) return "_";
    var cur_ord: u32 = 0;
    for (emitter.input.sym_table.getScopeMembers(struct_sym.target_scope)) |mem_idx| {
        const mem_sym = emitter.input.sym_table.getSymbol(mem_idx).*;
        if (mem_sym.kind != .field_sym) continue;
        if (cur_ord == decl_ord) return mem_sym.name_text;
        cur_ord += 1;
    }
    return "_";
}

/// Resolves the declared identifier text of variant `var_ord` on `.enum_ty` `enum_ty`.
fn resolveEnumVariantName(emitter: *const CModuleEmitter, enum_ty: TypeId, var_ord: u32) []const u8 {
    const sym_idx = SymbolIndex.fromInt(emitter.input.pool.getNode(enum_ty).rhs);
    if (sym_idx.isNone() or sym_idx.asInt() >= emitter.input.sym_table.symbols.items.len) return "";
    const enum_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
    if (enum_sym.target_scope.isNone()) return "";
    var cur_ord: u32 = 0;
    for (emitter.input.sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
        const mem_sym = emitter.input.sym_table.getSymbol(mem_idx).*;
        if (mem_sym.kind != .enum_variant_sym) continue;
        if (cur_ord == var_ord) return mem_sym.name_text;
        cur_ord += 1;
    }
    return "";
}

/// Emits a C99 string literal call `_cx_rt_buf_push_bytes(buf_var, "…", len)` with safe escaping.
fn emitBufPushStringLiteralC(emitter: *CModuleEmitter, buf_var: []const u8, text: []const u8) !void {
    if (text.len == 0) return;
    try emitter.print("    _cx_rt_buf_push_bytes({s}, (const uint8_t *)\"", .{buf_var});
    try appendEscapedCStringContents(emitter, text);
    try emitter.print("\", {d}u);\n", .{text.len});
}

/// Emits monomorphic `_cx_fmt_fn_ty_<id>` formatting `fmt_ty` with `FmtSpec` parity across engines (`SE-12`).
fn emitFmtHelperDefinition(emitter: *CModuleEmitter, fmt_ty: TypeId) !void {
    try emitter.print(
        "static void _cx_fmt_fn_ty_{d}(_cx_rt_buf_t *_out_b, const void *_val_p, uint32_t _spec_lo, uint32_t _spec_hi) {{\n" ++
            "    (void)_out_b; (void)_val_p; (void)_spec_lo; (void)_spec_hi;\n",
        .{fmt_ty.toU32()},
    );

    if (fmt_ty == .unit_ty) {
        try emitter.writeAll(
            "    _cx_rt_buf_pad_str(_out_b, (const uint8_t *)\"()\", 2u, _spec_lo, _spec_hi, 0u);\n}\n",
        );
        return;
    }
    if (fmt_ty == .bool_ty) {
        try emitter.writeAll(
            "    _cx_rt_fmt_bool_spec(_out_b, *(const uint8_t *)_val_p, _spec_lo, _spec_hi);\n}\n",
        );
        return;
    }
    if (fmt_ty == .char_ty) {
        try emitter.writeAll(
            "    uint32_t _cp = 0u; memcpy(&_cp, _val_p, sizeof(_cp));\n" ++
                "    _cx_rt_fmt_char_spec(_out_b, _cp, _spec_lo, _spec_hi);\n}\n",
        );
        return;
    }
    if (fmt_ty == .str_ty) {
        try emitter.writeAll(
            "    cx_str_t _sv; memcpy(&_sv, _val_p, sizeof(_sv));\n" ++
                "    _cx_rt_fmt_str_spec(_out_b, _sv, _spec_lo, _spec_hi);\n}\n",
        );
        return;
    }
    if (fmt_ty == .f32_ty) {
        try emitter.writeAll(
            "    float _fv = 0.0f; memcpy(&_fv, _val_p, sizeof(_fv));\n" ++
                "    _cx_rt_fmt_f64_spec(_out_b, (double)_fv, _spec_lo, _spec_hi);\n}\n",
        );
        return;
    }
    if (fmt_ty == .f64_ty or fmt_ty == .untyped_float_ty) {
        try emitter.writeAll(
            "    double _fv = 0.0; memcpy(&_fv, _val_p, sizeof(_fv));\n" ++
                "    _cx_rt_fmt_f64_spec(_out_b, _fv, _spec_lo, _spec_hi);\n}\n",
        );
        return;
    }
    if (fmt_ty == .source_loc_ty) {
        try emitter.writeAll(
            "    cx_source_loc_t _sl = NULL; memcpy(&_sl, _val_p, sizeof(_sl));\n" ++
                "    _cx_rt_fmt_source_loc_spec(_out_b, _sl, _spec_lo, _spec_hi);\n}\n",
        );
        return;
    }
    if (fmt_ty == .fmt_args_ty) {
        try emitter.writeAll(
            "    cx_fmt_args_t _fa; memcpy(&_fa, _val_p, sizeof(_fa));\n" ++
                "    _cx_rt_fmt_args_spec(_out_b, &_fa, _spec_lo, _spec_hi);\n}\n",
        );
        return;
    }
    if (fmt_ty == .fmt_spec_ty) {
        try emitter.writeAll(
            "    _cx_rt_buf_pad_str(_out_b, (const uint8_t *)\"FmtSpec\", 7u, _spec_lo, _spec_hi, 0u);\n}\n",
        );
        return;
    }
    if (fmt_ty == .task_group_base_ty or
        fmt_ty == .task_handle_base_ty or
        emitter.input.pool.isTaskGroupType(fmt_ty) or
        emitter.input.pool.isTaskHandleType(fmt_ty))
    {
        try emitter.writeAll(
            "    uintptr_t _pv = 0u; memcpy(&_pv, _val_p, sizeof(_pv));\n" ++
                "    _cx_rt_fmt_ptr_spec(_out_b, _pv, _spec_lo, _spec_hi);\n}\n",
        );
        return;
    }

    // Fieldless / backed `enum` prints variant name under Display/Debug, or backing integer under radix verbs:
    if (!fmt_ty.isPrimitiveOrSentinel() and
        emitter.input.pool.getNode(fmt_ty).tag == .enum_ty and
        (try emitter.resolver.getSumDetail(fmt_ty)) == null)
    {
        if (try isZeroSizedType(emitter, fmt_ty)) {
            const v0_name = resolveEnumVariantName(emitter, fmt_ty, 0);
            try emitter.writeAll("    _cx_rt_buf_pad_str(_out_b, (const uint8_t *)\"");
            try appendEscapedCStringContents(emitter, v0_name);
            try emitter.print("\", {d}u, _spec_lo, _spec_hi, 0u);\n}}\n", .{v0_name.len});
            return;
        }
        if (try resolveIntegerInfo(emitter, fmt_ty)) |enum_int| {
            const val_c = try formatCType(emitter, fmt_ty);
            defer emitter.allocator.free(val_c);
            try emitter.print(
                "    {s} _ev; memcpy(&_ev, _val_p, sizeof(_ev));\n" ++
                    "    uint32_t _evb = _cx_rt_eff_verb(_spec_lo);\n" ++
                    "    if (_evb <= 1u) {{\n",
                .{val_c},
            );
            const var_count = countEnumVariants(emitter, fmt_ty);
            var var_ord: u32 = 0;
            while (var_ord < var_count) : (var_ord += 1) {
                const disc_val = emitter.input.pool.getEnumVariantDiscriminant(fmt_ty, var_ord) orelse
                    @as(i128, var_ord);
                const disc_bits: u128 = @bitCast(disc_val);
                const var_name = resolveEnumVariantName(emitter, fmt_ty, var_ord);
                if (enum_int.bits == 128) {
                    try emitter.print(
                        "        if (_cx_u128_eq(_cx_as_u128(_ev), _cx_u128_make({d}ull, {d}ull))) {{\n",
                        .{ @as(u64, @truncate(disc_bits)), @as(u64, @truncate(disc_bits >> 64)) },
                    );
                } else {
                    const mask: u64 = if (enum_int.bits >= 64)
                        std.math.maxInt(u64)
                    else
                        (@as(u64, 1) << @intCast(enum_int.bits)) - 1;
                    const u_c = resolveUnsignedCTypeForBits(enum_int.bits);
                    try emitter.print(
                        "        if ((({s})_ev) == ({s})({d}ull)) {{\n",
                        .{ u_c, u_c, @as(u64, @truncate(disc_bits)) & mask },
                    );
                }
                try emitter.writeAll("            _cx_rt_buf_pad_str(_out_b, (const uint8_t *)\"");
                try appendEscapedCStringContents(emitter, var_name);
                try emitter.print("\", {d}u, _spec_lo, _spec_hi, 0u);\n            return;\n        }}\n", .{
                    var_name.len,
                });
            }
            try emitter.writeAll("    }\n");
        }
    }

    if (try resolveIntegerInfo(emitter, fmt_ty)) |int_info| {
        const val_c = try formatCType(emitter, fmt_ty);
        defer emitter.allocator.free(val_c);
        try emitter.print("    {s} _iv; memcpy(&_iv, _val_p, sizeof(_iv));\n", .{val_c});
        if (int_info.bits == 128) {
            if (int_info.is_signed) {
                try emitter.writeAll("    _cx_rt_fmt_i128_spec(_out_b, _iv, _spec_lo, _spec_hi);\n}\n");
            } else {
                try emitter.writeAll("    _cx_rt_fmt_u128_spec(_out_b, _iv, 0u, _spec_lo, _spec_hi);\n}\n");
            }
        } else {
            const mask: u64 = if (int_info.bits >= 64)
                std.math.maxInt(u64)
            else
                (@as(u64, 1) << @intCast(int_info.bits)) - 1;
            const u_c = resolveUnsignedCTypeForBits(int_info.bits);
            if (int_info.is_signed) {
                const s_c = resolveSignedCTypeForBits(int_info.bits);
                try emitter.print(
                    "    uint32_t _vc = (_spec_lo >> 27) & 0xFu;\n" ++
                        "    if (_vc >= 2u && _vc <= 5u) {{\n" ++
                        "        _cx_rt_fmt_u128_spec(_out_b, _cx_u128_make(((uint64_t)(({s})_iv)) & {d}ull, 0ull), 0u, _spec_lo, _spec_hi);\n" ++
                        "    }} else {{\n" ++
                        "        int64_t _sx = (int64_t)(({s})_iv);\n" ++
                        "        uint64_t _s_hi = _sx < 0 ? 0xFFFFFFFFFFFFFFFFull : 0ull;\n" ++
                        "        _cx_rt_fmt_i128_spec(_out_b, _cx_i128_make((uint64_t)_sx, _s_hi), _spec_lo, _spec_hi);\n" ++
                        "    }}\n}}\n",
                    .{ u_c, mask, s_c },
                );
            } else {
                try emitter.print(
                    "    _cx_rt_fmt_u128_spec(_out_b, _cx_u128_make(((uint64_t)(({s})_iv)) & {d}ull, 0ull), 0u, _spec_lo, _spec_hi);\n}}\n",
                    .{ u_c, mask },
                );
            }
        }
        return;
    }

    if (fmt_ty.isPrimitiveOrSentinel()) {
        try emitter.writeAll("}\n");
        return;
    }

    const node = emitter.input.pool.getNode(fmt_ty);
    switch (node.tag) {
        .ref_ty, .mut_ref_ty => {
            const pointee_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            try emitter.print(
                "    const void *_rp = NULL; memcpy(&_rp, _val_p, sizeof(_rp));\n" ++
                    "    if (((_spec_lo >> 27) & 0xFu) == 9u) {{\n" ++
                    "        _cx_rt_fmt_ptr_spec(_out_b, (uintptr_t)_rp, _spec_lo, _spec_hi);\n" ++
                    "    }} else {{\n" ++
                    "        _cx_fmt_fn_ty_{d}(_out_b, _rp, _spec_lo, _spec_hi);\n" ++
                    "    }}\n}}\n",
                .{pointee_ty.toU32()},
            );
        },
        .raw_ptr_ty, .fn_ty => {
            try emitter.writeAll(
                "    uintptr_t _pv = 0u; memcpy(&_pv, _val_p, sizeof(_pv));\n" ++
                    "    _cx_rt_fmt_ptr_spec(_out_b, _pv, _spec_lo, _spec_hi);\n}\n",
            );
        },
        .struct_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            const st_name = if (!sym_idx.isNone() and sym_idx.asInt() < emitter.input.sym_table.symbols.items.len)
                emitter.input.sym_table.getSymbol(sym_idx).name_text
            else
                "struct";
            const lay = try emitter.resolver.resolveType(fmt_ty);
            try emitter.writeAll(
                "    _cx_rt_buf_t _cb = { NULL, 0u, 0u };\n" ++
                    "    uint32_t _fspec = (_cx_rt_eff_verb(_spec_lo) == 1u) ? (1u << 27) : 0u;\n" ++
                    "    (void)_fspec;\n",
            );
            try emitBufPushStringLiteralC(emitter, "&_cb", st_name);
            try emitBufPushStringLiteralC(emitter, "&_cb", " { ");
            var fld_i: u32 = 0;
            while (fld_i < lay.aux_len) : (fld_i += 1) {
                if (fld_i > 0) try emitBufPushStringLiteralC(emitter, "&_cb", ", ");
                const fld = emitter.resolver.fields_by_decl.items[lay.aux_start + fld_i];
                const fld_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                try emitBufPushStringLiteralC(emitter, "&_cb", resolveStructFieldName(emitter, fmt_ty, fld_i));
                try emitBufPushStringLiteralC(emitter, "&_cb", ": ");
                try emitter.print(
                    "    _cx_fmt_fn_ty_{d}(&_cb, ((const uint8_t *)_val_p) + {d}u, _fspec, 0xFFFFFFFFu);\n",
                    .{ fld_ty.toU32(), fld.byte_offset },
                );
            }
            try emitBufPushStringLiteralC(emitter, "&_cb", " }");
            try emitter.writeAll(
                "    _cx_rt_buf_pad_str(_out_b, _cb.data, _cb.len, _spec_lo, _spec_hi, 0u);\n" ++
                    "    free(_cb.data);\n}\n",
            );
        },
        .tuple_ty => {
            const lay = try emitter.resolver.resolveType(fmt_ty);
            try emitter.writeAll(
                "    _cx_rt_buf_t _cb = { NULL, 0u, 0u };\n" ++
                    "    uint32_t _fspec = (_cx_rt_eff_verb(_spec_lo) == 1u) ? (1u << 27) : 0u;\n" ++
                    "    (void)_fspec;\n" ++
                    "    _cx_rt_buf_push_byte(&_cb, '(');\n",
            );
            var fld_i: u32 = 0;
            while (fld_i < lay.aux_len) : (fld_i += 1) {
                if (fld_i > 0) try emitBufPushStringLiteralC(emitter, "&_cb", ", ");
                const fld = emitter.resolver.fields_by_decl.items[lay.aux_start + fld_i];
                const fld_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                try emitter.print(
                    "    _cx_fmt_fn_ty_{d}(&_cb, ((const uint8_t *)_val_p) + {d}u, _fspec, 0xFFFFFFFFu);\n",
                    .{ fld_ty.toU32(), fld.byte_offset },
                );
            }
            if (lay.aux_len == 1) try emitter.writeAll("    _cx_rt_buf_push_byte(&_cb, ',');\n");
            try emitter.writeAll(
                "    _cx_rt_buf_push_byte(&_cb, ')');\n" ++
                    "    _cx_rt_buf_pad_str(_out_b, _cb.data, _cb.len, _spec_lo, _spec_hi, 0u);\n" ++
                    "    free(_cb.data);\n}\n",
            );
        },
        .array_ty => {
            const elem_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const elem_lay = try emitter.resolver.resolveType(elem_ty);
            const arr_len: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            try emitter.writeAll(
                "    _cx_rt_buf_t _cb = { NULL, 0u, 0u };\n" ++
                    "    uint32_t _fspec = (_cx_rt_eff_verb(_spec_lo) == 1u) ? (1u << 27) : 0u;\n" ++
                    "    (void)_fspec;\n" ++
                    "    _cx_rt_buf_push_byte(&_cb, '[');\n",
            );
            if (arr_len > 0) {
                try emitter.print(
                    "    {{ size_t _ai = 0u; while (_ai < {d}u) {{ " ++
                        "if (_ai > 0u) _cx_rt_buf_push_bytes(&_cb, (const uint8_t *)\", \", 2u); " ++
                        "_cx_fmt_fn_ty_{d}(&_cb, ((const uint8_t *)_val_p) + _ai * {d}u, _fspec, 0xFFFFFFFFu); " ++
                        "_ai += 1u; }} }}\n",
                    .{ arr_len, elem_ty.toU32(), elem_lay.stride_bytes },
                );
            }
            try emitter.writeAll(
                "    _cx_rt_buf_push_byte(&_cb, ']');\n" ++
                    "    _cx_rt_buf_pad_str(_out_b, _cb.data, _cb.len, _spec_lo, _spec_hi, 0u);\n" ++
                    "    free(_cb.data);\n}\n",
            );
        },
        .slice_ty => {
            const elem_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const elem_lay = try emitter.resolver.resolveType(elem_ty);
            const fmt_c = try formatCType(emitter, fmt_ty);
            defer emitter.allocator.free(fmt_c);
            try emitter.print(
                "    {s} _slv; memcpy(&_slv, _val_p, sizeof(_slv));\n" ++
                    "    _cx_rt_buf_t _cb = {{ NULL, 0u, 0u }};\n" ++
                    "    uint32_t _fspec = (_cx_rt_eff_verb(_spec_lo) == 1u) ? (1u << 27) : 0u;\n" ++
                    "    _cx_rt_buf_push_byte(&_cb, '[');\n" ++
                    "    {{ size_t _ai = 0u; while (_ai < (size_t)_slv.len) {{ " ++
                    "if (_ai > 0u) _cx_rt_buf_push_bytes(&_cb, (const uint8_t *)\", \", 2u); " ++
                    "_cx_fmt_fn_ty_{d}(&_cb, ((const uint8_t *)_slv.ptr) + _ai * {d}u, _fspec, 0xFFFFFFFFu); " ++
                    "_ai += 1u; }} }}\n" ++
                    "    _cx_rt_buf_push_byte(&_cb, ']');\n" ++
                    "    _cx_rt_buf_pad_str(_out_b, _cb.data, _cb.len, _spec_lo, _spec_hi, 0u);\n" ++
                    "    free(_cb.data);\n}}\n",
                .{ fmt_c, elem_ty.toU32(), elem_lay.stride_bytes },
            );
        },
        .optional_ty => {
            const some_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const sum_detail = (try emitter.resolver.getSumDetail(fmt_ty)) orelse {
                try emitter.writeAll("}\n");
                return;
            };
            const fmt_c = try formatCType(emitter, fmt_ty);
            defer emitter.allocator.free(fmt_c);
            const discr_expr = try formatSumDiscrReadExpr(emitter, fmt_ty, sum_detail, "_sv");
            defer emitter.allocator.free(discr_expr);
            try emitter.print(
                "    {s} _sv; memcpy(&_sv, _val_p, sizeof(_sv));\n" ++
                    "    uint64_t _dv = {s};\n" ++
                    "    _cx_rt_buf_t _cb = {{ NULL, 0u, 0u }};\n" ++
                    "    if (_dv == 0u) {{\n" ++
                    "        _cx_rt_buf_push_bytes(&_cb, (const uint8_t *)\"None\", 4u);\n" ++
                    "    }} else {{\n" ++
                    "        _cx_rt_buf_push_bytes(&_cb, (const uint8_t *)\"Some(\", 5u);\n" ++
                    "        _cx_fmt_fn_ty_{d}(&_cb, ((const uint8_t *)&_sv) + {d}u, 1u << 27, 0xFFFFFFFFu);\n" ++
                    "        _cx_rt_buf_push_byte(&_cb, ')');\n" ++
                    "    }}\n" ++
                    "    _cx_rt_buf_pad_str(_out_b, _cb.data, _cb.len, _spec_lo, _spec_hi, 0u);\n" ++
                    "    free(_cb.data);\n}}\n",
                .{ fmt_c, discr_expr, some_ty.toU32(), sum_detail.payload_offset },
            );
        },
        .result_ty => {
            const ok_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const err_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.rhs));
            const sum_detail = (try emitter.resolver.getSumDetail(fmt_ty)) orelse {
                try emitter.writeAll("}\n");
                return;
            };
            if (try isZeroSizedType(emitter, fmt_ty)) {
                try emitter.writeAll(
                    "    _cx_rt_buf_pad_str(_out_b, (const uint8_t *)\"Ok(())\", 6u, _spec_lo, _spec_hi, 0u);\n}\n",
                );
                return;
            }
            const fmt_c = try formatCType(emitter, fmt_ty);
            defer emitter.allocator.free(fmt_c);
            const discr_expr = try formatSumDiscrReadExpr(emitter, fmt_ty, sum_detail, "_sv");
            defer emitter.allocator.free(discr_expr);
            try emitter.print(
                "    {s} _sv; memcpy(&_sv, _val_p, sizeof(_sv));\n" ++
                    "    uint64_t _dv = {s};\n" ++
                    "    _cx_rt_buf_t _cb = {{ NULL, 0u, 0u }};\n" ++
                    "    if (_dv == 0u) {{\n" ++
                    "        _cx_rt_buf_push_bytes(&_cb, (const uint8_t *)\"Ok(\", 3u);\n" ++
                    "        _cx_fmt_fn_ty_{d}(&_cb, ((const uint8_t *)&_sv) + {d}u, 1u << 27, 0xFFFFFFFFu);\n" ++
                    "        _cx_rt_buf_push_byte(&_cb, ')');\n" ++
                    "    }} else {{\n" ++
                    "        _cx_rt_buf_push_bytes(&_cb, (const uint8_t *)\"Err(\", 4u);\n" ++
                    "        _cx_fmt_fn_ty_{d}(&_cb, ((const uint8_t *)&_sv) + {d}u, 1u << 27, 0xFFFFFFFFu);\n" ++
                    "        _cx_rt_buf_push_byte(&_cb, ')');\n" ++
                    "    }}\n" ++
                    "    _cx_rt_buf_pad_str(_out_b, _cb.data, _cb.len, _spec_lo, _spec_hi, 0u);\n" ++
                    "    free(_cb.data);\n}}\n",
                .{
                    fmt_c,
                    discr_expr,
                    ok_ty.toU32(),
                    sum_detail.payload_offset,
                    err_ty.toU32(),
                    sum_detail.payload_offset,
                },
            );
        },
        .enum_ty => {
            if (try isZeroSizedType(emitter, fmt_ty)) {
                const v0_name = resolveEnumVariantName(emitter, fmt_ty, 0);
                try emitter.writeAll("    _cx_rt_buf_pad_str(_out_b, (const uint8_t *)\"");
                try appendEscapedCStringContents(emitter, v0_name);
                try emitter.print("\", {d}u, _spec_lo, _spec_hi, 0u);\n}}\n", .{v0_name.len});
                return;
            }
            const sum_detail = (try emitter.resolver.getSumDetail(fmt_ty)) orelse {
                try emitter.writeAll("}\n");
                return;
            };
            const fmt_c = try formatCType(emitter, fmt_ty);
            defer emitter.allocator.free(fmt_c);
            const discr_expr = try formatSumDiscrReadExpr(emitter, fmt_ty, sum_detail, "_sv");
            defer emitter.allocator.free(discr_expr);
            try emitter.print(
                "    {s} _sv; memcpy(&_sv, _val_p, sizeof(_sv));\n" ++
                    "    uint64_t _dv = {s};\n" ++
                    "    _cx_rt_buf_t _cb = {{ NULL, 0u, 0u }};\n",
                .{ fmt_c, discr_expr },
            );
            const var_count = countEnumVariants(emitter, fmt_ty);
            var var_ord: u32 = 0;
            while (var_ord < var_count) : (var_ord += 1) {
                const kw = if (var_ord == 0) "    if" else "    else if";
                try emitter.print("{s} (_dv == {d}u) {{\n", .{ kw, var_ord });
                try emitBufPushStringLiteralC(emitter, "&_cb", resolveEnumVariantName(emitter, fmt_ty, var_ord));
                const var_pay = resolveEnumVariantPayloadType(emitter, fmt_ty, var_ord);
                if (var_pay != .unit_ty and !var_pay.isError()) {
                    try emitter.writeAll("        _cx_rt_buf_push_byte(&_cb, '(');\n");
                    if (!var_pay.isPrimitiveOrSentinel() and emitter.input.pool.getNode(var_pay).tag == .tuple_ty) {
                        const tup_lay = try emitter.resolver.resolveType(var_pay);
                        var tf_i: u32 = 0;
                        while (tf_i < tup_lay.aux_len) : (tf_i += 1) {
                            if (tf_i > 0) try emitBufPushStringLiteralC(emitter, "&_cb", ", ");
                            const tf = emitter.resolver.fields_by_decl.items[tup_lay.aux_start + tf_i];
                            const tf_ty = emitter.input.pool.unwrapUnderlyingType(tf.field_ty);
                            try emitter.print(
                                "        _cx_fmt_fn_ty_{d}(&_cb, ((const uint8_t *)&_sv) + {d}u, 1u << 27, 0xFFFFFFFFu);\n",
                                .{ tf_ty.toU32(), sum_detail.payload_offset + tf.byte_offset },
                            );
                        }
                    } else {
                        try emitter.print(
                            "        _cx_fmt_fn_ty_{d}(&_cb, ((const uint8_t *)&_sv) + {d}u, 1u << 27, 0xFFFFFFFFu);\n",
                            .{ var_pay.toU32(), sum_detail.payload_offset },
                        );
                    }
                    try emitter.writeAll("        _cx_rt_buf_push_byte(&_cb, ')');\n");
                }
                try emitter.writeAll("    }\n");
            }
            try emitter.writeAll(
                "    _cx_rt_buf_pad_str(_out_b, _cb.data, _cb.len, _spec_lo, _spec_hi, 0u);\n" ++
                    "    free(_cb.data);\n}\n",
            );
        },
        else => {
            var name_buf: [256]u8 = undefined;
            const rendered = emitter.input.pool.formatType(fmt_ty, emitter.input.sym_table, &name_buf);
            try emitter.writeAll("    _cx_rt_buf_pad_str(_out_b, (const uint8_t *)\"");
            try appendEscapedCStringContents(emitter, rendered);
            try emitter.print("\", {d}u, _spec_lo, _spec_hi, 0u);\n}}\n", .{rendered.len});
        },
    }
}

// --------------- MirPlace & Expression Lowering ---------------

/// Resolves the final projected `TypeId` of `place_id` in `body` without emitting C code.
fn resolvePlaceResultType(emitter: *CModuleEmitter, body: *const MirBody, place_id: PlaceId) TypeId {
    if (place_id.isNone() or place_id.asInt() >= body.places.items.len) return .unit_ty;
    const place = body.places.items[place_id.asInt()];
    if (place.base >= body.locals.items.len) return .unit_ty;
    var cur_ty = emitter.input.pool.unwrapUnderlyingType(body.locals.items[place.base].type_id);
    var active_downcast: ?u32 = null;
    var soa_col_field_ty: ?TypeId = null;

    for (body.getPlaceProjections(place_id)) |proj| {
        if (soa_col_field_ty) |col_ty| {
            soa_col_field_ty = null;
            if (proj.kind == .index) {
                cur_ty = col_ty;
                continue;
            } else if (proj.kind == .slice_len) {
                return .usize_ty;
            }
        }
        const node = emitter.input.pool.getNode(cur_ty);
        switch (proj.kind) {
            .deref => {
                active_downcast = null;
                cur_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            },
            .downcast => {
                active_downcast = proj.payload;
            },
            .field => {
                if (active_downcast) |tag_ord| {
                    active_downcast = null;
                    cur_ty = resolveEnumVariantPayloadType(emitter, cur_ty, tag_ord);
                    if (proj.payload > 0) {
                        if (emitter.resolver.getFieldByDeclOrdinal(cur_ty, proj.payload) catch null) |sub_fld| {
                            cur_ty = emitter.input.pool.unwrapUnderlyingType(sub_fld.field_ty);
                        }
                    }
                } else if (cur_ty == .source_loc_ty) {
                    cur_ty = switch (proj.payload) {
                        0, 1 => .str_ty,
                        else => .u32_ty,
                    };
                } else if (node.tag == .union_ty) {
                    cur_ty = resolveUnionFieldType(emitter, cur_ty, proj.payload);
                } else if (emitter.resolver.getFieldByDeclOrdinal(cur_ty, proj.payload) catch null) |fld| {
                    cur_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                }
            },
            .index => {
                active_downcast = null;
                cur_ty = if (cur_ty == .str_ty)
                    .u8_ty
                else
                    emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            },
            .soa_elem => {
                active_downcast = null;
                const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                if (emitter.resolver.getFieldByDeclOrdinal(elem_struct, proj.payload) catch null) |fld| {
                    soa_col_field_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                }
            },
            .slice_len => return .usize_ty,
        }
    }
    return cur_ty;
}

/// Resolves field `field_ord` of `.union_ty` `union_ty`.
fn resolveUnionFieldType(emitter: *const CModuleEmitter, union_ty: TypeId, field_ord: u32) TypeId {
    const node = emitter.input.pool.getNode(union_ty);
    const sym_idx = SymbolIndex.fromInt(node.rhs);
    if (sym_idx.isNone() or sym_idx.asInt() >= emitter.input.sym_table.symbols.items.len) return .unit_ty;
    const un_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
    if (un_sym.target_scope.isNone()) return .unit_ty;
    const subst = type_system.NominalTypeSubst.init(
        emitter.input.pool,
        emitter.input.sym_table,
        union_ty,
    );
    var cur_ord: u32 = 0;
    for (emitter.input.sym_table.getScopeMembers(un_sym.target_scope)) |mem_idx| {
        const mem_sym = emitter.input.sym_table.getSymbol(mem_idx).*;
        if (mem_sym.kind != .field_sym) continue;
        if (cur_ord == field_ord) {
            return emitter.input.pool.unwrapUnderlyingType(subst.resolve(mem_sym.type_id));
        }
        cur_ord += 1;
    }
    return .unit_ty;
}

/// Formats the dynamic C99 byte offset expression for `#soa [S]` column `field_ord` given `len_expr`.
fn formatDynamicSoaColOffsetExpr(
    emitter: *CModuleEmitter,
    elem_struct_ty: TypeId,
    field_ord: u32,
    len_expr: []const u8,
) ![]u8 {
    const lay = try emitter.resolver.resolveType(elem_struct_ty);
    const fld_start = lay.aux_start;
    const fld_len = lay.aux_len;
    if (field_ord == 0 or fld_len == 0) {
        return emitter.allocator.dupe(u8, "((size_t)0u)");
    }

    const last_ord = @min(field_ord, fld_len - 1);
    const simd_log2 = emitter.target_layout.simd_align_log2;
    var open_parens: usize = 0;
    var ord_i: u32 = 0;
    while (ord_i <= last_ord) : (ord_i += 1) {
        if (ord_i > 0) open_parens += 2;
        if (ord_i < field_ord) open_parens += 1;
    }

    var buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer buf.deinit(emitter.allocator);
    try buf.appendNTimes(emitter.allocator, '(', open_parens);
    try buf.appendSlice(emitter.allocator, "((size_t)0u)");

    ord_i = 0;
    while (ord_i <= last_ord) : (ord_i += 1) {
        const fld = emitter.resolver.fields_by_decl.items[fld_start + ord_i];
        if (ord_i > 0) {
            const col_align: u64 = @as(u64, 1) << @intCast(@max(fld.align_log2, simd_log2));
            const align_suffix = try std.fmt.allocPrint(
                emitter.allocator,
                " + {d}u) & ~((size_t){d}u))",
                .{ col_align - 1, col_align - 1 },
            );
            defer emitter.allocator.free(align_suffix);
            try buf.appendSlice(emitter.allocator, align_suffix);
        }
        if (ord_i < field_ord) {
            const add_suffix = try std.fmt.allocPrint(
                emitter.allocator,
                " + ((size_t){d}u * (size_t)({s})))",
                .{ fld.size_bytes, len_expr },
            );
            defer emitter.allocator.free(add_suffix);
            try buf.appendSlice(emitter.allocator, add_suffix);
        }
    }
    return buf.toOwnedSlice(emitter.allocator);
}

/// Lowers `place_id` in `body` to an addressable C99 lvalue expression or constant `.len`.
fn lowerPlaceC(emitter: *CModuleEmitter, body: *const MirBody, place_id: PlaceId) !LoweredPlaceC {
    const place = body.places.items[place_id.asInt()];
    const base_decl = body.locals.items[place.base];
    const is_ptr_param = place.base >= 1 and place.base <= body.param_count and
        (base_decl.mode() == .inout_mode or base_decl.mode() == .set_mode);
    var cur_expr = blk_base: {
        if (emitter.active_coro_body_idx) |coro_b_idx| {
            if (!(try isZeroSizedType(emitter, base_decl.type_id))) {
                const plan = emitter.async_plan.?.getBodyPlan(coro_b_idx);
                const frame_off = plan.getLocalOffset(place.base);
                const base_c = try formatCType(emitter, base_decl.type_id);
                defer emitter.allocator.free(base_c);
                if (is_ptr_param) {
                    break :blk_base try std.fmt.allocPrint(
                        emitter.allocator,
                        "(**(({s} **)(_frame + {d}u)))",
                        .{ base_c, frame_off },
                    );
                }
                break :blk_base try std.fmt.allocPrint(
                    emitter.allocator,
                    "(*(({s} *)(_frame + {d}u)))",
                    .{ base_c, frame_off },
                );
            }
        }
        if (is_ptr_param) {
            break :blk_base try std.fmt.allocPrint(emitter.allocator, "(*_loc_{d})", .{place.base});
        }
        break :blk_base try std.fmt.allocPrint(emitter.allocator, "_loc_{d}", .{place.base});
    };
    errdefer emitter.allocator.free(cur_expr);

    var cur_ty = emitter.input.pool.unwrapUnderlyingType(base_decl.type_id);
    var active_downcast: ?u32 = null;
    var soa_pending: ?struct {
        col_ptr_expr: []u8,
        len_expr: ?[]u8,
        const_cap: u64,
        field_ty: TypeId,
    } = null;
    errdefer if (soa_pending) |sp| {
        emitter.allocator.free(sp.col_ptr_expr);
        if (sp.len_expr) |le| emitter.allocator.free(le);
    };

    for (body.getPlaceProjections(place_id)) |proj| {
        if (soa_pending) |sp| {
            soa_pending = null;
            defer {
                emitter.allocator.free(sp.col_ptr_expr);
                if (sp.len_expr) |le| emitter.allocator.free(le);
            }
            if (proj.kind == .index) {
                const idx_expr = try formatSsaIndexUsizeExpr(emitter, body, MirValueId.fromInt(proj.payload));
                defer emitter.allocator.free(idx_expr);
                const next_expr = try std.fmt.allocPrint(
                    emitter.allocator,
                    "({s}[{s}])",
                    .{ sp.col_ptr_expr, idx_expr },
                );
                emitter.allocator.free(cur_expr);
                cur_expr = next_expr;
                cur_ty = sp.field_ty;
                continue;
            } else if (proj.kind == .slice_len) {
                emitter.allocator.free(cur_expr);
                if (sp.len_expr) |le| {
                    return .{ .lvalue_expr = .{
                        .expr_str = try emitter.allocator.dupe(u8, le),
                        .pointee_ty = .usize_ty,
                    } };
                }
                return .{ .const_len = sp.const_cap };
            }
        }

        const node = emitter.input.pool.getNode(cur_ty);
        switch (proj.kind) {
            .deref => {
                active_downcast = null;
                const next_expr = try std.fmt.allocPrint(emitter.allocator, "(*({s}))", .{cur_expr});
                emitter.allocator.free(cur_expr);
                cur_expr = next_expr;
                cur_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            },
            .downcast => {
                active_downcast = proj.payload;
            },
            .field => {
                if (active_downcast) |tag_ord| {
                    active_downcast = null;
                    const sum_detail = (try emitter.resolver.getSumDetail(cur_ty)).?;
                    const var_pay_ty = resolveEnumVariantPayloadType(emitter, cur_ty, tag_ord);
                    const pay_expr = if (sum_detail.repr == .explicit_tag)
                        try std.fmt.allocPrint(emitter.allocator, "(({s})._u._v{d})", .{ cur_expr, tag_ord })
                    else
                        try std.fmt.allocPrint(emitter.allocator, "(({s})._pay)", .{cur_expr});
                    emitter.allocator.free(cur_expr);
                    cur_expr = pay_expr;
                    cur_ty = var_pay_ty;
                    if (proj.payload > 0) {
                        const sub_fld = (try emitter.resolver.getFieldByDeclOrdinal(cur_ty, proj.payload)).?;
                        const sub_expr = try std.fmt.allocPrint(
                            emitter.allocator,
                            "(({s})._f{d})",
                            .{ cur_expr, proj.payload },
                        );
                        emitter.allocator.free(cur_expr);
                        cur_expr = sub_expr;
                        cur_ty = emitter.input.pool.unwrapUnderlyingType(sub_fld.field_ty);
                    }
                } else if (cur_ty == .source_loc_ty) {
                    const fld_name = switch (proj.payload) {
                        0 => "file",
                        1 => "fn_name",
                        2 => "line",
                        else => "col",
                    };
                    const fld_ty: TypeId = switch (proj.payload) {
                        0, 1 => .str_ty,
                        else => .u32_ty,
                    };
                    const next_expr = try std.fmt.allocPrint(
                        emitter.allocator,
                        "(({s})->{s})",
                        .{ cur_expr, fld_name },
                    );
                    emitter.allocator.free(cur_expr);
                    cur_expr = next_expr;
                    cur_ty = fld_ty;
                } else if (node.tag == .union_ty) {
                    const fld_ty = resolveUnionFieldType(emitter, cur_ty, proj.payload);
                    const next_expr = try std.fmt.allocPrint(
                        emitter.allocator,
                        "(({s})._f{d})",
                        .{ cur_expr, proj.payload },
                    );
                    emitter.allocator.free(cur_expr);
                    cur_expr = next_expr;
                    cur_ty = fld_ty;
                } else {
                    const fld = (try emitter.resolver.getFieldByDeclOrdinal(cur_ty, proj.payload)).?;
                    const next_expr = try std.fmt.allocPrint(
                        emitter.allocator,
                        "(({s})._f{d})",
                        .{ cur_expr, proj.payload },
                    );
                    emitter.allocator.free(cur_expr);
                    cur_expr = next_expr;
                    cur_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                }
            },
            .index => {
                active_downcast = null;
                const elem_ty = if (cur_ty == .str_ty)
                    TypeId.u8_ty
                else
                    emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const idx_expr = try formatSsaIndexUsizeExpr(emitter, body, MirValueId.fromInt(proj.payload));
                defer emitter.allocator.free(idx_expr);
                const next_expr = if (cur_ty == .str_ty)
                    try std.fmt.allocPrint(emitter.allocator, "(((uint8_t *)(({s}).ptr))[{s}])", .{ cur_expr, idx_expr })
                else if (node.tag == .array_ty)
                    try std.fmt.allocPrint(emitter.allocator, "(({s})._elems[{s}])", .{ cur_expr, idx_expr })
                else if (node.tag == .raw_ptr_ty)
                    try std.fmt.allocPrint(emitter.allocator, "(({s})[{s}])", .{ cur_expr, idx_expr })
                else
                    try std.fmt.allocPrint(emitter.allocator, "(({s}).ptr[{s}])", .{ cur_expr, idx_expr });
                emitter.allocator.free(cur_expr);
                cur_expr = next_expr;
                cur_ty = elem_ty;
            },
            .soa_elem => {
                active_downcast = null;
                const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const fld = (try emitter.resolver.getFieldByDeclOrdinal(elem_struct, proj.payload)).?;
                const fld_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                const fld_c = if (try isZeroSizedType(emitter, fld_ty))
                    try emitter.allocator.dupe(u8, "uint8_t")
                else
                    try formatCType(emitter, fld_ty);
                defer emitter.allocator.free(fld_c);

                if (node.tag == .soa_array_ty) {
                    const cap: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                    const col_info = emitter.resolver.getSoaColumnOffset(elem_struct, proj.payload, cap).?;
                    const col_ptr = try std.fmt.allocPrint(
                        emitter.allocator,
                        "(({s} *)(&(({s})._bytes[{d}u])))",
                        .{ fld_c, cur_expr, col_info.byte_offset },
                    );
                    soa_pending = .{
                        .col_ptr_expr = col_ptr,
                        .len_expr = null,
                        .const_cap = cap,
                        .field_ty = fld_ty,
                    };
                } else {
                    const len_str = try std.fmt.allocPrint(emitter.allocator, "(({s}).len)", .{cur_expr});
                    errdefer emitter.allocator.free(len_str);
                    const off_str = try formatDynamicSoaColOffsetExpr(
                        emitter,
                        elem_struct,
                        proj.payload,
                        len_str,
                    );
                    defer emitter.allocator.free(off_str);
                    const col_ptr = try std.fmt.allocPrint(
                        emitter.allocator,
                        "(({s} *)((({s}).ptr) + {s}))",
                        .{ fld_c, cur_expr, off_str },
                    );
                    soa_pending = .{
                        .col_ptr_expr = col_ptr,
                        .len_expr = len_str,
                        .const_cap = 0,
                        .field_ty = fld_ty,
                    };
                }
            },
            .slice_len => {
                if (node.tag == .array_ty or node.tag == .soa_array_ty) {
                    emitter.allocator.free(cur_expr);
                    return .{ .const_len = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG };
                }
                const next_expr = try std.fmt.allocPrint(emitter.allocator, "(({s}).len)", .{cur_expr});
                emitter.allocator.free(cur_expr);
                return .{ .lvalue_expr = .{ .expr_str = next_expr, .pointee_ty = .usize_ty } };
            },
        }
    }
    return .{ .lvalue_expr = .{ .expr_str = cur_expr, .pointee_ty = cur_ty } };
}

/// Formats SSA index `idx_val` as a C `size_t` expression (trapping on negative signed index).
fn formatSsaIndexUsizeExpr(
    emitter: *CModuleEmitter,
    body: *const MirBody,
    idx_val: MirValueId,
) ![]u8 {
    if (try resolveIntegerInfo(emitter, body.getInst(idx_val).type_id)) |info| {
        if (info.bits == 128) {
            return std.fmt.allocPrint(emitter.allocator, "((size_t)_cx_u128_lo(_v_{d}))", .{idx_val.asInt()});
        }
    }
    return std.fmt.allocPrint(emitter.allocator, "((size_t)_v_{d})", .{idx_val.asInt()});
}

/// Resolves the `memcpy`-backed C99 `_cx_read_u*` helper name for `scalar_bytes`.
fn resolveUnalignedReadHelperName(scalar_bytes: u8) []const u8 {
    return switch (scalar_bytes) {
        1 => "_cx_read_u8",
        2 => "_cx_read_u16",
        4 => "_cx_read_u32",
        else => "_cx_read_u64",
    };
}

/// Resolves the `memcpy`-backed C99 `_cx_write_u*` helper name for `scalar_bytes`.
fn resolveUnalignedWriteHelperName(scalar_bytes: u8) []const u8 {
    return switch (scalar_bytes) {
        1 => "_cx_write_u8",
        2 => "_cx_write_u16",
        4 => "_cx_write_u32",
        else => "_cx_write_u64",
    };
}

/// Formats a C99 expression reading the active `u64` discriminant tag of `sum_ty` at `val_expr`.
fn formatSumDiscrReadExpr(
    emitter: *CModuleEmitter,
    raw_sum_ty: TypeId,
    sum_detail: ResolvedSumDetail,
    val_expr: []const u8,
) ![]u8 {
    _ = raw_sum_ty;
    return switch (sum_detail.repr) {
        .transparent_ok => emitter.allocator.dupe(u8, "0u"),
        .explicit_tag => std.fmt.allocPrint(
            emitter.allocator,
            "((uint64_t){s}((const uint8_t *)&({s}), 0u))",
            .{ resolveUnalignedReadHelperName(sum_detail.tag_bytes), val_expr },
        ),
        .niche_single => blk: {
            const niche = sum_detail.niche;
            if (niche.encoding == .zero_niche) {
                const ptr_bytes: u8 = @intCast(emitter.cfg.target.ptrBytes());
                break :blk std.fmt.allocPrint(
                    emitter.allocator,
                    "(({s}((const uint8_t *)&({s}), {d}u) == 0u) ? {d}u : {d}u)",
                    .{
                        resolveUnalignedReadHelperName(ptr_bytes),
                        val_expr,
                        niche.byte_offset,
                        sum_detail.zst_discriminant,
                        sum_detail.payload_discriminant,
                    },
                );
            }
            const sc_c = resolveUnsignedCTypeForBits(@as(u16, niche.scalar_bytes) * 8);
            break :blk std.fmt.allocPrint(
                emitter.allocator,
                "(({s}((const uint8_t *)&({s}), {d}u) == ({s}){d}ull) ? {d}u : {d}u)",
                .{
                    resolveUnalignedReadHelperName(niche.scalar_bytes),
                    val_expr,
                    niche.byte_offset,
                    sc_c,
                    niche.invalid_first,
                    sum_detail.zst_discriminant,
                    sum_detail.payload_discriminant,
                },
            );
        },
        .not_sum => emitter.allocator.dupe(u8, "0u"),
    };
}

/// Emits C99 statements writing discriminant `tag_ord` into addressable `sum_ty` lvalue `lhs_expr`.
fn emitSumDiscrWriteStmt(
    emitter: *CModuleEmitter,
    sum_ty: TypeId,
    tag_ord: u32,
    lhs_expr: []const u8,
) !void {
    const sum_detail = (try emitter.resolver.getSumDetail(sum_ty)) orelse return;
    switch (sum_detail.repr) {
        .transparent_ok, .not_sum => {},
        .explicit_tag => {
            const tag_c = resolveUnsignedCTypeForBits(@as(u16, sum_detail.tag_bytes) * 8);
            try emitter.print(
                "    {s}((uint8_t *)&({s}), 0u, ({s}){d}u);\n",
                .{ resolveUnalignedWriteHelperName(sum_detail.tag_bytes), lhs_expr, tag_c, tag_ord },
            );
        },
        .niche_single => {
            if (tag_ord != sum_detail.zst_discriminant) return;
            const niche = sum_detail.niche;
            if (niche.encoding == .zero_niche) {
                const ptr_bytes: u8 = @intCast(emitter.cfg.target.ptrBytes());
                try emitter.print(
                    "    {s}((uint8_t *)&({s}), {d}u, 0u);\n",
                    .{ resolveUnalignedWriteHelperName(ptr_bytes), lhs_expr, niche.byte_offset },
                );
            } else {
                const sc_c = resolveUnsignedCTypeForBits(@as(u16, niche.scalar_bytes) * 8);
                try emitter.print(
                    "    {s}((uint8_t *)&({s}), {d}u, ({s}){d}ull);\n",
                    .{ resolveUnalignedWriteHelperName(niche.scalar_bytes), lhs_expr, niche.byte_offset, sc_c, niche.invalid_first },
                );
            }
        },
    }
}

/// Returns `true` if `enum_ty` has any declared variant whose discriminant differs from its 0-based ordinal.
fn hasCustomEnumDiscriminants(emitter: *const CModuleEmitter, enum_ty: TypeId) bool {
    const var_count = countEnumVariants(emitter, enum_ty);
    var var_ord: u32 = 0;
    while (var_ord < var_count) : (var_ord += 1) {
        const disc_val = emitter.input.pool.getEnumVariantDiscriminant(enum_ty, var_ord) orelse
            @as(i128, var_ord);
        if (disc_val != @as(i128, var_ord)) return true;
    }
    return false;
}

/// Emits C99 assignment writing the backing integer discriminant of variant `tag_ord` into `lhs_expr`.
fn emitScalarEnumDiscrimWriteC(
    emitter: *CModuleEmitter,
    enum_ty: TypeId,
    tag_ord: u32,
    lhs_expr: []const u8,
) !void {
    const info = (try resolveIntegerInfo(emitter, enum_ty)) orelse return;
    const disc_val = emitter.input.pool.getEnumVariantDiscriminant(enum_ty, tag_ord) orelse
        @as(i128, tag_ord);
    const disc_bits: u128 = @bitCast(disc_val);
    if (info.bits == 128) {
        const fn_make = if (info.is_signed) "_cx_i128_make" else "_cx_u128_make";
        try emitter.print(
            "    {s} = {s}({d}ull, {d}ull);\n",
            .{ lhs_expr, fn_make, @as(u64, @truncate(disc_bits)), @as(u64, @truncate(disc_bits >> 64)) },
        );
    } else {
        const mask: u64 = if (info.bits >= 64)
            std.math.maxInt(u64)
        else
            (@as(u64, 1) << @intCast(info.bits)) - 1;
        const dst_c = try formatCType(emitter, enum_ty);
        defer emitter.allocator.free(dst_c);
        try emitter.print(
            "    {s} = ({s})({d}ull);\n",
            .{ lhs_expr, dst_c, @as(u64, @truncate(disc_bits)) & mask },
        );
    }
}

/// Emits C99 statements mapping a fieldless/backed `enum` value `val_expr` to its 0-based ordinal in `_v_<dst_raw>`.
fn emitScalarEnumOrdinalReadC(
    emitter: *CModuleEmitter,
    enum_ty: TypeId,
    val_expr: []const u8,
    dst_raw: u32,
    dst_c: []const u8,
) !void {
    const info = (try resolveIntegerInfo(emitter, enum_ty)) orelse {
        try emitter.print("    _v_{d} = ({s})0u;\n", .{ dst_raw, dst_c });
        return;
    };
    if (!hasCustomEnumDiscriminants(emitter, enum_ty)) {
        if (info.bits == 128) {
            try emitter.print("    _v_{d} = ({s})_cx_u128_lo(_cx_as_u128({s}));\n", .{ dst_raw, dst_c, val_expr });
        } else {
            try emitter.print("    _v_{d} = ({s})({s});\n", .{ dst_raw, dst_c, val_expr });
        }
        return;
    }

    const var_count = countEnumVariants(emitter, enum_ty);
    const mask: u64 = if (info.bits >= 64)
        std.math.maxInt(u64)
    else
        (@as(u64, 1) << @intCast(info.bits)) - 1;
    const u_c = resolveUnsignedCTypeForBits(if (info.bits == 128) 64 else info.bits);
    var var_ord: u32 = 0;
    while (var_ord < var_count) : (var_ord += 1) {
        const disc_val = emitter.input.pool.getEnumVariantDiscriminant(enum_ty, var_ord) orelse
            @as(i128, var_ord);
        const disc_bits: u128 = @bitCast(disc_val);
        const kw = if (var_ord == 0) "    if" else "    else if";
        if (info.bits == 128) {
            try emitter.print(
                "{s} (_cx_u128_eq(_cx_as_u128({s}), _cx_u128_make({d}ull, {d}ull))) _v_{d} = ({s}){d}u;\n",
                .{
                    kw,
                    val_expr,
                    @as(u64, @truncate(disc_bits)),
                    @as(u64, @truncate(disc_bits >> 64)),
                    dst_raw,
                    dst_c,
                    var_ord,
                },
            );
        } else {
            try emitter.print(
                "{s} ((({s})({s})) == ({s})({d}ull)) _v_{d} = ({s}){d}u;\n",
                .{ kw, u_c, val_expr, u_c, @as(u64, @truncate(disc_bits)) & mask, dst_raw, dst_c, var_ord },
            );
        }
    }
    if (var_count > 0) {
        try emitter.print("    else _v_{d} = ({s})0u;\n", .{ dst_raw, dst_c });
    }
}

/// Returns `true` when `inst` is a 0-hole `.fmt_args_make` whose pieces are all `.str_val` constants.
fn isStaticConstFmtArgsMake(body: *const MirBody, inst: mir.MirInst) bool {
    const words = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
    if (words.len < 1) return false;
    const piece_count = extractConstUsizeFromBody(body, words[0]) orelse return false;
    if (words.len != 1 + piece_count) return false;
    var piece_i: usize = 0;
    while (piece_i < piece_count) : (piece_i += 1) {
        if (extractConstStrSymFromBody(body, words[1 + piece_i]) == null) return false;
    }
    return true;
}

/// Extracts `(ptr_expr, len_expr)` C99 expressions for a byte slice/array/ref value `val_id`.
fn formatWireByteSpanExprs(
    emitter: *CModuleEmitter,
    raw_ty: TypeId,
    val_id: MirValueId,
) !struct { ptr_expr: []u8, len_expr: []u8 } {
    const ty = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    const v_raw = val_id.asInt();
    if (ty == .str_ty) {
        return .{
            .ptr_expr = try std.fmt.allocPrint(emitter.allocator, "((const uint8_t *)_v_{d}.ptr)", .{v_raw}),
            .len_expr = try std.fmt.allocPrint(emitter.allocator, "((size_t)_v_{d}.len)", .{v_raw}),
        };
    }
    const node = emitter.input.pool.getNode(ty);
    switch (node.tag) {
        .slice_ty => return .{
            .ptr_expr = try std.fmt.allocPrint(emitter.allocator, "((const uint8_t *)_v_{d}.ptr)", .{v_raw}),
            .len_expr = try std.fmt.allocPrint(emitter.allocator, "((size_t)_v_{d}.len)", .{v_raw}),
        },
        .array_ty => {
            const arr_len: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            return .{
                .ptr_expr = try std.fmt.allocPrint(emitter.allocator, "((const uint8_t *)&_v_{d}._elems[0])", .{v_raw}),
                .len_expr = try std.fmt.allocPrint(emitter.allocator, "((size_t){d}u)", .{arr_len}),
            };
        },
        .ref_ty, .mut_ref_ty, .raw_ptr_ty => {
            const inner_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            if (inner_ty == .str_ty or emitter.input.pool.getNode(inner_ty).tag == .slice_ty) {
                return .{
                    .ptr_expr = try std.fmt.allocPrint(emitter.allocator, "((const uint8_t *)(_v_{d}->ptr))", .{v_raw}),
                    .len_expr = try std.fmt.allocPrint(emitter.allocator, "((size_t)(_v_{d}->len))", .{v_raw}),
                };
            }
            const inner_node = emitter.input.pool.getNode(inner_ty);
            if (inner_node.tag == .array_ty) {
                const arr_len: u64 = inner_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                return .{
                    .ptr_expr = try std.fmt.allocPrint(
                        emitter.allocator,
                        "((const uint8_t *)(&_v_{d}->_elems[0]))",
                        .{v_raw},
                    ),
                    .len_expr = try std.fmt.allocPrint(emitter.allocator, "((size_t){d}u)", .{arr_len}),
                };
            }
            const inner_lay = try emitter.resolver.resolveType(inner_ty);
            return .{
                .ptr_expr = try std.fmt.allocPrint(emitter.allocator, "((const uint8_t *)_v_{d})", .{v_raw}),
                .len_expr = try std.fmt.allocPrint(emitter.allocator, "((size_t){d}u)", .{inner_lay.size_bytes}),
            };
        },
        else => return .{
            .ptr_expr = try emitter.allocator.dupe(u8, "((const uint8_t *)0)"),
            .len_expr = try emitter.allocator.dupe(u8, "((size_t)0u)"),
        },
    }
}

/// Formats an integer SSA value `val_id` widened into signed `cx_i128` for `.narrow()` / `.try_narrow()`.
fn formatAsCxI128Expr(
    emitter: *CModuleEmitter,
    val_id: MirValueId,
    val_ty: TypeId,
) ![]u8 {
    const info = (try resolveIntegerInfo(emitter, val_ty)) orelse
        return emitter.allocator.dupe(u8, "_cx_i128_make(0ull, 0ull)");
    if (info.bits == 128) {
        return std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{val_id.asInt()});
    }
    if (info.is_signed) {
        const tmp_id = emitter.nextTempId();
        try emitter.print(
            "    int64_t _sx_{d} = (int64_t)_v_{d};\n",
            .{ tmp_id, val_id.asInt() },
        );
        return std.fmt.allocPrint(
            emitter.allocator,
            "_cx_i128_make((uint64_t)_sx_{d}, _sx_{d} < 0 ? 0xFFFFFFFFFFFFFFFFull : 0ull)",
            .{ tmp_id, tmp_id },
        );
    }
    return std.fmt.allocPrint(
        emitter.allocator,
        "_cx_i128_make((uint64_t)_v_{d}, 0ull)",
        .{val_id.asInt()},
    );
}

/// Formats an integer SSA value `val_id` widened into `cx_u128` (sign-extending signed `< 128`-bit values).
fn formatIntAsCxU128Expr(
    emitter: *CModuleEmitter,
    val_id: MirValueId,
    val_ty: TypeId,
) ![]u8 {
    const info = (try resolveIntegerInfo(emitter, val_ty)) orelse
        return emitter.allocator.dupe(u8, "_cx_u128_make(0ull, 0ull)");
    if (info.bits == 128) {
        return std.fmt.allocPrint(emitter.allocator, "_cx_as_u128(_v_{d})", .{val_id.asInt()});
    }
    if (info.is_signed) {
        const s_c = resolveSignedCTypeForBits(info.bits);
        const tmp_id = emitter.nextTempId();
        try emitter.print(
            "    int64_t _su_{d} = (int64_t)(({s})_v_{d});\n",
            .{ tmp_id, s_c, val_id.asInt() },
        );
        return std.fmt.allocPrint(
            emitter.allocator,
            "_cx_u128_make((uint64_t)_su_{d}, _su_{d} < 0 ? 0xFFFFFFFFFFFFFFFFull : 0ull)",
            .{ tmp_id, tmp_id },
        );
    }
    const u_c = resolveUnsignedCTypeForBits(info.bits);
    return std.fmt.allocPrint(
        emitter.allocator,
        "_cx_u128_make((uint64_t)(({s})_v_{d}), 0ull)",
        .{ u_c, val_id.asInt() },
    );
}

// ------------- MirBody Instruction & CFG Lowering -------------

/// Returns the inner `[T]` / `#soa [T]` slice `TypeId` if `raw_ty` is `&[T]` / `&mut [T]` / `*[T]`.
fn resolveSliceRefPointee(emitter: *const CModuleEmitter, raw_ty: TypeId) ?TypeId {
    const ty = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (ty.isPrimitiveOrSentinel()) return null;
    const node = emitter.input.pool.getNode(ty);
    if (node.tag != .ref_ty and node.tag != .mut_ref_ty and node.tag != .raw_ptr_ty) return null;
    const pointee = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
    if (pointee == .str_ty) return pointee;
    if (pointee.isPrimitiveOrSentinel()) return null;
    const p_tag = emitter.input.pool.getNode(pointee).tag;
    if (p_tag == .slice_ty or p_tag == .soa_slice_ty) return pointee;
    return null;
}

/// Resolves 1-based `(line, col)` for `byte_off` inside `entry` without mutating `*const VfsSourceMap`.
fn resolveSourceLineOneBased(entry: *const vfs_sourcemap.VfsFileEntry, byte_off: u32) u32 {
    if (entry.line_index) |*cached_idx| {
        return cached_idx.resolveLineCol(entry.content, byte_off).line;
    }
    const clamped_end: usize = @min(@as(usize, byte_off), entry.content.len);
    var line_num: u32 = 1;
    for (entry.content[0..clamped_end]) |ch_b| {
        if (ch_b == '\n') line_num += 1;
    }
    return line_num;
}

/// Emits `#line <line> "<file>"` when `has_line_directives` and source map metadata are available.
fn maybeEmitLineDirective(
    emitter: *CModuleEmitter,
    file_id: FileId,
    tok_idx: TokenIndex,
) !void {
    if (!emitter.cfg.has_line_directives or file_id.isNone() or tok_idx.isNone()) return;
    const smap = emitter.input.vfs_source_map orelse return;
    const tok_map = emitter.input.file_tokens orelse return;
    const tok_buf = tok_map.get(file_id.asInt()) orelse return;
    if (tok_idx.asInt() >= tok_buf.countTokens()) return;
    const file_entry = smap.getFileEntry(file_id) orelse return;
    const file_path = smap.getFilePath(file_id);
    if (file_path.len == 0) return;
    const byte_off = tok_buf.getToken(tok_idx).byte_offset;
    const line_one_based = resolveSourceLineOneBased(file_entry, byte_off);
    try emitter.print("#line {d} \"", .{line_one_based});
    try appendEscapedCStringContents(emitter, file_path);
    try emitter.writeAll("\"\n");
}

/// Emits the complete C99 definition of `body` (`emitter.input.bodies[body_idx]`).
fn emitMirBody(emitter: *CModuleEmitter, body_idx: u32, body: *const MirBody) !void {
    emitter.temp_counter = 0;
    emitter.is_in_c_abi_body = isBodyCAbiBoundary(emitter, body);
    defer emitter.is_in_c_abi_body = false;

    const is_void_ret = try isZeroSizedType(emitter, body.ret_ty);
    const ret_c = if (is_void_ret)
        try emitter.allocator.dupe(u8, "void")
    else
        try formatCType(emitter, body.ret_ty);
    defer emitter.allocator.free(ret_c);

    try emitBodyFunctionAttributesC(emitter, body, true);
    const storage_kw = if (isBodyExternallyVisible(emitter, body)) "" else "static ";
    try emitter.print("{s}{s} {s}", .{ storage_kw, ret_c, emitter.body_c_names.items[body_idx] });
    try emitBodyParamList(emitter, body, true);
    try emitter.writeAll(" {\n");

    if (body.is_async) {
        var p_i: u32 = 0;
        while (p_i < body.param_count) : (p_i += 1) {
            const p_decl = body.locals.items[1 + p_i];
            const p_mode = p_decl.mode();
            if (p_mode == .inout_mode or p_mode == .set_mode or !(try isZeroSizedType(emitter, p_decl.type_id))) {
                try emitter.print("    (void)_arg_{d};\n", .{1 + p_i});
            }
        }
        if (emitter.entry_main_body_idx == body_idx and
            body.param_count == 0 and
            emitter.has_async_ops)
        {
            const ret_lay = try emitter.resolver.resolveType(body.ret_ty);
            if (is_void_ret) {
                try emitter.print(
                    "    uint8_t *_mf = _cx_coro_alloc({d}u);\n" ++
                        "    _cx_fut_raw_t _mfut = {{ (void *)_mf, 1u, {d}u, 0u }};\n" ++
                        "    _cx_async_block_on(&_mfut, NULL);\n" ++
                        "    return;\n}}\n\n",
                    .{ body_idx, body_idx },
                );
            } else {
                try emitter.print(
                    "    {s} _mres; memset(&_mres, 0, sizeof(_mres));\n" ++
                        "    uint8_t *_mf = _cx_coro_alloc({d}u);\n" ++
                        "    _cx_fut_raw_t _mfut = {{ (void *)_mf, 1u, {d}u, {d}u }};\n" ++
                        "    _cx_async_block_on(&_mfut, &_mres);\n" ++
                        "    return _mres;\n}}\n\n",
                    .{ ret_c, body_idx, body_idx, ret_lay.size_bytes },
                );
            }
        } else if (is_void_ret) {
            try emitter.writeAll("    return;\n}\n\n");
        } else {
            try emitter.print(
                "    {s} _zres; memset(&_zres, 0, sizeof(_zres)); return _zres;\n}}\n\n",
                .{ret_c},
            );
        }
        if (emitter.has_async_ops) {
            try emitAsyncCoroPollBodyC(emitter, body_idx, body);
        }
        return;
    }

    // [1] Frame local declarations (`_loc_0 .. _loc_{N-1}`), zero-initializing all padding (`D-01`):
    for (body.locals.items, 0..) |loc_decl, loc_i| {
        const is_param = loc_i >= 1 and loc_i <= body.param_count;
        const p_mode = loc_decl.mode();
        if (is_param and (p_mode == .inout_mode or p_mode == .set_mode)) {
            if (try isZeroSizedType(emitter, loc_decl.type_id)) {
                try emitter.print("    uint8_t *_loc_{d} = _arg_{d}; (void)_loc_{d};\n", .{ loc_i, loc_i, loc_i });
            } else {
                const loc_c = try formatCType(emitter, loc_decl.type_id);
                defer emitter.allocator.free(loc_c);
                try emitter.print("    {s} *_loc_{d} = _arg_{d}; (void)_loc_{d};\n", .{ loc_c, loc_i, loc_i, loc_i });
            }
        } else if (try isZeroSizedType(emitter, loc_decl.type_id)) {
            try emitter.print("    uint8_t _loc_{d} = 0u; (void)_loc_{d};\n", .{ loc_i, loc_i });
        } else if (is_param) {
            const loc_c = try formatCType(emitter, loc_decl.type_id);
            defer emitter.allocator.free(loc_c);
            try emitter.print("    {s} _loc_{d} = _arg_{d}; (void)_loc_{d};\n", .{ loc_c, loc_i, loc_i, loc_i });
        } else {
            const loc_c = try formatCType(emitter, loc_decl.type_id);
            defer emitter.allocator.free(loc_c);
            try emitter.print(
                "    {s} _loc_{d}; memset(&_loc_{d}, 0, sizeof(_loc_{d})); (void)_loc_{d};\n",
                .{ loc_c, loc_i, loc_i, loc_i, loc_i },
            );
        }
    }

    // [2] SSA value registers (`_v_0 .. _v_{M-1}`), closure envs, and slice coercion temporaries:
    for (0..body.insts.len) |inst_i| {
        const inst = body.insts.get(inst_i);
        if (inst.op.isGhost()) continue;
        if (try isZeroSizedType(emitter, inst.type_id)) {
            try emitter.print("    uint8_t _v_{d} = 0u; (void)_v_{d};\n", .{ inst_i, inst_i });
        } else {
            const val_c = try formatCType(emitter, inst.type_id);
            defer emitter.allocator.free(val_c);
            try emitter.print(
                "    {s} _v_{d}; memset(&_v_{d}, 0, sizeof(_v_{d})); (void)_v_{d};\n",
                .{ val_c, inst_i, inst_i, inst_i, inst_i },
            );
        }

        if (inst.op == .aggregate_make) {
            const agg_k: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            if (agg_k == .closure_make) {
                const key: u64 = (@as(u64, body_idx) << 32) | @as(u64, @intCast(inst_i));
                if (emitter.closure_thunk_map.get(key)) |thunk_idx| {
                    const thunk = emitter.closure_thunks.items[thunk_idx];
                    if (!thunk.is_three_word and thunk.capture_types.len > 0) {
                        try emitter.print(
                            "    _cx_cenv_{d} _cenv_loc_{d}; memset(&_cenv_loc_{d}, 0, sizeof(_cenv_loc_{d}));\n",
                            .{ thunk_idx, inst_i, inst_i, inst_i },
                        );
                    }
                }
            } else if (agg_k == .fmt_args_make and !isStaticConstFmtArgsMake(body, inst)) {
                const words = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
                if (words.len >= 1) {
                    if (extractConstUsizeFromBody(body, words[0])) |piece_count| {
                        if (piece_count > 0) {
                            try emitter.print(
                                "    cx_str_t _fmt_p_{d}[{d}u]; memset(_fmt_p_{d}, 0, sizeof(_fmt_p_{d}));\n",
                                .{ inst_i, piece_count, inst_i, inst_i },
                            );
                        }
                        if (words.len >= 1 + piece_count) {
                            const hole_count = (words.len - 1 - piece_count) / 3;
                            if (hole_count > 0) {
                                try emitter.print(
                                    "    cx_fmt_arg_t _fmt_a_{d}[{d}u]; memset(_fmt_a_{d}, 0, sizeof(_fmt_a_{d}));\n",
                                    .{ inst_i, hole_count, inst_i, inst_i },
                                );
                                for (0..hole_count) |hole_j| {
                                    const hole_ref_raw = words[1 + piece_count + hole_j * 3];
                                    const hole_ref_ty = emitter.input.pool.unwrapUnderlyingType(
                                        body.getInst(MirValueId.fromInt(hole_ref_raw)).type_id,
                                    );
                                    const hole_node = emitter.input.pool.getNode(hole_ref_ty);
                                    const is_ptr_arg = hole_node.tag == .ref_ty or
                                        hole_node.tag == .mut_ref_ty or
                                        hole_node.tag == .raw_ptr_ty;
                                    if (!is_ptr_arg and !(try isZeroSizedType(emitter, hole_ref_ty))) {
                                        const hole_c = try formatCType(emitter, hole_ref_ty);
                                        defer emitter.allocator.free(hole_c);
                                        try emitter.print(
                                            "    {s} _fmt_h_{d}_{d}; memset(&_fmt_h_{d}_{d}, 0, sizeof(_fmt_h_{d}_{d}));\n",
                                            .{ hole_c, inst_i, hole_j, inst_i, hole_j, inst_i, hole_j },
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        if (inst.op == .place_addr or inst.op == .unary_op or inst.op == .intrinsic_op) {
            if (resolveSliceRefPointee(emitter, inst.type_id)) |sl_pointee| {
                const sl_c = try formatCType(emitter, sl_pointee);
                defer emitter.allocator.free(sl_c);
                try emitter.print(
                    "    {s} _stmp_{d}; memset(&_stmp_{d}, 0, sizeof(_stmp_{d}));\n",
                    .{ sl_c, inst_i, inst_i, inst_i },
                );
            }
        }
        if (inst.op == .intrinsic_op) {
            if (@as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)) == .ctx_get) {
                if (type_system.ContextFieldLayout.resolveRefPointee(
                    emitter.input.pool,
                    emitter.input.sym_table,
                    inst.type_id,
                )) |ctx_pointee| {
                    if (try isZeroSizedType(emitter, ctx_pointee)) {
                        try emitter.print("    uint8_t _ctx_snap_{d} = 0u;\n", .{inst_i});
                    } else {
                        const ctx_c = try formatCType(emitter, ctx_pointee);
                        defer emitter.allocator.free(ctx_c);
                        try emitter.print(
                            "    {s} _ctx_snap_{d}; memset(&_ctx_snap_{d}, 0, sizeof(_ctx_snap_{d}));\n",
                            .{ ctx_c, inst_i, inst_i, inst_i },
                        );
                    }
                }
            }
        }
    }

    if (body.blocks.items.len > 0) {
        try emitter.writeAll("    goto _bb_0;\n");
    }

    // [3] Basic blocks:
    for (body.blocks.items, 0..) |bb_rec, bb_i| {
        const bb_id = MirBlockId.fromInt(@intCast(bb_i));
        emitter.active_bb_id = bb_id;
        try emitter.print("_bb_{d}: ;\n", .{bb_i});
        for (body.getBlockInsts(bb_id)) |val_id| {
            const inst = body.getInst(val_id);
            if (inst.op.isGhost()) continue;
            if (val_id.asInt() < body.origin_tokens.items.len) {
                try maybeEmitLineDirective(emitter, body.file_id, body.origin_tokens.items[val_id.asInt()]);
            }
            try emitMirInstC(emitter, body_idx, body, val_id, inst);
        }
        try emitMirTerminatorC(emitter, body_idx, body, bb_id, bb_rec.terminator);
    }
    emitter.active_bb_id = .none;

    if (body.blocks.items.len == 0) {
        if (!is_void_ret) try emitter.writeAll("    return _loc_0;\n");
    }
    try emitter.writeAll("}\n\n");
}

/// Emits the stackless state-machine poll function `_cx_coro_poll_<body_idx>` (`DR-08` §2–§3).
fn emitAsyncCoroPollBodyC(emitter: *CModuleEmitter, body_idx: u32, body: *const MirBody) !void {
    const plan_mod = &(emitter.async_plan orelse return);
    const plan = plan_mod.getBodyPlan(body_idx);

    emitter.temp_counter = 0;
    emitter.active_coro_body_idx = body_idx;
    defer {
        emitter.active_coro_body_idx = null;
        emitter.active_bb_id = .none;
    }

    var undef_macros: std.ArrayListUnmanaged([]u8) = .empty;
    defer {
        for (undef_macros.items) |macro_name| emitter.allocator.free(macro_name);
        undef_macros.deinit(emitter.allocator);
    }

    try emitter.print(
        "static uint32_t _cx_coro_poll_{d}(uint8_t *_frame, void *_out_ptr, uint32_t _action, uint8_t *_parked_out) {{\n" ++
            "    (void)_frame; (void)_out_ptr; (void)_action; (void)_parked_out;\n",
        .{body_idx},
    );

    // [1] ZST dummy locals (`non-ZST` locals reside at `_frame + plan.getLocalOffset(loc_i)`):
    for (body.locals.items, 0..) |loc_decl, loc_i| {
        if (!(try isZeroSizedType(emitter, loc_decl.type_id))) continue;
        const is_param = loc_i >= 1 and loc_i <= body.param_count;
        const p_mode = loc_decl.mode();
        if (is_param and (p_mode == .inout_mode or p_mode == .set_mode)) {
            try emitter.print(
                "    uint8_t *_loc_{d} = (uint8_t *)((uintptr_t)1u); (void)_loc_{d};\n",
                .{ loc_i, loc_i },
            );
        } else {
            try emitter.print("    uint8_t _loc_{d} = 0u; (void)_loc_{d};\n", .{ loc_i, loc_i });
        }
    }

    // [2] Intra-block SSA temporaries (`_v_*`) & frame-backed `_cenv_loc_*` / `_fmt_*` / `_stmp_*` / `_ctx_snap_*`:
    var extra_cursor: u64 = std.mem.alignForward(
        u64,
        @max(@as(u64, plan.frame_layout.total_frame_bytes), 16),
        @as(u64, @max(plan.frame_align, 16)),
    );
    const ptr_bytes: u64 = emitter.cfg.target.ptrBytes();
    const ptr_scratch_align: u64 = @max(ptr_bytes, 8);
    const piece_stride: u64 = 2 * ptr_bytes;
    const arg_stride: u64 = std.mem.alignForward(u64, 2 * ptr_bytes + 8, ptr_bytes);
    for (0..body.insts.len) |inst_i| {
        const inst = body.insts.get(inst_i);
        if (inst.op.isGhost()) continue;
        if (try isZeroSizedType(emitter, inst.type_id)) {
            try emitter.print("    uint8_t _v_{d} = 0u; (void)_v_{d};\n", .{ inst_i, inst_i });
        } else {
            const val_c = try formatCType(emitter, inst.type_id);
            defer emitter.allocator.free(val_c);
            try emitter.print(
                "    {s} _v_{d}; memset(&_v_{d}, 0, sizeof(_v_{d})); (void)_v_{d};\n",
                .{ val_c, inst_i, inst_i, inst_i, inst_i },
            );
        }

        if (inst.op == .aggregate_make) {
            const agg_k: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            if (agg_k == .closure_make) {
                const key: u64 = (@as(u64, body_idx) << 32) | @as(u64, @intCast(inst_i));
                if (emitter.closure_thunk_map.get(key)) |thunk_idx| {
                    const thunk = emitter.closure_thunks.items[thunk_idx];
                    if (!thunk.is_three_word and thunk.capture_types.len > 0) {
                        const env_off = plan.findClosureEnvOffset(@intCast(inst_i)) orelse 16;
                        try emitter.print(
                            "#define _cenv_loc_{d} (*((_cx_cenv_{d} *)(_frame + {d}u)))\n",
                            .{ inst_i, thunk_idx, env_off },
                        );
                        try undef_macros.append(
                            emitter.allocator,
                            try std.fmt.allocPrint(emitter.allocator, "_cenv_loc_{d}", .{inst_i}),
                        );
                    }
                }
            } else if (agg_k == .fmt_args_make and !isStaticConstFmtArgsMake(body, inst)) {
                const words = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
                if (words.len >= 1) {
                    if (extractConstUsizeFromBody(body, words[0])) |piece_count| {
                        if (piece_count > 0) {
                            extra_cursor = std.mem.alignForward(u64, extra_cursor, ptr_scratch_align);
                            try emitter.print(
                                "#define _fmt_p_{d} ((cx_str_t *)(_frame + {d}u))\n",
                                .{ inst_i, extra_cursor },
                            );
                            try undef_macros.append(
                                emitter.allocator,
                                try std.fmt.allocPrint(emitter.allocator, "_fmt_p_{d}", .{inst_i}),
                            );
                            extra_cursor += @as(u64, piece_count) * piece_stride;
                        }
                        if (words.len >= 1 + piece_count) {
                            const hole_count = (words.len - 1 - piece_count) / 3;
                            if (hole_count > 0) {
                                extra_cursor = std.mem.alignForward(u64, extra_cursor, ptr_scratch_align);
                                try emitter.print(
                                    "#define _fmt_a_{d} ((cx_fmt_arg_t *)(_frame + {d}u))\n",
                                    .{ inst_i, extra_cursor },
                                );
                                try undef_macros.append(
                                    emitter.allocator,
                                    try std.fmt.allocPrint(emitter.allocator, "_fmt_a_{d}", .{inst_i}),
                                );
                                extra_cursor += @as(u64, hole_count) * arg_stride;
                                for (0..hole_count) |hole_j| {
                                    const hole_ref_raw = words[1 + piece_count + hole_j * 3];
                                    const hole_ref_ty = emitter.input.pool.unwrapUnderlyingType(
                                        body.getInst(MirValueId.fromInt(hole_ref_raw)).type_id,
                                    );
                                    const hole_node = emitter.input.pool.getNode(hole_ref_ty);
                                    const is_ptr_arg = hole_node.tag == .ref_ty or
                                        hole_node.tag == .mut_ref_ty or
                                        hole_node.tag == .raw_ptr_ty;
                                    if (!is_ptr_arg and !(try isZeroSizedType(emitter, hole_ref_ty))) {
                                        const hole_lay = try emitter.resolver.resolveType(hole_ref_ty);
                                        extra_cursor = std.mem.alignForward(
                                            u64,
                                            extra_cursor,
                                            @max(hole_lay.alignBytes(), 8),
                                        );
                                        const hole_c = try formatCType(emitter, hole_ref_ty);
                                        defer emitter.allocator.free(hole_c);
                                        try emitter.print(
                                            "#define _fmt_h_{d}_{d} (*(({s} *)(_frame + {d}u)))\n",
                                            .{ inst_i, hole_j, hole_c, extra_cursor },
                                        );
                                        try undef_macros.append(
                                            emitter.allocator,
                                            try std.fmt.allocPrint(emitter.allocator, "_fmt_h_{d}_{d}", .{ inst_i, hole_j }),
                                        );
                                        extra_cursor += @max(hole_lay.size_bytes, 1);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        if (inst.op == .place_addr or inst.op == .unary_op or inst.op == .intrinsic_op) {
            if (resolveSliceRefPointee(emitter, inst.type_id)) |sl_pointee| {
                const sl_lay = try emitter.resolver.resolveType(sl_pointee);
                extra_cursor = std.mem.alignForward(u64, extra_cursor, @max(sl_lay.alignBytes(), 8));
                const sl_c = try formatCType(emitter, sl_pointee);
                defer emitter.allocator.free(sl_c);
                try emitter.print(
                    "#define _stmp_{d} (*(({s} *)(_frame + {d}u)))\n",
                    .{ inst_i, sl_c, extra_cursor },
                );
                try undef_macros.append(
                    emitter.allocator,
                    try std.fmt.allocPrint(emitter.allocator, "_stmp_{d}", .{inst_i}),
                );
                extra_cursor += @max(sl_lay.size_bytes, 16);
            }
        }
        if (inst.op == .intrinsic_op) {
            if (@as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)) == .ctx_get) {
                if (type_system.ContextFieldLayout.resolveRefPointee(
                    emitter.input.pool,
                    emitter.input.sym_table,
                    inst.type_id,
                )) |ctx_pointee| {
                    if (try isZeroSizedType(emitter, ctx_pointee)) {
                        try emitter.print("    uint8_t _ctx_snap_{d} = 0u;\n", .{inst_i});
                    } else {
                        const ctx_lay = try emitter.resolver.resolveType(ctx_pointee);
                        extra_cursor = std.mem.alignForward(u64, extra_cursor, @max(ctx_lay.alignBytes(), 8));
                        const ctx_c = try formatCType(emitter, ctx_pointee);
                        defer emitter.allocator.free(ctx_c);
                        try emitter.print(
                            "#define _ctx_snap_{d} (*(({s} *)(_frame + {d}u)))\n",
                            .{ inst_i, ctx_c, extra_cursor },
                        );
                        try undef_macros.append(
                            emitter.allocator,
                            try std.fmt.allocPrint(emitter.allocator, "_ctx_snap_{d}", .{inst_i}),
                        );
                        extra_cursor += @max(ctx_lay.size_bytes, 8);
                    }
                }
            }
        }
    }

    // [3] Entry state switch (`0 = unpolled`, `1..K = suspended`, `completed/canceled = done`):
    try emitter.writeAll(
        "    uint32_t _coro_st = 0u;\n" ++
            "    memcpy(&_coro_st, _frame, 4u);\n" ++
            "    switch (_coro_st) {\n" ++
            "    case 0u:\n" ++
            "        if (_action == 1u) {\n" ++
            "            uint32_t _cs = 0xFFFFFFFFu;\n" ++
            "            memcpy(_frame, &_cs, 4u);\n",
    );
    var rev_p: u32 = body.param_count;
    while (rev_p > 0) {
        const p_decl = body.locals.items[rev_p];
        const p_mode = p_decl.mode();
        if (p_mode != .inout_mode and p_mode != .set_mode) {
            const unwrapped_p = emitter.input.pool.unwrapUnderlyingType(p_decl.type_id);
            if (!emitter.input.pool.getFlags(unwrapped_p).is_copy and
                emitter.drop_type_set.contains(unwrapped_p.toU32()) and
                !(try isZeroSizedType(emitter, unwrapped_p)))
            {
                const p_c = try formatCType(emitter, unwrapped_p);
                defer emitter.allocator.free(p_c);
                try emitter.print(
                    "            _cx_drop_ty_{d}(({s} *)(_frame + {d}u));\n",
                    .{ unwrapped_p.toU32(), p_c, plan.getLocalOffset(rev_p) },
                );
            }
        }
        rev_p -= 1;
    }
    try emitter.writeAll("            return 1u;\n        }\n");
    if (body.blocks.items.len > 0) {
        try emitter.writeAll("        goto _bb_0;\n");
    } else {
        try emitter.writeAll("        return 1u;\n");
    }
    for (plan.suspend_points) |sp_meta| {
        try emitter.print(
            "    case {d}u: goto _coro_disp_{d};\n",
            .{ sp_meta.state_tag, sp_meta.state_tag },
        );
    }
    try emitter.writeAll("    default: return 1u;\n    }\n");

    // [4] Per-suspend-point poll/cancel dispatch pads (`_coro_disp_<k>`):
    for (plan.suspend_points, 0..) |sp_meta, sp_idx| {
        const ready_ty = plan.suspend_ready_types[sp_idx];
        const resume_params = body.getBlockParams(sp_meta.resume_block);
        try emitter.print(
            "_coro_disp_{d}: ;\n" ++
                "    if (_action == 1u) {{\n" ++
                "        _cx_async_fut_cancel(_frame + {d}u);\n" ++
                "        goto _bb_{d};\n" ++
                "    }}\n",
            .{ sp_meta.state_tag, sp_meta.child_frame_offset, sp_meta.cancel_block.asInt() },
        );
        if (try isZeroSizedType(emitter, ready_ty)) {
            try emitter.print(
                "    if (_cx_async_fut_poll(_frame + {d}u, NULL, _parked_out) == 0u) return 0u;\n" ++
                    "    goto _bb_{d};\n",
                .{ sp_meta.child_frame_offset, sp_meta.resume_block.asInt() },
            );
        } else {
            const ready_c = try formatCType(emitter, ready_ty);
            defer emitter.allocator.free(ready_c);
            try emitter.print(
                "    {{ {s} _rval_{d}; memset(&_rval_{d}, 0, sizeof(_rval_{d}));\n" ++
                    "      if (_cx_async_fut_poll(_frame + {d}u, &_rval_{d}, _parked_out) == 0u) return 0u;\n",
                .{
                    ready_c,
                    sp_meta.state_tag,
                    sp_meta.state_tag,
                    sp_meta.state_tag,
                    sp_meta.child_frame_offset,
                    sp_meta.state_tag,
                },
            );
            if (resume_params.len >= 1 and !(try isZeroSizedType(emitter, body.getInst(resume_params[0]).type_id))) {
                try emitter.print("      _v_{d} = _rval_{d};\n", .{ resume_params[0].asInt(), sp_meta.state_tag });
            }
            try emitter.print("      goto _bb_{d}; }}\n", .{sp_meta.resume_block.asInt()});
        }
    }

    // [5] Basic blocks:
    for (body.blocks.items, 0..) |bb_rec, bb_i| {
        const bb_id = MirBlockId.fromInt(@intCast(bb_i));
        emitter.active_bb_id = bb_id;
        try emitter.print("_bb_{d}: ;\n", .{bb_i});
        for (body.getBlockInsts(bb_id)) |val_id| {
            const inst = body.getInst(val_id);
            if (inst.op.isGhost()) continue;
            if (val_id.asInt() < body.origin_tokens.items.len) {
                try maybeEmitLineDirective(emitter, body.file_id, body.origin_tokens.items[val_id.asInt()]);
            }
            try emitMirInstC(emitter, body_idx, body, val_id, inst);
        }
        try emitMirTerminatorC(emitter, body_idx, body, bb_id, bb_rec.terminator);
    }

    for (undef_macros.items) |macro_name| {
        try emitter.print("#undef {s}\n", .{macro_name});
    }
    try emitter.writeAll("}\n\n");
}

/// Emits C99 statements evaluating a single non-ghost `MirInst` into `_v_<val_id>`.
fn emitMirInstC(
    emitter: *CModuleEmitter,
    body_idx: u32,
    body: *const MirBody,
    val_id: MirValueId,
    inst: mir.MirInst,
) !void {
    const dst_raw = val_id.asInt();
    switch (inst.op) {
        .block_param,
        .ghost_access_let,
        .ghost_access_inout,
        .ghost_access_set,
        .ghost_access_end,
        .ghost_storage_init,
        .ghost_storage_move,
        .ghost_storage_deinit,
        => {},
        .const_scalar => {
            if (inst.operands.lhs >= body.consts.items.len) return;
            switch (body.consts.items[inst.operands.lhs]) {
                .unit_val => {},
                .bool_val => |b_flag| {
                    try emitter.print("    _v_{d} = {d}u;\n", .{ dst_raw, @intFromBool(b_flag) });
                },
                .char_val => |cp_val| {
                    try emitter.print("    _v_{d} = {d}u;\n", .{ dst_raw, @as(u32, cp_val) });
                },
                .int_val => |ival| {
                    if (try isZeroSizedType(emitter, inst.type_id)) return;
                    const u_bits: u128 = @bitCast(ival);
                    const info = (try resolveIntegerInfo(emitter, inst.type_id)) orelse return;
                    if (info.bits == 128) {
                        const lo_w: u64 = @truncate(u_bits);
                        const hi_w: u64 = @truncate(u_bits >> 64);
                        const fn_m = if (info.is_signed) "_cx_i128_make" else "_cx_u128_make";
                        try emitter.print("    _v_{d} = {s}({d}ull, {d}ull);\n", .{ dst_raw, fn_m, lo_w, hi_w });
                    } else {
                        const mask: u64 = if (info.bits >= 64)
                            std.math.maxInt(u64)
                        else
                            (@as(u64, 1) << @intCast(info.bits)) - 1;
                        const val_c = try formatCType(emitter, inst.type_id);
                        defer emitter.allocator.free(val_c);
                        const raw_u64: u64 = @as(u64, @truncate(u_bits)) & mask;
                        try emitter.print("    _v_{d} = ({s})({d}ull);\n", .{ dst_raw, val_c, raw_u64 });
                    }
                },
                .float_val => |fval| {
                    const unwrapped = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
                    if (unwrapped == .f32_ty) {
                        const f32_bits: u32 = @bitCast(@as(f32, @floatCast(fval)));
                        try emitter.print(
                            "    {{ uint32_t _fb = 0x{x:0>8}u; memcpy(&_v_{d}, &_fb, 4u); }}\n",
                            .{ f32_bits, dst_raw },
                        );
                    } else {
                        const f64_bits: u64 = @bitCast(fval);
                        try emitter.print(
                            "    {{ uint64_t _fb = 0x{x:0>16}ull; memcpy(&_v_{d}, &_fb, 8u); }}\n",
                            .{ f64_bits, dst_raw },
                        );
                    }
                },
                .str_val, .bytes_val => |sym_id| {
                    const bytes = emitter.input.interner.get(sym_id);
                    const unwrapped = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
                    if (resolveSliceRefPointee(emitter, unwrapped)) |sl_ty| {
                        const sl_c = try formatCType(emitter, sl_ty);
                        defer emitter.allocator.free(sl_c);
                        const dst_c = try formatCType(emitter, inst.type_id);
                        defer emitter.allocator.free(dst_c);
                        const tmp_id = emitter.nextTempId();
                        if (bytes.len == 0) {
                            try emitter.print(
                                "    {{ static const {s} _sref_{d} = {{ (uint8_t *)_cx_empty_rodata, 0u }}; " ++
                                    "_v_{d} = ({s})&_sref_{d}; }}\n",
                                .{ sl_c, tmp_id, dst_raw, dst_c, tmp_id },
                            );
                        } else {
                            try emitter.print(
                                "    {{ static const {s} _sref_{d} = {{ (uint8_t *)_cx_str_bytes_{d}, {d}u }}; " ++
                                    "_v_{d} = ({s})&_sref_{d}; }}\n",
                                .{ sl_c, tmp_id, sym_id.asInt(), bytes.len, dst_raw, dst_c, tmp_id },
                            );
                        }
                    } else if (unwrapped != .str_ty and emitter.input.pool.getNode(unwrapped).tag == .array_ty) {
                        if (bytes.len > 0) {
                            try emitter.print(
                                "    memcpy(&_v_{d}._elems[0], _cx_str_bytes_{d}, {d}u);\n",
                                .{ dst_raw, sym_id.asInt(), bytes.len },
                            );
                        }
                    } else if (unwrapped != .str_ty and !unwrapped.isPrimitiveOrSentinel() and
                        (emitter.input.pool.getNode(unwrapped).tag == .ref_ty or
                            emitter.input.pool.getNode(unwrapped).tag == .mut_ref_ty or
                            emitter.input.pool.getNode(unwrapped).tag == .raw_ptr_ty))
                    {
                        const dst_c = try formatCType(emitter, inst.type_id);
                        defer emitter.allocator.free(dst_c);
                        if (bytes.len == 0) {
                            try emitter.print(
                                "    _v_{d} = ({s})((const void *)_cx_empty_rodata);\n",
                                .{ dst_raw, dst_c },
                            );
                        } else {
                            try emitter.print(
                                "    _v_{d} = ({s})((const void *)_cx_str_bytes_{d});\n",
                                .{ dst_raw, dst_c, sym_id.asInt() },
                            );
                        }
                    } else {
                        if (bytes.len == 0) {
                            try emitter.print(
                                "    _v_{d}.ptr = (uint8_t *)_cx_empty_rodata; _v_{d}.len = 0u;\n",
                                .{ dst_raw, dst_raw },
                            );
                        } else {
                            try emitter.print(
                                "    _v_{d}.ptr = (uint8_t *)_cx_str_bytes_{d}; _v_{d}.len = {d}u;\n",
                                .{ dst_raw, sym_id.asInt(), dst_raw, bytes.len },
                            );
                        }
                    }
                },
                .raw_blob => |rb_const| {
                    const unwrapped_rb = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
                    if (resolveSliceRefPointee(emitter, unwrapped_rb)) |sl_ty| {
                        const sl_c = try formatCType(emitter, sl_ty);
                        defer emitter.allocator.free(sl_c);
                        try emitter.print(
                            "    _v_{d} = ({s} *)&_cx_blob_slice_{d};\n",
                            .{ dst_raw, sl_c, rb_const.blob_id },
                        );
                    } else if (unwrapped_rb != .str_ty and !unwrapped_rb.isPrimitiveOrSentinel() and
                        emitter.input.pool.getNode(unwrapped_rb).tag == .array_ty)
                    {
                        if (rb_const.byte_len > 0) {
                            try emitter.print(
                                "    memcpy(&_v_{d}._elems[0], _cx_blob_{d}, {d}u);\n",
                                .{ dst_raw, rb_const.blob_id, rb_const.byte_len },
                            );
                        }
                    } else if (unwrapped_rb != .str_ty and !unwrapped_rb.isPrimitiveOrSentinel() and
                        (emitter.input.pool.getNode(unwrapped_rb).tag == .ref_ty or
                            emitter.input.pool.getNode(unwrapped_rb).tag == .mut_ref_ty or
                            emitter.input.pool.getNode(unwrapped_rb).tag == .raw_ptr_ty))
                    {
                        const dst_c = try formatCType(emitter, inst.type_id);
                        defer emitter.allocator.free(dst_c);
                        if (rb_const.byte_len == 0) {
                            try emitter.print(
                                "    _v_{d} = ({s})((const void *)_cx_empty_rodata);\n",
                                .{ dst_raw, dst_c },
                            );
                        } else {
                            try emitter.print(
                                "    _v_{d} = ({s})((const void *)_cx_blob_{d});\n",
                                .{ dst_raw, dst_c, rb_const.blob_id },
                            );
                        }
                    } else if (rb_const.byte_len == 0) {
                        try emitter.print(
                            "    _v_{d}.ptr = (uint8_t *)((uintptr_t){d}u); _v_{d}.len = 0u;\n",
                            .{ dst_raw, @as(u32, 1) << @intCast(rb_const.align_log2), dst_raw },
                        );
                    } else {
                        try emitter.print(
                            "    _v_{d}.ptr = (uint8_t *)_cx_blob_{d}; _v_{d}.len = {d}u;\n",
                            .{ dst_raw, rb_const.blob_id, dst_raw, rb_const.byte_len },
                        );
                    }
                },
                .source_loc => |sloc| {
                    const sloc_key: u128 = (@as(u128, sloc.file_sym.asInt()) << 96) |
                        (@as(u128, sloc.fn_sym.asInt()) << 64) |
                        (@as(u128, sloc.line) << 32) |
                        @as(u128, sloc.col);
                    if (emitter.source_loc_map.get(sloc_key)) |loc_idx| {
                        try emitter.print("    _v_{d} = &_cx_loc_{d};\n", .{ dst_raw, loc_idx });
                    }
                },
            }
        },
        .copy_val => {
            if (!(try isZeroSizedType(emitter, inst.type_id))) {
                try emitter.print("    _v_{d} = _v_{d};\n", .{ dst_raw, inst.operands.lhs });
            }
        },
        .bin_op => {
            const bkind: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            try emitBinOpC(
                emitter,
                body,
                dst_raw,
                bkind,
                MirValueId.fromInt(inst.operands.lhs),
                MirValueId.fromInt(inst.operands.rhs),
                inst.type_id,
            );
        },
        .unary_op => {
            const ukind: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            try emitUnaryOpC(
                emitter,
                body,
                dst_raw,
                ukind,
                MirValueId.fromInt(inst.operands.lhs),
                inst.operands.rhs,
                inst.type_id,
            );
        },
        .aggregate_make => {
            const akind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            try emitAggregateMakeC(emitter, body_idx, body, dst_raw, akind, inst);
        },
        .aggregate_extract => {
            if (try isZeroSizedType(emitter, inst.type_id)) return;
            const agg_ty = emitter.input.pool.unwrapUnderlyingType(
                body.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id,
            );
            const agg_tag = emitter.input.pool.getNode(agg_ty).tag;
            if (agg_ty == .source_loc_ty) {
                const fld_name = switch (inst.operands.rhs) {
                    0 => "file",
                    1 => "fn_name",
                    2 => "line",
                    else => "col",
                };
                try emitter.print("    _v_{d} = _v_{d}->{s};\n", .{ dst_raw, inst.operands.lhs, fld_name });
            } else if (agg_ty == .str_ty or agg_tag == .slice_ty or agg_tag == .soa_slice_ty) {
                const dst_c = try formatCType(emitter, inst.type_id);
                defer emitter.allocator.free(dst_c);
                const slice_fld = if (inst.operands.rhs == 0) "ptr" else "len";
                try emitter.print(
                    "    _v_{d} = ({s})(_v_{d}.{s});\n",
                    .{ dst_raw, dst_c, inst.operands.lhs, slice_fld },
                );
            } else if (agg_tag == .array_ty) {
                try emitter.print(
                    "    _v_{d} = _v_{d}._elems[{d}u];\n",
                    .{ dst_raw, inst.operands.lhs, inst.operands.rhs },
                );
            } else {
                try emitter.print(
                    "    _v_{d} = _v_{d}._f{d};\n",
                    .{ dst_raw, inst.operands.lhs, inst.operands.rhs },
                );
            }
        },
        .aggregate_insert => {
            if (try isZeroSizedType(emitter, inst.type_id)) return;
            const ord = body.extra_args.items[inst.operands.rhs];
            const new_val = body.extra_args.items[inst.operands.rhs + 1];
            try emitter.print("    _v_{d} = _v_{d};\n", .{ dst_raw, inst.operands.lhs });
            const elem_ty = body.getInst(MirValueId.fromInt(new_val)).type_id;
            if (!(try isZeroSizedType(emitter, elem_ty))) {
                const agg_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
                const agg_tag = emitter.input.pool.getNode(agg_ty).tag;
                if (agg_ty == .str_ty or agg_tag == .slice_ty or agg_tag == .soa_slice_ty) {
                    if (ord == 0) {
                        try emitter.print(
                            "    memcpy(&(_v_{d}.ptr), &_v_{d}, sizeof(_v_{d}.ptr));\n",
                            .{ dst_raw, new_val, dst_raw },
                        );
                    } else {
                        try emitter.print("    _v_{d}.len = _v_{d};\n", .{ dst_raw, new_val });
                    }
                } else if (agg_tag == .array_ty) {
                    try emitter.print("    _v_{d}._elems[{d}u] = _v_{d};\n", .{ dst_raw, ord, new_val });
                } else {
                    try emitter.print("    _v_{d}._f{d} = _v_{d};\n", .{ dst_raw, ord, new_val });
                }
            }
        },
        .bitfield_extract => {
            const bspec = BitSpec.fromU32(inst.operands.rhs);
            const width: u16 = bspec.bit_width;
            const src_val = MirValueId.fromInt(inst.operands.lhs);
            const src_ty_raw = body.getInst(src_val).type_id;
            const dst_info = (try resolveIntegerInfo(emitter, inst.type_id)) orelse return;
            const width_mask: u128 = if (width >= 128) std.math.maxInt(u128) else (@as(u128, 1) << @intCast(width)) - 1;
            const mask_lo: u64 = @truncate(width_mask);
            const mask_hi: u64 = @truncate(width_mask >> 64);
            const tmp_id = emitter.nextTempId();

            if (try resolveIntegerInfo(emitter, src_ty_raw)) |src_info| {
                const src_u128_e = if (src_info.bits == 128)
                    try std.fmt.allocPrint(emitter.allocator, "_cx_as_u128(_v_{d})", .{src_val.asInt()})
                else
                    try std.fmt.allocPrint(
                        emitter.allocator,
                        "_cx_u128_make((uint64_t)(({s})_v_{d}), 0ull)",
                        .{ resolveUnsignedCTypeForBits(src_info.bits), src_val.asInt() },
                    );
                defer emitter.allocator.free(src_u128_e);

                if (bspec.bit_offset >= 128) {
                    try emitter.print("    cx_u128 _bf_{d} = _cx_u128_make(0ull, 0ull);\n", .{tmp_id});
                } else if (bspec.bit_offset == 0) {
                    try emitter.print(
                        "    cx_u128 _bf_{d} = _cx_u128_and({s}, _cx_u128_make({d}ull, {d}ull));\n",
                        .{ tmp_id, src_u128_e, mask_lo, mask_hi },
                    );
                } else {
                    try emitter.print(
                        "    cx_u128 _bf_{d} = _cx_u128_and(_cx_u128_lshr({s}, {d}u), _cx_u128_make({d}ull, {d}ull));\n",
                        .{ tmp_id, src_u128_e, bspec.bit_offset, mask_lo, mask_hi },
                    );
                }
            } else {
                var eff_src_ty = emitter.input.pool.unwrapUnderlyingType(src_ty_raw);
                if (!eff_src_ty.isPrimitiveOrSentinel() and emitter.input.pool.getNode(eff_src_ty).tag == .bit_field_ty) {
                    eff_src_ty = emitter.input.pool.unwrapUnderlyingType(
                        TypeId.fromInt(emitter.input.pool.getNode(eff_src_ty).lhs),
                    );
                }
                if (eff_src_ty.isPrimitiveOrSentinel() or emitter.input.pool.getNode(eff_src_ty).tag != .array_ty) return;
                const arr_len: u32 = emitter.input.pool.getNode(eff_src_ty).rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                const bit_start: u32 = bspec.fullBitOffset();
                const start_byte: u32 = bit_start / 8;
                const end_byte: u32 = @min((bit_start + @as(u32, width) + 7) / 8, arr_len);
                const span_len: usize = if (end_byte > start_byte) @intCast(end_byte - start_byte) else 0;
                const intra_bit: u8 = @intCast(bit_start % 8);
                try emitter.print("    cx_u128 _bf_{d} = _cx_u128_make(0ull, 0ull);\n", .{tmp_id});
                for (0..span_len) |byte_k| {
                    const byte_idx: u32 = start_byte + @as(u32, @intCast(byte_k));
                    if (byte_k == 0) {
                        try emitter.print(
                            "    _bf_{d} = _cx_u128_or(_bf_{d}, _cx_u128_make((uint64_t)(((uint8_t)_v_{d}._elems[{d}u]) >> {d}u), 0ull));\n",
                            .{ tmp_id, tmp_id, src_val.asInt(), byte_idx, intra_bit },
                        );
                    } else {
                        const shift_amt: usize = byte_k * 8 - intra_bit;
                        try emitter.print(
                            "    _bf_{d} = _cx_u128_or(_bf_{d}, _cx_u128_shl(" ++
                                "_cx_u128_make((uint64_t)((uint8_t)_v_{d}._elems[{d}u]), 0ull), {d}u));\n",
                            .{ tmp_id, tmp_id, src_val.asInt(), byte_idx, shift_amt },
                        );
                    }
                }
                try emitter.print(
                    "    _bf_{d} = _cx_u128_and(_bf_{d}, _cx_u128_make({d}ull, {d}ull));\n",
                    .{ tmp_id, tmp_id, mask_lo, mask_hi },
                );
            }
            if ((dst_info.is_signed or bspec.is_signed) and width > 0 and width < 128) {
                const sign_bit: u128 = @as(u128, 1) << @intCast(width - 1);
                const inv_mask: u128 = ~width_mask;
                try emitter.print(
                    "    {{ cx_u128 _sb = _cx_u128_and(_bf_{d}, _cx_u128_make({d}ull, {d}ull)); " ++
                        "if (_cx_u128_lo(_sb) != 0ull || _cx_u128_hi(_sb) != 0ull) " ++
                        "_bf_{d} = _cx_u128_or(_bf_{d}, _cx_u128_make({d}ull, {d}ull)); }}\n",
                    .{
                        tmp_id,
                        @as(u64, @truncate(sign_bit)),
                        @as(u64, @truncate(sign_bit >> 64)),
                        tmp_id,
                        tmp_id,
                        @as(u64, @truncate(inv_mask)),
                        @as(u64, @truncate(inv_mask >> 64)),
                    },
                );
            }
            if (dst_info.bits == 128) {
                if (dst_info.is_signed) {
                    try emitter.print("    _v_{d} = _cx_as_i128(_bf_{d});\n", .{ dst_raw, tmp_id });
                } else {
                    try emitter.print("    _v_{d} = _bf_{d};\n", .{ dst_raw, tmp_id });
                }
            } else if (emitter.input.pool.unwrapUnderlyingType(inst.type_id) == .bool_ty) {
                try emitter.print("    _v_{d} = (_cx_u128_lo(_bf_{d}) & 1ull) ? 1u : 0u;\n", .{ dst_raw, tmp_id });
            } else {
                const dst_c = try formatCType(emitter, inst.type_id);
                defer emitter.allocator.free(dst_c);
                try emitter.print("    _v_{d} = ({s})_cx_u128_lo(_bf_{d});\n", .{ dst_raw, dst_c, tmp_id });
            }
        },
        .bitfield_insert => {
            const bspec = BitSpec.fromU32(inst.operands.rhs);
            const width: u16 = bspec.bit_width;
            const base_val = MirValueId.fromInt(body.extra_args.items[inst.operands.lhs]);
            const ins_val = MirValueId.fromInt(body.extra_args.items[inst.operands.lhs + 1]);
            const width_mask: u128 = if (width >= 128) std.math.maxInt(u128) else (@as(u128, 1) << @intCast(width)) - 1;
            const dst_info = (try resolveIntegerInfo(emitter, inst.type_id)) orelse {
                var eff_dst_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
                if (!eff_dst_ty.isPrimitiveOrSentinel() and emitter.input.pool.getNode(eff_dst_ty).tag == .bit_field_ty) {
                    eff_dst_ty = emitter.input.pool.unwrapUnderlyingType(
                        TypeId.fromInt(emitter.input.pool.getNode(eff_dst_ty).lhs),
                    );
                }
                if (eff_dst_ty.isPrimitiveOrSentinel() or emitter.input.pool.getNode(eff_dst_ty).tag != .array_ty) return;
                const ins_arr_info = (try resolveIntegerInfo(emitter, body.getInst(ins_val).type_id)) orelse return;
                const ins_arr_u128 = if (ins_arr_info.bits == 128)
                    try std.fmt.allocPrint(emitter.allocator, "_cx_as_u128(_v_{d})", .{ins_val.asInt()})
                else
                    try std.fmt.allocPrint(
                        emitter.allocator,
                        "_cx_u128_make((uint64_t)(({s})_v_{d}), 0ull)",
                        .{ resolveUnsignedCTypeForBits(ins_arr_info.bits), ins_val.asInt() },
                    );
                defer emitter.allocator.free(ins_arr_u128);
                const tmp_arr_id = emitter.nextTempId();
                try emitter.print(
                    "    cx_u128 _bi_{d} = _cx_u128_and({s}, _cx_u128_make({d}ull, {d}ull));\n" ++
                        "    _v_{d} = _v_{d};\n",
                    .{
                        tmp_arr_id,
                        ins_arr_u128,
                        @as(u64, @truncate(width_mask)),
                        @as(u64, @truncate(width_mask >> 64)),
                        dst_raw,
                        base_val.asInt(),
                    },
                );
                const arr_len: u32 = emitter.input.pool.getNode(eff_dst_ty).rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                const bit_start: u32 = bspec.fullBitOffset();
                const bit_end: u32 = bit_start + @as(u32, width);
                const start_byte: u32 = bit_start / 8;
                const end_byte: u32 = @min((bit_end + 7) / 8, arr_len);
                const span_len: usize = if (end_byte > start_byte) @intCast(end_byte - start_byte) else 0;
                for (0..span_len) |byte_k| {
                    const byte_idx: u32 = start_byte + @as(u32, @intCast(byte_k));
                    const bit_lo: u8 = if (bit_start > byte_idx * 8) @intCast(bit_start - byte_idx * 8) else 0;
                    const bit_hi: u8 = if (bit_end < byte_idx * 8 + 8) @intCast(bit_end - byte_idx * 8) else 8;
                    const byte_mask: u8 = @intCast(((@as(u16, 1) << @intCast(bit_hi - bit_lo)) - 1) << @intCast(bit_lo));
                    const clr_byte_mask: u8 = ~byte_mask;
                    const ins_shift: u32 = (byte_idx * 8 + bit_lo) - bit_start;
                    const shifted_lo = if (ins_shift == 0)
                        try std.fmt.allocPrint(emitter.allocator, "_cx_u128_lo(_bi_{d})", .{tmp_arr_id})
                    else
                        try std.fmt.allocPrint(
                            emitter.allocator,
                            "_cx_u128_lo(_cx_u128_lshr(_bi_{d}, {d}u))",
                            .{ tmp_arr_id, ins_shift },
                        );
                    defer emitter.allocator.free(shifted_lo);
                    try emitter.print(
                        "    _v_{d}._elems[{d}u] = (uint8_t)(((uint8_t)(_v_{d}._elems[{d}u] & {d}u)) | " ++
                            "((uint8_t)((((uint8_t)({s})) << {d}u) & {d}u)));\n",
                        .{ dst_raw, byte_idx, dst_raw, byte_idx, clr_byte_mask, shifted_lo, bit_lo, byte_mask },
                    );
                }
                return;
            };
            const ins_info = (try resolveIntegerInfo(emitter, body.getInst(ins_val).type_id)) orelse dst_info;
            const base_u128_e = if (dst_info.bits == 128)
                try std.fmt.allocPrint(emitter.allocator, "_cx_as_u128(_v_{d})", .{base_val.asInt()})
            else
                try std.fmt.allocPrint(
                    emitter.allocator,
                    "_cx_u128_make((uint64_t)(({s})_v_{d}), 0ull)",
                    .{ resolveUnsignedCTypeForBits(dst_info.bits), base_val.asInt() },
                );
            defer emitter.allocator.free(base_u128_e);
            const ins_u128_e = if (ins_info.bits == 128)
                try std.fmt.allocPrint(emitter.allocator, "_cx_as_u128(_v_{d})", .{ins_val.asInt()})
            else
                try std.fmt.allocPrint(
                    emitter.allocator,
                    "_cx_u128_make((uint64_t)(({s})_v_{d}), 0ull)",
                    .{ resolveUnsignedCTypeForBits(ins_info.bits), ins_val.asInt() },
                );
            defer emitter.allocator.free(ins_u128_e);

            const shifted_mask: u128 = if (bspec.bit_offset >= 128) 0 else width_mask << @intCast(bspec.bit_offset);
            const clear_mask: u128 = ~shifted_mask;
            const tmp_id = emitter.nextTempId();
            if (bspec.bit_offset >= 128) {
                try emitter.print("    cx_u128 _bi_{d} = {s};\n", .{ tmp_id, base_u128_e });
            } else {
                const masked_ins_e = try std.fmt.allocPrint(
                    emitter.allocator,
                    "_cx_u128_and({s}, _cx_u128_make({d}ull, {d}ull))",
                    .{ ins_u128_e, @as(u64, @truncate(width_mask)), @as(u64, @truncate(width_mask >> 64)) },
                );
                defer emitter.allocator.free(masked_ins_e);
                const placed_e = if (bspec.bit_offset == 0)
                    try emitter.allocator.dupe(u8, masked_ins_e)
                else
                    try std.fmt.allocPrint(emitter.allocator, "_cx_u128_shl({s}, {d}u)", .{ masked_ins_e, bspec.bit_offset });
                defer emitter.allocator.free(placed_e);
                try emitter.print(
                    "    cx_u128 _bi_{d} = _cx_u128_or(_cx_u128_and({s}, _cx_u128_make({d}ull, {d}ull)), {s});\n",
                    .{
                        tmp_id,
                        base_u128_e,
                        @as(u64, @truncate(clear_mask)),
                        @as(u64, @truncate(clear_mask >> 64)),
                        placed_e,
                    },
                );
            }
            if (dst_info.bits == 128) {
                if (dst_info.is_signed) {
                    try emitter.print("    _v_{d} = _cx_as_i128(_bi_{d});\n", .{ dst_raw, tmp_id });
                } else {
                    try emitter.print("    _v_{d} = _bi_{d};\n", .{ dst_raw, tmp_id });
                }
            } else {
                const dst_c = try formatCType(emitter, inst.type_id);
                defer emitter.allocator.free(dst_c);
                try emitter.print("    _v_{d} = ({s})_cx_u128_lo(_bi_{d});\n", .{ dst_raw, dst_c, tmp_id });
            }
        },
        .fn_addr => {
            const target_def = DefId.fromInt(inst.operands.lhs);
            const target_sym = SymbolIndex.fromInt(inst.operands.rhs);
            const fn_c = try formatCType(emitter, inst.type_id);
            defer emitter.allocator.free(fn_c);
            if (resolveBodyIndex(emitter, target_def, target_sym)) |b_target| {
                if (emitter.input.is_dev_got_enabled) {
                    try emitter.print(
                        "    _v_{d} = ({s})_cx_dev_got[{d}u];\n",
                        .{ dst_raw, fn_c, b_target },
                    );
                } else {
                    try emitter.print(
                        "    _v_{d} = ({s}){s};\n",
                        .{ dst_raw, fn_c, emitter.body_c_names.items[b_target] },
                    );
                }
            } else if (!target_sym.isNone() and
                target_sym.asInt() < emitter.input.sym_table.symbols.items.len)
            {
                if (emitter.extern_global_sym_set.contains(target_sym.asInt())) {
                    const glob_rec = emitter.input.sym_table.getSymbol(target_sym).*;
                    const sym_ty = emitter.input.pool.unwrapUnderlyingType(glob_rec.type_id);
                    const inst_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
                    if (inst_ty == sym_ty) {
                        if (!(try isZeroSizedType(emitter, inst.type_id))) {
                            try emitter.print("    _v_{d} = _cx_ext_glob_{d};\n", .{ dst_raw, target_sym.asInt() });
                        }
                    } else {
                        try emitter.print(
                            "    _v_{d} = ({s})(&_cx_ext_glob_{d});\n",
                            .{ dst_raw, fn_c, target_sym.asInt() },
                        );
                    }
                } else {
                    try emitter.print("    _v_{d} = ({s})_cx_ext_{d};\n", .{ dst_raw, fn_c, target_sym.asInt() });
                }
            }
        },
        .place_load => {
            if (try isZeroSizedType(emitter, inst.type_id)) return;
            switch (try lowerPlaceC(emitter, body, PlaceId.fromInt(inst.operands.lhs))) {
                .const_len => |clen| {
                    const dst_c = try formatCType(emitter, inst.type_id);
                    defer emitter.allocator.free(dst_c);
                    try emitter.print("    _v_{d} = ({s}){d}u;\n", .{ dst_raw, dst_c, clen });
                },
                .lvalue_expr => |lv| {
                    defer emitter.allocator.free(lv.expr_str);
                    try emitter.print("    _v_{d} = {s};\n", .{ dst_raw, lv.expr_str });
                },
            }
        },
        .place_store => {
            const rhs_val = MirValueId.fromInt(inst.operands.rhs);
            if (try isZeroSizedType(emitter, body.getInst(rhs_val).type_id)) return;
            switch (try lowerPlaceC(emitter, body, PlaceId.fromInt(inst.operands.lhs))) {
                .const_len => {},
                .lvalue_expr => |lv| {
                    defer emitter.allocator.free(lv.expr_str);
                    try emitter.print("    {s} = _v_{d};\n", .{ lv.expr_str, rhs_val.asInt() });
                },
            }
        },
        .place_discriminant => {
            switch (try lowerPlaceC(emitter, body, PlaceId.fromInt(inst.operands.lhs))) {
                .const_len => {},
                .lvalue_expr => |lv| {
                    defer emitter.allocator.free(lv.expr_str);
                    const dst_c = try formatCType(emitter, inst.type_id);
                    defer emitter.allocator.free(dst_c);
                    if (try emitter.resolver.getSumDetail(lv.pointee_ty)) |sum_detail| {
                        const d_expr = try formatSumDiscrReadExpr(emitter, lv.pointee_ty, sum_detail, lv.expr_str);
                        defer emitter.allocator.free(d_expr);
                        try emitter.print("    _v_{d} = ({s})({s});\n", .{ dst_raw, dst_c, d_expr });
                    } else if (!lv.pointee_ty.isPrimitiveOrSentinel() and
                        emitter.input.pool.getNode(lv.pointee_ty).tag == .enum_ty)
                    {
                        try emitScalarEnumOrdinalReadC(emitter, lv.pointee_ty, lv.expr_str, dst_raw, dst_c);
                    } else {
                        try emitter.print("    _v_{d} = ({s})({s});\n", .{ dst_raw, dst_c, lv.expr_str });
                    }
                },
            }
        },
        .place_set_discrim => {
            switch (try lowerPlaceC(emitter, body, PlaceId.fromInt(inst.operands.lhs))) {
                .const_len => {},
                .lvalue_expr => |lv| {
                    defer emitter.allocator.free(lv.expr_str);
                    if (!(try isZeroSizedType(emitter, lv.pointee_ty))) {
                        if ((try emitter.resolver.getSumDetail(lv.pointee_ty)) != null) {
                            try emitSumDiscrWriteStmt(emitter, lv.pointee_ty, inst.operands.rhs, lv.expr_str);
                        } else if (!lv.pointee_ty.isPrimitiveOrSentinel() and
                            emitter.input.pool.getNode(lv.pointee_ty).tag == .enum_ty)
                        {
                            try emitScalarEnumDiscrimWriteC(emitter, lv.pointee_ty, inst.operands.rhs, lv.expr_str);
                        }
                    }
                },
            }
        },
        .place_addr => {
            switch (try lowerPlaceC(emitter, body, PlaceId.fromInt(inst.operands.lhs))) {
                .const_len => {},
                .lvalue_expr => |lv| {
                    defer emitter.allocator.free(lv.expr_str);
                    const p_node = emitter.input.pool.getNode(lv.pointee_ty);
                    const dst_unwrapped = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
                    const dst_node = emitter.input.pool.getNode(dst_unwrapped);

                    // Array-to-slice coercion (`&[T; N]` -> `[T]` or `&[T]`):
                    if ((p_node.tag == .array_ty or p_node.tag == .soa_array_ty) and
                        (dst_node.tag == .slice_ty or dst_node.tag == .soa_slice_ty))
                    {
                        try emitArrayLvalueToSliceValueC(
                            emitter,
                            lv.expr_str,
                            lv.pointee_ty,
                            dst_unwrapped,
                            dst_raw,
                            false,
                        );
                    } else if ((p_node.tag == .array_ty or p_node.tag == .soa_array_ty) and
                        resolveSliceRefPointee(emitter, dst_unwrapped) != null)
                    {
                        const sl_ty = resolveSliceRefPointee(emitter, dst_unwrapped).?;
                        try emitArrayLvalueToSliceValueC(
                            emitter,
                            lv.expr_str,
                            lv.pointee_ty,
                            sl_ty,
                            dst_raw,
                            true,
                        );
                    } else if (try isZeroSizedType(emitter, lv.pointee_ty)) {
                        const p_lay = try emitter.resolver.resolveType(lv.pointee_ty);
                        try emitter.print(
                            "    _v_{d} = (uint8_t *)((uintptr_t){d}u);\n",
                            .{ dst_raw, p_lay.alignBytes() },
                        );
                    } else {
                        const dst_c = try formatCType(emitter, inst.type_id);
                        defer emitter.allocator.free(dst_c);
                        try emitter.print("    _v_{d} = ({s})(&({s}));\n", .{ dst_raw, dst_c, lv.expr_str });
                    }
                },
            }
        },
        .soa_column_slice => {
            switch (try lowerPlaceC(emitter, body, PlaceId.fromInt(inst.operands.lhs))) {
                .const_len => {},
                .lvalue_expr => |lv| {
                    defer emitter.allocator.free(lv.expr_str);
                    const base_node = emitter.input.pool.getNode(lv.pointee_ty);
                    const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(base_node.lhs));
                    const fld = (try emitter.resolver.getFieldByDeclOrdinal(elem_struct, inst.operands.rhs)).?;
                    const fld_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                    const fld_lay = try emitter.resolver.resolveType(fld_ty);
                    const fld_c = if (try isZeroSizedType(emitter, fld_ty))
                        try emitter.allocator.dupe(u8, "uint8_t")
                    else
                        try formatCType(emitter, fld_ty);
                    defer emitter.allocator.free(fld_c);

                    if (base_node.tag == .soa_array_ty) {
                        const cap: u64 = base_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                        if (cap == 0) {
                            try emitter.print(
                                "    _v_{d}.ptr = ({s} *)((uintptr_t){d}u); _v_{d}.len = 0u;\n",
                                .{ dst_raw, fld_c, fld_lay.alignBytes(), dst_raw },
                            );
                        } else {
                            const col = emitter.resolver.getSoaColumnOffset(elem_struct, inst.operands.rhs, cap).?;
                            try emitter.print(
                                "    _v_{d}.ptr = ({s} *)(&({s})._bytes[{d}u]); _v_{d}.len = {d}u;\n",
                                .{ dst_raw, fld_c, lv.expr_str, col.byte_offset, dst_raw, cap },
                            );
                        }
                    } else {
                        const len_str = try std.fmt.allocPrint(emitter.allocator, "(({s}).len)", .{lv.expr_str});
                        defer emitter.allocator.free(len_str);
                        const off_str = try formatDynamicSoaColOffsetExpr(
                            emitter,
                            elem_struct,
                            inst.operands.rhs,
                            len_str,
                        );
                        defer emitter.allocator.free(off_str);
                        try emitter.print(
                            "    if ({s} == 0u) {{ _v_{d}.ptr = ({s} *)((uintptr_t){d}u); _v_{d}.len = 0u; }} " ++
                                "else {{ _v_{d}.ptr = ({s} *)((({s}).ptr) + {s}); _v_{d}.len = {s}; }}\n",
                            .{
                                len_str,
                                dst_raw,
                                fld_c,
                                fld_lay.alignBytes(),
                                dst_raw,
                                dst_raw,
                                fld_c,
                                lv.expr_str,
                                off_str,
                                dst_raw,
                                len_str,
                            },
                        );
                    }
                },
            }
        },
        .intrinsic_op => {
            const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
            try emitIntrinsicOpC(emitter, body, dst_raw, ikind, inst);
        },
    }
}

/// Materializes `[T]` or `&[T]` from an array lvalue `arr_expr`, preserving non-null dangling pointers on `N == 0`.
fn emitArrayLvalueToSliceValueC(
    emitter: *CModuleEmitter,
    arr_expr: []const u8,
    arr_ty: TypeId,
    slice_ty: TypeId,
    dst_raw: u32,
    is_via_stmp_ref: bool,
) !void {
    const arr_node = emitter.input.pool.getNode(arr_ty);
    const arr_len: u64 = arr_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
    const elem_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(arr_node.lhs));
    const elem_lay = try emitter.resolver.resolveType(elem_ty);
    const sl_node = emitter.input.pool.getNode(slice_ty);
    const ptr_c = if (sl_node.tag == .soa_slice_ty or (try isZeroSizedType(emitter, elem_ty)))
        try emitter.allocator.dupe(u8, "uint8_t")
    else
        try formatCType(emitter, elem_ty);
    defer emitter.allocator.free(ptr_c);

    const dst_prefix = if (is_via_stmp_ref) "_stmp_" else "_v_";
    if (arr_len == 0 or (try isZeroSizedType(emitter, arr_ty))) {
        const align_b = if (arr_node.tag == .soa_array_ty)
            (@as(u32, 1) << @intCast(@max(elem_lay.align_log2, emitter.target_layout.simd_align_log2)))
        else
            elem_lay.alignBytes();
        try emitter.print(
            "    {s}{d}.ptr = ({s} *)((uintptr_t){d}u); {s}{d}.len = {d}u;\n",
            .{ dst_prefix, dst_raw, ptr_c, align_b, dst_prefix, dst_raw, arr_len },
        );
    } else if (arr_node.tag == .soa_array_ty) {
        try emitter.print(
            "    {s}{d}.ptr = (uint8_t *)(&({s})._bytes[0]); {s}{d}.len = {d}u;\n",
            .{ dst_prefix, dst_raw, arr_expr, dst_prefix, dst_raw, arr_len },
        );
    } else {
        try emitter.print(
            "    {s}{d}.ptr = ({s} *)(&({s})._elems[0]); {s}{d}.len = {d}u;\n",
            .{ dst_prefix, dst_raw, ptr_c, arr_expr, dst_prefix, dst_raw, arr_len },
        );
    }
    if (is_via_stmp_ref) {
        try emitter.print("    _v_{d} = &_stmp_{d};\n", .{ dst_raw, dst_raw });
    }
}

/// Formats a UB-free C99 boolean (`1u` / `0u`) equality expression for aligned local variables `(lhs_var, rhs_var)`.
fn formatAlignedVarEqExprC(
    emitter: *CModuleEmitter,
    raw_ty: TypeId,
    lhs_var: []const u8,
    rhs_var: []const u8,
) anyerror![]u8 {
    var ty = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (!ty.isPrimitiveOrSentinel() and emitter.input.pool.getNode(ty).tag == .bit_field_ty) {
        ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(emitter.input.pool.getNode(ty).lhs));
    }
    if (try isZeroSizedType(emitter, ty)) return emitter.allocator.dupe(u8, "1u");

    if (ty == .bool_ty) {
        return std.fmt.allocPrint(
            emitter.allocator,
            "(((((uint8_t)({s})) & 1u) == (((uint8_t)({s})) & 1u)) ? 1u : 0u)",
            .{ lhs_var, rhs_var },
        );
    }
    if (ty == .str_ty) {
        return std.fmt.allocPrint(
            emitter.allocator,
            "_cx_str_eq(({s}).ptr, (size_t)({s}).len, ({s}).ptr, (size_t)({s}).len)",
            .{ lhs_var, lhs_var, rhs_var, rhs_var },
        );
    }
    if (ty == .source_loc_ty) {
        return std.fmt.allocPrint(emitter.allocator, "_cx_source_loc_eq({s}, {s})", .{ lhs_var, rhs_var });
    }
    if (ty == .fmt_spec_ty) {
        return std.fmt.allocPrint(emitter.allocator, "_cx_fmt_spec_eq({s}, {s})", .{ lhs_var, rhs_var });
    }
    if (ty == .task_group_base_ty or
        ty == .task_handle_base_ty or
        emitter.input.pool.isTaskGroupType(ty) or
        emitter.input.pool.isTaskHandleType(ty))
    {
        return std.fmt.allocPrint(
            emitter.allocator,
            "(((uintptr_t)({s}) == (uintptr_t)({s})) ? 1u : 0u)",
            .{ lhs_var, rhs_var },
        );
    }
    if (ty == .f32_ty or ty == .f64_ty or ty == .untyped_float_ty) {
        return std.fmt.allocPrint(emitter.allocator, "((({s}) == ({s})) ? 1u : 0u)", .{ lhs_var, rhs_var });
    }
    if (try resolveIntegerInfo(emitter, ty)) |int_info| {
        if (int_info.bits == 128) {
            return std.fmt.allocPrint(
                emitter.allocator,
                "_cx_u128_eq(_cx_as_u128({s}), _cx_as_u128({s}))",
                .{ lhs_var, rhs_var },
            );
        }
        return std.fmt.allocPrint(emitter.allocator, "((({s}) == ({s})) ? 1u : 0u)", .{ lhs_var, rhs_var });
    }
    if (ty.isPrimitiveOrSentinel()) return emitter.allocator.dupe(u8, "0u");

    const node = emitter.input.pool.getNode(ty);
    return switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .fn_ty => std.fmt.allocPrint(
            emitter.allocator,
            "(((uintptr_t)({s}) == (uintptr_t)({s})) ? 1u : 0u)",
            .{ lhs_var, rhs_var },
        ),
        .struct_ty,
        .tuple_ty,
        .array_ty,
        .slice_ty,
        .soa_array_ty,
        .soa_slice_ty,
        .optional_ty,
        .result_ty,
        .enum_ty,
        => if (emitter.eq_type_set.contains(ty.toU32()))
            std.fmt.allocPrint(emitter.allocator, "_cx_eq_ty_{d}(&({s}), &({s}))", .{ ty.toU32(), lhs_var, rhs_var })
        else
            emitter.allocator.dupe(u8, "0u"),
        else => emitter.allocator.dupe(u8, "0u"),
    };
}

/// Emits UB-free C99 binary arithmetic, shift, bitwise, and relational operations into `_v_<dst_raw>`.
fn emitBinOpC(
    emitter: *CModuleEmitter,
    body: *const MirBody,
    dst_raw: u32,
    kind: BinOpKind,
    lhs_val: MirValueId,
    rhs_val: MirValueId,
    res_ty: TypeId,
) !void {
    const l_raw = lhs_val.asInt();
    const r_raw = rhs_val.asInt();
    const op_ty = emitter.input.pool.unwrapUnderlyingType(body.getInst(lhs_val).type_id);

    if ((kind == .eq or kind == .ne) and (try isZeroSizedType(emitter, op_ty))) {
        try emitter.print("    _v_{d} = {d}u;\n", .{ dst_raw, @as(u8, if (kind == .eq) 1 else 0) });
        return;
    }

    if (op_ty == .str_ty and (kind == .eq or kind == .ne)) {
        const xor_mask: u8 = if (kind == .ne) 1 else 0;
        try emitter.print(
            "    _v_{d} = _cx_str_eq(_v_{d}.ptr, (size_t)_v_{d}.len, _v_{d}.ptr, (size_t)_v_{d}.len) ^ {d}u;\n",
            .{ dst_raw, l_raw, l_raw, r_raw, r_raw, xor_mask },
        );
        return;
    }

    if (op_ty == .f32_ty or op_ty == .f64_ty or op_ty == .untyped_float_ty) {
        switch (kind) {
            .fadd => try emitter.print("    _v_{d} = _v_{d} + _v_{d};\n", .{ dst_raw, l_raw, r_raw }),
            .fsub => try emitter.print("    _v_{d} = _v_{d} - _v_{d};\n", .{ dst_raw, l_raw, r_raw }),
            .fmul => try emitter.print("    _v_{d} = _v_{d} * _v_{d};\n", .{ dst_raw, l_raw, r_raw }),
            .fdiv => try emitter.print("    _v_{d} = _v_{d} / _v_{d};\n", .{ dst_raw, l_raw, r_raw }),
            .frem => {
                const fn_rem = if (op_ty == .f32_ty) "fmodf" else "fmod";
                try emitter.print("    _v_{d} = {s}(_v_{d}, _v_{d});\n", .{ dst_raw, fn_rem, l_raw, r_raw });
            },
            .eq => try emitter.print("    _v_{d} = (_v_{d} == _v_{d}) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            .ne => try emitter.print("    _v_{d} = (_v_{d} != _v_{d}) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            .flt => try emitter.print("    _v_{d} = (_v_{d} < _v_{d}) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            .fle => try emitter.print("    _v_{d} = (_v_{d} <= _v_{d}) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            .fgt => try emitter.print("    _v_{d} = (_v_{d} > _v_{d}) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            .fge => try emitter.print("    _v_{d} = (_v_{d} >= _v_{d}) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            else => {},
        }
        return;
    }

    if (!op_ty.isPrimitiveOrSentinel()) {
        const op_tag = emitter.input.pool.getNode(op_ty).tag;
        if (op_tag == .ref_ty or op_tag == .mut_ref_ty or op_tag == .raw_ptr_ty or op_tag == .fn_ty) {
            const cmp_op = switch (kind) {
                .eq => "==",
                .ne => "!=",
                .ult, .slt => "<",
                .ule, .sle => "<=",
                .ugt, .sgt => ">",
                .uge, .sge => ">=",
                else => "==",
            };
            try emitter.print(
                "    _v_{d} = ((uintptr_t)_v_{d} {s} (uintptr_t)_v_{d}) ? 1u : 0u;\n",
                .{ dst_raw, l_raw, cmp_op, r_raw },
            );
            return;
        }
    }

    const info = (try resolveIntegerInfo(emitter, op_ty)) orelse {
        if (kind == .eq or kind == .ne) {
            const l_lv = try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{l_raw});
            defer emitter.allocator.free(l_lv);
            const r_lv = try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{r_raw});
            defer emitter.allocator.free(r_lv);
            const eq_expr = try formatAlignedVarEqExprC(emitter, op_ty, l_lv, r_lv);
            defer emitter.allocator.free(eq_expr);
            const xor_mask: u8 = if (kind == .ne) 1 else 0;
            try emitter.print("    _v_{d} = ({s}) ^ {d}u;\n", .{ dst_raw, eq_expr, xor_mask });
        }
        return;
    };
    if (info.bits == 128) {
        try emitInt128BinOpC(emitter, body, dst_raw, kind, l_raw, r_raw, rhs_val);
        return;
    }

    if (info.bits == 1) {
        switch (kind) {
            .bit_and => try emitter.print("    _v_{d} = (_v_{d} & _v_{d}) & 1u;\n", .{ dst_raw, l_raw, r_raw }),
            .bit_or => try emitter.print("    _v_{d} = (_v_{d} | _v_{d}) & 1u;\n", .{ dst_raw, l_raw, r_raw }),
            .bit_xor => try emitter.print("    _v_{d} = (_v_{d} ^ _v_{d}) & 1u;\n", .{ dst_raw, l_raw, r_raw }),
            .eq => try emitter.print("    _v_{d} = ((_v_{d} & 1u) == (_v_{d} & 1u)) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            .ne => try emitter.print("    _v_{d} = ((_v_{d} & 1u) != (_v_{d} & 1u)) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            .ult, .slt => try emitter.print("    _v_{d} = ((_v_{d} & 1u) < (_v_{d} & 1u)) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            .ule, .sle => try emitter.print("    _v_{d} = ((_v_{d} & 1u) <= (_v_{d} & 1u)) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            .ugt, .sgt => try emitter.print("    _v_{d} = ((_v_{d} & 1u) > (_v_{d} & 1u)) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            .uge, .sge => try emitter.print("    _v_{d} = ((_v_{d} & 1u) >= (_v_{d} & 1u)) ? 1u : 0u;\n", .{ dst_raw, l_raw, r_raw }),
            else => {},
        }
        return;
    }

    const u_c = resolveUnsignedCTypeForBits(info.bits);
    const s_c = resolveSignedCTypeForBits(info.bits);
    const dst_c = try formatCType(emitter, res_ty);
    defer emitter.allocator.free(dst_c);
    const min_s_bits: u64 = @as(u64, 1) << @intCast(info.bits - 1);
    const max_s_bits: u64 = min_s_bits - 1;
    const max_u_bits: u64 = if (info.bits >= 64) std.math.maxInt(u64) else (@as(u64, 1) << @intCast(info.bits)) - 1;

    switch (kind) {
        .sadd_checked => try emitter.print(
            "    {{ {s} _ov = 0; if (__builtin_add_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) _cx_rt_trap(2); _v_{d} = ({s})_ov; }}\n",
            .{ s_c, s_c, l_raw, s_c, r_raw, dst_raw, dst_c },
        ),
        .uadd_checked => try emitter.print(
            "    {{ {s} _ov = 0u; if (__builtin_add_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) _cx_rt_trap(2); _v_{d} = ({s})_ov; }}\n",
            .{ u_c, u_c, l_raw, u_c, r_raw, dst_raw, dst_c },
        ),
        .ssub_checked => try emitter.print(
            "    {{ {s} _ov = 0; if (__builtin_sub_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) _cx_rt_trap(2); _v_{d} = ({s})_ov; }}\n",
            .{ s_c, s_c, l_raw, s_c, r_raw, dst_raw, dst_c },
        ),
        .usub_checked => try emitter.print(
            "    {{ {s} _ov = 0u; if (__builtin_sub_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) _cx_rt_trap(2); _v_{d} = ({s})_ov; }}\n",
            .{ u_c, u_c, l_raw, u_c, r_raw, dst_raw, dst_c },
        ),
        .smul_checked => try emitter.print(
            "    {{ {s} _ov = 0; if (__builtin_mul_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) _cx_rt_trap(2); _v_{d} = ({s})_ov; }}\n",
            .{ s_c, s_c, l_raw, s_c, r_raw, dst_raw, dst_c },
        ),
        .umul_checked => try emitter.print(
            "    {{ {s} _ov = 0u; if (__builtin_mul_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) _cx_rt_trap(2); _v_{d} = ({s})_ov; }}\n",
            .{ u_c, u_c, l_raw, u_c, r_raw, dst_raw, dst_c },
        ),
        .sdiv_checked => try emitter.print(
            "    if (_v_{d} == 0 || (({s})_v_{d} == ({s}){d}ull && ({s})_v_{d} == ({s})(-1))) _cx_rt_trap(2); " ++
                "_v_{d} = ({s})((({s})_v_{d}) / (({s})_v_{d}));\n",
            .{ r_raw, u_c, l_raw, u_c, min_s_bits, s_c, r_raw, s_c, dst_raw, dst_c, s_c, l_raw, s_c, r_raw },
        ),
        .udiv_checked => try emitter.print(
            "    if (_v_{d} == 0u) _cx_rt_trap(2); _v_{d} = ({s})((({s})_v_{d}) / (({s})_v_{d}));\n",
            .{ r_raw, dst_raw, dst_c, u_c, l_raw, u_c, r_raw },
        ),
        .srem_checked => try emitter.print(
            "    if (_v_{d} == 0 || (({s})_v_{d} == ({s}){d}ull && ({s})_v_{d} == ({s})(-1))) _cx_rt_trap(2); " ++
                "_v_{d} = ({s})((({s})_v_{d}) % (({s})_v_{d}));\n",
            .{ r_raw, u_c, l_raw, u_c, min_s_bits, s_c, r_raw, s_c, dst_raw, dst_c, s_c, l_raw, s_c, r_raw },
        ),
        .urem_checked => try emitter.print(
            "    if (_v_{d} == 0u) _cx_rt_trap(2); _v_{d} = ({s})((({s})_v_{d}) % (({s})_v_{d}));\n",
            .{ r_raw, dst_raw, dst_c, u_c, l_raw, u_c, r_raw },
        ),
        .shl_checked, .ashr_checked, .lshr_checked => {
            const rhs_u128_e = try formatIntAsCxU128Expr(emitter, rhs_val, body.getInst(rhs_val).type_id);
            defer emitter.allocator.free(rhs_u128_e);
            const tmp_id = emitter.nextTempId();
            const lhs_c = if (kind == .ashr_checked) s_c else u_c;
            const sh_tok = if (kind == .shl_checked) "<<" else ">>";
            try emitter.print(
                "    {{ cx_u128 _sr_{d} = {s}; if (_cx_u128_hi(_sr_{d}) != 0ull || _cx_u128_lo(_sr_{d}) >= {d}ull) " ++
                    "_cx_rt_trap(2); _v_{d} = ({s})((({s})_v_{d}) {s} ((uint32_t)_cx_u128_lo(_sr_{d}))); }}\n",
                .{ tmp_id, rhs_u128_e, tmp_id, tmp_id, info.bits, dst_raw, dst_c, lhs_c, l_raw, sh_tok, tmp_id },
            );
        },
        .add_wrap => try emitter.print(
            "    _v_{d} = ({s})((({s})_v_{d}) + (({s})_v_{d}));\n",
            .{ dst_raw, dst_c, u_c, l_raw, u_c, r_raw },
        ),
        .sub_wrap => try emitter.print(
            "    _v_{d} = ({s})((({s})_v_{d}) - (({s})_v_{d}));\n",
            .{ dst_raw, dst_c, u_c, l_raw, u_c, r_raw },
        ),
        .mul_wrap => try emitter.print(
            "    _v_{d} = ({s})((({s})_v_{d}) * (({s})_v_{d}));\n",
            .{ dst_raw, dst_c, u_c, l_raw, u_c, r_raw },
        ),
        .shl_wrap, .ashr_wrap, .lshr_wrap => {
            const rhs_u128_e = try formatIntAsCxU128Expr(emitter, rhs_val, body.getInst(rhs_val).type_id);
            defer emitter.allocator.free(rhs_u128_e);
            const lhs_c = if (kind == .ashr_wrap) s_c else u_c;
            const sh_tok = if (kind == .shl_wrap) "<<" else ">>";
            try emitter.print(
                "    _v_{d} = ({s})((({s})_v_{d}) {s} (((uint32_t)_cx_u128_lo({s})) & {d}u));\n",
                .{ dst_raw, dst_c, lhs_c, l_raw, sh_tok, rhs_u128_e, info.bits - 1 },
            );
        },
        .sadd_sat => try emitter.print(
            "    {{ {s} _ov = 0; if (__builtin_add_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) " ++
                "_ov = (({s})_v_{d} < 0) ? ({s})({d}ull) : ({s})({d}ull); _v_{d} = ({s})_ov; }}\n",
            .{ s_c, s_c, l_raw, s_c, r_raw, s_c, l_raw, s_c, min_s_bits, s_c, max_s_bits, dst_raw, dst_c },
        ),
        .uadd_sat => try emitter.print(
            "    {{ {s} _ov = 0u; if (__builtin_add_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) " ++
                "_ov = ({s})({d}ull); _v_{d} = ({s})_ov; }}\n",
            .{ u_c, u_c, l_raw, u_c, r_raw, u_c, max_u_bits, dst_raw, dst_c },
        ),
        .ssub_sat => try emitter.print(
            "    {{ {s} _ov = 0; if (__builtin_sub_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) " ++
                "_ov = (({s})_v_{d} < 0) ? ({s})({d}ull) : ({s})({d}ull); _v_{d} = ({s})_ov; }}\n",
            .{ s_c, s_c, l_raw, s_c, r_raw, s_c, l_raw, s_c, min_s_bits, s_c, max_s_bits, dst_raw, dst_c },
        ),
        .usub_sat => try emitter.print(
            "    {{ {s} _ov = 0u; if (__builtin_sub_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) " ++
                "_ov = 0u; _v_{d} = ({s})_ov; }}\n",
            .{ u_c, u_c, l_raw, u_c, r_raw, dst_raw, dst_c },
        ),
        .smul_sat => try emitter.print(
            "    {{ {s} _ov = 0; if (__builtin_mul_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) " ++
                "_ov = (((({s})_v_{d} < 0) != (({s})_v_{d} < 0))) ? ({s})({d}ull) : ({s})({d}ull); _v_{d} = ({s})_ov; }}\n",
            .{ s_c, s_c, l_raw, s_c, r_raw, s_c, l_raw, s_c, r_raw, s_c, min_s_bits, s_c, max_s_bits, dst_raw, dst_c },
        ),
        .umul_sat => try emitter.print(
            "    {{ {s} _ov = 0u; if (__builtin_mul_overflow(({s})_v_{d}, ({s})_v_{d}, &_ov)) " ++
                "_ov = ({s})({d}ull); _v_{d} = ({s})_ov; }}\n",
            .{ u_c, u_c, l_raw, u_c, r_raw, u_c, max_u_bits, dst_raw, dst_c },
        ),
        .bit_and => try emitter.print(
            "    _v_{d} = ({s})((({s})_v_{d}) & (({s})_v_{d}));\n",
            .{ dst_raw, dst_c, u_c, l_raw, u_c, r_raw },
        ),
        .bit_or => try emitter.print(
            "    _v_{d} = ({s})((({s})_v_{d}) | (({s})_v_{d}));\n",
            .{ dst_raw, dst_c, u_c, l_raw, u_c, r_raw },
        ),
        .bit_xor => try emitter.print(
            "    _v_{d} = ({s})((({s})_v_{d}) ^ (({s})_v_{d}));\n",
            .{ dst_raw, dst_c, u_c, l_raw, u_c, r_raw },
        ),
        .eq => try emitter.print(
            "    _v_{d} = ((({s})_v_{d}) == (({s})_v_{d})) ? 1u : 0u;\n",
            .{ dst_raw, u_c, l_raw, u_c, r_raw },
        ),
        .ne => try emitter.print(
            "    _v_{d} = ((({s})_v_{d}) != (({s})_v_{d})) ? 1u : 0u;\n",
            .{ dst_raw, u_c, l_raw, u_c, r_raw },
        ),
        .slt => try emitter.print(
            "    _v_{d} = ((({s})_v_{d}) < (({s})_v_{d})) ? 1u : 0u;\n",
            .{ dst_raw, s_c, l_raw, s_c, r_raw },
        ),
        .ult => try emitter.print(
            "    _v_{d} = ((({s})_v_{d}) < (({s})_v_{d})) ? 1u : 0u;\n",
            .{ dst_raw, u_c, l_raw, u_c, r_raw },
        ),
        .sle => try emitter.print(
            "    _v_{d} = ((({s})_v_{d}) <= (({s})_v_{d})) ? 1u : 0u;\n",
            .{ dst_raw, s_c, l_raw, s_c, r_raw },
        ),
        .ule => try emitter.print(
            "    _v_{d} = ((({s})_v_{d}) <= (({s})_v_{d})) ? 1u : 0u;\n",
            .{ dst_raw, u_c, l_raw, u_c, r_raw },
        ),
        .sgt => try emitter.print(
            "    _v_{d} = ((({s})_v_{d}) > (({s})_v_{d})) ? 1u : 0u;\n",
            .{ dst_raw, s_c, l_raw, s_c, r_raw },
        ),
        .ugt => try emitter.print(
            "    _v_{d} = ((({s})_v_{d}) > (({s})_v_{d})) ? 1u : 0u;\n",
            .{ dst_raw, u_c, l_raw, u_c, r_raw },
        ),
        .sge => try emitter.print(
            "    _v_{d} = ((({s})_v_{d}) >= (({s})_v_{d})) ? 1u : 0u;\n",
            .{ dst_raw, s_c, l_raw, s_c, r_raw },
        ),
        .uge => try emitter.print(
            "    _v_{d} = ((({s})_v_{d}) >= (({s})_v_{d})) ? 1u : 0u;\n",
            .{ dst_raw, u_c, l_raw, u_c, r_raw },
        ),
        else => {},
    }
}

/// Emits 128-bit integer binary operations using `cx_u128` / `cx_i128` helpers.
fn emitInt128BinOpC(
    emitter: *CModuleEmitter,
    body: *const MirBody,
    dst_raw: u32,
    kind: BinOpKind,
    l_raw: u32,
    r_raw: u32,
    rhs_val: MirValueId,
) !void {
    switch (kind) {
        .sadd_checked => try emitter.print("    _v_{d} = _cx_i128_add_chk(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .uadd_checked => try emitter.print("    _v_{d} = _cx_u128_add_chk(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .ssub_checked => try emitter.print("    _v_{d} = _cx_i128_sub_chk(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .usub_checked => try emitter.print("    _v_{d} = _cx_u128_sub_chk(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .smul_checked => try emitter.print("    _v_{d} = _cx_i128_mul_chk(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .umul_checked => try emitter.print("    _v_{d} = _cx_u128_mul_chk(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .sdiv_checked => try emitter.print("    _v_{d} = _cx_i128_div_chk(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .udiv_checked => try emitter.print("    _v_{d} = _cx_u128_div_chk(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .srem_checked => try emitter.print("    _v_{d} = _cx_i128_rem_chk(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .urem_checked => try emitter.print("    _v_{d} = _cx_u128_rem_chk(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .add_wrap => try emitter.print("    _v_{d} = _cx_u128_add_wrap(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .sub_wrap => try emitter.print("    _v_{d} = _cx_u128_sub_wrap(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .mul_wrap => try emitter.print("    _v_{d} = _cx_u128_mul_wrap(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .sadd_sat => try emitter.print("    _v_{d} = _cx_i128_add_sat(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .uadd_sat => try emitter.print("    _v_{d} = _cx_u128_add_sat(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .ssub_sat => try emitter.print("    _v_{d} = _cx_i128_sub_sat(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .usub_sat => try emitter.print("    _v_{d} = _cx_u128_sub_sat(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .smul_sat => try emitter.print("    _v_{d} = _cx_i128_mul_sat(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .umul_sat => try emitter.print("    _v_{d} = _cx_u128_mul_sat(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .bit_and => try emitter.print("    _v_{d} = _cx_u128_and(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .bit_or => try emitter.print("    _v_{d} = _cx_u128_or(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .bit_xor => try emitter.print("    _v_{d} = _cx_u128_xor(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .shl_wrap, .lshr_wrap, .ashr_wrap => {
            const rhs_u128_e = try formatIntAsCxU128Expr(emitter, rhs_val, body.getInst(rhs_val).type_id);
            defer emitter.allocator.free(rhs_u128_e);
            const fn_sh = switch (kind) {
                .shl_wrap => "_cx_u128_shl",
                .lshr_wrap => "_cx_u128_lshr",
                else => "_cx_i128_ashr",
            };
            try emitter.print(
                "    _v_{d} = {s}(_v_{d}, (uint32_t)_cx_u128_lo({s}));\n",
                .{ dst_raw, fn_sh, l_raw, rhs_u128_e },
            );
        },
        .shl_checked, .lshr_checked, .ashr_checked => {
            const rhs_u128_e = try formatIntAsCxU128Expr(emitter, rhs_val, body.getInst(rhs_val).type_id);
            defer emitter.allocator.free(rhs_u128_e);
            const tmp_id = emitter.nextTempId();
            const fn_sh = switch (kind) {
                .shl_checked => "_cx_u128_shl",
                .lshr_checked => "_cx_u128_lshr",
                else => "_cx_i128_ashr",
            };
            try emitter.print(
                "    {{ cx_u128 _sr_{d} = {s}; if (_cx_u128_hi(_sr_{d}) != 0ull || _cx_u128_lo(_sr_{d}) >= 128ull) " ++
                    "_cx_rt_trap(2); _v_{d} = {s}(_v_{d}, (uint32_t)_cx_u128_lo(_sr_{d})); }}\n",
                .{ tmp_id, rhs_u128_e, tmp_id, tmp_id, dst_raw, fn_sh, l_raw, tmp_id },
            );
        },
        .eq => try emitter.print("    _v_{d} = _cx_u128_eq(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .ne => try emitter.print("    _v_{d} = _cx_u128_eq(_v_{d}, _v_{d}) ^ 1u;\n", .{ dst_raw, l_raw, r_raw }),
        .ult => try emitter.print("    _v_{d} = _cx_u128_ult(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .ule => try emitter.print("    _v_{d} = _cx_u128_ult(_v_{d}, _v_{d}) ^ 1u;\n", .{ dst_raw, r_raw, l_raw }),
        .ugt => try emitter.print("    _v_{d} = _cx_u128_ult(_v_{d}, _v_{d});\n", .{ dst_raw, r_raw, l_raw }),
        .uge => try emitter.print("    _v_{d} = _cx_u128_ult(_v_{d}, _v_{d}) ^ 1u;\n", .{ dst_raw, l_raw, r_raw }),
        .slt => try emitter.print("    _v_{d} = _cx_i128_slt(_v_{d}, _v_{d});\n", .{ dst_raw, l_raw, r_raw }),
        .sle => try emitter.print("    _v_{d} = _cx_i128_slt(_v_{d}, _v_{d}) ^ 1u;\n", .{ dst_raw, r_raw, l_raw }),
        .sgt => try emitter.print("    _v_{d} = _cx_i128_slt(_v_{d}, _v_{d});\n", .{ dst_raw, r_raw, l_raw }),
        .sge => try emitter.print("    _v_{d} = _cx_i128_slt(_v_{d}, _v_{d}) ^ 1u;\n", .{ dst_raw, l_raw, r_raw }),
        else => {},
    }
}

/// Emits UB-free C99 unary operations and conversions into `_v_<dst_raw>`.
fn emitUnaryOpC(
    emitter: *CModuleEmitter,
    body: *const MirBody,
    dst_raw: u32,
    kind: UnaryOpKind,
    src_val: MirValueId,
    rhs_ord: u32,
    dst_ty: TypeId,
) !void {
    const s_raw = src_val.asInt();
    const src_ty = emitter.input.pool.unwrapUnderlyingType(body.getInst(src_val).type_id);
    const unwrapped_dst = emitter.input.pool.unwrapUnderlyingType(dst_ty);
    const dst_c = try formatCType(emitter, dst_ty);
    defer emitter.allocator.free(dst_c);

    switch (kind) {
        .sneg_checked => {
            const info = (try resolveIntegerInfo(emitter, dst_ty)) orelse return;
            if (info.bits == 128) {
                try emitter.print(
                    "    _v_{d} = _cx_i128_sub_chk(_cx_i128_make(0ull, 0ull), _v_{d});\n",
                    .{ dst_raw, s_raw },
                );
            } else {
                const s_c = resolveSignedCTypeForBits(info.bits);
                try emitter.print(
                    "    {{ {s} _ov = 0; if (__builtin_sub_overflow(({s})0, ({s})_v_{d}, &_ov)) _cx_rt_trap(2); _v_{d} = ({s})_ov; }}\n",
                    .{ s_c, s_c, s_c, s_raw, dst_raw, dst_c },
                );
            }
        },
        .neg_wrap => {
            const info = (try resolveIntegerInfo(emitter, dst_ty)) orelse return;
            if (info.bits == 128) {
                try emitter.print(
                    "    _v_{d} = _cx_u128_sub_wrap(_cx_u128_make(0ull, 0ull), _v_{d});\n",
                    .{ dst_raw, s_raw },
                );
            } else {
                const u_c = resolveUnsignedCTypeForBits(info.bits);
                try emitter.print(
                    "    _v_{d} = ({s})((({s})0u) - (({s})_v_{d}));\n",
                    .{ dst_raw, dst_c, u_c, u_c, s_raw },
                );
            }
        },
        .fneg => try emitter.print("    _v_{d} = -_v_{d};\n", .{ dst_raw, s_raw }),
        .bool_not => try emitter.print("    _v_{d} = (_v_{d} & 1u) ^ 1u;\n", .{ dst_raw, s_raw }),
        .bit_not => {
            var eff_dst = unwrapped_dst;
            if (!eff_dst.isPrimitiveOrSentinel() and emitter.input.pool.getNode(eff_dst).tag == .bit_field_ty) {
                eff_dst = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(emitter.input.pool.getNode(eff_dst).lhs));
            }
            if (!eff_dst.isPrimitiveOrSentinel() and emitter.input.pool.getNode(eff_dst).tag == .array_ty) {
                const arr_node = emitter.input.pool.getNode(eff_dst);
                const lane_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(arr_node.lhs));
                const lane_count: u64 = arr_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                if (try resolveIntegerInfo(emitter, lane_ty)) |lane_info| {
                    const lane_c = try formatCType(emitter, lane_ty);
                    defer emitter.allocator.free(lane_c);
                    var lane_i: u64 = 0;
                    while (lane_i < lane_count) : (lane_i += 1) {
                        if (lane_info.bits == 128) {
                            try emitter.print(
                                "    _v_{d}._elems[{d}u] = _cx_u128_not(_v_{d}._elems[{d}u]);\n",
                                .{ dst_raw, lane_i, s_raw, lane_i },
                            );
                        } else {
                            const ulane_c = resolveUnsignedCTypeForBits(lane_info.bits);
                            try emitter.print(
                                "    _v_{d}._elems[{d}u] = ({s})(~(({s})_v_{d}._elems[{d}u]));\n",
                                .{ dst_raw, lane_i, lane_c, ulane_c, s_raw, lane_i },
                            );
                        }
                    }
                }
                return;
            }
            const info = (try resolveIntegerInfo(emitter, dst_ty)) orelse return;
            if (info.bits == 128) {
                try emitter.print("    _v_{d} = _cx_u128_not(_v_{d});\n", .{ dst_raw, s_raw });
            } else {
                const u_c = resolveUnsignedCTypeForBits(info.bits);
                try emitter.print("    _v_{d} = ({s})(~(({s})_v_{d}));\n", .{ dst_raw, dst_c, u_c, s_raw });
            }
        },
        .int_sext => {
            const src_info = (try resolveIntegerInfo(emitter, src_ty)) orelse return;
            const dst_info = (try resolveIntegerInfo(emitter, dst_ty)) orelse return;
            if (dst_info.bits == 128) {
                if (src_info.bits == 128) {
                    try emitter.print("    _v_{d} = _v_{d};\n", .{ dst_raw, s_raw });
                } else {
                    const s_c = resolveSignedCTypeForBits(src_info.bits);
                    const tmp_id = emitter.nextTempId();
                    try emitter.print(
                        "    int64_t _se_{d} = (int64_t)(({s})_v_{d});\n" ++
                            "    _v_{d} = _cx_i128_make((uint64_t)_se_{d}, _se_{d} < 0 ? 0xFFFFFFFFFFFFFFFFull : 0ull);\n",
                        .{ tmp_id, s_c, s_raw, dst_raw, tmp_id, tmp_id },
                    );
                }
            } else {
                const s_src = resolveSignedCTypeForBits(src_info.bits);
                const s_dst = resolveSignedCTypeForBits(dst_info.bits);
                try emitter.print("    _v_{d} = ({s})(({s})(({s})_v_{d}));\n", .{ dst_raw, dst_c, s_dst, s_src, s_raw });
            }
        },
        .int_zext => {
            const src_info = (try resolveIntegerInfo(emitter, src_ty)) orelse return;
            const dst_info = (try resolveIntegerInfo(emitter, dst_ty)) orelse return;
            if (dst_info.bits == 128) {
                if (src_info.bits == 128) {
                    try emitter.print("    _v_{d} = _v_{d};\n", .{ dst_raw, s_raw });
                } else {
                    const u_src = resolveUnsignedCTypeForBits(src_info.bits);
                    try emitter.print(
                        "    _v_{d} = _cx_u128_make((uint64_t)(({s})_v_{d}), 0ull);\n",
                        .{ dst_raw, u_src, s_raw },
                    );
                }
            } else {
                const u_src = resolveUnsignedCTypeForBits(src_info.bits);
                try emitter.print("    _v_{d} = ({s})(({s})_v_{d});\n", .{ dst_raw, dst_c, u_src, s_raw });
            }
        },
        .int_trunc => {
            const src_info = (try resolveIntegerInfo(emitter, src_ty)) orelse return;
            if (src_info.bits == 128) {
                if (unwrapped_dst == .bool_ty) {
                    try emitter.print("    _v_{d} = (_cx_u128_lo(_v_{d}) & 1ull) ? 1u : 0u;\n", .{ dst_raw, s_raw });
                } else {
                    try emitter.print("    _v_{d} = ({s})_cx_u128_lo(_v_{d});\n", .{ dst_raw, dst_c, s_raw });
                }
            } else if (unwrapped_dst == .bool_ty) {
                try emitter.print("    _v_{d} = (_v_{d} & 1u) ? 1u : 0u;\n", .{ dst_raw, s_raw });
            } else {
                try emitter.print("    _v_{d} = ({s})_v_{d};\n", .{ dst_raw, dst_c, s_raw });
            }
        },
        .int_to_float_signed => {
            const src_info = (try resolveIntegerInfo(emitter, src_ty)) orelse return;
            if (src_info.bits == 128) {
                const fn_conv = if (unwrapped_dst == .f32_ty) "_cx_i128_to_f32" else "_cx_i128_to_f64";
                try emitter.print("    _v_{d} = {s}(_v_{d});\n", .{ dst_raw, fn_conv, s_raw });
            } else {
                const s_c = resolveSignedCTypeForBits(src_info.bits);
                try emitter.print("    _v_{d} = ({s})(({s})_v_{d});\n", .{ dst_raw, dst_c, s_c, s_raw });
            }
        },
        .int_to_float_unsigned => {
            const src_info = (try resolveIntegerInfo(emitter, src_ty)) orelse return;
            if (src_info.bits == 128) {
                const fn_conv = if (unwrapped_dst == .f32_ty) "_cx_u128_to_f32" else "_cx_u128_to_f64";
                try emitter.print("    _v_{d} = {s}(_v_{d});\n", .{ dst_raw, fn_conv, s_raw });
            } else {
                const u_c = resolveUnsignedCTypeForBits(src_info.bits);
                try emitter.print("    _v_{d} = ({s})(({s})_v_{d});\n", .{ dst_raw, dst_c, u_c, s_raw });
            }
        },
        .float_to_int_signed => {
            const dst_info = (try resolveIntegerInfo(emitter, dst_ty)) orelse return;
            if (dst_info.bits <= 64) {
                const min_incl: f64 = -@as(f64, @floatFromInt(@as(u128, 1) << @intCast(dst_info.bits - 1)));
                const max_excl: f64 = @floatFromInt(@as(u128, 1) << @intCast(dst_info.bits - 1));
                try emitter.print(
                    "    _v_{d} = ({s})_cx_f64_to_i64((double)_v_{d}, {e}, {e});\n",
                    .{ dst_raw, dst_c, s_raw, min_incl, max_excl },
                );
            } else {
                try emitter.print(
                    "    _v_{d} = _cx_f64_to_i128((double)_v_{d});\n",
                    .{ dst_raw, s_raw },
                );
            }
        },
        .float_to_int_unsigned => {
            const dst_info = (try resolveIntegerInfo(emitter, dst_ty)) orelse return;
            if (dst_info.bits <= 64) {
                const max_excl: f64 = @floatFromInt(@as(u128, 1) << @intCast(dst_info.bits));
                try emitter.print(
                    "    _v_{d} = ({s})_cx_f64_to_u64((double)_v_{d}, {e});\n",
                    .{ dst_raw, dst_c, s_raw, max_excl },
                );
            } else {
                try emitter.print(
                    "    _v_{d} = _cx_f64_to_u128((double)_v_{d});\n",
                    .{ dst_raw, s_raw },
                );
            }
        },
        .float_promote, .float_demote => {
            try emitter.print("    _v_{d} = ({s})_v_{d};\n", .{ dst_raw, dst_c, s_raw });
        },
        .bitcast_op, .ptr_cast => {
            const src_node = emitter.input.pool.getNode(src_ty);
            const dst_node = emitter.input.pool.getNode(unwrapped_dst);
            if ((src_node.tag == .ref_ty or src_node.tag == .mut_ref_ty or src_node.tag == .raw_ptr_ty) and
                (dst_node.tag == .slice_ty or dst_node.tag == .soa_slice_ty))
            {
                const p_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(src_node.lhs));
                const deref_str = try std.fmt.allocPrint(emitter.allocator, "(*_v_{d})", .{s_raw});
                defer emitter.allocator.free(deref_str);
                try emitArrayLvalueToSliceValueC(emitter, deref_str, p_ty, unwrapped_dst, dst_raw, false);
                return;
            }
            if ((src_node.tag == .ref_ty or src_node.tag == .mut_ref_ty or src_node.tag == .raw_ptr_ty) and
                resolveSliceRefPointee(emitter, unwrapped_dst) != null)
            {
                const p_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(src_node.lhs));
                const p_tag = emitter.input.pool.getNode(p_ty).tag;
                if (p_tag == .array_ty or p_tag == .soa_array_ty) {
                    const sl_ty = resolveSliceRefPointee(emitter, unwrapped_dst).?;
                    const deref_str = try std.fmt.allocPrint(emitter.allocator, "(*_v_{d})", .{s_raw});
                    defer emitter.allocator.free(deref_str);
                    try emitArrayLvalueToSliceValueC(emitter, deref_str, p_ty, sl_ty, dst_raw, true);
                    return;
                }
            }
            if (kind == .ptr_cast) {
                if ((src_node.tag == .ref_ty or src_node.tag == .mut_ref_ty or
                    src_node.tag == .raw_ptr_ty or src_node.tag == .fn_ty) and
                    (dst_node.tag == .ref_ty or dst_node.tag == .mut_ref_ty or
                        dst_node.tag == .raw_ptr_ty or dst_node.tag == .fn_ty))
                {
                    try emitter.print("    _v_{d} = ({s})_v_{d};\n", .{ dst_raw, dst_c, s_raw });
                } else {
                    try emitter.print("    _v_{d} = ({s})((uintptr_t)_v_{d});\n", .{ dst_raw, dst_c, s_raw });
                }
            } else if (!(try isZeroSizedType(emitter, dst_ty))) {
                try emitter.print("    memcpy(&_v_{d}, &_v_{d}, sizeof(_v_{d}));\n", .{ dst_raw, s_raw, dst_raw });
            }
        },
        .ssa_discriminant => {
            if (try emitter.resolver.getSumDetail(src_ty)) |sum_detail| {
                const v_str = try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{s_raw});
                defer emitter.allocator.free(v_str);
                const d_expr = try formatSumDiscrReadExpr(emitter, src_ty, sum_detail, v_str);
                defer emitter.allocator.free(d_expr);
                try emitter.print("    _v_{d} = ({s})({s});\n", .{ dst_raw, dst_c, d_expr });
            } else if (!src_ty.isPrimitiveOrSentinel() and emitter.input.pool.getNode(src_ty).tag == .enum_ty) {
                const v_str = try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{s_raw});
                defer emitter.allocator.free(v_str);
                try emitScalarEnumOrdinalReadC(emitter, src_ty, v_str, dst_raw, dst_c);
            } else {
                try emitter.print("    _v_{d} = ({s})_v_{d};\n", .{ dst_raw, dst_c, s_raw });
            }
        },
        .ssa_variant_payload => {
            if (try isZeroSizedType(emitter, dst_ty)) return;
            if (try emitter.resolver.getSumDetail(src_ty)) |sum_detail| {
                if (sum_detail.repr == .explicit_tag) {
                    try emitter.print("    _v_{d} = _v_{d}._u._v{d};\n", .{ dst_raw, s_raw, rhs_ord });
                } else {
                    try emitter.print("    _v_{d} = _v_{d}._pay;\n", .{ dst_raw, s_raw });
                }
            }
        },
    }
}

/// Emits `MirOp.aggregate_make` (tuples, structs, arrays, sum variants, closures, `str_concat`) into `_v_<dst_raw>`.
fn emitAggregateMakeC(
    emitter: *CModuleEmitter,
    body_idx: u32,
    body: *const MirBody,
    dst_raw: u32,
    kind: AggregateKind,
    inst: mir.MirInst,
) !void {
    if (try isZeroSizedType(emitter, inst.type_id)) return;
    try emitter.print("    memset(&_v_{d}, 0, sizeof(_v_{d}));\n", .{ dst_raw, dst_raw });

    switch (kind) {
        .tuple_agg, .struct_agg => {
            const elems = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
            const agg_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            if (emitter.input.pool.getNode(agg_ty).tag == .union_ty) {
                for (elems) |elem_raw| {
                    const elem_ty = body.getInst(MirValueId.fromInt(elem_raw)).type_id;
                    if (!(try isZeroSizedType(emitter, elem_ty))) {
                        try emitter.print(
                            "    memcpy(&_v_{d}, &_v_{d}, sizeof(_v_{d}));\n",
                            .{ dst_raw, elem_raw, elem_raw },
                        );
                    }
                }
                return;
            }
            for (elems, 0..) |elem_raw, fld_i| {
                const elem_ty = body.getInst(MirValueId.fromInt(elem_raw)).type_id;
                if (!(try isZeroSizedType(emitter, elem_ty))) {
                    try emitter.print("    _v_{d}._f{d} = _v_{d};\n", .{ dst_raw, fld_i, elem_raw });
                }
            }
        },
        .array_elems => {
            const elems = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
            const arr_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            const arr_node = emitter.input.pool.getNode(arr_ty);
            if (arr_node.tag == .soa_array_ty) {
                const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(arr_node.lhs));
                const st_lay = try emitter.resolver.resolveType(elem_struct);
                const fld_start = st_lay.aux_start;
                const fld_len = st_lay.aux_len;
                const cap: u64 = arr_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                for (elems, 0..) |elem_raw, elem_i| {
                    var fld_ord: u32 = 0;
                    while (fld_ord < fld_len) : (fld_ord += 1) {
                        const fld = emitter.resolver.fields_by_decl.items[fld_start + fld_ord];
                        if (fld.size_bytes == 0) continue;
                        const col = emitter.resolver.getSoaColumnOffset(elem_struct, fld_ord, cap).?;
                        const fld_c = try formatCType(emitter, fld.field_ty);
                        defer emitter.allocator.free(fld_c);
                        try emitter.print(
                            "    (({s} *)(&_v_{d}._bytes[{d}u]))[{d}u] = _v_{d}._f{d};\n",
                            .{ fld_c, dst_raw, col.byte_offset, elem_i, elem_raw, fld_ord },
                        );
                    }
                }
            } else {
                for (elems, 0..) |elem_raw, elem_i| {
                    const elem_ty = body.getInst(MirValueId.fromInt(elem_raw)).type_id;
                    if (!(try isZeroSizedType(emitter, elem_ty))) {
                        try emitter.print("    _v_{d}._elems[{d}u] = _v_{d};\n", .{ dst_raw, elem_i, elem_raw });
                    }
                }
            }
        },
        .array_repeat => {
            const elem_raw = inst.operands.lhs;
            const rep_count: u64 = inst.operands.rhs;
            const elem_ty = body.getInst(MirValueId.fromInt(elem_raw)).type_id;
            if (rep_count == 0 or (try isZeroSizedType(emitter, elem_ty))) return;
            var arr_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            if (!arr_ty.isPrimitiveOrSentinel() and emitter.input.pool.getNode(arr_ty).tag == .bit_field_ty) {
                arr_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(emitter.input.pool.getNode(arr_ty).lhs));
            }
            const arr_node = emitter.input.pool.getNode(arr_ty);
            if (arr_node.tag == .soa_array_ty) {
                const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(arr_node.lhs));
                const st_lay = try emitter.resolver.resolveType(elem_struct);
                const fld_start = st_lay.aux_start;
                const fld_len = st_lay.aux_len;
                var fld_ord: u32 = 0;
                while (fld_ord < fld_len) : (fld_ord += 1) {
                    const fld = emitter.resolver.fields_by_decl.items[fld_start + fld_ord];
                    if (fld.size_bytes == 0) continue;
                    const col = emitter.resolver.getSoaColumnOffset(elem_struct, fld_ord, rep_count).?;
                    const fld_c = try formatCType(emitter, fld.field_ty);
                    defer emitter.allocator.free(fld_c);
                    try emitter.print(
                        "    {{ size_t _ri = 0u; while (_ri < {d}u) {{ (({s} *)(&_v_{d}._bytes[{d}u]))[_ri] = _v_{d}._f{d}; _ri += 1u; }} }}\n",
                        .{ rep_count, fld_c, dst_raw, col.byte_offset, elem_raw, fld_ord },
                    );
                }
            } else {
                try emitter.print(
                    "    {{ size_t _ri = 0u; while (_ri < {d}u) {{ _v_{d}._elems[_ri] = _v_{d}; _ri += 1u; }} }}\n",
                    .{ rep_count, dst_raw, elem_raw },
                );
            }
        },
        .tagged_variant => {
            const tag_ord: u32 = inst.operands.rhs >> 16;
            const arg_len: u32 = inst.operands.rhs & 0xFFFF;
            const args = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + arg_len];
            const sum_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            if (try emitter.resolver.getSumDetail(sum_ty)) |sum_detail| {
                const var_pay_ty = resolveEnumVariantPayloadType(emitter, sum_ty, tag_ord);
                if (arg_len > 0 and !(try isZeroSizedType(emitter, var_pay_ty))) {
                    const pay_access = if (sum_detail.repr == .explicit_tag)
                        try std.fmt.allocPrint(emitter.allocator, "_v_{d}._u._v{d}", .{ dst_raw, tag_ord })
                    else
                        try std.fmt.allocPrint(emitter.allocator, "_v_{d}._pay", .{dst_raw});
                    defer emitter.allocator.free(pay_access);
                    if (arg_len == 1 and
                        emitter.input.pool.unwrapUnderlyingType(body.getInst(MirValueId.fromInt(args[0])).type_id) == var_pay_ty)
                    {
                        try emitter.print("    {s} = _v_{d};\n", .{ pay_access, args[0] });
                    } else {
                        for (args, 0..) |sub_raw, sub_i| {
                            if (!(try isZeroSizedType(emitter, body.getInst(MirValueId.fromInt(sub_raw)).type_id))) {
                                try emitter.print("    {s}._f{d} = _v_{d};\n", .{ pay_access, sub_i, sub_raw });
                            }
                        }
                    }
                }
                const dst_str = try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{dst_raw});
                defer emitter.allocator.free(dst_str);
                try emitSumDiscrWriteStmt(emitter, sum_ty, tag_ord, dst_str);
            } else if (!sum_ty.isPrimitiveOrSentinel() and emitter.input.pool.getNode(sum_ty).tag == .enum_ty) {
                const dst_str = try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{dst_raw});
                defer emitter.allocator.free(dst_str);
                try emitScalarEnumDiscrimWriteC(emitter, sum_ty, tag_ord, dst_str);
            } else {
                const dst_c = try formatCType(emitter, inst.type_id);
                defer emitter.allocator.free(dst_c);
                try emitter.print("    _v_{d} = ({s}){d}u;\n", .{ dst_raw, dst_c, tag_ord });
            }
        },
        .closure_make => {
            const key: u64 = (@as(u64, body_idx) << 32) | @as(u64, dst_raw);
            const thunk_idx = emitter.closure_thunk_map.get(key) orelse return;
            const thunk = emitter.closure_thunks.items[thunk_idx];
            if (thunk.is_three_word) {
                if (thunk.capture_types.len > 0) {
                    const tmp_id = emitter.nextTempId();
                    try emitter.print(
                        "    {{ _cx_cenv_{d} *_henv_{d} = (_cx_cenv_{d} *)calloc(1u, sizeof(_cx_cenv_{d}));\n" ++
                            "      if (_henv_{d} == NULL) _cx_rt_trap(0u);\n",
                        .{ thunk_idx, tmp_id, thunk_idx, thunk_idx, tmp_id },
                    );
                    for (thunk.capture_types, 0..) |cap_ty, cap_i| {
                        if (try isZeroSizedType(emitter, cap_ty)) continue;
                        const cap_val = body.extra_args.items[inst.operands.rhs + 1 + cap_i];
                        try emitter.print("      _henv_{d}->_c{d} = _v_{d};\n", .{ tmp_id, cap_i, cap_val });
                    }
                    try emitter.print(
                        "      _v_{d}.env_ptr = (uint8_t *)_henv_{d}; _v_{d}.drop_fn = _cx_cdrop_{d}; }}\n",
                        .{ dst_raw, tmp_id, dst_raw, thunk_idx },
                    );
                } else {
                    try emitter.print(
                        "    _v_{d}.env_ptr = (uint8_t *)((uintptr_t){d}u); _v_{d}.drop_fn = NULL;\n",
                        .{ dst_raw, emitter.cfg.target.ptrBytes(), dst_raw },
                    );
                }
            } else if (thunk.capture_types.len > 0) {
                for (thunk.capture_types, 0..) |cap_ty, cap_i| {
                    if (try isZeroSizedType(emitter, cap_ty)) continue;
                    const cap_val = body.extra_args.items[inst.operands.rhs + 1 + cap_i];
                    try emitter.print("    _cenv_loc_{d}._c{d} = _v_{d};\n", .{ dst_raw, cap_i, cap_val });
                }
                try emitter.print("    _v_{d}.env_ptr = (uint8_t *)&_cenv_loc_{d};\n", .{ dst_raw, dst_raw });
            } else {
                try emitter.print(
                    "    _v_{d}.env_ptr = (uint8_t *)((uintptr_t){d}u);\n",
                    .{ dst_raw, emitter.cfg.target.ptrBytes() },
                );
            }
            try emitter.print("    _v_{d}.fn_ptr = _cx_cthunk_{d};\n", .{ dst_raw, thunk_idx });
        },
        .fmt_args_make => {
            const words = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
            if (words.len < 1) return;
            const piece_count = extractConstUsizeFromBody(body, words[0]) orelse return;
            if (words.len < 1 + piece_count) return;
            const hole_count = (words.len - 1 - piece_count) / 3;
            if (isStaticConstFmtArgsMake(body, inst)) {
                const tmp_id = emitter.nextTempId();
                try emitter.print("    {{ static const cx_str_t _fsp_{d}[{d}u] = {{", .{ tmp_id, @max(piece_count, 1) });
                if (piece_count == 0) {
                    try emitter.writeAll(" { (uint8_t *)_cx_empty_rodata, 0u } ");
                } else {
                    var piece_i: usize = 0;
                    while (piece_i < piece_count) : (piece_i += 1) {
                        if (piece_i > 0) try emitter.writeAll(",");
                        const sym_id = extractConstStrSymFromBody(body, words[1 + piece_i]).?;
                        const str_bytes = emitter.input.interner.get(sym_id);
                        if (str_bytes.len == 0) {
                            try emitter.writeAll(" { (uint8_t *)_cx_empty_rodata, 0u }");
                        } else {
                            try emitter.print(" {{ (uint8_t *)_cx_str_bytes_{d}, {d}u }}", .{ sym_id.asInt(), str_bytes.len });
                        }
                    }
                }
                try emitter.print(
                    " }}; _v_{d}.pieces_ptr = _fsp_{d}; _v_{d}.pieces_len = {d}u; " ++
                        "_v_{d}.args_ptr = NULL; _v_{d}.args_len = 0u; }}\n",
                    .{ dst_raw, tmp_id, dst_raw, piece_count, dst_raw, dst_raw },
                );
                return;
            }
            var piece_i: usize = 0;
            while (piece_i < piece_count) : (piece_i += 1) {
                try emitter.print("    _fmt_p_{d}[{d}u] = _v_{d};\n", .{ dst_raw, piece_i, words[1 + piece_i] });
            }
            var hole_j: usize = 0;
            while (hole_j < hole_count) : (hole_j += 1) {
                const hole_ref_raw = words[1 + piece_count + hole_j * 3];
                const spec_lo_raw = words[1 + piece_count + hole_j * 3 + 1];
                const spec_hi_raw = words[1 + piece_count + hole_j * 3 + 2];
                const hole_ref_ty = emitter.input.pool.unwrapUnderlyingType(
                    body.getInst(MirValueId.fromInt(hole_ref_raw)).type_id,
                );
                const hole_node = emitter.input.pool.getNode(hole_ref_ty);
                const is_ptr_arg = hole_node.tag == .ref_ty or
                    hole_node.tag == .mut_ref_ty or
                    hole_node.tag == .raw_ptr_ty;
                const hole_ty = if (is_ptr_arg)
                    emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(hole_node.lhs))
                else
                    hole_ref_ty;
                const data_expr = if (is_ptr_arg)
                    try std.fmt.allocPrint(emitter.allocator, "(const void *)_v_{d}", .{hole_ref_raw})
                else if (try isZeroSizedType(emitter, hole_ty))
                    try emitter.allocator.dupe(u8, "(const void *)((uintptr_t)1u)")
                else blk_hspill: {
                    try emitter.print("    _fmt_h_{d}_{d} = _v_{d};\n", .{ dst_raw, hole_j, hole_ref_raw });
                    break :blk_hspill try std.fmt.allocPrint(
                        emitter.allocator,
                        "(const void *)(&_fmt_h_{d}_{d})",
                        .{ dst_raw, hole_j },
                    );
                };
                defer emitter.allocator.free(data_expr);
                try emitter.print(
                    "    _fmt_a_{d}[{d}u].data = {s}; " ++
                        "_fmt_a_{d}[{d}u].fmt_fn = _cx_fmt_fn_ty_{d}; " ++
                        "_fmt_a_{d}[{d}u].spec.flags_and_fill = (uint32_t)_v_{d}; " ++
                        "_fmt_a_{d}[{d}u].spec.width_or_none = (uint16_t)(((uint32_t)_v_{d}) & 0xFFFFu); " ++
                        "_fmt_a_{d}[{d}u].spec.precision_or_none = (uint16_t)(((uint32_t)_v_{d}) >> 16);\n",
                    .{
                        dst_raw, hole_j, data_expr,
                        dst_raw, hole_j, hole_ty.toU32(),
                        dst_raw, hole_j, spec_lo_raw,
                        dst_raw, hole_j, spec_hi_raw,
                        dst_raw, hole_j, spec_hi_raw,
                    },
                );
            }
            if (piece_count > 0) {
                try emitter.print("    _v_{d}.pieces_ptr = _fmt_p_{d};\n", .{ dst_raw, dst_raw });
            } else {
                try emitter.print("    _v_{d}.pieces_ptr = NULL;\n", .{dst_raw});
            }
            try emitter.print("    _v_{d}.pieces_len = {d}u;\n", .{ dst_raw, piece_count });
            if (hole_count > 0) {
                try emitter.print("    _v_{d}.args_ptr = _fmt_a_{d};\n", .{ dst_raw, dst_raw });
            } else {
                try emitter.print("    _v_{d}.args_ptr = NULL;\n", .{dst_raw});
            }
            try emitter.print("    _v_{d}.args_len = {d}u;\n", .{ dst_raw, hole_count });
        },
        .str_concat => {
            const parts = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
            const tmp_id = emitter.nextTempId();
            try emitter.print("    {{ size_t _tot_{d} = 0u;\n", .{tmp_id});
            for (parts, 0..) |part_raw, part_k| {
                const part_ty = emitter.input.pool.unwrapUnderlyingType(
                    body.getInst(MirValueId.fromInt(part_raw)).type_id,
                );
                if (part_ty == .str_ty) {
                    try emitter.print(
                        "      const uint8_t *_pp_{d}_{d} = _v_{d}.ptr; size_t _pl_{d}_{d} = (size_t)_v_{d}.len;\n",
                        .{ tmp_id, part_k, part_raw, tmp_id, part_k, part_raw },
                    );
                } else if (part_ty == .bool_ty) {
                    try emitter.print(
                        "      const uint8_t *_pp_{d}_{d} = (_v_{d} & 1u) ? (const uint8_t *)\"true\" : " ++
                            "(const uint8_t *)\"false\"; size_t _pl_{d}_{d} = (_v_{d} & 1u) ? 4u : 5u;\n",
                        .{ tmp_id, part_k, part_raw, tmp_id, part_k, part_raw },
                    );
                } else if (try resolveIntegerInfo(emitter, part_ty)) |p_int| {
                    if (p_int.bits == 128) {
                        const fmt_fn = if (p_int.is_signed) "_cx_fmt_i128" else "_cx_fmt_u128";
                        try emitter.print(
                            "      char _pbuf_{d}_{d}[64]; size_t _pl_{d}_{d} = {s}(_pbuf_{d}_{d}, _v_{d}); " ++
                                "const uint8_t *_pp_{d}_{d} = (const uint8_t *)_pbuf_{d}_{d};\n",
                            .{ tmp_id, part_k, tmp_id, part_k, fmt_fn, tmp_id, part_k, part_raw, tmp_id, part_k, tmp_id, part_k },
                        );
                    } else if (p_int.is_signed) {
                        try emitter.print(
                            "      char _pbuf_{d}_{d}[64]; int _pn_{d}_{d} = snprintf(_pbuf_{d}_{d}, 64u, " ++
                                "\"%lld\", (long long)_v_{d}); const uint8_t *_pp_{d}_{d} = " ++
                                "(const uint8_t *)_pbuf_{d}_{d}; size_t _pl_{d}_{d} = _pn_{d}_{d} > 0 ? " ++
                                "(size_t)_pn_{d}_{d} : 0u;\n",
                            .{
                                tmp_id, part_k, tmp_id, part_k, tmp_id, part_k, part_raw,
                                tmp_id, part_k, tmp_id, part_k, tmp_id, part_k, tmp_id,
                                part_k, tmp_id, part_k,
                            },
                        );
                    } else {
                        try emitter.print(
                            "      char _pbuf_{d}_{d}[64]; int _pn_{d}_{d} = snprintf(_pbuf_{d}_{d}, 64u, " ++
                                "\"%llu\", (unsigned long long)_v_{d}); const uint8_t *_pp_{d}_{d} = " ++
                                "(const uint8_t *)_pbuf_{d}_{d}; size_t _pl_{d}_{d} = _pn_{d}_{d} > 0 ? " ++
                                "(size_t)_pn_{d}_{d} : 0u;\n",
                            .{
                                tmp_id, part_k, tmp_id, part_k, tmp_id, part_k, part_raw,
                                tmp_id, part_k, tmp_id, part_k, tmp_id, part_k, tmp_id,
                                part_k, tmp_id, part_k,
                            },
                        );
                    }
                } else if (part_ty == .f32_ty or part_ty == .f64_ty) {
                    try emitter.print(
                        "      char _pbuf_{d}_{d}[64]; int _pn_{d}_{d} = snprintf(_pbuf_{d}_{d}, 64u, " ++
                            "\"%g\", (double)_v_{d}); const uint8_t *_pp_{d}_{d} = " ++
                            "(const uint8_t *)_pbuf_{d}_{d}; size_t _pl_{d}_{d} = _pn_{d}_{d} > 0 ? " ++
                            "(size_t)_pn_{d}_{d} : 0u;\n",
                        .{
                            tmp_id, part_k, tmp_id, part_k, tmp_id, part_k, part_raw,
                            tmp_id, part_k, tmp_id, part_k, tmp_id, part_k, tmp_id,
                            part_k, tmp_id, part_k,
                        },
                    );
                } else {
                    try emitter.print(
                        "      const uint8_t *_pp_{d}_{d} = (const uint8_t *)\"\"; size_t _pl_{d}_{d} = 0u;\n",
                        .{ tmp_id, part_k, tmp_id, part_k },
                    );
                }
                try emitter.print(
                    "      if (_pl_{d}_{d} > ((size_t)-1) - _tot_{d}) _cx_rt_trap(1u); _tot_{d} += _pl_{d}_{d};\n",
                    .{ tmp_id, part_k, tmp_id, tmp_id, tmp_id, part_k },
                );
            }
            try emitter.print(
                "      if (_tot_{d} == 0u) {{ _v_{d}.ptr = (uint8_t *)((uintptr_t)1u); _v_{d}.len = 0u; }} else {{\n" ++
                    "        uint8_t *_sbuf_{d} = (uint8_t *)malloc(_tot_{d});\n" ++
                    "        if (_sbuf_{d} == NULL) _cx_rt_trap(0);\n" ++
                    "        size_t _scur_{d} = 0u;\n",
                .{ tmp_id, dst_raw, dst_raw, tmp_id, tmp_id, tmp_id, tmp_id },
            );
            for (0..parts.len) |part_k| {
                try emitter.print(
                    "        if (_pl_{d}_{d} > 0u) {{ memcpy(_sbuf_{d} + _scur_{d}, _pp_{d}_{d}, _pl_{d}_{d}); " ++
                        "_scur_{d} += _pl_{d}_{d}; }}\n",
                    .{ tmp_id, part_k, tmp_id, tmp_id, tmp_id, part_k, tmp_id, part_k, tmp_id, tmp_id, part_k },
                );
            }
            try emitter.print(
                "        _v_{d}.ptr = _sbuf_{d}; _v_{d}.len = _tot_{d};\n      }} }}\n",
                .{ dst_raw, tmp_id, dst_raw, tmp_id },
            );
        },
    }
}

/// Classification of C11/GNU `__atomic_*` memory-order clamping rules.
const AtomicOrderSlotKind = enum {
    /// `@atomic_fence` and `@atomic_rmw_*`: all 5 C11 memory models valid (`Consume -> Acquire`).
    fence_or_rmw,
    /// `@atomic_load`: `Release` -> `Relaxed` and `AcqRel` -> `Acquire` per C11 `atomic_load_explicit`.
    load_op,
    /// `@atomic_store`: `Consume`/`Acquire` -> `Relaxed` and `AcqRel` -> `Release` per C11 `atomic_store_explicit`.
    store_op,
};

/// Resolves the compile-time `__ATOMIC_*` macro name for CoreX `MemoryOrder` code `0..5` (`null` if `> 5`).
fn resolveAtomicOrderMacroC(order_code: u64, slot_kind: AtomicOrderSlotKind) ?[]const u8 {
    return switch (slot_kind) {
        .fence_or_rmw => switch (order_code) {
            0 => "__ATOMIC_RELAXED",
            1, 2 => "__ATOMIC_ACQUIRE",
            3 => "__ATOMIC_RELEASE",
            4 => "__ATOMIC_ACQ_REL",
            5 => "__ATOMIC_SEQ_CST",
            else => null,
        },
        .load_op => switch (order_code) {
            0, 3 => "__ATOMIC_RELAXED",
            1, 2, 4 => "__ATOMIC_ACQUIRE",
            5 => "__ATOMIC_SEQ_CST",
            else => null,
        },
        .store_op => switch (order_code) {
            0, 1, 2 => "__ATOMIC_RELAXED",
            3, 4 => "__ATOMIC_RELEASE",
            5 => "__ATOMIC_SEQ_CST",
            else => null,
        },
    };
}

/// Emits a single-order `__atomic_*` statement with constant fast-path and `0..5` runtime switch fallback.
fn emitSingleOrderAtomicStmtC(
    emitter: *CModuleEmitter,
    body: *const MirBody,
    slot_kind: AtomicOrderSlotKind,
    order_vid_opt: ?u32,
    stmt_prefix: []const u8,
) !void {
    const order_vid = order_vid_opt orelse {
        try emitter.print("    {s}__ATOMIC_SEQ_CST);\n", .{stmt_prefix});
        return;
    };
    if (extractConstUsizeFromBody(body, order_vid)) |const_ord| {
        if (resolveAtomicOrderMacroC(const_ord, slot_kind)) |macro_s| {
            try emitter.print("    {s}{s});\n", .{ stmt_prefix, macro_s });
        } else {
            try emitter.writeAll("    _cx_rt_trap(3u);\n");
        }
        return;
    }
    try emitter.print("    switch ((uint32_t)_v_{d}) {{\n", .{order_vid});
    var ord_code: u64 = 0;
    while (ord_code <= 5) : (ord_code += 1) {
        try emitter.print(
            "    case {d}u: {s}{s}); break;\n",
            .{ ord_code, stmt_prefix, resolveAtomicOrderMacroC(ord_code, slot_kind).? },
        );
    }
    try emitter.writeAll("    default: _cx_rt_trap(3u);\n    }\n");
}

/// Resolves a warning-free `(succ_macro, fail_macro)` pair for `__atomic_compare_exchange_n`.
fn resolveCmpxchgOrderMacrosC(
    succ_code: u64,
    fail_code: u64,
) ?struct { succ_macro: []const u8, fail_macro: []const u8 } {
    if (succ_code > 5 or fail_code > 5) return null;
    if (fail_code == 5) {
        return .{ .succ_macro = "__ATOMIC_SEQ_CST", .fail_macro = "__ATOMIC_SEQ_CST" };
    }
    if (fail_code == 1 or fail_code == 2 or fail_code == 4) {
        const succ_m = switch (succ_code) {
            0, 1, 2 => "__ATOMIC_ACQUIRE",
            3, 4 => "__ATOMIC_ACQ_REL",
            else => "__ATOMIC_SEQ_CST",
        };
        return .{ .succ_macro = succ_m, .fail_macro = "__ATOMIC_ACQUIRE" };
    }
    const succ_m = resolveAtomicOrderMacroC(succ_code, .fence_or_rmw).?;
    return .{ .succ_macro = succ_m, .fail_macro = "__ATOMIC_RELAXED" };
}

/// Emits C99 statements evaluating a `MirOp.intrinsic_op` across all surface and internal intrinsics.
fn emitIntrinsicOpC(
    emitter: *CModuleEmitter,
    body: *const MirBody,
    dst_raw: u32,
    ikind: MirIntrinsicKind,
    inst: mir.MirInst,
) !void {
    const args: []const u32 = if (ikind.hasExtraArgs() and inst.operands.rhs > 0)
        body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]
    else
        &.{};

    switch (ikind) {
        .compile_assert => {
            if (args.len >= 1) {
                try emitter.print("    if ((_v_{d} & 1u) == 0u) _cx_rt_trap(3u);\n", .{args[0]});
            } else {
                try emitter.writeAll("    _cx_rt_trap(3u);\n");
            }
        },
        .compile_error, .abort_vacated_panic => {
            try emitter.writeAll("    _cx_rt_trap(3u);\n");
        },
        .embed_bytes => {
            try emitter.writeAll("    _cx_rt_trap(0u);\n");
        },
        .derive_debug_fmt => {
            if (args.len >= 1) {
                const val_ty = emitter.input.pool.unwrapUnderlyingType(
                    body.getInst(MirValueId.fromInt(args[0])).type_id,
                );
                try emitter.print(
                    "    {{ _cx_rt_buf_t _fb = {{ NULL, 0u, 0u }}; " ++
                        "_cx_fmt_fn_ty_{d}(&_fb, &_v_{d}, 1u << 27, 0xFFFFFFFFu); " ++
                        "_v_{d} = _cx_rt_buf_finish_str(&_fb); }}\n",
                    .{ val_ty.toU32(), args[0], dst_raw },
                );
            }
        },
        .fmt_value => {
            if (args.len >= 3) {
                const val_ty = emitter.input.pool.unwrapUnderlyingType(
                    body.getInst(MirValueId.fromInt(args[0])).type_id,
                );
                try emitter.print(
                    "    {{ _cx_rt_buf_t _fb = {{ NULL, 0u, 0u }}; " ++
                        "_cx_fmt_fn_ty_{d}(&_fb, &_v_{d}, (uint32_t)_v_{d}, (uint32_t)_v_{d}); " ++
                        "_v_{d} = _cx_rt_buf_finish_str(&_fb); }}\n",
                    .{ val_ty.toU32(), args[0], args[1], args[2], dst_raw },
                );
            }
        },
        .size_of => {
            const refl_lay = try emitter.resolver.resolveType(TypeId.fromInt(inst.operands.lhs));
            const dst_c = try formatCType(emitter, inst.type_id);
            defer emitter.allocator.free(dst_c);
            try emitter.print("    _v_{d} = ({s}){d}ull;\n", .{ dst_raw, dst_c, refl_lay.size_bytes });
        },
        .align_of => {
            const refl_lay = try emitter.resolver.resolveType(TypeId.fromInt(inst.operands.lhs));
            const dst_c = try formatCType(emitter, inst.type_id);
            defer emitter.allocator.free(dst_c);
            try emitter.print("    _v_{d} = ({s}){d}ull;\n", .{ dst_raw, dst_c, refl_lay.alignBytes() });
        },
        .type_name => {
            const refl_ty = TypeId.fromInt(inst.operands.lhs);
            var name_buf: [512]u8 = undefined;
            const rendered = emitter.input.pool.formatType(refl_ty, emitter.input.sym_table, &name_buf);
            if (rendered.len == 0) {
                try emitter.print(
                    "    _v_{d}.ptr = (uint8_t *)((uintptr_t)1u); _v_{d}.len = 0u;\n",
                    .{ dst_raw, dst_raw },
                );
            } else {
                try emitter.print(
                    "    _v_{d}.ptr = (uint8_t *)_cx_tyname_{d}; _v_{d}.len = {d}u;\n",
                    .{ dst_raw, refl_ty.toU32(), dst_raw, rendered.len },
                );
            }
        },
        .as_bytes => {
            if (args.len < 1) return;
            const ref_val = MirValueId.fromInt(args[0]);
            const ref_ty = emitter.input.pool.unwrapUnderlyingType(body.getInst(ref_val).type_id);
            const ref_node = emitter.input.pool.getNode(ref_ty);
            const val_ty = if (ref_node.tag == .ref_ty or
                ref_node.tag == .mut_ref_ty or
                ref_node.tag == .raw_ptr_ty)
                emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(ref_node.lhs))
            else
                ref_ty;
            const val_lay = try emitter.resolver.resolveType(val_ty);
            const raw_ptr_expr = if (ref_node.tag == .ref_ty or
                ref_node.tag == .mut_ref_ty or
                ref_node.tag == .raw_ptr_ty)
                try std.fmt.allocPrint(emitter.allocator, "(uint8_t *)_v_{d}", .{args[0]})
            else
                try std.fmt.allocPrint(emitter.allocator, "(uint8_t *)(&_v_{d})", .{args[0]});
            defer emitter.allocator.free(raw_ptr_expr);

            if (resolveSliceRefPointee(emitter, inst.type_id) != null) {
                if (val_lay.size_bytes == 0) {
                    try emitter.print(
                        "    _stmp_{d}.ptr = (uint8_t *)((uintptr_t)1u); _stmp_{d}.len = 0u; _v_{d} = &_stmp_{d};\n",
                        .{ dst_raw, dst_raw, dst_raw, dst_raw },
                    );
                } else {
                    try emitter.print(
                        "    _stmp_{d}.ptr = {s}; _stmp_{d}.len = {d}u; _v_{d} = &_stmp_{d};\n",
                        .{ dst_raw, raw_ptr_expr, dst_raw, val_lay.size_bytes, dst_raw, dst_raw },
                    );
                }
            } else if (val_lay.size_bytes == 0) {
                try emitter.print(
                    "    _v_{d}.ptr = (uint8_t *)((uintptr_t)1u); _v_{d}.len = 0u;\n",
                    .{ dst_raw, dst_raw },
                );
            } else {
                try emitter.print(
                    "    _v_{d}.ptr = {s}; _v_{d}.len = {d}u;\n",
                    .{ dst_raw, raw_ptr_expr, dst_raw, val_lay.size_bytes },
                );
            }
        },
        .bit_cast => {
            if (args.len < 1 or (try isZeroSizedType(emitter, inst.type_id))) return;
            try emitter.print(
                "    memcpy(&_v_{d}, &_v_{d}, sizeof(_v_{d}));\n",
                .{ dst_raw, args[0], dst_raw },
            );
        },
        .from_bytes, .view_bytes => {
            if (args.len < 1) return;
            const is_view = ikind == .view_bytes;
            const src_val = MirValueId.fromInt(args[0]);
            const span_exprs = try formatWireByteSpanExprs(
                emitter,
                body.getInst(src_val).type_id,
                src_val,
            );
            defer emitter.allocator.free(span_exprs.ptr_expr);
            defer emitter.allocator.free(span_exprs.len_expr);

            const opt_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            const opt_node = emitter.input.pool.getNode(opt_ty);
            const some_pay_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(opt_node.lhs));
            const some_node = emitter.input.pool.getNode(some_pay_ty);
            const target_ty = if (is_view and
                (some_node.tag == .ref_ty or some_node.tag == .mut_ref_ty or some_node.tag == .raw_ptr_ty))
                emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(some_node.lhs))
            else
                some_pay_ty;
            const target_lay = try emitter.resolver.resolveType(target_ty);
            const sum_detail = (try emitter.resolver.getSumDetail(opt_ty)) orelse return;
            const pay_access = if (sum_detail.repr == .explicit_tag)
                try std.fmt.allocPrint(emitter.allocator, "_v_{d}._u._v1", .{dst_raw})
            else
                try std.fmt.allocPrint(emitter.allocator, "_v_{d}._pay", .{dst_raw});
            defer emitter.allocator.free(pay_access);
            const dst_str = try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{dst_raw});
            defer emitter.allocator.free(dst_str);

            if (is_view) {
                try emitter.print(
                    "    if (({s}) == {d}u && ({s}) != NULL && (((uintptr_t)({s})) & ({d}u - 1u)) == 0u) {{\n",
                    .{
                        span_exprs.len_expr,
                        target_lay.size_bytes,
                        span_exprs.ptr_expr,
                        span_exprs.ptr_expr,
                        target_lay.alignBytes(),
                    },
                );
                if (!(try isZeroSizedType(emitter, some_pay_ty))) {
                    const some_c = try formatCType(emitter, some_pay_ty);
                    defer emitter.allocator.free(some_c);
                    try emitter.print("    {s} = ({s})({s});\n", .{ pay_access, some_c, span_exprs.ptr_expr });
                }
            } else {
                try emitter.print("    if (({s}) == {d}u) {{\n", .{ span_exprs.len_expr, target_lay.size_bytes });
                if (target_lay.size_bytes > 0) {
                    try emitter.print(
                        "    memcpy(&({s}), {s}, {d}u);\n",
                        .{ pay_access, span_exprs.ptr_expr, target_lay.size_bytes },
                    );
                }
            }
            try emitSumDiscrWriteStmt(emitter, opt_ty, 1, dst_str);
            try emitter.writeAll("    } else {\n");
            try emitSumDiscrWriteStmt(emitter, opt_ty, 0, dst_str);
            try emitter.writeAll("    }\n");
        },
        .drop_trace => {
            if (args.len >= 1) {
                try emitter.print("    _cx_rt_drop_trace((int64_t)_v_{d});\n", .{args[0]});
            }
        },
        .bounds_check => {
            if (args.len < 2) return;
            const idx_val = MirValueId.fromInt(args[0]);
            const len_val = MirValueId.fromInt(args[1]);
            const idx_ty = body.getInst(idx_val).type_id;
            const len_ty = body.getInst(len_val).type_id;
            if (try resolveIntegerInfo(emitter, idx_ty)) |idx_info| {
                if (idx_info.is_signed) {
                    if (idx_info.bits == 128) {
                        try emitter.print("    if (_cx_i128_slt(_v_{d}, _cx_i128_make(0ull, 0ull))) _cx_rt_trap(2u);\n", .{args[0]});
                    } else {
                        try emitter.print("    if (_v_{d} < 0) _cx_rt_trap(2u);\n", .{args[0]});
                    }
                }
            }
            const idx_u128_e = try formatIntAsCxU128Expr(emitter, idx_val, idx_ty);
            defer emitter.allocator.free(idx_u128_e);
            const len_u128_e = try formatIntAsCxU128Expr(emitter, len_val, len_ty);
            defer emitter.allocator.free(len_u128_e);
            try emitter.print(
                "    if (!_cx_u128_ult({s}, {s})) _cx_rt_trap(2u);\n",
                .{ idx_u128_e, len_u128_e },
            );
        },
        .slice_range_check => {
            if (args.len < 3) return;
            const lo_val = MirValueId.fromInt(args[0]);
            const hi_val = MirValueId.fromInt(args[1]);
            const len_val = MirValueId.fromInt(args[2]);
            const lo_ty = body.getInst(lo_val).type_id;
            const hi_ty = body.getInst(hi_val).type_id;
            const len_ty = body.getInst(len_val).type_id;
            if (try resolveIntegerInfo(emitter, lo_ty)) |lo_info| {
                if (lo_info.is_signed) {
                    if (lo_info.bits == 128) {
                        try emitter.print("    if (_cx_i128_slt(_v_{d}, _cx_i128_make(0ull, 0ull))) _cx_rt_trap(2u);\n", .{args[0]});
                    } else {
                        try emitter.print("    if (_v_{d} < 0) _cx_rt_trap(2u);\n", .{args[0]});
                    }
                }
            }
            if (try resolveIntegerInfo(emitter, hi_ty)) |hi_info| {
                if (hi_info.is_signed) {
                    if (hi_info.bits == 128) {
                        try emitter.print("    if (_cx_i128_slt(_v_{d}, _cx_i128_make(0ull, 0ull))) _cx_rt_trap(2u);\n", .{args[1]});
                    } else {
                        try emitter.print("    if (_v_{d} < 0) _cx_rt_trap(2u);\n", .{args[1]});
                    }
                }
            }
            const lo_u128_e = try formatIntAsCxU128Expr(emitter, lo_val, lo_ty);
            defer emitter.allocator.free(lo_u128_e);
            const hi_u128_e = try formatIntAsCxU128Expr(emitter, hi_val, hi_ty);
            defer emitter.allocator.free(hi_u128_e);
            const len_u128_e = try formatIntAsCxU128Expr(emitter, len_val, len_ty);
            defer emitter.allocator.free(len_u128_e);
            try emitter.print(
                "    if (_cx_u128_ult({s}, {s}) || _cx_u128_ult({s}, {s})) _cx_rt_trap(2u);\n",
                .{ hi_u128_e, lo_u128_e, len_u128_e, hi_u128_e },
            );
        },
        .narrow_check, .try_narrow => {
            if (args.len < 3) return;
            const is_try = ikind == .try_narrow;
            const opt_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            const dst_ty = if (is_try) TypeId.fromInt(emitter.input.pool.getNode(opt_ty).lhs) else inst.type_id;
            const dst_unwrapped = emitter.input.pool.unwrapUnderlyingType(dst_ty);
            const src_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
            const min_ty = body.getInst(MirValueId.fromInt(args[1])).type_id;
            const max_ty = body.getInst(MirValueId.fromInt(args[2])).type_id;
            const src_info = (try resolveIntegerInfo(emitter, src_ty)) orelse return;
            const dst_info = (try resolveIntegerInfo(emitter, dst_ty)) orelse return;

            const min_e = try formatAsCxI128Expr(emitter, MirValueId.fromInt(args[1]), min_ty);
            defer emitter.allocator.free(min_e);
            const max_e = try formatAsCxI128Expr(emitter, MirValueId.fromInt(args[2]), max_ty);
            defer emitter.allocator.free(max_e);
            const tmp_id = emitter.nextTempId();
            try emitter.print(
                "    cx_i128 _nmin_{d} = {s}; cx_i128 _nmax_{d} = {s}; uint8_t _nok_{d} = 0u;\n",
                .{ tmp_id, min_e, tmp_id, max_e, tmp_id },
            );

            const is_unrefined_u128 = dst_unwrapped == .u128_ty and
                emitter.input.pool.getRefinementBounds(dst_ty) == null;
            if (src_info.is_signed) {
                const src_e = try formatAsCxI128Expr(emitter, MirValueId.fromInt(args[0]), src_ty);
                defer emitter.allocator.free(src_e);
                try emitter.print("    cx_i128 _nsrc_{d} = {s};\n", .{ tmp_id, src_e });
                if (is_unrefined_u128) {
                    try emitter.print(
                        "    _nok_{d} = !_cx_i128_slt(_nsrc_{d}, _cx_i128_make(0ull, 0ull)) ? 1u : 0u;\n",
                        .{ tmp_id, tmp_id },
                    );
                } else {
                    try emitter.print(
                        "    _nok_{d} = (!_cx_i128_slt(_nsrc_{d}, _nmin_{d}) && " ++
                            "!_cx_i128_slt(_nmax_{d}, _nsrc_{d})) ? 1u : 0u;\n",
                        .{ tmp_id, tmp_id, tmp_id, tmp_id, tmp_id },
                    );
                }
            } else {
                if (src_info.bits == 128) {
                    try emitter.print("    cx_u128 _nusrc_{d} = _v_{d};\n", .{ tmp_id, args[0] });
                } else {
                    try emitter.print(
                        "    cx_u128 _nusrc_{d} = _cx_u128_make((uint64_t)_v_{d}, 0ull);\n",
                        .{ tmp_id, args[0] },
                    );
                }
                if (is_unrefined_u128) {
                    try emitter.print("    _nok_{d} = 1u;\n", .{tmp_id});
                } else {
                    try emitter.print(
                        "    if (!_cx_i128_slt(_nmax_{d}, _cx_i128_make(0ull, 0ull))) {{\n" ++
                            "      cx_u128 _numin_{d} = _cx_i128_slt(_nmin_{d}, _cx_i128_make(0ull, 0ull)) ? " ++
                            "_cx_u128_make(0ull, 0ull) : _cx_as_u128(_nmin_{d});\n" ++
                            "      _nok_{d} = (!_cx_u128_ult(_nusrc_{d}, _numin_{d}) && " ++
                            "!_cx_u128_ult(_cx_as_u128(_nmax_{d}), _nusrc_{d})) ? 1u : 0u;\n    }}\n",
                        .{ tmp_id, tmp_id, tmp_id, tmp_id, tmp_id, tmp_id, tmp_id, tmp_id, tmp_id },
                    );
                }
            }

            const conv_c = try formatCType(emitter, dst_ty);
            defer emitter.allocator.free(conv_c);
            const conv_expr = if (dst_info.bits == 128)
                (if (src_info.is_signed)
                    (if (dst_info.is_signed)
                        try std.fmt.allocPrint(emitter.allocator, "_nsrc_{d}", .{tmp_id})
                    else
                        try std.fmt.allocPrint(emitter.allocator, "_cx_as_u128(_nsrc_{d})", .{tmp_id}))
                else
                    (if (dst_info.is_signed)
                        try std.fmt.allocPrint(emitter.allocator, "_cx_as_i128(_nusrc_{d})", .{tmp_id})
                    else
                        try std.fmt.allocPrint(emitter.allocator, "_nusrc_{d}", .{tmp_id})))
            else if (src_info.is_signed)
                try std.fmt.allocPrint(
                    emitter.allocator,
                    "({s})_cx_u128_lo(_cx_as_u128(_nsrc_{d}))",
                    .{ conv_c, tmp_id },
                )
            else
                try std.fmt.allocPrint(
                    emitter.allocator,
                    "({s})_cx_u128_lo(_nusrc_{d})",
                    .{ conv_c, tmp_id },
                );
            defer emitter.allocator.free(conv_expr);

            if (!is_try) {
                try emitter.print(
                    "    if (!_nok_{d}) _cx_rt_trap(2u);\n    _v_{d} = {s};\n",
                    .{ tmp_id, dst_raw, conv_expr },
                );
            } else {
                const sum_detail = (try emitter.resolver.getSumDetail(opt_ty)) orelse return;
                const pay_access = if (sum_detail.repr == .explicit_tag)
                    try std.fmt.allocPrint(emitter.allocator, "_v_{d}._u._v1", .{dst_raw})
                else
                    try std.fmt.allocPrint(emitter.allocator, "_v_{d}._pay", .{dst_raw});
                defer emitter.allocator.free(pay_access);
                const dst_str = try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{dst_raw});
                defer emitter.allocator.free(dst_str);

                try emitter.print("    if (_nok_{d}) {{\n", .{tmp_id});
                if (!(try isZeroSizedType(emitter, dst_ty))) {
                    try emitter.print("    {s} = {s};\n", .{ pay_access, conv_expr });
                }
                try emitSumDiscrWriteStmt(emitter, opt_ty, 1, dst_str);
                try emitter.writeAll("    } else {\n");
                try emitSumDiscrWriteStmt(emitter, opt_ty, 0, dst_str);
                try emitter.writeAll("    }\n");
            }
        },
        .zero_pad => {
            switch (try lowerPlaceC(emitter, body, PlaceId.fromInt(inst.operands.lhs))) {
                .const_len => {},
                .lvalue_expr => |lv| {
                    defer emitter.allocator.free(lv.expr_str);
                    if (!(try isZeroSizedType(emitter, lv.pointee_ty))) {
                        try emitter.print(
                            "    memset(&({s}), 0, sizeof({s}));\n",
                            .{ lv.expr_str, lv.expr_str },
                        );
                    }
                },
            }
        },
        .drop_in_place, .drop_if_live => {
            switch (try lowerPlaceC(emitter, body, PlaceId.fromInt(inst.operands.lhs))) {
                .const_len => {},
                .lvalue_expr => |lv| {
                    defer emitter.allocator.free(lv.expr_str);
                    const dropped_ty = emitter.input.pool.unwrapUnderlyingType(
                        if (inst.type_id != .unit_ty and !inst.type_id.isError())
                            inst.type_id
                        else
                            lv.pointee_ty,
                    );
                    if (emitter.drop_type_set.contains(dropped_ty.toU32()) and
                        !(try isZeroSizedType(emitter, dropped_ty)))
                    {
                        if (ikind == .drop_if_live) {
                            if (inst.operands.rhs != mir.NONE_U32) {
                                try emitter.print(
                                    "    if ((_v_{d} & 1u) != 0u) _cx_drop_ty_{d}(&({s}));\n",
                                    .{ inst.operands.rhs, dropped_ty.toU32(), lv.expr_str },
                                );
                            }
                        } else {
                            try emitter.print(
                                "    _cx_drop_ty_{d}(&({s}));\n",
                                .{ dropped_ty.toU32(), lv.expr_str },
                            );
                        }
                    }
                },
            }
        },
        .ghost_storage_free => {},
        .atomic_fence => {
            try emitSingleOrderAtomicStmtC(
                emitter,
                body,
                .fence_or_rmw,
                if (args.len >= 1) args[0] else null,
                "__atomic_thread_fence(",
            );
        },
        .atomic_load => {
            if (args.len < 1 or (try isZeroSizedType(emitter, inst.type_id))) return;
            const stmt_pfx = try std.fmt.allocPrint(
                emitter.allocator,
                "_v_{d} = __atomic_load_n(_v_{d}, ",
                .{ dst_raw, args[0] },
            );
            defer emitter.allocator.free(stmt_pfx);
            try emitSingleOrderAtomicStmtC(
                emitter,
                body,
                .load_op,
                if (args.len >= 2) args[1] else null,
                stmt_pfx,
            );
        },
        .atomic_store => {
            if (args.len < 2) return;
            const val_ty = body.getInst(MirValueId.fromInt(args[1])).type_id;
            if (try isZeroSizedType(emitter, val_ty)) return;
            const stmt_pfx = try std.fmt.allocPrint(
                emitter.allocator,
                "__atomic_store_n(_v_{d}, _v_{d}, ",
                .{ args[0], args[1] },
            );
            defer emitter.allocator.free(stmt_pfx);
            try emitSingleOrderAtomicStmtC(
                emitter,
                body,
                .store_op,
                if (args.len >= 3) args[2] else null,
                stmt_pfx,
            );
        },
        .atomic_rmw_add => {
            if (args.len < 2 or (try isZeroSizedType(emitter, inst.type_id))) return;
            const stmt_pfx = try std.fmt.allocPrint(
                emitter.allocator,
                "_v_{d} = __atomic_fetch_add(_v_{d}, _v_{d}, ",
                .{ dst_raw, args[0], args[1] },
            );
            defer emitter.allocator.free(stmt_pfx);
            try emitSingleOrderAtomicStmtC(
                emitter,
                body,
                .fence_or_rmw,
                if (args.len >= 3) args[2] else null,
                stmt_pfx,
            );
        },
        .atomic_rmw_sub => {
            if (args.len < 2 or (try isZeroSizedType(emitter, inst.type_id))) return;
            const stmt_pfx = try std.fmt.allocPrint(
                emitter.allocator,
                "_v_{d} = __atomic_fetch_sub(_v_{d}, _v_{d}, ",
                .{ dst_raw, args[0], args[1] },
            );
            defer emitter.allocator.free(stmt_pfx);
            try emitSingleOrderAtomicStmtC(
                emitter,
                body,
                .fence_or_rmw,
                if (args.len >= 3) args[2] else null,
                stmt_pfx,
            );
        },
        .atomic_rmw_xchg => {
            if (args.len < 2 or (try isZeroSizedType(emitter, inst.type_id))) return;
            const stmt_pfx = try std.fmt.allocPrint(
                emitter.allocator,
                "_v_{d} = __atomic_exchange_n(_v_{d}, _v_{d}, ",
                .{ dst_raw, args[0], args[1] },
            );
            defer emitter.allocator.free(stmt_pfx);
            try emitSingleOrderAtomicStmtC(
                emitter,
                body,
                .fence_or_rmw,
                if (args.len >= 3) args[2] else null,
                stmt_pfx,
            );
        },
        .atomic_cmpxchg => {
            if (args.len < 3) return;
            const val_ty = body.getInst(MirValueId.fromInt(args[1])).type_id;
            const val_c = try formatCType(emitter, val_ty);
            defer emitter.allocator.free(val_c);
            const tmp_id = emitter.nextTempId();
            const const_succ: ?u64 = if (args.len >= 4) extractConstUsizeFromBody(body, args[3]) else 5;
            const const_fail: ?u64 = if (args.len >= 5) extractConstUsizeFromBody(body, args[4]) else (const_succ orelse null);
            const weak_expr: []u8 = if (args.len >= 6) blk_wk: {
                if (extractConstWeakFromBody(body, args[5])) |is_wk| {
                    break :blk_wk try emitter.allocator.dupe(u8, if (is_wk) "true" else "false");
                }
                break :blk_wk try std.fmt.allocPrint(emitter.allocator, "((bool)(_v_{d} != 0))", .{args[5]});
            } else try emitter.allocator.dupe(u8, "false");
            defer emitter.allocator.free(weak_expr);
            if (const_succ != null and const_fail != null) {
                if (resolveCmpxchgOrderMacrosC(const_succ.?, const_fail.?)) |pair| {
                    try emitter.print(
                        "    {{ {s} _cexp_{d} = _v_{d}; bool _cok_{d} = __atomic_compare_exchange_n(" ++
                            "_v_{d}, &_cexp_{d}, _v_{d}, {s}, {s}, {s}); " ++
                            "_v_{d}._f0 = _cexp_{d}; _v_{d}._f1 = _cok_{d} ? 1u : 0u; }}\n",
                        .{
                            val_c,   tmp_id,  args[1],   tmp_id,          args[0],
                            tmp_id,  args[2], weak_expr, pair.succ_macro, pair.fail_macro,
                            dst_raw, tmp_id,  dst_raw,   tmp_id,
                        },
                    );
                } else {
                    try emitter.writeAll("    _cx_rt_trap(3u);\n");
                }
            } else {
                const succ_expr = if (args.len >= 4)
                    try std.fmt.allocPrint(emitter.allocator, "((uint32_t)_v_{d})", .{args[3]})
                else
                    try emitter.allocator.dupe(u8, "5u");
                defer emitter.allocator.free(succ_expr);
                const fail_expr = if (args.len >= 5)
                    try std.fmt.allocPrint(emitter.allocator, "((uint32_t)_v_{d})", .{args[4]})
                else
                    try emitter.allocator.dupe(u8, succ_expr);
                defer emitter.allocator.free(fail_expr);
                try emitter.print(
                    "    {{ uint32_t _cso_{d} = {s}; uint32_t _cfo_{d} = {s}; bool _cwk_{d} = {s}; " ++
                        "if (_cso_{d} > 5u || _cfo_{d} > 5u) _cx_rt_trap(3u); " ++
                        "{s} _cexp_{d} = _v_{d}; bool _cok_{d} = false;\n",
                    .{
                        tmp_id, succ_expr, tmp_id, fail_expr, tmp_id,  weak_expr,
                        tmp_id, tmp_id,    val_c,  tmp_id,    args[1], tmp_id,
                    },
                );
                try emitter.print(
                    "      if (_cfo_{d} == 5u) {{ _cok_{d} = __atomic_compare_exchange_n(" ++
                        "_v_{d}, &_cexp_{d}, _v_{d}, _cwk_{d}, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST); }} " ++
                        "else if (_cfo_{d} == 1u || _cfo_{d} == 2u || _cfo_{d} == 4u) {{\n" ++
                        "        if (_cso_{d} == 5u) _cok_{d} = __atomic_compare_exchange_n(" ++
                        "_v_{d}, &_cexp_{d}, _v_{d}, _cwk_{d}, __ATOMIC_SEQ_CST, __ATOMIC_ACQUIRE);\n" ++
                        "        else if (_cso_{d} >= 3u) _cok_{d} = __atomic_compare_exchange_n(" ++
                        "_v_{d}, &_cexp_{d}, _v_{d}, _cwk_{d}, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);\n" ++
                        "        else _cok_{d} = __atomic_compare_exchange_n(" ++
                        "_v_{d}, &_cexp_{d}, _v_{d}, _cwk_{d}, __ATOMIC_ACQUIRE, __ATOMIC_ACQUIRE);\n" ++
                        "      }} else {{\n",
                    .{
                        tmp_id,  tmp_id,  args[0], tmp_id, args[2], tmp_id,
                        tmp_id,  tmp_id,  tmp_id,  tmp_id, tmp_id,  args[0],
                        tmp_id,  args[2], tmp_id,  tmp_id, tmp_id,  args[0],
                        tmp_id,  args[2], tmp_id,  tmp_id, args[0], tmp_id,
                        args[2], tmp_id,
                    },
                );
                var succ_ord: u64 = 0;
                while (succ_ord <= 5) : (succ_ord += 1) {
                    const kw = if (succ_ord == 0) "        if" else "        else if";
                    try emitter.print(
                        "{s} (_cso_{d} == {d}u) _cok_{d} = __atomic_compare_exchange_n(" ++
                            "_v_{d}, &_cexp_{d}, _v_{d}, _cwk_{d}, {s}, __ATOMIC_RELAXED);\n",
                        .{
                            kw,
                            tmp_id,
                            succ_ord,
                            tmp_id,
                            args[0],
                            tmp_id,
                            args[2],
                            tmp_id,
                            resolveAtomicOrderMacroC(succ_ord, .fence_or_rmw).?,
                        },
                    );
                }
                try emitter.print(
                    "      }} _v_{d}._f0 = _cexp_{d}; _v_{d}._f1 = _cok_{d} ? 1u : 0u; }}\n",
                    .{ dst_raw, tmp_id, dst_raw, tmp_id },
                );
            }
        },
        .simd_splat => {
            if (args.len < 1) return;
            const vec_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            const vec_node = emitter.input.pool.getNode(vec_ty);
            const lane_count: u64 = vec_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            var lane_i: u64 = 0;
            while (lane_i < lane_count) : (lane_i += 1) {
                try emitter.print("    _v_{d}._elems[{d}u] = _v_{d};\n", .{ dst_raw, lane_i, args[0] });
            }
        },
        .simd_add, .simd_sub, .simd_mul => {
            if (args.len < 2) return;
            const vec_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            const vec_node = emitter.input.pool.getNode(vec_ty);
            const lane_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(vec_node.lhs));
            const lane_count: u64 = vec_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            const op_tok = switch (ikind) {
                .simd_add => "+",
                .simd_sub => "-",
                else => "*",
            };
            if (lane_ty == .f32_ty or lane_ty == .f64_ty) {
                var lane_i: u64 = 0;
                while (lane_i < lane_count) : (lane_i += 1) {
                    try emitter.print(
                        "    _v_{d}._elems[{d}u] = _v_{d}._elems[{d}u] {s} _v_{d}._elems[{d}u];\n",
                        .{ dst_raw, lane_i, args[0], lane_i, op_tok, args[1], lane_i },
                    );
                }
            } else if (try resolveIntegerInfo(emitter, lane_ty)) |l_info| {
                const ulane_c = resolveUnsignedCTypeForBits(l_info.bits);
                const slane_c = try formatCType(emitter, lane_ty);
                defer emitter.allocator.free(slane_c);
                var lane_i: u64 = 0;
                while (lane_i < lane_count) : (lane_i += 1) {
                    try emitter.print(
                        "    _v_{d}._elems[{d}u] = ({s})((({s})_v_{d}._elems[{d}u]) {s} (({s})_v_{d}._elems[{d}u]));\n",
                        .{ dst_raw, lane_i, slane_c, ulane_c, args[0], lane_i, op_tok, ulane_c, args[1], lane_i },
                    );
                }
            }
        },
        .simd_reduce_add => {
            if (args.len < 1) return;
            const vec_ty = emitter.input.pool.unwrapUnderlyingType(body.getInst(MirValueId.fromInt(args[0])).type_id);
            const vec_node = emitter.input.pool.getNode(vec_ty);
            const lane_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(vec_node.lhs));
            const lane_count: u64 = vec_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            if (lane_ty == .f32_ty or lane_ty == .f64_ty) {
                const flt_c = if (lane_ty == .f32_ty) "float" else "double";
                const tmp_id = emitter.nextTempId();
                try emitter.print("    {{ {s} _racc_{d} = ({s})0.0;\n", .{ flt_c, tmp_id, flt_c });
                var lane_i: u64 = 0;
                while (lane_i < lane_count) : (lane_i += 1) {
                    try emitter.print("      _racc_{d} += _v_{d}._elems[{d}u];\n", .{ tmp_id, args[0], lane_i });
                }
                try emitter.print("      _v_{d} = _racc_{d}; }}\n", .{ dst_raw, tmp_id });
            } else if (try resolveIntegerInfo(emitter, lane_ty)) |l_info| {
                const ulane_c = resolveUnsignedCTypeForBits(l_info.bits);
                const slane_c = try formatCType(emitter, inst.type_id);
                defer emitter.allocator.free(slane_c);
                const tmp_id = emitter.nextTempId();
                try emitter.print("    {{ {s} _racc_{d} = 0u;\n", .{ ulane_c, tmp_id });
                var lane_i: u64 = 0;
                while (lane_i < lane_count) : (lane_i += 1) {
                    try emitter.print(
                        "      _racc_{d} = ({s})(_racc_{d} + ({s})_v_{d}._elems[{d}u]);\n",
                        .{ tmp_id, ulane_c, tmp_id, ulane_c, args[0], lane_i },
                    );
                }
                try emitter.print("      _v_{d} = ({s})_racc_{d}; }}\n", .{ dst_raw, slane_c, tmp_id });
            }
        },
        .poll_reload => {
            if (emitter.input.is_dev_got_enabled) {
                try emitter.print(
                    "    if (_cx_reload_ctrl.pending_patch_gen > _cx_reload_ctrl.applied_patch_gen) {{ " ++
                        "_cx_reload_ctrl.applied_patch_gen = _cx_reload_ctrl.pending_patch_gen; _v_{d} = 1u; }} " ++
                        "else {{ _v_{d} = 0u; }}\n",
                    .{ dst_raw, dst_raw },
                );
            } else {
                try emitter.print("    _v_{d} = 0u;\n", .{dst_raw});
            }
        },
        .panic => {
            if (emitter.cfg.target.isFreestanding() or
                (emitter.is_in_c_abi_body and !emitter.input.is_oracle_trace_enabled))
            {
                try emitter.writeAll("    __builtin_trap();\n");
            } else if (args.len >= 1) {
                const msg_ty = emitter.input.pool.unwrapUnderlyingType(
                    body.getInst(MirValueId.fromInt(args[0])).type_id,
                );
                if (msg_ty == .fmt_args_ty) {
                    try emitter.print("    _cx_rt_panic_fmt_args(&_v_{d});\n", .{args[0]});
                } else {
                    try emitter.print("    _cx_rt_panic(_v_{d}.ptr, (size_t)_v_{d}.len);\n", .{ args[0], args[0] });
                }
            } else {
                try emitter.writeAll("    _cx_rt_panic((const uint8_t *)0, 0u);\n");
            }
        },
        .trap => {
            if (emitter.cfg.target.isFreestanding() or
                (emitter.is_in_c_abi_body and !emitter.input.is_oracle_trace_enabled))
            {
                try emitter.writeAll("    __builtin_trap();\n");
            } else {
                try emitter.writeAll("    _cx_rt_trap(0u);\n");
            }
        },
        .sys_write => {
            if (args.len < 2) return;
            const buf_val = MirValueId.fromInt(args[1]);
            const span_exprs = try formatWireByteSpanExprs(
                emitter,
                body.getInst(buf_val).type_id,
                buf_val,
            );
            defer emitter.allocator.free(span_exprs.ptr_expr);
            defer emitter.allocator.free(span_exprs.len_expr);
            const dst_c = try formatCType(emitter, inst.type_id);
            defer emitter.allocator.free(dst_c);
            try emitter.print(
                "    _v_{d} = ({s})_cx_rt_sys_write((int32_t)_v_{d}, {s}, {s});\n",
                .{ dst_raw, dst_c, args[0], span_exprs.ptr_expr, span_exprs.len_expr },
            );
        },
        .sys_exit => {
            if (args.len >= 1) {
                try emitter.print("    _cx_rt_sys_exit((int32_t)_v_{d});\n", .{args[0]});
            } else {
                try emitter.writeAll("    _cx_rt_sys_exit(0);\n");
            }
        },
        .subslice_make => {
            if (args.len < 3) return;
            const base_val = MirValueId.fromInt(args[0]);
            const base_ty = emitter.input.pool.unwrapUnderlyingType(body.getInst(base_val).type_id);
            const base_node = emitter.input.pool.getNode(base_ty);
            const lo_expr = try formatSsaIndexUsizeExpr(emitter, body, MirValueId.fromInt(args[1]));
            defer emitter.allocator.free(lo_expr);
            const hi_expr = try formatSsaIndexUsizeExpr(emitter, body, MirValueId.fromInt(args[2]));
            defer emitter.allocator.free(hi_expr);

            const base_ptr_expr: []u8 = if (base_ty == .str_ty or
                base_node.tag == .slice_ty or
                base_node.tag == .soa_slice_ty)
                try std.fmt.allocPrint(emitter.allocator, "((uintptr_t)(_v_{d}.ptr))", .{args[0]})
            else if (base_node.tag == .ref_ty or
                base_node.tag == .mut_ref_ty or
                base_node.tag == .raw_ptr_ty)
            blk_ref: {
                const pt_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(base_node.lhs));
                const pt_tag = emitter.input.pool.getNode(pt_ty).tag;
                if (pt_ty == .str_ty or pt_tag == .slice_ty or pt_tag == .soa_slice_ty) {
                    break :blk_ref try std.fmt.allocPrint(
                        emitter.allocator,
                        "((uintptr_t)(_v_{d}->ptr))",
                        .{args[0]},
                    );
                }
                break :blk_ref try std.fmt.allocPrint(emitter.allocator, "((uintptr_t)_v_{d})", .{args[0]});
            } else if (try isZeroSizedType(emitter, base_ty))
                try emitter.allocator.dupe(u8, "((uintptr_t)1u)")
            else
                try std.fmt.allocPrint(emitter.allocator, "((uintptr_t)(&_v_{d}._elems[0]))", .{args[0]});
            defer emitter.allocator.free(base_ptr_expr);

            const sl_ref_pt = resolveSliceRefPointee(emitter, inst.type_id);
            const sl_ty = sl_ref_pt orelse emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            const elem_ty = if (sl_ty == .str_ty)
                TypeId.u8_ty
            else
                emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(emitter.input.pool.getNode(sl_ty).lhs));
            const elem_lay = try emitter.resolver.resolveType(elem_ty);
            const elem_ptr_c: []u8 = if (sl_ty == .str_ty or (try isZeroSizedType(emitter, elem_ty)))
                try emitter.allocator.dupe(u8, "uint8_t *")
            else blk_ep: {
                const elem_c = try formatCType(emitter, elem_ty);
                defer emitter.allocator.free(elem_c);
                break :blk_ep try std.fmt.allocPrint(emitter.allocator, "{s} *", .{elem_c});
            };
            defer emitter.allocator.free(elem_ptr_c);

            const usize_c = if (emitter.cfg.target.ptrBytes() == 4) "uint32_t" else "uint64_t";
            if (sl_ref_pt != null) {
                try emitter.print(
                    "    _stmp_{d}.ptr = ({s})({s} + ((uintptr_t)({s}) * (uintptr_t){d}u)); " ++
                        "_stmp_{d}.len = ({s})(({s}) - ({s})); _v_{d} = &_stmp_{d};\n",
                    .{
                        dst_raw,               elem_ptr_c, base_ptr_expr, lo_expr,
                        elem_lay.stride_bytes, dst_raw,    usize_c,       hi_expr,
                        lo_expr,               dst_raw,    dst_raw,
                    },
                );
            } else {
                try emitter.print(
                    "    _v_{d}.ptr = ({s})({s} + ((uintptr_t)({s}) * (uintptr_t){d}u)); " ++
                        "_v_{d}.len = ({s})(({s}) - ({s}));\n",
                    .{
                        dst_raw,               elem_ptr_c, base_ptr_expr, lo_expr,
                        elem_lay.stride_bytes, dst_raw,    usize_c,       hi_expr,
                        lo_expr,
                    },
                );
            }
        },
        .ctx_get => {
            if (args.len < 1 or (try isZeroSizedType(emitter, inst.type_id))) return;
            if (type_system.ContextFieldLayout.resolveRefPointee(
                emitter.input.pool,
                emitter.input.sym_table,
                inst.type_id,
            )) |ctx_pointee| {
                const dst_c = try formatCType(emitter, inst.type_id);
                defer emitter.allocator.free(dst_c);
                if (!(try isZeroSizedType(emitter, ctx_pointee))) {
                    const ctx_lay = try emitter.resolver.resolveType(ctx_pointee);
                    try emitter.print(
                        "    memset(&_ctx_snap_{d}, 0, sizeof(_ctx_snap_{d}));\n",
                        .{ dst_raw, dst_raw },
                    );
                    var decl_ord: u32 = 0;
                    while (decl_ord < ctx_lay.aux_len and decl_ord < 10) : (decl_ord += 1) {
                        const fld = emitter.resolver.fields_by_decl.items[ctx_lay.aux_start + decl_ord];
                        if (fld.size_bytes == 0 or fld.size_bytes > emitter.ctx_slot_stride_bytes) continue;
                        try emitter.print(
                            "    memcpy(&_ctx_snap_{d}._f{d}, &_cx_tls_ctx[{d}u * {d}u], {d}u);\n",
                            .{ dst_raw, decl_ord, decl_ord, emitter.ctx_slot_stride_bytes, fld.size_bytes },
                        );
                    }
                }
                try emitter.print("    _v_{d} = ({s})&_ctx_snap_{d};\n", .{ dst_raw, dst_c, dst_raw });
                return;
            }
            try emitter.print(
                "    memcpy(&_v_{d}, &_cx_tls_ctx[(((size_t)_v_{d}) % 10u) * {d}u], sizeof(_v_{d}));\n",
                .{ dst_raw, args[0], emitter.ctx_slot_stride_bytes, dst_raw },
            );
        },
        .ctx_set => {
            if (args.len < 2) return;
            if (try isZeroSizedType(emitter, body.getInst(MirValueId.fromInt(args[1])).type_id)) return;
            try emitter.print(
                "    memcpy(&_cx_tls_ctx[(((size_t)_v_{d}) % 10u) * {d}u], &_v_{d}, sizeof(_v_{d}));\n",
                .{ args[0], emitter.ctx_slot_stride_bytes, args[1], args[1] },
            );
        },
        .ghost_ctx_region_push, .ghost_ctx_region_pop => {},
        .async_future_make => {
            if (!emitter.has_async_ops or args.len < 3) return;
            try emitAsyncFutureMakeC(emitter, body, dst_raw, inst.type_id, args);
        },
        .async_task_group_enter => {
            if (!emitter.has_async_ops) return;
            try emitter.print(
                "    {{ void *_gp = _cx_async_group_enter(); memcpy(&_v_{d}, &_gp, sizeof(void *)); }}\n",
                .{dst_raw},
            );
        },
        .async_spawn => {
            if (!emitter.has_async_ops or args.len < 3) return;
            const fut_ty = emitter.input.pool.unwrapUnderlyingType(
                body.getInst(MirValueId.fromInt(args[2])).type_id,
            );
            const out_ty = emitter.input.pool.unwrapUnderlyingType(
                emitter.input.pool.getFutureOutputType(fut_ty) orelse .unit_ty,
            );
            const out_lay = try emitter.resolver.resolveType(out_ty);
            var err_fn_buf: [64]u8 = undefined;
            const err_fn_str: []const u8 = if (emitter.res_err_check_set.contains(out_ty.toU32()))
                try std.fmt.bufPrint(&err_fn_buf, "_cx_is_err_ty_{d}", .{out_ty.toU32()})
            else
                "NULL";
            try emitter.print(
                "    {{ void *_gp = NULL; memcpy(&_gp, _v_{d}, sizeof(void *)); " ++
                    "void *_hp = _cx_async_spawn(_gp, &_v_{d}, {d}u, {s}); " ++
                    "memcpy(&_v_{d}, &_hp, sizeof(void *)); }}\n",
                .{ args[1], args[2], out_lay.size_bytes, err_fn_str, dst_raw },
            );
        },
        .async_join => {
            if (!emitter.has_async_ops or args.len < 1) return;
            const fut_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            const out_ty = emitter.input.pool.getFutureOutputType(fut_ty) orelse .unit_ty;
            const out_lay = try emitter.resolver.resolveType(out_ty);
            try emitter.print(
                "    {{ void *_hp = NULL; memcpy(&_hp, &_v_{d}, sizeof(void *)); " ++
                    "memset(&_v_{d}, 0, sizeof(_v_{d})); _v_{d}._handle = _hp; " ++
                    "_v_{d}._kind = 3u; _v_{d}._out_sz = {d}u; }}\n",
                .{ args[0], dst_raw, dst_raw, dst_raw, dst_raw, dst_raw, out_lay.size_bytes },
            );
        },
        .async_cancel => {
            if (!emitter.has_async_ops or args.len < 1) return;
            const ret_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
            if (args.len >= 2 or ret_ty == .bool_ty) {
                try emitter.print(
                    "    {{ void *_gp = NULL; memcpy(&_gp, _v_{d}, sizeof(void *)); " ++
                        "_v_{d} = (_gp != NULL && ((_cx_task_group_t *)_gp)->is_canceled) ? 1u : 0u; }}\n",
                    .{ args[0], dst_raw },
                );
            } else if (emitter.input.pool.isFutureType(ret_ty)) {
                try emitter.print(
                    "    {{ void *_hp = NULL; memcpy(&_hp, &_v_{d}, sizeof(void *)); " ++
                        "memset(&_v_{d}, 0, sizeof(_v_{d})); _v_{d}._handle = _hp; _v_{d}._kind = 4u; }}\n",
                    .{ args[0], dst_raw, dst_raw, dst_raw, dst_raw },
                );
            } else {
                try emitter.print(
                    "    {{ void *_gp = NULL; memcpy(&_gp, _v_{d}, sizeof(void *)); " ++
                        "_cx_async_group_cancel_all((_cx_task_group_t *)_gp); }}\n",
                    .{args[0]},
                );
            }
        },
        .async_task_group_exit => {
            if (!emitter.has_async_ops or args.len < 1) return;
            try emitAsyncTaskGroupExitC(emitter, body, args[0]);
        },
        .async_yield => {
            if (!emitter.has_async_ops) return;
            try emitter.print(
                "    memset(&_v_{d}, 0, sizeof(_v_{d})); _v_{d}._kind = 2u; _v_{d}._aux = 0u;\n",
                .{ dst_raw, dst_raw, dst_raw, dst_raw },
            );
        },
        .async_block_on => {
            if (!emitter.has_async_ops or args.len < 1) return;
            if (try isZeroSizedType(emitter, inst.type_id)) {
                try emitter.print("    _cx_async_block_on(&_v_{d}, NULL);\n", .{args[0]});
            } else {
                try emitter.print("    _cx_async_block_on(&_v_{d}, &_v_{d});\n", .{ args[0], dst_raw });
            }
        },
    }
}

/// Returns `true` when `cand_i` matches an indirect `async_future_make` signature.
fn isCompatibleIndirectAsyncCandidateC(
    emitter: *const CModuleEmitter,
    caller_body: *const MirBody,
    cand_i: u32,
    callee_ty: TypeId,
    out_ty: TypeId,
    formal_args: []const u32,
) bool {
    const pool = emitter.input.pool;
    const cand_body = &emitter.input.bodies[cand_i];
    if (!cand_body.is_async) return false;
    if (pool.unwrapUnderlyingType(cand_body.ret_ty) != out_ty) return false;

    const is_closure = !callee_ty.isPrimitiveOrSentinel() and pool.getNode(callee_ty).tag == .closure_ty;
    const sig_opt = pool.getFnSignatureView(callee_ty);
    if (sig_opt) |sv| {
        if (sv.paramCount() != formal_args.len) return false;
    }

    var capture_count: usize = 0;
    if (is_closure) {
        const expected_three_word = codegen_abi.isThreeWordClosureType(pool, callee_ty);
        var matched_thunk: ?ClosureThunkSpec = null;
        for (emitter.closure_thunks.items) |cand_thunk| {
            if (cand_thunk.target_body_idx == cand_i) {
                matched_thunk = cand_thunk;
                break;
            }
        }
        const thunk = matched_thunk orelse return false;
        if (thunk.is_three_word != expected_three_word) return false;
        capture_count = thunk.capture_types.len;
        if (cand_body.param_count != capture_count + formal_args.len) return false;
    } else {
        for (emitter.closure_thunks.items) |cand_thunk| {
            if (cand_thunk.target_body_idx == cand_i and cand_thunk.capture_types.len > 0) return false;
        }
        if (cand_body.param_count != formal_args.len) return false;
    }

    for (formal_args, 0..) |arg_raw, arg_i| {
        const param_idx = 1 + capture_count + arg_i;
        if (param_idx >= cand_body.locals.items.len or arg_raw >= caller_body.insts.len) return false;
        const param_decl = cand_body.locals.items[param_idx];
        const param_mode = param_decl.mode();
        if (sig_opt) |sv| {
            if (sv.getParamMode(arg_i) != param_mode) return false;
        }
        const cand_param_ty = pool.unwrapUnderlyingType(param_decl.type_id);
        const caller_arg_ty = pool.unwrapUnderlyingType(caller_body.insts.get(arg_raw).type_id);
        if (param_mode == .inout_mode or param_mode == .set_mode) {
            if (caller_arg_ty.isPrimitiveOrSentinel()) return false;
            const arg_node = pool.getNode(caller_arg_ty);
            if (arg_node.tag != .ref_ty and arg_node.tag != .mut_ref_ty and arg_node.tag != .raw_ptr_ty) {
                return false;
            }
            if (pool.unwrapUnderlyingType(TypeId.fromInt(arg_node.lhs)) != cand_param_ty) return false;
        } else {
            if (caller_arg_ty != cand_param_ty) return false;
        }
    }
    return true;
}

/// Emits C99 statements populating `target_b`'s coroutine frame parameters & closure captures into `_nfr`.
fn emitPopulateCoroFrameArgsC(
    emitter: *CModuleEmitter,
    caller_body: *const MirBody,
    target_b: u32,
    callee_ty: TypeId,
    callee_val_raw: u32,
    formal_args: []const u32,
) !void {
    const callee_body = &emitter.input.bodies[target_b];
    const callee_plan = emitter.async_plan.?.getBodyPlan(target_b);
    const is_closure = !callee_ty.isPrimitiveOrSentinel() and
        emitter.input.pool.getNode(callee_ty).tag == .closure_ty;
    const formal_count: usize = if (is_closure)
        (if (emitter.input.pool.getFnSignatureView(callee_ty)) |sv| sv.paramCount() else 0)
    else
        callee_body.param_count;
    const capture_count: usize = callee_body.param_count -| formal_count;

    if (is_closure) {
        var matched_thunk: ?ClosureThunkSpec = null;
        for (emitter.closure_thunks.items) |cand_thunk| {
            if (cand_thunk.target_body_idx == target_b) {
                matched_thunk = cand_thunk;
                break;
            }
        }
        if (matched_thunk) |thunk| {
            if (capture_count > 0 and thunk.capture_types.len > 0) {
                try emitter.print(
                    "        _cx_cenv_{d} *_senv = (_cx_cenv_{d} *)_v_{d}.env_ptr;\n",
                    .{ thunk.thunk_idx, thunk.thunk_idx, callee_val_raw },
                );
                const copy_caps = @min(capture_count, thunk.capture_types.len);
                for (0..copy_caps) |cap_i| {
                    const cap_decl = callee_body.locals.items[1 + cap_i];
                    const cap_off = callee_plan.getLocalOffset(@intCast(1 + cap_i));
                    if (try isZeroSizedType(emitter, cap_decl.type_id)) continue;
                    if (cap_decl.mode() == .inout_mode or cap_decl.mode() == .set_mode) {
                        try emitter.print(
                            "        {{ void *_cp = (void *)&_senv->_c{d}; memcpy(_nfr + {d}u, &_cp, sizeof(void *)); }}\n",
                            .{ cap_i, cap_off },
                        );
                    } else {
                        try emitter.print(
                            "        memcpy(_nfr + {d}u, &_senv->_c{d}, sizeof(_senv->_c{d}));\n",
                            .{ cap_off, cap_i, cap_i },
                        );
                    }
                }
            }
        }
    }

    const avail_args = @min(formal_count, formal_args.len);
    for (0..avail_args) |arg_i| {
        const param_idx: u32 = @intCast(1 + capture_count + arg_i);
        const param_decl = callee_body.locals.items[param_idx];
        const param_off = callee_plan.getLocalOffset(param_idx);
        const arg_raw = formal_args[arg_i];
        _ = caller_body;
        if (try isZeroSizedType(emitter, param_decl.type_id)) continue;
        if (param_decl.mode() == .inout_mode or param_decl.mode() == .set_mode) {
            try emitter.print(
                "        memcpy(_nfr + {d}u, &_v_{d}, sizeof(void *));\n",
                .{ param_off, arg_raw },
            );
        } else {
            try emitter.print(
                "        memcpy(_nfr + {d}u, &_v_{d}, sizeof(_v_{d}));\n",
                .{ param_off, arg_raw, arg_raw },
            );
        }
    }
}

/// Emits C99 lazy unpolled coroutine allocation for `MirIntrinsicKind.async_future_make`.
fn emitAsyncFutureMakeC(
    emitter: *CModuleEmitter,
    body: *const MirBody,
    dst_raw: u32,
    fut_raw_ty: TypeId,
    args: []const u32,
) !void {
    const fut_ty = emitter.input.pool.unwrapUnderlyingType(fut_raw_ty);
    const out_ty = emitter.input.pool.unwrapUnderlyingType(
        emitter.input.pool.getFutureOutputType(fut_ty) orelse .unit_ty,
    );
    const out_lay = try emitter.resolver.resolveType(out_ty);
    const def_raw: u32 = if (extractConstUsizeFromBody(body, args[0])) |def_val|
        @truncate(def_val)
    else
        mir.NONE_U32;
    const sym_raw: u32 = if (extractConstUsizeFromBody(body, args[1])) |sym_val|
        @truncate(sym_val)
    else
        mir.NONE_U32;
    const callee_ty = emitter.input.pool.unwrapUnderlyingType(
        body.getInst(MirValueId.fromInt(args[2])).type_id,
    );
    const is_closure = !callee_ty.isPrimitiveOrSentinel() and
        emitter.input.pool.getNode(callee_ty).tag == .closure_ty;

    var resolved_b = resolveBodyIndex(emitter, DefId.fromInt(def_raw), SymbolIndex.fromInt(sym_raw));
    if (resolved_b == null and args[2] < body.insts.len) {
        const callee_inst = body.insts.get(args[2]);
        if (callee_inst.op == .aggregate_make) {
            const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(callee_inst.aux_u16))));
            if (agg_kind == .closure_make) {
                resolved_b = resolveBodyIndex(emitter, DefId.fromInt(callee_inst.operands.lhs), .none);
            }
        } else if (callee_inst.op == .fn_addr) {
            resolved_b = resolveBodyIndex(
                emitter,
                DefId.fromInt(callee_inst.operands.lhs),
                SymbolIndex.fromInt(callee_inst.operands.rhs),
            );
        }
    }

    if (resolved_b) |target_b| {
        try emitter.print(
            "    {{\n        uint8_t *_nfr = _cx_coro_alloc({d}u);\n",
            .{target_b},
        );
        try emitPopulateCoroFrameArgsC(emitter, body, target_b, callee_ty, args[2], args[3..]);
        try emitter.print(
            "        memset(&_v_{d}, 0, sizeof(_v_{d}));\n" ++
                "        _v_{d}._handle = (void *)_nfr; _v_{d}._kind = 1u; " ++
                "_v_{d}._aux = {d}u; _v_{d}._out_sz = {d}u;\n    }}\n",
            .{ dst_raw, dst_raw, dst_raw, dst_raw, dst_raw, target_b, dst_raw, out_lay.size_bytes },
        );
        return;
    }

    const fn_ptr_expr = if (is_closure)
        try std.fmt.allocPrint(emitter.allocator, "(const void *)(uintptr_t)_v_{d}.fn_ptr", .{args[2]})
    else
        try std.fmt.allocPrint(emitter.allocator, "(const void *)(uintptr_t)_v_{d}", .{args[2]});
    defer emitter.allocator.free(fn_ptr_expr);

    try emitter.print(
        "    {{\n        uint32_t _db = _cx_coro_lookup_fn({s});\n" ++
            "        uint8_t *_nfr = _cx_coro_alloc(_db);\n" ++
            "        switch (_db) {{\n",
        .{fn_ptr_expr},
    );
    for (0..emitter.input.bodies.len) |cand_i| {
        if (!isCompatibleIndirectAsyncCandidateC(emitter, body, @intCast(cand_i), callee_ty, out_ty, args[3..])) {
            continue;
        }
        try emitter.print("        case {d}u:\n", .{cand_i});
        try emitPopulateCoroFrameArgsC(emitter, body, @intCast(cand_i), callee_ty, args[2], args[3..]);
        try emitter.writeAll("            break;\n");
    }
    try emitter.print(
        "        default: break;\n        }}\n" ++
            "        memset(&_v_{d}, 0, sizeof(_v_{d}));\n" ++
            "        _v_{d}._handle = (void *)_nfr; _v_{d}._kind = 1u; " ++
            "_v_{d}._aux = _db; _v_{d}._out_sz = {d}u;\n    }}\n",
        .{ dst_raw, dst_raw, dst_raw, dst_raw, dst_raw, dst_raw, out_lay.size_bytes },
    );
}

/// Emits C99 nursery barrier (`async_task_group_exit`) canceling on `Err`/cleanup or draining FIFO.
fn emitAsyncTaskGroupExitC(emitter: *CModuleEmitter, body: *const MirBody, group_val_raw: u32) !void {
    var err_cond: []u8 = if (emitter.active_coro_body_idx != null)
        try emitter.allocator.dupe(u8, "(_action == 1u)")
    else
        try emitter.allocator.dupe(u8, "0");
    defer emitter.allocator.free(err_cond);

    if (!emitter.active_bb_id.isNone() and emitter.active_bb_id.asInt() < body.blocks.items.len) {
        const bb_rec = body.blocks.items[emitter.active_bb_id.asInt()];
        if (bb_rec.isCleanupPad()) {
            emitter.allocator.free(err_cond);
            err_cond = try emitter.allocator.dupe(u8, "1");
        } else if (bb_rec.terminator.kind == .ret) {
            const unwrapped_ret = emitter.input.pool.unwrapUnderlyingType(body.ret_ty);
            if (!unwrapped_ret.isPrimitiveOrSentinel() and
                emitter.input.pool.getNode(unwrapped_ret).tag == .result_ty and
                !(try isZeroSizedType(emitter, unwrapped_ret)))
            {
                if (try emitter.resolver.getSumDetail(unwrapped_ret)) |sum_detail| {
                    const ret_lv = if (bb_rec.terminator.cond_or_val != mir.NONE_U32)
                        try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{bb_rec.terminator.cond_or_val})
                    else if (emitter.active_coro_body_idx) |cb_idx| blk_coro_r: {
                        const ret_c = try formatCType(emitter, unwrapped_ret);
                        defer emitter.allocator.free(ret_c);
                        const off_0 = emitter.async_plan.?.getBodyPlan(cb_idx).getLocalOffset(0);
                        break :blk_coro_r try std.fmt.allocPrint(
                            emitter.allocator,
                            "(*(({s} *)(_frame + {d}u)))",
                            .{ ret_c, off_0 },
                        );
                    } else try emitter.allocator.dupe(u8, "_loc_0");
                    defer emitter.allocator.free(ret_lv);

                    const d_expr = try formatSumDiscrReadExpr(emitter, unwrapped_ret, sum_detail, ret_lv);
                    defer emitter.allocator.free(d_expr);
                    const combined = try std.fmt.allocPrint(
                        emitter.allocator,
                        "({s} || (({s}) == 1u))",
                        .{ err_cond, d_expr },
                    );
                    emitter.allocator.free(err_cond);
                    err_cond = combined;
                }
            }
        }
    }

    try emitter.print(
        "    {{ void *_gp = NULL; memcpy(&_gp, &_v_{d}, sizeof(void *)); " ++
            "_cx_async_group_exit(_gp, ({s}) ? 1u : 0u); }}\n",
        .{ group_val_raw, err_cond },
    );
}

/// Emits cycle-safe scoped parallel block-argument moves (`_phi_<k>`) followed by `goto _bb_<target>`.
fn emitEdgeParallelMovesAndGotoC(
    emitter: *CModuleEmitter,
    body: *const MirBody,
    edge: mir.MirOutgoingEdge,
) !void {
    const dst_params = body.getBlockParams(edge.target_bb);
    const args = body.extra_args.items[edge.args_start .. edge.args_start + edge.args_len];
    const move_count = @min(dst_params.len, args.len);

    if (move_count == 0) {
        try emitter.print("    goto _bb_{d};\n", .{edge.target_bb.asInt()});
        return;
    }

    try emitter.writeAll("    {\n");
    for (0..move_count) |param_k| {
        const param_ty = body.getInst(dst_params[param_k]).type_id;
        if (try isZeroSizedType(emitter, param_ty)) continue;
        const param_c = try formatCType(emitter, param_ty);
        defer emitter.allocator.free(param_c);
        try emitter.print("        {s} _phi_{d} = _v_{d};\n", .{ param_c, param_k, args[param_k] });
    }
    for (0..move_count) |param_k| {
        const param_ty = body.getInst(dst_params[param_k]).type_id;
        if (try isZeroSizedType(emitter, param_ty)) continue;
        try emitter.print("        _v_{d} = _phi_{d};\n", .{ dst_params[param_k].asInt(), param_k });
    }
    try emitter.print("        goto _bb_{d};\n    }}\n", .{edge.target_bb.asInt()});
}

/// Emits C99 control-flow statements for `term` at the end of `bb_id`.
fn emitMirTerminatorC(
    emitter: *CModuleEmitter,
    body_idx: u32,
    body: *const MirBody,
    bb_id: MirBlockId,
    term: mir.MirTerminator,
) !void {
    switch (term.kind) {
        .unreachable_term => {
            if (emitter.cfg.target.isFreestanding() or
                (emitter.is_in_c_abi_body and !emitter.input.is_oracle_trace_enabled))
            {
                try emitter.writeAll("    __builtin_trap();\n");
            } else {
                try emitter.writeAll("    _cx_rt_trap(0u);\n");
            }
        },
        .trap => {
            if (emitter.cfg.target.isFreestanding() or
                (emitter.is_in_c_abi_body and !emitter.input.is_oracle_trace_enabled))
            {
                try emitter.writeAll("    __builtin_trap();\n");
            } else {
                try emitter.print("    _cx_rt_trap({d}u);\n", .{term.aux_u8});
            }
        },
        .ret => {
            const is_void = try isZeroSizedType(emitter, body.ret_ty);
            if (emitter.active_coro_body_idx) |cb_idx| {
                const ret_expr = if (term.cond_or_val != mir.NONE_U32)
                    try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{term.cond_or_val})
                else if (is_void)
                    try emitter.allocator.dupe(u8, "0u")
                else blk_coro_ret: {
                    const ret_c = try formatCType(emitter, body.ret_ty);
                    defer emitter.allocator.free(ret_c);
                    const off_0 = emitter.async_plan.?.getBodyPlan(cb_idx).getLocalOffset(0);
                    break :blk_coro_ret try std.fmt.allocPrint(
                        emitter.allocator,
                        "(*(({s} *)(_frame + {d}u)))",
                        .{ ret_c, off_0 },
                    );
                };
                defer emitter.allocator.free(ret_expr);

                try emitter.writeAll(
                    "    if (_action == 1u) {\n" ++
                        "        uint32_t _cs = 0xFFFFFFFFu;\n" ++
                        "        memcpy(_frame, &_cs, 4u);\n" ++
                        "        return 1u;\n" ++
                        "    }\n",
                );
                if (!emitter.cfg.is_release_mode and !is_void) {
                    const unwrapped_ret = emitter.input.pool.unwrapUnderlyingType(body.ret_ty);
                    if (emitter.input.pool.getNode(unwrapped_ret).tag == .result_ty) {
                        if (try emitter.resolver.getSumDetail(unwrapped_ret)) |sum_detail| {
                            const d_expr = try formatSumDiscrReadExpr(emitter, unwrapped_ret, sum_detail, ret_expr);
                            defer emitter.allocator.free(d_expr);
                            const site_tag: u64 = (@as(u64, body_idx + 1) << 16) | @as(u64, bb_id.asInt());
                            try emitter.print(
                                "    if (({s}) == 1u) _cx_record_err_ret((uintptr_t){d}ull);\n",
                                .{ d_expr, site_tag },
                            );
                        }
                    }
                }
                if (!is_void) {
                    const ret_lay = try emitter.resolver.resolveType(body.ret_ty);
                    try emitter.print(
                        "    if (_out_ptr != NULL) memcpy(_out_ptr, &({s}), {d}u);\n",
                        .{ ret_expr, ret_lay.size_bytes },
                    );
                }
                try emitter.writeAll(
                    "    { uint32_t _cs = 0xFFFFFFFEu; memcpy(_frame, &_cs, 4u); }\n" ++
                        "    return 1u;\n",
                );
                return;
            }

            const ret_expr = if (term.cond_or_val != mir.NONE_U32)
                try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{term.cond_or_val})
            else
                try emitter.allocator.dupe(u8, "_loc_0");
            defer emitter.allocator.free(ret_expr);

            if (!emitter.cfg.is_release_mode and !is_void) {
                const unwrapped_ret = emitter.input.pool.unwrapUnderlyingType(body.ret_ty);
                if (emitter.input.pool.getNode(unwrapped_ret).tag == .result_ty) {
                    if (try emitter.resolver.getSumDetail(unwrapped_ret)) |sum_detail| {
                        const d_expr = try formatSumDiscrReadExpr(emitter, unwrapped_ret, sum_detail, ret_expr);
                        defer emitter.allocator.free(d_expr);
                        const site_tag: u64 = (@as(u64, body_idx + 1) << 16) | @as(u64, bb_id.asInt());
                        try emitter.print(
                            "    if (({s}) == 1u) _cx_record_err_ret((uintptr_t){d}ull);\n",
                            .{ d_expr, site_tag },
                        );
                    }
                }
            }
            if (is_void) {
                try emitter.writeAll("    return;\n");
            } else {
                try emitter.print("    return {s};\n", .{ret_expr});
            }
        },
        .br => {
            try emitEdgeParallelMovesAndGotoC(emitter, body, body.extra_edges.items[term.edge_start]);
        },
        .cond_br => {
            try emitter.print("    if ((_v_{d} & 1u) != 0u) {{\n", .{term.cond_or_val});
            try emitEdgeParallelMovesAndGotoC(emitter, body, body.extra_edges.items[term.edge_start]);
            try emitter.writeAll("    } else {\n");
            try emitEdgeParallelMovesAndGotoC(emitter, body, body.extra_edges.items[term.edge_start + 1]);
            try emitter.writeAll("    }\n");
        },
        .switch_int => {
            const discr_val = MirValueId.fromInt(term.cond_or_val);
            const discr_ty = emitter.input.pool.unwrapUnderlyingType(body.getInst(discr_val).type_id);
            const discr_info = try resolveIntegerInfo(emitter, discr_ty);
            if (discr_info != null and discr_info.?.bits == 128) {
                var case_i: u32 = 0;
                while (case_i + 1 < term.edge_len) : (case_i += 1) {
                    const edge = body.extra_edges.items[term.edge_start + case_i];
                    const case_u128: u128 = @bitCast(body.switch_values.items[edge.case_tag_idx]);
                    const lo_w: u64 = @truncate(case_u128);
                    const hi_w: u64 = @truncate(case_u128 >> 64);
                    const kw = if (case_i == 0) "    if" else "    else if";
                    try emitter.print(
                        "{s} (_cx_u128_eq(_cx_as_u128(_v_{d}), _cx_u128_make({d}ull, {d}ull))) {{\n",
                        .{ kw, term.cond_or_val, lo_w, hi_w },
                    );
                    try emitEdgeParallelMovesAndGotoC(emitter, body, edge);
                    try emitter.writeAll("    }\n");
                }
                const def_edge = body.extra_edges.items[term.edge_start + term.edge_len - 1];
                if (term.edge_len > 1) {
                    try emitter.writeAll("    else {\n");
                    try emitEdgeParallelMovesAndGotoC(emitter, body, def_edge);
                    try emitter.writeAll("    }\n");
                } else {
                    try emitEdgeParallelMovesAndGotoC(emitter, body, def_edge);
                }
            } else {
                const bits: u16 = if (discr_info) |inf| inf.bits else 64;
                const mask: u64 = if (bits >= 64) std.math.maxInt(u64) else (@as(u64, 1) << @intCast(bits)) - 1;
                try emitter.print("    switch (((uint64_t)_v_{d}) & {d}ull) {{\n", .{ term.cond_or_val, mask });
                var seen_cases: std.AutoHashMapUnmanaged(u64, void) = .empty;
                defer seen_cases.deinit(emitter.allocator);
                var case_i: u32 = 0;
                while (case_i + 1 < term.edge_len) : (case_i += 1) {
                    const edge = body.extra_edges.items[term.edge_start + case_i];
                    const case_u128: u128 = @bitCast(body.switch_values.items[edge.case_tag_idx]);
                    const case_u64: u64 = @as(u64, @truncate(case_u128)) & mask;
                    if ((try seen_cases.getOrPut(emitter.allocator, case_u64)).found_existing) continue;
                    try emitter.print("    case {d}ull:\n", .{case_u64});
                    try emitEdgeParallelMovesAndGotoC(emitter, body, edge);
                }
                try emitter.writeAll("    default:\n");
                try emitEdgeParallelMovesAndGotoC(
                    emitter,
                    body,
                    body.extra_edges.items[term.edge_start + term.edge_len - 1],
                );
                try emitter.writeAll("    }\n");
            }
        },
        .call => {
            const call_site = body.calls.items[term.cond_or_val];
            if (!call_site.origin_token.isNone()) {
                try maybeEmitLineDirective(emitter, body.file_id, call_site.origin_token);
            }
            var arg_strs: std.ArrayListUnmanaged([]u8) = .empty;
            defer {
                for (arg_strs.items) |owned_s| emitter.allocator.free(owned_s);
                arg_strs.deinit(emitter.allocator);
            }

            const indirect_sig: ?type_system.FnSignatureView = if (call_site.direct_symbol.isNone() and
                call_site.direct_def_id.isNone() and
                !call_site.callee_val.isNone())
                emitter.input.pool.getFnSignatureView(
                    emitter.input.pool.unwrapUnderlyingType(body.getInst(call_site.callee_val).type_id),
                )
            else
                null;
            const is_variadic_call = call_site.is_c_variadic or
                (indirect_sig != null and indirect_sig.?.is_variadic);
            const fixed_arity: usize = if (call_site.is_c_variadic)
                call_site.fixed_arity
            else if (indirect_sig) |isig|
                isig.paramCount()
            else
                call_site.args_len;

            var arg_i: usize = 0;
            while (arg_i < call_site.args_len) : (arg_i += 1) {
                const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                const word = body.extra_args.items[call_site.args_start + arg_i];
                if (mode == .let_mode or mode == .sink_mode) {
                    const arg_ty = emitter.input.pool.unwrapUnderlyingType(
                        body.getInst(MirValueId.fromInt(word)).type_id,
                    );
                    if (!(try isZeroSizedType(emitter, arg_ty))) {
                        const is_vararg_tail = is_variadic_call and arg_i >= fixed_arity;
                        const arg_expr = if (is_vararg_tail and arg_ty == .f32_ty)
                            try std.fmt.allocPrint(emitter.allocator, "((double)_v_{d})", .{word})
                        else if (is_vararg_tail and arg_ty == .bool_ty)
                            try std.fmt.allocPrint(emitter.allocator, "((int32_t)(_v_{d} & 1u))", .{word})
                        else if (is_vararg_tail) blk_va: {
                            if (try resolveIntegerInfo(emitter, arg_ty)) |va_int| {
                                if (va_int.bits < 32) {
                                    if (va_int.is_signed) {
                                        break :blk_va try std.fmt.allocPrint(
                                            emitter.allocator,
                                            "((int32_t)_v_{d})",
                                            .{word},
                                        );
                                    }
                                    break :blk_va try std.fmt.allocPrint(
                                        emitter.allocator,
                                        "((int32_t)((uint32_t)_v_{d}))",
                                        .{word},
                                    );
                                }
                            }
                            break :blk_va try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{word});
                        } else try std.fmt.allocPrint(emitter.allocator, "_v_{d}", .{word});
                        try arg_strs.append(emitter.allocator, arg_expr);
                    }
                } else {
                    switch (try lowerPlaceC(emitter, body, PlaceId.fromInt(word))) {
                        .const_len => {},
                        .lvalue_expr => |lv| {
                            defer emitter.allocator.free(lv.expr_str);
                            if (try isZeroSizedType(emitter, lv.pointee_ty)) {
                                const p_lay = try emitter.resolver.resolveType(lv.pointee_ty);
                                try arg_strs.append(
                                    emitter.allocator,
                                    try std.fmt.allocPrint(
                                        emitter.allocator,
                                        "(uint8_t *)((uintptr_t){d}u)",
                                        .{p_lay.alignBytes()},
                                    ),
                                );
                            } else {
                                try arg_strs.append(
                                    emitter.allocator,
                                    try std.fmt.allocPrint(emitter.allocator, "(&({s}))", .{lv.expr_str}),
                                );
                            }
                        },
                    }
                }
            }

            const normal_edge = body.extra_edges.items[term.edge_start];
            const dst_params = body.getBlockParams(normal_edge.target_bb);
            const has_ret_assign = !(try isZeroSizedType(emitter, call_site.ret_ty)) and
                dst_params.len >= 1 and
                !(try isZeroSizedType(emitter, body.getInst(dst_params[0]).type_id));

            try emitter.writeAll("    ");
            if (has_ret_assign) {
                try emitter.print("_v_{d} = ", .{dst_params[0].asInt()});
            }

            if (resolveBodyIndex(emitter, call_site.direct_def_id, call_site.direct_symbol)) |target_b| {
                if (emitter.input.is_dev_got_enabled) {
                    try emitter.print("((_cx_body_fn_t_{d})_cx_dev_got[{d}u])(", .{ target_b, target_b });
                } else {
                    try emitter.print("{s}(", .{emitter.body_c_names.items[target_b]});
                }
                for (arg_strs.items, 0..) |a_str, idx| {
                    if (idx > 0) try emitter.writeAll(", ");
                    try emitter.writeAll(a_str);
                }
                try emitter.writeAll(");\n");
            } else if (!call_site.direct_symbol.isNone() and
                call_site.direct_symbol.asInt() < emitter.input.sym_table.symbols.items.len)
            {
                try emitter.print("_cx_ext_{d}(", .{call_site.direct_symbol.asInt()});
                for (arg_strs.items, 0..) |a_str, idx| {
                    if (idx > 0) try emitter.writeAll(", ");
                    try emitter.writeAll(a_str);
                }
                try emitter.writeAll(");\n");
            } else {
                const callee_ty = emitter.input.pool.unwrapUnderlyingType(
                    body.getInst(call_site.callee_val).type_id,
                );
                if (emitter.input.pool.getNode(callee_ty).tag == .closure_ty) {
                    try emitter.print(
                        "_v_{d}.fn_ptr(_v_{d}.env_ptr",
                        .{ call_site.callee_val.asInt(), call_site.callee_val.asInt() },
                    );
                    for (arg_strs.items) |a_str| {
                        try emitter.print(", {s}", .{a_str});
                    }
                    try emitter.writeAll(");\n");
                } else {
                    try emitter.print("_v_{d}(", .{call_site.callee_val.asInt()});
                    for (arg_strs.items, 0..) |a_str, idx| {
                        if (idx > 0) try emitter.writeAll(", ");
                        try emitter.writeAll(a_str);
                    }
                    try emitter.writeAll(");\n");
                }
            }
            try emitter.print("    goto _bb_{d};\n", .{normal_edge.target_bb.asInt()});
        },
        .coro_suspend => {
            if (emitter.active_coro_body_idx) |cb_idx| {
                const plan = emitter.async_plan.?.getBodyPlan(cb_idx);
                if (plan.findSuspendByBlock(bb_id)) |sp_idx| {
                    const sp_meta = plan.suspend_points[sp_idx];
                    try emitter.print(
                        "    memcpy(_frame + {d}u, &_v_{d}, sizeof(_v_{d}));\n" ++
                            "    memset(&_v_{d}, 0, sizeof(_v_{d}));\n" ++
                            "    {{ uint32_t _ns = {d}u; memcpy(_frame, &_ns, 4u); }}\n" ++
                            "    goto _coro_disp_{d};\n",
                        .{
                            sp_meta.child_frame_offset,
                            term.cond_or_val,
                            term.cond_or_val,
                            term.cond_or_val,
                            term.cond_or_val,
                            sp_meta.state_tag,
                            sp_meta.state_tag,
                        },
                    );
                    return;
                }
            }
            try emitter.writeAll("    _cx_rt_trap(0u);\n");
        },
    }
}

/// Emits the C `int main(void)` entrypoint wrapper invoking CoreX `main` when present.
fn emitMainEntrypointWrapper(emitter: *CModuleEmitter) !void {
    const main_b = emitter.entry_main_body_idx orelse return;
    const main_body = &emitter.input.bodies[main_b];
    if (main_body.param_count != 0) return;

    const call_fn = if (emitter.input.is_dev_got_enabled)
        try std.fmt.allocPrint(emitter.allocator, "((_cx_body_fn_t_{d})_cx_dev_got[{d}u])", .{ main_b, main_b })
    else
        try emitter.allocator.dupe(u8, emitter.body_c_names.items[main_b]);
    defer emitter.allocator.free(call_fn);

    const ret_ty = emitter.input.pool.unwrapUnderlyingType(main_body.ret_ty);
    if (emitter.cfg.target.isFreestanding()) {
        try emitter.writeAll("int main(void) {\n");
        if (try isZeroSizedType(emitter, ret_ty)) {
            try emitter.print("    {s}();\n    return 0;\n}}\n", .{call_fn});
        } else {
            const ret_c = try formatCType(emitter, ret_ty);
            defer emitter.allocator.free(ret_c);
            try emitter.print("    {s} _main_res = {s}();\n    return (int)_main_res;\n}}\n", .{ ret_c, call_fn });
        }
        return;
    }

    try emitter.writeAll("int main(void) {\n    _cx_rt_init();\n");
    if (try isZeroSizedType(emitter, ret_ty)) {
        try emitter.print(
            "    {s}();\n    _cx_rt_trace_append(\"RET:0\\n\");\n    return 0;\n}}\n",
            .{call_fn},
        );
        return;
    }

    const ret_c = try formatCType(emitter, ret_ty);
    defer emitter.allocator.free(ret_c);
    try emitter.print("    {s} _main_res = {s}();\n", .{ ret_c, call_fn });

    if (try resolveIntegerInfo(emitter, ret_ty)) |int_info| {
        if (int_info.bits <= 64) {
            if (int_info.is_signed) {
                try emitter.writeAll(
                    "    { char _rb[64]; (void)snprintf(_rb, sizeof(_rb), \"RET:%lld\\n\", " ++
                        "(long long)_main_res); _cx_rt_trace_append(_rb); }\n" ++
                        "    return (int)_main_res;\n}\n",
                );
            } else {
                try emitter.writeAll(
                    "    { char _rb[64]; (void)snprintf(_rb, sizeof(_rb), \"RET:%llu\\n\", " ++
                        "(unsigned long long)_main_res); _cx_rt_trace_append(_rb); }\n" ++
                        "    return (int)_main_res;\n}\n",
                );
            }
            return;
        }
    }

    if (emitter.input.pool.getNode(ret_ty).tag == .result_ty) {
        if (try emitter.resolver.getSumDetail(ret_ty)) |sum_detail| {
            const d_expr = try formatSumDiscrReadExpr(emitter, ret_ty, sum_detail, "_main_res");
            defer emitter.allocator.free(d_expr);
            try emitter.print(
                "    if (({s}) == 1u) {{ _cx_rt_trace_append(\"ERR:1\\n\"); return 1; }}\n" ++
                    "    _cx_rt_trace_append(\"RET:0\\n\");\n    return 0;\n}}\n",
                .{d_expr},
            );
            return;
        }
    }

    try emitter.writeAll("    _cx_rt_trace_append(\"RET:0\\n\");\n    return 0;\n}\n");
}

// ------------ `zig cc` Driver & Atomic File Write -------------

/// Monotonic atomic counter ensuring concurrent in-process compilations never collide on temp dirs.
var next_driver_scratch_seq = std.atomic.Value(u32).init(1);

/// Compiles `c_source` via `zig cc` and `codegen_link` across all 11 targets and publishes `output_path`.
fn compileCSourceWithZigDriver(
    allocator: std.mem.Allocator,
    cfg: CBackendConfig,
    input: CodegenModuleInput,
    c_source: []const u8,
    collected_link_libs: []const []const u8,
) CCodegenError![]u8 {
    const out_path = input.output_path orelse return error.MissingOutputConfig;
    const io = input.io orelse return error.MissingOutputConfig;

    const zig_exe = codegen_abi.resolveZigExecutable(io, allocator, input.environ_map) catch
        return error.OutOfMemory;
    defer allocator.free(zig_exe);

    const seq_id = next_driver_scratch_seq.fetchAdd(1, .monotonic);
    const proc_salt = @intFromPtr(&next_driver_scratch_seq) ^ (@intFromPtr(&seq_id) >> 4);
    const scratch_dir = std.fmt.allocPrint(
        allocator,
        ".zig-cache/cx_c_drv_{x}_{d}",
        .{ proc_salt, seq_id },
    ) catch return error.OutOfMemory;
    defer allocator.free(scratch_dir);
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};

    const is_sdkless_msvc_obj = cfg.target.os == .windows and cfg.target.abi == .msvc and
        (input.artifact_kind == .object_file or input.artifact_kind == .static_library);
    const is_freestanding_cc = cfg.target.isFreestanding() or is_sdkless_msvc_obj;

    var staged_fs_c: ?[]u8 = null;
    defer if (staged_fs_c) |fs_buf| allocator.free(fs_buf);
    const active_c_source: []const u8 = if (is_sdkless_msvc_obj and !cfg.target.isFreestanding()) blk_fs: {
        const prelude_tail = "_cx_rt_panic(msg_b.data, msg_b.len);\n}\n";
        if (std.mem.indexOf(u8, c_source, prelude_tail)) |tail_pos| {
            const user_tail = c_source[tail_pos + prelude_tail.len ..];
            const hosted_alloc_decls =
                "void *calloc(size_t, size_t);\n" ++
                "void *realloc(void *, size_t);\n" ++
                "void free(void *);\n\n";
            staged_fs_c = std.fmt.allocPrint(
                allocator,
                "{s}{s}{s}{s}{s}",
                .{ C99_FREESTANDING_PREAMBLE, C99_ARITH_HELPERS, C99_FREESTANDING_TAIL, hosted_alloc_decls, user_tail },
            ) catch return error.OutOfMemory;
            break :blk_fs staged_fs_c.?;
        }
        break :blk_fs c_source;
    } else c_source;

    const c_src_path = std.fmt.allocPrint(allocator, "{s}/module.c", .{scratch_dir}) catch
        return error.OutOfMemory;
    defer allocator.free(c_src_path);
    codegen_abi.atomicWriteOutputFile(io, allocator, c_src_path, active_c_source) catch
        return error.BackendFailure;

    const zig_triple = cfg.target.asZigTargetTriple();
    const opt_flag = if (cfg.is_release_mode)
        (if (cfg.target.isWasm()) "-Oz" else "-O2")
    else
        "-O0";

    if (cfg.is_fuzz_instrumented) {
        const ir_path = std.fmt.allocPrint(allocator, "{s}/module.ll", .{scratch_dir}) catch
            return error.OutOfMemory;
        defer allocator.free(ir_path);
        const mod_obj_path = std.fmt.allocPrint(allocator, "{s}/module.o", .{scratch_dir}) catch
            return error.OutOfMemory;
        defer allocator.free(mod_obj_path);

        try runZigCcCommand(allocator, io, input.environ_map, input.diagnostic_sink, &.{
            zig_exe,
            "cc",
            "-S",
            "-emit-llvm",
            "-target",
            zig_triple,
            "-std=c99",
            "-fno-strict-aliasing",
            "-Wno-unused-function",
            "-Wno-unused-variable",
            opt_flag,
            c_src_path,
            "-o",
            ir_path,
        });

        try runZigCcCommand(allocator, io, input.environ_map, input.diagnostic_sink, &.{
            zig_exe,
            "cc",
            "-c",
            "-target",
            zig_triple,
            "-Wno-override-module",
            opt_flag,
            "-fsanitize-coverage=inline-8bit-counters,pc-table,trace-cmp,trace-div",
            ir_path,
            "-o",
            mod_obj_path,
        });

        if (input.artifact_kind == .object_file) {
            codegen_abi.publishStagedFileAtomic(io, allocator, mod_obj_path, out_path) catch
                return error.BackendFailure;
            return allocator.dupe(u8, out_path) catch return error.OutOfMemory;
        }

        const shim_c_path = std.fmt.allocPrint(allocator, "{s}/sancov_shim.c", .{scratch_dir}) catch
            return error.OutOfMemory;
        defer allocator.free(shim_c_path);
        const shim_obj_path = std.fmt.allocPrint(allocator, "{s}/sancov_shim.o", .{scratch_dir}) catch
            return error.OutOfMemory;
        defer allocator.free(shim_obj_path);
        const tmp_exe_path = std.fmt.allocPrint(
            allocator,
            "{s}/out{s}",
            .{ scratch_dir, cfg.target.executableExtension() },
        ) catch return error.OutOfMemory;
        defer allocator.free(tmp_exe_path);

        codegen_abi.atomicWriteOutputFile(io, allocator, shim_c_path, SANCOV_SHIM_C_SOURCE) catch
            return error.BackendFailure;
        try runZigCcCommand(allocator, io, input.environ_map, input.diagnostic_sink, &.{
            zig_exe,
            "cc",
            "-c",
            "-target",
            zig_triple,
            "-std=c99",
            "-O2",
            shim_c_path,
            "-o",
            shim_obj_path,
        });
        try runZigCcCommand(allocator, io, input.environ_map, input.diagnostic_sink, &.{
            zig_exe,
            "cc",
            "-target",
            zig_triple,
            mod_obj_path,
            shim_obj_path,
            "-o",
            tmp_exe_path,
        });
        codegen_abi.publishStagedFileAtomic(io, allocator, tmp_exe_path, out_path) catch
            return error.BackendFailure;
        return allocator.dupe(u8, out_path) catch return error.OutOfMemory;
    }

    const mod_obj_path = std.fmt.allocPrint(
        allocator,
        "{s}/module{s}",
        .{ scratch_dir, cfg.target.defaultObjExtension() },
    ) catch return error.OutOfMemory;
    defer allocator.free(mod_obj_path);

    var cc_argv: std.ArrayListUnmanaged([]const u8) = .empty;
    defer cc_argv.deinit(allocator);
    cc_argv.appendSlice(allocator, &.{
        zig_exe,
        "cc",
        "-c",
        "-target",
        zig_triple,
        "-std=c99",
        "-fno-strict-aliasing",
        "-ffunction-sections",
        "-fdata-sections",
        "-Wno-unused-function",
        "-Wno-unused-variable",
        opt_flag,
    }) catch return error.OutOfMemory;
    if (is_freestanding_cc) {
        cc_argv.appendSlice(allocator, &.{ "-ffreestanding", "-nostdlib" }) catch return error.OutOfMemory;
    }
    cc_argv.appendSlice(allocator, &.{ c_src_path, "-o", mod_obj_path }) catch return error.OutOfMemory;

    try runZigCcCommand(allocator, io, input.environ_map, input.diagnostic_sink, cc_argv.items);

    if (input.artifact_kind == .object_file) {
        codegen_abi.publishStagedFileAtomic(io, allocator, mod_obj_path, out_path) catch
            return error.BackendFailure;
        return allocator.dupe(u8, out_path) catch return error.OutOfMemory;
    }

    var merged_libs: std.ArrayListUnmanaged([]const u8) = .empty;
    defer merged_libs.deinit(allocator);
    for (input.extra_libs) |ext_l| {
        merged_libs.append(allocator, ext_l) catch return error.OutOfMemory;
    }
    for (collected_link_libs) |col_l| {
        var is_dup = false;
        for (merged_libs.items) |existing_l| {
            if (std.mem.eql(u8, existing_l, col_l)) {
                is_dup = true;
                break;
            }
        }
        if (!is_dup) merged_libs.append(allocator, col_l) catch return error.OutOfMemory;
    }

    codegen_link.linkCrossTarget(io, allocator, .{
        .target = cfg.target,
        .object_paths = &.{mod_obj_path},
        .output_path = out_path,
        .artifact_kind = input.artifact_kind,
        .link_mode = input.link_mode,
        .is_release_mode = cfg.is_release_mode,
        .has_dwarf_tables = cfg.has_line_directives and input.vfs_source_map != null,
        .is_nostdlib = cfg.target.isFreestanding(),
        .extra_libs = merged_libs.items,
        .lib_dirs = input.lib_dirs,
        .environ_map = input.environ_map,
        .diagnostic_sink = input.diagnostic_sink,
    }) catch |link_err| switch (link_err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.LinkerFailed => return error.CompilerDriverFailed,
        else => return error.BackendFailure,
    };

    return allocator.dupe(u8, out_path) catch return error.OutOfMemory;
}

/// Runs a `zig cc` subprocess, emitting `E0008` into `diagnostic_sink` if compilation or linking fails.
pub fn runZigCcCommand(
    allocator: std.mem.Allocator,
    io: std.Io,
    environ_map: ?*const std.process.Environ.Map,
    diagnostic_sink: ?*diagnostic.DiagnosticSink,
    argv: []const []const u8,
) CCodegenError!void {
    var det_env = codegen_abi.prepareDeterministicDriverEnv(allocator, environ_map) catch
        return error.OutOfMemory;
    defer det_env.deinit();

    const run_res = std.process.run(allocator, io, .{
        .argv = argv,
        .environ_map = det_env.asConstPtr(),
    }) catch return error.CompilerDriverFailed;
    defer allocator.free(run_res.stdout);
    defer allocator.free(run_res.stderr);

    if (!run_res.term.success()) {
        if (diagnostic_sink) |sink| {
            const exit_code: u32 = switch (run_res.term) {
                .exited => |code| code,
                else => 1,
            };
            codegen_abi.emitLinkerFailureDiagnostic(
                sink,
                Span.ZERO,
                exit_code,
                run_res.stderr,
            ) catch {};
        }
        return error.CompilerDriverFailed;
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Returns `true` iff `body_ptr` is the top-level binary entrypoint `fn main` in `PackageId.root`.
pub fn isRootEntryMainCandidate(
    body_ptr: *const MirBody,
    sym_table: *const SymbolTable,
    raw_name: []const u8,
    is_exported_main: bool,
) bool {
    return isRootEntryMainCandidateWithEntry(
        body_ptr,
        sym_table,
        raw_name,
        is_exported_main,
        sym_table.active_entry_file_id,
    );
}

/// Returns `true` iff `body_ptr` is the binary entrypoint `fn main` matching `entry_file_id` (or `.root` root file).
pub fn isRootEntryMainCandidateWithEntry(
    body_ptr: *const MirBody,
    sym_table: *const SymbolTable,
    raw_name: []const u8,
    is_exported_main: bool,
    entry_file_id: FileId,
) bool {
    if (!std.mem.eql(u8, raw_name, "main") or is_exported_main) return false;
    const effective_entry = if (!entry_file_id.isNone()) entry_file_id else sym_table.active_entry_file_id;
    if (!body_ptr.file_id.isNone()) {
        if (sym_table.getFilePackageId(body_ptr.file_id) != .root) return false;
        if (!effective_entry.isNone()) {
            if (body_ptr.file_id != effective_entry) return false;
        } else if (sym_table.package_metas.get(.root)) |root_meta| {
            if (!root_meta.root_file_id.isNone() and body_ptr.file_id != root_meta.root_file_id) {
                return false;
            }
        } else if (sym_table.lookupPackageRootScope(.root)) |root_pkg_scope| {
            if (!root_pkg_scope.isNone()) {
                const root_scope_fid = sym_table.scope_arena.getScope(root_pkg_scope).file_id;
                if (!root_scope_fid.isNone() and body_ptr.file_id != root_scope_fid) {
                    return false;
                }
            }
        }
    }
    var resolved_sym_idx: SymbolIndex = body_ptr.symbol_index;
    if (resolved_sym_idx.isNone() and !body_ptr.def_id.isNone()) {
        if (sym_table.def_to_symbol.get(body_ptr.def_id.asInt())) |mapped_sym| {
            resolved_sym_idx = mapped_sym;
        }
    }
    if (!resolved_sym_idx.isNone() and resolved_sym_idx.asInt() < sym_table.symbols.items.len) {
        const sym_rec = sym_table.getSymbol(resolved_sym_idx).*;
        if (!sym_rec.owner_def_id.isNone()) return false;
        if (!body_ptr.file_id.isNone()) {
            if (sym_table.file_module_scopes.get(body_ptr.file_id.asInt())) |mod_scope| {
                if (!sym_rec.scope_id.isNone() and sym_rec.scope_id != mod_scope) return false;
            }
        }
    }
    return true;
}

/// Formats a deterministic C99 / LLVM internal symbol identifier for `body_ptr`.
/// Preserves exact `_cx_fn_{body_idx}_{clean_suffix}` in single-package standalone mode for golden parity,
/// and emits `_cx_p{pkg_id}_{pkg_ver_hash8}_f{file_id}_{body_idx}_{clean_suffix}` in multi-package mode.
pub fn formatInternalBodySymbolAlloc(
    allocator: std.mem.Allocator,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    body_ptr: *const MirBody,
    body_idx: u32,
    clean_suffix: []const u8,
) ![]u8 {
    const pkg_id = if (!body_ptr.file_id.isNone())
        sym_table.getFilePackageId(body_ptr.file_id)
    else
        vfs_sourcemap.PackageId.root;
    const is_multi_pkg_mode = (pkg_id != .root) or
        sym_table.is_flat_named_module_scopes_suppressed or
        (sym_table.package_metas.count() > 0) or
        (sym_table.package_canonical_names.count() > 0);
    if (!is_multi_pkg_mode) {
        return std.fmt.allocPrint(allocator, "_cx_fn_{d}_{s}", .{ body_idx, clean_suffix });
    }

    var hasher = std.hash.Wyhash.init(0);
    if (sym_table.package_metas.get(pkg_id)) |pkg_meta| {
        if (pkg_meta.canonical_name_sym != .empty) {
            hasher.update(interner.get(pkg_meta.canonical_name_sym));
        }
        hasher.update("@");
        hasher.update(pkg_meta.version_text);
    } else if (sym_table.package_canonical_names.get(pkg_id)) |canon_sym| {
        hasher.update(interner.get(canon_sym));
        hasher.update("@");
        if (sym_table.package_version_labels.get(pkg_id)) |ver_id| {
            hasher.update(interner.get(ver_id));
        }
    } else {
        const raw_pkg_bytes: [2]u8 = @bitCast(pkg_id.asInt());
        hasher.update(&raw_pkg_bytes);
    }
    const pkg_ver_hash8: u32 = @truncate(hasher.final());
    const fid_raw: u32 = if (!body_ptr.file_id.isNone()) body_ptr.file_id.asInt() else 0;
    return std.fmt.allocPrint(
        allocator,
        "_cx_p{d}_{x:0>8}_f{d}_{d}_{s}",
        .{ pkg_id.asInt(), pkg_ver_hash8, fid_raw, body_idx, clean_suffix },
    );
}

/// Verifies that unmangled external export `export_name` (`@export` / `@link_name` / `@wasm_export`)
/// does not collide with another distinct `SymbolIndex` across packages (`E0011`).
pub fn checkAndRecordExportedLinkerSymbol(
    allocator: std.mem.Allocator,
    seen_exports: *std.StringHashMapUnmanaged(SymbolIndex),
    sym_table: *const SymbolTable,
    diagnostic_sink: ?*diagnostic.DiagnosticSink,
    export_name: []const u8,
    body_ptr: *const MirBody,
) !void {
    if (export_name.len == 0) return;
    const cur_sym_idx = body_ptr.symbol_index;
    if (!cur_sym_idx.isNone() and cur_sym_idx.asInt() < sym_table.symbols.items.len and
        sym_table.getSymbol(cur_sym_idx).flags.is_prototype_only)
    {
        return;
    }
    const gop = try seen_exports.getOrPut(allocator, export_name);
    if (!gop.found_existing) {
        gop.value_ptr.* = cur_sym_idx;
        return;
    }
    if (!cur_sym_idx.isNone() and gop.value_ptr.* == cur_sym_idx) return;

    if (diagnostic_sink) |sink| {
        const primary_span = if (!cur_sym_idx.isNone() and cur_sym_idx.asInt() < sym_table.symbols.items.len)
            sym_table.getSymbol(cur_sym_idx).decl_span
        else
            Span.init(body_ptr.file_id, 0, 0);
        const prev_sym_idx = gop.value_ptr.*;
        const display_name = if (std.mem.eql(u8, export_name, "_cx_user_main")) "main" else export_name;
        const msg = try std.fmt.allocPrint(
            allocator,
            "duplicate exported native linker symbol `{s}` across compiled modules/packages",
            .{display_name},
        );
        defer allocator.free(msg);

        var labels_buf: [2]diagnostic.LabeledSpan = undefined;
        var label_len: usize = 0;
        labels_buf[label_len] = .{
            .span = primary_span,
            .label = "conflicting exported symbol defined here",
            .style = .primary,
        };
        label_len += 1;
        if (!prev_sym_idx.isNone() and prev_sym_idx.asInt() < sym_table.symbols.items.len) {
            const prev_span = sym_table.getSymbol(prev_sym_idx).decl_span;
            if (!prev_span.file_id.isNone()) {
                labels_buf[label_len] = .{
                    .span = prev_span,
                    .label = "first exported definition here",
                    .style = .secondary,
                };
                label_len += 1;
            }
        }
        try sink.emit(.{
            .code = .e0011_native_links_collision,
            .severity = .err,
            .primary_span = primary_span,
            .message = msg,
            .labels = labels_buf[0..label_len],
            .notes = &[_][]const u8{
                "help: rename one of the `@export` / `@link_name` / `@wasm_export` symbols to avoid linker collision",
            },
        });
    }
    return error.BackendFailure;
}

/// Emits deterministic ISO C99 source for `input` and optionally compiles/links via `zig cc`.
pub fn emitModule(
    allocator: std.mem.Allocator,
    cfg: CBackendConfig,
    input: CodegenModuleInput,
) CCodegenError!CodegenArtifact {
    var emitter = CModuleEmitter.init(allocator, cfg, input);
    defer emitter.deinit();

    var dev_seam_bytes: ?[]u8 = null;
    errdefer if (dev_seam_bytes) |buf| allocator.free(buf);

    emitter.writeAll("/* Generated deterministically by CoreX Stage-0 Tier A (-ofmt=c) */\n/* module: ") catch
        return error.OutOfMemory;
    for (input.module_name) |ch_b| {
        if (ch_b >= 0x20 and ch_b <= 0x7E and ch_b != '*') {
            emitter.out.append(allocator, ch_b) catch return error.OutOfMemory;
        } else {
            emitter.writeAll("_") catch return error.OutOfMemory;
        }
    }
    emitter.print(" | target: {s} */\n\n", .{
        formatC99BannerTargetName(cfg.target),
    }) catch return error.OutOfMemory;

    if (cfg.target.isFreestanding()) {
        emitter.writeAll(C99_FREESTANDING_PREAMBLE) catch return error.OutOfMemory;
        emitter.writeAll(C99_ARITH_HELPERS) catch return error.OutOfMemory;
        emitter.writeAll(C99_FREESTANDING_TAIL) catch return error.OutOfMemory;
    } else {
        emitter.writeAll(C99_RUNTIME_PREAMBLE) catch return error.OutOfMemory;
        emitter.writeAll(C99_ARITH_HELPERS) catch return error.OutOfMemory;
        emitter.writeAll(C99_HOSTED_ARITH_FMT) catch return error.OutOfMemory;
        emitter.writeAll(C99_FMT_HELPERS) catch return error.OutOfMemory;
    }
    emitter.writeAll("\n") catch return error.OutOfMemory;

    var has_any_async = false;
    for (input.bodies) |*body_ptr| {
        if (mir_async.hasBodyAsyncOperations(body_ptr)) {
            has_any_async = true;
            break;
        }
    }
    if (has_any_async) {
        const cloned_bodies = allocator.alloc(MirBody, input.bodies.len) catch return error.OutOfMemory;
        var cloned_count: usize = 0;
        errdefer {
            for (cloned_bodies[0..cloned_count]) |*cb| cb.deinit();
            allocator.free(cloned_bodies);
        }
        for (input.bodies, 0..) |*src_b, idx| {
            cloned_bodies[idx] = src_b.clone(allocator) catch return error.OutOfMemory;
            cloned_count += 1;
        }
        const plan = mir_async.prepareAndAnalyzeAsyncModule(
            allocator,
            cloned_bodies,
            input.pool,
            input.sym_table,
            emitter.target_layout,
            null,
        ) catch |err| {
            return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
        };
        emitter.owned_async_bodies = cloned_bodies;
        emitter.async_plan = plan;
        emitter.input.bodies = cloned_bodies;
        emitter.has_async_ops = true;
        emitter.has_context_ops = true;
    }

    indexModuleEntities(&emitter) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };
    const is_sdkless_msvc_obj = cfg.target.os == .windows and cfg.target.abi == .msvc and
        (input.artifact_kind == .object_file or input.artifact_kind == .static_library);
    if (cfg.target.isFreestanding() or is_sdkless_msvc_obj) {
        emitter.ordered_fmt_types.clearRetainingCapacity();
    }
    emitTypeDeclarations(&emitter) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };
    emitRodataAndDevSeam(&emitter, &dev_seam_bytes) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };
    emitCallablePrototypesAndDrops(&emitter) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };

    for (emitter.input.bodies, 0..) |*body_ptr, b_idx| {
        emitMirBody(&emitter, @intCast(b_idx), body_ptr) catch |err| {
            return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
        };
    }

    emitMainEntrypointWrapper(&emitter) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };

    const emitted_c = emitter.out.toOwnedSlice(allocator) catch return error.OutOfMemory;
    errdefer allocator.free(emitted_c);

    var written_path: ?[]u8 = null;
    if (input.artifact_kind == .source_text) {
        if (input.output_path) |out_path| {
            const io = input.io orelse return error.MissingOutputConfig;
            codegen_abi.atomicWriteOutputFile(io, allocator, out_path, emitted_c) catch
                return error.BackendFailure;
            written_path = allocator.dupe(u8, out_path) catch return error.OutOfMemory;
        }
    } else {
        written_path = try compileCSourceWithZigDriver(
            allocator,
            cfg,
            input,
            emitted_c,
            emitter.collected_link_libs.items,
        );
    }

    return .{
        .emitted_text = emitted_c,
        .dev_seam_bytes = dev_seam_bytes,
        .written_output_path = written_path,
    };
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_codegen_c_source_loc_fmt_atomics_variadics_and_bytes" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    const host_spec = TargetSpec.host();

    // [1] Variadic `extern "C" fn` + `*opaque` / `*mut opaque` C99 emission and `zig cc -c` object verification:
    const variadic_src =
        \\extern "C" fn c_var_log(ctx: *mut opaque, tag: *opaque, fmt: *u8, ...) -> i32;
        \\pub fn invoke_variadic(ctx: *mut opaque, tag: *opaque) -> i32 {
        \\    let fmt_bytes: &[u8; 6] = b"%d-%x\x00";
        \\    let flag: bool = true;
        \\    let small: u8 = 7;
        \\    let ratio: f32 = 1.5;
        \\    return unsafe {
        \\        c_var_log(ctx, tag, (&raw fmt_bytes[0]), flag, small, ratio, 0x2a_i32)
        \\    };
        \\}
    ;
    var var_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(201),
        variadic_src,
        host_spec.asTargetLayout(),
        .{},
    );
    defer var_bundle.deinit();
    try std.testing.expect(!var_bundle.hir_bundle.diagnostics.hasErrors());

    const obj_out_path = std.fmt.allocPrint(
        allocator,
        ".zig-cache/test_phase76_c_var{s}",
        .{host_spec.objectExtension()},
    ) catch unreachable;
    defer allocator.free(obj_out_path);
    defer std.Io.Dir.cwd().deleteFile(io, obj_out_path) catch {};

    var var_art = try emitModule(
        allocator,
        .{ .target = host_spec },
        .{
            .bodies = var_bundle.mir_bundle.bodies.items,
            .pool = &var_bundle.hir_bundle.pool,
            .sym_table = &var_bundle.hir_bundle.sym_table,
            .interner = &var_bundle.hir_bundle.interner,
            .module_name = "test_c_variadic",
            .artifact_kind = .object_file,
            .output_path = obj_out_path,
            .io = io,
        },
    );
    defer var_art.deinit(allocator);

    try std.testing.expect(std.mem.indexOf(u8, var_art.emitted_text, "void *, const void *, uint8_t *, ...") != null);
    try std.testing.expect(std.mem.indexOf(u8, var_art.emitted_text, "c_var_log") != null);

    // [2] End-to-end executable verification: `SourceLoc` (both `.field` & `aggregate_extract`), `fmt_value`,
    // static 0-hole `FmtArgs`, `Atomic*` interior mutability (`MemoryOrder` `0..5`), `b"…"`, & `~vec`:
    const exec_src =
        \\pub enum MemoryOrder: u8 {
        \\    Relaxed = 0,
        \\    Consume = 1,
        \\    Acquire = 2,
        \\    Release = 3,
        \\    AcqRel = 4,
        \\    SeqCst = 5,
        \\}
        \\pub struct AtomicBox {
        \\    pub val: u32,
        \\}
        \\impl AtomicBox {
        \\    pub fn fetch_add(&self, delta: u32, order: MemoryOrder) -> u32 {
        \\        return unsafe { @atomic_rmw_add((&raw self.val) as *mut u32, delta, order as u8) };
        \\    }
        \\    pub fn load(&self, order: MemoryOrder) -> u32 {
        \\        return unsafe { @atomic_load(&raw self.val, order as u8) };
        \\    }
        \\}
        \\pub fn read_loc(loc: SourceLoc = @caller_location()) -> u32 {
        \\    let fn_len: u32 = loc.fn_name.len() as u32;
        \\    return loc.line * 10 + (@caller_location().col) + fn_len;
        \\}
        \\pub enum SignedKind: i16 {
        \\    Low = -5,
        \\    High = 9,
        \\}
        \\pub fn static_fmt_msg() -> FmtArgs {
        \\    let msg: FmtArgs = "ok";
        \\    return msg;
        \\}
        \\pub fn main() -> i32 {
        \\    let counter = AtomicBox { val: 10 };
        \\    let p0: u32 = counter.fetch_add(5, .Relaxed);
        \\    let p1: u32 = counter.fetch_add(7, .Consume);
        \\    let p2: u32 = counter.fetch_add(3, .SeqCst);
        \\    let cur: u32 = counter.load(.Acquire);
        \\    var scratch: u32 = 1;
        \\    let opaque_mut: *mut opaque = (&raw mut scratch) as *mut opaque;
        \\    unsafe { (opaque_mut as *mut u32).* = 9; }
        \\    let b_lit: &[u8; 3] = b"ABC";
        \\    let vec: [u8; 4] = [0xF0, 0x0F, 0xAA, 0x55];
        \\    let inv: [u8; 4] = ~vec;
        \\    let _keep: FmtArgs = static_fmt_msg();
        \\    let loc_score: u32 = read_loc();
        \\    let label: str = "hi";
        \\    let num: u32 = 0x2a;
        \\    let neg: i32 = -1;
        \\    let sk: SignedKind = .Low;
        \\    let sk_tag: u32 = match sk {
        \\        .Low => 1,
        \\        .High => 2,
        \\    };
        \\    let dyn_fa: FmtArgs = "k={num:02x},{sk:?}";
        \\    let formatted: str = "{num:08x}|{label:>6}|{num=}|{neg:x}|{dyn_fa}";
        \\    let _written: isize = @sys_write(1, formatted);
        \\    let total: u32 = p0 + p1 + p2 + cur + scratch + (b_lit[0] as u32) + (inv[0] as u32) + sk_tag;
        \\    if total == 162 and loc_score > 200 {
        \\        return 0;
        \\    }
        \\    return 1;
        \\}
    ;
    var exec_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(202),
        exec_src,
        host_spec.asTargetLayout(),
        .{},
    );
    defer exec_bundle.deinit();
    try std.testing.expect(!exec_bundle.hir_bundle.diagnostics.hasErrors());

    const exe_out_path = std.fmt.allocPrint(
        allocator,
        ".zig-cache/test_phase76_c_exec{s}",
        .{host_spec.executableExtension()},
    ) catch unreachable;
    defer allocator.free(exe_out_path);
    defer std.Io.Dir.cwd().deleteFile(io, exe_out_path) catch {};

    var exec_art = try emitModule(
        allocator,
        .{ .target = host_spec },
        .{
            .bodies = exec_bundle.mir_bundle.bodies.items,
            .pool = &exec_bundle.hir_bundle.pool,
            .sym_table = &exec_bundle.hir_bundle.sym_table,
            .interner = &exec_bundle.hir_bundle.interner,
            .module_name = "test_c_exec",
            .artifact_kind = .executable,
            .output_path = exe_out_path,
            .io = io,
        },
    );
    defer exec_art.deinit(allocator);

    try std.testing.expect(std.mem.indexOf(u8, exec_art.emitted_text, "static const cx_source_loc_data_t _cx_loc_0") != null);
    try std.testing.expect(std.mem.indexOf(u8, exec_art.emitted_text, "static const cx_str_t _fsp_") != null);

    const run_res = try std.process.run(allocator, io, .{ .argv = &.{exe_out_path} });
    defer allocator.free(run_res.stdout);
    defer allocator.free(run_res.stderr);
    try std.testing.expect(run_res.term.success());
    try std.testing.expectEqualStrings("0000002a|    hi|num=42|ffffffff|k=2a,Low", run_res.stdout);
}

test "test_codegen_c_zero_env_own_closure_cmpxchg_and_float_fmt" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    const host_spec = TargetSpec.host();

    const reg_src =
        \\pub enum Mask128: u128 {
        \\    Low = 1,
        \\    High = 2,
        \\}
        \\pub extern "C" fn bounce_mask128(mask_in: Mask128) -> Mask128 {
        \\    return mask_in;
        \\}
        \\pub fn eval_zero_env_own_niche() -> i32 {
        \\    let some_cb: (own |i32| -> i32)? = .Some(own |val: i32| -> i32 { return val + 40; });
        \\    let none_cb: (own |i32| -> i32)? = .None;
        \\    let hit_val: i32 = match some_cb {
        \\        .Some(cb_fn) => cb_fn(2),
        \\        .None => -100,
        \\    };
        \\    let miss_val: i32 = match none_cb {
        \\        .Some(cb_fn2) => cb_fn2(2),
        \\        .None => 7,
        \\    };
        \\    return hit_val + miss_val;
        \\}
        \\pub fn probe_cmpxchg_six_arg(weak_flag: u8) -> u32 {
        \\    var cell: u32 = 10;
        \\    let (prev_val, is_ok) = unsafe {
        \\        @atomic_cmpxchg(&raw mut cell, 10_u32, 25_u32, 5_u8, 5_u8, weak_flag != 0)
        \\    };
        \\    if is_ok {
        \\        return prev_val + cell;
        \\    }
        \\    return cell;
        \\}
        \\pub fn render_float_parity(seed_five: f64) -> str {
        \\    let f_tiny: f64 = 1.0e-13;
        \\    let f_small: f64 = 1.0e-5;
        \\    let f_big: f64 = 1.0e16;
        \\    let zero_f: f64 = seed_five - 5.0;
        \\    let f_nan: f64 = zero_f / zero_f;
        \\    let f_inf: f64 = 1.0 / zero_f;
        \\    let f_ninf: f64 = -1.0 / zero_f;
        \\    let part_a: str = "{seed_five}|{seed_five:?}|{f_tiny}|{f_small}|{f_big}";
        \\    let part_b: str = "{f_nan}|{f_nan:+}|{f_nan:E}|{f_inf}|{f_inf:+}|{f_ninf}|{f_inf:E}|{f_ninf:E}";
        \\    return "{part_a}|{part_b}";
        \\}
        \\pub fn main() -> i32 {
        \\    let niche_sum: i32 = eval_zero_env_own_niche();
        \\    let cx_res: u32 = probe_cmpxchg_six_arg(1);
        \\    let bounced: Mask128 = bounce_mask128(.High);
        \\    let m_tag: i32 = match bounced {
        \\        .Low => 1,
        \\        .High => 2,
        \\    };
        \\    let rendered: str = render_float_parity(5.0);
        \\    let _wrote: isize = @sys_write(1, rendered);
        \\    if niche_sum == 49 and (cx_res == 35 or cx_res == 10) and m_tag == 2 {
        \\        return 0;
        \\    }
        \\    return 1;
        \\}
    ;

    var reg_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(203),
        reg_src,
        host_spec.asTargetLayout(),
        .{},
    );
    defer reg_bundle.deinit();
    try std.testing.expect(!reg_bundle.hir_bundle.diagnostics.hasErrors());

    const exe_path = try std.fmt.allocPrint(
        allocator,
        ".zig-cache/test_stage4_c_reg{s}",
        .{host_spec.executableExtension()},
    );
    defer allocator.free(exe_path);
    defer std.Io.Dir.cwd().deleteFile(io, exe_path) catch {};

    var reg_art = try emitModule(
        allocator,
        .{ .target = host_spec },
        .{
            .bodies = reg_bundle.mir_bundle.bodies.items,
            .pool = &reg_bundle.hir_bundle.pool,
            .sym_table = &reg_bundle.hir_bundle.sym_table,
            .interner = &reg_bundle.hir_bundle.interner,
            .module_name = "test_stage4_c",
            .artifact_kind = .executable,
            .output_path = exe_path,
            .io = io,
        },
    );
    defer reg_art.deinit(allocator);

    try std.testing.expect(std.mem.indexOf(u8, reg_art.emitted_text, "((bool)(_v_") != null);

    const run_out = try std.process.run(allocator, io, .{ .argv = &.{exe_path} });
    defer allocator.free(run_out.stdout);
    defer allocator.free(run_out.stderr);
    try std.testing.expect(run_out.term.success());
    try std.testing.expectEqualStrings(
        "5|5|1e-13|1e-5|1e16|nan|nan|NAN|inf|+inf|-inf|INF|-INF",
        run_out.stdout,
    );
}

test "test_codegen_c_freestanding_wasm_and_sdkless_aarch64_msvc_obj" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Freestanding `wasm32-unknown-freestanding` (`< 10 KB` `.wasm`, zero hosted libc headers, `@wasm_import`/`@wasm_export`):
    const wasm_src =
        \\@wasm_import("host_env", "host_tick")
        \\extern "C" fn host_tick(delta: i32) -> i32;
        \\
        \\@wasm_export("wasm_step")
        \\pub fn wasm_step(seed: i32) -> i32 {
        \\    if seed < 0 {
        \\        @panic("negative seed");
        \\    }
        \\    return unsafe { host_tick(seed + 1) };
        \\}
    ;
    var wasm_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(210),
        wasm_src,
        TargetSpec.WASM32_UNKNOWN_FREESTANDING.asTargetLayout(),
        .{},
    );
    defer wasm_bundle.deinit();
    try std.testing.expect(!wasm_bundle.hir_bundle.diagnostics.hasErrors());

    const wasm_path = ".zig-cache/test_phase8_c_freestanding.wasm";
    defer std.Io.Dir.cwd().deleteFile(io, wasm_path) catch {};

    var wasm_art = try emitModule(
        allocator,
        .{ .target = TargetSpec.WASM32_UNKNOWN_FREESTANDING, .is_release_mode = true },
        .{
            .bodies = wasm_bundle.mir_bundle.bodies.items,
            .pool = &wasm_bundle.hir_bundle.pool,
            .sym_table = &wasm_bundle.hir_bundle.sym_table,
            .interner = &wasm_bundle.hir_bundle.interner,
            .module_name = "test_wasm_fs",
            .artifact_kind = .executable,
            .output_path = wasm_path,
            .io = io,
        },
    );
    defer wasm_art.deinit(allocator);

    try std.testing.expect(std.mem.indexOf(u8, wasm_art.emitted_text, "<stdio.h>") == null);
    try std.testing.expect(std.mem.indexOf(u8, wasm_art.emitted_text, "<stdlib.h>") == null);
    try std.testing.expect(std.mem.indexOf(u8, wasm_art.emitted_text, "<string.h>") == null);
    try std.testing.expect(std.mem.indexOf(u8, wasm_art.emitted_text, "<inttypes.h>") == null);
    try std.testing.expect(std.mem.indexOf(u8, wasm_art.emitted_text, "int main(") == null);
    try std.testing.expect(
        std.mem.indexOf(u8, wasm_art.emitted_text, "import_module(\"host_env\"), import_name(\"host_tick\")") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, wasm_art.emitted_text, "export_name(\"wasm_step\")") != null);

    const wasm_file = try std.Io.Dir.cwd().openFile(io, wasm_path, .{ .mode = .read_only });
    defer wasm_file.close(io);
    const wasm_size: usize = @intCast((try wasm_file.stat(io)).size);
    try std.testing.expect(wasm_size >= 8 and wasm_size < 10_240);

    // [2] SDK-less `aarch64-windows-msvc` `.obj` and `.lib` static archive emission:
    const arm64_src =
        \\@export
        \\@link_name("cx_arm64_add")
        \\pub fn arm64_add(lhs_val: i32, rhs_val: i32) -> i32 {
        \\    return lhs_val +% rhs_val;
        \\}
    ;
    var arm64_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(211),
        arm64_src,
        TargetSpec.AARCH64_WINDOWS_MSVC.asTargetLayout(),
        .{},
    );
    defer arm64_bundle.deinit();
    try std.testing.expect(!arm64_bundle.hir_bundle.diagnostics.hasErrors());

    const arm64_obj_path = ".zig-cache/test_phase8_c_arm64.obj";
    const arm64_lib_path = ".zig-cache/test_phase8_c_arm64.lib";
    defer std.Io.Dir.cwd().deleteFile(io, arm64_obj_path) catch {};
    defer std.Io.Dir.cwd().deleteFile(io, arm64_lib_path) catch {};

    var obj_art = try emitModule(
        allocator,
        .{ .target = TargetSpec.AARCH64_WINDOWS_MSVC, .is_release_mode = true },
        .{
            .bodies = arm64_bundle.mir_bundle.bodies.items,
            .pool = &arm64_bundle.hir_bundle.pool,
            .sym_table = &arm64_bundle.hir_bundle.sym_table,
            .interner = &arm64_bundle.hir_bundle.interner,
            .module_name = "test_arm64_msvc",
            .artifact_kind = .object_file,
            .output_path = arm64_obj_path,
            .io = io,
        },
    );
    defer obj_art.deinit(allocator);

    var lib_art = try emitModule(
        allocator,
        .{ .target = TargetSpec.AARCH64_WINDOWS_MSVC, .is_release_mode = true },
        .{
            .bodies = arm64_bundle.mir_bundle.bodies.items,
            .pool = &arm64_bundle.hir_bundle.pool,
            .sym_table = &arm64_bundle.hir_bundle.sym_table,
            .interner = &arm64_bundle.hir_bundle.interner,
            .module_name = "test_arm64_msvc_lib",
            .artifact_kind = .static_library,
            .output_path = arm64_lib_path,
            .io = io,
        },
    );
    defer lib_art.deinit(allocator);

    const lib_file = try std.Io.Dir.cwd().openFile(io, arm64_lib_path, .{ .mode = .read_only });
    defer lib_file.close(io);
    try std.testing.expect((try lib_file.stat(io)).size > 8);
}

test "test_phase9_duplicate_link_name_main_emits_e0011" {
    const allocator = std.testing.allocator;
    const dup_main_src =
        \\@link_name("main")
        \\pub fn entry_one() -> i32 = 0;
        \\@link_name("main")
        \\pub fn entry_two() -> i32 = 1;
    ;
    var dup_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(99),
        dup_main_src,
        TargetSpec.X86_64_LINUX_GNU.asTargetLayout(),
        .{},
    );
    defer dup_bundle.deinit();
    var dup_sink = diagnostic.DiagnosticSink.init(allocator);
    defer dup_sink.deinit();
    try std.testing.expectError(
        error.BackendFailure,
        emitModule(
            allocator,
            .{ .target = TargetSpec.X86_64_LINUX_GNU, .is_release_mode = false },
            .{
                .bodies = dup_bundle.mir_bundle.bodies.items,
                .pool = &dup_bundle.hir_bundle.pool,
                .sym_table = &dup_bundle.hir_bundle.sym_table,
                .interner = &dup_bundle.hir_bundle.interner,
                .module_name = "dup_user_main",
                .artifact_kind = .source_text,
                .diagnostic_sink = &dup_sink,
            },
        ),
    );
    var has_e0011 = false;
    for (dup_sink.asSlice()) |diag_item| {
        if (diag_item.code == .e0011_native_links_collision) has_e0011 = true;
    }
    try std.testing.expect(has_e0011);
}

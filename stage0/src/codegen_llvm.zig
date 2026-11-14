//! CoreX Stage-0 Tier B Backend (LLVM 20–23 Opaque-Pointer `.ll` Emitter & Driver)
//!
//! Lowers canonical Block-Argument SSA `MirBody` modules (`DR-07`, `DR-09`, `DR-18`, `DR-19`,
//! `DR-20`, and `phase7_spec.md` §3–§4) into deterministic LLVM 20–23 opaque-pointer (`ptr`)
//! textual IR across all 7 supported targets (`x86_64-linux`, `x86_64-macos`, `x86_64-windows`,
//! `aarch64-linux`, `aarch64-macos`, `aarch64-windows`, and `wasm32-wasi`), and compiles objects
//! or executables via the optional `-Dllvm-prefix` C++20 `PassBuilder` static bridge or `zig cc`.
//!
//! Key Invariants:
//! - Two-pass basic-block emission collects all `alloca`s (including a single `swifterror` caller
//!   slot `%_cx_call_err = alloca swifterror ptr, align 8`) and hoisted MVS
//!   `@llvm.experimental.noalias.scope.decl` intrinsics into entry block `_bb_0` (`DR-09` §4.1),
//!   tracks exact post-split predecessor labels for `phi` headers, and synthesizes `_bb_edge_<idx>`
//!   trampolines whenever a multi-way terminator branches to the same target block more than once
//!   (`[CRITICAL-05]`).
//! - Exact `AbiClassifier` (`AbiFnRecipe`) lowering for `cx_native` (`swiftcc`), `cx_result_cc`
//!   (`swiftcc` + bare `ptr swifterror %_cx_err_slot`, `[CRITICAL-06]`), platform `c_system` FFI,
//!   and `wasm_mvp`.
//! - Pentagon `ProvenValueRange` lowering (`[MAJOR-08]`): `!range` + `!noundef` strictly on scalar
//!   integer `load`/`call` instructions when `!is_full_domain` and `bit_width <= 64`,
//!   `@llvm.assume` `"nonnull"`/`"align"` operand bundles on pointers, and `nsw`/`nuw` promotion.
//! - Zero C++ unwind LSDA (`nounwind uwtable(sync)` on native, `nounwind` on `wasm32`, `Prune-04`)
//!   and minimal DWARF v5 `LineTablesOnly` metadata (`-gz=zstd` on Linux ELF).

const std = @import("std");
const build_options = @import("build_options");
const mem_foundation = @import("mem_foundation.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const diagnostic = @import("diag/diagnostic.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const query_db = @import("query_db.zig");
const hir = @import("hir.zig");
const mir = @import("mir.zig");
const codegen_abi = @import("codegen_abi.zig");
const codegen_dev_seam = @import("codegen_dev_seam.zig");
const codegen_c = @import("codegen_c.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const TokenIndex = mem_foundation.TokenIndex;
const MirBlockId = mem_foundation.MirBlockId;
const MirValueId = mem_foundation.MirValueId;
const TypeId = mem_foundation.TypeId;
const DefId = query_db.DefId;

const SymbolIndex = symbol_resolver.SymbolIndex;
const ParamMode = type_system.ParamMode;
const TargetLayout = type_system.TargetLayout;
const MirBody = mir.MirBody;
const PlaceId = mir.PlaceId;

const TargetSpec = codegen_abi.TargetSpec;
const TypeLayoutResolver = codegen_abi.TypeLayoutResolver;
const ResolvedSumDetail = codegen_abi.ResolvedSumDetail;
const AbiClassifier = codegen_abi.AbiClassifier;
const AbiFnRecipe = codegen_abi.AbiFnRecipe;
const AbiParamRecipe = codegen_abi.AbiParamRecipe;
const FnParamSpec = codegen_abi.FnParamSpec;
const FnSignatureView = type_system.FnSignatureView;
const ProvenValueRange = codegen_abi.ProvenValueRange;
const LlvmBackendConfig = codegen_abi.LlvmBackendConfig;
const CodegenModuleInput = codegen_abi.CodegenModuleInput;
const CodegenArtifact = codegen_abi.CodegenArtifact;

// ---------------------------------------- TYPES ----------------------------------------

/// Pure C99 FFI declarations mirroring `stage0/src/corex_llvm.h` (`AGENTS.md` §1, zero `void*`).
const c_llvm_bridge = struct {
    /// Mirrors `CxLlvmCompileRequest` in `stage0/src/corex_llvm.h`.
    pub const CxLlvmCompileRequest = extern struct {
        /// NUL-terminated LLVM target triple string.
        target_triple: [*:0]const u8,
        /// NUL-terminated LLVM target CPU name (`"generic"`).
        target_cpu: [*:0]const u8,
        /// NUL-terminated comma-separated target feature string.
        target_features: [*:0]const u8,
        /// NUL-terminated logical module identifier.
        module_name: [*:0]const u8,
        /// Borrowed pointer to textual `.ll` IR bytes.
        ir_text_ptr: [*]const u8,
        /// Byte length of `ir_text_ptr`.
        ir_text_len: usize,
        /// NUL-terminated staged object output path.
        output_obj_path: [*:0]const u8,
        /// `CxLlvmOptLevel` (`0`..`3`).
        opt_level: u8,
        /// `1` when `OptimizerLastEP` `SanitizerCoveragePass` is enabled.
        is_fuzz_sancov: u8,
        /// `1` for PIC relocation model.
        is_pic: u8,
        /// Explicit alignment padding byte (`0`).
        _pad: u8,
    };

    /// Success status code matching `CX_LLVM_OK` (`0`) in `stage0/src/corex_llvm.h`.
    pub const CX_LLVM_OK: i32 = 0;

    /// C99 bridge entrypoint defined in `stage0/src/corex_llvm.cpp` when `-Dllvm-prefix` is enabled.
    pub extern "c" fn cx_llvm_compile_ir_to_object(
        request: *const CxLlvmCompileRequest,
        err_buf: [*]u8,
        err_buf_cap: usize,
    ) i32;
};

/// Error set returned by Tier B LLVM 20–23 emission and driver compilation.
pub const LlvmCodegenError = error{
    /// Backing allocator exhausted during IR emission or driver argument assembly.
    OutOfMemory,
    /// `.object_file` or `.executable` requested without `output_path` or `io`.
    MissingOutputConfig,
    /// Internal IR emission, layout, or static C++ bridge compilation failure.
    BackendFailure,
    /// External `zig cc` object compilation or link invocation returned non-zero.
    CompilerDriverFailed,
};

/// Resolved integer width and signedness descriptor for scalar integer types.
const IntScalarInfo = struct {
    /// Exact integer bit-width (`8`, `16`, `32`, `64`, or `128`).
    bits: u16,
    /// `true` for signed two's-complement types (`i8..i128`, `isize`), `false` for unsigned.
    is_signed: bool,
};

/// Discovered closure environment and forwarding-thunk specification.
const ClosureThunkSpec = struct {
    /// Owning caller `MirBody` index containing the `.closure_make` instruction.
    owner_body_idx: u32,
    /// Raw `MirValueId` of the `.closure_make` instruction.
    inst_val_raw: u32,
    /// Target closure `MirBody` index invoked by the generated thunk.
    callee_body_idx: u32,
    /// Concrete `closure_ty` `TypeId`.
    closure_ty: TypeId,
    /// Captured environment field `TypeId`s in capture order (owned by `allocator`).
    capture_types: []TypeId,
};

/// Lowered `MirPlace` address or compile-time array length constant.
const PlaceLoweringResult = union(enum) {
    /// Compile-time constant array/SoA length yielded by `.slice_len` on fixed `[T; N]`.
    const_len: struct {
        /// Element count of the fixed-capacity array.
        elem_count: u64,
    },
    /// Addressable memory pointer SSA name (`%…` or `@…`) and projected pointee `TypeId`.
    addr_val: struct {
        /// Owned LLVM pointer operand string (`%_loc_1`, `%_gep_4`, …).
        ptr_str: []u8,
        /// Unwrapped concrete `TypeId` stored at `ptr_str`.
        pointee_ty: TypeId,
        /// Byte alignment (`>= 1`) proven for `ptr_str`.
        align_bytes: u32,
        /// Root formal parameter local index (`1 .. param_count`) if directly rooted, else `0`.
        root_param_local: u32 = 0,
    },
};

/// Synthetic duplicate-predecessor trampoline block `_bb_edge_<tramp_idx>` (`[CRITICAL-05]`).
const TrampolineEdge = struct {
    /// Zero-based trampoline index within the enclosing `MirBody`.
    tramp_idx: u32,
    /// Originating `EdgeId` index in `body.extra_edges`.
    edge_idx: u32,
    /// Target `MirBlockId` jumped to by `br label %_bb_<target>`.
    target_bb: MirBlockId,
};

/// Disjoint MVS parameter alias-scope metadata IDs hoisted to function entry (`DR-09` §4.1).
const MvsParamScope = struct {
    /// Formal parameter local index (`1 .. body.param_count`).
    local_idx: u32,
    /// Metadata node ID of `!<list_id> = !{!<scope_id>}` for `!alias.scope`.
    scope_list_md: u32,
    /// Optional metadata node ID of `!<other_list_id>` for `!noalias` (`0` when single-param).
    noalias_list_md: u32,
};

/// Lowered LLVM loop metadata IDs attached to latch back-edges and loop memory instructions.
const LoopIrMetadata = struct {
    /// Loop header `MirBlockId`.
    header_bb: MirBlockId,
    /// Loop latch `MirBlockId`.
    latch_bb: MirBlockId,
    /// Optional `!llvm.access.group` distinct metadata ID (`0` when unused).
    access_group_md: u32,
    /// `!llvm.loop` distinct metadata ID attached to `latch_bb`'s terminator `br`.
    loop_md: u32,
};

/// Per-function state during two-pass LLVM IR basic-block emission.
const BodyEmitState = struct {
    /// Backing allocator.
    allocator: std.mem.Allocator,
    /// Entry-block `alloca` buffer emitted at the top of `_bb_0`.
    entry_allocas: std.ArrayListUnmanaged(u8) = .empty,
    /// Active block instruction buffer during Pass 1.
    cur_buf: std.ArrayListUnmanaged(u8) = .empty,
    /// Active LLVM basic-block label name (without leading `%`, e.g., `"_bb_0"` or `"_ok_4"`).
    cur_label: []u8,
    /// `true` once `%_cx_call_err = alloca swifterror ptr, align 8` is added to `entry_allocas`.
    has_swifterror_call_slot: bool = false,
    /// Monotonic local temporary counter (`%_t_<k>`, `%_scratch_<k>`, `_ok_<k>`).
    next_tmp_id: u32 = 0,
    /// Per-local LLVM pointer operand string (`%_loc_<i>` or `%_arg_p<i>`, empty when ZST).
    local_ptrs: [][]u8,
    /// Per-local alignment in bytes.
    local_aligns: []u32,
    /// Per-edge final predecessor label (`%_bb_…`, `%_ok_…`, `%_bb_edge_…`, or `%_call_join_…`).
    edge_pred_labels: [][]u8,
    /// Per-edge reconstructed call return SSA value string for `.call` normal edges.
    edge_call_ret_vals: [][]u8,
    /// Per-edge optional synthetic trampoline index (`null` when direct).
    edge_trampoline: []?u32,
    /// Synthetic trampolines generated for multi-way duplicate targets (`[CRITICAL-05]`).
    trampolines: std.ArrayListUnmanaged(TrampolineEdge) = .empty,
    /// MVS alias scopes hoisted into `_bb_0`.
    mvs_scopes: std.ArrayListUnmanaged(MvsParamScope) = .empty,
    /// Loop vectorization metadata records for `body.loop_contracts`.
    loop_mds: std.ArrayListUnmanaged(LoopIrMetadata) = .empty,
    /// Per-block active `!llvm.access.group` metadata ID (`0` outside `@must_vectorize` loops).
    block_access_group: []u32,
    /// Optional `!DISubprogram` metadata ID (`0` when debug info is omitted).
    subprogram_md: u32 = 0,
    /// Active `!DILocation` metadata ID (`0` when unset).
    active_dbg_loc_md: u32 = 0,

    /// Releases all per-function buffers and owned label slices.
    fn deinit(self: *BodyEmitState) void {
        self.entry_allocas.deinit(self.allocator);
        self.cur_buf.deinit(self.allocator);
        if (self.cur_label.len > 0) self.allocator.free(self.cur_label);
        for (self.local_ptrs) |ptr_s| {
            if (ptr_s.len > 0) self.allocator.free(ptr_s);
        }
        self.allocator.free(self.local_ptrs);
        self.allocator.free(self.local_aligns);
        for (self.edge_pred_labels) |lbl_s| {
            if (lbl_s.len > 0) self.allocator.free(lbl_s);
        }
        self.allocator.free(self.edge_pred_labels);
        for (self.edge_call_ret_vals) |ret_s| {
            if (ret_s.len > 0) self.allocator.free(ret_s);
        }
        self.allocator.free(self.edge_call_ret_vals);
        self.allocator.free(self.edge_trampoline);
        self.trampolines.deinit(self.allocator);
        self.mvs_scopes.deinit(self.allocator);
        self.loop_mds.deinit(self.allocator);
        self.allocator.free(self.block_access_group);
    }

    /// Allocates the next monotonic temporary ID within this function.
    fn nextTmp(self: *BodyEmitState) u32 {
        const id = self.next_tmp_id;
        self.next_tmp_id += 1;
        return id;
    }

    /// Switches `cur_label` to `new_owned_label`, freeing the previous label buffer.
    fn setLabelOwned(self: *BodyEmitState, new_owned_label: []u8) void {
        if (self.cur_label.len > 0) self.allocator.free(self.cur_label);
        self.cur_label = new_owned_label;
    }

    /// Appends raw text to `cur_buf`.
    fn writeAll(self: *BodyEmitState, text: []const u8) !void {
        try self.cur_buf.appendSlice(self.allocator, text);
    }

    /// Appends formatted text to `cur_buf`.
    fn print(self: *BodyEmitState, comptime fmt: []const u8, args: anytype) !void {
        const formatted = try std.fmt.allocPrint(self.allocator, fmt, args);
        defer self.allocator.free(formatted);
        try self.cur_buf.appendSlice(self.allocator, formatted);
    }

    /// Allocates a fixed-size byte scratch slot in `_bb_0` and returns its owned `%_scratch_<id>` name.
    fn allocEntryBytes(self: *BodyEmitState, size_bytes: u64, align_bytes: u32) ![]u8 {
        const tmp_id = self.nextTmp();
        const clamped_sz = @max(size_bytes, 1);
        const eff_align = @max(align_bytes, 8);
        const line = try std.fmt.allocPrint(
            self.allocator,
            "  %_scratch_{d} = alloca [{d} x i8], align {d}\n",
            .{ tmp_id, clamped_sz, eff_align },
        );
        defer self.allocator.free(line);
        try self.entry_allocas.appendSlice(self.allocator, line);
        return std.fmt.allocPrint(self.allocator, "%_scratch_{d}", .{tmp_id});
    }

    /// Ensures `%_cx_call_err = alloca swifterror ptr, align 8` exists in `_bb_0`.
    fn ensureSwifterrorCallSlot(self: *BodyEmitState) !void {
        if (self.has_swifterror_call_slot) return;
        self.has_swifterror_call_slot = true;
        try self.entry_allocas.appendSlice(
            self.allocator,
            "  %_cx_call_err = alloca swifterror ptr, align 8\n",
        );
    }
};

/// Deferred `#soa` column projection state awaiting a trailing `.index` or `.slice_len`.
const PendingSoaCol = struct {
    /// Owned LLVM pointer operand addressing column element `0`.
    col_ptr: []u8,
    /// Resolved scalar/aggregate field type stored in the column.
    field_ty: TypeId,
    /// Guaranteed byte alignment of `col_ptr`.
    col_align: u32,
    /// True when backed by a fixed-capacity `#soa [S; N]` array.
    is_fixed: bool,
    /// Compile-time capacity `N` when `is_fixed` is true.
    fixed_cap: u64,
    /// Owned LLVM pointer operand addressing the `#soa [S]` slice header.
    slice_base_ptr: []u8,
};

/// Post-call copy-back record for unaligned `@packed` `inout`/`set` arguments bounced through aligned stack slots.
const InoutBounceWriteback = struct {
    /// Aligned temporary stack slot passed to the callee.
    bounce_ptr: []u8,
    /// Alignment in bytes of `bounce_ptr`.
    bounce_align: u32,
    /// Original unaligned place destination pointer.
    dst_ptr: []u8,
    /// Alignment in bytes of `dst_ptr`.
    dst_align: u32,
    /// Payload byte size copied back after the call.
    size_bytes: u64,
};

/// Deterministic module-wide LLVM 20–23 `.ll` emitter state.
const LlvmModuleEmitter = struct {
    /// Backing allocator.
    allocator: std.mem.Allocator,
    /// Active Tier B backend configuration.
    cfg: LlvmBackendConfig,
    /// Input MIR module bundle and symbol/type tables.
    input: CodegenModuleInput,
    /// Target pointer/cache/SIMD layout derived from `cfg.target`.
    target_layout: TargetLayout,
    /// Shared canonical layout, niche, and `#soa` resolver.
    resolver: TypeLayoutResolver,
    /// Primary module `.ll` output buffer.
    out: std.ArrayListUnmanaged(u8) = .empty,
    /// Deferred metadata lines (`!0 = …`) emitted at the bottom of the `.ll` module.
    meta_lines: std.ArrayListUnmanaged(u8) = .empty,
    /// Next numbered metadata ID (`!0`, `!1`, …).
    next_md_id: u32 = 0,
    /// `!DICompileUnit` metadata ID (`0` before initialization).
    di_cu_md: u32 = 0,
    /// Default `!DIFile` metadata ID.
    di_default_file_md: u32 = 0,
    /// Empty `!{}` metadata ID.
    di_empty_tuple_md: u32 = 0,
    /// `!DISubroutineType` metadata ID (`!{}`).
    di_subroutine_ty_md: u32 = 0,
    /// Map `FileId.asInt() -> !DIFile` metadata ID.
    di_file_map: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// Deduplicated `(subprogram_md << 32) | (line << 12) | col -> !DILocation` cache.
    di_loc_cache: std.AutoHashMapUnmanaged(u64, u32) = .empty,
    /// Deduplicated `!range !{iW lo, iW hi}` cache keyed by `(W, lo, hi)` hash.
    range_md_cache: std.AutoHashMapUnmanaged(u64, u32) = .empty,

    /// Canonical LLVM symbol name per `input.bodies[i]` (without leading `@`).
    body_llvm_names: std.ArrayListUnmanaged([]u8) = .empty,
    /// Cached `AbiFnRecipe` per `input.bodies[i]`.
    body_recipes: std.ArrayListUnmanaged(AbiFnRecipe) = .empty,
    /// Map `DefId.asInt() -> body_idx`.
    def_to_body: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// Map `SymbolIndex.asInt() -> body_idx`.
    sym_to_body: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// Optional index of CoreX `main` inside `input.bodies`.
    entry_main_body_idx: ?u32 = null,

    /// Topologically sorted composite `TypeId`s emitted as `%_cx_ty_<id> = type <{ … }>`.
    ordered_composites: std.ArrayListUnmanaged(TypeId) = .empty,
    /// Membership set of collected composite `TypeId.toU32()`.
    composite_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Types requiring generated `@_cx_drop_ty_<id>` helpers.
    drop_type_list: std.ArrayListUnmanaged(TypeId) = .empty,
    /// Membership set of `drop_type_list`.
    drop_type_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Referenced `extern` function `SymbolIndex` list sorted ascending.
    extern_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty,
    /// Interned string/byte literal `SymbolId.asInt()` values sorted ascending.
    str_sym_ids: std.ArrayListUnmanaged(u32) = .empty,
    /// Reflected `@type_name[T]()` `TypeId.toU32()` values sorted ascending.
    type_name_ids: std.ArrayListUnmanaged(u32) = .empty,
    /// Referenced `MirBlobStore` `blob_id` values sorted ascending.
    blob_ids: std.ArrayListUnmanaged(u32) = .empty,
    /// Discovered `.closure_make` thunks.
    closure_thunks: std.ArrayListUnmanaged(ClosureThunkSpec) = .empty,
    /// Map `(body_idx << 32) | inst_val_raw -> thunk_idx`.
    closure_thunk_map: std.AutoHashMapUnmanaged(u64, u32) = .empty,
    /// Ordered `target_body_idx` entries requiring a stateful `fn(…)` `%_cx_ctx` adapter thunk.
    ctx_wrap_bodies: std.ArrayListUnmanaged(u32) = .empty,
    /// Map `target_body_idx -> stateful fn_ty` for `@_cx_fn_ctxwrap_<target_b>`.
    ctx_wrap_map: std.AutoHashMapUnmanaged(u32, TypeId) = .empty,
    /// Required `@llvm.*` intrinsic declarations keyed by full declaration line.
    intrinsic_decls: std.StringHashMapUnmanaged(void) = .empty,
    /// Owned declaration strings stored in `intrinsic_decls`.
    owned_intrinsic_decls: std.ArrayListUnmanaged([]u8) = .empty,
    /// Synthesized module-scope `.rodata` constants and on-demand runtime helpers.
    synth_globals: std.ArrayListUnmanaged(u8) = .empty,
    /// Next monotonic ID for synthesized `.rodata` constants (`@_cx_sref_<id>`, `@_cx_dbg_<id>`).
    next_synth_id: u32 = 0,
    /// `true` once `@_cx_rt_fmt_u128` has been emitted into `synth_globals`.
    has_fmt_u128_helper: bool = false,
    /// `true` once `@_cx_rt_fmt_i128` has been emitted into `synth_globals`.
    has_fmt_i128_helper: bool = false,
    /// Deduplication set of already-declared external C/WASI symbol names (`[CRITICAL-08]`).
    declared_externs: std.StringHashMapUnmanaged(void) = .empty,
    /// Owned symbol name strings backing `declared_externs`.
    owned_declared_externs: std.ArrayListUnmanaged([]u8) = .empty,

    /// Initializes `LlvmModuleEmitter` for `cfg` and `input`.
    fn init(
        allocator: std.mem.Allocator,
        cfg: LlvmBackendConfig,
        input: CodegenModuleInput,
    ) LlvmModuleEmitter {
        return .{
            .allocator = allocator,
            .cfg = cfg,
            .input = input,
            .target_layout = cfg.target.asTargetLayout(),
            .resolver = TypeLayoutResolver.init(allocator, input.pool, input.sym_table, cfg.target),
        };
    }

    /// Releases all buffers, ABI recipes, and tables owned by `self`.
    fn deinit(self: *LlvmModuleEmitter) void {
        self.resolver.deinit();
        self.out.deinit(self.allocator);
        self.meta_lines.deinit(self.allocator);
        self.di_file_map.deinit(self.allocator);
        self.di_loc_cache.deinit(self.allocator);
        self.range_md_cache.deinit(self.allocator);
        for (self.body_llvm_names.items) |name_s| self.allocator.free(name_s);
        self.body_llvm_names.deinit(self.allocator);
        for (self.body_recipes.items) |*rec| rec.deinit(self.allocator);
        self.body_recipes.deinit(self.allocator);
        self.def_to_body.deinit(self.allocator);
        self.sym_to_body.deinit(self.allocator);
        self.ordered_composites.deinit(self.allocator);
        self.composite_set.deinit(self.allocator);
        self.drop_type_list.deinit(self.allocator);
        self.drop_type_set.deinit(self.allocator);
        self.extern_syms.deinit(self.allocator);
        self.str_sym_ids.deinit(self.allocator);
        self.type_name_ids.deinit(self.allocator);
        self.blob_ids.deinit(self.allocator);
        for (self.closure_thunks.items) |thunk| {
            if (thunk.capture_types.len > 0) self.allocator.free(thunk.capture_types);
        }
        self.closure_thunks.deinit(self.allocator);
        self.closure_thunk_map.deinit(self.allocator);
        self.ctx_wrap_bodies.deinit(self.allocator);
        self.ctx_wrap_map.deinit(self.allocator);
        self.intrinsic_decls.deinit(self.allocator);
        for (self.owned_intrinsic_decls.items) |decl_s| self.allocator.free(decl_s);
        self.owned_intrinsic_decls.deinit(self.allocator);
        self.synth_globals.deinit(self.allocator);
        self.declared_externs.deinit(self.allocator);
        for (self.owned_declared_externs.items) |ext_s| self.allocator.free(ext_s);
        self.owned_declared_externs.deinit(self.allocator);
    }

    /// Appends raw text to `self.out`.
    fn writeAll(self: *LlvmModuleEmitter, text: []const u8) !void {
        try self.out.appendSlice(self.allocator, text);
    }

    /// Appends formatted text to `self.out`.
    fn print(self: *LlvmModuleEmitter, comptime fmt: []const u8, args: anytype) !void {
        const formatted = try std.fmt.allocPrint(self.allocator, fmt, args);
        defer self.allocator.free(formatted);
        try self.out.appendSlice(self.allocator, formatted);
    }

    /// Allocates a fresh metadata node ID `!<id>` and appends `!<id> = <rhs>\n` to `meta_lines`.
    fn addMetadataNode(self: *LlvmModuleEmitter, rhs: []const u8) !u32 {
        const md_id = self.next_md_id;
        self.next_md_id += 1;
        const line = try std.fmt.allocPrint(self.allocator, "!{d} = {s}\n", .{ md_id, rhs });
        defer self.allocator.free(line);
        try self.meta_lines.appendSlice(self.allocator, line);
        return md_id;
    }

    /// Allocates a self-referential distinct metadata node (e.g., alias domain/scope or `!llvm.loop`).
    fn reserveMetadataId(self: *LlvmModuleEmitter) u32 {
        const md_id = self.next_md_id;
        self.next_md_id += 1;
        return md_id;
    }

    /// Appends a pre-reserved metadata definition `!<md_id> = <rhs>\n` to `meta_lines`.
    fn defineReservedMetadata(self: *LlvmModuleEmitter, md_id: u32, rhs: []const u8) !void {
        const line = try std.fmt.allocPrint(self.allocator, "!{d} = {s}\n", .{ md_id, rhs });
        defer self.allocator.free(line);
        try self.meta_lines.appendSlice(self.allocator, line);
    }

    /// Registers an `@llvm.*` intrinsic declaration line if not already registered.
    fn requireIntrinsicDecl(self: *LlvmModuleEmitter, decl_line: []const u8) !void {
        if (self.intrinsic_decls.contains(decl_line)) return;
        const owned = try self.allocator.dupe(u8, decl_line);
        errdefer self.allocator.free(owned);
        try self.owned_intrinsic_decls.append(self.allocator, owned);
        try self.intrinsic_decls.put(self.allocator, owned, {});
    }

    /// Records `ext_name` as declared at module scope; returns `false` if already declared.
    fn markExternDeclared(self: *LlvmModuleEmitter, ext_name: []const u8) !bool {
        if (self.declared_externs.contains(ext_name)) return false;
        const owned = try self.allocator.dupe(u8, ext_name);
        errdefer self.allocator.free(owned);
        try self.owned_declared_externs.append(self.allocator, owned);
        try self.declared_externs.put(self.allocator, owned, {});
        return true;
    }

    /// Allocates the next monotonic synthesized `.rodata` constant ID.
    fn nextSynthGlobalId(self: *LlvmModuleEmitter) u32 {
        const sid = self.next_synth_id;
        self.next_synth_id += 1;
        return sid;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum structural recursion depth for composite type registration (`AGENTS.md` §2).
const MAX_COMPOSITE_COLLECT_DEPTH: u32 = 64;

/// Bit-56 tag OR-ed onto `.tagged_int56` `swifterror` payloads so `.Err(0)` is non-null (`[CRITICAL-06]`).
const SWIFTERROR_INT56_TAG: u64 = @as(u64, 1) << 56;

/// O(1) static byte-size lookup table for fixed-size LLVM ABI register piece/aggregate types.
const ABI_TYPE_BYTE_SIZE_MAP = std.StaticStringMap(u64).initComptime(.{
    .{ "double", 8 },
    .{ "float", 4 },
    .{ "i1", 1 },
    .{ "i128", 16 },
    .{ "i16", 2 },
    .{ "i32", 4 },
    .{ "i64", 8 },
    .{ "i8", 1 },
    .{ "void", 0 },
    .{ "{ double, double }", 16 },
    .{ "{ double, float }", 12 },
    .{ "{ double, i64 }", 16 },
    .{ "{ i64, double }", 16 },
    .{ "{ i64, float }", 12 },
    .{ "{ i64, i64 }", 16 },
    .{ "{ i64, i64, i64 }", 24 },
    .{ "{ i64, i64, i64, i64 }", 32 },
    .{ "{ ptr, i64 }", 16 },
    .{ "{ ptr, ptr }", 16 },
});

/// O(1) static set of canonical `wasi_snapshot_preview1` host import names on `wasm32-wasi`.
const WASI_PREVIEW1_IMPORT_SET = std.StaticStringMap(void).initComptime(.{
    .{ "args_get", {} },
    .{ "args_sizes_get", {} },
    .{ "clock_res_get", {} },
    .{ "clock_time_get", {} },
    .{ "environ_get", {} },
    .{ "environ_sizes_get", {} },
    .{ "fd_advise", {} },
    .{ "fd_allocate", {} },
    .{ "fd_close", {} },
    .{ "fd_datasync", {} },
    .{ "fd_fdstat_get", {} },
    .{ "fd_fdstat_set_flags", {} },
    .{ "fd_fdstat_set_rights", {} },
    .{ "fd_filestat_get", {} },
    .{ "fd_filestat_set_size", {} },
    .{ "fd_filestat_set_times", {} },
    .{ "fd_pread", {} },
    .{ "fd_prestat_dir_name", {} },
    .{ "fd_prestat_get", {} },
    .{ "fd_pwrite", {} },
    .{ "fd_read", {} },
    .{ "fd_readdir", {} },
    .{ "fd_renumber", {} },
    .{ "fd_seek", {} },
    .{ "fd_sync", {} },
    .{ "fd_tell", {} },
    .{ "fd_write", {} },
    .{ "path_create_directory", {} },
    .{ "path_filestat_get", {} },
    .{ "path_filestat_set_times", {} },
    .{ "path_link", {} },
    .{ "path_open", {} },
    .{ "path_readlink", {} },
    .{ "path_remove_directory", {} },
    .{ "path_rename", {} },
    .{ "path_symlink", {} },
    .{ "path_unlink_file", {} },
    .{ "poll_oneoff", {} },
    .{ "proc_exit", {} },
    .{ "proc_raise", {} },
    .{ "random_get", {} },
    .{ "sched_yield", {} },
    .{ "sock_accept", {} },
    .{ "sock_recv", {} },
    .{ "sock_send", {} },
    .{ "sock_shutdown", {} },
});

/// Monotonic atomic counter ensuring concurrent in-process LLVM driver runs use distinct scratch dirs.
var next_llvm_scratch_seq = std.atomic.Value(u32).init(1);

// -------------------------------------- INTERNALS --------------------------------------

// --------------- Target, Type & Layout Queries ----------------

/// Returns the LLVM pointer-sized integer type (`"i32"` on `wasm32`, `"i64"` on 64-bit targets).
fn ptrIntType(emitter: *const LlvmModuleEmitter) []const u8 {
    return if (emitter.cfg.target.isWasm()) "i32" else "i64";
}

/// Returns the function attribute suffix (`"nounwind"` on `wasm32`, `"nounwind uwtable(sync)"` on native).
fn fnUnwindAttrs(emitter: *const LlvmModuleEmitter) []const u8 {
    return if (emitter.cfg.target.isWasm()) "nounwind" else "nounwind uwtable(sync)";
}

/// Returns `true` when `raw_ty` resolves to a zero-sized type (`size_bytes == 0`).
fn isZeroSizedType(emitter: *LlvmModuleEmitter, raw_ty: TypeId) !bool {
    const unwrapped = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped.isError() or unwrapped == .unit_ty or unwrapped == .never_ty) return true;
    return (try emitter.resolver.resolveType(unwrapped)).size_bytes == 0;
}

/// Resolves scalar integer bit-width and signedness for `raw_ty`, or `null` if non-integer.
fn resolveIntegerInfo(emitter: *const LlvmModuleEmitter, raw_ty: TypeId) ?IntScalarInfo {
    var ty = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    if (!ty.isPrimitiveOrSentinel()) {
        const cur_node = emitter.input.pool.getNode(ty);
        if (cur_node.tag == .bit_field_ty) {
            ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(cur_node.lhs));
        }
    }
    const ptr_bits: u16 = @as(u16, emitter.cfg.target.ptrBytes()) * 8;
    return switch (ty) {
        .i8_ty => .{ .bits = 8, .is_signed = true },
        .u8_ty => .{ .bits = 8, .is_signed = false },
        .i16_ty => .{ .bits = 16, .is_signed = true },
        .u16_ty => .{ .bits = 16, .is_signed = false },
        .i32_ty => .{ .bits = 32, .is_signed = true },
        .u32_ty, .char_ty => .{ .bits = 32, .is_signed = false },
        .i64_ty, .untyped_int_ty => .{ .bits = 64, .is_signed = true },
        .u64_ty => .{ .bits = 64, .is_signed = false },
        .i128_ty => .{ .bits = 128, .is_signed = true },
        .u128_ty => .{ .bits = 128, .is_signed = false },
        .isize_ty => .{ .bits = ptr_bits, .is_signed = true },
        .usize_ty => .{ .bits = ptr_bits, .is_signed = false },
        else => null,
    };
}

/// Unwraps transparent `Result[T, never]` (`SumReprKind.transparent_ok`) and type aliases/newtypes.
fn unwrapTransparentType(emitter: *LlvmModuleEmitter, raw_ty: TypeId) !TypeId {
    var cur_ty = emitter.input.pool.unwrapUnderlyingType(raw_ty);
    while (!cur_ty.isPrimitiveOrSentinel() and emitter.input.pool.getNode(cur_ty).tag == .result_ty) {
        if (try emitter.resolver.getSumDetail(cur_ty)) |detail| {
            if (detail.repr == .transparent_ok) {
                cur_ty = emitter.input.pool.unwrapUnderlyingType(detail.payload_ty);
                continue;
            }
        }
        break;
    }
    return cur_ty;
}

/// Returns `true` when `ty` requires a named `%_cx_ty_<id>` composite struct declaration.
fn isNamedCompositeType(emitter: *LlvmModuleEmitter, raw_ty: TypeId) !bool {
    const ty = try unwrapTransparentType(emitter, raw_ty);
    if (try isZeroSizedType(emitter, ty)) return false;
    if (ty.isPrimitiveOrSentinel()) return false;
    return switch (emitter.input.pool.getNode(ty).tag) {
        .struct_ty,
        .tuple_ty,
        .soa_array_ty,
        .union_ty,
        .enum_ty,
        .optional_ty,
        .result_ty,
        => true,
        else => false,
    };
}

/// Formats the canonical LLVM SSA value type for `raw_ty` (caller owns returned slice).
fn formatLlvmValueType(emitter: *LlvmModuleEmitter, raw_ty: TypeId) ![]u8 {
    const ty = try unwrapTransparentType(emitter, raw_ty);
    if (try isZeroSizedType(emitter, ty)) {
        return emitter.allocator.dupe(u8, "void");
    }
    if (ty == .bool_ty) return emitter.allocator.dupe(u8, "i1");
    if (ty == .f32_ty) return emitter.allocator.dupe(u8, "float");
    if (ty == .f64_ty or ty == .untyped_float_ty) return emitter.allocator.dupe(u8, "double");
    if (ty == .str_ty) {
        return std.fmt.allocPrint(emitter.allocator, "{{ ptr, {s} }}", .{ptrIntType(emitter)});
    }
    if (resolveIntegerInfo(emitter, ty)) |int_info| {
        return std.fmt.allocPrint(emitter.allocator, "i{d}", .{int_info.bits});
    }
    if (ty.isPrimitiveOrSentinel()) return emitter.allocator.dupe(u8, "i8");

    const node = emitter.input.pool.getNode(ty);
    return switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .fn_ty => emitter.allocator.dupe(u8, "ptr"),
        .closure_ty => emitter.allocator.dupe(u8, "{ ptr, ptr }"),
        .slice_ty, .soa_slice_ty => std.fmt.allocPrint(
            emitter.allocator,
            "{{ ptr, {s} }}",
            .{ptrIntType(emitter)},
        ),
        .array_ty => {
            const elem_ty = TypeId.fromInt(node.lhs);
            const elem_count: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            const elem_mem = try formatLlvmMemoryType(emitter, elem_ty);
            defer emitter.allocator.free(elem_mem);
            return std.fmt.allocPrint(emitter.allocator, "[{d} x {s}]", .{ elem_count, elem_mem });
        },
        else => std.fmt.allocPrint(emitter.allocator, "%_cx_ty_{d}", .{ty.toU32()}),
    };
}

/// Formats the canonical LLVM in-memory storage type (`i8` for `bool`, `[0 x i8]` for ZST).
fn formatLlvmMemoryType(emitter: *LlvmModuleEmitter, raw_ty: TypeId) anyerror![]u8 {
    const ty = try unwrapTransparentType(emitter, raw_ty);
    if (try isZeroSizedType(emitter, ty)) {
        return emitter.allocator.dupe(u8, "[0 x i8]");
    }
    if (ty == .bool_ty) return emitter.allocator.dupe(u8, "i8");
    return formatLlvmValueType(emitter, ty);
}

/// Resolves the zero literal (`0`, `false`, `0.0`, `null`, `zeroinitializer`) for an LLVM type string.
fn resolveZeroLiteralForLlvmType(llvm_ty: []const u8) []const u8 {
    if (std.mem.eql(u8, llvm_ty, "i1")) return "false";
    if (std.mem.eql(u8, llvm_ty, "ptr")) return "null";
    if (std.mem.eql(u8, llvm_ty, "float") or std.mem.eql(u8, llvm_ty, "double")) return "0.0";
    if (llvm_ty.len >= 2 and llvm_ty[0] == 'i' and std.ascii.isDigit(llvm_ty[1])) return "0";
    return "zeroinitializer";
}

/// Computes the alignment guaranteed for `byte_offset` relative to a base pointer (`<= natural_align`).
fn effectiveOffsetAlign(byte_offset: u64, natural_align: u32) u32 {
    const nat = @max(natural_align, 1);
    if (byte_offset == 0) return nat;
    const low_bit_u64: u64 = byte_offset & (~byte_offset +% 1);
    const low_bit: u32 = if (low_bit_u64 > @as(u64, nat)) nat else @intCast(low_bit_u64);
    return @max(@min(nat, low_bit), 1);
}

/// Recursively registers composite types reachable from `raw_ty` in deterministic topological order.
fn collectCompositeType(emitter: *LlvmModuleEmitter, raw_ty: TypeId, depth: u32) anyerror!void {
    if (depth > MAX_COMPOSITE_COLLECT_DEPTH) return;
    const ty = try unwrapTransparentType(emitter, raw_ty);
    if (try isZeroSizedType(emitter, ty)) return;
    if (ty.isPrimitiveOrSentinel()) return;

    const node = emitter.input.pool.getNode(ty);
    switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .slice_ty, .soa_slice_ty, .fn_ty, .closure_ty => return,
        .array_ty => {
            try collectCompositeType(emitter, TypeId.fromInt(node.lhs), depth + 1);
            return;
        },
        .struct_ty, .tuple_ty => {
            if (emitter.composite_set.contains(ty.toU32())) return;
            try emitter.composite_set.put(emitter.allocator, ty.toU32(), {});
            const lay = try emitter.resolver.resolveType(ty);
            var fld_i: u32 = 0;
            while (fld_i < lay.aux_len) : (fld_i += 1) {
                const fld = emitter.resolver.fields_by_decl.items[lay.aux_start + fld_i];
                if (fld.size_bytes > 0) {
                    try collectCompositeType(emitter, fld.field_ty, depth + 1);
                }
            }
            try emitter.ordered_composites.append(emitter.allocator, ty);
        },
        .soa_array_ty, .union_ty, .enum_ty, .optional_ty, .result_ty => {
            if (emitter.composite_set.contains(ty.toU32())) return;
            try emitter.composite_set.put(emitter.allocator, ty.toU32(), {});
            if (node.tag == .soa_array_ty) {
                try collectCompositeType(emitter, TypeId.fromInt(node.lhs), depth + 1);
            } else if (node.tag == .optional_ty) {
                try collectCompositeType(emitter, TypeId.fromInt(node.lhs), depth + 1);
            } else if (node.tag == .result_ty) {
                try collectCompositeType(emitter, TypeId.fromInt(node.lhs), depth + 1);
                try collectCompositeType(emitter, TypeId.fromInt(node.rhs), depth + 1);
            } else if (node.tag == .enum_ty or node.tag == .union_ty) {
                const sym_idx = SymbolIndex.fromInt(node.rhs);
                if (!sym_idx.isNone() and sym_idx.asInt() < emitter.input.sym_table.symbols.items.len) {
                    const sym_rec = emitter.input.sym_table.getSymbol(sym_idx).*;
                    if (!sym_rec.target_scope.isNone()) {
                        const subst = type_system.NominalTypeSubst.init(
                            emitter.input.pool,
                            emitter.input.sym_table,
                            ty,
                        );
                        for (emitter.input.sym_table.getScopeMembers(sym_rec.target_scope)) |mem_idx| {
                            const mem_sym = emitter.input.sym_table.getSymbol(mem_idx).*;
                            if ((mem_sym.kind == .enum_variant_sym or mem_sym.kind == .field_sym) and
                                !mem_sym.type_id.isNone())
                            {
                                try collectCompositeType(emitter, subst.resolve(mem_sym.type_id), depth + 1);
                            }
                        }
                    }
                }
            }
            try emitter.ordered_composites.append(emitter.allocator, ty);
        },
        else => {},
    }
}

/// Emits deterministic `%_cx_ty_<id> = type <{ … }>` declarations matching `TypeLayoutResolver` byte-for-byte.
fn emitCompositeTypeDeclarations(emitter: *LlvmModuleEmitter) !void {
    if (emitter.ordered_composites.items.len == 0) return;
    for (emitter.ordered_composites.items) |ty| {
        const lay = try emitter.resolver.resolveType(ty);
        if (lay.size_bytes == 0) continue;
        const node = emitter.input.pool.getNode(ty);
        if (node.tag == .struct_ty or node.tag == .tuple_ty) {
            const pad_spans_raw = try emitter.resolver.getPaddingSpans(ty);
            const pad_spans = try emitter.allocator.dupe(codegen_abi.PaddingSpan, pad_spans_raw);
            defer if (pad_spans.len > 0) emitter.allocator.free(pad_spans);

            try emitter.print("%_cx_ty_{d} = type <{{ ", .{ty.toU32()});
            var pad_cursor: usize = 0;
            var emitted_count: usize = 0;
            var phys_i: u32 = 0;
            while (phys_i < lay.aux_len) : (phys_i += 1) {
                const decl_ord = emitter.resolver.phys_to_decl.items[lay.aux_start + phys_i];
                const fld = emitter.resolver.fields_by_decl.items[lay.aux_start + decl_ord];
                while (pad_cursor < pad_spans.len and
                    pad_spans[pad_cursor].byte_offset <= fld.byte_offset)
                {
                    const pad = pad_spans[pad_cursor];
                    pad_cursor += 1;
                    if (emitted_count > 0) try emitter.writeAll(", ");
                    try emitter.print("[{d} x i8]", .{pad.byte_len});
                    emitted_count += 1;
                }
                if (fld.size_bytes == 0) continue;
                const fld_mem = try formatLlvmMemoryType(emitter, fld.field_ty);
                defer emitter.allocator.free(fld_mem);
                if (emitted_count > 0) try emitter.writeAll(", ");
                try emitter.writeAll(fld_mem);
                emitted_count += 1;
            }
            while (pad_cursor < pad_spans.len) {
                const pad = pad_spans[pad_cursor];
                pad_cursor += 1;
                if (emitted_count > 0) try emitter.writeAll(", ");
                try emitter.print("[{d} x i8]", .{pad.byte_len});
                emitted_count += 1;
            }
            if (emitted_count == 0) {
                try emitter.print("[{d} x i8]", .{lay.size_bytes});
            }
            try emitter.writeAll(" }>\n");
        } else {
            try emitter.print("%_cx_ty_{d} = type <{{ [{d} x i8] }}>\n", .{ ty.toU32(), lay.size_bytes });
        }
    }
    try emitter.writeAll("\n");
}

// ------------ Module Indexing, ABI & Global Rodata ------------

/// Sanitizes a raw identifier so it contains only `[A-Za-z0-9_]` characters for internal symbol suffixes.
fn sanitizeLlvmIdentAlloc(allocator: std.mem.Allocator, raw_name: []const u8) ![]u8 {
    if (raw_name.len == 0) return allocator.dupe(u8, "anon");
    var buf = try allocator.alloc(u8, raw_name.len);
    for (raw_name, 0..) |ch, idx| {
        buf[idx] = if (std.ascii.isAlphanumeric(ch) or ch == '_') ch else '_';
    }
    return buf;
}

/// Escapes `raw_text` for an LLVM string/metadata literal `"…"` (caller owns returned slice).
fn escapeMetadataStringAlloc(allocator: std.mem.Allocator, raw_text: []const u8) ![]u8 {
    var buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer buf.deinit(allocator);
    for (raw_text) |ch_b| {
        if (ch_b >= 0x20 and ch_b <= 0x7E and ch_b != '"' and ch_b != '\\') {
            try buf.append(allocator, ch_b);
        } else {
            const hex_esc = try std.fmt.allocPrint(allocator, "\\{X:0>2}", .{ch_b});
            defer allocator.free(hex_esc);
            try buf.appendSlice(allocator, hex_esc);
        }
    }
    return buf.toOwnedSlice(allocator);
}

/// Formats `raw_name` as a valid LLVM global identifier (`@foo` when bare-safe, else `@"…"`).
fn formatLlvmGlobalIdent(allocator: std.mem.Allocator, raw_name: []const u8) ![]u8 {
    var is_bare_ok = raw_name.len > 0 and !std.ascii.isDigit(raw_name[0]);
    if (is_bare_ok) {
        for (raw_name) |ch_b| {
            if (!std.ascii.isAlphanumeric(ch_b) and ch_b != '_' and ch_b != '.' and ch_b != '$') {
                is_bare_ok = false;
                break;
            }
        }
    }
    if (is_bare_ok) {
        return std.fmt.allocPrint(allocator, "@{s}", .{raw_name});
    }
    const escaped = try escapeMetadataStringAlloc(allocator, raw_name);
    defer allocator.free(escaped);
    return std.fmt.allocPrint(allocator, "@\"{s}\"", .{escaped});
}

/// Resolves `(def_id, sym_idx)` to a 0-based index in `emitter.input.bodies` (`null` if external).
fn resolveBodyIndex(
    emitter: *const LlvmModuleEmitter,
    def_id: DefId,
    sym_idx: SymbolIndex,
) ?u32 {
    if (!sym_idx.isNone()) {
        if (emitter.sym_to_body.get(sym_idx.asInt())) |found_sym| return found_sym;
        if (sym_idx.asInt() < emitter.input.sym_table.symbols.items.len) {
            const sym_rec = emitter.input.sym_table.getSymbol(sym_idx).*;
            if (!sym_rec.def_id.isNone()) {
                if (emitter.def_to_body.get(sym_rec.def_id.asInt())) |found_def| return found_def;
            }
        }
    }
    if (!def_id.isNone()) {
        if (emitter.def_to_body.get(def_id.asInt())) |found_by_def| return found_by_def;
    }
    return null;
}

/// Returns `true` if `body` carries `@export` or `@link_name` external C-ABI visibility.
fn isBodyExternallyVisible(emitter: *const LlvmModuleEmitter, body: *const MirBody) bool {
    if (body.symbol_index.isNone() or
        body.symbol_index.asInt() >= emitter.input.sym_table.symbols.items.len) return false;
    const sym_rec = emitter.input.sym_table.getSymbol(body.symbol_index).*;
    return sym_rec.contract_flags.is_export or sym_rec.contract_flags.has_link_name;
}

/// Classifies `body`'s machine calling convention via `AbiClassifier.classifyFn`.
fn classifyBodyAbi(emitter: *LlvmModuleEmitter, body: *const MirBody) !AbiFnRecipe {
    var param_specs = try emitter.allocator.alloc(FnParamSpec, body.param_count);
    defer if (param_specs.len > 0) emitter.allocator.free(param_specs);

    var param_i: u32 = 0;
    while (param_i < body.param_count) : (param_i += 1) {
        const loc_decl = body.locals.items[1 + param_i];
        param_specs[param_i] = .{
            .type_id = loc_decl.type_id,
            .mode = loc_decl.mode(),
            .is_non_escaping = true,
        };
    }
    return AbiClassifier.classifyFn(emitter.allocator, &emitter.resolver, .{
        .params = param_specs,
        .ret_ty = body.ret_ty,
        .is_extern_c = isBodyExternallyVisible(emitter, body),
        .is_contextless = body.is_contextless,
    });
}

/// Classifies an `InternPool` `fn_ty` or `closure_ty` signature via `AbiClassifier.classifyFn`.
fn classifyFnTypeAbi(
    emitter: *LlvmModuleEmitter,
    fn_ty: TypeId,
    is_extern_c: bool,
    force_contextless: ?bool,
) !AbiFnRecipe {
    const unwrapped = emitter.input.pool.unwrapUnderlyingType(fn_ty);
    const sig_view = emitter.input.pool.getFnSignatureView(unwrapped) orelse {
        return AbiClassifier.classifyFn(emitter.allocator, &emitter.resolver, .{
            .params = &.{},
            .ret_ty = .unit_ty,
            .is_extern_c = is_extern_c,
            .is_contextless = true,
        });
    };
    const arity = sig_view.paramCount();
    var param_specs = try emitter.allocator.alloc(FnParamSpec, arity);
    defer if (arity > 0) emitter.allocator.free(param_specs);

    for (0..arity) |idx| {
        param_specs[idx] = .{
            .type_id = sig_view.getParamType(idx),
            .mode = sig_view.getParamMode(idx),
            .is_non_escaping = true,
        };
    }
    const is_ctxless = force_contextless orelse
        (is_extern_c or sig_view.contracts.has_no_alloc);
    return AbiClassifier.classifyFn(emitter.allocator, &emitter.resolver, .{
        .params = param_specs,
        .ret_ty = sig_view.ret_ty,
        .is_extern_c = is_extern_c,
        .is_contextless = is_ctxless,
    });
}

/// Registers `raw_ty` and its constituent fields/elements/variants for `@_cx_drop_ty_<id>` generation.
fn registerDropTypeRecursive(emitter: *LlvmModuleEmitter, raw_ty: TypeId, depth: u32) !void {
    if (depth >= 64) return;
    const ty = try unwrapTransparentType(emitter, raw_ty);
    if (try isZeroSizedType(emitter, ty)) return;
    if (ty.isPrimitiveOrSentinel()) return;

    if ((try emitter.drop_type_set.getOrPut(emitter.allocator, ty.toU32())).found_existing) return;

    try collectCompositeType(emitter, ty, 0);
    const node = emitter.input.pool.getNode(ty);
    switch (node.tag) {
        .struct_ty, .tuple_ty => {
            const lay = try emitter.resolver.resolveType(ty);
            var fld_i: u32 = 0;
            while (fld_i < lay.aux_len) : (fld_i += 1) {
                const fld = emitter.resolver.fields_by_decl.items[lay.aux_start + fld_i];
                try registerDropTypeRecursive(emitter, fld.field_ty, depth + 1);
            }
        },
        .array_ty => {
            try registerDropTypeRecursive(emitter, TypeId.fromInt(node.lhs), depth + 1);
        },
        .soa_array_ty => {
            const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const lay = try emitter.resolver.resolveType(elem_struct);
            var fld_i: u32 = 0;
            while (fld_i < lay.aux_len) : (fld_i += 1) {
                const fld = emitter.resolver.fields_by_decl.items[lay.aux_start + fld_i];
                try registerDropTypeRecursive(emitter, fld.field_ty, depth + 1);
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
        else => {},
    }
    try emitter.drop_type_list.append(emitter.allocator, ty);
}

/// Records an `extern` function symbol if referenced without a local `MirBody`.
fn maybeRegisterExternSymbol(
    emitter: *LlvmModuleEmitter,
    seen_set: *std.AutoHashMapUnmanaged(u32, void),
    def_id: DefId,
    sym_idx: SymbolIndex,
) !void {
    if (resolveBodyIndex(emitter, def_id, sym_idx) != null) return;
    if (sym_idx.isNone() or sym_idx.asInt() >= emitter.input.sym_table.symbols.items.len) return;
    const sym_rec = emitter.input.sym_table.getSymbol(sym_idx).*;
    if (sym_rec.kind != .fn_sym) return;
    if (!(try seen_set.getOrPut(emitter.allocator, sym_idx.asInt())).found_existing) {
        try emitter.extern_syms.append(emitter.allocator, sym_idx);
        if (emitter.input.pool.getFnSignatureView(sym_rec.type_id)) |sig| {
            try collectCompositeType(emitter, sig.ret_ty, 0);
            for (0..sig.paramCount()) |idx| {
                try collectCompositeType(emitter, sig.getParamType(idx), 0);
            }
        }
    }
}

/// Returns `true` when `target_b` is contextless (`!has_implicit_context`) while `fn_ty` is a stateful `fn(…)`.
fn isFnAddrCtxWrapperNeeded(emitter: *const LlvmModuleEmitter, target_b: u32, fn_ty: TypeId) bool {
    if (target_b >= emitter.body_recipes.items.len) return false;
    if (emitter.body_recipes.items[target_b].has_implicit_context) return false;
    const unwrapped = emitter.input.pool.unwrapUnderlyingType(fn_ty);
    if (emitter.input.pool.getNode(unwrapped).tag != .fn_ty) return false;
    const sig_view = emitter.input.pool.getFnSignatureView(unwrapped) orelse return false;
    return !sig_view.contracts.has_no_alloc;
}

/// Returns `true` when `MirOp.fn_addr` value `fn_val_raw` in `body_ptr` is reified beyond a direct `callee_val`.
fn isFnAddrUsedAsValue(body_ptr: *const MirBody, fn_val_raw: u32) bool {
    for (0..body_ptr.insts.len) |other_raw| {
        const other_inst = body_ptr.insts.get(other_raw);
        switch (other_inst.op) {
            .copy_val, .unary_op, .aggregate_extract, .bitfield_extract => {
                if (other_inst.operands.lhs == fn_val_raw) return true;
            },
            .bin_op => {
                if (other_inst.operands.lhs == fn_val_raw or other_inst.operands.rhs == fn_val_raw) return true;
            },
            .place_store => {
                if (other_inst.operands.rhs == fn_val_raw) return true;
            },
            .aggregate_insert => {
                if (other_inst.operands.lhs == fn_val_raw) return true;
                if (other_inst.operands.rhs + 1 < body_ptr.extra_args.items.len and
                    body_ptr.extra_args.items[other_inst.operands.rhs + 1] == fn_val_raw)
                {
                    return true;
                }
            },
            .bitfield_insert => {
                if (other_inst.operands.lhs + 1 < body_ptr.extra_args.items.len and
                    (body_ptr.extra_args.items[other_inst.operands.lhs] == fn_val_raw or
                        body_ptr.extra_args.items[other_inst.operands.lhs + 1] == fn_val_raw))
                {
                    return true;
                }
            },
            .aggregate_make => {
                const agg_kind: mir.AggregateKind = @fromBackingInt(
                    @intCast(@as(u8, @truncate(other_inst.aux_u16))),
                );
                switch (agg_kind) {
                    .closure_make => {
                        const cap_len: usize = if (other_inst.operands.rhs < body_ptr.extra_args.items.len)
                            body_ptr.extra_args.items[other_inst.operands.rhs]
                        else
                            0;
                        for (0..cap_len) |cap_i| {
                            if (other_inst.operands.rhs + 1 + cap_i < body_ptr.extra_args.items.len and
                                body_ptr.extra_args.items[other_inst.operands.rhs + 1 + cap_i] == fn_val_raw)
                            {
                                return true;
                            }
                        }
                    },
                    .array_repeat => {
                        if (other_inst.operands.lhs == fn_val_raw) return true;
                    },
                    .tagged_variant => {
                        for (0..(other_inst.operands.rhs & 0xFFFF)) |arg_i| {
                            if (other_inst.operands.lhs + arg_i < body_ptr.extra_args.items.len and
                                body_ptr.extra_args.items[other_inst.operands.lhs + arg_i] == fn_val_raw)
                            {
                                return true;
                            }
                        }
                    },
                    .tuple_agg, .struct_agg, .array_elems, .str_concat => {
                        for (0..other_inst.operands.rhs) |elem_i| {
                            if (other_inst.operands.lhs + elem_i < body_ptr.extra_args.items.len and
                                body_ptr.extra_args.items[other_inst.operands.lhs + elem_i] == fn_val_raw)
                            {
                                return true;
                            }
                        }
                    },
                }
            },
            .intrinsic_op => {
                if (@as(mir.MirIntrinsicKind, @fromBackingInt(other_inst.aux_u16)).hasExtraArgs()) {
                    for (0..other_inst.operands.rhs) |arg_i| {
                        if (other_inst.operands.lhs + arg_i < body_ptr.extra_args.items.len and
                            body_ptr.extra_args.items[other_inst.operands.lhs + arg_i] == fn_val_raw)
                        {
                            return true;
                        }
                    }
                }
            },
            else => {},
        }
    }
    for (body_ptr.calls.items) |call_site| {
        if (call_site.direct_def_id.isNone() and call_site.direct_symbol.isNone() and
            call_site.callee_val.asInt() == fn_val_raw)
        {
            return true;
        }
        for (0..call_site.args_len) |arg_i| {
            const mode: type_system.ParamMode = if (call_site.modes_start + arg_i < body_ptr.call_arg_modes.items.len)
                body_ptr.call_arg_modes.items[call_site.modes_start + arg_i]
            else
                .let_mode;
            if (mode != .inout_mode and mode != .set_mode and
                call_site.args_start + arg_i < body_ptr.extra_args.items.len and
                body_ptr.extra_args.items[call_site.args_start + arg_i] == fn_val_raw)
            {
                return true;
            }
        }
    }
    for (body_ptr.blocks.items) |blk_rec| {
        switch (blk_rec.terminator.kind) {
            .ret, .cond_br, .switch_int => {
                if (blk_rec.terminator.cond_or_val == fn_val_raw) return true;
            },
            else => {},
        }
    }
    for (body_ptr.extra_edges.items) |edge_rec| {
        for (0..edge_rec.args_len) |edge_arg_i| {
            if (edge_rec.args_start + edge_arg_i < body_ptr.extra_args.items.len and
                body_ptr.extra_args.items[edge_rec.args_start + edge_arg_i] == fn_val_raw)
            {
                return true;
            }
        }
    }
    for (body_ptr.projections.items) |proj_rec| {
        if (proj_rec.kind == .index and proj_rec.payload == fn_val_raw) return true;
    }
    return false;
}

/// Indexes all `MirBody` functions, composite types, string/blob constants, externs, closures, and drops.
fn indexModuleEntities(emitter: *LlvmModuleEmitter) !void {
    for (emitter.input.bodies, 0..) |*body_ptr, body_i| {
        const b_idx: u32 = @intCast(body_i);
        if (!body_ptr.def_id.isNone()) {
            try emitter.def_to_body.put(emitter.allocator, body_ptr.def_id.asInt(), b_idx);
        }
        if (!body_ptr.symbol_index.isNone()) {
            try emitter.sym_to_body.put(emitter.allocator, body_ptr.symbol_index.asInt(), b_idx);
        }

        const raw_name = emitter.input.interner.get(body_ptr.name);
        var is_export_sym = false;
        var link_name_override: ?[]const u8 = null;
        if (!body_ptr.symbol_index.isNone() and
            body_ptr.symbol_index.asInt() < emitter.input.sym_table.symbols.items.len)
        {
            const sym_rec = emitter.input.sym_table.getSymbol(body_ptr.symbol_index).*;
            is_export_sym = sym_rec.contract_flags.is_export;
            if (sym_rec.contract_flags.has_link_name and sym_rec.link_name_text.len > 0) {
                link_name_override = sym_rec.link_name_text;
            }
        }
        if (std.mem.eql(u8, raw_name, "main")) {
            emitter.entry_main_body_idx = b_idx;
        }

        const llvm_name = if (link_name_override) |lnk_str|
            (if (std.mem.eql(u8, lnk_str, "main"))
                try emitter.allocator.dupe(u8, "_cx_user_main")
            else
                try emitter.allocator.dupe(u8, lnk_str))
        else if (is_export_sym and !std.mem.eql(u8, raw_name, "main"))
            try emitter.allocator.dupe(u8, raw_name)
        else blk: {
            const clean_suffix = try sanitizeLlvmIdentAlloc(emitter.allocator, raw_name);
            defer emitter.allocator.free(clean_suffix);
            break :blk try std.fmt.allocPrint(emitter.allocator, "_cx_fn_{d}_{s}", .{ b_idx, clean_suffix });
        };
        try emitter.body_llvm_names.append(emitter.allocator, llvm_name);
        try emitter.body_recipes.append(emitter.allocator, try classifyBodyAbi(emitter, body_ptr));
    }

    var str_set: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer str_set.deinit(emitter.allocator);
    var blob_set: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer blob_set.deinit(emitter.allocator);
    var extern_set: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer extern_set.deinit(emitter.allocator);
    var candidate_types: std.ArrayListUnmanaged(TypeId) = .empty;
    defer candidate_types.deinit(emitter.allocator);
    var cand_set: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer cand_set.deinit(emitter.allocator);

    for (emitter.input.bodies, 0..) |*body_ptr, body_i| {
        const b_idx: u32 = @intCast(body_i);
        if (!(try cand_set.getOrPut(emitter.allocator, body_ptr.ret_ty.toU32())).found_existing) {
            try candidate_types.append(emitter.allocator, body_ptr.ret_ty);
        }
        for (body_ptr.locals.items) |loc_decl| {
            if (!(try cand_set.getOrPut(emitter.allocator, loc_decl.type_id.toU32())).found_existing) {
                try candidate_types.append(emitter.allocator, loc_decl.type_id);
            }
        }
        for (body_ptr.consts.items) |mir_const| {
            switch (mir_const) {
                .str_val, .bytes_val => |sym_id| {
                    if (!(try str_set.getOrPut(emitter.allocator, sym_id.asInt())).found_existing) {
                        try emitter.str_sym_ids.append(emitter.allocator, sym_id.asInt());
                    }
                },
                .raw_blob => |rb_const| {
                    if (!(try blob_set.getOrPut(emitter.allocator, rb_const.blob_id)).found_existing) {
                        try emitter.blob_ids.append(emitter.allocator, rb_const.blob_id);
                    }
                },
                else => {},
            }
        }
        for (0..body_ptr.insts.len) |inst_raw| {
            const inst = body_ptr.insts.get(inst_raw);
            if (!(try cand_set.getOrPut(emitter.allocator, inst.type_id.toU32())).found_existing) {
                try candidate_types.append(emitter.allocator, inst.type_id);
            }
            if (inst.op == .fn_addr) {
                const fn_def_id = DefId.fromInt(inst.operands.lhs);
                const fn_sym_idx = SymbolIndex.fromInt(inst.operands.rhs);
                try maybeRegisterExternSymbol(
                    emitter,
                    &extern_set,
                    fn_def_id,
                    fn_sym_idx,
                );
                if (resolveBodyIndex(emitter, fn_def_id, fn_sym_idx)) |target_b| {
                    if (isFnAddrCtxWrapperNeeded(emitter, target_b, inst.type_id) and
                        isFnAddrUsedAsValue(body_ptr, @intCast(inst_raw)))
                    {
                        const gop = try emitter.ctx_wrap_map.getOrPut(emitter.allocator, target_b);
                        if (!gop.found_existing) {
                            gop.value_ptr.* = emitter.input.pool.unwrapUnderlyingType(inst.type_id);
                            try emitter.ctx_wrap_bodies.append(emitter.allocator, target_b);
                        }
                    }
                }
            } else if (inst.op == .aggregate_make) {
                const agg_kind: mir.AggregateKind = @fromBackingInt(
                    @intCast(@as(u8, @truncate(inst.aux_u16))),
                );
                if (agg_kind == .closure_make) {
                    if (resolveBodyIndex(emitter, DefId.fromInt(inst.operands.lhs), .none)) |callee_b| {
                        const key: u64 = (@as(u64, b_idx) << 32) | @as(u64, @intCast(inst_raw));
                        if (!emitter.closure_thunk_map.contains(key)) {
                            const cap_len: usize = if (inst.operands.rhs < body_ptr.extra_args.items.len)
                                body_ptr.extra_args.items[inst.operands.rhs]
                            else
                                0;
                            const cap_tys = try emitter.allocator.alloc(TypeId, cap_len);
                            for (0..cap_len) |cap_i| {
                                const cap_val = MirValueId.fromInt(
                                    body_ptr.extra_args.items[inst.operands.rhs + 1 + cap_i],
                                );
                                cap_tys[cap_i] = body_ptr.getInst(cap_val).type_id;
                                if (!(try cand_set.getOrPut(emitter.allocator, cap_tys[cap_i].toU32())).found_existing) {
                                    try candidate_types.append(emitter.allocator, cap_tys[cap_i]);
                                }
                            }
                            const thunk_idx: u32 = @intCast(emitter.closure_thunks.items.len);
                            try emitter.closure_thunks.append(emitter.allocator, .{
                                .owner_body_idx = b_idx,
                                .inst_val_raw = @intCast(inst_raw),
                                .callee_body_idx = callee_b,
                                .closure_ty = emitter.input.pool.unwrapUnderlyingType(inst.type_id),
                                .capture_types = cap_tys,
                            });
                            try emitter.closure_thunk_map.put(emitter.allocator, key, thunk_idx);
                        }
                    }
                }
            } else if (inst.op == .intrinsic_op) {
                const ikind: mir.MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                if (ikind == .drop_in_place or ikind == .drop_if_live) {
                    const place_ty = resolvePlaceResultType(emitter, body_ptr, PlaceId.fromInt(inst.operands.lhs));
                    const dropped_ty = if (inst.type_id != .unit_ty and !inst.type_id.isError())
                        inst.type_id
                    else
                        place_ty;
                    try registerDropTypeRecursive(emitter, dropped_ty, 0);
                } else if (ikind == .type_name) {
                    const refl_raw = inst.operands.lhs;
                    var has_tn = false;
                    for (emitter.type_name_ids.items) |existing_tn| {
                        if (existing_tn == refl_raw) {
                            has_tn = true;
                            break;
                        }
                    }
                    if (!has_tn) {
                        try emitter.type_name_ids.append(emitter.allocator, refl_raw);
                    }
                }
            }
        }
        for (body_ptr.calls.items) |call_site| {
            if (!(try cand_set.getOrPut(emitter.allocator, call_site.ret_ty.toU32())).found_existing) {
                try candidate_types.append(emitter.allocator, call_site.ret_ty);
            }
            if (!call_site.direct_def_id.isNone() or !call_site.direct_symbol.isNone()) {
                try maybeRegisterExternSymbol(
                    emitter,
                    &extern_set,
                    call_site.direct_def_id,
                    call_site.direct_symbol,
                );
            }
        }
    }

    // Sort candidate types ascending by `TypeId.toU32()` before topological DFS (`DR-01`).
    std.mem.sort(TypeId, candidate_types.items, {}, struct {
        /// Orders candidate `TypeId` handles ascending by raw integer ID.
        fn lessThan(_: void, lhs_id: TypeId, rhs_id: TypeId) bool {
            return lhs_id.toU32() < rhs_id.toU32();
        }
    }.lessThan);
    for (candidate_types.items) |cand_ty| {
        try collectCompositeType(emitter, cand_ty, 0);
    }

    std.mem.sort(u32, emitter.str_sym_ids.items, {}, std.sort.asc(u32));
    std.mem.sort(u32, emitter.type_name_ids.items, {}, std.sort.asc(u32));
    std.mem.sort(u32, emitter.blob_ids.items, {}, std.sort.asc(u32));
    std.mem.sort(SymbolIndex, emitter.extern_syms.items, {}, struct {
        /// Orders external `SymbolIndex` handles ascending by raw integer index.
        fn lessThan(_: void, lhs_s: SymbolIndex, rhs_s: SymbolIndex) bool {
            return lhs_s.asInt() < rhs_s.asInt();
        }
    }.lessThan);
}

// --------------- ABI Signature & Coercion Layer ---------------

/// Resolves the LLVM calling-convention prefix (`"swiftcc "` or `""`) for `recipe`.
fn resolveCallingConvPrefix(recipe: *const AbiFnRecipe) []const u8 {
    return switch (recipe.calling_conv) {
        .cx_native, .cx_result_cc => "swiftcc ",
        .c_system, .wasm_mvp => "",
    };
}

/// Formats the lowered LLVM register/pointer type for `param_rec` and CoreX `raw_ty`.
fn formatAbiParamOrRetType(
    emitter: *LlvmModuleEmitter,
    raw_ty: TypeId,
    param_rec: AbiParamRecipe,
) ![]u8 {
    const ty = try unwrapTransparentType(emitter, raw_ty);
    return switch (param_rec.pass_mode) {
        .ignore_zst => emitter.allocator.dupe(u8, "void"),
        .indirect_by_ref, .indirect_byval, .sret_ptr, .swifterror_ptr => emitter.allocator.dupe(u8, "ptr"),
        .direct_scalar => {
            if (ty == .bool_ty) return emitter.allocator.dupe(u8, "i1");
            if (ty == .f32_ty) return emitter.allocator.dupe(u8, "float");
            if (ty == .f64_ty or ty == .untyped_float_ty) return emitter.allocator.dupe(u8, "double");
            if (resolveIntegerInfo(emitter, ty)) |int_info| {
                if (int_info.bits <= 64) {
                    return std.fmt.allocPrint(emitter.allocator, "i{d}", .{int_info.bits});
                }
            }
            if (!ty.isPrimitiveOrSentinel()) {
                const tag = emitter.input.pool.getNode(ty).tag;
                if (tag == .ref_ty or tag == .mut_ref_ty or tag == .raw_ptr_ty or tag == .fn_ty) {
                    return emitter.allocator.dupe(u8, "ptr");
                }
                if (emitter.cfg.target.isWasm() and
                    (tag == .slice_ty or tag == .soa_slice_ty or tag == .closure_ty))
                {
                    return emitter.allocator.dupe(u8, "i64");
                }
            }
            if (ty == .str_ty and emitter.cfg.target.isWasm()) {
                return emitter.allocator.dupe(u8, "i64");
            }
            if (param_rec.bank_0 == .xmm_vec) {
                return emitter.allocator.dupe(
                    u8,
                    if (param_rec.lowered_size_bytes <= 4) "float" else "double",
                );
            }
            const sz = param_rec.lowered_size_bytes;
            if (sz <= 1) return emitter.allocator.dupe(u8, "i8");
            if (sz == 2) return emitter.allocator.dupe(u8, "i16");
            if (sz <= 4) return emitter.allocator.dupe(u8, "i32");
            return emitter.allocator.dupe(u8, "i64");
        },
        .direct_pair => {
            if (ty == .i128_ty or ty == .u128_ty) {
                return emitter.allocator.dupe(u8, "i128");
            }
            if (!emitter.cfg.target.isWasm()) {
                if (ty == .str_ty) return emitter.allocator.dupe(u8, "{ ptr, i64 }");
                if (!ty.isPrimitiveOrSentinel()) {
                    const tag = emitter.input.pool.getNode(ty).tag;
                    if (tag == .slice_ty or tag == .soa_slice_ty) {
                        return emitter.allocator.dupe(u8, "{ ptr, i64 }");
                    }
                    if (tag == .closure_ty) {
                        return emitter.allocator.dupe(u8, "{ ptr, ptr }");
                    }
                }
            }
            const p0 = if (param_rec.bank_0 == .xmm_vec) "double" else "i64";
            const p1 = if (param_rec.bank_1 == .xmm_vec)
                (if (param_rec.lowered_size_bytes == 12) "float" else "double")
            else
                "i64";
            return std.fmt.allocPrint(emitter.allocator, "{{ {s}, {s} }}", .{ p0, p1 });
        },
        .direct_quad => {
            if (param_rec.piece_count <= 3) {
                return emitter.allocator.dupe(u8, "{ i64, i64, i64 }");
            }
            return emitter.allocator.dupe(u8, "{ i64, i64, i64, i64 }");
        },
        .direct_hfa => {
            const lane_count: u32 = @max(param_rec.piece_count, 1);
            const lane_str = if (param_rec.lowered_size_bytes == lane_count * 4) "float" else "double";
            return std.fmt.allocPrint(emitter.allocator, "[{d} x {s}]", .{ lane_count, lane_str });
        },
    };
}

/// Computes the byte size of an ABI register piece/aggregate type string in O(1).
fn computeAbiTypeByteSize(emitter: *const LlvmModuleEmitter, abi_ty: []const u8) u64 {
    if (std.mem.eql(u8, abi_ty, "ptr")) return emitter.cfg.target.ptrBytes();
    if (ABI_TYPE_BYTE_SIZE_MAP.get(abi_ty)) |fixed_sz| return fixed_sz;
    if (abi_ty.len > 4 and abi_ty[0] == '[') {
        if (std.mem.indexOfScalar(u8, abi_ty, ' ')) |sp_idx| {
            const count = std.fmt.parseInt(u64, abi_ty[1..sp_idx], 10) catch 1;
            const is_f32 = std.mem.indexOf(u8, abi_ty, "float") != null;
            return count * (if (is_f32) @as(u64, 4) else @as(u64, 8));
        }
    }
    return 16;
}

/// Formats LLVM parameter attributes for `param_rec` (`ptr noalias nonnull …` or `i32 zeroext …`).
fn formatAbiParamDeclPiece(
    emitter: *LlvmModuleEmitter,
    raw_ty: TypeId,
    param_rec: AbiParamRecipe,
    maybe_name: ?[]const u8,
) ![]u8 {
    var buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer buf.deinit(emitter.allocator);
    const attrs = param_rec.attrs();

    switch (param_rec.pass_mode) {
        .ignore_zst => return buf.toOwnedSlice(emitter.allocator),
        .swifterror_ptr => {
            // Emit bare `ptr swifterror` with zero extra pointer attributes (`[CRITICAL-06]`).
            try buf.appendSlice(emitter.allocator, "ptr swifterror");
        },
        .sret_ptr => {
            const mem_ty = try formatLlvmMemoryType(emitter, raw_ty);
            defer emitter.allocator.free(mem_ty);
            const part = try std.fmt.allocPrint(
                emitter.allocator,
                "ptr noalias nonnull writeonly nocapture align {d} sret({s})",
                .{ @max(param_rec.pointee_align_bytes, 1), mem_ty },
            );
            defer emitter.allocator.free(part);
            try buf.appendSlice(emitter.allocator, part);
        },
        .indirect_byval => {
            const mem_ty = try formatLlvmMemoryType(emitter, raw_ty);
            defer emitter.allocator.free(mem_ty);
            const part = try std.fmt.allocPrint(
                emitter.allocator,
                "ptr byval({s}) align {d}",
                .{ mem_ty, @max(param_rec.pointee_align_bytes, 1) },
            );
            defer emitter.allocator.free(part);
            try buf.appendSlice(emitter.allocator, part);
        },
        .indirect_by_ref => {
            try buf.appendSlice(emitter.allocator, "ptr");
            if (attrs.is_noalias) try buf.appendSlice(emitter.allocator, " noalias");
            if (attrs.is_nonnull) try buf.appendSlice(emitter.allocator, " nonnull");
            if (attrs.is_noundef) try buf.appendSlice(emitter.allocator, " noundef");
            if (attrs.is_readonly) try buf.appendSlice(emitter.allocator, " readonly");
            if (attrs.is_writeonly) try buf.appendSlice(emitter.allocator, " writeonly");
            if (attrs.is_nocapture) try buf.appendSlice(emitter.allocator, " nocapture");
            const align_part = try std.fmt.allocPrint(
                emitter.allocator,
                " align {d}",
                .{@max(param_rec.pointee_align_bytes, 1)},
            );
            defer emitter.allocator.free(align_part);
            try buf.appendSlice(emitter.allocator, align_part);
            if (param_rec.lowered_size_bytes > 0 and !attrs.is_writeonly) {
                const deref_part = try std.fmt.allocPrint(
                    emitter.allocator,
                    " dereferenceable({d})",
                    .{param_rec.lowered_size_bytes},
                );
                defer emitter.allocator.free(deref_part);
                try buf.appendSlice(emitter.allocator, deref_part);
            }
        },
        .direct_scalar, .direct_pair, .direct_quad, .direct_hfa => {
            const abi_ty = try formatAbiParamOrRetType(emitter, raw_ty, param_rec);
            defer emitter.allocator.free(abi_ty);
            try buf.appendSlice(emitter.allocator, abi_ty);
            const is_ptr_ty = std.mem.eql(u8, abi_ty, "ptr");
            const is_int_ty = abi_ty.len >= 2 and abi_ty[0] == 'i' and std.ascii.isDigit(abi_ty[1]);
            if (is_int_ty and attrs.is_zext) try buf.appendSlice(emitter.allocator, " zeroext");
            if (is_int_ty and attrs.is_sext) try buf.appendSlice(emitter.allocator, " signext");
            if (is_ptr_ty and attrs.is_nonnull) try buf.appendSlice(emitter.allocator, " nonnull");
            if ((is_ptr_ty or is_int_ty or std.mem.eql(u8, abi_ty, "float") or
                std.mem.eql(u8, abi_ty, "double")) and attrs.is_noundef)
            {
                try buf.appendSlice(emitter.allocator, " noundef");
            }
        },
    }

    if (maybe_name) |arg_name| {
        try buf.append(emitter.allocator, ' ');
        try buf.appendSlice(emitter.allocator, arg_name);
    }
    return buf.toOwnedSlice(emitter.allocator);
}

/// Formats the LLVM return attribute + type prefix (e.g., `"zeroext i8"` or `"void"`) for `recipe`.
fn formatAbiReturnDecl(
    emitter: *LlvmModuleEmitter,
    sig_ret_ty: TypeId,
    recipe: *const AbiFnRecipe,
) !struct { full_decl: []u8, bare_ty: []u8 } {
    if (recipe.has_sret or recipe.ret_recipe.pass_mode == .ignore_zst) {
        return .{
            .full_decl = try emitter.allocator.dupe(u8, "void"),
            .bare_ty = try emitter.allocator.dupe(u8, "void"),
        };
    }
    const eff_ty = if (recipe.calling_conv == .cx_result_cc) recipe.ok_ty else sig_ret_ty;
    const bare_ty = try formatAbiParamOrRetType(emitter, eff_ty, recipe.ret_recipe);
    errdefer emitter.allocator.free(bare_ty);

    const attrs = recipe.ret_recipe.attrs();
    var prefix: std.ArrayListUnmanaged(u8) = .empty;
    errdefer prefix.deinit(emitter.allocator);

    const is_ptr_ty = std.mem.eql(u8, bare_ty, "ptr");
    const is_int_ty = bare_ty.len >= 2 and bare_ty[0] == 'i' and std.ascii.isDigit(bare_ty[1]);
    if (is_int_ty and attrs.is_zext) try prefix.appendSlice(emitter.allocator, "zeroext ");
    if (is_int_ty and attrs.is_sext) try prefix.appendSlice(emitter.allocator, "signext ");
    if (is_ptr_ty and attrs.is_nonnull) try prefix.appendSlice(emitter.allocator, "nonnull ");
    if ((is_ptr_ty or is_int_ty or std.mem.eql(u8, bare_ty, "float") or
        std.mem.eql(u8, bare_ty, "double")) and attrs.is_noundef)
    {
        try prefix.appendSlice(emitter.allocator, "noundef ");
    }
    try prefix.appendSlice(emitter.allocator, bare_ty);
    return .{
        .full_decl = try prefix.toOwnedSlice(emitter.allocator),
        .bare_ty = bare_ty,
    };
}

/// Emits `@llvm.memset.p0.i64` zeroing `size_bytes` at `ptr_str`.
fn emitMemsetZero(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    ptr_str: []const u8,
    size_bytes: u64,
    align_bytes: u32,
) !void {
    if (size_bytes == 0) return;
    try emitter.requireIntrinsicDecl(
        "declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg)",
    );
    try state.print(
        "  call void @llvm.memset.p0.i64(ptr align {d} {s}, i8 0, i64 {d}, i1 false)\n",
        .{ @max(align_bytes, 1), ptr_str, size_bytes },
    );
}

/// Emits `@llvm.memcpy.p0.p0.i64` copying `size_bytes` from `src_ptr` to `dst_ptr`.
fn emitMemcpyBytes(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    dst_ptr: []const u8,
    dst_align: u32,
    src_ptr: []const u8,
    src_align: u32,
    size_bytes: u64,
) !void {
    if (size_bytes == 0) return;
    try emitter.requireIntrinsicDecl(
        "declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, " ++
            "ptr noalias nocapture readonly, i64, i1 immarg)",
    );
    try state.print(
        "  call void @llvm.memcpy.p0.p0.i64(ptr align {d} {s}, ptr align {d} {s}, i64 {d}, i1 false)\n",
        .{ @max(dst_align, 1), dst_ptr, @max(src_align, 1), src_ptr, size_bytes },
    );
}

/// Packs a CoreX SSA value `val_str` of `raw_ty` into `abi_ty` (zero-copy when types already match).
fn emitCoerceValueToAbi(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    raw_ty: TypeId,
    val_str: []const u8,
    abi_ty: []const u8,
) ![]u8 {
    const val_ty = try formatLlvmValueType(emitter, raw_ty);
    defer emitter.allocator.free(val_ty);
    if (std.mem.eql(u8, val_ty, abi_ty)) {
        return emitter.allocator.dupe(u8, val_str);
    }

    const lay = try emitter.resolver.resolveType(raw_ty);
    const scratch_sz = @max(lay.size_bytes, computeAbiTypeByteSize(emitter, abi_ty));
    const eff_align = @max(lay.alignBytes(), 8);
    const slot = try state.allocEntryBytes(scratch_sz, eff_align);
    defer emitter.allocator.free(slot);

    try emitMemsetZero(emitter, state, slot, scratch_sz, eff_align);
    try emitStoreValueToPtr(emitter, state, raw_ty, val_str, slot, eff_align, 0, 0, 0);

    const out_tmp = state.nextTmp();
    try state.print(
        "  %_abi_pk_{d} = load {s}, ptr {s}, align {d}\n",
        .{ out_tmp, abi_ty, slot, eff_align },
    );
    return std.fmt.allocPrint(emitter.allocator, "%_abi_pk_{d}", .{out_tmp});
}

/// Unpacks an ABI register value `abi_val_str` of `abi_ty` into a CoreX SSA value of `raw_ty`.
fn emitCoerceAbiToValue(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    raw_ty: TypeId,
    abi_ty: []const u8,
    abi_val_str: []const u8,
) ![]u8 {
    const val_ty = try formatLlvmValueType(emitter, raw_ty);
    defer emitter.allocator.free(val_ty);
    if (std.mem.eql(u8, val_ty, abi_ty)) {
        return emitter.allocator.dupe(u8, abi_val_str);
    }

    const lay = try emitter.resolver.resolveType(raw_ty);
    const scratch_sz = @max(lay.size_bytes, computeAbiTypeByteSize(emitter, abi_ty));
    const eff_align = @max(lay.alignBytes(), 8);
    const slot = try state.allocEntryBytes(scratch_sz, eff_align);
    defer emitter.allocator.free(slot);

    try emitMemsetZero(emitter, state, slot, scratch_sz, eff_align);
    try state.print(
        "  store {s} {s}, ptr {s}, align {d}\n",
        .{ abi_ty, abi_val_str, slot, eff_align },
    );
    return emitLoadValueFromPtr(emitter, state, raw_ty, slot, eff_align, null, 0, 0, 0);
}

// ---------- Global `.rodata`, `--dev` Seam & Runtime ----------

/// Appends an LLVM byte-array literal `c"…"` (escaping non-printable bytes as `\XX`) to `emitter.out`.
fn writeLlvmByteStringLiteral(emitter: *LlvmModuleEmitter, bytes: []const u8) !void {
    try emitter.writeAll("c\"");
    for (bytes) |byte_val| {
        if (byte_val >= 0x20 and byte_val <= 0x7E and byte_val != '"' and byte_val != '\\') {
            try emitter.out.append(emitter.allocator, byte_val);
        } else {
            try emitter.print("\\{X:0>2}", .{byte_val});
        }
    }
    try emitter.writeAll("\"");
}

/// Builds serialized `.cx_dev_meta` binary metadata (`DR-19` §1.2) for `--dev` GOT builds.
fn buildDevSeamBytes(emitter: *LlvmModuleEmitter) ![]u8 {
    var got_slots = try emitter.allocator.alloc(
        codegen_dev_seam.CxGotSlotMeta,
        emitter.input.bodies.len,
    );
    defer if (got_slots.len > 0) emitter.allocator.free(got_slots);

    var total_loop_contracts: u32 = 0;
    for (emitter.input.bodies, 0..) |*body_ptr, body_i| {
        total_loop_contracts +|= @intCast(body_ptr.loop_contracts.items.len);
        const body_rec = &emitter.body_recipes.items[body_i];
        got_slots[body_i] = .{
            .def_id = body_ptr.def_id,
            .got_idx = @intCast(body_i),
            .abi_sig_hash64 = body_rec.abiSigHash64(),
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
    defer if (type_records.len > 0) emitter.allocator.free(type_records);

    const header = codegen_dev_seam.CxDevSeamHeader{
        .arch_os_tag = emitter.cfg.target.archOsTag(),
        .got_slot_count = @intCast(got_slots.len),
        .type_record_count = @intCast(type_records.len),
        .loop_contract_count = total_loop_contracts,
    };
    return codegen_dev_seam.serializeDevSeamMeta(
        emitter.allocator,
        header,
        got_slots,
        type_records,
    );
}

/// Emits `.rodata` constants, `--dev` GOT / `ErrorReturnTrace` globals, and self-contained runtime helpers.
fn emitRodataAndRuntimeHelpers(
    emitter: *LlvmModuleEmitter,
    dev_seam_out: *?[]u8,
) !void {
    const ptr_int = ptrIntType(emitter);

    // [1] Default 32-byte `Context` storage passed to contextful functions from `main` / thunks:
    try emitter.writeAll("@_cx_default_ctx = internal global [32 x i8] zeroinitializer, align 8\n");

    // [2] Interned string and byte literals (`@_cx_str_bytes_<id>`) & `@type_name` tables:
    for (emitter.str_sym_ids.items) |sym_raw| {
        const bytes = emitter.input.interner.get(SymbolId.fromInt(sym_raw));
        if (bytes.len == 0) continue;
        try emitter.print(
            "@_cx_str_bytes_{d} = private unnamed_addr constant [{d} x i8] ",
            .{ sym_raw, bytes.len },
        );
        try writeLlvmByteStringLiteral(emitter, bytes);
        try emitter.writeAll(", align 1\n");
    }
    for (emitter.type_name_ids.items) |ty_u32| {
        var name_buf: [512]u8 = undefined;
        const rendered = emitter.input.pool.formatType(
            TypeId.fromInt(ty_u32),
            emitter.input.sym_table,
            &name_buf,
        );
        if (rendered.len == 0) continue;
        try emitter.print(
            "@_cx_tyname_{d} = private unnamed_addr constant [{d} x i8] ",
            .{ ty_u32, rendered.len },
        );
        try writeLlvmByteStringLiteral(emitter, rendered);
        try emitter.writeAll(", align 1\n");
    }

    // [3] `@embed_bytes` raw binary blobs (`MirBlobStore`, `DR-20` `D-03`, `[CRITICAL-07]`):
    if (emitter.input.blob_store) |bstore| {
        for (emitter.blob_ids.items) |blob_id| {
            const payload = bstore.getBytes(blob_id) orelse &[_]u8{};
            var align_log2: u8 = 0;
            for (emitter.input.bodies) |*body_ptr| {
                for (body_ptr.consts.items) |mc| {
                    if (mc == .raw_blob and mc.raw_blob.blob_id == blob_id) {
                        align_log2 = @max(align_log2, mc.raw_blob.align_log2);
                    }
                }
            }
            const align_bytes: u32 = @as(u32, 1) << @intCast(align_log2);
            if (payload.len > 0) {
                try emitter.print(
                    "@_cx_blob_{d} = private unnamed_addr constant [{d} x i8] ",
                    .{ blob_id, payload.len },
                );
                try writeLlvmByteStringLiteral(emitter, payload);
                try emitter.print(", align {d}\n", .{align_bytes});
                try emitter.print(
                    "@_cx_blob_slice_{d} = internal constant {{ ptr, {s} }} " ++
                        "{{ ptr @_cx_blob_{d}, {s} {d} }}, align {d}\n",
                    .{ blob_id, ptr_int, blob_id, ptr_int, payload.len, emitter.cfg.target.ptrBytes() },
                );
            } else {
                try emitter.print(
                    "@_cx_blob_slice_{d} = internal constant {{ ptr, {s} }} " ++
                        "{{ ptr inttoptr ({s} {d} to ptr), {s} 0 }}, align {d}\n",
                    .{ blob_id, ptr_int, ptr_int, align_bytes, ptr_int, emitter.cfg.target.ptrBytes() },
                );
            }
        }
    }

    // [4] Promoted `RodataPool` blobs:
    if (emitter.input.rodata_pool) |rpool| {
        for (rpool.blobs.items, 0..) |rblob, r_idx| {
            const align_bytes: u32 = @as(u32, 1) << @intCast(rblob.align_log2);
            const eff_bytes = if (rblob.bytes.len > 0) rblob.bytes else &[_]u8{0};
            try emitter.print(
                "@_cx_rodata_{d} = private unnamed_addr constant [{d} x i8] ",
                .{ r_idx, eff_bytes.len },
            );
            try writeLlvmByteStringLiteral(emitter, eff_bytes);
            try emitter.print(", align {d}\n", .{align_bytes});
        }
    }

    // [5] `--dev` 16-slot thread-local `ErrorReturnTrace` (`0` bytes in `--release`, `D-06B`):
    if (!emitter.cfg.is_release_mode) {
        const tls_kw = if (emitter.cfg.target.isWasm()) "internal global" else "internal thread_local global";
        try emitter.print(
            "@_cx_err_trace = {s} {{ [16 x {s}], i32, i32 }} zeroinitializer, align 8\n",
            .{ tls_kw, ptr_int },
        );
    }

    // [6] `--dev` hot-reload GOT table (`@_cx_dev_got`) and control block (`@_cx_reload_ctrl`, `DR-19`):
    if (emitter.input.is_dev_got_enabled) {
        const slot_count = @max(emitter.input.bodies.len, 1);
        try emitter.print("@_cx_dev_got = internal global [{d} x ptr] [", .{slot_count});
        if (emitter.input.bodies.len == 0) {
            try emitter.writeAll("ptr null");
        } else {
            for (emitter.body_llvm_names.items, 0..) |fn_name, idx| {
                if (idx > 0) try emitter.writeAll(", ");
                const fn_ident = try formatLlvmGlobalIdent(emitter.allocator, fn_name);
                defer emitter.allocator.free(fn_ident);
                try emitter.print("ptr {s}", .{fn_ident});
            }
        }
        try emitter.print("], align {d}\n", .{emitter.cfg.target.ptrBytes()});
        try emitter.writeAll(
            "@_cx_reload_ctrl = internal global { i64, i64, i64, i32, i32, i32, i32, i64, i32, i32, i64 } " ++
                "{ i64 0, i64 0, i64 0, i32 1, i32 0, i32 0, i32 0, i64 0, i32 -1, i32 0, i64 0 }, align 64\n",
        );
        dev_seam_out.* = try buildDevSeamBytes(emitter);
    }

    // [7] Runtime string constants & libc declarations for oracle tracing, panic, trap, and syscalls:
    try emitter.writeAll(
        \\@.cx_env_oracle = private unnamed_addr constant [24 x i8] c"COREX_ORACLE_TRACE_FILE\00", align 1
        \\@.cx_fmode_ab = private unnamed_addr constant [3 x i8] c"ab\00", align 1
        \\@.cx_msg_trap = private unnamed_addr constant [8 x i8] c"TRAP:1\0A\00", align 1
        \\@.cx_msg_ret0 = private unnamed_addr constant [7 x i8] c"RET:0\0A\00", align 1
        \\@.cx_msg_err1 = private unnamed_addr constant [7 x i8] c"ERR:1\0A\00", align 1
        \\@.cx_fmt_ret_s = private unnamed_addr constant [10 x i8] c"RET:%lld\0A\00", align 1
        \\@.cx_fmt_ret_u = private unnamed_addr constant [10 x i8] c"RET:%llu\0A\00", align 1
        \\@.cx_fmt_drop = private unnamed_addr constant [11 x i8] c"DROP:%lld\0A\00", align 1
        \\@.cx_fmt_exit = private unnamed_addr constant [9 x i8] c"EXIT:%d\0A\00", align 1
        \\@.cx_panic_pfx = private unnamed_addr constant [7 x i8] c"panic: ", align 1
        \\@.cx_panic_nl = private unnamed_addr constant [1 x i8] c"\0A", align 1
        \\@.cx_str_true = private unnamed_addr constant [4 x i8] c"true", align 1
        \\@.cx_str_false = private unnamed_addr constant [5 x i8] c"false", align 1
        \\@.cx_fmt_i64 = private unnamed_addr constant [5 x i8] c"%lld\00", align 1
        \\@.cx_fmt_u64 = private unnamed_addr constant [5 x i8] c"%llu\00", align 1
        \\
        \\declare void @llvm.trap() cold noreturn nounwind
        \\declare ptr @getenv(ptr) nounwind
        \\declare ptr @fopen(ptr, ptr) nounwind
        \\declare i32 @fflush(ptr) nounwind
        \\declare i32 @fclose(ptr) nounwind
        \\declare void @_exit(i32) noreturn nounwind
        \\
    );
    _ = try emitter.markExternDeclared("getenv");
    _ = try emitter.markExternDeclared("fopen");
    _ = try emitter.markExternDeclared("fflush");
    _ = try emitter.markExternDeclared("fclose");
    _ = try emitter.markExternDeclared("_exit");
    _ = try emitter.markExternDeclared("fwrite");
    _ = try emitter.markExternDeclared("snprintf");
    try emitter.print(
        "declare {s} @fwrite(ptr, {s}, {s}, ptr) nounwind\n" ++
            "declare i32 @snprintf(ptr, {s}, ptr, ...) nounwind\n",
        .{ ptr_int, ptr_int, ptr_int, ptr_int },
    );
    if (emitter.cfg.target.isWindows()) {
        _ = try emitter.markExternDeclared("_setmode");
        _ = try emitter.markExternDeclared("_write");
        try emitter.writeAll(
            "declare i32 @_setmode(i32, i32) nounwind\n" ++
                "declare i32 @_write(i32, ptr, i32) nounwind\n\n",
        );
    } else {
        _ = try emitter.markExternDeclared("write");
        try emitter.print("declare {s} @write(i32, ptr, {s}) nounwind\n\n", .{ ptr_int, ptr_int });
    }

    const fn_attrs = fnUnwindAttrs(emitter);

    // `@_cx_rt_init` sets `_O_BINARY` (`0x8000`) on Windows `stdout`/`stderr` so `\n` is never mangled.
    try emitter.print("define internal void @_cx_rt_init() {s} {{\nentry:\n", .{fn_attrs});
    if (emitter.cfg.target.isWindows()) {
        try emitter.writeAll(
            "  %_sm1 = call i32 @_setmode(i32 1, i32 32768)\n" ++
                "  %_sm2 = call i32 @_setmode(i32 2, i32 32768)\n",
        );
    }
    try emitter.writeAll("  ret void\n}\n\n");

    // `@_cx_rt_trace_append(ptr %line_ptr, <usize> %line_len)`:
    try emitter.print(
        "define internal void @_cx_rt_trace_append(ptr %line_ptr, {s} %line_len) {s} {{\n" ++
            "entry:\n" ++
            "  %path = call ptr @getenv(ptr @.cx_env_oracle)\n" ++
            "  %has_p = icmp ne ptr %path, null\n" ++
            "  br i1 %has_p, label %chk_nonempty, label %done\n" ++
            "chk_nonempty:\n" ++
            "  %ch0 = load i8, ptr %path, align 1\n" ++
            "  %ok0 = icmp ne i8 %ch0, 0\n" ++
            "  br i1 %ok0, label %open_f, label %done\n" ++
            "open_f:\n" ++
            "  %fp = call ptr @fopen(ptr %path, ptr @.cx_fmode_ab)\n" ++
            "  %ok_fp = icmp ne ptr %fp, null\n" ++
            "  br i1 %ok_fp, label %do_wr, label %done\n" ++
            "do_wr:\n" ++
            "  %_w = call {s} @fwrite(ptr %line_ptr, {s} 1, {s} %line_len, ptr %fp)\n" ++
            "  %_f = call i32 @fflush(ptr %fp)\n" ++
            "  %_c = call i32 @fclose(ptr %fp)\n" ++
            "  br label %done\n" ++
            "done:\n" ++
            "  ret void\n" ++
            "}}\n\n",
        .{ ptr_int, fn_attrs, ptr_int, ptr_int, ptr_int },
    );

    // `@_cx_rt_trap(i32 %reason)` writes `TRAP:1\n` + `_exit(101)` under oracle mode, else `@llvm.trap()`.
    try emitter.print(
        "define internal void @_cx_rt_trap(i32 %reason) cold noreturn {s} {{\n" ++
            "entry:\n" ++
            "  %path = call ptr @getenv(ptr @.cx_env_oracle)\n" ++
            "  %has_p = icmp ne ptr %path, null\n" ++
            "  br i1 %has_p, label %chk_ch, label %hard_trap\n" ++
            "chk_ch:\n" ++
            "  %ch0 = load i8, ptr %path, align 1\n" ++
            "  %ok0 = icmp ne i8 %ch0, 0\n" ++
            "  br i1 %ok0, label %oracle_exit, label %hard_trap\n" ++
            "oracle_exit:\n" ++
            "  call void @_cx_rt_trace_append(ptr @.cx_msg_trap, {s} 7)\n" ++
            "  %_fl_t = call i32 @fflush(ptr null)\n" ++
            "  call void @_exit(i32 101)\n" ++
            "  unreachable\n" ++
            "hard_trap:\n" ++
            "  call void @llvm.trap()\n" ++
            "  unreachable\n" ++
            "}}\n\n",
        .{ fn_attrs, ptr_int },
    );

    // `@_cx_rt_sys_write(i32 %fd, ptr %buf, <usize> %len) -> <isize>`:
    try emitter.print(
        "define internal {s} @_cx_rt_sys_write(i32 %fd, ptr %buf, {s} %len) {s} {{\nentry:\n",
        .{ ptr_int, ptr_int, fn_attrs },
    );
    if (emitter.cfg.target.isWindows()) {
        try emitter.writeAll(
            "  %is_z = icmp eq i64 %len, 0\n" ++
                "  br i1 %is_z, label %ret_z, label %do_w\n" ++
                "ret_z:\n" ++
                "  ret i64 0\n" ++
                "do_w:\n" ++
                "  %clamped = call i64 @llvm.umin.i64(i64 %len, i64 2147483647)\n" ++
                "  %len32 = trunc i64 %clamped to i32\n" ++
                "  %res32 = call i32 @_write(i32 %fd, ptr %buf, i32 %len32)\n" ++
                "  %res64 = sext i32 %res32 to i64\n" ++
                "  ret i64 %res64\n}\n\n",
        );
        try emitter.requireIntrinsicDecl("declare i64 @llvm.umin.i64(i64, i64)");
    } else {
        try emitter.print(
            "  %res = call {s} @write(i32 %fd, ptr %buf, {s} %len)\n  ret {s} %res\n}}\n\n",
            .{ ptr_int, ptr_int, ptr_int },
        );
    }

    // `@_cx_rt_panic(ptr %msg_ptr, <usize> %msg_len)` and `@_cx_rt_sys_exit(i32 %code)`:
    try emitter.print(
        "define internal void @_cx_rt_panic(ptr %msg_ptr, {s} %msg_len) cold noreturn {s} {{\n" ++
            "entry:\n" ++
            "  %_pfx = call {s} @_cx_rt_sys_write(i32 2, ptr @.cx_panic_pfx, {s} 7)\n" ++
            "  %has_m = icmp ne ptr %msg_ptr, null\n" ++
            "  %has_l = icmp ne {s} %msg_len, 0\n" ++
            "  %do_p = and i1 %has_m, %has_l\n" ++
            "  br i1 %do_p, label %wr_m, label %go_trap\n" ++
            "wr_m:\n" ++
            "  %_ign = call {s} @_cx_rt_sys_write(i32 2, ptr %msg_ptr, {s} %msg_len)\n" ++
            "  br label %go_trap\n" ++
            "go_trap:\n" ++
            "  %_nl = call {s} @_cx_rt_sys_write(i32 2, ptr @.cx_panic_nl, {s} 1)\n" ++
            "  call void @_cx_rt_trap(i32 1)\n" ++
            "  unreachable\n" ++
            "}}\n\n" ++
            "define internal void @_cx_rt_sys_exit(i32 %code) noreturn {s} {{\n" ++
            "entry:\n" ++
            "  %ebuf = alloca [64 x i8], align 8\n" ++
            "  %en32 = call i32 (ptr, {s}, ptr, ...) @snprintf(ptr %ebuf, {s} 64, ptr @.cx_fmt_exit, i32 %code)\n" ++
            "  %eok = icmp sgt i32 %en32, 0\n" ++
            "  %ecl = select i1 %eok, i32 %en32, i32 0\n",
        .{
            ptr_int,
            fn_attrs,
            ptr_int,
            ptr_int,
            ptr_int,
            ptr_int,
            ptr_int,
            ptr_int,
            ptr_int,
            fn_attrs,
            ptr_int,
            ptr_int,
        },
    );
    if (emitter.cfg.target.isWasm()) {
        try emitter.writeAll(
            "  call void @_cx_rt_trace_append(ptr %ebuf, i32 %ecl)\n" ++
                "  %_fl = call i32 @fflush(ptr null)\n" ++
                "  call void @_exit(i32 %code)\n" ++
                "  unreachable\n}\n\n",
        );
    } else {
        try emitter.writeAll(
            "  %eln = zext i32 %ecl to i64\n" ++
                "  call void @_cx_rt_trace_append(ptr %ebuf, i64 %eln)\n" ++
                "  %_fl = call i32 @fflush(ptr null)\n" ++
                "  call void @_exit(i32 %code)\n" ++
                "  unreachable\n}\n\n",
        );
    }

    // `@_cx_record_err_ret(<usize> %site_tag)` in `--dev` mode:
    if (!emitter.cfg.is_release_mode) {
        try emitter.print(
            "define internal void @_cx_record_err_ret({s} %site_tag) {s} {{\n" ++
                "entry:\n" ++
                "  %w_ptr = getelementptr inbounds {{ [16 x {s}], i32, i32 }}, ptr @_cx_err_trace, i32 0, i32 1\n" ++
                "  %w_val = load i32, ptr %w_ptr, align 4\n" ++
                "  %slot_i = and i32 %w_val, 15\n" ++
                "  %pc_ptr = getelementptr inbounds {{ [16 x {s}], i32, i32 }}, " ++
                "ptr @_cx_err_trace, i32 0, i32 0, i32 %slot_i\n" ++
                "  store {s} %site_tag, ptr %pc_ptr, align {d}\n" ++
                "  %w_next = add i32 %w_val, 1\n" ++
                "  store i32 %w_next, ptr %w_ptr, align 4\n" ++
                "  %c_ptr = getelementptr inbounds {{ [16 x {s}], i32, i32 }}, ptr @_cx_err_trace, i32 0, i32 2\n" ++
                "  %c_val = load i32, ptr %c_ptr, align 4\n" ++
                "  %lt16 = icmp ult i32 %c_val, 16\n" ++
                "  %c_inc = add i32 %c_val, 1\n" ++
                "  %c_new = select i1 %lt16, i32 %c_inc, i32 %c_val\n" ++
                "  store i32 %c_new, ptr %c_ptr, align 4\n" ++
                "  ret void\n" ++
                "}}\n\n",
            .{
                ptr_int,                       fn_attrs, ptr_int, ptr_int, ptr_int,
                emitter.cfg.target.ptrBytes(), ptr_int,
            },
        );
    }
}

/// Emits external `declare` prototypes for all referenced `extern` FFI symbols.
fn emitExternDeclarations(emitter: *LlvmModuleEmitter) !void {
    var emitted_decls: usize = 0;
    for (emitter.extern_syms.items) |sym_idx| {
        const sym_rec = emitter.input.sym_table.getSymbol(sym_idx).*;
        const sig_view = emitter.input.pool.getFnSignatureView(sym_rec.type_id) orelse continue;
        const ext_name = if (sym_rec.contract_flags.has_link_name and sym_rec.link_name_text.len > 0)
            sym_rec.link_name_text
        else
            sym_rec.name_text;

        if (!(try emitter.markExternDeclared(ext_name))) continue;

        var ext_recipe = try classifyFnTypeAbi(emitter, sym_rec.type_id, true, true);
        defer ext_recipe.deinit(emitter.allocator);

        const ret_decl = try formatAbiReturnDecl(emitter, sig_view.ret_ty, &ext_recipe);
        defer emitter.allocator.free(ret_decl.full_decl);
        defer emitter.allocator.free(ret_decl.bare_ty);

        const ext_ident = try formatLlvmGlobalIdent(emitter.allocator, ext_name);
        defer emitter.allocator.free(ext_ident);

        try emitter.print("declare {s}{s} {s}(", .{
            resolveCallingConvPrefix(&ext_recipe),
            ret_decl.full_decl,
            ext_ident,
        });
        var param_count_emitted: usize = 0;
        if (ext_recipe.has_sret) {
            const sret_piece = try formatAbiParamDeclPiece(
                emitter,
                sig_view.ret_ty,
                ext_recipe.sret_recipe,
                null,
            );
            defer emitter.allocator.free(sret_piece);
            try emitter.writeAll(sret_piece);
            param_count_emitted += 1;
        }
        for (ext_recipe.param_recipes, 0..) |p_rec, idx| {
            if (p_rec.pass_mode == .ignore_zst) continue;
            const piece_s = try formatAbiParamDeclPiece(emitter, sig_view.getParamType(idx), p_rec, null);
            defer emitter.allocator.free(piece_s);
            if (param_count_emitted > 0) try emitter.writeAll(", ");
            try emitter.writeAll(piece_s);
            param_count_emitted += 1;
        }
        if (emitter.cfg.target.os == .wasi and WASI_PREVIEW1_IMPORT_SET.has(ext_name)) {
            const esc_imp = try escapeMetadataStringAlloc(emitter.allocator, ext_name);
            defer emitter.allocator.free(esc_imp);
            try emitter.print(
                ") nounwind \"wasm-import-module\"=\"wasi_snapshot_preview1\" " ++
                    "\"wasm-import-name\"=\"{s}\"\n",
                .{esc_imp},
            );
        } else {
            try emitter.writeAll(") nounwind\n");
        }
        emitted_decls += 1;
    }
    if (emitted_decls > 0) try emitter.writeAll("\n");
}

// ---------- Sum Layout, Drop Glue, Places & Pentagon ----------

/// Resolves the payload `TypeId` of variant `tag_ord` in `.enum_ty` / `.optional_ty` / `.result_ty`.
fn resolveEnumVariantPayloadType(
    emitter: *const LlvmModuleEmitter,
    raw_sum_ty: TypeId,
    tag_ord: u32,
) TypeId {
    const sum_ty = emitter.input.pool.unwrapUnderlyingType(raw_sum_ty);
    if (sum_ty.isPrimitiveOrSentinel()) return .unit_ty;
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
                    if (mem_sym.type_id.isNone()) return .unit_ty;
                    return emitter.input.pool.unwrapUnderlyingType(subst.resolve(mem_sym.type_id));
                }
                cur_ord += 1;
            }
            return .unit_ty;
        },
        else => return .unit_ty,
    }
}

/// Resolves field `field_ord` of `.union_ty` `union_ty`.
fn resolveUnionFieldType(
    emitter: *const LlvmModuleEmitter,
    union_ty: TypeId,
    field_ord: u32,
) TypeId {
    const sym_idx = SymbolIndex.fromInt(emitter.input.pool.getNode(union_ty).rhs);
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

/// Reads the active `i32` discriminant ordinal of `raw_sum_ty` stored in memory at `base_ptr`.
fn emitReadSumDiscriminantFromPtr(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    raw_sum_ty: TypeId,
    base_ptr: []const u8,
    base_align: u32,
) ![]u8 {
    const sum_ty = emitter.input.pool.unwrapUnderlyingType(raw_sum_ty);
    const detail_opt = try emitter.resolver.getSumDetail(sum_ty);
    if (detail_opt == null) {
        return emitter.allocator.dupe(u8, "0");
    }
    const detail = detail_opt.?;
    switch (detail.repr) {
        .not_sum => return emitter.allocator.dupe(u8, "0"),
        .transparent_ok => {
            return std.fmt.allocPrint(emitter.allocator, "{d}", .{detail.payload_discriminant});
        },
        .explicit_tag => {
            const tmp_id = state.nextTmp();
            const tag_bits: u16 = @as(u16, @max(detail.tag_bytes, 1)) * 8;
            const eff_align = @min(@max(base_align, 1), @max(detail.tag_bytes, 1));
            try state.print(
                "  %_tag_ld_{d} = load i{d}, ptr {s}, align {d}\n",
                .{ tmp_id, tag_bits, base_ptr, eff_align },
            );
            if (tag_bits == 32) {
                return std.fmt.allocPrint(emitter.allocator, "%_tag_ld_{d}", .{tmp_id});
            } else if (tag_bits < 32) {
                try state.print(
                    "  %_tag_32_{d} = zext i{d} %_tag_ld_{d} to i32\n",
                    .{ tmp_id, tag_bits, tmp_id },
                );
                return std.fmt.allocPrint(emitter.allocator, "%_tag_32_{d}", .{tmp_id});
            } else {
                try state.print(
                    "  %_tag_32_{d} = trunc i{d} %_tag_ld_{d} to i32\n",
                    .{ tmp_id, tag_bits, tmp_id },
                );
                return std.fmt.allocPrint(emitter.allocator, "%_tag_32_{d}", .{tmp_id});
            }
        },
        .niche_single => {
            const tmp_id = state.nextTmp();
            const ptr_int = ptrIntType(emitter);
            const niche_ptr = if (detail.niche.byte_offset == 0)
                try emitter.allocator.dupe(u8, base_ptr)
            else blk: {
                try state.print(
                    "  %_nptr_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                    .{ tmp_id, base_ptr, ptr_int, detail.niche.byte_offset },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_nptr_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(niche_ptr);

            if (detail.niche.encoding == .zero_niche) {
                try state.print(
                    "  %_nval_{d} = load ptr, ptr {s}, align 1\n" ++
                        "  %_isz_{d} = icmp eq ptr %_nval_{d}, null\n" ++
                        "  %_ndisc_{d} = select i1 %_isz_{d}, i32 {d}, i32 {d}\n",
                    .{
                        tmp_id,
                        niche_ptr,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        detail.zst_discriminant,
                        detail.payload_discriminant,
                    },
                );
                return std.fmt.allocPrint(emitter.allocator, "%_ndisc_{d}", .{tmp_id});
            } else {
                const s_bits: u16 = @as(u16, @max(detail.niche.scalar_bytes, 1)) * 8;
                try state.print(
                    "  %_nval_{d} = load i{d}, ptr {s}, align 1\n",
                    .{ tmp_id, s_bits, niche_ptr },
                );
                if (s_bits < 64) {
                    try state.print(
                        "  %_n64_{d} = zext i{d} %_nval_{d} to i64\n" ++
                            "  %_isz_{d} = icmp eq i64 %_n64_{d}, {d}\n",
                        .{ tmp_id, s_bits, tmp_id, tmp_id, tmp_id, detail.niche.invalid_first },
                    );
                } else {
                    try state.print(
                        "  %_isz_{d} = icmp eq i{d} %_nval_{d}, {d}\n",
                        .{ tmp_id, s_bits, tmp_id, detail.niche.invalid_first },
                    );
                }
                try state.print(
                    "  %_ndisc_{d} = select i1 %_isz_{d}, i32 {d}, i32 {d}\n",
                    .{
                        tmp_id,
                        tmp_id,
                        detail.zst_discriminant,
                        detail.payload_discriminant,
                    },
                );
                return std.fmt.allocPrint(emitter.allocator, "%_ndisc_{d}", .{tmp_id});
            }
        },
    }
}

/// Writes active discriminant `tag_ord` into `raw_sum_ty` at `base_ptr` (preserving payload on non-ZST).
fn emitWriteSumDiscriminantToPtr(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    raw_sum_ty: TypeId,
    base_ptr: []const u8,
    base_align: u32,
    tag_ord: u32,
) !void {
    const sum_ty = emitter.input.pool.unwrapUnderlyingType(raw_sum_ty);
    const detail = (try emitter.resolver.getSumDetail(sum_ty)) orelse return;
    switch (detail.repr) {
        .not_sum, .transparent_ok => {},
        .explicit_tag => {
            const tag_bits: u16 = @as(u16, @max(detail.tag_bytes, 1)) * 8;
            const eff_align = @min(@max(base_align, 1), @max(detail.tag_bytes, 1));
            try state.print(
                "  store i{d} {d}, ptr {s}, align {d}\n",
                .{ tag_bits, tag_ord, base_ptr, eff_align },
            );
        },
        .niche_single => {
            if (tag_ord != detail.zst_discriminant) return;
            const tmp_id = state.nextTmp();
            const ptr_int = ptrIntType(emitter);
            const niche_ptr = if (detail.niche.byte_offset == 0)
                try emitter.allocator.dupe(u8, base_ptr)
            else blk: {
                try state.print(
                    "  %_wnp_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                    .{ tmp_id, base_ptr, ptr_int, detail.niche.byte_offset },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_wnp_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(niche_ptr);

            if (detail.niche.encoding == .zero_niche) {
                try state.print("  store ptr null, ptr {s}, align 1\n", .{niche_ptr});
            } else {
                const s_bits: u16 = @as(u16, @max(detail.niche.scalar_bytes, 1)) * 8;
                try state.print(
                    "  store i{d} {d}, ptr {s}, align 1\n",
                    .{ s_bits, detail.niche.invalid_first, niche_ptr },
                );
            }
        },
    }
}

/// Finds a lowered `Drop::drop` `MirBody` index for `drop_ty` if one exists in `emitter.input.bodies`.
fn lookupDropBodyIndexForType(emitter: *const LlvmModuleEmitter, drop_ty: TypeId) ?u32 {
    const ty = emitter.input.pool.unwrapUnderlyingType(drop_ty);
    if (!ty.isPrimitiveOrSentinel()) {
        const node = emitter.input.pool.getNode(ty);
        if (node.tag == .struct_ty or node.tag == .enum_ty or node.tag == .union_ty) {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
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
    }
    for (emitter.input.bodies, 0..) |*cand_body, b_idx| {
        if (cand_body.param_count != 1 or cand_body.locals.items.len < 2) continue;
        const fn_name = emitter.input.interner.get(cand_body.name);
        if (!std.mem.eql(u8, fn_name, "drop") and
            !std.mem.endsWith(u8, fn_name, "::drop") and
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

/// Emits `@_cx_drop_ty_<id>(ptr %_self_ptr)` helpers for all registered `drop_type_list` types.
fn emitDropHelpersAndClosureThunks(emitter: *LlvmModuleEmitter) !void {
    const ptr_int = ptrIntType(emitter);
    const fn_attrs = fnUnwindAttrs(emitter);

    // [1] Synthesized closure forwarding thunks `@_cx_cthunk_<idx>`:
    for (emitter.closure_thunks.items, 0..) |thunk, thunk_idx| {
        try emitSingleClosureThunk(emitter, thunk, @intCast(thunk_idx));
    }

    // [1b] Synthesized stateful `fn(…)` `%_cx_ctx` adapter thunks `@_cx_fn_ctxwrap_<target_b>`:
    for (emitter.ctx_wrap_bodies.items) |target_b| {
        if (emitter.ctx_wrap_map.get(target_b)) |wrap_fn_ty| {
            try emitSingleFnCtxWrapper(emitter, target_b, wrap_fn_ty);
        }
    }

    // [2] Synthesized recursive drop glue `@_cx_drop_ty_<id>`:
    for (emitter.drop_type_list.items) |drop_ty| {
        if (try isZeroSizedType(emitter, drop_ty)) continue;
        try emitter.print(
            "define internal void @_cx_drop_ty_{d}(ptr %_self_ptr) {s} {{\n" ++
                "entry:\n" ++
                "  %_isn = icmp eq ptr %_self_ptr, null\n" ++
                "  br i1 %_isn, label %done_drop, label %run_drop\n",
            .{ drop_ty.toU32(), fn_attrs },
        );

        var state = BodyEmitState{
            .allocator = emitter.allocator,
            .cur_label = try emitter.allocator.dupe(u8, "run_drop"),
            .local_ptrs = try emitter.allocator.alloc([]u8, 0),
            .local_aligns = try emitter.allocator.alloc(u32, 0),
            .edge_pred_labels = try emitter.allocator.alloc([]u8, 0),
            .edge_call_ret_vals = try emitter.allocator.alloc([]u8, 0),
            .edge_trampoline = try emitter.allocator.alloc(?u32, 0),
            .block_access_group = try emitter.allocator.alloc(u32, 0),
        };
        defer state.deinit();

        if (lookupDropBodyIndexForType(emitter, drop_ty)) |drop_b| {
            const drop_body = &emitter.input.bodies[drop_b];
            const drop_rec = &emitter.body_recipes.items[drop_b];
            const p_decl = drop_body.locals.items[1];
            const p_unwrapped = emitter.input.pool.unwrapUnderlyingType(p_decl.type_id);
            const p_tag = emitter.input.pool.getNode(p_unwrapped).tag;
            const is_ptr_param = p_decl.mode() == .inout_mode or p_decl.mode() == .set_mode or
                p_tag == .ref_ty or p_tag == .mut_ref_ty or p_tag == .raw_ptr_ty;
            const drop_lay = try emitter.resolver.resolveType(drop_ty);

            var call_args: std.ArrayListUnmanaged(u8) = .empty;
            defer call_args.deinit(emitter.allocator);
            var arg_emitted: usize = 0;
            if (drop_rec.has_implicit_context) {
                const ctx_decl = try formatAbiParamDeclPiece(
                    emitter,
                    .usize_ty,
                    drop_rec.context_recipe,
                    "@_cx_default_ctx",
                );
                defer emitter.allocator.free(ctx_decl);
                try call_args.appendSlice(emitter.allocator, ctx_decl);
                arg_emitted += 1;
            }
            var bounce_slot_opt: ?[]u8 = null;
            var bounce_align: u32 = 1;
            defer if (bounce_slot_opt) |bs| emitter.allocator.free(bs);

            if (drop_rec.param_recipes.len >= 1 and drop_rec.param_recipes[0].pass_mode != .ignore_zst) {
                const p0_rec = drop_rec.param_recipes[0];
                const is_indirect_self = is_ptr_param or p0_rec.pass_mode == .indirect_by_ref or
                    p0_rec.pass_mode == .indirect_byval;
                const arg_op = if (is_indirect_self) blk: {
                    if (p0_rec.pointee_align_bytes > 1 and drop_lay.size_bytes > 0) {
                        bounce_align = @max(drop_lay.alignBytes(), p0_rec.pointee_align_bytes);
                        const bounce_slot = try state.allocEntryBytes(drop_lay.size_bytes, bounce_align);
                        try emitMemcpyBytes(
                            emitter,
                            &state,
                            bounce_slot,
                            bounce_align,
                            "%_self_ptr",
                            1,
                            drop_lay.size_bytes,
                        );
                        bounce_slot_opt = try emitter.allocator.dupe(u8, bounce_slot);
                        break :blk bounce_slot;
                    }
                    break :blk try emitter.allocator.dupe(u8, "%_self_ptr");
                } else blk: {
                    const loaded_v = try emitLoadValueFromPtr(
                        emitter,
                        &state,
                        p_decl.type_id,
                        "%_self_ptr",
                        1,
                        null,
                        0,
                        0,
                        0,
                    );
                    defer emitter.allocator.free(loaded_v);
                    const abi_ty = try formatAbiParamOrRetType(emitter, p_decl.type_id, p0_rec);
                    defer emitter.allocator.free(abi_ty);
                    break :blk try emitCoerceValueToAbi(emitter, &state, p_decl.type_id, loaded_v, abi_ty);
                };
                defer emitter.allocator.free(arg_op);
                const piece_decl = try formatAbiParamDeclPiece(emitter, p_decl.type_id, p0_rec, arg_op);
                defer emitter.allocator.free(piece_decl);
                if (arg_emitted > 0) try call_args.appendSlice(emitter.allocator, ", ");
                try call_args.appendSlice(emitter.allocator, piece_decl);
            }

            const callee_op = if (emitter.input.is_dev_got_enabled) blk: {
                const got_t = state.nextTmp();
                try state.print(
                    "  %_got_p_{d} = getelementptr inbounds [{d} x ptr], " ++
                        "ptr @_cx_dev_got, {s} 0, {s} {d}\n" ++
                        "  %_got_fn_{d} = load ptr, ptr %_got_p_{d}, align {d}\n",
                    .{
                        got_t,
                        @max(emitter.input.bodies.len, 1),
                        ptr_int,
                        ptr_int,
                        drop_b,
                        got_t,
                        got_t,
                        emitter.cfg.target.ptrBytes(),
                    },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_got_fn_{d}", .{got_t});
            } else try formatLlvmGlobalIdent(emitter.allocator, emitter.body_llvm_names.items[drop_b]);
            defer emitter.allocator.free(callee_op);

            try state.print(
                "  call {s}void {s}({s})\n",
                .{ resolveCallingConvPrefix(drop_rec), callee_op, call_args.items },
            );
            if (bounce_slot_opt) |bounce_slot| {
                if (is_ptr_param and !drop_rec.param_recipes[0].attrs().is_readonly) {
                    try emitMemcpyBytes(
                        emitter,
                        &state,
                        "%_self_ptr",
                        1,
                        bounce_slot,
                        bounce_align,
                        drop_lay.size_bytes,
                    );
                }
            }
        }

        const node = emitter.input.pool.getNode(drop_ty);
        switch (node.tag) {
            .struct_ty, .tuple_ty => {
                const lay = try emitter.resolver.resolveType(drop_ty);
                var rev_i: u32 = lay.aux_len;
                while (rev_i > 0) {
                    rev_i -= 1;
                    const fld = emitter.resolver.fields_by_decl.items[lay.aux_start + rev_i];
                    const fld_ty = try unwrapTransparentType(emitter, fld.field_ty);
                    if (fld.size_bytes > 0 and emitter.drop_type_set.contains(fld_ty.toU32())) {
                        const t_id = state.nextTmp();
                        try state.print(
                            "  %_dfld_{d} = getelementptr inbounds i8, ptr %_self_ptr, {s} {d}\n" ++
                                "  call void @_cx_drop_ty_{d}(ptr %_dfld_{d})\n",
                            .{ t_id, ptr_int, fld.byte_offset, fld_ty.toU32(), t_id },
                        );
                    }
                }
            },
            .array_ty => {
                const elem_ty = try unwrapTransparentType(emitter, TypeId.fromInt(node.lhs));
                const arr_len: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                if (arr_len > 0 and emitter.drop_type_set.contains(elem_ty.toU32()) and
                    !(try isZeroSizedType(emitter, elem_ty)))
                {
                    const elem_lay = try emitter.resolver.resolveType(elem_ty);
                    var elem_k: u64 = arr_len;
                    while (elem_k > 0) {
                        elem_k -= 1;
                        const t_id = state.nextTmp();
                        try state.print(
                            "  %_darr_{d} = getelementptr inbounds i8, ptr %_self_ptr, {s} {d}\n" ++
                                "  call void @_cx_drop_ty_{d}(ptr %_darr_{d})\n",
                            .{ t_id, ptr_int, elem_k * elem_lay.stride_bytes, elem_ty.toU32(), t_id },
                        );
                    }
                }
            },
            .optional_ty, .result_ty, .enum_ty => {
                if (try emitter.resolver.getSumDetail(drop_ty)) |sum_detail| {
                    const discr_s = try emitReadSumDiscriminantFromPtr(emitter, &state, drop_ty, "%_self_ptr", 1);
                    defer emitter.allocator.free(discr_s);
                    const var_count: u32 = switch (node.tag) {
                        .optional_ty, .result_ty => 2,
                        .enum_ty => blk: {
                            const sym_idx = SymbolIndex.fromInt(node.rhs);
                            if (sym_idx.isNone() or sym_idx.asInt() >= emitter.input.sym_table.symbols.items.len) {
                                break :blk 0;
                            }
                            const enum_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
                            if (enum_sym.target_scope.isNone()) break :blk 0;
                            var cnt: u32 = 0;
                            for (emitter.input.sym_table.getScopeMembers(enum_sym.target_scope)) |m_idx| {
                                if (emitter.input.sym_table.getSymbol(m_idx).kind == .enum_variant_sym) cnt += 1;
                            }
                            break :blk cnt;
                        },
                        else => 0,
                    };
                    var var_ord: u32 = 0;
                    while (var_ord < var_count) : (var_ord += 1) {
                        const v_pay = try unwrapTransparentType(
                            emitter,
                            resolveEnumVariantPayloadType(emitter, drop_ty, var_ord),
                        );
                        if (emitter.drop_type_set.contains(v_pay.toU32()) and
                            !(try isZeroSizedType(emitter, v_pay)))
                        {
                            const t_id = state.nextTmp();
                            try state.print(
                                "  %_dvc_{d} = icmp eq i32 {s}, {d}\n" ++
                                    "  br i1 %_dvc_{d}, label %_dv_hit_{d}, label %_dv_nxt_{d}\n" ++
                                    "_dv_hit_{d}:\n" ++
                                    "  %_dvp_{d} = getelementptr inbounds i8, ptr %_self_ptr, {s} {d}\n" ++
                                    "  call void @_cx_drop_ty_{d}(ptr %_dvp_{d})\n" ++
                                    "  br label %_dv_nxt_{d}\n" ++
                                    "_dv_nxt_{d}:\n",
                                .{
                                    t_id,
                                    discr_s,
                                    var_ord,
                                    t_id,
                                    t_id,
                                    t_id,
                                    t_id,
                                    t_id,
                                    ptr_int,
                                    sum_detail.payload_offset,
                                    v_pay.toU32(),
                                    t_id,
                                    t_id,
                                    t_id,
                                },
                            );
                        }
                    }
                }
            },
            else => {},
        }

        try emitter.writeAll("run_drop:\n");
        if (state.entry_allocas.items.len > 0) {
            try emitter.writeAll(state.entry_allocas.items);
        }
        try emitter.writeAll(state.cur_buf.items);
        try emitter.writeAll("  br label %done_drop\ndone_drop:\n  ret void\n}\n\n");
    }
}

/// Adapts incoming parameter `param_name` (`src_rec`) into a callee argument declaration piece (`dst_rec`).
fn emitForwardAdaptedParamLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    param_ty: TypeId,
    src_rec: codegen_abi.AbiParamRecipe,
    dst_rec: codegen_abi.AbiParamRecipe,
    param_name: []const u8,
) ![]u8 {
    const src_abi_ty = try formatAbiParamOrRetType(emitter, param_ty, src_rec);
    defer emitter.allocator.free(src_abi_ty);
    const dst_abi_ty = try formatAbiParamOrRetType(emitter, param_ty, dst_rec);
    defer emitter.allocator.free(dst_abi_ty);

    const is_src_indirect = src_rec.pass_mode == .indirect_by_ref or src_rec.pass_mode == .indirect_byval;
    const is_dst_indirect = dst_rec.pass_mode == .indirect_by_ref or dst_rec.pass_mode == .indirect_byval;

    if (src_rec.pass_mode == dst_rec.pass_mode and
        std.mem.eql(u8, src_abi_ty, dst_abi_ty) and
        (!is_dst_indirect or src_rec.pointee_align_bytes >= dst_rec.pointee_align_bytes))
    {
        return formatAbiParamDeclPiece(emitter, param_ty, dst_rec, param_name);
    }

    const lay = try emitter.resolver.resolveType(param_ty);
    const slot_align = @max(@max(lay.alignBytes(), dst_rec.pointee_align_bytes), 8);
    const slot_ptr = try state.allocEntryBytes(@max(lay.size_bytes, 1), slot_align);
    defer emitter.allocator.free(slot_ptr);

    if (is_src_indirect) {
        try emitMemcpyBytes(
            emitter,
            state,
            slot_ptr,
            slot_align,
            param_name,
            @max(src_rec.pointee_align_bytes, 1),
            lay.size_bytes,
        );
    } else {
        const unpacked_v = try emitCoerceAbiToValue(emitter, state, param_ty, src_abi_ty, param_name);
        defer emitter.allocator.free(unpacked_v);
        try emitStoreValueToPtr(emitter, state, param_ty, unpacked_v, slot_ptr, slot_align, 0, 0, 0);
    }

    if (is_dst_indirect) {
        return formatAbiParamDeclPiece(emitter, param_ty, dst_rec, slot_ptr);
    }

    const loaded_v = try emitLoadValueFromPtr(
        emitter,
        state,
        param_ty,
        slot_ptr,
        slot_align,
        null,
        0,
        0,
        0,
    );
    defer emitter.allocator.free(loaded_v);
    const coerced_v = try emitCoerceValueToAbi(emitter, state, param_ty, loaded_v, dst_abi_ty);
    defer emitter.allocator.free(coerced_v);
    return formatAbiParamDeclPiece(emitter, param_ty, dst_rec, coerced_v);
}

/// Emits a synthesized closure forwarding thunk `@_cx_cthunk_<idx>(ptr %_env, …)`.
fn emitSingleClosureThunk(
    emitter: *LlvmModuleEmitter,
    thunk: ClosureThunkSpec,
    thunk_idx: u32,
) !void {
    const sig_view = emitter.input.pool.getFnSignatureView(thunk.closure_ty) orelse return;
    var clos_recipe = try classifyFnTypeAbi(emitter, thunk.closure_ty, false, true);
    defer clos_recipe.deinit(emitter.allocator);

    const callee_rec = &emitter.body_recipes.items[thunk.callee_body_idx];
    const callee_body = &emitter.input.bodies[thunk.callee_body_idx];
    const ptr_int = ptrIntType(emitter);

    const ret_decl = try formatAbiReturnDecl(emitter, sig_view.ret_ty, &clos_recipe);
    defer emitter.allocator.free(ret_decl.full_decl);
    defer emitter.allocator.free(ret_decl.bare_ty);

    try emitter.print(
        "define internal {s}{s} @_cx_cthunk_{d}(",
        .{ resolveCallingConvPrefix(&clos_recipe), ret_decl.full_decl, thunk_idx },
    );
    var hdr_count: usize = 0;
    if (clos_recipe.has_sret) {
        const sret_s = try formatAbiParamDeclPiece(
            emitter,
            sig_view.ret_ty,
            clos_recipe.sret_recipe,
            "%_sret",
        );
        defer emitter.allocator.free(sret_s);
        try emitter.writeAll(sret_s);
        hdr_count += 1;
    }
    if (hdr_count > 0) try emitter.writeAll(", ");
    try emitter.writeAll("ptr nonnull noundef %_env");
    hdr_count += 1;

    for (clos_recipe.param_recipes, 0..) |p_rec, idx| {
        if (p_rec.pass_mode == .ignore_zst) continue;
        const p_name = try std.fmt.allocPrint(emitter.allocator, "%_cp_{d}", .{idx});
        defer emitter.allocator.free(p_name);
        const piece_s = try formatAbiParamDeclPiece(emitter, sig_view.getParamType(idx), p_rec, p_name);
        defer emitter.allocator.free(piece_s);
        try emitter.writeAll(", ");
        try emitter.writeAll(piece_s);
    }
    if (clos_recipe.swifterror_kind != .none) {
        try emitter.writeAll(", ptr swifterror %_cx_err_slot");
    }
    try emitter.print(") {s} {{\nentry:\n", .{fnUnwindAttrs(emitter)});

    var state = BodyEmitState{
        .allocator = emitter.allocator,
        .cur_label = try emitter.allocator.dupe(u8, "entry"),
        .local_ptrs = try emitter.allocator.alloc([]u8, 0),
        .local_aligns = try emitter.allocator.alloc(u32, 0),
        .edge_pred_labels = try emitter.allocator.alloc([]u8, 0),
        .edge_call_ret_vals = try emitter.allocator.alloc([]u8, 0),
        .edge_trampoline = try emitter.allocator.alloc(?u32, 0),
        .block_access_group = try emitter.allocator.alloc(u32, 0),
    };
    defer state.deinit();

    var call_args: std.ArrayListUnmanaged(u8) = .empty;
    defer call_args.deinit(emitter.allocator);
    var emitted_args: usize = 0;

    if (callee_rec.has_sret) {
        const sret_s = try formatAbiParamDeclPiece(
            emitter,
            callee_body.ret_ty,
            callee_rec.sret_recipe,
            "%_sret",
        );
        defer emitter.allocator.free(sret_s);
        try call_args.appendSlice(emitter.allocator, sret_s);
        emitted_args += 1;
    }
    if (callee_rec.has_implicit_context) {
        const ctx_s = try formatAbiParamDeclPiece(
            emitter,
            .usize_ty,
            callee_rec.context_recipe,
            "@_cx_default_ctx",
        );
        defer emitter.allocator.free(ctx_s);
        if (emitted_args > 0) try call_args.appendSlice(emitter.allocator, ", ");
        try call_args.appendSlice(emitter.allocator, ctx_s);
        emitted_args += 1;
    }

    // Load captured values from `%_env` at aligned byte offsets:
    var cur_env_off: u64 = 0;
    const cap_count = thunk.capture_types.len;
    for (thunk.capture_types, 0..) |cap_ty, cap_i| {
        const cap_lay = try emitter.resolver.resolveType(cap_ty);
        if (cap_lay.size_bytes == 0) continue;
        cur_env_off = std.mem.alignForward(u64, cur_env_off, @max(@as(u64, cap_lay.alignBytes()), 1));
        if (cap_i < callee_rec.param_recipes.len) {
            const dst_rec = callee_rec.param_recipes[cap_i];
            if (dst_rec.pass_mode != .ignore_zst) {
                const t_id = state.nextTmp();
                try state.print(
                    "  %_cap_ptr_{d} = getelementptr inbounds i8, ptr %_env, {s} {d}\n",
                    .{ t_id, ptr_int, cur_env_off },
                );
                const cap_ptr_s = try std.fmt.allocPrint(emitter.allocator, "%_cap_ptr_{d}", .{t_id});
                defer emitter.allocator.free(cap_ptr_s);
                const arg_val_s = if (dst_rec.pass_mode == .indirect_by_ref or
                    dst_rec.pass_mode == .indirect_byval)
                    try emitter.allocator.dupe(u8, cap_ptr_s)
                else blk: {
                    const loaded_c = try emitLoadValueFromPtr(
                        emitter,
                        &state,
                        cap_ty,
                        cap_ptr_s,
                        cap_lay.alignBytes(),
                        null,
                        0,
                        0,
                        0,
                    );
                    defer emitter.allocator.free(loaded_c);
                    const abi_ty = try formatAbiParamOrRetType(emitter, cap_ty, dst_rec);
                    defer emitter.allocator.free(abi_ty);
                    break :blk try emitCoerceValueToAbi(emitter, &state, cap_ty, loaded_c, abi_ty);
                };
                defer emitter.allocator.free(arg_val_s);
                const piece_s = try formatAbiParamDeclPiece(emitter, cap_ty, dst_rec, arg_val_s);
                defer emitter.allocator.free(piece_s);
                if (emitted_args > 0) try call_args.appendSlice(emitter.allocator, ", ");
                try call_args.appendSlice(emitter.allocator, piece_s);
                emitted_args += 1;
            }
        }
        cur_env_off += cap_lay.size_bytes;
    }

    // Append forwarded explicit closure call parameters:
    for (clos_recipe.param_recipes, 0..) |src_rec, idx| {
        if (src_rec.pass_mode == .ignore_zst) continue;
        const callee_p_idx = cap_count + idx;
        if (callee_p_idx >= callee_rec.param_recipes.len) continue;
        const dst_rec = callee_rec.param_recipes[callee_p_idx];
        const p_name = try std.fmt.allocPrint(emitter.allocator, "%_cp_{d}", .{idx});
        defer emitter.allocator.free(p_name);
        const piece_s = try emitForwardAdaptedParamLlvm(
            emitter,
            &state,
            sig_view.getParamType(idx),
            src_rec,
            dst_rec,
            p_name,
        );
        defer emitter.allocator.free(piece_s);
        if (emitted_args > 0) try call_args.appendSlice(emitter.allocator, ", ");
        try call_args.appendSlice(emitter.allocator, piece_s);
        emitted_args += 1;
    }

    if (callee_rec.swifterror_kind != .none) {
        try state.ensureSwifterrorCallSlot();
        try state.writeAll("  store ptr null, ptr %_cx_call_err, align 8\n");
        if (emitted_args > 0) try call_args.appendSlice(emitter.allocator, ", ");
        try call_args.appendSlice(emitter.allocator, "ptr swifterror %_cx_call_err");
    }

    const callee_ret = try formatAbiReturnDecl(emitter, callee_body.ret_ty, callee_rec);
    defer emitter.allocator.free(callee_ret.full_decl);
    defer emitter.allocator.free(callee_ret.bare_ty);

    const callee_ident = try formatLlvmGlobalIdent(
        emitter.allocator,
        emitter.body_llvm_names.items[thunk.callee_body_idx],
    );
    defer emitter.allocator.free(callee_ident);

    if (std.mem.eql(u8, callee_ret.bare_ty, "void")) {
        try state.print(
            "  call {s}void {s}({s})\n",
            .{ resolveCallingConvPrefix(callee_rec), callee_ident, call_args.items },
        );
    } else {
        try state.print(
            "  %_thk_res = call {s}{s} {s}({s})\n",
            .{
                resolveCallingConvPrefix(callee_rec),
                callee_ret.full_decl,
                callee_ident,
                call_args.items,
            },
        );
    }

    if (callee_rec.swifterror_kind != .none and clos_recipe.swifterror_kind != .none) {
        try state.writeAll(
            "  %_thk_err = load ptr, ptr %_cx_call_err, align 8\n" ++
                "  %_thk_he = icmp ne ptr %_thk_err, null\n" ++
                "  br i1 %_thk_he, label %thk_store_err, label %thk_ret_ok\n" ++
                "thk_store_err:\n" ++
                "  store ptr %_thk_err, ptr %_cx_err_slot, align 8\n" ++
                "  br label %thk_ret_ok\n" ++
                "thk_ret_ok:\n",
        );
    }

    if (std.mem.eql(u8, ret_decl.bare_ty, "void")) {
        try state.writeAll("  ret void\n");
    } else {
        try state.print("  ret {s} %_thk_res\n", .{ret_decl.bare_ty});
    }

    if (state.entry_allocas.items.len > 0) {
        try emitter.writeAll(state.entry_allocas.items);
    }
    try emitter.writeAll(state.cur_buf.items);
    try emitter.writeAll("}\n\n");
}

/// Emits a stateful `fn(…)` `%_cx_ctx` adapter thunk `@_cx_fn_ctxwrap_<target_b>` forwarding to a contextless `MirBody`.
fn emitSingleFnCtxWrapper(
    emitter: *LlvmModuleEmitter,
    target_b: u32,
    fn_ty: TypeId,
) !void {
    const sig_view = emitter.input.pool.getFnSignatureView(fn_ty) orelse return;
    var wrap_recipe = try classifyFnTypeAbi(emitter, fn_ty, false, false);
    defer wrap_recipe.deinit(emitter.allocator);

    const callee_rec = &emitter.body_recipes.items[target_b];
    const callee_body = &emitter.input.bodies[target_b];
    const ptr_int = ptrIntType(emitter);

    const ret_decl = try formatAbiReturnDecl(emitter, sig_view.ret_ty, &wrap_recipe);
    defer emitter.allocator.free(ret_decl.full_decl);
    defer emitter.allocator.free(ret_decl.bare_ty);

    try emitter.print(
        "define internal {s}{s} @_cx_fn_ctxwrap_{d}(",
        .{ resolveCallingConvPrefix(&wrap_recipe), ret_decl.full_decl, target_b },
    );
    var hdr_count: usize = 0;
    if (wrap_recipe.has_sret) {
        const sret_s = try formatAbiParamDeclPiece(
            emitter,
            sig_view.ret_ty,
            wrap_recipe.sret_recipe,
            "%_sret",
        );
        defer emitter.allocator.free(sret_s);
        try emitter.writeAll(sret_s);
        hdr_count += 1;
    }
    if (wrap_recipe.has_implicit_context) {
        const ctx_s = try formatAbiParamDeclPiece(
            emitter,
            .usize_ty,
            wrap_recipe.context_recipe,
            "%_cx_ctx",
        );
        defer emitter.allocator.free(ctx_s);
        if (hdr_count > 0) try emitter.writeAll(", ");
        try emitter.writeAll(ctx_s);
        hdr_count += 1;
    }
    for (wrap_recipe.param_recipes, 0..) |param_rec, idx| {
        if (param_rec.pass_mode == .ignore_zst) continue;
        const param_name = try std.fmt.allocPrint(emitter.allocator, "%_wp_{d}", .{idx});
        defer emitter.allocator.free(param_name);
        const piece_s = try formatAbiParamDeclPiece(
            emitter,
            sig_view.getParamType(idx),
            param_rec,
            param_name,
        );
        defer emitter.allocator.free(piece_s);
        if (hdr_count > 0) try emitter.writeAll(", ");
        try emitter.writeAll(piece_s);
        hdr_count += 1;
    }
    if (wrap_recipe.swifterror_kind != .none) {
        if (hdr_count > 0) try emitter.writeAll(", ");
        try emitter.writeAll("ptr swifterror %_cx_err_slot");
    }
    try emitter.print(") {s} {{\nentry:\n", .{fnUnwindAttrs(emitter)});

    var state = BodyEmitState{
        .allocator = emitter.allocator,
        .cur_label = try emitter.allocator.dupe(u8, "entry"),
        .local_ptrs = try emitter.allocator.alloc([]u8, 0),
        .local_aligns = try emitter.allocator.alloc(u32, 0),
        .edge_pred_labels = try emitter.allocator.alloc([]u8, 0),
        .edge_call_ret_vals = try emitter.allocator.alloc([]u8, 0),
        .edge_trampoline = try emitter.allocator.alloc(?u32, 0),
        .block_access_group = try emitter.allocator.alloc(u32, 0),
    };
    defer state.deinit();

    var call_args: std.ArrayListUnmanaged(u8) = .empty;
    defer call_args.deinit(emitter.allocator);
    var emitted_args: usize = 0;

    if (callee_rec.has_sret) {
        const sret_s = try formatAbiParamDeclPiece(
            emitter,
            callee_body.ret_ty,
            callee_rec.sret_recipe,
            "%_sret",
        );
        defer emitter.allocator.free(sret_s);
        try call_args.appendSlice(emitter.allocator, sret_s);
        emitted_args += 1;
    }
    if (callee_rec.has_implicit_context) {
        const ctx_op = if (wrap_recipe.has_implicit_context) "%_cx_ctx" else "@_cx_default_ctx";
        const ctx_s = try formatAbiParamDeclPiece(
            emitter,
            .usize_ty,
            callee_rec.context_recipe,
            ctx_op,
        );
        defer emitter.allocator.free(ctx_s);
        if (emitted_args > 0) try call_args.appendSlice(emitter.allocator, ", ");
        try call_args.appendSlice(emitter.allocator, ctx_s);
        emitted_args += 1;
    }

    for (wrap_recipe.param_recipes, 0..) |src_rec, idx| {
        if (src_rec.pass_mode == .ignore_zst) continue;
        if (idx >= callee_rec.param_recipes.len) continue;
        const dst_rec = callee_rec.param_recipes[idx];
        const param_name = try std.fmt.allocPrint(emitter.allocator, "%_wp_{d}", .{idx});
        defer emitter.allocator.free(param_name);
        const piece_s = try emitForwardAdaptedParamLlvm(
            emitter,
            &state,
            sig_view.getParamType(idx),
            src_rec,
            dst_rec,
            param_name,
        );
        defer emitter.allocator.free(piece_s);
        if (emitted_args > 0) try call_args.appendSlice(emitter.allocator, ", ");
        try call_args.appendSlice(emitter.allocator, piece_s);
        emitted_args += 1;
    }

    if (callee_rec.swifterror_kind != .none) {
        try state.ensureSwifterrorCallSlot();
        try state.writeAll("  store ptr null, ptr %_cx_call_err, align 8\n");
        if (emitted_args > 0) try call_args.appendSlice(emitter.allocator, ", ");
        try call_args.appendSlice(emitter.allocator, "ptr swifterror %_cx_call_err");
    }

    const callee_op = if (emitter.input.is_dev_got_enabled) blk: {
        const got_t = state.nextTmp();
        try state.print(
            "  %_wgot_p_{d} = getelementptr inbounds [{d} x ptr], " ++
                "ptr @_cx_dev_got, {s} 0, {s} {d}\n" ++
                "  %_wgot_f_{d} = load ptr, ptr %_wgot_p_{d}, align {d}\n",
            .{
                got_t,
                @max(emitter.input.bodies.len, 1),
                ptr_int,
                ptr_int,
                target_b,
                got_t,
                got_t,
                emitter.cfg.target.ptrBytes(),
            },
        );
        break :blk try std.fmt.allocPrint(emitter.allocator, "%_wgot_f_{d}", .{got_t});
    } else try formatLlvmGlobalIdent(emitter.allocator, emitter.body_llvm_names.items[target_b]);
    defer emitter.allocator.free(callee_op);

    const callee_ret = try formatAbiReturnDecl(emitter, callee_body.ret_ty, callee_rec);
    defer emitter.allocator.free(callee_ret.full_decl);
    defer emitter.allocator.free(callee_ret.bare_ty);

    if (std.mem.eql(u8, callee_ret.bare_ty, "void")) {
        try state.print(
            "  call {s}void {s}({s})\n",
            .{ resolveCallingConvPrefix(callee_rec), callee_op, call_args.items },
        );
    } else {
        try state.print(
            "  %_wres = call {s}{s} {s}({s})\n",
            .{ resolveCallingConvPrefix(callee_rec), callee_ret.full_decl, callee_op, call_args.items },
        );
    }

    if (callee_rec.swifterror_kind != .none and wrap_recipe.swifterror_kind != .none) {
        try state.writeAll(
            "  %_werr = load ptr, ptr %_cx_call_err, align 8\n" ++
                "  %_whe = icmp ne ptr %_werr, null\n" ++
                "  br i1 %_whe, label %wrap_store_err, label %wrap_ret_ok\n" ++
                "wrap_store_err:\n" ++
                "  store ptr %_werr, ptr %_cx_err_slot, align 8\n" ++
                "  br label %wrap_ret_ok\n" ++
                "wrap_ret_ok:\n",
        );
    }

    if (std.mem.eql(u8, ret_decl.bare_ty, "void")) {
        try state.writeAll("  ret void\n");
    } else {
        try state.print("  ret {s} %_wres\n", .{ret_decl.bare_ty});
    }

    if (state.entry_allocas.items.len > 0) {
        try emitter.writeAll(state.entry_allocas.items);
    }
    try emitter.writeAll(state.cur_buf.items);
    try emitter.writeAll("}\n\n");
}

// ----------- Pentagon Metadata, Places & Load/Store -----------

/// Looks up a Pentagon `ProvenValueRange` for `val_raw` inside `body_idx` (`null` if absent).
fn lookupProvenRange(
    emitter: *const LlvmModuleEmitter,
    body_idx: u32,
    val_raw: u32,
) ?ProvenValueRange {
    const all_ranges = emitter.input.proven_ranges orelse return null;
    if (body_idx >= all_ranges.len) return null;
    for (all_ranges[body_idx]) |entry| {
        if (entry.mir_value_raw == val_raw) return entry;
    }
    return null;
}

/// Interns or returns a valid LLVM `!range !{iW lo, iW hi_excl}` metadata ID (`null` when full domain).
fn getOrInternValidRangeMd(
    emitter: *LlvmModuleEmitter,
    range: ProvenValueRange,
) !?u32 {
    const width = range.bit_width;
    if (width == 0 or width > 64) return null;
    const mask: u64 = if (width == 64) std.math.maxInt(u64) else (@as(u64, 1) << @intCast(width)) - 1;

    var lo_w: u64 = 0;
    var hi_incl_w: u64 = 0;
    if (range.flags().is_signed) {
        const s_min = range.signedMin();
        const s_max = range.signedMax();
        if (s_min > s_max) return null;
        const domain_min: i64 = if (width == 64) std.math.minInt(i64) else -(@as(i64, 1) << @intCast(width - 1));
        const domain_max: i64 = if (width == 64) std.math.maxInt(i64) else (@as(i64, 1) << @intCast(width - 1)) - 1;
        if (s_min <= domain_min and s_max >= domain_max) return null;
        const clamped_min = @max(s_min, domain_min);
        const clamped_max = @min(s_max, domain_max);
        lo_w = (@as(u64, @bitCast(clamped_min))) & mask;
        hi_incl_w = (@as(u64, @bitCast(clamped_max))) & mask;
    } else {
        if (range.min_bits > range.max_bits) return null;
        if (range.min_bits == 0 and range.max_bits >= mask) return null;
        const clamped_min: u64 = @intCast(@min(range.min_bits, @as(u128, mask)));
        const clamped_max: u64 = @intCast(@min(range.max_bits, @as(u128, mask)));
        lo_w = clamped_min & mask;
        hi_incl_w = clamped_max & mask;
    }
    const hi_excl_w: u64 = (hi_incl_w +% 1) & mask;
    // LLVM Verifier rule (`[MAJOR-08]`): `lo_w == hi_excl_w` is full `2^W` domain and MUST NOT emit `!range`.
    if (lo_w == hi_excl_w) return null;

    var hasher = std.hash.Wyhash.init(0x524E_4745);
    hasher.update(std.mem.asBytes(&width));
    hasher.update(std.mem.asBytes(&lo_w));
    hasher.update(std.mem.asBytes(&hi_excl_w));
    const cache_key = hasher.final();
    if (emitter.range_md_cache.get(cache_key)) |existing_md| return existing_md;

    const rhs = try std.fmt.allocPrint(
        emitter.allocator,
        "!{{i{d} {d}, i{d} {d}}}",
        .{ width, lo_w, width, hi_excl_w },
    );
    defer emitter.allocator.free(rhs);
    const md_id = try emitter.addMetadataNode(rhs);
    try emitter.range_md_cache.put(emitter.allocator, cache_key, md_id);
    return md_id;
}

/// Emits `@llvm.assume(i1 true) [ "nonnull"…, "align"… ]` when `range` proves pointer facts.
fn maybeEmitPointerAssume(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    ptr_ssa: []const u8,
    range: ProvenValueRange,
) !void {
    const is_nn = range.flags().is_nonnull_ptr or range.flags().is_non_zero;
    const align_log2 = range.proven_align_log2;
    if (!is_nn and align_log2 == 0) return;

    try emitter.requireIntrinsicDecl("declare void @llvm.assume(i1 noundef)");
    if (is_nn and align_log2 > 0) {
        const align_bytes: u64 = @as(u64, 1) << @intCast(@min(align_log2, 30));
        try state.print(
            "  call void @llvm.assume(i1 true) [ \"nonnull\"(ptr {s}), \"align\"(ptr {s}, i64 {d}) ]\n",
            .{ ptr_ssa, ptr_ssa, align_bytes },
        );
    } else if (is_nn) {
        try state.print(
            "  call void @llvm.assume(i1 true) [ \"nonnull\"(ptr {s}) ]\n",
            .{ptr_ssa},
        );
    } else {
        const align_bytes: u64 = @as(u64, 1) << @intCast(@min(align_log2, 30));
        try state.print(
            "  call void @llvm.assume(i1 true) [ \"align\"(ptr {s}, i64 {d}) ]\n",
            .{ ptr_ssa, align_bytes },
        );
    }
}

/// Checks whether Pentagon `ProvenValueRange` bounds prove `nsw` and/or `nuw` on `add`/`sub`/`mul`.
fn checkProvenNoWrapFlags(
    emitter: *const LlvmModuleEmitter,
    body_idx: u32,
    op_kind: mir.BinOpKind,
    lhs_raw: u32,
    rhs_raw: u32,
    bits: u16,
) struct { has_nsw: bool, has_nuw: bool } {
    if (bits == 0 or bits > 64) return .{ .has_nsw = false, .has_nuw = false };
    const lhs_r = lookupProvenRange(emitter, body_idx, lhs_raw) orelse
        return .{ .has_nsw = false, .has_nuw = false };
    const rhs_r = lookupProvenRange(emitter, body_idx, rhs_raw) orelse
        return .{ .has_nsw = false, .has_nuw = false };

    var has_nsw = false;
    var has_nuw = false;

    if (lhs_r.flags().is_signed and rhs_r.flags().is_signed) {
        const l_lo: i128 = lhs_r.signedMin();
        const l_hi: i128 = lhs_r.signedMax();
        const r_lo: i128 = rhs_r.signedMin();
        const r_hi: i128 = rhs_r.signedMax();
        const s_min: i128 = -(@as(i128, 1) << @intCast(bits - 1));
        const s_max: i128 = (@as(i128, 1) << @intCast(bits - 1)) - 1;
        switch (op_kind) {
            .add_wrap => {
                has_nsw = (l_lo + r_lo >= s_min) and (l_hi + r_hi <= s_max);
            },
            .sub_wrap => {
                has_nsw = (l_lo - r_hi >= s_min) and (l_hi - r_lo <= s_max);
            },
            .mul_wrap => {
                const c0 = l_lo * r_lo;
                const c1 = l_lo * r_hi;
                const c2 = l_hi * r_lo;
                const c3 = l_hi * r_hi;
                has_nsw = (@min(@min(c0, c1), @min(c2, c3)) >= s_min) and
                    (@max(@max(c0, c1), @max(c2, c3)) <= s_max);
            },
            else => {},
        }
    } else if (!lhs_r.flags().is_signed and !rhs_r.flags().is_signed) {
        const l_lo: u128 = lhs_r.min_bits;
        const l_hi: u128 = lhs_r.max_bits;
        const r_hi: u128 = rhs_r.max_bits;
        const u_max: u128 = if (bits == 64)
            std.math.maxInt(u64)
        else
            (@as(u128, 1) << @intCast(bits)) - 1;
        switch (op_kind) {
            .add_wrap => has_nuw = (l_hi + r_hi <= u_max),
            .sub_wrap => has_nuw = (l_lo >= r_hi),
            .mul_wrap => has_nuw = (l_hi * r_hi <= u_max),
            else => {},
        }
    }
    return .{ .has_nsw = has_nsw, .has_nuw = has_nuw };
}

/// Resolves MVS `!alias.scope` and `!noalias` metadata IDs for `root_param_local`.
fn lookupMvsScopeForLocal(
    state: *const BodyEmitState,
    root_param_local: u32,
) struct { scope_md: u32, noalias_md: u32 } {
    if (root_param_local == 0) return .{ .scope_md = 0, .noalias_md = 0 };
    for (state.mvs_scopes.items) |entry| {
        if (entry.local_idx == root_param_local) {
            return .{ .scope_md = entry.scope_list_md, .noalias_md = entry.noalias_list_md };
        }
    }
    return .{ .scope_md = 0, .noalias_md = 0 };
}

/// Appends optional `!alias.scope`, `!noalias`, `!llvm.access.group`, and `!dbg` suffixes to `cur_buf`.
fn appendMemMetadataSuffix(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    scope_md: u32,
    noalias_md: u32,
    access_group_md: u32,
    range_md: ?u32,
) !void {
    if (range_md) |r_md| {
        if (emitter.di_empty_tuple_md == 0) {
            emitter.di_empty_tuple_md = try emitter.addMetadataNode("!{}");
        }
        try state.print(", !range !{d}, !noundef !{d}", .{ r_md, emitter.di_empty_tuple_md });
    }
    if (scope_md != 0) try state.print(", !alias.scope !{d}", .{scope_md});
    if (noalias_md != 0) try state.print(", !noalias !{d}", .{noalias_md});
    if (access_group_md != 0) try state.print(", !llvm.access.group !{d}", .{access_group_md});
    if (state.active_dbg_loc_md != 0) try state.print(", !dbg !{d}", .{state.active_dbg_loc_md});
    try state.writeAll("\n");
}

/// Loads a CoreX SSA value of `raw_ty` from `ptr_str` (`bool` loaded as `i8` + `& 1` + `trunc to i1`).
fn emitLoadValueFromPtr(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    raw_ty: TypeId,
    ptr_str: []const u8,
    align_bytes: u32,
    maybe_range: ?ProvenValueRange,
    scope_md: u32,
    noalias_md: u32,
    access_group_md: u32,
) ![]u8 {
    const ty = try unwrapTransparentType(emitter, raw_ty);
    const eff_align = @max(align_bytes, 1);
    if (ty == .bool_ty) {
        const tmp_id = state.nextTmp();
        try state.print("  %_bld_{d} = load i8, ptr {s}, align {d}", .{ tmp_id, ptr_str, eff_align });
        try appendMemMetadataSuffix(emitter, state, scope_md, noalias_md, access_group_md, null);
        try state.print(
            "  %_band_{d} = and i8 %_bld_{d}, 1\n" ++
                "  %_bval_{d} = trunc i8 %_band_{d} to i1\n",
            .{ tmp_id, tmp_id, tmp_id, tmp_id },
        );
        return std.fmt.allocPrint(emitter.allocator, "%_bval_{d}", .{tmp_id});
    }

    const val_ty = try formatLlvmValueType(emitter, ty);
    defer emitter.allocator.free(val_ty);
    var range_md: ?u32 = null;
    if (maybe_range) |prov_r| {
        if (resolveIntegerInfo(emitter, ty)) |int_info| {
            if (int_info.bits <= 64 and prov_r.bit_width == int_info.bits) {
                range_md = try getOrInternValidRangeMd(emitter, prov_r);
            }
        }
    }
    const tmp_id = state.nextTmp();
    try state.print("  %_ld_{d} = load {s}, ptr {s}, align {d}", .{ tmp_id, val_ty, ptr_str, eff_align });
    try appendMemMetadataSuffix(emitter, state, scope_md, noalias_md, access_group_md, range_md);
    return std.fmt.allocPrint(emitter.allocator, "%_ld_{d}", .{tmp_id});
}

/// Stores a CoreX SSA value `val_str` of `raw_ty` into `ptr_str` (`bool` zero-extended to `i8`).
fn emitStoreValueToPtr(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    raw_ty: TypeId,
    val_str: []const u8,
    ptr_str: []const u8,
    align_bytes: u32,
    scope_md: u32,
    noalias_md: u32,
    access_group_md: u32,
) !void {
    const ty = try unwrapTransparentType(emitter, raw_ty);
    if (try isZeroSizedType(emitter, ty)) return;
    const eff_align = @max(align_bytes, 1);
    if (ty == .bool_ty) {
        const tmp_id = state.nextTmp();
        try state.print("  %_bst_{d} = zext i1 {s} to i8\n", .{ tmp_id, val_str });
        try state.print("  store i8 %_bst_{d}, ptr {s}, align {d}", .{ tmp_id, ptr_str, eff_align });
        try appendMemMetadataSuffix(emitter, state, scope_md, noalias_md, access_group_md, null);
        return;
    }
    const val_ty = try formatLlvmValueType(emitter, ty);
    defer emitter.allocator.free(val_ty);
    try state.print("  store {s} {s}, ptr {s}, align {d}", .{ val_ty, val_str, ptr_str, eff_align });
    try appendMemMetadataSuffix(emitter, state, scope_md, noalias_md, access_group_md, null);
}

/// Resolves the final projected `TypeId` of `place_id` in `body` without emitting IR.
fn resolvePlaceResultType(
    emitter: *LlvmModuleEmitter,
    body: *const MirBody,
    place_id: PlaceId,
) TypeId {
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
                } else if (node.tag == .union_ty) {
                    cur_ty = resolveUnionFieldType(emitter, cur_ty, proj.payload);
                } else if (emitter.resolver.getFieldByDeclOrdinal(cur_ty, proj.payload) catch null) |fld| {
                    cur_ty = emitter.input.pool.unwrapUnderlyingType(fld.field_ty);
                }
            },
            .index => {
                active_downcast = null;
                cur_ty = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
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

/// Emits dynamic `#soa [S]` column byte-offset computation for `elem_struct_ty` column `field_ord`.
fn emitDynamicSoaColByteOffset(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    elem_struct_ty: TypeId,
    field_ord: u32,
    len_ssa: []const u8,
) !struct { off_ssa: []u8, col_align_bytes: u32 } {
    const ptr_int = ptrIntType(emitter);
    const lay = try emitter.resolver.resolveType(elem_struct_ty);
    const simd_log2 = emitter.target_layout.simd_align_log2;

    var cur_ssa = try emitter.allocator.dupe(u8, "0");
    errdefer emitter.allocator.free(cur_ssa);
    var final_align: u32 = @as(u32, 1) << @intCast(simd_log2);

    var ord_i: u32 = 0;
    while (ord_i <= field_ord and ord_i < lay.aux_len) : (ord_i += 1) {
        const fld = emitter.resolver.fields_by_decl.items[lay.aux_start + ord_i];
        const col_align: u64 = @as(u64, 1) << @intCast(@max(fld.align_log2, simd_log2));
        const aligned_ssa = if (ord_i == 0)
            try emitter.allocator.dupe(u8, "0")
        else blk: {
            const t_id = state.nextTmp();
            try state.print(
                "  %_soa_add_{d} = add {s} {s}, {d}\n" ++
                    "  %_soa_al_{d} = and {s} %_soa_add_{d}, {d}\n",
                .{
                    t_id,
                    ptr_int,
                    cur_ssa,
                    col_align - 1,
                    t_id,
                    ptr_int,
                    t_id,
                    @as(i64, -@as(i64, @intCast(col_align))),
                },
            );
            break :blk try std.fmt.allocPrint(emitter.allocator, "%_soa_al_{d}", .{t_id});
        };
        if (ord_i == field_ord) {
            emitter.allocator.free(cur_ssa);
            final_align = @intCast(col_align);
            return .{ .off_ssa = aligned_ssa, .col_align_bytes = final_align };
        }
        defer emitter.allocator.free(aligned_ssa);
        const t_id = state.nextTmp();
        try state.print(
            "  %_soa_mul_{d} = mul {s} {s}, {d}\n" ++
                "  %_soa_nx_{d} = add {s} {s}, %_soa_mul_{d}\n",
            .{ t_id, ptr_int, len_ssa, fld.size_bytes, t_id, ptr_int, aligned_ssa, t_id },
        );
        emitter.allocator.free(cur_ssa);
        cur_ssa = try std.fmt.allocPrint(emitter.allocator, "%_soa_nx_{d}", .{t_id});
    }
    return .{ .off_ssa = cur_ssa, .col_align_bytes = final_align };
}

/// Lowers `place_id` to an addressable `ptr` operand or compile-time array length (`[CRITICAL-03]`).
fn lowerPlaceLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body: *const MirBody,
    place_id: PlaceId,
) !PlaceLoweringResult {
    const ptr_int = ptrIntType(emitter);
    const base_local = body.places.items[place_id.asInt()].base;
    const base_decl = body.locals.items[base_local];
    var cur_ty = try unwrapTransparentType(emitter, base_decl.type_id);
    var cur_align: u32 = if (base_local < state.local_aligns.len) state.local_aligns[base_local] else 1;

    const is_param_local = base_local >= 1 and base_local <= body.param_count;
    const is_direct_mvs_param = is_param_local and
        (base_decl.mode() == .inout_mode or base_decl.mode() == .set_mode);
    var active_mvs_param: u32 = if (is_direct_mvs_param) base_local else 0;
    var can_enter_param_ptr: bool = is_param_local and !is_direct_mvs_param;

    var cur_ptr = if (base_local < state.local_ptrs.len and state.local_ptrs[base_local].len > 0)
        try emitter.allocator.dupe(u8, state.local_ptrs[base_local])
    else
        try std.fmt.allocPrint(
            emitter.allocator,
            "inttoptr ({s} {d} to ptr)",
            .{ ptr_int, @max(cur_align, 1) },
        );
    errdefer emitter.allocator.free(cur_ptr);

    var active_downcast: ?u32 = null;
    var pending_soa: ?PendingSoaCol = null;
    defer if (pending_soa) |pend| {
        emitter.allocator.free(pend.col_ptr);
        emitter.allocator.free(pend.slice_base_ptr);
    };

    for (body.getPlaceProjections(place_id)) |proj| {
        if (pending_soa) |pend| {
            pending_soa = null;
            defer emitter.allocator.free(pend.col_ptr);
            defer emitter.allocator.free(pend.slice_base_ptr);
            if (proj.kind == .index) {
                const elem_lay = try emitter.resolver.resolveType(pend.field_ty);
                const idx_ssa = try coerceIndexToPtrInt(emitter, state, body, proj.payload);
                defer emitter.allocator.free(idx_ssa);
                const t_id = state.nextTmp();
                try state.print(
                    "  %_sidx_b_{d} = mul {s} {s}, {d}\n" ++
                        "  %_sidx_p_{d} = getelementptr inbounds i8, ptr {s}, {s} %_sidx_b_{d}\n",
                    .{ t_id, ptr_int, idx_ssa, elem_lay.stride_bytes, t_id, pend.col_ptr, ptr_int, t_id },
                );
                emitter.allocator.free(cur_ptr);
                cur_ptr = try std.fmt.allocPrint(emitter.allocator, "%_sidx_p_{d}", .{t_id});
                cur_ty = pend.field_ty;
                cur_align = @min(
                    @max(pend.col_align, 1),
                    effectiveOffsetAlign(elem_lay.stride_bytes, elem_lay.alignBytes()),
                );
                continue;
            } else if (proj.kind == .slice_len) {
                if (pend.is_fixed) {
                    emitter.allocator.free(cur_ptr);
                    return .{ .const_len = .{ .elem_count = pend.fixed_cap } };
                }
                const t_id = state.nextTmp();
                try state.print(
                    "  %_slen_p_{d} = getelementptr inbounds {{ ptr, {s} }}, ptr {s}, i32 0, i32 1\n",
                    .{ t_id, ptr_int, pend.slice_base_ptr },
                );
                emitter.allocator.free(cur_ptr);
                return .{
                    .addr_val = .{
                        .ptr_str = try std.fmt.allocPrint(emitter.allocator, "%_slen_p_{d}", .{t_id}),
                        .pointee_ty = .usize_ty,
                        .align_bytes = @min(@max(cur_align, 1), emitter.cfg.target.ptrBytes()),
                        .root_param_local = active_mvs_param,
                    },
                };
            }
        }

        const node = emitter.input.pool.getNode(cur_ty);
        switch (proj.kind) {
            .deref => {
                active_downcast = null;
                const pointee_ty = try unwrapTransparentType(emitter, TypeId.fromInt(node.lhs));
                const p_lay = try emitter.resolver.resolveType(pointee_ty);
                const ptr_load_align = @min(@max(cur_align, 1), @max(emitter.cfg.target.ptrBytes(), 1));
                const t_id = state.nextTmp();
                try state.print(
                    "  %_deref_{d} = load ptr, ptr {s}, align {d}\n",
                    .{ t_id, cur_ptr, ptr_load_align },
                );
                emitter.allocator.free(cur_ptr);
                cur_ptr = try std.fmt.allocPrint(emitter.allocator, "%_deref_{d}", .{t_id});
                cur_ty = pointee_ty;
                if (node.tag == .raw_ptr_ty) {
                    cur_align = 1;
                    active_mvs_param = 0;
                    can_enter_param_ptr = false;
                } else {
                    cur_align = p_lay.alignBytes();
                    if (can_enter_param_ptr) {
                        active_mvs_param = base_local;
                        can_enter_param_ptr = false;
                    } else {
                        active_mvs_param = 0;
                    }
                }
            },
            .downcast => {
                active_downcast = proj.payload;
            },
            .field => {
                if (active_downcast) |tag_ord| {
                    active_downcast = null;
                    const sum_detail_opt = try emitter.resolver.getSumDetail(cur_ty);
                    const pay_off: u64 = if (sum_detail_opt) |sd| sd.payload_offset else 0;
                    const var_pay_ty = try unwrapTransparentType(
                        emitter,
                        resolveEnumVariantPayloadType(emitter, cur_ty, tag_ord),
                    );
                    var total_off: u64 = pay_off;
                    var final_ty = var_pay_ty;
                    if (proj.payload > 0) {
                        if (try emitter.resolver.getFieldByDeclOrdinal(var_pay_ty, proj.payload)) |sub_fld| {
                            total_off += sub_fld.byte_offset;
                            final_ty = try unwrapTransparentType(emitter, sub_fld.field_ty);
                        }
                    }
                    const f_lay = try emitter.resolver.resolveType(final_ty);
                    if (total_off > 0) {
                        const t_id = state.nextTmp();
                        try state.print(
                            "  %_vpay_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                            .{ t_id, cur_ptr, ptr_int, total_off },
                        );
                        emitter.allocator.free(cur_ptr);
                        cur_ptr = try std.fmt.allocPrint(emitter.allocator, "%_vpay_{d}", .{t_id});
                    }
                    cur_ty = final_ty;
                    cur_align = @min(@max(cur_align, 1), effectiveOffsetAlign(total_off, f_lay.alignBytes()));
                } else if (node.tag == .union_ty) {
                    const fld_ty = try unwrapTransparentType(
                        emitter,
                        resolveUnionFieldType(emitter, cur_ty, proj.payload),
                    );
                    const f_lay = try emitter.resolver.resolveType(fld_ty);
                    cur_ty = fld_ty;
                    cur_align = @min(@max(cur_align, 1), f_lay.alignBytes());
                } else if (try emitter.resolver.getFieldByDeclOrdinal(cur_ty, proj.payload)) |fld| {
                    const parent_lay = try emitter.resolver.resolveType(cur_ty);
                    const fld_ty = try unwrapTransparentType(emitter, fld.field_ty);
                    if (fld.byte_offset > 0) {
                        const t_id = state.nextTmp();
                        try state.print(
                            "  %_fld_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                            .{ t_id, cur_ptr, ptr_int, fld.byte_offset },
                        );
                        emitter.allocator.free(cur_ptr);
                        cur_ptr = try std.fmt.allocPrint(emitter.allocator, "%_fld_{d}", .{t_id});
                    }
                    cur_ty = fld_ty;
                    if (parent_lay.reprFlags().is_packed) {
                        cur_align = 1;
                    } else {
                        const fld_nat_align = @as(u32, 1) << @intCast(fld.align_log2);
                        cur_align = @min(
                            @min(@max(cur_align, 1), parent_lay.alignBytes()),
                            effectiveOffsetAlign(fld.byte_offset, fld_nat_align),
                        );
                    }
                }
            },
            .index => {
                active_downcast = null;
                const elem_ty = try unwrapTransparentType(emitter, TypeId.fromInt(node.lhs));
                const elem_lay = try emitter.resolver.resolveType(elem_ty);
                const idx_ssa = try coerceIndexToPtrInt(emitter, state, body, proj.payload);
                defer emitter.allocator.free(idx_ssa);
                const t_id = state.nextTmp();
                if (node.tag == .slice_ty) {
                    const hdr_align = @min(@max(cur_align, 1), emitter.cfg.target.ptrBytes());
                    try state.print(
                        "  %_sl_dp_{d} = load ptr, ptr {s}, align {d}\n" ++
                            "  %_sl_bo_{d} = mul {s} {s}, {d}\n" ++
                            "  %_sl_ep_{d} = getelementptr inbounds i8, ptr %_sl_dp_{d}, {s} %_sl_bo_{d}\n",
                        .{
                            t_id,
                            cur_ptr,
                            hdr_align,
                            t_id,
                            ptr_int,
                            idx_ssa,
                            elem_lay.stride_bytes,
                            t_id,
                            t_id,
                            ptr_int,
                            t_id,
                        },
                    );
                    emitter.allocator.free(cur_ptr);
                    cur_ptr = try std.fmt.allocPrint(emitter.allocator, "%_sl_ep_{d}", .{t_id});
                    cur_align = @min(
                        elem_lay.alignBytes(),
                        effectiveOffsetAlign(elem_lay.stride_bytes, elem_lay.alignBytes()),
                    );
                    if (can_enter_param_ptr) {
                        active_mvs_param = base_local;
                        can_enter_param_ptr = false;
                    }
                } else {
                    try state.print(
                        "  %_ar_bo_{d} = mul {s} {s}, {d}\n" ++
                            "  %_ar_ep_{d} = getelementptr inbounds i8, ptr {s}, {s} %_ar_bo_{d}\n",
                        .{ t_id, ptr_int, idx_ssa, elem_lay.stride_bytes, t_id, cur_ptr, ptr_int, t_id },
                    );
                    emitter.allocator.free(cur_ptr);
                    cur_ptr = try std.fmt.allocPrint(emitter.allocator, "%_ar_ep_{d}", .{t_id});
                    cur_align = @min(
                        @max(cur_align, 1),
                        effectiveOffsetAlign(elem_lay.stride_bytes, elem_lay.alignBytes()),
                    );
                }
                cur_ty = elem_ty;
            },
            .soa_elem => {
                active_downcast = null;
                const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const fld = (try emitter.resolver.getFieldByDeclOrdinal(elem_struct, proj.payload)).?;
                const fld_ty = try unwrapTransparentType(emitter, fld.field_ty);
                if (node.tag == .soa_array_ty) {
                    const cap: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                    const col_info = emitter.resolver.getSoaColumnOffset(elem_struct, proj.payload, cap).?;
                    const nat_col_align = @as(u32, 1) << @intCast(col_info.col_align_log2);
                    const t_id = state.nextTmp();
                    try state.print(
                        "  %_scol_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                        .{ t_id, cur_ptr, ptr_int, col_info.byte_offset },
                    );
                    pending_soa = .{
                        .col_ptr = try std.fmt.allocPrint(emitter.allocator, "%_scol_{d}", .{t_id}),
                        .field_ty = fld_ty,
                        .col_align = @min(
                            @max(cur_align, 1),
                            effectiveOffsetAlign(col_info.byte_offset, nat_col_align),
                        ),
                        .is_fixed = true,
                        .fixed_cap = cap,
                        .slice_base_ptr = try emitter.allocator.dupe(u8, cur_ptr),
                    };
                } else {
                    const hdr_align = @min(@max(cur_align, 1), emitter.cfg.target.ptrBytes());
                    const t_id = state.nextTmp();
                    try state.print(
                        "  %_ssl_dp_{d} = load ptr, ptr {s}, align {d}\n" ++
                            "  %_ssl_lp_{d} = getelementptr inbounds {{ ptr, {s} }}, ptr {s}, i32 0, i32 1\n" ++
                            "  %_ssl_ln_{d} = load {s}, ptr %_ssl_lp_{d}, align {d}\n",
                        .{
                            t_id,
                            cur_ptr,
                            hdr_align,
                            t_id,
                            ptr_int,
                            cur_ptr,
                            t_id,
                            ptr_int,
                            t_id,
                            hdr_align,
                        },
                    );
                    if (can_enter_param_ptr) {
                        active_mvs_param = base_local;
                        can_enter_param_ptr = false;
                    }
                    const len_s = try std.fmt.allocPrint(emitter.allocator, "%_ssl_ln_{d}", .{t_id});
                    defer emitter.allocator.free(len_s);
                    const dyn_col = try emitDynamicSoaColByteOffset(
                        emitter,
                        state,
                        elem_struct,
                        proj.payload,
                        len_s,
                    );
                    defer emitter.allocator.free(dyn_col.off_ssa);
                    try state.print(
                        "  %_scol_{d} = getelementptr inbounds i8, ptr %_ssl_dp_{d}, {s} {s}\n",
                        .{ t_id, t_id, ptr_int, dyn_col.off_ssa },
                    );
                    pending_soa = .{
                        .col_ptr = try std.fmt.allocPrint(emitter.allocator, "%_scol_{d}", .{t_id}),
                        .field_ty = fld_ty,
                        .col_align = dyn_col.col_align_bytes,
                        .is_fixed = false,
                        .fixed_cap = 0,
                        .slice_base_ptr = try emitter.allocator.dupe(u8, cur_ptr),
                    };
                }
            },
            .slice_len => {
                if (cur_ty != .str_ty and
                    (node.tag == .array_ty or node.tag == .soa_array_ty))
                {
                    const arr_cap: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                    emitter.allocator.free(cur_ptr);
                    return .{ .const_len = .{ .elem_count = arr_cap } };
                }
                const t_id = state.nextTmp();
                try state.print(
                    "  %_len_p_{d} = getelementptr inbounds {{ ptr, {s} }}, ptr {s}, i32 0, i32 1\n",
                    .{ t_id, ptr_int, cur_ptr },
                );
                emitter.allocator.free(cur_ptr);
                return .{
                    .addr_val = .{
                        .ptr_str = try std.fmt.allocPrint(emitter.allocator, "%_len_p_{d}", .{t_id}),
                        .pointee_ty = .usize_ty,
                        .align_bytes = @min(@max(cur_align, 1), emitter.cfg.target.ptrBytes()),
                        .root_param_local = active_mvs_param,
                    },
                };
            },
        }
    }

    return .{
        .addr_val = .{
            .ptr_str = cur_ptr,
            .pointee_ty = cur_ty,
            .align_bytes = @max(cur_align, 1),
            .root_param_local = active_mvs_param,
        },
    };
}

/// Converts an index `MirValueId` (`idx_raw`) to pointer-width integer (`i32` on `wasm32`, `i64` on 64-bit).
fn coerceIndexToPtrInt(
    emitter: *const LlvmModuleEmitter,
    state: *BodyEmitState,
    body: *const MirBody,
    idx_raw: u32,
) ![]u8 {
    const ptr_bits: u16 = @as(u16, emitter.cfg.target.ptrBytes()) * 8;
    const idx_ty = body.getInst(MirValueId.fromInt(idx_raw)).type_id;
    const idx_info = resolveIntegerInfo(emitter, idx_ty) orelse IntScalarInfo{
        .bits = ptr_bits,
        .is_signed = false,
    };
    if (idx_info.bits == ptr_bits) {
        return std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{idx_raw});
    }
    const tmp_id = state.nextTmp();
    const cast_op = if (idx_info.bits < ptr_bits)
        (if (idx_info.is_signed) "sext" else "zext")
    else
        "trunc";
    try state.print(
        "  %_idx_c_{d} = {s} i{d} %_v_{d} to i{d}\n",
        .{ tmp_id, cast_op, idx_info.bits, idx_raw, ptr_bits },
    );
    return std.fmt.allocPrint(emitter.allocator, "%_idx_c_{d}", .{tmp_id});
}

// ------------------ MIR Instruction Lowering ------------------

/// Emits a conditional trap branch (`if (cond_i1) _cx_rt_trap(reason)`) and updates `state.cur_label`.
fn emitInlineTrapIfTrue(
    emitter: *const LlvmModuleEmitter,
    state: *BodyEmitState,
    cond_ssa: []const u8,
    reason_code: u32,
) !void {
    const tmp_id = state.nextTmp();
    try state.print(
        "  br i1 {s}, label %_trap_{d}, label %_ok_{d}\n" ++
            "_trap_{d}:\n" ++
            "  call void @_cx_rt_trap(i32 {d})\n" ++
            "  unreachable\n" ++
            "_ok_{d}:\n",
        .{ cond_ssa, tmp_id, tmp_id, tmp_id, reason_code, tmp_id },
    );
    state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_ok_{d}", .{tmp_id}));
}

/// Terminates a `noreturn` intrinsic call and opens a dead continuation block for any trailing MIR ops.
fn emitUnreachableAndDeadBlock(
    emitter: *const LlvmModuleEmitter,
    state: *BodyEmitState,
    dst_raw: u32,
) !void {
    const tmp_id = state.nextTmp();
    try state.print(
        "  unreachable\n_dead_{d}:\n  %_v_{d} = add i8 0, 0\n",
        .{ tmp_id, dst_raw },
    );
    state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_dead_{d}", .{tmp_id}));
}

/// Formats an IEEE-754 value as an exact 16-hex-digit LLVM IR floating-point constant (`0x…`).
fn formatLlvmHexFloatLiteral(allocator: std.mem.Allocator, is_f32: bool, raw_f64: f64) ![]u8 {
    if (is_f32) {
        const f32_val: f32 = @floatCast(raw_f64);
        if (std.math.isNan(f32_val)) {
            return allocator.dupe(u8, "0x7FF8000000000000");
        }
        const bits: u64 = @bitCast(@as(f64, @floatCast(f32_val)));
        return std.fmt.allocPrint(allocator, "0x{X:0>16}", .{bits});
    }
    if (std.math.isNan(raw_f64)) {
        return allocator.dupe(u8, "0x7FF8000000000000");
    }
    const bits: u64 = @bitCast(raw_f64);
    return std.fmt.allocPrint(allocator, "0x{X:0>16}", .{bits});
}

/// Extracts `(ptr_ssa, len_ssa)` (where `len_ssa` has type `ptrIntType`) from `str`, `[u8]`, `&[u8]`, or `[u8; N]`.
fn emitExtractByteSpanLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body: *const MirBody,
    arg_val: MirValueId,
) !struct { ptr_ssa: []u8, len_ssa: []u8 } {
    const ptr_int = ptrIntType(emitter);
    const arg_raw = arg_val.asInt();
    const arg_ty = try unwrapTransparentType(emitter, body.getInst(arg_val).type_id);
    if (arg_ty == .str_ty) {
        const tmp_id = state.nextTmp();
        try state.print(
            "  %_bsp_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 0\n" ++
                "  %_bsl_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 1\n",
            .{ tmp_id, ptr_int, arg_raw, tmp_id, ptr_int, arg_raw },
        );
        return .{
            .ptr_ssa = try std.fmt.allocPrint(emitter.allocator, "%_bsp_{d}", .{tmp_id}),
            .len_ssa = try std.fmt.allocPrint(emitter.allocator, "%_bsl_{d}", .{tmp_id}),
        };
    }
    const node = emitter.input.pool.getNode(arg_ty);
    if (node.tag == .slice_ty) {
        const tmp_id = state.nextTmp();
        try state.print(
            "  %_bsp_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 0\n" ++
                "  %_bsl_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 1\n",
            .{ tmp_id, ptr_int, arg_raw, tmp_id, ptr_int, arg_raw },
        );
        return .{
            .ptr_ssa = try std.fmt.allocPrint(emitter.allocator, "%_bsp_{d}", .{tmp_id}),
            .len_ssa = try std.fmt.allocPrint(emitter.allocator, "%_bsl_{d}", .{tmp_id}),
        };
    }
    if (node.tag == .array_ty) {
        const cap: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
        const lay = try emitter.resolver.resolveType(arg_ty);
        const scratch = try state.allocEntryBytes(lay.size_bytes, lay.alignBytes());
        const val_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{arg_raw});
        defer emitter.allocator.free(val_ssa);
        try emitStoreValueToPtr(emitter, state, arg_ty, val_ssa, scratch, lay.alignBytes(), 0, 0, 0);
        return .{
            .ptr_ssa = scratch,
            .len_ssa = try std.fmt.allocPrint(emitter.allocator, "{d}", .{cap}),
        };
    }
    if (node.tag == .ref_ty or node.tag == .mut_ref_ty or node.tag == .raw_ptr_ty) {
        const pointee = try unwrapTransparentType(emitter, TypeId.fromInt(node.lhs));
        if (pointee == .str_ty or emitter.input.pool.getNode(pointee).tag == .slice_ty) {
            const tmp_id = state.nextTmp();
            try state.print(
                "  %_bsfat_{d} = load {{ ptr, {s} }}, ptr %_v_{d}, align {d}\n" ++
                    "  %_bsp_{d} = extractvalue {{ ptr, {s} }} %_bsfat_{d}, 0\n" ++
                    "  %_bsl_{d} = extractvalue {{ ptr, {s} }} %_bsfat_{d}, 1\n",
                .{
                    tmp_id,
                    ptr_int,
                    arg_raw,
                    emitter.cfg.target.ptrBytes(),
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                },
            );
            return .{
                .ptr_ssa = try std.fmt.allocPrint(emitter.allocator, "%_bsp_{d}", .{tmp_id}),
                .len_ssa = try std.fmt.allocPrint(emitter.allocator, "%_bsl_{d}", .{tmp_id}),
            };
        }
        const p_node = emitter.input.pool.getNode(pointee);
        if (p_node.tag == .array_ty) {
            const cap: u64 = p_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            return .{
                .ptr_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{arg_raw}),
                .len_ssa = try std.fmt.allocPrint(emitter.allocator, "{d}", .{cap}),
            };
        }
    }
    return .{
        .ptr_ssa = try std.fmt.allocPrint(emitter.allocator, "inttoptr ({s} 1 to ptr)", .{ptr_int}),
        .len_ssa = try emitter.allocator.dupe(u8, "0"),
    };
}

/// Widens or sign/zero-extends an integer SSA value `%_v_<val_raw>` (`val_ty`) to `i128`.
fn emitExtendIntToI128(
    emitter: *const LlvmModuleEmitter,
    state: *BodyEmitState,
    val_raw: u32,
    val_ty: TypeId,
    is_forced_unsigned: bool,
) ![]u8 {
    const unwrapped = emitter.input.pool.unwrapUnderlyingType(val_ty);
    if (unwrapped == .bool_ty) {
        const tmp_id = state.nextTmp();
        try state.print("  %_w128_{d} = zext i1 %_v_{d} to i128\n", .{ tmp_id, val_raw });
        return std.fmt.allocPrint(emitter.allocator, "%_w128_{d}", .{tmp_id});
    }
    const info = resolveIntegerInfo(emitter, unwrapped) orelse
        return emitter.allocator.dupe(u8, "0");
    if (info.bits == 128) {
        return std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{val_raw});
    }
    const tmp_id = state.nextTmp();
    const op_s = if (!is_forced_unsigned and info.is_signed) "sext" else "zext";
    try state.print(
        "  %_w128_{d} = {s} i{d} %_v_{d} to i128\n",
        .{ tmp_id, op_s, info.bits, val_raw },
    );
    return std.fmt.allocPrint(emitter.allocator, "%_w128_{d}", .{tmp_id});
}

/// Appends an LLVM byte-array literal `c"…"` (escaping non-printable bytes as `\XX`) to `buf`.
fn appendByteStringLiteralToBuf(
    allocator: std.mem.Allocator,
    buf: *std.ArrayListUnmanaged(u8),
    bytes: []const u8,
) !void {
    try buf.appendSlice(allocator, "c\"");
    for (bytes) |byte_val| {
        if (byte_val >= 0x20 and byte_val <= 0x7E and byte_val != '"' and byte_val != '\\') {
            try buf.append(allocator, byte_val);
        } else {
            var esc_buf: [3]u8 = undefined;
            const esc = std.fmt.bufPrint(&esc_buf, "\\{X:0>2}", .{byte_val}) catch unreachable;
            try buf.appendSlice(allocator, esc);
        }
    }
    try buf.append(allocator, '"');
}

/// Lazily emits `@_cx_rt_fmt_u128` into `emitter.synth_globals` for `128`-bit `str_concat` formatting.
fn ensureFmtU128Helper(emitter: *LlvmModuleEmitter) !void {
    if (emitter.has_fmt_u128_helper) return;
    emitter.has_fmt_u128_helper = true;
    const fn_ir = try std.fmt.allocPrint(
        emitter.allocator,
        "define internal i32 @_cx_rt_fmt_u128(ptr %buf, i128 %val) {s} {{\n" ++
            "entry:\n" ++
            "  %rev = alloca [48 x i8], align 1\n" ++
            "  %isz = icmp eq i128 %val, 0\n" ++
            "  br i1 %isz, label %zero, label %loop\n" ++
            "zero:\n" ++
            "  store i8 48, ptr %buf, align 1\n" ++
            "  ret i32 1\n" ++
            "loop:\n" ++
            "  %cur = phi i128 [ %val, %entry ], [ %nxt, %loop ]\n" ++
            "  %cnt = phi i32 [ 0, %entry ], [ %cnt_nx, %loop ]\n" ++
            "  %rem = urem i128 %cur, 10\n" ++
            "  %nxt = udiv i128 %cur, 10\n" ++
            "  %rem8 = trunc i128 %rem to i8\n" ++
            "  %dig = add i8 %rem8, 48\n" ++
            "  %rp = getelementptr inbounds [48 x i8], ptr %rev, i32 0, i32 %cnt\n" ++
            "  store i8 %dig, ptr %rp, align 1\n" ++
            "  %cnt_nx = add i32 %cnt, 1\n" ++
            "  %has_more = icmp ne i128 %nxt, 0\n" ++
            "  br i1 %has_more, label %loop, label %copy\n" ++
            "copy:\n" ++
            "  %idx = phi i32 [ 0, %loop ], [ %idx_nx, %copy ]\n" ++
            "  %ri_sub = sub i32 %cnt_nx, 1\n" ++
            "  %ri = sub i32 %ri_sub, %idx\n" ++
            "  %sp = getelementptr inbounds [48 x i8], ptr %rev, i32 0, i32 %ri\n" ++
            "  %ch = load i8, ptr %sp, align 1\n" ++
            "  %dp = getelementptr inbounds i8, ptr %buf, i32 %idx\n" ++
            "  store i8 %ch, ptr %dp, align 1\n" ++
            "  %idx_nx = add i32 %idx, 1\n" ++
            "  %more_cp = icmp slt i32 %idx_nx, %cnt_nx\n" ++
            "  br i1 %more_cp, label %copy, label %done\n" ++
            "done:\n" ++
            "  ret i32 %cnt_nx\n" ++
            "}}\n\n",
        .{fnUnwindAttrs(emitter)},
    );
    defer emitter.allocator.free(fn_ir);
    try emitter.synth_globals.appendSlice(emitter.allocator, fn_ir);
}

/// Lazily emits `@_cx_rt_fmt_i128` into `emitter.synth_globals` for signed `128`-bit `str_concat` formatting.
fn ensureFmtI128Helper(emitter: *LlvmModuleEmitter) !void {
    try ensureFmtU128Helper(emitter);
    if (emitter.has_fmt_i128_helper) return;
    emitter.has_fmt_i128_helper = true;
    const fn_ir = try std.fmt.allocPrint(
        emitter.allocator,
        "define internal i32 @_cx_rt_fmt_i128(ptr %buf, i128 %val) {s} {{\n" ++
            "entry:\n" ++
            "  %isneg = icmp slt i128 %val, 0\n" ++
            "  br i1 %isneg, label %neg, label %pos\n" ++
            "neg:\n" ++
            "  store i8 45, ptr %buf, align 1\n" ++
            "  %mag = sub i128 0, %val\n" ++
            "  %nbuf = getelementptr inbounds i8, ptr %buf, i32 1\n" ++
            "  %nlen = call i32 @_cx_rt_fmt_u128(ptr %nbuf, i128 %mag)\n" ++
            "  %tot = add i32 %nlen, 1\n" ++
            "  ret i32 %tot\n" ++
            "pos:\n" ++
            "  %plen = call i32 @_cx_rt_fmt_u128(ptr %buf, i128 %val)\n" ++
            "  ret i32 %plen\n" ++
            "}}\n\n",
        .{fnUnwindAttrs(emitter)},
    );
    defer emitter.allocator.free(fn_ir);
    try emitter.synth_globals.appendSlice(emitter.allocator, fn_ir);
}

/// Emits `&[T; N]` -> `[T]` / `&[T]` and `&[T]` <-> `[T]` pointer-slice coercions when applicable.
fn tryEmitSliceArrayPtrCoercionLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body: *const MirBody,
    dst_raw: u32,
    src_raw: u32,
    src_ty: TypeId,
    dst_ty: TypeId,
) !bool {
    if (src_ty.isPrimitiveOrSentinel() and src_ty != .str_ty) return false;
    if (dst_ty.isPrimitiveOrSentinel() and dst_ty != .str_ty) return false;

    const ptr_int = ptrIntType(emitter);
    const ptr_bytes = emitter.cfg.target.ptrBytes();
    const src_is_ptr_like = if (src_ty == .str_ty) false else blk: {
        const sn = emitter.input.pool.getNode(src_ty);
        break :blk sn.tag == .ref_ty or sn.tag == .mut_ref_ty or sn.tag == .raw_ptr_ty;
    };
    const dst_is_ptr_like = if (dst_ty == .str_ty) false else blk: {
        const dn = emitter.input.pool.getNode(dst_ty);
        break :blk dn.tag == .ref_ty or dn.tag == .mut_ref_ty or dn.tag == .raw_ptr_ty;
    };
    const dst_is_fat_slice = if (dst_ty == .str_ty) true else blk: {
        const dn = emitter.input.pool.getNode(dst_ty);
        break :blk dn.tag == .slice_ty or dn.tag == .soa_slice_ty;
    };
    const src_is_fat_slice = if (src_ty == .str_ty) true else blk: {
        const sn = emitter.input.pool.getNode(src_ty);
        break :blk sn.tag == .slice_ty or sn.tag == .soa_slice_ty;
    };

    if (src_is_ptr_like) {
        const src_pointee = try unwrapTransparentType(
            emitter,
            TypeId.fromInt(emitter.input.pool.getNode(src_ty).lhs),
        );
        if (src_pointee != .str_ty and !src_pointee.isPrimitiveOrSentinel()) {
            const sp_node = emitter.input.pool.getNode(src_pointee);
            if (sp_node.tag == .array_ty or sp_node.tag == .soa_array_ty) {
                const cap: u64 = sp_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                const elem_ty = try unwrapTransparentType(emitter, TypeId.fromInt(sp_node.lhs));
                const elem_lay = try emitter.resolver.resolveType(elem_ty);
                const data_ptr_s = if (cap == 0)
                    try std.fmt.allocPrint(
                        emitter.allocator,
                        "inttoptr ({s} {d} to ptr)",
                        .{ ptr_int, @max(elem_lay.alignBytes(), 1) },
                    )
                else
                    try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{src_raw});
                defer emitter.allocator.free(data_ptr_s);

                if (dst_is_fat_slice) {
                    const tmp_id = state.nextTmp();
                    try state.print(
                        "  %_sac0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr {s}, 0\n" ++
                            "  %_v_{d} = insertvalue {{ ptr, {s} }} %_sac0_{d}, {s} {d}, 1\n",
                        .{ tmp_id, ptr_int, data_ptr_s, dst_raw, ptr_int, tmp_id, ptr_int, cap },
                    );
                    return true;
                }
                if (dst_is_ptr_like) {
                    const dst_pointee = try unwrapTransparentType(
                        emitter,
                        TypeId.fromInt(emitter.input.pool.getNode(dst_ty).lhs),
                    );
                    const dp_is_slice = if (dst_pointee == .str_ty) true else if (dst_pointee.isPrimitiveOrSentinel()) false else sub: {
                        const dpn = emitter.input.pool.getNode(dst_pointee);
                        break :sub dpn.tag == .slice_ty or dpn.tag == .soa_slice_ty;
                    };
                    if (dp_is_slice) {
                        const fat_slot = try state.allocEntryBytes(2 * ptr_bytes, ptr_bytes);
                        defer emitter.allocator.free(fat_slot);
                        const tmp_id = state.nextTmp();
                        try state.print(
                            "  store ptr {s}, ptr {s}, align {d}\n" ++
                                "  %_sacp_{d} = getelementptr inbounds {{ ptr, {s} }}, ptr {s}, i32 0, i32 1\n" ++
                                "  store {s} {d}, ptr %_sacp_{d}, align {d}\n" ++
                                "  %_v_{d} = select i1 true, ptr {s}, ptr {s}\n",
                            .{
                                data_ptr_s,
                                fat_slot,
                                ptr_bytes,
                                tmp_id,
                                ptr_int,
                                fat_slot,
                                ptr_int,
                                cap,
                                tmp_id,
                                ptr_bytes,
                                dst_raw,
                                fat_slot,
                                fat_slot,
                            },
                        );
                        return true;
                    }
                }
            }
        }
        const sp_is_slice = if (src_pointee == .str_ty) true else if (src_pointee.isPrimitiveOrSentinel()) false else sub: {
            const spn = emitter.input.pool.getNode(src_pointee);
            break :sub spn.tag == .slice_ty or spn.tag == .soa_slice_ty;
        };
        if (sp_is_slice and dst_is_fat_slice) {
            try state.print(
                "  %_v_{d} = load {{ ptr, {s} }}, ptr %_v_{d}, align {d}\n",
                .{ dst_raw, ptr_int, src_raw, ptr_bytes },
            );
            return true;
        }
    }

    if (src_is_fat_slice and dst_is_ptr_like) {
        const dst_pointee = try unwrapTransparentType(
            emitter,
            TypeId.fromInt(emitter.input.pool.getNode(dst_ty).lhs),
        );
        const dp_is_slice = if (dst_pointee == .str_ty) true else if (dst_pointee.isPrimitiveOrSentinel()) false else sub: {
            const dpn = emitter.input.pool.getNode(dst_pointee);
            break :sub dpn.tag == .slice_ty or dpn.tag == .soa_slice_ty;
        };
        if (dp_is_slice) {
            const src_inst = body.getInst(MirValueId.fromInt(src_raw));
            if (src_inst.op == .const_scalar) {
                const c_val = body.consts.items[src_inst.operands.lhs];
                switch (c_val) {
                    .str_val, .bytes_val => |sym_id| {
                        const raw_bytes = emitter.input.interner.get(sym_id);
                        const ptr_expr = if (raw_bytes.len == 0)
                            try std.fmt.allocPrint(emitter.allocator, "inttoptr ({s} 1 to ptr)", .{ptr_int})
                        else
                            try std.fmt.allocPrint(emitter.allocator, "@_cx_str_bytes_{d}", .{sym_id.asInt()});
                        defer emitter.allocator.free(ptr_expr);
                        const sid = emitter.nextSynthGlobalId();
                        const hdr_line = try std.fmt.allocPrint(
                            emitter.allocator,
                            "@_cx_sref_{d} = private unnamed_addr constant {{ ptr, {s} }} " ++
                                "{{ ptr {s}, {s} {d} }}, align {d}\n",
                            .{ sid, ptr_int, ptr_expr, ptr_int, raw_bytes.len, ptr_bytes },
                        );
                        defer emitter.allocator.free(hdr_line);
                        try emitter.synth_globals.appendSlice(emitter.allocator, hdr_line);
                        try state.print(
                            "  %_v_{d} = select i1 true, ptr @_cx_sref_{d}, ptr @_cx_sref_{d}\n",
                            .{ dst_raw, sid, sid },
                        );
                        return true;
                    },
                    .raw_blob => |rb| {
                        try state.print(
                            "  %_v_{d} = select i1 true, ptr @_cx_blob_slice_{d}, ptr @_cx_blob_slice_{d}\n",
                            .{ dst_raw, rb.blob_id, rb.blob_id },
                        );
                        return true;
                    },
                    else => {},
                }
            }
            const fat_slot = try state.allocEntryBytes(2 * ptr_bytes, ptr_bytes);
            defer emitter.allocator.free(fat_slot);
            try state.print(
                "  store {{ ptr, {s} }} %_v_{d}, ptr {s}, align {d}\n" ++
                    "  %_v_{d} = select i1 true, ptr {s}, ptr {s}\n",
                .{ ptr_int, src_raw, fat_slot, ptr_bytes, dst_raw, fat_slot, fat_slot },
            );
            return true;
        }
    }

    return false;
}

/// Emits a single non-terminator `MirInst` inside `body_idx` (`Pass 1`).
fn emitMirInstLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body_idx: u32,
    body: *const MirBody,
    bb_idx: u32,
    val_id: MirValueId,
) !void {
    const dst_raw = val_id.asInt();
    const inst = body.getInst(val_id);
    if (inst.op == .block_param or inst.op.isGhost()) return;

    const access_grp = if (bb_idx < state.block_access_group.len) state.block_access_group[bb_idx] else 0;
    const ptr_int = ptrIntType(emitter);

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
            if (try isZeroSizedType(emitter, inst.type_id)) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const c_val = body.consts.items[inst.operands.lhs];
            const dst_ty = try unwrapTransparentType(emitter, inst.type_id);
            switch (c_val) {
                .unit_val => try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw}),
                .bool_val => |bv| try state.print(
                    "  %_v_{d} = or i1 false, {s}\n",
                    .{ dst_raw, if (bv) "true" else "false" },
                ),
                .char_val => |cv| try state.print("  %_v_{d} = add i32 0, {d}\n", .{ dst_raw, @as(u32, cv) }),
                .int_val => |iv| {
                    if (dst_ty == .bool_ty) {
                        try state.print(
                            "  %_v_{d} = or i1 false, {s}\n",
                            .{ dst_raw, if ((iv & 1) != 0) "true" else "false" },
                        );
                    } else if (resolveIntegerInfo(emitter, dst_ty)) |info| {
                        if (info.bits == 128) {
                            try state.print("  %_v_{d} = add i128 0, {d}\n", .{ dst_raw, iv });
                        } else {
                            const mask: u128 = (@as(u128, 1) << @intCast(info.bits)) - 1;
                            const u_bits: u128 = (@as(u128, @bitCast(iv))) & mask;
                            try state.print("  %_v_{d} = add i{d} 0, {d}\n", .{ dst_raw, info.bits, u_bits });
                        }
                    } else {
                        const ty_s = try formatLlvmValueType(emitter, dst_ty);
                        defer emitter.allocator.free(ty_s);
                        if (std.mem.eql(u8, ty_s, "ptr")) {
                            const addr_u: u64 = @truncate(@as(u128, @bitCast(iv)));
                            if (addr_u == 0) {
                                try state.print("  %_v_{d} = select i1 true, ptr null, ptr null\n", .{dst_raw});
                            } else {
                                try state.print(
                                    "  %_v_{d} = select i1 true, ptr inttoptr ({s} {d} to ptr), ptr null\n",
                                    .{ dst_raw, ptr_int, addr_u },
                                );
                            }
                        } else {
                            const zero_s = resolveZeroLiteralForLlvmType(ty_s);
                            try state.print(
                                "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                                .{ dst_raw, ty_s, zero_s, ty_s, zero_s },
                            );
                        }
                    }
                },
                .float_val => |fv| {
                    const is_f32 = dst_ty == .f32_ty;
                    const flt_ty = if (is_f32) "float" else "double";
                    const hex_s = try formatLlvmHexFloatLiteral(emitter.allocator, is_f32, fv);
                    defer emitter.allocator.free(hex_s);
                    try state.print(
                        "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                        .{ dst_raw, flt_ty, hex_s, flt_ty, hex_s },
                    );
                },
                .str_val, .bytes_val => |sym_id| {
                    const raw_bytes = emitter.input.interner.get(sym_id);
                    const dst_node = emitter.input.pool.getNode(dst_ty);
                    const ptr_expr = if (raw_bytes.len == 0)
                        try std.fmt.allocPrint(emitter.allocator, "inttoptr ({s} 1 to ptr)", .{ptr_int})
                    else
                        try std.fmt.allocPrint(emitter.allocator, "@_cx_str_bytes_{d}", .{sym_id.asInt()});
                    defer emitter.allocator.free(ptr_expr);

                    if (dst_node.tag == .ref_ty or dst_node.tag == .mut_ref_ty or dst_node.tag == .raw_ptr_ty) {
                        const pointee = try unwrapTransparentType(emitter, TypeId.fromInt(dst_node.lhs));
                        if (emitter.input.pool.getNode(pointee).tag == .slice_ty or pointee == .str_ty) {
                            const sid = emitter.nextSynthGlobalId();
                            const hdr_line = try std.fmt.allocPrint(
                                emitter.allocator,
                                "@_cx_sref_{d} = private unnamed_addr constant {{ ptr, {s} }} " ++
                                    "{{ ptr {s}, {s} {d} }}, align {d}\n",
                                .{ sid, ptr_int, ptr_expr, ptr_int, raw_bytes.len, emitter.cfg.target.ptrBytes() },
                            );
                            defer emitter.allocator.free(hdr_line);
                            try emitter.synth_globals.appendSlice(emitter.allocator, hdr_line);
                            try state.print(
                                "  %_v_{d} = select i1 true, ptr @_cx_sref_{d}, ptr @_cx_sref_{d}\n",
                                .{ dst_raw, sid, sid },
                            );
                        } else {
                            try state.print(
                                "  %_v_{d} = select i1 true, ptr {s}, ptr {s}\n",
                                .{ dst_raw, ptr_expr, ptr_expr },
                            );
                        }
                    } else {
                        const tmp_id = state.nextTmp();
                        try state.print(
                            "  %_sf0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr {s}, 0\n" ++
                                "  %_v_{d} = insertvalue {{ ptr, {s} }} %_sf0_{d}, {s} {d}, 1\n",
                            .{ tmp_id, ptr_int, ptr_expr, dst_raw, ptr_int, tmp_id, ptr_int, raw_bytes.len },
                        );
                    }
                },
                .raw_blob => |rb| {
                    const dst_node = emitter.input.pool.getNode(dst_ty);
                    if (dst_node.tag == .ref_ty or dst_node.tag == .mut_ref_ty or dst_node.tag == .raw_ptr_ty) {
                        const pointee = try unwrapTransparentType(emitter, TypeId.fromInt(dst_node.lhs));
                        if (emitter.input.pool.getNode(pointee).tag == .slice_ty) {
                            try state.print(
                                "  %_v_{d} = select i1 true, ptr @_cx_blob_slice_{d}, ptr @_cx_blob_slice_{d}\n",
                                .{ dst_raw, rb.blob_id, rb.blob_id },
                            );
                        } else if (rb.byte_len == 0) {
                            const align_b: u32 = @as(u32, 1) << @intCast(rb.align_log2);
                            try state.print(
                                "  %_v_{d} = select i1 true, ptr inttoptr ({s} {d} to ptr), ptr null\n",
                                .{ dst_raw, ptr_int, @max(align_b, 1) },
                            );
                        } else {
                            try state.print(
                                "  %_v_{d} = select i1 true, ptr @_cx_blob_{d}, ptr @_cx_blob_{d}\n",
                                .{ dst_raw, rb.blob_id, rb.blob_id },
                            );
                        }
                    } else {
                        try state.print(
                            "  %_v_{d} = load {{ ptr, {s} }}, ptr @_cx_blob_slice_{d}, align {d}\n",
                            .{ dst_raw, ptr_int, rb.blob_id, emitter.cfg.target.ptrBytes() },
                        );
                    }
                },
            }
        },

        .copy_val => {
            if (try isZeroSizedType(emitter, inst.type_id)) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const val_ty = try formatLlvmValueType(emitter, inst.type_id);
            defer emitter.allocator.free(val_ty);
            try state.print(
                "  %_v_{d} = select i1 true, {s} %_v_{d}, {s} %_v_{d}\n",
                .{ dst_raw, val_ty, inst.operands.lhs, val_ty, inst.operands.lhs },
            );
            if (std.mem.eql(u8, val_ty, "ptr")) {
                if (lookupProvenRange(emitter, body_idx, dst_raw)) |prov_r| {
                    const dst_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{dst_raw});
                    defer emitter.allocator.free(dst_ssa);
                    try maybeEmitPointerAssume(emitter, state, dst_ssa, prov_r);
                }
            }
        },

        .bin_op => {
            const kind: mir.BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            try emitBinOpLlvm(
                emitter,
                state,
                body_idx,
                body,
                dst_raw,
                kind,
                MirValueId.fromInt(inst.operands.lhs),
                MirValueId.fromInt(inst.operands.rhs),
                inst.type_id,
            );
        },

        .unary_op => {
            const kind: mir.UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            try emitUnaryOpLlvm(
                emitter,
                state,
                body,
                dst_raw,
                kind,
                MirValueId.fromInt(inst.operands.lhs),
                inst.operands.rhs,
                inst.type_id,
            );
        },

        .aggregate_make => {
            const kind: mir.AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            try emitAggregateMakeLlvm(emitter, state, body_idx, body, dst_raw, kind, inst);
        },

        .aggregate_extract => {
            if (try isZeroSizedType(emitter, inst.type_id)) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const src_raw = inst.operands.lhs;
            const fld_ord = inst.operands.rhs;
            const src_ty = try unwrapTransparentType(emitter, body.getInst(MirValueId.fromInt(src_raw)).type_id);
            const src_lay = try emitter.resolver.resolveType(src_ty);
            const scratch = try state.allocEntryBytes(src_lay.size_bytes, src_lay.alignBytes());
            defer emitter.allocator.free(scratch);
            const src_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{src_raw});
            defer emitter.allocator.free(src_ssa);
            try emitStoreValueToPtr(emitter, state, src_ty, src_ssa, scratch, src_lay.alignBytes(), 0, 0, 0);

            const src_node = emitter.input.pool.getNode(src_ty);
            var elem_off: u64 = 0;
            var elem_align: u32 = 1;
            if (src_node.tag == .array_ty) {
                const elem_lay = try emitter.resolver.resolveType(inst.type_id);
                elem_off = @as(u64, fld_ord) * elem_lay.stride_bytes;
                elem_align = @min(src_lay.alignBytes(), effectiveOffsetAlign(elem_off, elem_lay.alignBytes()));
            } else if (src_node.tag == .slice_ty or src_ty == .str_ty or src_node.tag == .soa_slice_ty) {
                elem_off = if (fld_ord == 0) 0 else emitter.cfg.target.ptrBytes();
                elem_align = emitter.cfg.target.ptrBytes();
            } else if (try emitter.resolver.getFieldByDeclOrdinal(src_ty, fld_ord)) |fld| {
                elem_off = fld.byte_offset;
                const nat_align = @as(u32, 1) << @intCast(fld.align_log2);
                elem_align = if (src_lay.reprFlags().is_packed)
                    1
                else
                    @min(src_lay.alignBytes(), effectiveOffsetAlign(fld.byte_offset, nat_align));
            }

            const fld_ptr = if (elem_off == 0)
                try emitter.allocator.dupe(u8, scratch)
            else blk: {
                const tmp_id = state.nextTmp();
                try state.print(
                    "  %_aep_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                    .{ tmp_id, scratch, ptr_int, elem_off },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_aep_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(fld_ptr);

            const loaded = try emitLoadValueFromPtr(
                emitter,
                state,
                inst.type_id,
                fld_ptr,
                elem_align,
                lookupProvenRange(emitter, body_idx, dst_raw),
                0,
                0,
                0,
            );
            defer emitter.allocator.free(loaded);
            const dst_val_ty = try formatLlvmValueType(emitter, inst.type_id);
            defer emitter.allocator.free(dst_val_ty);
            try state.print(
                "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                .{ dst_raw, dst_val_ty, loaded, dst_val_ty, loaded },
            );
        },

        .aggregate_insert => {
            if (try isZeroSizedType(emitter, inst.type_id)) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const src_raw = inst.operands.lhs;
            const fld_ord = body.extra_args.items[inst.operands.rhs];
            const elem_raw = body.extra_args.items[inst.operands.rhs + 1];
            const agg_ty = try unwrapTransparentType(emitter, inst.type_id);
            const agg_lay = try emitter.resolver.resolveType(agg_ty);
            const scratch = try state.allocEntryBytes(agg_lay.size_bytes, agg_lay.alignBytes());
            defer emitter.allocator.free(scratch);
            const src_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{src_raw});
            defer emitter.allocator.free(src_ssa);
            try emitStoreValueToPtr(emitter, state, agg_ty, src_ssa, scratch, agg_lay.alignBytes(), 0, 0, 0);

            const elem_ty = body.getInst(MirValueId.fromInt(elem_raw)).type_id;
            if (!(try isZeroSizedType(emitter, elem_ty))) {
                const agg_node = emitter.input.pool.getNode(agg_ty);
                var elem_off: u64 = 0;
                var elem_align: u32 = 1;
                if (agg_node.tag == .array_ty) {
                    const elem_lay = try emitter.resolver.resolveType(elem_ty);
                    elem_off = @as(u64, fld_ord) * elem_lay.stride_bytes;
                    elem_align = @min(agg_lay.alignBytes(), effectiveOffsetAlign(elem_off, elem_lay.alignBytes()));
                } else if (try emitter.resolver.getFieldByDeclOrdinal(agg_ty, fld_ord)) |fld| {
                    elem_off = fld.byte_offset;
                    const nat_align = @as(u32, 1) << @intCast(fld.align_log2);
                    elem_align = if (agg_lay.reprFlags().is_packed)
                        1
                    else
                        @min(agg_lay.alignBytes(), effectiveOffsetAlign(fld.byte_offset, nat_align));
                }
                const fld_ptr = if (elem_off == 0)
                    try emitter.allocator.dupe(u8, scratch)
                else blk: {
                    const tmp_id = state.nextTmp();
                    try state.print(
                        "  %_aip_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                        .{ tmp_id, scratch, ptr_int, elem_off },
                    );
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_aip_{d}", .{tmp_id});
                };
                defer emitter.allocator.free(fld_ptr);
                const elem_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{elem_raw});
                defer emitter.allocator.free(elem_ssa);
                try emitStoreValueToPtr(emitter, state, elem_ty, elem_ssa, fld_ptr, elem_align, 0, 0, 0);
            }
            const loaded = try emitLoadValueFromPtr(
                emitter,
                state,
                agg_ty,
                scratch,
                agg_lay.alignBytes(),
                null,
                0,
                0,
                0,
            );
            defer emitter.allocator.free(loaded);
            const agg_val_ty = try formatLlvmValueType(emitter, agg_ty);
            defer emitter.allocator.free(agg_val_ty);
            try state.print(
                "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                .{ dst_raw, agg_val_ty, loaded, agg_val_ty, loaded },
            );
        },

        .bitfield_extract => {
            const spec = hir.BitSpec.fromU32(inst.operands.rhs);
            const back_bits: u16 = @max(@as(u16, spec.backing_bits), 8);
            const tmp_id = state.nextTmp();
            if (spec.is_signed) {
                const sh_left: u16 = back_bits -| (@as(u16, spec.bit_offset) + @as(u16, spec.bit_width));
                const sh_right: u16 = back_bits -| @as(u16, spec.bit_width);
                try state.print(
                    "  %_bfe_l_{d} = shl i{d} %_v_{d}, {d}\n" ++
                        "  %_bfe_r_{d} = ashr i{d} %_bfe_l_{d}, {d}\n",
                    .{ tmp_id, back_bits, inst.operands.lhs, sh_left, tmp_id, back_bits, tmp_id, sh_right },
                );
            } else {
                try state.print(
                    "  %_bfe_s_{d} = lshr i{d} %_v_{d}, {d}\n",
                    .{ tmp_id, back_bits, inst.operands.lhs, spec.bit_offset },
                );
                if (spec.bit_width >= back_bits) {
                    try state.print(
                        "  %_bfe_r_{d} = add i{d} %_bfe_s_{d}, 0\n",
                        .{ tmp_id, back_bits, tmp_id },
                    );
                } else if (back_bits == 128) {
                    const mask_128: u128 = (@as(u128, 1) << @intCast(spec.bit_width)) - 1;
                    try state.print(
                        "  %_bfe_r_{d} = and i128 %_bfe_s_{d}, {d}\n",
                        .{ tmp_id, tmp_id, @as(i128, @bitCast(mask_128)) },
                    );
                } else {
                    const mask_u: u64 = (@as(u64, 1) << @intCast(spec.bit_width)) - 1;
                    try state.print(
                        "  %_bfe_r_{d} = and i{d} %_bfe_s_{d}, {d}\n",
                        .{ tmp_id, back_bits, tmp_id, mask_u },
                    );
                }
            }
            const dst_unwrapped = try unwrapTransparentType(emitter, inst.type_id);
            if (dst_unwrapped == .bool_ty) {
                try state.print("  %_v_{d} = trunc i{d} %_bfe_r_{d} to i1\n", .{ dst_raw, back_bits, tmp_id });
            } else if (resolveIntegerInfo(emitter, dst_unwrapped)) |dst_info| {
                if (dst_info.bits == back_bits) {
                    try state.print("  %_v_{d} = add i{d} %_bfe_r_{d}, 0\n", .{ dst_raw, back_bits, tmp_id });
                } else if (dst_info.bits < back_bits) {
                    try state.print(
                        "  %_v_{d} = trunc i{d} %_bfe_r_{d} to i{d}\n",
                        .{ dst_raw, back_bits, tmp_id, dst_info.bits },
                    );
                } else {
                    const ext_op = if (spec.is_signed) "sext" else "zext";
                    try state.print(
                        "  %_v_{d} = {s} i{d} %_bfe_r_{d} to i{d}\n",
                        .{ dst_raw, ext_op, back_bits, tmp_id, dst_info.bits },
                    );
                }
            }
        },

        .bitfield_insert => {
            const spec = hir.BitSpec.fromU32(inst.operands.rhs);
            const back_bits: u16 = @max(@as(u16, spec.backing_bits), 8);
            const base_raw = body.extra_args.items[inst.operands.lhs];
            const ins_raw = body.extra_args.items[inst.operands.lhs + 1];
            const ins_ty = try unwrapTransparentType(emitter, body.getInst(MirValueId.fromInt(ins_raw)).type_id);
            const tmp_id = state.nextTmp();

            if (ins_ty == .bool_ty) {
                try state.print("  %_bfi_c_{d} = zext i1 %_v_{d} to i{d}\n", .{ tmp_id, ins_raw, back_bits });
            } else if (resolveIntegerInfo(emitter, ins_ty)) |ins_info| {
                if (ins_info.bits == back_bits) {
                    try state.print("  %_bfi_c_{d} = add i{d} %_v_{d}, 0\n", .{ tmp_id, back_bits, ins_raw });
                } else if (ins_info.bits < back_bits) {
                    try state.print(
                        "  %_bfi_c_{d} = zext i{d} %_v_{d} to i{d}\n",
                        .{ tmp_id, ins_info.bits, ins_raw, back_bits },
                    );
                } else {
                    try state.print(
                        "  %_bfi_c_{d} = trunc i{d} %_v_{d} to i{d}\n",
                        .{ tmp_id, ins_info.bits, ins_raw, back_bits },
                    );
                }
            } else {
                try state.print("  %_bfi_c_{d} = add i{d} 0, 0\n", .{ tmp_id, back_bits });
            }

            if (spec.bit_width >= back_bits) {
                try state.print("  %_v_{d} = add i{d} %_bfi_c_{d}, 0\n", .{ dst_raw, back_bits, tmp_id });
            } else {
                const raw_mask: u128 = (@as(u128, 1) << @intCast(spec.bit_width)) - 1;
                const pos_mask: u128 = raw_mask << @intCast(spec.bit_offset);
                const full_mask: u128 = if (back_bits == 128)
                    std.math.maxInt(u128)
                else
                    (@as(u128, 1) << @intCast(back_bits)) - 1;
                const clr_mask: u128 = full_mask ^ pos_mask;
                try state.print(
                    "  %_bfi_m_{d} = and i{d} %_bfi_c_{d}, {d}\n" ++
                        "  %_bfi_s_{d} = shl i{d} %_bfi_m_{d}, {d}\n" ++
                        "  %_bfi_b_{d} = and i{d} %_v_{d}, {d}\n" ++
                        "  %_v_{d} = or i{d} %_bfi_b_{d}, %_bfi_s_{d}\n",
                    .{
                        tmp_id,
                        back_bits,
                        tmp_id,
                        @as(i128, @bitCast(raw_mask)),
                        tmp_id,
                        back_bits,
                        tmp_id,
                        spec.bit_offset,
                        tmp_id,
                        back_bits,
                        base_raw,
                        @as(i128, @bitCast(clr_mask)),
                        dst_raw,
                        back_bits,
                        tmp_id,
                        tmp_id,
                    },
                );
            }
        },

        .fn_addr => {
            const def_id = DefId.fromInt(inst.operands.lhs);
            const sym_idx = SymbolIndex.fromInt(inst.operands.rhs);
            if (resolveBodyIndex(emitter, def_id, sym_idx)) |target_b| {
                const fn_name = emitter.body_llvm_names.items[target_b];
                if (emitter.ctx_wrap_map.contains(target_b) and
                    isFnAddrCtxWrapperNeeded(emitter, target_b, inst.type_id) and
                    isFnAddrUsedAsValue(body, dst_raw))
                {
                    try state.print(
                        "  %_v_{d} = select i1 true, ptr @_cx_fn_ctxwrap_{d}, ptr @_cx_fn_ctxwrap_{d}\n",
                        .{ dst_raw, target_b, target_b },
                    );
                } else if (emitter.input.is_dev_got_enabled) {
                    const got_len = @max(emitter.input.bodies.len, 1);
                    const tmp_id = state.nextTmp();
                    try state.print(
                        "  %_fngp_{d} = getelementptr inbounds [{d} x ptr], ptr @_cx_dev_got, {s} 0, {s} {d}\n" ++
                            "  %_v_{d} = load ptr, ptr %_fngp_{d}, align {d}\n",
                        .{
                            tmp_id,
                            got_len,
                            ptr_int,
                            ptr_int,
                            target_b,
                            dst_raw,
                            tmp_id,
                            emitter.cfg.target.ptrBytes(),
                        },
                    );
                } else {
                    const fn_ident = try formatLlvmGlobalIdent(emitter.allocator, fn_name);
                    defer emitter.allocator.free(fn_ident);
                    try state.print(
                        "  %_v_{d} = select i1 true, ptr {s}, ptr {s}\n",
                        .{ dst_raw, fn_ident, fn_ident },
                    );
                }
            } else if (!sym_idx.isNone() and sym_idx.asInt() < emitter.input.sym_table.symbols.items.len) {
                const sym_rec = emitter.input.sym_table.getSymbol(sym_idx).*;
                const ext_name = if (sym_rec.contract_flags.has_link_name and sym_rec.link_name_text.len > 0)
                    sym_rec.link_name_text
                else
                    sym_rec.name_text;
                const ext_ident = try formatLlvmGlobalIdent(emitter.allocator, ext_name);
                defer emitter.allocator.free(ext_ident);
                try state.print(
                    "  %_v_{d} = select i1 true, ptr {s}, ptr {s}\n",
                    .{ dst_raw, ext_ident, ext_ident },
                );
            } else {
                try state.print(
                    "  %_v_{d} = select i1 true, ptr inttoptr ({s} 1 to ptr), ptr null\n",
                    .{ dst_raw, ptr_int },
                );
            }
        },

        .place_load => {
            if (try isZeroSizedType(emitter, inst.type_id)) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const place_id = PlaceId.fromInt(inst.operands.lhs);
            const eff_access_grp = if (body.getPlaceProjections(place_id).len > 0) access_grp else 0;
            const lowered = try lowerPlaceLlvm(emitter, state, body, place_id);
            switch (lowered) {
                .const_len => |cl| {
                    const dst_info = resolveIntegerInfo(emitter, inst.type_id) orelse IntScalarInfo{
                        .bits = @as(u16, emitter.cfg.target.ptrBytes()) * 8,
                        .is_signed = false,
                    };
                    try state.print("  %_v_{d} = add i{d} 0, {d}\n", .{ dst_raw, dst_info.bits, cl.elem_count });
                },
                .addr_val => |av| {
                    defer emitter.allocator.free(av.ptr_str);
                    const mvs = lookupMvsScopeForLocal(state, av.root_param_local);
                    const prov_r = lookupProvenRange(emitter, body_idx, dst_raw);
                    const loaded = try emitLoadValueFromPtr(
                        emitter,
                        state,
                        inst.type_id,
                        av.ptr_str,
                        av.align_bytes,
                        prov_r,
                        mvs.scope_md,
                        mvs.noalias_md,
                        eff_access_grp,
                    );
                    defer emitter.allocator.free(loaded);
                    const val_ty = try formatLlvmValueType(emitter, inst.type_id);
                    defer emitter.allocator.free(val_ty);
                    try state.print(
                        "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                        .{ dst_raw, val_ty, loaded, val_ty, loaded },
                    );
                    if (std.mem.eql(u8, val_ty, "ptr")) {
                        if (prov_r) |p_rng| {
                            const dst_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{dst_raw});
                            defer emitter.allocator.free(dst_ssa);
                            try maybeEmitPointerAssume(emitter, state, dst_ssa, p_rng);
                        }
                    }
                },
            }
        },

        .place_store => {
            const val_raw = inst.operands.rhs;
            const val_ty = body.getInst(MirValueId.fromInt(val_raw)).type_id;
            const place_id = PlaceId.fromInt(inst.operands.lhs);
            const eff_access_grp = if (body.getPlaceProjections(place_id).len > 0) access_grp else 0;
            const lowered = try lowerPlaceLlvm(emitter, state, body, place_id);
            switch (lowered) {
                .const_len => {},
                .addr_val => |av| {
                    defer emitter.allocator.free(av.ptr_str);
                    const mvs = lookupMvsScopeForLocal(state, av.root_param_local);
                    const val_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{val_raw});
                    defer emitter.allocator.free(val_ssa);
                    try emitStoreValueToPtr(
                        emitter,
                        state,
                        val_ty,
                        val_ssa,
                        av.ptr_str,
                        av.align_bytes,
                        mvs.scope_md,
                        mvs.noalias_md,
                        eff_access_grp,
                    );
                },
            }
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        },

        .place_discriminant => {
            const lowered = try lowerPlaceLlvm(emitter, state, body, PlaceId.fromInt(inst.operands.lhs));
            switch (lowered) {
                .const_len => try state.print("  %_v_{d} = add i32 0, 0\n", .{dst_raw}),
                .addr_val => |av| {
                    defer emitter.allocator.free(av.ptr_str);
                    const disc_32 = try emitReadSumDiscriminantFromPtr(
                        emitter,
                        state,
                        av.pointee_ty,
                        av.ptr_str,
                        av.align_bytes,
                    );
                    defer emitter.allocator.free(disc_32);
                    const dst_info = resolveIntegerInfo(emitter, inst.type_id) orelse
                        IntScalarInfo{ .bits = 32, .is_signed = false };
                    if (dst_info.bits == 32) {
                        try state.print("  %_v_{d} = add i32 {s}, 0\n", .{ dst_raw, disc_32 });
                    } else if (dst_info.bits < 32) {
                        try state.print(
                            "  %_v_{d} = trunc i32 {s} to i{d}\n",
                            .{ dst_raw, disc_32, dst_info.bits },
                        );
                    } else {
                        try state.print(
                            "  %_v_{d} = zext i32 {s} to i{d}\n",
                            .{ dst_raw, disc_32, dst_info.bits },
                        );
                    }
                },
            }
        },

        .place_set_discrim => {
            const lowered = try lowerPlaceLlvm(emitter, state, body, PlaceId.fromInt(inst.operands.lhs));
            switch (lowered) {
                .const_len => {},
                .addr_val => |av| {
                    defer emitter.allocator.free(av.ptr_str);
                    try emitWriteSumDiscriminantToPtr(
                        emitter,
                        state,
                        av.pointee_ty,
                        av.ptr_str,
                        av.align_bytes,
                        inst.operands.rhs,
                    );
                },
            }
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        },

        .place_addr => {
            const lowered = try lowerPlaceLlvm(emitter, state, body, PlaceId.fromInt(inst.operands.lhs));
            switch (lowered) {
                .const_len => |cl| {
                    try state.print(
                        "  %_v_{d} = select i1 true, ptr inttoptr ({s} {d} to ptr), ptr null\n",
                        .{ dst_raw, ptr_int, @max(cl.elem_count, 1) },
                    );
                },
                .addr_val => |av| {
                    defer emitter.allocator.free(av.ptr_str);
                    const dst_unwrapped = try unwrapTransparentType(emitter, inst.type_id);
                    const dst_node = emitter.input.pool.getNode(dst_unwrapped);
                    const src_node = emitter.input.pool.getNode(av.pointee_ty);

                    const is_dst_slice_ref = (dst_node.tag == .ref_ty or
                        dst_node.tag == .mut_ref_ty or
                        dst_node.tag == .raw_ptr_ty) and blk: {
                        const dp = try unwrapTransparentType(emitter, TypeId.fromInt(dst_node.lhs));
                        if (dp == .str_ty) break :blk true;
                        if (dp.isPrimitiveOrSentinel()) break :blk false;
                        const dpn = emitter.input.pool.getNode(dp);
                        break :blk dpn.tag == .slice_ty or dpn.tag == .soa_slice_ty;
                    };

                    // Coercion `&[T; N]` / `&mut [T; N]` -> fat slice `[T]` or `&[T]` (`[CRITICAL-03]`):
                    if ((dst_node.tag == .slice_ty or dst_node.tag == .soa_slice_ty) and
                        (src_node.tag == .array_ty or src_node.tag == .soa_array_ty))
                    {
                        const cap: u64 = src_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                        const elem_ty = try unwrapTransparentType(emitter, TypeId.fromInt(src_node.lhs));
                        const elem_lay = try emitter.resolver.resolveType(elem_ty);
                        const data_ptr_s = if (cap == 0)
                            try std.fmt.allocPrint(
                                emitter.allocator,
                                "inttoptr ({s} {d} to ptr)",
                                .{ ptr_int, @max(elem_lay.alignBytes(), 1) },
                            )
                        else
                            try emitter.allocator.dupe(u8, av.ptr_str);
                        defer emitter.allocator.free(data_ptr_s);
                        const tmp_id = state.nextTmp();
                        try state.print(
                            "  %_paf_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr {s}, 0\n" ++
                                "  %_v_{d} = insertvalue {{ ptr, {s} }} %_paf_{d}, {s} {d}, 1\n",
                            .{ tmp_id, ptr_int, data_ptr_s, dst_raw, ptr_int, tmp_id, ptr_int, cap },
                        );
                    } else if (is_dst_slice_ref and
                        (src_node.tag == .array_ty or src_node.tag == .soa_array_ty))
                    {
                        const ptr_bytes = emitter.cfg.target.ptrBytes();
                        const cap: u64 = src_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                        const elem_ty = try unwrapTransparentType(emitter, TypeId.fromInt(src_node.lhs));
                        const elem_lay = try emitter.resolver.resolveType(elem_ty);
                        const data_ptr_s = if (cap == 0)
                            try std.fmt.allocPrint(
                                emitter.allocator,
                                "inttoptr ({s} {d} to ptr)",
                                .{ ptr_int, @max(elem_lay.alignBytes(), 1) },
                            )
                        else
                            try emitter.allocator.dupe(u8, av.ptr_str);
                        defer emitter.allocator.free(data_ptr_s);
                        const fat_slot = try state.allocEntryBytes(2 * ptr_bytes, ptr_bytes);
                        defer emitter.allocator.free(fat_slot);
                        const tmp_id = state.nextTmp();
                        try state.print(
                            "  store ptr {s}, ptr {s}, align {d}\n" ++
                                "  %_pas_{d} = getelementptr inbounds {{ ptr, {s} }}, ptr {s}, i32 0, i32 1\n" ++
                                "  store {s} {d}, ptr %_pas_{d}, align {d}\n" ++
                                "  %_v_{d} = select i1 true, ptr {s}, ptr {s}\n",
                            .{
                                data_ptr_s,
                                fat_slot,
                                ptr_bytes,
                                tmp_id,
                                ptr_int,
                                fat_slot,
                                ptr_int,
                                cap,
                                tmp_id,
                                ptr_bytes,
                                dst_raw,
                                fat_slot,
                                fat_slot,
                            },
                        );
                    } else {
                        try state.print(
                            "  %_v_{d} = select i1 true, ptr {s}, ptr {s}\n",
                            .{ dst_raw, av.ptr_str, av.ptr_str },
                        );
                        if (lookupProvenRange(emitter, body_idx, dst_raw)) |prov_r| {
                            var clamped_r = prov_r;
                            const place_log2: u8 = if (av.align_bytes > 1)
                                std.math.log2_int(u32, av.align_bytes)
                            else
                                0;
                            clamped_r.proven_align_log2 = @min(clamped_r.proven_align_log2, place_log2);
                            const dst_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{dst_raw});
                            defer emitter.allocator.free(dst_ssa);
                            try maybeEmitPointerAssume(emitter, state, dst_ssa, clamped_r);
                        }
                    }
                },
            }
        },

        .soa_column_slice => {
            const base_raw = inst.operands.lhs;
            const field_ord = inst.operands.rhs;
            const base_ty = try unwrapTransparentType(
                emitter,
                body.getInst(MirValueId.fromInt(base_raw)).type_id,
            );
            const base_node = emitter.input.pool.getNode(base_ty);
            const unwrapped_src = if (base_node.tag == .ref_ty or
                base_node.tag == .mut_ref_ty or
                base_node.tag == .raw_ptr_ty)
                try unwrapTransparentType(emitter, TypeId.fromInt(base_node.lhs))
            else
                base_ty;
            const src_node = emitter.input.pool.getNode(unwrapped_src);
            const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(src_node.lhs));
            const fld = (try emitter.resolver.getFieldByDeclOrdinal(elem_struct, field_ord)).?;
            const fld_align: u32 = @as(u32, 1) << @intCast(fld.align_log2);

            if (src_node.tag == .soa_array_ty) {
                const cap: u64 = src_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                const col_info = emitter.resolver.getSoaColumnOffset(elem_struct, field_ord, cap).?;
                const base_ptr_s = if (base_node.tag == .ref_ty or
                    base_node.tag == .mut_ref_ty or
                    base_node.tag == .raw_ptr_ty)
                    try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{base_raw})
                else blk: {
                    const arr_lay = try emitter.resolver.resolveType(unwrapped_src);
                    const scratch = try state.allocEntryBytes(arr_lay.size_bytes, arr_lay.alignBytes());
                    const val_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{base_raw});
                    defer emitter.allocator.free(val_ssa);
                    try emitStoreValueToPtr(emitter, state, unwrapped_src, val_ssa, scratch, arr_lay.alignBytes(), 0, 0, 0);
                    break :blk scratch;
                };
                defer emitter.allocator.free(base_ptr_s);

                const tmp_id = state.nextTmp();
                if (cap == 0) {
                    try state.print(
                        "  %_scs0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr inttoptr ({s} {d} to ptr), 0\n" ++
                            "  %_v_{d} = insertvalue {{ ptr, {s} }} %_scs0_{d}, {s} 0, 1\n",
                        .{ tmp_id, ptr_int, ptr_int, @max(fld_align, 1), dst_raw, ptr_int, tmp_id, ptr_int },
                    );
                } else {
                    try state.print(
                        "  %_scsp_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n" ++
                            "  %_scs0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr %_scsp_{d}, 0\n" ++
                            "  %_v_{d} = insertvalue {{ ptr, {s} }} %_scs0_{d}, {s} {d}, 1\n",
                        .{
                            tmp_id,
                            base_ptr_s,
                            ptr_int,
                            col_info.byte_offset,
                            tmp_id,
                            ptr_int,
                            tmp_id,
                            dst_raw,
                            ptr_int,
                            tmp_id,
                            ptr_int,
                            cap,
                        },
                    );
                }
            } else {
                const tmp_id = state.nextTmp();
                if (base_node.tag == .ref_ty or base_node.tag == .mut_ref_ty or base_node.tag == .raw_ptr_ty) {
                    try state.print(
                        "  %_scsf_{d} = load {{ ptr, {s} }}, ptr %_v_{d}, align {d}\n" ++
                            "  %_scsd_{d} = extractvalue {{ ptr, {s} }} %_scsf_{d}, 0\n" ++
                            "  %_scsl_{d} = extractvalue {{ ptr, {s} }} %_scsf_{d}, 1\n",
                        .{
                            tmp_id,
                            ptr_int,
                            base_raw,
                            emitter.cfg.target.ptrBytes(),
                            tmp_id,
                            ptr_int,
                            tmp_id,
                            tmp_id,
                            ptr_int,
                            tmp_id,
                        },
                    );
                } else {
                    try state.print(
                        "  %_scsd_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 0\n" ++
                            "  %_scsl_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 1\n",
                        .{ tmp_id, ptr_int, base_raw, tmp_id, ptr_int, base_raw },
                    );
                }
                const len_s = try std.fmt.allocPrint(emitter.allocator, "%_scsl_{d}", .{tmp_id});
                defer emitter.allocator.free(len_s);
                const dyn_col = try emitDynamicSoaColByteOffset(emitter, state, elem_struct, field_ord, len_s);
                defer emitter.allocator.free(dyn_col.off_ssa);
                try state.print(
                    "  %_scsp_{d} = getelementptr inbounds i8, ptr %_scsd_{d}, {s} {s}\n" ++
                        "  %_scsz_{d} = icmp eq {s} %_scsl_{d}, 0\n" ++
                        "  %_scsnn_{d} = select i1 %_scsz_{d}, ptr inttoptr ({s} {d} to ptr), ptr %_scsp_{d}\n" ++
                        "  %_scs0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr %_scsnn_{d}, 0\n" ++
                        "  %_v_{d} = insertvalue {{ ptr, {s} }} %_scs0_{d}, {s} %_scsl_{d}, 1\n",
                    .{
                        tmp_id,
                        tmp_id,
                        ptr_int,
                        dyn_col.off_ssa,
                        tmp_id,
                        ptr_int,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        ptr_int,
                        @max(fld_align, 1),
                        tmp_id,
                        tmp_id,
                        ptr_int,
                        tmp_id,
                        dst_raw,
                        ptr_int,
                        tmp_id,
                        ptr_int,
                        tmp_id,
                    },
                );
            }
        },

        .intrinsic_op => {
            const ikind: mir.MirIntrinsicKind = @fromBackingInt(@intCast(inst.aux_u16));
            try emitIntrinsicOpLlvm(emitter, state, body, bb_idx, dst_raw, ikind, inst);
        },
    }
}

/// Emits an element-by-element structural equality loop (`i1`) over `count_ssa` items of `elem_ty`.
fn emitStructuralSpanLoopEqLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    elem_ty: TypeId,
    base_l_ptr: []const u8,
    base_r_ptr: []const u8,
    count_ssa: []const u8,
    depth: u32,
) anyerror![]u8 {
    if (try isZeroSizedType(emitter, elem_ty)) return emitter.allocator.dupe(u8, "true");
    const ptr_int = ptrIntType(emitter);
    const ptr_bytes = emitter.cfg.target.ptrBytes();
    const elem_lay = try emitter.resolver.resolveType(elem_ty);

    const idx_slot = try state.allocEntryBytes(ptr_bytes, ptr_bytes);
    defer emitter.allocator.free(idx_slot);
    const res_slot = try state.allocEntryBytes(1, 1);
    defer emitter.allocator.free(res_slot);

    const tmp_id = state.nextTmp();
    try state.print(
        "  store {s} 0, ptr {s}, align {d}\n" ++
            "  store i8 1, ptr {s}, align 1\n" ++
            "  br label %_lpeq_hdr_{d}\n" ++
            "_lpeq_hdr_{d}:\n" ++
            "  %_lpeq_i_{d} = load {s}, ptr {s}, align {d}\n" ++
            "  %_lpeq_c_{d} = icmp ult {s} %_lpeq_i_{d}, {s}\n" ++
            "  br i1 %_lpeq_c_{d}, label %_lpeq_bd_{d}, label %_lpeq_dn_{d}\n" ++
            "_lpeq_bd_{d}:\n" ++
            "  %_lpeq_bo_{d} = mul {s} %_lpeq_i_{d}, {d}\n" ++
            "  %_lpeq_lp_{d} = getelementptr inbounds i8, ptr {s}, {s} %_lpeq_bo_{d}\n" ++
            "  %_lpeq_rp_{d} = getelementptr inbounds i8, ptr {s}, {s} %_lpeq_bo_{d}\n",
        .{
            ptr_int,               idx_slot,  ptr_bytes,
            res_slot,              tmp_id,    tmp_id,
            tmp_id,                ptr_int,   idx_slot,
            ptr_bytes,             tmp_id,    ptr_int,
            tmp_id,                count_ssa, tmp_id,
            tmp_id,                tmp_id,    tmp_id,
            tmp_id,                ptr_int,   tmp_id,
            elem_lay.stride_bytes, tmp_id,    base_l_ptr,
            ptr_int,               tmp_id,    tmp_id,
            base_r_ptr,            ptr_int,   tmp_id,
        },
    );
    state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_lpeq_bd_{d}", .{tmp_id}));

    const lp_s = try std.fmt.allocPrint(emitter.allocator, "%_lpeq_lp_{d}", .{tmp_id});
    defer emitter.allocator.free(lp_s);
    const rp_s = try std.fmt.allocPrint(emitter.allocator, "%_lpeq_rp_{d}", .{tmp_id});
    defer emitter.allocator.free(rp_s);
    const el_eq = try emitStructuralPtrEqLlvm(emitter, state, elem_ty, lp_s, rp_s, depth + 1);
    defer emitter.allocator.free(el_eq);

    try state.print(
        "  br i1 {s}, label %_lpeq_nx_{d}, label %_lpeq_fl_{d}\n" ++
            "_lpeq_fl_{d}:\n" ++
            "  store i8 0, ptr {s}, align 1\n" ++
            "  br label %_lpeq_dn_{d}\n" ++
            "_lpeq_nx_{d}:\n" ++
            "  %_lpeq_ni_{d} = add {s} %_lpeq_i_{d}, 1\n" ++
            "  store {s} %_lpeq_ni_{d}, ptr {s}, align {d}\n" ++
            "  br label %_lpeq_hdr_{d}\n" ++
            "_lpeq_dn_{d}:\n" ++
            "  %_lpeq_ld_{d} = load i8, ptr {s}, align 1\n" ++
            "  %_lpeq_rs_{d} = trunc i8 %_lpeq_ld_{d} to i1\n",
        .{
            el_eq,    tmp_id,    tmp_id,
            tmp_id,   res_slot,  tmp_id,
            tmp_id,   tmp_id,    ptr_int,
            tmp_id,   ptr_int,   tmp_id,
            idx_slot, ptr_bytes, tmp_id,
            tmp_id,   tmp_id,    res_slot,
            tmp_id,   tmp_id,
        },
    );
    state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_lpeq_dn_{d}", .{tmp_id}));
    return std.fmt.allocPrint(emitter.allocator, "%_lpeq_rs_{d}", .{tmp_id});
}

/// Emits UB-free, niche-aware structural equality (`i1`) comparing `raw_ty` at `(lhs_ptr, rhs_ptr)`.
fn emitStructuralPtrEqLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    raw_ty: TypeId,
    lhs_ptr: []const u8,
    rhs_ptr: []const u8,
    depth: u32,
) anyerror![]u8 {
    if (depth > 16) return emitter.allocator.dupe(u8, "false");
    const ty = try unwrapTransparentType(emitter, raw_ty);
    if (try isZeroSizedType(emitter, ty)) return emitter.allocator.dupe(u8, "true");
    const ptr_int = ptrIntType(emitter);

    if (ty == .bool_ty) {
        const tmp_id = state.nextTmp();
        try state.print(
            "  %_peqb_l_{d} = load i8, ptr {s}, align 1\n" ++
                "  %_peqb_r_{d} = load i8, ptr {s}, align 1\n" ++
                "  %_peqb_lm_{d} = and i8 %_peqb_l_{d}, 1\n" ++
                "  %_peqb_rm_{d} = and i8 %_peqb_r_{d}, 1\n" ++
                "  %_peqb_eq_{d} = icmp eq i8 %_peqb_lm_{d}, %_peqb_rm_{d}\n",
            .{
                tmp_id, lhs_ptr,
                tmp_id, rhs_ptr,
                tmp_id, tmp_id,
                tmp_id, tmp_id,
                tmp_id, tmp_id,
                tmp_id,
            },
        );
        return std.fmt.allocPrint(emitter.allocator, "%_peqb_eq_{d}", .{tmp_id});
    }

    if (ty == .str_ty) {
        if (!emitter.declared_externs.contains("memcmp")) {
            try emitter.requireIntrinsicDecl(
                if (emitter.cfg.target.isWasm())
                    "declare i32 @memcmp(ptr, ptr, i32) nounwind"
                else
                    "declare i32 @memcmp(ptr, ptr, i64) nounwind",
            );
        }
        const tmp_id = state.nextTmp();
        try state.print(
            "  %_peqs_l_{d} = load {{ ptr, {s} }}, ptr {s}, align 1\n" ++
                "  %_peqs_r_{d} = load {{ ptr, {s} }}, ptr {s}, align 1\n" ++
                "  %_peqs_lp_{d} = extractvalue {{ ptr, {s} }} %_peqs_l_{d}, 0\n" ++
                "  %_peqs_ll_{d} = extractvalue {{ ptr, {s} }} %_peqs_l_{d}, 1\n" ++
                "  %_peqs_rp_{d} = extractvalue {{ ptr, {s} }} %_peqs_r_{d}, 0\n" ++
                "  %_peqs_rl_{d} = extractvalue {{ ptr, {s} }} %_peqs_r_{d}, 1\n" ++
                "  %_peqs_ln_{d} = icmp eq {s} %_peqs_ll_{d}, %_peqs_rl_{d}\n" ++
                "  br i1 %_peqs_ln_{d}, label %_peqs_cz_{d}, label %_peqs_fl_{d}\n",
            .{
                tmp_id, ptr_int, lhs_ptr,
                tmp_id, ptr_int, rhs_ptr,
                tmp_id, ptr_int, tmp_id,
                tmp_id, ptr_int, tmp_id,
                tmp_id, ptr_int, tmp_id,
                tmp_id, ptr_int, tmp_id,
                tmp_id, ptr_int, tmp_id,
                tmp_id, tmp_id,  tmp_id,
                tmp_id,
            },
        );
        try state.print(
            "_peqs_cz_{d}:\n" ++
                "  %_peqs_iz_{d} = icmp eq {s} %_peqs_ll_{d}, 0\n" ++
                "  br i1 %_peqs_iz_{d}, label %_peqs_tr_{d}, label %_peqs_mc_{d}\n" ++
                "_peqs_mc_{d}:\n" ++
                "  %_peqs_mv_{d} = call i32 @memcmp(ptr %_peqs_lp_{d}, ptr %_peqs_rp_{d}, {s} %_peqs_ll_{d})\n" ++
                "  %_peqs_m0_{d} = icmp eq i32 %_peqs_mv_{d}, 0\n" ++
                "  br label %_peqs_jn_{d}\n" ++
                "_peqs_tr_{d}:\n  br label %_peqs_jn_{d}\n" ++
                "_peqs_fl_{d}:\n  br label %_peqs_jn_{d}\n" ++
                "_peqs_jn_{d}:\n" ++
                "  %_peqs_eq_{d} = phi i1 [ %_peqs_m0_{d}, %_peqs_mc_{d} ], " ++
                "[ true, %_peqs_tr_{d} ], [ false, %_peqs_fl_{d} ]\n",
            .{
                tmp_id,
                tmp_id,
                ptr_int,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                ptr_int,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
            },
        );
        state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_peqs_jn_{d}", .{tmp_id}));
        return std.fmt.allocPrint(emitter.allocator, "%_peqs_eq_{d}", .{tmp_id});
    }

    if (ty == .f32_ty or ty == .f64_ty or ty == .untyped_float_ty) {
        const flt_ty = if (ty == .f32_ty) "float" else "double";
        const tmp_id = state.nextTmp();
        try state.print(
            "  %_peqf_l_{d} = load {s}, ptr {s}, align 1\n" ++
                "  %_peqf_r_{d} = load {s}, ptr {s}, align 1\n" ++
                "  %_peqf_eq_{d} = fcmp oeq {s} %_peqf_l_{d}, %_peqf_r_{d}\n",
            .{ tmp_id, flt_ty, lhs_ptr, tmp_id, flt_ty, rhs_ptr, tmp_id, flt_ty, tmp_id, tmp_id },
        );
        return std.fmt.allocPrint(emitter.allocator, "%_peqf_eq_{d}", .{tmp_id});
    }

    if (resolveIntegerInfo(emitter, ty)) |int_info| {
        const tmp_id = state.nextTmp();
        try state.print(
            "  %_peqi_l_{d} = load i{d}, ptr {s}, align 1\n" ++
                "  %_peqi_r_{d} = load i{d}, ptr {s}, align 1\n" ++
                "  %_peqi_eq_{d} = icmp eq i{d} %_peqi_l_{d}, %_peqi_r_{d}\n",
            .{
                tmp_id, int_info.bits, lhs_ptr,
                tmp_id, int_info.bits, rhs_ptr,
                tmp_id, int_info.bits, tmp_id,
                tmp_id,
            },
        );
        return std.fmt.allocPrint(emitter.allocator, "%_peqi_eq_{d}", .{tmp_id});
    }

    if (ty.isPrimitiveOrSentinel()) return emitter.allocator.dupe(u8, "false");
    const node = emitter.input.pool.getNode(ty);

    switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .fn_ty => {
            const tmp_id = state.nextTmp();
            try state.print(
                "  %_peqp_l_{d} = load ptr, ptr {s}, align 1\n" ++
                    "  %_peqp_r_{d} = load ptr, ptr {s}, align 1\n" ++
                    "  %_peqp_eq_{d} = icmp eq ptr %_peqp_l_{d}, %_peqp_r_{d}\n",
                .{ tmp_id, lhs_ptr, tmp_id, rhs_ptr, tmp_id, tmp_id, tmp_id },
            );
            return std.fmt.allocPrint(emitter.allocator, "%_peqp_eq_{d}", .{tmp_id});
        },
        .optional_ty, .result_ty, .enum_ty => {
            const sum_detail = (try emitter.resolver.getSumDetail(ty)) orelse {
                const lay = try emitter.resolver.resolveType(ty);
                const bits: u16 = @intCast(@max(lay.size_bytes, 1) * 8);
                const tmp_id = state.nextTmp();
                try state.print(
                    "  %_peqe_l_{d} = load i{d}, ptr {s}, align 1\n" ++
                        "  %_peqe_r_{d} = load i{d}, ptr {s}, align 1\n" ++
                        "  %_peqe_eq_{d} = icmp eq i{d} %_peqe_l_{d}, %_peqe_r_{d}\n",
                    .{ tmp_id, bits, lhs_ptr, tmp_id, bits, rhs_ptr, tmp_id, bits, tmp_id, tmp_id },
                );
                return std.fmt.allocPrint(emitter.allocator, "%_peqe_eq_{d}", .{tmp_id});
            };

            const disc_l = try emitReadSumDiscriminantFromPtr(emitter, state, ty, lhs_ptr, 1);
            defer emitter.allocator.free(disc_l);
            const disc_r = try emitReadSumDiscriminantFromPtr(emitter, state, ty, rhs_ptr, 1);
            defer emitter.allocator.free(disc_r);

            const var_count: u32 = switch (node.tag) {
                .optional_ty, .result_ty => 2,
                .enum_ty => blk: {
                    const sym_idx = SymbolIndex.fromInt(node.rhs);
                    if (sym_idx.isNone() or sym_idx.asInt() >= emitter.input.sym_table.symbols.items.len) break :blk 0;
                    const enum_sym = emitter.input.sym_table.getSymbol(sym_idx).*;
                    if (enum_sym.target_scope.isNone()) break :blk 0;
                    var cnt: u32 = 0;
                    for (emitter.input.sym_table.getScopeMembers(enum_sym.target_scope)) |m_idx| {
                        if (emitter.input.sym_table.getSymbol(m_idx).kind == .enum_variant_sym) cnt += 1;
                    }
                    break :blk cnt;
                },
                else => 0,
            };

            var has_non_zst_payload = false;
            var scan_ord: u32 = 0;
            while (scan_ord < var_count) : (scan_ord += 1) {
                const v_pay = resolveEnumVariantPayloadType(emitter, ty, scan_ord);
                if (!(try isZeroSizedType(emitter, v_pay))) {
                    has_non_zst_payload = true;
                    break;
                }
            }

            const tmp_id = state.nextTmp();
            try state.print(
                "  %_peqd_eq_{d} = icmp eq i32 {s}, {s}\n",
                .{ tmp_id, disc_l, disc_r },
            );
            if (!has_non_zst_payload) {
                return std.fmt.allocPrint(emitter.allocator, "%_peqd_eq_{d}", .{tmp_id});
            }

            const res_slot = try state.allocEntryBytes(1, 1);
            defer emitter.allocator.free(res_slot);
            try state.print(
                "  store i8 0, ptr {s}, align 1\n" ++
                    "  br i1 %_peqd_eq_{d}, label %_peqd_sm_{d}, label %_peqd_dn_{d}\n" ++
                    "_peqd_sm_{d}:\n",
                .{ res_slot, tmp_id, tmp_id, tmp_id, tmp_id },
            );

            const pay_l = if (sum_detail.payload_offset == 0)
                try emitter.allocator.dupe(u8, lhs_ptr)
            else blk: {
                try state.print(
                    "  %_peqd_pl_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                    .{ tmp_id, lhs_ptr, ptr_int, sum_detail.payload_offset },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_peqd_pl_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(pay_l);

            const pay_r = if (sum_detail.payload_offset == 0)
                try emitter.allocator.dupe(u8, rhs_ptr)
            else blk: {
                try state.print(
                    "  %_peqd_pr_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                    .{ tmp_id, rhs_ptr, ptr_int, sum_detail.payload_offset },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_peqd_pr_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(pay_r);

            var var_ord: u32 = 0;
            while (var_ord < var_count) : (var_ord += 1) {
                const sub_id = state.nextTmp();
                const v_pay = resolveEnumVariantPayloadType(emitter, ty, var_ord);
                try state.print(
                    "  %_peqd_vc_{d} = icmp eq i32 {s}, {d}\n" ++
                        "  br i1 %_peqd_vc_{d}, label %_peqd_vh_{d}, label %_peqd_vn_{d}\n" ++
                        "_peqd_vh_{d}:\n",
                    .{ sub_id, disc_l, var_ord, sub_id, sub_id, sub_id, sub_id },
                );
                state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_peqd_vh_{d}", .{sub_id}));
                const v_eq = try emitStructuralPtrEqLlvm(emitter, state, v_pay, pay_l, pay_r, depth + 1);
                defer emitter.allocator.free(v_eq);
                try state.print(
                    "  %_peqd_vz_{d} = zext i1 {s} to i8\n" ++
                        "  store i8 %_peqd_vz_{d}, ptr {s}, align 1\n" ++
                        "  br label %_peqd_dn_{d}\n" ++
                        "_peqd_vn_{d}:\n",
                    .{ sub_id, v_eq, sub_id, res_slot, tmp_id, sub_id },
                );
                state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_peqd_vn_{d}", .{sub_id}));
            }

            try state.print(
                "  br label %_peqd_dn_{d}\n" ++
                    "_peqd_dn_{d}:\n" ++
                    "  %_peqd_ld_{d} = load i8, ptr {s}, align 1\n" ++
                    "  %_peqd_res_{d} = trunc i8 %_peqd_ld_{d} to i1\n",
                .{ tmp_id, tmp_id, tmp_id, res_slot, tmp_id, tmp_id },
            );
            state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_peqd_dn_{d}", .{tmp_id}));
            return std.fmt.allocPrint(emitter.allocator, "%_peqd_res_{d}", .{tmp_id});
        },
        .struct_ty, .tuple_ty => {
            const lay = try emitter.resolver.resolveType(ty);
            var acc_ssa = try emitter.allocator.dupe(u8, "true");
            errdefer emitter.allocator.free(acc_ssa);
            var fld_i: u32 = 0;
            while (fld_i < lay.aux_len) : (fld_i += 1) {
                const fld = emitter.resolver.fields_by_decl.items[lay.aux_start + fld_i];
                if (fld.size_bytes == 0) continue;
                const sub_id = state.nextTmp();
                const fp_l = if (fld.byte_offset == 0)
                    try emitter.allocator.dupe(u8, lhs_ptr)
                else blk: {
                    try state.print(
                        "  %_peqst_l_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                        .{ sub_id, lhs_ptr, ptr_int, fld.byte_offset },
                    );
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_peqst_l_{d}", .{sub_id});
                };
                defer emitter.allocator.free(fp_l);
                const fp_r = if (fld.byte_offset == 0)
                    try emitter.allocator.dupe(u8, rhs_ptr)
                else blk: {
                    try state.print(
                        "  %_peqst_r_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                        .{ sub_id, rhs_ptr, ptr_int, fld.byte_offset },
                    );
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_peqst_r_{d}", .{sub_id});
                };
                defer emitter.allocator.free(fp_r);
                const fld_eq = try emitStructuralPtrEqLlvm(emitter, state, fld.field_ty, fp_l, fp_r, depth + 1);
                defer emitter.allocator.free(fld_eq);
                try state.print(
                    "  %_peqst_a_{d} = and i1 {s}, {s}\n",
                    .{ sub_id, acc_ssa, fld_eq },
                );
                emitter.allocator.free(acc_ssa);
                acc_ssa = try std.fmt.allocPrint(emitter.allocator, "%_peqst_a_{d}", .{sub_id});
            }
            return acc_ssa;
        },
        .array_ty => {
            const elem_ty = try unwrapTransparentType(emitter, TypeId.fromInt(node.lhs));
            const cap: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            if (cap == 0) return emitter.allocator.dupe(u8, "true");
            const cap_s = try std.fmt.allocPrint(emitter.allocator, "{d}", .{cap});
            defer emitter.allocator.free(cap_s);
            return emitStructuralSpanLoopEqLlvm(emitter, state, elem_ty, lhs_ptr, rhs_ptr, cap_s, depth);
        },
        .soa_array_ty => {
            const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const st_lay = try emitter.resolver.resolveType(elem_struct);
            const cap: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            if (cap == 0 or st_lay.size_bytes == 0) return emitter.allocator.dupe(u8, "true");
            const cap_s = try std.fmt.allocPrint(emitter.allocator, "{d}", .{cap});
            defer emitter.allocator.free(cap_s);
            var acc_ssa = try emitter.allocator.dupe(u8, "true");
            errdefer emitter.allocator.free(acc_ssa);
            var col_ord: u32 = 0;
            while (col_ord < st_lay.aux_len) : (col_ord += 1) {
                const fld = emitter.resolver.fields_by_decl.items[st_lay.aux_start + col_ord];
                if (fld.size_bytes == 0) continue;
                const col = emitter.resolver.getSoaColumnOffset(elem_struct, col_ord, cap).?;
                const sub_id = state.nextTmp();
                const col_l = if (col.byte_offset == 0)
                    try emitter.allocator.dupe(u8, lhs_ptr)
                else blk: {
                    try state.print(
                        "  %_peqsa_l_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                        .{ sub_id, lhs_ptr, ptr_int, col.byte_offset },
                    );
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_peqsa_l_{d}", .{sub_id});
                };
                defer emitter.allocator.free(col_l);
                const col_r = if (col.byte_offset == 0)
                    try emitter.allocator.dupe(u8, rhs_ptr)
                else blk: {
                    try state.print(
                        "  %_peqsa_r_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                        .{ sub_id, rhs_ptr, ptr_int, col.byte_offset },
                    );
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_peqsa_r_{d}", .{sub_id});
                };
                defer emitter.allocator.free(col_r);
                const col_eq = try emitStructuralSpanLoopEqLlvm(
                    emitter,
                    state,
                    fld.field_ty,
                    col_l,
                    col_r,
                    cap_s,
                    depth,
                );
                defer emitter.allocator.free(col_eq);
                try state.print("  %_peqsa_a_{d} = and i1 {s}, {s}\n", .{ sub_id, acc_ssa, col_eq });
                emitter.allocator.free(acc_ssa);
                acc_ssa = try std.fmt.allocPrint(emitter.allocator, "%_peqsa_a_{d}", .{sub_id});
            }
            return acc_ssa;
        },
        .slice_ty => {
            const elem_ty = try unwrapTransparentType(emitter, TypeId.fromInt(node.lhs));
            const res_slot = try state.allocEntryBytes(1, 1);
            defer emitter.allocator.free(res_slot);
            const tmp_id = state.nextTmp();
            try state.print(
                "  store i8 0, ptr {s}, align 1\n" ++
                    "  %_peqsl_l_{d} = load {{ ptr, {s} }}, ptr {s}, align 1\n" ++
                    "  %_peqsl_r_{d} = load {{ ptr, {s} }}, ptr {s}, align 1\n" ++
                    "  %_peqsl_lp_{d} = extractvalue {{ ptr, {s} }} %_peqsl_l_{d}, 0\n" ++
                    "  %_peqsl_ll_{d} = extractvalue {{ ptr, {s} }} %_peqsl_l_{d}, 1\n" ++
                    "  %_peqsl_rp_{d} = extractvalue {{ ptr, {s} }} %_peqsl_r_{d}, 0\n" ++
                    "  %_peqsl_rl_{d} = extractvalue {{ ptr, {s} }} %_peqsl_r_{d}, 1\n" ++
                    "  %_peqsl_le_{d} = icmp eq {s} %_peqsl_ll_{d}, %_peqsl_rl_{d}\n" ++
                    "  br i1 %_peqsl_le_{d}, label %_peqsl_sm_{d}, label %_peqsl_dn_{d}\n" ++
                    "_peqsl_sm_{d}:\n",
                .{
                    res_slot,
                    tmp_id,
                    ptr_int,
                    lhs_ptr,
                    tmp_id,
                    ptr_int,
                    rhs_ptr,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                },
            );
            state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_peqsl_sm_{d}", .{tmp_id}));
            const lp_s = try std.fmt.allocPrint(emitter.allocator, "%_peqsl_lp_{d}", .{tmp_id});
            defer emitter.allocator.free(lp_s);
            const rp_s = try std.fmt.allocPrint(emitter.allocator, "%_peqsl_rp_{d}", .{tmp_id});
            defer emitter.allocator.free(rp_s);
            const ll_s = try std.fmt.allocPrint(emitter.allocator, "%_peqsl_ll_{d}", .{tmp_id});
            defer emitter.allocator.free(ll_s);
            const span_eq = try emitStructuralSpanLoopEqLlvm(emitter, state, elem_ty, lp_s, rp_s, ll_s, depth);
            defer emitter.allocator.free(span_eq);
            try state.print(
                "  %_peqsl_z_{d} = zext i1 {s} to i8\n" ++
                    "  store i8 %_peqsl_z_{d}, ptr {s}, align 1\n" ++
                    "  br label %_peqsl_dn_{d}\n" ++
                    "_peqsl_dn_{d}:\n" ++
                    "  %_peqsl_ld_{d} = load i8, ptr {s}, align 1\n" ++
                    "  %_peqsl_rs_{d} = trunc i8 %_peqsl_ld_{d} to i1\n",
                .{ tmp_id, span_eq, tmp_id, res_slot, tmp_id, tmp_id, tmp_id, res_slot, tmp_id, tmp_id },
            );
            state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_peqsl_dn_{d}", .{tmp_id}));
            return std.fmt.allocPrint(emitter.allocator, "%_peqsl_rs_{d}", .{tmp_id});
        },
        .soa_slice_ty => {
            const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const st_lay = try emitter.resolver.resolveType(elem_struct);
            const res_slot = try state.allocEntryBytes(1, 1);
            defer emitter.allocator.free(res_slot);
            const tmp_id = state.nextTmp();
            try state.print(
                "  store i8 0, ptr {s}, align 1\n" ++
                    "  %_peqss_l_{d} = load {{ ptr, {s} }}, ptr {s}, align 1\n" ++
                    "  %_peqss_r_{d} = load {{ ptr, {s} }}, ptr {s}, align 1\n" ++
                    "  %_peqss_lp_{d} = extractvalue {{ ptr, {s} }} %_peqss_l_{d}, 0\n" ++
                    "  %_peqss_ll_{d} = extractvalue {{ ptr, {s} }} %_peqss_l_{d}, 1\n" ++
                    "  %_peqss_rp_{d} = extractvalue {{ ptr, {s} }} %_peqss_r_{d}, 0\n" ++
                    "  %_peqss_rl_{d} = extractvalue {{ ptr, {s} }} %_peqss_r_{d}, 1\n" ++
                    "  %_peqss_le_{d} = icmp eq {s} %_peqss_ll_{d}, %_peqss_rl_{d}\n" ++
                    "  br i1 %_peqss_le_{d}, label %_peqss_sm_{d}, label %_peqss_dn_{d}\n" ++
                    "_peqss_sm_{d}:\n",
                .{
                    res_slot,
                    tmp_id,
                    ptr_int,
                    lhs_ptr,
                    tmp_id,
                    ptr_int,
                    rhs_ptr,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                },
            );
            state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_peqss_sm_{d}", .{tmp_id}));
            const ll_s = try std.fmt.allocPrint(emitter.allocator, "%_peqss_ll_{d}", .{tmp_id});
            defer emitter.allocator.free(ll_s);
            var acc_ssa = try emitter.allocator.dupe(u8, "true");
            errdefer emitter.allocator.free(acc_ssa);
            var col_ord: u32 = 0;
            while (col_ord < st_lay.aux_len) : (col_ord += 1) {
                const fld = emitter.resolver.fields_by_decl.items[st_lay.aux_start + col_ord];
                if (fld.size_bytes == 0) continue;
                const dyn_col = try emitDynamicSoaColByteOffset(emitter, state, elem_struct, col_ord, ll_s);
                defer emitter.allocator.free(dyn_col.off_ssa);
                const sub_id = state.nextTmp();
                try state.print(
                    "  %_peqss_cl_{d} = getelementptr inbounds i8, ptr %_peqss_lp_{d}, {s} {s}\n" ++
                        "  %_peqss_cr_{d} = getelementptr inbounds i8, ptr %_peqss_rp_{d}, {s} {s}\n",
                    .{
                        sub_id, tmp_id, ptr_int, dyn_col.off_ssa,
                        sub_id, tmp_id, ptr_int, dyn_col.off_ssa,
                    },
                );
                const col_l = try std.fmt.allocPrint(emitter.allocator, "%_peqss_cl_{d}", .{sub_id});
                defer emitter.allocator.free(col_l);
                const col_r = try std.fmt.allocPrint(emitter.allocator, "%_peqss_cr_{d}", .{sub_id});
                defer emitter.allocator.free(col_r);
                const col_eq = try emitStructuralSpanLoopEqLlvm(
                    emitter,
                    state,
                    fld.field_ty,
                    col_l,
                    col_r,
                    ll_s,
                    depth,
                );
                defer emitter.allocator.free(col_eq);
                try state.print("  %_peqss_a_{d} = and i1 {s}, {s}\n", .{ sub_id, acc_ssa, col_eq });
                emitter.allocator.free(acc_ssa);
                acc_ssa = try std.fmt.allocPrint(emitter.allocator, "%_peqss_a_{d}", .{sub_id});
            }
            defer emitter.allocator.free(acc_ssa);
            try state.print(
                "  %_peqss_z_{d} = zext i1 {s} to i8\n" ++
                    "  store i8 %_peqss_z_{d}, ptr {s}, align 1\n" ++
                    "  br label %_peqss_dn_{d}\n" ++
                    "_peqss_dn_{d}:\n" ++
                    "  %_peqss_ld_{d} = load i8, ptr {s}, align 1\n" ++
                    "  %_peqss_rs_{d} = trunc i8 %_peqss_ld_{d} to i1\n",
                .{ tmp_id, acc_ssa, tmp_id, res_slot, tmp_id, tmp_id, tmp_id, res_slot, tmp_id, tmp_id },
            );
            state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_peqss_dn_{d}", .{tmp_id}));
            return std.fmt.allocPrint(emitter.allocator, "%_peqss_rs_{d}", .{tmp_id});
        },
        else => return emitter.allocator.dupe(u8, "false"),
    }
}

/// Emits UB-free LLVM binary arithmetic, shift, bitwise, and relational operations into `%_v_<dst_raw>`.
fn emitBinOpLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body_idx: u32,
    body: *const MirBody,
    dst_raw: u32,
    kind: mir.BinOpKind,
    lhs_val: MirValueId,
    rhs_val: MirValueId,
    res_ty: TypeId,
) !void {
    const l_raw = lhs_val.asInt();
    const r_raw = rhs_val.asInt();
    const op_ty = try unwrapTransparentType(emitter, body.getInst(lhs_val).type_id);
    const ptr_int = ptrIntType(emitter);

    // [0] Zero-sized equality (`unit == unit`, `unit != unit`):
    if ((kind == .eq or kind == .ne) and (try isZeroSizedType(emitter, op_ty))) {
        const res_lit = if (kind == .eq) "true" else "false";
        try state.print("  %_v_{d} = or i1 false, {s}\n", .{ dst_raw, res_lit });
        return;
    }

    // [1] Fat-string equality (`str == str`, `str != str`):
    if (op_ty == .str_ty and (kind == .eq or kind == .ne)) {
        if (!emitter.declared_externs.contains("memcmp")) {
            try emitter.requireIntrinsicDecl(
                if (emitter.cfg.target.isWasm())
                    "declare i32 @memcmp(ptr, ptr, i32) nounwind"
                else
                    "declare i32 @memcmp(ptr, ptr, i64) nounwind",
            );
        }
        const tmp_id = state.nextTmp();
        try state.print(
            "  %_slp_l_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 0\n" ++
                "  %_sll_l_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 1\n" ++
                "  %_slp_r_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 0\n" ++
                "  %_sll_r_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 1\n" ++
                "  %_seq_ln_{d} = icmp eq {s} %_sll_l_{d}, %_sll_r_{d}\n" ++
                "  br i1 %_seq_ln_{d}, label %_seq_chkz_{d}, label %_seq_false_{d}\n" ++
                "_seq_chkz_{d}:\n" ++
                "  %_seq_isz_{d} = icmp eq {s} %_sll_l_{d}, 0\n" ++
                "  br i1 %_seq_isz_{d}, label %_seq_true_{d}, label %_seq_mcmp_{d}\n",
            .{
                tmp_id,  ptr_int, l_raw,
                tmp_id,  ptr_int, l_raw,
                tmp_id,  ptr_int, r_raw,
                tmp_id,  ptr_int, r_raw,
                tmp_id,  ptr_int, tmp_id,
                tmp_id,  tmp_id,  tmp_id,
                tmp_id,  tmp_id,  tmp_id,
                ptr_int, tmp_id,  tmp_id,
                tmp_id,  tmp_id,
            },
        );
        try state.print(
            "_seq_mcmp_{d}:\n" ++
                "  %_seq_mc_{d} = call i32 @memcmp(ptr %_slp_l_{d}, ptr %_slp_r_{d}, {s} %_sll_l_{d})\n" ++
                "  %_seq_m0_{d} = icmp eq i32 %_seq_mc_{d}, 0\n" ++
                "  br label %_seq_join_{d}\n" ++
                "_seq_true_{d}:\n" ++
                "  br label %_seq_join_{d}\n" ++
                "_seq_false_{d}:\n" ++
                "  br label %_seq_join_{d}\n" ++
                "_seq_join_{d}:\n" ++
                "  %_seq_eq_{d} = phi i1 [ %_seq_m0_{d}, %_seq_mcmp_{d} ], [ true, %_seq_true_{d} ], [ false, %_seq_false_{d} ]\n",
            .{
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                ptr_int,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
                tmp_id,
            },
        );
        if (kind == .ne) {
            try state.print("  %_v_{d} = xor i1 %_seq_eq_{d}, true\n", .{ dst_raw, tmp_id });
        } else {
            try state.print("  %_v_{d} = or i1 %_seq_eq_{d}, false\n", .{ dst_raw, tmp_id });
        }
        state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_seq_join_{d}", .{tmp_id}));
        return;
    }

    // [2] IEEE-754 floating-point arithmetic and relational comparisons:
    if (op_ty == .f32_ty or op_ty == .f64_ty or op_ty == .untyped_float_ty) {
        const flt_ty = if (op_ty == .f32_ty) "float" else "double";
        switch (kind) {
            .fadd => try state.print("  %_v_{d} = fadd {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            .fsub => try state.print("  %_v_{d} = fsub {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            .fmul => try state.print("  %_v_{d} = fmul {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            .fdiv => try state.print("  %_v_{d} = fdiv {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            .frem => try state.print("  %_v_{d} = frem {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            .eq => try state.print("  %_v_{d} = fcmp oeq {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            .ne => try state.print("  %_v_{d} = fcmp une {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            .flt => try state.print("  %_v_{d} = fcmp olt {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            .fle => try state.print("  %_v_{d} = fcmp ole {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            .fgt => try state.print("  %_v_{d} = fcmp ogt {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            .fge => try state.print("  %_v_{d} = fcmp oge {s} %_v_{d}, %_v_{d}\n", .{ dst_raw, flt_ty, l_raw, r_raw }),
            else => try state.print("  %_v_{d} = or i1 false, false\n", .{dst_raw}),
        }
        return;
    }

    // [3] Pointer relational and equality comparisons + composite structural equality (`Option`, `Result`, etc.):
    if (!op_ty.isPrimitiveOrSentinel()) {
        const op_tag = emitter.input.pool.getNode(op_ty).tag;
        if (op_tag == .ref_ty or op_tag == .mut_ref_ty or op_tag == .raw_ptr_ty or op_tag == .fn_ty) {
            const pred = switch (kind) {
                .eq => "eq",
                .ne => "ne",
                .ult, .slt => "ult",
                .ule, .sle => "ule",
                .ugt, .sgt => "ugt",
                .uge, .sge => "uge",
                else => "eq",
            };
            try state.print("  %_v_{d} = icmp {s} ptr %_v_{d}, %_v_{d}\n", .{ dst_raw, pred, l_raw, r_raw });
            return;
        }
        if ((kind == .eq or kind == .ne) and resolveIntegerInfo(emitter, op_ty) == null) {
            const lay = try emitter.resolver.resolveType(op_ty);
            const l_slot = try state.allocEntryBytes(lay.size_bytes, lay.alignBytes());
            defer emitter.allocator.free(l_slot);
            const r_slot = try state.allocEntryBytes(lay.size_bytes, lay.alignBytes());
            defer emitter.allocator.free(r_slot);
            try emitMemsetZero(emitter, state, l_slot, lay.size_bytes, lay.alignBytes());
            try emitMemsetZero(emitter, state, r_slot, lay.size_bytes, lay.alignBytes());
            const l_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{l_raw});
            defer emitter.allocator.free(l_ssa);
            const r_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{r_raw});
            defer emitter.allocator.free(r_ssa);
            try emitStoreValueToPtr(emitter, state, op_ty, l_ssa, l_slot, lay.alignBytes(), 0, 0, 0);
            try emitStoreValueToPtr(emitter, state, op_ty, r_ssa, r_slot, lay.alignBytes(), 0, 0, 0);

            const eq_ssa = try emitStructuralPtrEqLlvm(emitter, state, op_ty, l_slot, r_slot, 0);
            defer emitter.allocator.free(eq_ssa);
            if (kind == .ne) {
                try state.print("  %_v_{d} = xor i1 {s}, true\n", .{ dst_raw, eq_ssa });
            } else {
                try state.print("  %_v_{d} = or i1 {s}, false\n", .{ dst_raw, eq_ssa });
            }
            return;
        }
    }

    // [4] Boolean operations (`i1`):
    if (op_ty == .bool_ty) {
        switch (kind) {
            .bit_and => try state.print("  %_v_{d} = and i1 %_v_{d}, %_v_{d}\n", .{ dst_raw, l_raw, r_raw }),
            .bit_or => try state.print("  %_v_{d} = or i1 %_v_{d}, %_v_{d}\n", .{ dst_raw, l_raw, r_raw }),
            .bit_xor, .ne => try state.print("  %_v_{d} = xor i1 %_v_{d}, %_v_{d}\n", .{ dst_raw, l_raw, r_raw }),
            .eq => {
                const tmp_id = state.nextTmp();
                try state.print(
                    "  %_bneq_{d} = xor i1 %_v_{d}, %_v_{d}\n" ++
                        "  %_v_{d} = xor i1 %_bneq_{d}, true\n",
                    .{ tmp_id, l_raw, r_raw, dst_raw, tmp_id },
                );
            },
            .ult, .slt => try state.print("  %_v_{d} = icmp ult i1 %_v_{d}, %_v_{d}\n", .{ dst_raw, l_raw, r_raw }),
            .ule, .sle => try state.print("  %_v_{d} = icmp ule i1 %_v_{d}, %_v_{d}\n", .{ dst_raw, l_raw, r_raw }),
            .ugt, .sgt => try state.print("  %_v_{d} = icmp ugt i1 %_v_{d}, %_v_{d}\n", .{ dst_raw, l_raw, r_raw }),
            .uge, .sge => try state.print("  %_v_{d} = icmp uge i1 %_v_{d}, %_v_{d}\n", .{ dst_raw, l_raw, r_raw }),
            else => try state.print("  %_v_{d} = or i1 false, false\n", .{dst_raw}),
        }
        return;
    }

    // [5] Integer operations (`i8`, `i16`, `i32`, `i64`, `i128`):
    const info = resolveIntegerInfo(emitter, if (kind == .eq or kind == .ne or
        kind == .slt or kind == .ult or kind == .sle or kind == .ule or
        kind == .sgt or kind == .ugt or kind == .sge or kind == .uge)
        op_ty
    else
        res_ty) orelse {
        if (emitter.input.pool.unwrapUnderlyingType(res_ty) == .bool_ty) {
            try state.print("  %_v_{d} = or i1 false, false\n", .{dst_raw});
        } else {
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        }
        return;
    };
    const bits = info.bits;

    switch (kind) {
        .sadd_checked, .uadd_checked, .ssub_checked, .usub_checked, .smul_checked, .umul_checked => {
            const intr_stem = switch (kind) {
                .sadd_checked => "sadd",
                .uadd_checked => "uadd",
                .ssub_checked => "ssub",
                .usub_checked => "usub",
                .smul_checked => "smul",
                else => "umul",
            };
            const decl = try std.fmt.allocPrint(
                emitter.allocator,
                "declare {{ i{d}, i1 }} @llvm.{s}.with.overflow.i{d}(i{d}, i{d})",
                .{ bits, intr_stem, bits, bits, bits },
            );
            defer emitter.allocator.free(decl);
            try emitter.requireIntrinsicDecl(decl);

            const tmp_id = state.nextTmp();
            try state.print(
                "  %_ovp_{d} = call {{ i{d}, i1 }} @llvm.{s}.with.overflow.i{d}(i{d} %_v_{d}, i{d} %_v_{d})\n" ++
                    "  %_ovf_{d} = extractvalue {{ i{d}, i1 }} %_ovp_{d}, 1\n",
                .{ tmp_id, bits, intr_stem, bits, bits, l_raw, bits, r_raw, tmp_id, bits, tmp_id },
            );
            const ov_ssa = try std.fmt.allocPrint(emitter.allocator, "%_ovf_{d}", .{tmp_id});
            defer emitter.allocator.free(ov_ssa);
            try emitInlineTrapIfTrue(emitter, state, ov_ssa, 2);
            try state.print(
                "  %_v_{d} = extractvalue {{ i{d}, i1 }} %_ovp_{d}, 0\n",
                .{ dst_raw, bits, tmp_id },
            );
        },

        .udiv_checked, .urem_checked => {
            const tmp_id = state.nextTmp();
            try state.print("  %_dz_{d} = icmp eq i{d} %_v_{d}, 0\n", .{ tmp_id, bits, r_raw });
            const dz_ssa = try std.fmt.allocPrint(emitter.allocator, "%_dz_{d}", .{tmp_id});
            defer emitter.allocator.free(dz_ssa);
            try emitInlineTrapIfTrue(emitter, state, dz_ssa, 2);
            const div_op = if (kind == .udiv_checked) "udiv" else "urem";
            try state.print(
                "  %_v_{d} = {s} i{d} %_v_{d}, %_v_{d}\n",
                .{ dst_raw, div_op, bits, l_raw, r_raw },
            );
        },

        .sdiv_checked, .srem_checked => {
            const min_s: i128 = -(@as(i128, 1) << @intCast(bits - 1));
            const tmp_id = state.nextTmp();
            try state.print(
                "  %_dz_{d} = icmp eq i{d} %_v_{d}, 0\n" ++
                    "  %_ismin_{d} = icmp eq i{d} %_v_{d}, {d}\n" ++
                    "  %_isn1_{d} = icmp eq i{d} %_v_{d}, -1\n" ++
                    "  %_dov_{d} = and i1 %_ismin_{d}, %_isn1_{d}\n" ++
                    "  %_dbad_{d} = or i1 %_dz_{d}, %_dov_{d}\n",
                .{
                    tmp_id, bits,   r_raw,
                    tmp_id, bits,   l_raw,
                    min_s,  tmp_id, bits,
                    r_raw,  tmp_id, tmp_id,
                    tmp_id, tmp_id, tmp_id,
                    tmp_id,
                },
            );
            const bad_ssa = try std.fmt.allocPrint(emitter.allocator, "%_dbad_{d}", .{tmp_id});
            defer emitter.allocator.free(bad_ssa);
            try emitInlineTrapIfTrue(emitter, state, bad_ssa, 2);
            const div_op = if (kind == .sdiv_checked) "sdiv" else "srem";
            try state.print(
                "  %_v_{d} = {s} i{d} %_v_{d}, %_v_{d}\n",
                .{ dst_raw, div_op, bits, l_raw, r_raw },
            );
        },

        .shl_checked, .ashr_checked, .lshr_checked => {
            const rhs_info = resolveIntegerInfo(emitter, body.getInst(rhs_val).type_id) orelse
                IntScalarInfo{ .bits = bits, .is_signed = false };
            const tmp_id = state.nextTmp();
            try state.print(
                "  %_shoob_{d} = icmp uge i{d} %_v_{d}, {d}\n",
                .{ tmp_id, rhs_info.bits, r_raw, bits },
            );
            const oob_ssa = try std.fmt.allocPrint(emitter.allocator, "%_shoob_{d}", .{tmp_id});
            defer emitter.allocator.free(oob_ssa);
            try emitInlineTrapIfTrue(emitter, state, oob_ssa, 2);

            const amt_ssa = if (rhs_info.bits == bits)
                try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{r_raw})
            else blk: {
                const cast_op = if (rhs_info.bits < bits) "zext" else "trunc";
                try state.print(
                    "  %_shamt_{d} = {s} i{d} %_v_{d} to i{d}\n",
                    .{ tmp_id, cast_op, rhs_info.bits, r_raw, bits },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_shamt_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(amt_ssa);
            const sh_op = switch (kind) {
                .shl_checked => "shl",
                .ashr_checked => "ashr",
                else => "lshr",
            };
            try state.print(
                "  %_v_{d} = {s} i{d} %_v_{d}, {s}\n",
                .{ dst_raw, sh_op, bits, l_raw, amt_ssa },
            );
        },

        .add_wrap, .sub_wrap, .mul_wrap => {
            const nw = checkProvenNoWrapFlags(emitter, body_idx, kind, l_raw, r_raw, bits);
            const op_tok = switch (kind) {
                .add_wrap => "add",
                .sub_wrap => "sub",
                else => "mul",
            };
            const flag_s = if (nw.has_nsw and nw.has_nuw)
                " nsw nuw"
            else if (nw.has_nsw)
                " nsw"
            else if (nw.has_nuw)
                " nuw"
            else
                "";
            try state.print(
                "  %_v_{d} = {s}{s} i{d} %_v_{d}, %_v_{d}\n",
                .{ dst_raw, op_tok, flag_s, bits, l_raw, r_raw },
            );
        },

        .shl_wrap, .ashr_wrap, .lshr_wrap => {
            const rhs_info = resolveIntegerInfo(emitter, body.getInst(rhs_val).type_id) orelse
                IntScalarInfo{ .bits = bits, .is_signed = false };
            const tmp_id = state.nextTmp();
            const coerced_s = if (rhs_info.bits == bits)
                try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{r_raw})
            else blk: {
                const cast_op = if (rhs_info.bits < bits) "zext" else "trunc";
                try state.print(
                    "  %_shw_c_{d} = {s} i{d} %_v_{d} to i{d}\n",
                    .{ tmp_id, cast_op, rhs_info.bits, r_raw, bits },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_shw_c_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(coerced_s);
            const sh_op = switch (kind) {
                .shl_wrap => "shl",
                .ashr_wrap => "ashr",
                else => "lshr",
            };
            try state.print(
                "  %_shw_m_{d} = and i{d} {s}, {d}\n" ++
                    "  %_v_{d} = {s} i{d} %_v_{d}, %_shw_m_{d}\n",
                .{ tmp_id, bits, coerced_s, bits - 1, dst_raw, sh_op, bits, l_raw, tmp_id },
            );
        },

        .sadd_sat, .uadd_sat, .ssub_sat, .usub_sat => {
            const intr_stem = switch (kind) {
                .sadd_sat => "sadd",
                .uadd_sat => "uadd",
                .ssub_sat => "ssub",
                else => "usub",
            };
            const decl = try std.fmt.allocPrint(
                emitter.allocator,
                "declare i{d} @llvm.{s}.sat.i{d}(i{d}, i{d})",
                .{ bits, intr_stem, bits, bits, bits },
            );
            defer emitter.allocator.free(decl);
            try emitter.requireIntrinsicDecl(decl);
            try state.print(
                "  %_v_{d} = call i{d} @llvm.{s}.sat.i{d}(i{d} %_v_{d}, i{d} %_v_{d})\n",
                .{ dst_raw, bits, intr_stem, bits, bits, l_raw, bits, r_raw },
            );
        },

        .umul_sat => {
            const decl = try std.fmt.allocPrint(
                emitter.allocator,
                "declare {{ i{d}, i1 }} @llvm.umul.with.overflow.i{d}(i{d}, i{d})",
                .{ bits, bits, bits, bits },
            );
            defer emitter.allocator.free(decl);
            try emitter.requireIntrinsicDecl(decl);
            const tmp_id = state.nextTmp();
            try state.print(
                "  %_ums_p_{d} = call {{ i{d}, i1 }} @llvm.umul.with.overflow.i{d}(i{d} %_v_{d}, i{d} %_v_{d})\n" ++
                    "  %_ums_v_{d} = extractvalue {{ i{d}, i1 }} %_ums_p_{d}, 0\n" ++
                    "  %_ums_o_{d} = extractvalue {{ i{d}, i1 }} %_ums_p_{d}, 1\n" ++
                    "  %_v_{d} = select i1 %_ums_o_{d}, i{d} -1, i{d} %_ums_v_{d}\n",
                .{
                    tmp_id, bits, bits,   bits,   l_raw, bits,   r_raw,
                    tmp_id, bits, tmp_id, tmp_id, bits,  tmp_id, dst_raw,
                    tmp_id, bits, bits,   tmp_id,
                },
            );
        },

        .smul_sat => {
            const decl = try std.fmt.allocPrint(
                emitter.allocator,
                "declare {{ i{d}, i1 }} @llvm.smul.with.overflow.i{d}(i{d}, i{d})",
                .{ bits, bits, bits, bits },
            );
            defer emitter.allocator.free(decl);
            try emitter.requireIntrinsicDecl(decl);
            const min_s: i128 = -(@as(i128, 1) << @intCast(bits - 1));
            const max_s: i128 = (@as(i128, 1) << @intCast(bits - 1)) - 1;
            const tmp_id = state.nextTmp();
            try state.print(
                "  %_sms_p_{d} = call {{ i{d}, i1 }} @llvm.smul.with.overflow.i{d}(i{d} %_v_{d}, i{d} %_v_{d})\n" ++
                    "  %_sms_v_{d} = extractvalue {{ i{d}, i1 }} %_sms_p_{d}, 0\n" ++
                    "  %_sms_o_{d} = extractvalue {{ i{d}, i1 }} %_sms_p_{d}, 1\n",
                .{
                    tmp_id, bits, bits,   bits,   l_raw, bits,   r_raw,
                    tmp_id, bits, tmp_id, tmp_id, bits,  tmp_id,
                },
            );
            try state.print(
                "  %_sms_x_{d} = xor i{d} %_v_{d}, %_v_{d}\n" ++
                    "  %_sms_n_{d} = icmp slt i{d} %_sms_x_{d}, 0\n" ++
                    "  %_sms_l_{d} = select i1 %_sms_n_{d}, i{d} {d}, i{d} {d}\n" ++
                    "  %_v_{d} = select i1 %_sms_o_{d}, i{d} %_sms_l_{d}, i{d} %_sms_v_{d}\n",
                .{
                    tmp_id, bits,    l_raw,  r_raw,
                    tmp_id, bits,    tmp_id, tmp_id,
                    tmp_id, bits,    min_s,  bits,
                    max_s,  dst_raw, tmp_id, bits,
                    tmp_id, bits,    tmp_id,
                },
            );
        },

        .bit_and => try state.print("  %_v_{d} = and i{d} %_v_{d}, %_v_{d}\n", .{ dst_raw, bits, l_raw, r_raw }),
        .bit_or => try state.print("  %_v_{d} = or i{d} %_v_{d}, %_v_{d}\n", .{ dst_raw, bits, l_raw, r_raw }),
        .bit_xor => try state.print("  %_v_{d} = xor i{d} %_v_{d}, %_v_{d}\n", .{ dst_raw, bits, l_raw, r_raw }),

        .eq, .ne, .slt, .ult, .sle, .ule, .sgt, .ugt, .sge, .uge => {
            const pred = switch (kind) {
                .eq => "eq",
                .ne => "ne",
                .slt => "slt",
                .ult => "ult",
                .sle => "sle",
                .ule => "ule",
                .sgt => "sgt",
                .ugt => "ugt",
                .sge => "sge",
                else => "uge",
            };
            try state.print("  %_v_{d} = icmp {s} i{d} %_v_{d}, %_v_{d}\n", .{ dst_raw, pred, bits, l_raw, r_raw });
        },

        else => try state.print("  %_v_{d} = add i{d} 0, 0\n", .{ dst_raw, bits }),
    }
}

/// Emits UB-free LLVM unary operations and scalar/aggregate casts into `%_v_<dst_raw>`.
fn emitUnaryOpLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body: *const MirBody,
    dst_raw: u32,
    kind: mir.UnaryOpKind,
    src_val: MirValueId,
    rhs_ord: u32,
    dst_ty: TypeId,
) !void {
    const s_raw = src_val.asInt();
    const src_ty = try unwrapTransparentType(emitter, body.getInst(src_val).type_id);
    const unwrapped_dst = try unwrapTransparentType(emitter, dst_ty);
    const ptr_int = ptrIntType(emitter);

    switch (kind) {
        .sneg_checked => {
            const info = resolveIntegerInfo(emitter, unwrapped_dst) orelse return;
            const decl = try std.fmt.allocPrint(
                emitter.allocator,
                "declare {{ i{d}, i1 }} @llvm.ssub.with.overflow.i{d}(i{d}, i{d})",
                .{ info.bits, info.bits, info.bits, info.bits },
            );
            defer emitter.allocator.free(decl);
            try emitter.requireIntrinsicDecl(decl);
            const tmp_id = state.nextTmp();
            try state.print(
                "  %_negp_{d} = call {{ i{d}, i1 }} @llvm.ssub.with.overflow.i{d}(i{d} 0, i{d} %_v_{d})\n" ++
                    "  %_nego_{d} = extractvalue {{ i{d}, i1 }} %_negp_{d}, 1\n",
                .{ tmp_id, info.bits, info.bits, info.bits, info.bits, s_raw, tmp_id, info.bits, tmp_id },
            );
            const ov_ssa = try std.fmt.allocPrint(emitter.allocator, "%_nego_{d}", .{tmp_id});
            defer emitter.allocator.free(ov_ssa);
            try emitInlineTrapIfTrue(emitter, state, ov_ssa, 2);
            try state.print(
                "  %_v_{d} = extractvalue {{ i{d}, i1 }} %_negp_{d}, 0\n",
                .{ dst_raw, info.bits, tmp_id },
            );
        },

        .neg_wrap => {
            const info = resolveIntegerInfo(emitter, unwrapped_dst) orelse return;
            try state.print("  %_v_{d} = sub i{d} 0, %_v_{d}\n", .{ dst_raw, info.bits, s_raw });
        },

        .fneg => {
            const flt_ty = if (unwrapped_dst == .f32_ty) "float" else "double";
            try state.print("  %_v_{d} = fneg {s} %_v_{d}\n", .{ dst_raw, flt_ty, s_raw });
        },

        .bool_not => {
            try state.print("  %_v_{d} = xor i1 %_v_{d}, true\n", .{ dst_raw, s_raw });
        },

        .bit_not => {
            if (unwrapped_dst == .bool_ty) {
                try state.print("  %_v_{d} = xor i1 %_v_{d}, true\n", .{ dst_raw, s_raw });
            } else if (resolveIntegerInfo(emitter, unwrapped_dst)) |info| {
                try state.print("  %_v_{d} = xor i{d} %_v_{d}, -1\n", .{ dst_raw, info.bits, s_raw });
            }
        },

        .int_sext, .int_zext, .int_trunc => {
            const src_bits: u16 = if (src_ty == .bool_ty)
                1
            else if (resolveIntegerInfo(emitter, src_ty)) |si|
                si.bits
            else
                32;
            if (unwrapped_dst == .bool_ty) {
                if (src_bits == 1) {
                    try state.print("  %_v_{d} = or i1 %_v_{d}, false\n", .{ dst_raw, s_raw });
                } else {
                    try state.print("  %_v_{d} = trunc i{d} %_v_{d} to i1\n", .{ dst_raw, src_bits, s_raw });
                }
                return;
            }
            const dst_info = resolveIntegerInfo(emitter, unwrapped_dst) orelse return;
            if (src_bits == dst_info.bits) {
                try state.print("  %_v_{d} = add i{d} %_v_{d}, 0\n", .{ dst_raw, dst_info.bits, s_raw });
            } else if (src_bits < dst_info.bits) {
                const ext_op = if (kind == .int_sext and src_ty != .bool_ty) "sext" else "zext";
                try state.print(
                    "  %_v_{d} = {s} i{d} %_v_{d} to i{d}\n",
                    .{ dst_raw, ext_op, src_bits, s_raw, dst_info.bits },
                );
            } else {
                try state.print(
                    "  %_v_{d} = trunc i{d} %_v_{d} to i{d}\n",
                    .{ dst_raw, src_bits, s_raw, dst_info.bits },
                );
            }
        },

        .int_to_float_signed, .int_to_float_unsigned => {
            const src_bits: u16 = if (src_ty == .bool_ty)
                1
            else if (resolveIntegerInfo(emitter, src_ty)) |si|
                si.bits
            else
                32;
            const flt_ty = if (unwrapped_dst == .f32_ty) "float" else "double";
            const conv_op = if (kind == .int_to_float_signed and src_ty != .bool_ty) "sitofp" else "uitofp";
            try state.print(
                "  %_v_{d} = {s} i{d} %_v_{d} to {s}\n",
                .{ dst_raw, conv_op, src_bits, s_raw, flt_ty },
            );
        },

        .float_to_int_signed, .float_to_int_unsigned => {
            const dst_info = resolveIntegerInfo(emitter, unwrapped_dst) orelse return;
            const is_signed = kind == .float_to_int_signed;
            try emitter.requireIntrinsicDecl("declare double @llvm.fabs.f64(double)");
            try emitter.requireIntrinsicDecl("declare double @llvm.trunc.f64(double)");

            const tmp_id = state.nextTmp();
            const f64_ssa = if (src_ty == .f32_ty) blk: {
                try state.print("  %_ftiw_{d} = fpext float %_v_{d} to double\n", .{ tmp_id, s_raw });
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_ftiw_{d}", .{tmp_id});
            } else try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{s_raw});
            defer emitter.allocator.free(f64_ssa);

            const min_f64: f64 = if (is_signed)
                std.math.ldexp(@as(f64, -1.0), @as(i32, @intCast(dst_info.bits - 1)))
            else
                0.0;
            const max_excl_f64: f64 = std.math.ldexp(
                @as(f64, 1.0),
                @as(i32, @intCast(if (is_signed) dst_info.bits - 1 else dst_info.bits)),
            );
            const min_hex = try formatLlvmHexFloatLiteral(emitter.allocator, false, min_f64);
            defer emitter.allocator.free(min_hex);
            const max_hex = try formatLlvmHexFloatLiteral(emitter.allocator, false, max_excl_f64);
            defer emitter.allocator.free(max_hex);

            try state.print(
                "  %_ftia_{d} = call double @llvm.fabs.f64(double {s})\n" ++
                    "  %_ftibad_{d} = fcmp uge double %_ftia_{d}, 0x7FF0000000000000\n" ++
                    "  %_ftitr_{d} = call double @llvm.trunc.f64(double {s})\n" ++
                    "  %_ftilt_{d} = fcmp olt double %_ftitr_{d}, {s}\n" ++
                    "  %_ftige_{d} = fcmp oge double %_ftitr_{d}, {s}\n" ++
                    "  %_ftio1_{d} = or i1 %_ftibad_{d}, %_ftilt_{d}\n" ++
                    "  %_ftioob_{d} = or i1 %_ftio1_{d}, %_ftige_{d}\n",
                .{
                    tmp_id,  f64_ssa,
                    tmp_id,  tmp_id,
                    tmp_id,  f64_ssa,
                    tmp_id,  tmp_id,
                    min_hex, tmp_id,
                    tmp_id,  max_hex,
                    tmp_id,  tmp_id,
                    tmp_id,  tmp_id,
                    tmp_id,  tmp_id,
                },
            );
            const oob_ssa = try std.fmt.allocPrint(emitter.allocator, "%_ftioob_{d}", .{tmp_id});
            defer emitter.allocator.free(oob_ssa);
            try emitInlineTrapIfTrue(emitter, state, oob_ssa, 2);

            const conv_op = if (is_signed) "fptosi" else "fptoui";
            try state.print(
                "  %_v_{d} = {s} double %_ftitr_{d} to i{d}\n",
                .{ dst_raw, conv_op, tmp_id, dst_info.bits },
            );
        },

        .float_promote => {
            try state.print("  %_v_{d} = fpext float %_v_{d} to double\n", .{ dst_raw, s_raw });
        },

        .float_demote => {
            try state.print("  %_v_{d} = fptrunc double %_v_{d} to float\n", .{ dst_raw, s_raw });
        },

        .bitcast_op => {
            if (try isZeroSizedType(emitter, unwrapped_dst)) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            if (try tryEmitSliceArrayPtrCoercionLlvm(
                emitter,
                state,
                body,
                dst_raw,
                s_raw,
                src_ty,
                unwrapped_dst,
            )) return;
            const dst_lay = try emitter.resolver.resolveType(unwrapped_dst);
            const src_lay = try emitter.resolver.resolveType(src_ty);
            const scratch = try state.allocEntryBytes(
                @max(dst_lay.size_bytes, src_lay.size_bytes),
                @max(dst_lay.alignBytes(), src_lay.alignBytes()),
            );
            defer emitter.allocator.free(scratch);
            try emitMemsetZero(
                emitter,
                state,
                scratch,
                @max(dst_lay.size_bytes, src_lay.size_bytes),
                @max(dst_lay.alignBytes(), src_lay.alignBytes()),
            );
            const src_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{s_raw});
            defer emitter.allocator.free(src_ssa);
            try emitStoreValueToPtr(emitter, state, src_ty, src_ssa, scratch, src_lay.alignBytes(), 0, 0, 0);
            const loaded = try emitLoadValueFromPtr(
                emitter,
                state,
                unwrapped_dst,
                scratch,
                dst_lay.alignBytes(),
                null,
                0,
                0,
                0,
            );
            defer emitter.allocator.free(loaded);
            const dst_val_ty = try formatLlvmValueType(emitter, unwrapped_dst);
            defer emitter.allocator.free(dst_val_ty);
            try state.print(
                "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                .{ dst_raw, dst_val_ty, loaded, dst_val_ty, loaded },
            );
        },

        .ptr_cast => {
            if (try tryEmitSliceArrayPtrCoercionLlvm(
                emitter,
                state,
                body,
                dst_raw,
                s_raw,
                src_ty,
                unwrapped_dst,
            )) return;
            const src_val_ty = try formatLlvmValueType(emitter, src_ty);
            defer emitter.allocator.free(src_val_ty);
            const dst_val_ty = try formatLlvmValueType(emitter, unwrapped_dst);
            defer emitter.allocator.free(dst_val_ty);

            const src_is_ptr = std.mem.eql(u8, src_val_ty, "ptr");
            const dst_is_ptr = std.mem.eql(u8, dst_val_ty, "ptr");
            if (src_is_ptr and dst_is_ptr) {
                try state.print("  %_v_{d} = select i1 true, ptr %_v_{d}, ptr %_v_{d}\n", .{ dst_raw, s_raw, s_raw });
            } else if (src_is_ptr and !dst_is_ptr) {
                const dst_info = resolveIntegerInfo(emitter, unwrapped_dst) orelse
                    IntScalarInfo{ .bits = @as(u16, emitter.cfg.target.ptrBytes()) * 8, .is_signed = false };
                try state.print("  %_v_{d} = ptrtoint ptr %_v_{d} to i{d}\n", .{ dst_raw, s_raw, dst_info.bits });
            } else if (!src_is_ptr and dst_is_ptr) {
                const src_info = resolveIntegerInfo(emitter, src_ty) orelse
                    IntScalarInfo{ .bits = @as(u16, emitter.cfg.target.ptrBytes()) * 8, .is_signed = false };
                try state.print("  %_v_{d} = inttoptr i{d} %_v_{d} to ptr\n", .{ dst_raw, src_info.bits, s_raw });
            } else {
                try state.print(
                    "  %_v_{d} = select i1 true, {s} %_v_{d}, {s} %_v_{d}\n",
                    .{ dst_raw, dst_val_ty, s_raw, dst_val_ty, s_raw },
                );
            }
        },

        .ssa_discriminant => {
            if (try isZeroSizedType(emitter, src_ty)) {
                const detail_opt = try emitter.resolver.getSumDetail(src_ty);
                const d_val: u32 = if (detail_opt) |sd| sd.payload_discriminant else 0;
                const dst_info = resolveIntegerInfo(emitter, unwrapped_dst) orelse
                    IntScalarInfo{ .bits = 32, .is_signed = false };
                try state.print("  %_v_{d} = add i{d} 0, {d}\n", .{ dst_raw, dst_info.bits, d_val });
                return;
            }
            const src_lay = try emitter.resolver.resolveType(src_ty);
            const scratch = try state.allocEntryBytes(src_lay.size_bytes, src_lay.alignBytes());
            defer emitter.allocator.free(scratch);
            const src_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{s_raw});
            defer emitter.allocator.free(src_ssa);
            try emitStoreValueToPtr(emitter, state, src_ty, src_ssa, scratch, src_lay.alignBytes(), 0, 0, 0);

            if ((try emitter.resolver.getSumDetail(src_ty)) != null) {
                const disc_32 = try emitReadSumDiscriminantFromPtr(
                    emitter,
                    state,
                    src_ty,
                    scratch,
                    src_lay.alignBytes(),
                );
                defer emitter.allocator.free(disc_32);
                const dst_info = resolveIntegerInfo(emitter, unwrapped_dst) orelse
                    IntScalarInfo{ .bits = 32, .is_signed = false };
                if (dst_info.bits == 32) {
                    try state.print("  %_v_{d} = add i32 {s}, 0\n", .{ dst_raw, disc_32 });
                } else if (dst_info.bits < 32) {
                    try state.print("  %_v_{d} = trunc i32 {s} to i{d}\n", .{ dst_raw, disc_32, dst_info.bits });
                } else {
                    try state.print("  %_v_{d} = zext i32 {s} to i{d}\n", .{ dst_raw, disc_32, dst_info.bits });
                }
            } else {
                const loaded = try emitLoadValueFromPtr(
                    emitter,
                    state,
                    unwrapped_dst,
                    scratch,
                    src_lay.alignBytes(),
                    null,
                    0,
                    0,
                    0,
                );
                defer emitter.allocator.free(loaded);
                const dst_val_ty = try formatLlvmValueType(emitter, unwrapped_dst);
                defer emitter.allocator.free(dst_val_ty);
                try state.print(
                    "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                    .{ dst_raw, dst_val_ty, loaded, dst_val_ty, loaded },
                );
            }
        },

        .ssa_variant_payload => {
            if (try isZeroSizedType(emitter, unwrapped_dst)) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const src_lay = try emitter.resolver.resolveType(src_ty);
            const scratch = try state.allocEntryBytes(src_lay.size_bytes, src_lay.alignBytes());
            defer emitter.allocator.free(scratch);
            const src_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{s_raw});
            defer emitter.allocator.free(src_ssa);
            try emitStoreValueToPtr(emitter, state, src_ty, src_ssa, scratch, src_lay.alignBytes(), 0, 0, 0);

            const detail_opt = try emitter.resolver.getSumDetail(src_ty);
            const pay_off: u64 = if (detail_opt) |sd| sd.payload_offset else 0;
            _ = rhs_ord;
            const pay_ptr = if (pay_off == 0)
                try emitter.allocator.dupe(u8, scratch)
            else blk: {
                const tmp_id = state.nextTmp();
                try state.print(
                    "  %_svpp_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                    .{ tmp_id, scratch, ptr_int, pay_off },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_svpp_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(pay_ptr);

            const dst_lay = try emitter.resolver.resolveType(unwrapped_dst);
            const loaded = try emitLoadValueFromPtr(
                emitter,
                state,
                unwrapped_dst,
                pay_ptr,
                @min(src_lay.alignBytes(), effectiveOffsetAlign(pay_off, dst_lay.alignBytes())),
                null,
                0,
                0,
                0,
            );
            defer emitter.allocator.free(loaded);
            const dst_val_ty = try formatLlvmValueType(emitter, unwrapped_dst);
            defer emitter.allocator.free(dst_val_ty);
            try state.print(
                "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                .{ dst_raw, dst_val_ty, loaded, dst_val_ty, loaded },
            );
        },
    }
}

/// Emits `MirOp.aggregate_make` into `%_v_<dst_raw>` with zeroed `@zero_pad` memory semantics (`D-01`).
fn emitAggregateMakeLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body_idx: u32,
    body: *const MirBody,
    dst_raw: u32,
    kind: mir.AggregateKind,
    inst: mir.MirInst,
) !void {
    if (try isZeroSizedType(emitter, inst.type_id)) {
        try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        return;
    }
    const ptr_int = ptrIntType(emitter);
    const agg_ty = try unwrapTransparentType(emitter, inst.type_id);

    switch (kind) {
        .closure_make => {
            const key: u64 = (@as(u64, body_idx) << 32) | @as(u64, dst_raw);
            const thunk_idx = emitter.closure_thunk_map.get(key) orelse {
                try state.print(
                    "  %_v_{d} = select i1 true, {{ ptr, ptr }} zeroinitializer, {{ ptr, ptr }} zeroinitializer\n",
                    .{dst_raw},
                );
                return;
            };
            const thunk = emitter.closure_thunks.items[thunk_idx];
            var env_size: u64 = 0;
            var env_align: u32 = emitter.cfg.target.ptrBytes();
            for (thunk.capture_types) |cap_ty| {
                const cap_lay = try emitter.resolver.resolveType(cap_ty);
                if (cap_lay.size_bytes == 0) continue;
                env_align = @max(env_align, cap_lay.alignBytes());
                env_size = std.mem.alignForward(u64, env_size, @max(@as(u64, cap_lay.alignBytes()), 1));
                env_size += cap_lay.size_bytes;
            }
            const env_ptr_s = if (env_size == 0)
                try std.fmt.allocPrint(
                    emitter.allocator,
                    "inttoptr ({s} {d} to ptr)",
                    .{ ptr_int, emitter.cfg.target.ptrBytes() },
                )
            else blk: {
                const env_slot = try state.allocEntryBytes(env_size, env_align);
                try emitMemsetZero(emitter, state, env_slot, env_size, env_align);
                var cur_off: u64 = 0;
                for (thunk.capture_types, 0..) |cap_ty, cap_i| {
                    const cap_lay = try emitter.resolver.resolveType(cap_ty);
                    if (cap_lay.size_bytes == 0) continue;
                    cur_off = std.mem.alignForward(u64, cur_off, @max(@as(u64, cap_lay.alignBytes()), 1));
                    const cap_val_raw = body.extra_args.items[inst.operands.rhs + 1 + cap_i];
                    const dst_p = if (cur_off == 0)
                        try emitter.allocator.dupe(u8, env_slot)
                    else sub: {
                        const t_id = state.nextTmp();
                        try state.print(
                            "  %_cenv_p_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                            .{ t_id, env_slot, ptr_int, cur_off },
                        );
                        break :sub try std.fmt.allocPrint(emitter.allocator, "%_cenv_p_{d}", .{t_id});
                    };
                    defer emitter.allocator.free(dst_p);
                    const cap_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{cap_val_raw});
                    defer emitter.allocator.free(cap_ssa);
                    try emitStoreValueToPtr(emitter, state, cap_ty, cap_ssa, dst_p, cap_lay.alignBytes(), 0, 0, 0);
                    cur_off += cap_lay.size_bytes;
                }
                break :blk env_slot;
            };
            defer emitter.allocator.free(env_ptr_s);

            const tmp_id = state.nextTmp();
            try state.print(
                "  %_cm0_{d} = insertvalue {{ ptr, ptr }} zeroinitializer, ptr {s}, 0\n" ++
                    "  %_v_{d} = insertvalue {{ ptr, ptr }} %_cm0_{d}, ptr @_cx_cthunk_{d}, 1\n",
                .{ tmp_id, env_ptr_s, dst_raw, tmp_id, thunk_idx },
            );
            return;
        },

        .str_concat => {
            if (!emitter.declared_externs.contains("malloc")) {
                try emitter.requireIntrinsicDecl(
                    if (emitter.cfg.target.isWasm())
                        "declare ptr @malloc(i32) nounwind"
                    else
                        "declare ptr @malloc(i64) nounwind",
                );
            }
            const uadd_decl = try std.fmt.allocPrint(
                emitter.allocator,
                "declare {{ {s}, i1 }} @llvm.uadd.with.overflow.{s}({s}, {s})",
                .{ ptr_int, ptr_int, ptr_int, ptr_int },
            );
            defer emitter.allocator.free(uadd_decl);
            try emitter.requireIntrinsicDecl(uadd_decl);

            const parts = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
            const tmp_id = state.nextTmp();
            const part_ptrs = try emitter.allocator.alloc([]u8, parts.len);
            defer {
                for (part_ptrs) |ps| emitter.allocator.free(ps);
                emitter.allocator.free(part_ptrs);
            }
            const part_lens = try emitter.allocator.alloc([]u8, parts.len);
            defer {
                for (part_lens) |ls| emitter.allocator.free(ls);
                emitter.allocator.free(part_lens);
            }

            var tot_ssa = try emitter.allocator.dupe(u8, "0");
            defer emitter.allocator.free(tot_ssa);

            for (parts, 0..) |part_raw, pk| {
                const part_ty = try unwrapTransparentType(
                    emitter,
                    body.getInst(MirValueId.fromInt(part_raw)).type_id,
                );
                const sub_id = state.nextTmp();
                if (part_ty == .str_ty) {
                    try state.print(
                        "  %_scp_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 0\n" ++
                            "  %_scl_{d} = extractvalue {{ ptr, {s} }} %_v_{d}, 1\n",
                        .{ sub_id, ptr_int, part_raw, sub_id, ptr_int, part_raw },
                    );
                    part_ptrs[pk] = try std.fmt.allocPrint(emitter.allocator, "%_scp_{d}", .{sub_id});
                    part_lens[pk] = try std.fmt.allocPrint(emitter.allocator, "%_scl_{d}", .{sub_id});
                } else if (part_ty == .bool_ty) {
                    try state.print(
                        "  %_scp_{d} = select i1 %_v_{d}, ptr @.cx_str_true, ptr @.cx_str_false\n" ++
                            "  %_scl_{d} = select i1 %_v_{d}, {s} 4, {s} 5\n",
                        .{ sub_id, part_raw, sub_id, part_raw, ptr_int, ptr_int },
                    );
                    part_ptrs[pk] = try std.fmt.allocPrint(emitter.allocator, "%_scp_{d}", .{sub_id});
                    part_lens[pk] = try std.fmt.allocPrint(emitter.allocator, "%_scl_{d}", .{sub_id});
                } else if (resolveIntegerInfo(emitter, part_ty)) |p_int| {
                    const fmt_buf = try state.allocEntryBytes(64, 8);
                    if (p_int.bits == 128) {
                        if (p_int.is_signed) {
                            try ensureFmtI128Helper(emitter);
                            try state.print(
                                "  %_sccl_{d} = call i32 @_cx_rt_fmt_i128(ptr {s}, i128 %_v_{d})\n",
                                .{ sub_id, fmt_buf, part_raw },
                            );
                        } else {
                            try ensureFmtU128Helper(emitter);
                            try state.print(
                                "  %_sccl_{d} = call i32 @_cx_rt_fmt_u128(ptr {s}, i128 %_v_{d})\n",
                                .{ sub_id, fmt_buf, part_raw },
                            );
                        }
                    } else {
                        const ext_op = if (p_int.bits < 64)
                            (if (p_int.is_signed) "sext" else "zext")
                        else
                            "trunc";
                        if (p_int.bits == 64) {
                            try state.print("  %_sci64_{d} = add i64 %_v_{d}, 0\n", .{ sub_id, part_raw });
                        } else {
                            try state.print(
                                "  %_sci64_{d} = {s} i{d} %_v_{d} to i64\n",
                                .{ sub_id, ext_op, p_int.bits, part_raw },
                            );
                        }
                        const fmt_sym = if (p_int.is_signed) "@.cx_fmt_i64" else "@.cx_fmt_u64";
                        try state.print(
                            "  %_scn32_{d} = call i32 (ptr, {s}, ptr, ...) @snprintf(" ++
                                "ptr {s}, {s} 64, ptr {s}, i64 %_sci64_{d})\n" ++
                                "  %_scpos_{d} = icmp sgt i32 %_scn32_{d}, 0\n" ++
                                "  %_sccl_{d} = select i1 %_scpos_{d}, i32 %_scn32_{d}, i32 0\n",
                            .{
                                sub_id, ptr_int, fmt_buf, ptr_int, fmt_sym, sub_id,
                                sub_id, sub_id,  sub_id,  sub_id,  sub_id,
                            },
                        );
                    }
                    if (emitter.cfg.target.isWasm()) {
                        try state.print("  %_scl_{d} = add i32 %_sccl_{d}, 0\n", .{ sub_id, sub_id });
                    } else {
                        try state.print("  %_scl_{d} = zext i32 %_sccl_{d} to i64\n", .{ sub_id, sub_id });
                    }
                    part_ptrs[pk] = fmt_buf;
                    part_lens[pk] = try std.fmt.allocPrint(emitter.allocator, "%_scl_{d}", .{sub_id});
                } else {
                    part_ptrs[pk] = try std.fmt.allocPrint(emitter.allocator, "inttoptr ({s} 1 to ptr)", .{ptr_int});
                    part_lens[pk] = try emitter.allocator.dupe(u8, "0");
                }
                const add_id = state.nextTmp();
                try state.print(
                    "  %_scovp_{d} = call {{ {s}, i1 }} @llvm.uadd.with.overflow.{s}({s} {s}, {s} {s})\n" ++
                        "  %_scovf_{d} = extractvalue {{ {s}, i1 }} %_scovp_{d}, 1\n",
                    .{
                        add_id, ptr_int, ptr_int, ptr_int, tot_ssa, ptr_int, part_lens[pk],
                        add_id, ptr_int, add_id,
                    },
                );
                const ov_ssa = try std.fmt.allocPrint(emitter.allocator, "%_scovf_{d}", .{add_id});
                defer emitter.allocator.free(ov_ssa);
                try emitInlineTrapIfTrue(emitter, state, ov_ssa, 1);
                try state.print(
                    "  %_sctot_{d} = extractvalue {{ {s}, i1 }} %_scovp_{d}, 0\n",
                    .{ add_id, ptr_int, add_id },
                );
                emitter.allocator.free(tot_ssa);
                tot_ssa = try std.fmt.allocPrint(emitter.allocator, "%_sctot_{d}", .{add_id});
            }

            try state.print(
                "  %_sc_isz_{d} = icmp eq {s} {s}, 0\n" ++
                    "  br i1 %_sc_isz_{d}, label %_sc_empty_{d}, label %_sc_alloc_{d}\n" ++
                    "_sc_alloc_{d}:\n" ++
                    "  %_sc_buf_{d} = call ptr @malloc({s} {s})\n" ++
                    "  %_sc_oom_{d} = icmp eq ptr %_sc_buf_{d}, null\n",
                .{ tmp_id, ptr_int, tot_ssa, tmp_id, tmp_id, tmp_id, tmp_id, tmp_id, ptr_int, tot_ssa, tmp_id, tmp_id },
            );
            const oom_ssa = try std.fmt.allocPrint(emitter.allocator, "%_sc_oom_{d}", .{tmp_id});
            defer emitter.allocator.free(oom_ssa);
            try emitInlineTrapIfTrue(emitter, state, oom_ssa, 0);

            var cur_off_s = try emitter.allocator.dupe(u8, "0");
            defer emitter.allocator.free(cur_off_s);
            try emitter.requireIntrinsicDecl(
                "declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg)",
            );
            for (0..parts.len) |pk| {
                const cp_id = state.nextTmp();
                const len64_s = if (emitter.cfg.target.isWasm()) blk: {
                    try state.print("  %_scl64_{d} = zext i32 {s} to i64\n", .{ cp_id, part_lens[pk] });
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_scl64_{d}", .{cp_id});
                } else try emitter.allocator.dupe(u8, part_lens[pk]);
                defer emitter.allocator.free(len64_s);

                try state.print(
                    "  %_scdst_{d} = getelementptr inbounds i8, ptr %_sc_buf_{d}, {s} {s}\n" ++
                        "  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_scdst_{d}, ptr align 1 {s}, i64 {s}, i1 false)\n" ++
                        "  %_scnx_{d} = add {s} {s}, {s}\n",
                    .{
                        cp_id,   tmp_id,        ptr_int,       cur_off_s,
                        cp_id,   part_ptrs[pk], len64_s,       cp_id,
                        ptr_int, cur_off_s,     part_lens[pk],
                    },
                );
                emitter.allocator.free(cur_off_s);
                cur_off_s = try std.fmt.allocPrint(emitter.allocator, "%_scnx_{d}", .{cp_id});
            }
            const alloc_end_lbl = try emitter.allocator.dupe(u8, state.cur_label);
            defer emitter.allocator.free(alloc_end_lbl);

            try state.print(
                "  br label %_sc_done_{d}\n" ++
                    "_sc_empty_{d}:\n" ++
                    "  br label %_sc_done_{d}\n" ++
                    "_sc_done_{d}:\n" ++
                    "  %_sc_fp_{d} = phi ptr [ %_sc_buf_{d}, %{s} ], [ inttoptr ({s} 1 to ptr), %_sc_empty_{d} ]\n" ++
                    "  %_sc_f0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr %_sc_fp_{d}, 0\n" ++
                    "  %_v_{d} = insertvalue {{ ptr, {s} }} %_sc_f0_{d}, {s} {s}, 1\n",
                .{
                    tmp_id,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                    tmp_id,
                    alloc_end_lbl,
                    ptr_int,
                    tmp_id,
                    tmp_id,
                    ptr_int,
                    tmp_id,
                    dst_raw,
                    ptr_int,
                    tmp_id,
                    ptr_int,
                    tot_ssa,
                },
            );
            state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_sc_done_{d}", .{tmp_id}));
            return;
        },

        else => {},
    }

    const agg_lay = try emitter.resolver.resolveType(agg_ty);
    const scratch = try state.allocEntryBytes(agg_lay.size_bytes, agg_lay.alignBytes());
    defer emitter.allocator.free(scratch);
    try emitMemsetZero(emitter, state, scratch, agg_lay.size_bytes, agg_lay.alignBytes());

    switch (kind) {
        .tuple_agg, .struct_agg => {
            const elems = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
            if (emitter.input.pool.getNode(agg_ty).tag == .union_ty) {
                for (elems) |elem_raw| {
                    const elem_ty = body.getInst(MirValueId.fromInt(elem_raw)).type_id;
                    if (try isZeroSizedType(emitter, elem_ty)) continue;
                    const elem_lay = try emitter.resolver.resolveType(elem_ty);
                    const elem_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{elem_raw});
                    defer emitter.allocator.free(elem_ssa);
                    try emitStoreValueToPtr(
                        emitter,
                        state,
                        elem_ty,
                        elem_ssa,
                        scratch,
                        @min(agg_lay.alignBytes(), elem_lay.alignBytes()),
                        0,
                        0,
                        0,
                    );
                }
            } else {
                for (elems, 0..) |elem_raw, fld_i| {
                    const elem_ty = body.getInst(MirValueId.fromInt(elem_raw)).type_id;
                    if (try isZeroSizedType(emitter, elem_ty)) continue;
                    const fld = (try emitter.resolver.getFieldByDeclOrdinal(agg_ty, @intCast(fld_i))) orelse continue;
                    const fld_ptr = if (fld.byte_offset == 0)
                        try emitter.allocator.dupe(u8, scratch)
                    else blk: {
                        const tmp_id = state.nextTmp();
                        try state.print(
                            "  %_agp_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                            .{ tmp_id, scratch, ptr_int, fld.byte_offset },
                        );
                        break :blk try std.fmt.allocPrint(emitter.allocator, "%_agp_{d}", .{tmp_id});
                    };
                    defer emitter.allocator.free(fld_ptr);
                    const elem_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{elem_raw});
                    defer emitter.allocator.free(elem_ssa);
                    const nat_align = @as(u32, 1) << @intCast(fld.align_log2);
                    const fld_align = if (agg_lay.reprFlags().is_packed)
                        1
                    else
                        @min(agg_lay.alignBytes(), effectiveOffsetAlign(fld.byte_offset, nat_align));
                    try emitStoreValueToPtr(
                        emitter,
                        state,
                        elem_ty,
                        elem_ssa,
                        fld_ptr,
                        fld_align,
                        0,
                        0,
                        0,
                    );
                }
            }
        },

        .array_elems => {
            const elems = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
            const arr_node = emitter.input.pool.getNode(agg_ty);
            if (arr_node.tag == .soa_array_ty) {
                const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(arr_node.lhs));
                const st_lay = try emitter.resolver.resolveType(elem_struct);
                const cap: u64 = arr_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                const elem_scratch = try state.allocEntryBytes(st_lay.size_bytes, st_lay.alignBytes());
                defer emitter.allocator.free(elem_scratch);

                for (elems, 0..) |elem_raw, elem_i| {
                    const elem_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{elem_raw});
                    defer emitter.allocator.free(elem_ssa);
                    try emitStoreValueToPtr(
                        emitter,
                        state,
                        elem_struct,
                        elem_ssa,
                        elem_scratch,
                        st_lay.alignBytes(),
                        0,
                        0,
                        0,
                    );
                    var fld_ord: u32 = 0;
                    while (fld_ord < st_lay.aux_len) : (fld_ord += 1) {
                        const fld = emitter.resolver.fields_by_decl.items[st_lay.aux_start + fld_ord];
                        if (fld.size_bytes == 0) continue;
                        const col = emitter.resolver.getSoaColumnOffset(elem_struct, fld_ord, cap).?;
                        const f_lay = try emitter.resolver.resolveType(fld.field_ty);
                        const src_fp = if (fld.byte_offset == 0)
                            try emitter.allocator.dupe(u8, elem_scratch)
                        else blk: {
                            const t_id = state.nextTmp();
                            try state.print(
                                "  %_aes_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                                .{ t_id, elem_scratch, ptr_int, fld.byte_offset },
                            );
                            break :blk try std.fmt.allocPrint(emitter.allocator, "%_aes_{d}", .{t_id});
                        };
                        defer emitter.allocator.free(src_fp);
                        const src_align = if (st_lay.reprFlags().is_packed)
                            1
                        else
                            @min(st_lay.alignBytes(), effectiveOffsetAlign(fld.byte_offset, f_lay.alignBytes()));
                        const f_val = try emitLoadValueFromPtr(
                            emitter,
                            state,
                            fld.field_ty,
                            src_fp,
                            src_align,
                            null,
                            0,
                            0,
                            0,
                        );
                        defer emitter.allocator.free(f_val);

                        const dst_off = col.byte_offset + @as(u64, elem_i) * f_lay.stride_bytes;
                        const t_id = state.nextTmp();
                        try state.print(
                            "  %_aed_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                            .{ t_id, scratch, ptr_int, dst_off },
                        );
                        const dst_fp = try std.fmt.allocPrint(emitter.allocator, "%_aed_{d}", .{t_id});
                        defer emitter.allocator.free(dst_fp);
                        const dst_align = @min(
                            agg_lay.alignBytes(),
                            effectiveOffsetAlign(dst_off, f_lay.alignBytes()),
                        );
                        try emitStoreValueToPtr(emitter, state, fld.field_ty, f_val, dst_fp, dst_align, 0, 0, 0);
                    }
                }
            } else {
                for (elems, 0..) |elem_raw, elem_i| {
                    const elem_ty = body.getInst(MirValueId.fromInt(elem_raw)).type_id;
                    if (try isZeroSizedType(emitter, elem_ty)) continue;
                    const elem_lay = try emitter.resolver.resolveType(elem_ty);
                    const off = @as(u64, elem_i) * elem_lay.stride_bytes;
                    const dst_p = if (off == 0)
                        try emitter.allocator.dupe(u8, scratch)
                    else blk: {
                        const t_id = state.nextTmp();
                        try state.print(
                            "  %_aep2_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                            .{ t_id, scratch, ptr_int, off },
                        );
                        break :blk try std.fmt.allocPrint(emitter.allocator, "%_aep2_{d}", .{t_id});
                    };
                    defer emitter.allocator.free(dst_p);
                    const elem_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{elem_raw});
                    defer emitter.allocator.free(elem_ssa);
                    const dst_align = @min(
                        agg_lay.alignBytes(),
                        effectiveOffsetAlign(off, elem_lay.alignBytes()),
                    );
                    try emitStoreValueToPtr(emitter, state, elem_ty, elem_ssa, dst_p, dst_align, 0, 0, 0);
                }
            }
        },

        .array_repeat => {
            const elem_raw = inst.operands.lhs;
            const rep_count: u64 = inst.operands.rhs;
            const elem_ty = body.getInst(MirValueId.fromInt(elem_raw)).type_id;
            if (rep_count > 0 and !(try isZeroSizedType(emitter, elem_ty))) {
                const arr_node = emitter.input.pool.getNode(agg_ty);
                const loop_id = state.nextTmp();
                const pre_lbl = try emitter.allocator.dupe(u8, state.cur_label);
                defer emitter.allocator.free(pre_lbl);

                if (arr_node.tag == .soa_array_ty) {
                    const elem_struct = emitter.input.pool.unwrapUnderlyingType(TypeId.fromInt(arr_node.lhs));
                    const st_lay = try emitter.resolver.resolveType(elem_struct);
                    const elem_scratch = try state.allocEntryBytes(st_lay.size_bytes, st_lay.alignBytes());
                    defer emitter.allocator.free(elem_scratch);
                    const elem_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{elem_raw});
                    defer emitter.allocator.free(elem_ssa);
                    try emitStoreValueToPtr(
                        emitter,
                        state,
                        elem_struct,
                        elem_ssa,
                        elem_scratch,
                        st_lay.alignBytes(),
                        0,
                        0,
                        0,
                    );

                    try state.print(
                        "  br label %_rep_hdr_{d}\n" ++
                            "_rep_hdr_{d}:\n" ++
                            "  %_rep_i_{d} = phi {s} [ 0, %{s} ], [ %_rep_nx_{d}, %_rep_body_{d} ]\n" ++
                            "  %_rep_c_{d} = icmp ult {s} %_rep_i_{d}, {d}\n" ++
                            "  br i1 %_rep_c_{d}, label %_rep_body_{d}, label %_rep_end_{d}\n" ++
                            "_rep_body_{d}:\n",
                        .{
                            loop_id,   loop_id,
                            loop_id,   ptr_int,
                            pre_lbl,   loop_id,
                            loop_id,   loop_id,
                            ptr_int,   loop_id,
                            rep_count, loop_id,
                            loop_id,   loop_id,
                            loop_id,
                        },
                    );
                    var fld_ord: u32 = 0;
                    while (fld_ord < st_lay.aux_len) : (fld_ord += 1) {
                        const fld = emitter.resolver.fields_by_decl.items[st_lay.aux_start + fld_ord];
                        if (fld.size_bytes == 0) continue;
                        const col = emitter.resolver.getSoaColumnOffset(elem_struct, fld_ord, rep_count).?;
                        const f_lay = try emitter.resolver.resolveType(fld.field_ty);
                        const sub_id = state.nextTmp();
                        try state.print(
                            "  %_rfs_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                            .{ sub_id, elem_scratch, ptr_int, fld.byte_offset },
                        );
                        const s_fp = try std.fmt.allocPrint(emitter.allocator, "%_rfs_{d}", .{sub_id});
                        defer emitter.allocator.free(s_fp);
                        const src_align = if (st_lay.reprFlags().is_packed)
                            1
                        else
                            @min(st_lay.alignBytes(), effectiveOffsetAlign(fld.byte_offset, f_lay.alignBytes()));
                        const f_val = try emitLoadValueFromPtr(
                            emitter,
                            state,
                            fld.field_ty,
                            s_fp,
                            src_align,
                            null,
                            0,
                            0,
                            0,
                        );
                        defer emitter.allocator.free(f_val);
                        try state.print(
                            "  %_rfo_{d} = mul {s} %_rep_i_{d}, {d}\n" ++
                                "  %_rfa_{d} = add {s} %_rfo_{d}, {d}\n" ++
                                "  %_rfd_{d} = getelementptr inbounds i8, ptr {s}, {s} %_rfa_{d}\n",
                            .{
                                sub_id, ptr_int, loop_id, f_lay.stride_bytes,
                                sub_id, ptr_int, sub_id,  col.byte_offset,
                                sub_id, scratch, ptr_int, sub_id,
                            },
                        );
                        const d_fp = try std.fmt.allocPrint(emitter.allocator, "%_rfd_{d}", .{sub_id});
                        defer emitter.allocator.free(d_fp);
                        const dst_align = @min(
                            agg_lay.alignBytes(),
                            effectiveOffsetAlign(col.byte_offset, f_lay.alignBytes()),
                        );
                        try emitStoreValueToPtr(emitter, state, fld.field_ty, f_val, d_fp, dst_align, 0, 0, 0);
                    }
                    try state.print(
                        "  %_rep_nx_{d} = add {s} %_rep_i_{d}, 1\n" ++
                            "  br label %_rep_hdr_{d}\n" ++
                            "_rep_end_{d}:\n",
                        .{ loop_id, ptr_int, loop_id, loop_id, loop_id },
                    );
                } else {
                    const elem_lay = try emitter.resolver.resolveType(elem_ty);
                    try state.print(
                        "  br label %_rep_hdr_{d}\n" ++
                            "_rep_hdr_{d}:\n" ++
                            "  %_rep_i_{d} = phi {s} [ 0, %{s} ], [ %_rep_nx_{d}, %_rep_body_{d} ]\n" ++
                            "  %_rep_c_{d} = icmp ult {s} %_rep_i_{d}, {d}\n" ++
                            "  br i1 %_rep_c_{d}, label %_rep_body_{d}, label %_rep_end_{d}\n" ++
                            "_rep_body_{d}:\n" ++
                            "  %_rep_bo_{d} = mul {s} %_rep_i_{d}, {d}\n" ++
                            "  %_rep_dp_{d} = getelementptr inbounds i8, ptr {s}, {s} %_rep_bo_{d}\n",
                        .{
                            loop_id,               loop_id,
                            loop_id,               ptr_int,
                            pre_lbl,               loop_id,
                            loop_id,               loop_id,
                            ptr_int,               loop_id,
                            rep_count,             loop_id,
                            loop_id,               loop_id,
                            loop_id,               loop_id,
                            ptr_int,               loop_id,
                            elem_lay.stride_bytes, loop_id,
                            scratch,               ptr_int,
                            loop_id,
                        },
                    );
                    const dp_s = try std.fmt.allocPrint(emitter.allocator, "%_rep_dp_{d}", .{loop_id});
                    defer emitter.allocator.free(dp_s);
                    const elem_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{elem_raw});
                    defer emitter.allocator.free(elem_ssa);
                    const dst_align = @min(
                        agg_lay.alignBytes(),
                        effectiveOffsetAlign(elem_lay.stride_bytes, elem_lay.alignBytes()),
                    );
                    try emitStoreValueToPtr(emitter, state, elem_ty, elem_ssa, dp_s, dst_align, 0, 0, 0);
                    try state.print(
                        "  %_rep_nx_{d} = add {s} %_rep_i_{d}, 1\n" ++
                            "  br label %_rep_hdr_{d}\n" ++
                            "_rep_end_{d}:\n",
                        .{ loop_id, ptr_int, loop_id, loop_id, loop_id },
                    );
                }
                state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_rep_end_{d}", .{loop_id}));
            }
        },

        .tagged_variant => {
            const tag_ord: u32 = inst.operands.rhs >> 16;
            const arg_len: u32 = inst.operands.rhs & 0xFFFF;
            const args = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + arg_len];
            if (try emitter.resolver.getSumDetail(agg_ty)) |sum_detail| {
                const var_pay_ty = try unwrapTransparentType(
                    emitter,
                    resolveEnumVariantPayloadType(emitter, agg_ty, tag_ord),
                );
                if (arg_len > 0 and !(try isZeroSizedType(emitter, var_pay_ty))) {
                    const pay_ptr = if (sum_detail.payload_offset == 0)
                        try emitter.allocator.dupe(u8, scratch)
                    else blk: {
                        const tmp_id = state.nextTmp();
                        try state.print(
                            "  %_tvp_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                            .{ tmp_id, scratch, ptr_int, sum_detail.payload_offset },
                        );
                        break :blk try std.fmt.allocPrint(emitter.allocator, "%_tvp_{d}", .{tmp_id});
                    };
                    defer emitter.allocator.free(pay_ptr);

                    if (arg_len == 1 and
                        (try unwrapTransparentType(
                            emitter,
                            body.getInst(MirValueId.fromInt(args[0])).type_id,
                        )) == var_pay_ty)
                    {
                        const pay_lay = try emitter.resolver.resolveType(var_pay_ty);
                        const arg_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{args[0]});
                        defer emitter.allocator.free(arg_ssa);
                        try emitStoreValueToPtr(
                            emitter,
                            state,
                            var_pay_ty,
                            arg_ssa,
                            pay_ptr,
                            @min(
                                agg_lay.alignBytes(),
                                effectiveOffsetAlign(sum_detail.payload_offset, pay_lay.alignBytes()),
                            ),
                            0,
                            0,
                            0,
                        );
                    } else {
                        for (args, 0..) |sub_raw, sub_i| {
                            const sub_ty = body.getInst(MirValueId.fromInt(sub_raw)).type_id;
                            if (try isZeroSizedType(emitter, sub_ty)) continue;
                            const fld = (try emitter.resolver.getFieldByDeclOrdinal(var_pay_ty, @intCast(sub_i))) orelse
                                continue;
                            const sub_ptr = if (fld.byte_offset == 0)
                                try emitter.allocator.dupe(u8, pay_ptr)
                            else blk: {
                                const tmp_id = state.nextTmp();
                                try state.print(
                                    "  %_tvsp_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                                    .{ tmp_id, pay_ptr, ptr_int, fld.byte_offset },
                                );
                                break :blk try std.fmt.allocPrint(emitter.allocator, "%_tvsp_{d}", .{tmp_id});
                            };
                            defer emitter.allocator.free(sub_ptr);
                            const sub_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{sub_raw});
                            defer emitter.allocator.free(sub_ssa);
                            const total_off = sum_detail.payload_offset + fld.byte_offset;
                            const nat_align = @as(u32, 1) << @intCast(fld.align_log2);
                            try emitStoreValueToPtr(
                                emitter,
                                state,
                                sub_ty,
                                sub_ssa,
                                sub_ptr,
                                @min(agg_lay.alignBytes(), effectiveOffsetAlign(total_off, nat_align)),
                                0,
                                0,
                                0,
                            );
                        }
                    }
                }
                try emitWriteSumDiscriminantToPtr(
                    emitter,
                    state,
                    agg_ty,
                    scratch,
                    agg_lay.alignBytes(),
                    tag_ord,
                );
            } else if (resolveIntegerInfo(emitter, agg_ty)) |enum_int| {
                try state.print("  %_v_{d} = add i{d} 0, {d}\n", .{ dst_raw, enum_int.bits, tag_ord });
                return;
            }
        },

        .closure_make, .str_concat => unreachable,
    }

    const loaded = try emitLoadValueFromPtr(emitter, state, agg_ty, scratch, agg_lay.alignBytes(), null, 0, 0, 0);
    defer emitter.allocator.free(loaded);
    const val_ty = try formatLlvmValueType(emitter, agg_ty);
    defer emitter.allocator.free(val_ty);
    try state.print(
        "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
        .{ dst_raw, val_ty, loaded, val_ty, loaded },
    );
}

/// Emits `MirOp.intrinsic_op` across all 38 surface and internal intrinsics (`DR-19`, `phase7_spec.md` §3).
fn emitIntrinsicOpLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body: *const MirBody,
    bb_idx: u32,
    dst_raw: u32,
    ikind: mir.MirIntrinsicKind,
    inst: mir.MirInst,
) !void {
    const ptr_int = ptrIntType(emitter);
    const access_grp = if (bb_idx < state.block_access_group.len) state.block_access_group[bb_idx] else 0;
    const args: []const u32 = if (ikind.hasExtraArgs() and inst.operands.rhs > 0)
        body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]
    else
        &.{};

    switch (ikind) {
        .compile_assert => {
            if (args.len >= 1) {
                const tmp_id = state.nextTmp();
                try state.print("  %_ca_bad_{d} = xor i1 %_v_{d}, true\n", .{ tmp_id, args[0] });
                const bad_ssa = try std.fmt.allocPrint(emitter.allocator, "%_ca_bad_{d}", .{tmp_id});
                defer emitter.allocator.free(bad_ssa);
                try emitInlineTrapIfTrue(emitter, state, bad_ssa, 3);
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
            } else {
                try state.writeAll("  call void @_cx_rt_trap(i32 3)\n");
                try emitUnreachableAndDeadBlock(emitter, state, dst_raw);
            }
        },

        .compile_error, .abort_vacated_panic, .embed_bytes => {
            const reason: u32 = if (ikind == .embed_bytes) 0 else 3;
            try state.print("  call void @_cx_rt_trap(i32 {d})\n", .{reason});
            try emitUnreachableAndDeadBlock(emitter, state, dst_raw);
        },

        .derive_debug_fmt => {
            if (args.len >= 1) {
                var name_buf: [256]u8 = undefined;
                const arg_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
                const rendered = emitter.input.pool.formatType(arg_ty, emitter.input.sym_table, &name_buf);
                if (rendered.len == 0) {
                    const tmp_id = state.nextTmp();
                    try state.print(
                        "  %_ddf0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr inttoptr ({s} 1 to ptr), 0\n" ++
                            "  %_v_{d} = insertvalue {{ ptr, {s} }} %_ddf0_{d}, {s} 0, 1\n",
                        .{ tmp_id, ptr_int, ptr_int, dst_raw, ptr_int, tmp_id, ptr_int },
                    );
                } else {
                    const sid = emitter.nextSynthGlobalId();
                    const hdr_s = try std.fmt.allocPrint(
                        emitter.allocator,
                        "@_cx_dbg_{d} = private unnamed_addr constant [{d} x i8] ",
                        .{ sid, rendered.len },
                    );
                    defer emitter.allocator.free(hdr_s);
                    try emitter.synth_globals.appendSlice(emitter.allocator, hdr_s);
                    try appendByteStringLiteralToBuf(emitter.allocator, &emitter.synth_globals, rendered);
                    try emitter.synth_globals.appendSlice(emitter.allocator, ", align 1\n");
                    const tmp_id = state.nextTmp();
                    try state.print(
                        "  %_ddf0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr @_cx_dbg_{d}, 0\n" ++
                            "  %_v_{d} = insertvalue {{ ptr, {s} }} %_ddf0_{d}, {s} {d}, 1\n",
                        .{ tmp_id, ptr_int, sid, dst_raw, ptr_int, tmp_id, ptr_int, rendered.len },
                    );
                }
            } else {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
            }
        },

        .size_of => {
            const refl_lay = try emitter.resolver.resolveType(TypeId.fromInt(inst.operands.lhs));
            const dst_info = resolveIntegerInfo(emitter, inst.type_id) orelse
                IntScalarInfo{ .bits = @as(u16, emitter.cfg.target.ptrBytes()) * 8, .is_signed = false };
            try state.print("  %_v_{d} = add i{d} 0, {d}\n", .{ dst_raw, dst_info.bits, refl_lay.size_bytes });
        },

        .align_of => {
            const refl_lay = try emitter.resolver.resolveType(TypeId.fromInt(inst.operands.lhs));
            const dst_info = resolveIntegerInfo(emitter, inst.type_id) orelse
                IntScalarInfo{ .bits = @as(u16, emitter.cfg.target.ptrBytes()) * 8, .is_signed = false };
            try state.print("  %_v_{d} = add i{d} 0, {d}\n", .{ dst_raw, dst_info.bits, refl_lay.alignBytes() });
        },

        .type_name => {
            const refl_ty = TypeId.fromInt(inst.operands.lhs);
            var name_buf: [512]u8 = undefined;
            const rendered = emitter.input.pool.formatType(refl_ty, emitter.input.sym_table, &name_buf);
            const tmp_id = state.nextTmp();
            if (rendered.len == 0) {
                try state.print(
                    "  %_tn0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr inttoptr ({s} 1 to ptr), 0\n" ++
                        "  %_v_{d} = insertvalue {{ ptr, {s} }} %_tn0_{d}, {s} 0, 1\n",
                    .{ tmp_id, ptr_int, ptr_int, dst_raw, ptr_int, tmp_id, ptr_int },
                );
            } else {
                try state.print(
                    "  %_tn0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr @_cx_tyname_{d}, 0\n" ++
                        "  %_v_{d} = insertvalue {{ ptr, {s} }} %_tn0_{d}, {s} {d}, 1\n",
                    .{ tmp_id, ptr_int, refl_ty.toU32(), dst_raw, ptr_int, tmp_id, ptr_int, rendered.len },
                );
            }
        },

        .as_bytes => {
            if (args.len < 1) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const ref_val = MirValueId.fromInt(args[0]);
            const ref_ty = try unwrapTransparentType(emitter, body.getInst(ref_val).type_id);
            const ref_node = emitter.input.pool.getNode(ref_ty);
            const is_ptr_src = ref_node.tag == .ref_ty or ref_node.tag == .mut_ref_ty or ref_node.tag == .raw_ptr_ty;
            const val_ty = if (is_ptr_src)
                try unwrapTransparentType(emitter, TypeId.fromInt(ref_node.lhs))
            else
                ref_ty;
            const val_lay = try emitter.resolver.resolveType(val_ty);

            const data_ptr_s = if (val_lay.size_bytes == 0)
                try std.fmt.allocPrint(emitter.allocator, "inttoptr ({s} 1 to ptr)", .{ptr_int})
            else if (is_ptr_src)
                try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{args[0]})
            else blk: {
                const scratch = try state.allocEntryBytes(val_lay.size_bytes, val_lay.alignBytes());
                const src_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{args[0]});
                defer emitter.allocator.free(src_ssa);
                try emitStoreValueToPtr(emitter, state, val_ty, src_ssa, scratch, val_lay.alignBytes(), 0, 0, 0);
                break :blk scratch;
            };
            defer emitter.allocator.free(data_ptr_s);

            const dst_unwrapped = try unwrapTransparentType(emitter, inst.type_id);
            const dst_node = emitter.input.pool.getNode(dst_unwrapped);
            const tmp_id = state.nextTmp();
            if (dst_node.tag == .ref_ty or dst_node.tag == .mut_ref_ty or dst_node.tag == .raw_ptr_ty) {
                const fat_slot = try state.allocEntryBytes(
                    2 * emitter.cfg.target.ptrBytes(),
                    emitter.cfg.target.ptrBytes(),
                );
                defer emitter.allocator.free(fat_slot);
                try state.print(
                    "  store ptr {s}, ptr {s}, align {d}\n" ++
                        "  %_ab_lp_{d} = getelementptr inbounds {{ ptr, {s} }}, ptr {s}, i32 0, i32 1\n" ++
                        "  store {s} {d}, ptr %_ab_lp_{d}, align {d}\n" ++
                        "  %_v_{d} = select i1 true, ptr {s}, ptr {s}\n",
                    .{
                        data_ptr_s,
                        fat_slot,
                        emitter.cfg.target.ptrBytes(),
                        tmp_id,
                        ptr_int,
                        fat_slot,
                        ptr_int,
                        val_lay.size_bytes,
                        tmp_id,
                        emitter.cfg.target.ptrBytes(),
                        dst_raw,
                        fat_slot,
                        fat_slot,
                    },
                );
            } else {
                try state.print(
                    "  %_ab0_{d} = insertvalue {{ ptr, {s} }} zeroinitializer, ptr {s}, 0\n" ++
                        "  %_v_{d} = insertvalue {{ ptr, {s} }} %_ab0_{d}, {s} {d}, 1\n",
                    .{ tmp_id, ptr_int, data_ptr_s, dst_raw, ptr_int, tmp_id, ptr_int, val_lay.size_bytes },
                );
            }
        },

        .bit_cast => {
            if (args.len < 1 or (try isZeroSizedType(emitter, inst.type_id))) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const src_ty = try unwrapTransparentType(emitter, body.getInst(MirValueId.fromInt(args[0])).type_id);
            const dst_ty = try unwrapTransparentType(emitter, inst.type_id);
            const src_lay = try emitter.resolver.resolveType(src_ty);
            const dst_lay = try emitter.resolver.resolveType(dst_ty);
            const max_sz = @max(src_lay.size_bytes, dst_lay.size_bytes);
            const max_al = @max(src_lay.alignBytes(), dst_lay.alignBytes());
            const scratch = try state.allocEntryBytes(max_sz, max_al);
            defer emitter.allocator.free(scratch);
            try emitMemsetZero(emitter, state, scratch, max_sz, max_al);
            const src_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{args[0]});
            defer emitter.allocator.free(src_ssa);
            try emitStoreValueToPtr(emitter, state, src_ty, src_ssa, scratch, src_lay.alignBytes(), 0, 0, 0);
            const loaded = try emitLoadValueFromPtr(emitter, state, dst_ty, scratch, dst_lay.alignBytes(), null, 0, 0, 0);
            defer emitter.allocator.free(loaded);
            const dst_val_ty = try formatLlvmValueType(emitter, dst_ty);
            defer emitter.allocator.free(dst_val_ty);
            try state.print(
                "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                .{ dst_raw, dst_val_ty, loaded, dst_val_ty, loaded },
            );
        },

        .from_bytes, .view_bytes => {
            if (args.len < 1 or (try isZeroSizedType(emitter, inst.type_id))) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const is_view = ikind == .view_bytes;
            const span_s = try emitExtractByteSpanLlvm(emitter, state, body, MirValueId.fromInt(args[0]));
            defer emitter.allocator.free(span_s.ptr_ssa);
            defer emitter.allocator.free(span_s.len_ssa);

            const opt_ty = try unwrapTransparentType(emitter, inst.type_id);
            const opt_lay = try emitter.resolver.resolveType(opt_ty);
            const opt_node = emitter.input.pool.getNode(opt_ty);
            const some_pay_ty = try unwrapTransparentType(emitter, TypeId.fromInt(opt_node.lhs));
            const some_node = emitter.input.pool.getNode(some_pay_ty);
            const target_ty = if (is_view and
                (some_node.tag == .ref_ty or some_node.tag == .mut_ref_ty or some_node.tag == .raw_ptr_ty))
                try unwrapTransparentType(emitter, TypeId.fromInt(some_node.lhs))
            else
                some_pay_ty;
            const target_lay = try emitter.resolver.resolveType(target_ty);
            const sum_detail = (try emitter.resolver.getSumDetail(opt_ty)) orelse {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            };

            const out_slot = try state.allocEntryBytes(opt_lay.size_bytes, opt_lay.alignBytes());
            defer emitter.allocator.free(out_slot);
            try emitMemsetZero(emitter, state, out_slot, opt_lay.size_bytes, opt_lay.alignBytes());

            const tmp_id = state.nextTmp();
            if (is_view) {
                try state.print(
                    "  %_vw_sz_{d} = icmp eq {s} {s}, {d}\n" ++
                        "  %_vw_nn_{d} = icmp ne ptr {s}, null\n" ++
                        "  %_vw_pi_{d} = ptrtoint ptr {s} to {s}\n" ++
                        "  %_vw_am_{d} = and {s} %_vw_pi_{d}, {d}\n" ++
                        "  %_vw_al_{d} = icmp eq {s} %_vw_am_{d}, 0\n" ++
                        "  %_vw_c1_{d} = and i1 %_vw_sz_{d}, %_vw_nn_{d}\n" ++
                        "  %_vw_ok_{d} = and i1 %_vw_c1_{d}, %_vw_al_{d}\n",
                    .{
                        tmp_id,                      ptr_int,        span_s.len_ssa, target_lay.size_bytes,
                        tmp_id,                      span_s.ptr_ssa, tmp_id,         span_s.ptr_ssa,
                        ptr_int,                     tmp_id,         ptr_int,        tmp_id,
                        target_lay.alignBytes() - 1, tmp_id,         ptr_int,        tmp_id,
                        tmp_id,                      tmp_id,         tmp_id,         tmp_id,
                        tmp_id,                      tmp_id,
                    },
                );
            } else {
                try state.print(
                    "  %_vw_ok_{d} = icmp eq {s} {s}, {d}\n",
                    .{ tmp_id, ptr_int, span_s.len_ssa, target_lay.size_bytes },
                );
            }

            try state.print(
                "  br i1 %_vw_ok_{d}, label %_fb_some_{d}, label %_fb_none_{d}\n" ++
                    "_fb_some_{d}:\n",
                .{ tmp_id, tmp_id, tmp_id, tmp_id },
            );
            const pay_ptr = if (sum_detail.payload_offset == 0)
                try emitter.allocator.dupe(u8, out_slot)
            else blk: {
                try state.print(
                    "  %_fb_pp_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                    .{ tmp_id, out_slot, ptr_int, sum_detail.payload_offset },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_fb_pp_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(pay_ptr);

            if (is_view) {
                if (!(try isZeroSizedType(emitter, some_pay_ty))) {
                    try emitStoreValueToPtr(
                        emitter,
                        state,
                        some_pay_ty,
                        span_s.ptr_ssa,
                        pay_ptr,
                        @min(opt_lay.alignBytes(), emitter.cfg.target.ptrBytes()),
                        0,
                        0,
                        0,
                    );
                }
            } else if (target_lay.size_bytes > 0) {
                try emitMemcpyBytes(emitter, state, pay_ptr, 1, span_s.ptr_ssa, 1, target_lay.size_bytes);
            }
            try emitWriteSumDiscriminantToPtr(emitter, state, opt_ty, out_slot, opt_lay.alignBytes(), 1);
            try state.print("  br label %_fb_join_{d}\n_fb_none_{d}:\n", .{ tmp_id, tmp_id });
            try emitWriteSumDiscriminantToPtr(emitter, state, opt_ty, out_slot, opt_lay.alignBytes(), 0);
            try state.print("  br label %_fb_join_{d}\n_fb_join_{d}:\n", .{ tmp_id, tmp_id });
            state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_fb_join_{d}", .{tmp_id}));

            const loaded = try emitLoadValueFromPtr(emitter, state, opt_ty, out_slot, opt_lay.alignBytes(), null, 0, 0, 0);
            defer emitter.allocator.free(loaded);
            const opt_val_ty = try formatLlvmValueType(emitter, opt_ty);
            defer emitter.allocator.free(opt_val_ty);
            try state.print(
                "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                .{ dst_raw, opt_val_ty, loaded, opt_val_ty, loaded },
            );
        },

        .drop_trace => {
            if (args.len >= 1) {
                const id_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
                const id_info = resolveIntegerInfo(emitter, id_ty) orelse
                    IntScalarInfo{ .bits = 64, .is_signed = true };
                const tmp_id = state.nextTmp();
                if (id_info.bits == 64) {
                    try state.print("  %_dt_i64_{d} = add i64 %_v_{d}, 0\n", .{ tmp_id, args[0] });
                } else if (id_info.bits < 64) {
                    const ext_s = if (id_info.is_signed) "sext" else "zext";
                    try state.print(
                        "  %_dt_i64_{d} = {s} i{d} %_v_{d} to i64\n",
                        .{ tmp_id, ext_s, id_info.bits, args[0] },
                    );
                } else {
                    try state.print("  %_dt_i64_{d} = trunc i128 %_v_{d} to i64\n", .{ tmp_id, args[0] });
                }
                const buf_s = try state.allocEntryBytes(64, 8);
                defer emitter.allocator.free(buf_s);
                try state.print(
                    "  %_dt_n32_{d} = call i32 (ptr, {s}, ptr, ...) @snprintf(" ++
                        "ptr {s}, {s} 64, ptr @.cx_fmt_drop, i64 %_dt_i64_{d})\n" ++
                        "  %_dt_ok_{d} = icmp sgt i32 %_dt_n32_{d}, 0\n" ++
                        "  %_dt_cl_{d} = select i1 %_dt_ok_{d}, i32 %_dt_n32_{d}, i32 0\n",
                    .{
                        tmp_id, ptr_int, buf_s,  ptr_int, tmp_id,
                        tmp_id, tmp_id,  tmp_id, tmp_id,  tmp_id,
                    },
                );
                if (emitter.cfg.target.isWasm()) {
                    try state.print(
                        "  call void @_cx_rt_trace_append(ptr {s}, i32 %_dt_cl_{d})\n",
                        .{ buf_s, tmp_id },
                    );
                } else {
                    try state.print(
                        "  %_dt_ln_{d} = zext i32 %_dt_cl_{d} to i64\n" ++
                            "  call void @_cx_rt_trace_append(ptr {s}, i64 %_dt_ln_{d})\n",
                        .{ tmp_id, tmp_id, buf_s, tmp_id },
                    );
                }
            }
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        },

        .bounds_check => {
            if (args.len >= 2) {
                const idx_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
                const idx_info = resolveIntegerInfo(emitter, idx_ty) orelse
                    IntScalarInfo{ .bits = 64, .is_signed = false };
                if (idx_info.is_signed) {
                    const neg_id = state.nextTmp();
                    try state.print("  %_bc_neg_{d} = icmp slt i{d} %_v_{d}, 0\n", .{ neg_id, idx_info.bits, args[0] });
                    const neg_s = try std.fmt.allocPrint(emitter.allocator, "%_bc_neg_{d}", .{neg_id});
                    defer emitter.allocator.free(neg_s);
                    try emitInlineTrapIfTrue(emitter, state, neg_s, 2);
                }
                const idx_u = try emitExtendIntToI128(emitter, state, args[0], idx_ty, true);
                defer emitter.allocator.free(idx_u);
                const len_ty = body.getInst(MirValueId.fromInt(args[1])).type_id;
                const len_u = try emitExtendIntToI128(emitter, state, args[1], len_ty, true);
                defer emitter.allocator.free(len_u);
                const cmp_id = state.nextTmp();
                try state.print("  %_bc_ge_{d} = icmp uge i128 {s}, {s}\n", .{ cmp_id, idx_u, len_u });
                const ge_s = try std.fmt.allocPrint(emitter.allocator, "%_bc_ge_{d}", .{cmp_id});
                defer emitter.allocator.free(ge_s);
                try emitInlineTrapIfTrue(emitter, state, ge_s, 2);
            }
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        },

        .slice_range_check => {
            if (args.len >= 3) {
                const lo_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
                const hi_ty = body.getInst(MirValueId.fromInt(args[1])).type_id;
                const len_ty = body.getInst(MirValueId.fromInt(args[2])).type_id;
                if (resolveIntegerInfo(emitter, lo_ty)) |lo_i| {
                    if (lo_i.is_signed) {
                        const nid = state.nextTmp();
                        try state.print("  %_sr_ln_{d} = icmp slt i{d} %_v_{d}, 0\n", .{ nid, lo_i.bits, args[0] });
                        const ns = try std.fmt.allocPrint(emitter.allocator, "%_sr_ln_{d}", .{nid});
                        defer emitter.allocator.free(ns);
                        try emitInlineTrapIfTrue(emitter, state, ns, 2);
                    }
                }
                if (resolveIntegerInfo(emitter, hi_ty)) |hi_i| {
                    if (hi_i.is_signed) {
                        const nid = state.nextTmp();
                        try state.print("  %_sr_hn_{d} = icmp slt i{d} %_v_{d}, 0\n", .{ nid, hi_i.bits, args[1] });
                        const ns = try std.fmt.allocPrint(emitter.allocator, "%_sr_hn_{d}", .{nid});
                        defer emitter.allocator.free(ns);
                        try emitInlineTrapIfTrue(emitter, state, ns, 2);
                    }
                }
                const lo_u = try emitExtendIntToI128(emitter, state, args[0], lo_ty, true);
                defer emitter.allocator.free(lo_u);
                const hi_u = try emitExtendIntToI128(emitter, state, args[1], hi_ty, true);
                defer emitter.allocator.free(hi_u);
                const len_u = try emitExtendIntToI128(emitter, state, args[2], len_ty, true);
                defer emitter.allocator.free(len_u);
                const cid = state.nextTmp();
                try state.print(
                    "  %_sr_c1_{d} = icmp ugt i128 {s}, {s}\n" ++
                        "  %_sr_c2_{d} = icmp ugt i128 {s}, {s}\n" ++
                        "  %_sr_bad_{d} = or i1 %_sr_c1_{d}, %_sr_c2_{d}\n",
                    .{ cid, lo_u, hi_u, cid, hi_u, len_u, cid, cid, cid },
                );
                const bad_s = try std.fmt.allocPrint(emitter.allocator, "%_sr_bad_{d}", .{cid});
                defer emitter.allocator.free(bad_s);
                try emitInlineTrapIfTrue(emitter, state, bad_s, 2);
            }
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        },

        .narrow_check, .try_narrow => {
            if (args.len < 3) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const is_try = ikind == .try_narrow;
            const opt_ty = try unwrapTransparentType(emitter, inst.type_id);
            const dst_ty = if (is_try) TypeId.fromInt(emitter.input.pool.getNode(opt_ty).lhs) else inst.type_id;
            const dst_unwrapped = emitter.input.pool.unwrapUnderlyingType(dst_ty);
            const src_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
            const min_ty = body.getInst(MirValueId.fromInt(args[1])).type_id;
            const max_ty = body.getInst(MirValueId.fromInt(args[2])).type_id;
            const src_info = resolveIntegerInfo(emitter, src_ty) orelse return;
            const dst_info = resolveIntegerInfo(emitter, dst_ty) orelse return;

            const min_128 = try emitExtendIntToI128(emitter, state, args[1], min_ty, false);
            defer emitter.allocator.free(min_128);
            const max_128 = try emitExtendIntToI128(emitter, state, args[2], max_ty, false);
            defer emitter.allocator.free(max_128);
            const src_128 = try emitExtendIntToI128(emitter, state, args[0], src_ty, !src_info.is_signed);
            defer emitter.allocator.free(src_128);

            const is_unrefined_u128 = dst_unwrapped == .u128_ty and
                emitter.input.pool.getRefinementBounds(dst_ty) == null;
            const tmp_id = state.nextTmp();

            if (src_info.is_signed) {
                if (is_unrefined_u128) {
                    try state.print("  %_nr_ok_{d} = icmp sge i128 {s}, 0\n", .{ tmp_id, src_128 });
                } else {
                    try state.print(
                        "  %_nr_ge_{d} = icmp sge i128 {s}, {s}\n" ++
                            "  %_nr_le_{d} = icmp sle i128 {s}, {s}\n" ++
                            "  %_nr_ok_{d} = and i1 %_nr_ge_{d}, %_nr_le_{d}\n",
                        .{ tmp_id, src_128, min_128, tmp_id, src_128, max_128, tmp_id, tmp_id, tmp_id },
                    );
                }
            } else if (is_unrefined_u128) {
                try state.print("  %_nr_ok_{d} = or i1 true, true\n", .{tmp_id});
            } else {
                try state.print(
                    "  %_nr_mxnn_{d} = icmp sge i128 {s}, 0\n" ++
                        "  %_nr_mnng_{d} = icmp slt i128 {s}, 0\n" ++
                        "  %_nr_umin_{d} = select i1 %_nr_mnng_{d}, i128 0, i128 {s}\n" ++
                        "  %_nr_uge_{d} = icmp uge i128 {s}, %_nr_umin_{d}\n" ++
                        "  %_nr_ule_{d} = icmp ule i128 {s}, {s}\n" ++
                        "  %_nr_ub_{d} = and i1 %_nr_uge_{d}, %_nr_ule_{d}\n" ++
                        "  %_nr_ok_{d} = and i1 %_nr_mxnn_{d}, %_nr_ub_{d}\n",
                    .{
                        tmp_id,  max_128,
                        tmp_id,  min_128,
                        tmp_id,  tmp_id,
                        min_128, tmp_id,
                        src_128, tmp_id,
                        tmp_id,  src_128,
                        max_128, tmp_id,
                        tmp_id,  tmp_id,
                        tmp_id,  tmp_id,
                        tmp_id,
                    },
                );
            }

            const conv_ssa = if (dst_info.bits == 128)
                try emitter.allocator.dupe(u8, src_128)
            else blk: {
                try state.print(
                    "  %_nr_cv_{d} = trunc i128 {s} to i{d}\n",
                    .{ tmp_id, src_128, dst_info.bits },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_nr_cv_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(conv_ssa);

            if (!is_try) {
                try state.print("  %_nr_bad_{d} = xor i1 %_nr_ok_{d}, true\n", .{ tmp_id, tmp_id });
                const bad_s = try std.fmt.allocPrint(emitter.allocator, "%_nr_bad_{d}", .{tmp_id});
                defer emitter.allocator.free(bad_s);
                try emitInlineTrapIfTrue(emitter, state, bad_s, 2);
                try state.print("  %_v_{d} = add i{d} {s}, 0\n", .{ dst_raw, dst_info.bits, conv_ssa });
            } else {
                const opt_lay = try emitter.resolver.resolveType(opt_ty);
                const sum_detail = (try emitter.resolver.getSumDetail(opt_ty)) orelse return;
                const out_slot = try state.allocEntryBytes(opt_lay.size_bytes, opt_lay.alignBytes());
                defer emitter.allocator.free(out_slot);
                try emitMemsetZero(emitter, state, out_slot, opt_lay.size_bytes, opt_lay.alignBytes());

                try state.print(
                    "  br i1 %_nr_ok_{d}, label %_nr_some_{d}, label %_nr_none_{d}\n" ++
                        "_nr_some_{d}:\n",
                    .{ tmp_id, tmp_id, tmp_id, tmp_id },
                );
                const pay_ptr = if (sum_detail.payload_offset == 0)
                    try emitter.allocator.dupe(u8, out_slot)
                else blk: {
                    try state.print(
                        "  %_nr_pp_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                        .{ tmp_id, out_slot, ptr_int, sum_detail.payload_offset },
                    );
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_nr_pp_{d}", .{tmp_id});
                };
                defer emitter.allocator.free(pay_ptr);

                if (!(try isZeroSizedType(emitter, dst_ty))) {
                    const dst_lay = try emitter.resolver.resolveType(dst_ty);
                    try emitStoreValueToPtr(
                        emitter,
                        state,
                        dst_ty,
                        conv_ssa,
                        pay_ptr,
                        @min(opt_lay.alignBytes(), dst_lay.alignBytes()),
                        0,
                        0,
                        0,
                    );
                }
                try emitWriteSumDiscriminantToPtr(emitter, state, opt_ty, out_slot, opt_lay.alignBytes(), 1);
                try state.print("  br label %_nr_join_{d}\n_nr_none_{d}:\n", .{ tmp_id, tmp_id });
                try emitWriteSumDiscriminantToPtr(emitter, state, opt_ty, out_slot, opt_lay.alignBytes(), 0);
                try state.print("  br label %_nr_join_{d}\n_nr_join_{d}:\n", .{ tmp_id, tmp_id });
                state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_nr_join_{d}", .{tmp_id}));

                const loaded = try emitLoadValueFromPtr(emitter, state, opt_ty, out_slot, opt_lay.alignBytes(), null, 0, 0, 0);
                defer emitter.allocator.free(loaded);
                const opt_val_ty = try formatLlvmValueType(emitter, opt_ty);
                defer emitter.allocator.free(opt_val_ty);
                try state.print(
                    "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                    .{ dst_raw, opt_val_ty, loaded, opt_val_ty, loaded },
                );
            }
        },

        .zero_pad => {
            const lowered = try lowerPlaceLlvm(emitter, state, body, PlaceId.fromInt(inst.operands.lhs));
            switch (lowered) {
                .const_len => {},
                .addr_val => |av| {
                    defer emitter.allocator.free(av.ptr_str);
                    if (!(try isZeroSizedType(emitter, av.pointee_ty))) {
                        const lay = try emitter.resolver.resolveType(av.pointee_ty);
                        try emitMemsetZero(emitter, state, av.ptr_str, lay.size_bytes, av.align_bytes);
                    }
                },
            }
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        },

        .drop_in_place, .drop_if_live => {
            const lowered = try lowerPlaceLlvm(emitter, state, body, PlaceId.fromInt(inst.operands.lhs));
            switch (lowered) {
                .const_len => {},
                .addr_val => |av| {
                    defer emitter.allocator.free(av.ptr_str);
                    const dropped_ty = emitter.input.pool.unwrapUnderlyingType(
                        if (inst.type_id != .unit_ty and !inst.type_id.isError())
                            inst.type_id
                        else
                            av.pointee_ty,
                    );
                    if (emitter.drop_type_set.contains(dropped_ty.toU32()) and
                        !(try isZeroSizedType(emitter, dropped_ty)))
                    {
                        if (ikind == .drop_if_live) {
                            if (inst.operands.rhs != mir.NONE_U32) {
                                const tmp_id = state.nextTmp();
                                try state.print(
                                    "  br i1 %_v_{d}, label %_dil_do_{d}, label %_dil_nx_{d}\n" ++
                                        "_dil_do_{d}:\n" ++
                                        "  call void @_cx_drop_ty_{d}(ptr {s})\n" ++
                                        "  br label %_dil_nx_{d}\n" ++
                                        "_dil_nx_{d}:\n",
                                    .{
                                        inst.operands.rhs, tmp_id,             tmp_id,
                                        tmp_id,            dropped_ty.toU32(), av.ptr_str,
                                        tmp_id,            tmp_id,
                                    },
                                );
                                state.setLabelOwned(
                                    try std.fmt.allocPrint(emitter.allocator, "_dil_nx_{d}", .{tmp_id}),
                                );
                            }
                        } else {
                            try state.print(
                                "  call void @_cx_drop_ty_{d}(ptr {s})\n",
                                .{ dropped_ty.toU32(), av.ptr_str },
                            );
                        }
                    }
                },
            }
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        },

        .ghost_storage_free => {
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        },

        .atomic_fence => {
            try state.writeAll("  fence seq_cst\n");
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        },

        .atomic_load => {
            if (args.len < 1 or (try isZeroSizedType(emitter, inst.type_id))) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const dst_ty = try unwrapTransparentType(emitter, inst.type_id);
            const lay = try emitter.resolver.resolveType(dst_ty);
            if (dst_ty == .bool_ty) {
                const tmp_id = state.nextTmp();
                try state.print(
                    "  %_ald8_{d} = load atomic i8, ptr %_v_{d} seq_cst, align 1\n" ++
                        "  %_alda_{d} = and i8 %_ald8_{d}, 1\n" ++
                        "  %_v_{d} = trunc i8 %_alda_{d} to i1\n",
                    .{ tmp_id, args[0], tmp_id, tmp_id, dst_raw, tmp_id },
                );
            } else {
                const val_ty = try formatLlvmValueType(emitter, dst_ty);
                defer emitter.allocator.free(val_ty);
                try state.print(
                    "  %_v_{d} = load atomic {s}, ptr %_v_{d} seq_cst, align {d}\n",
                    .{ dst_raw, val_ty, args[0], @max(lay.alignBytes(), 1) },
                );
            }
        },

        .atomic_store => {
            if (args.len >= 2) {
                const val_ty = try unwrapTransparentType(
                    emitter,
                    body.getInst(MirValueId.fromInt(args[1])).type_id,
                );
                if (!(try isZeroSizedType(emitter, val_ty))) {
                    const lay = try emitter.resolver.resolveType(val_ty);
                    if (val_ty == .bool_ty) {
                        const tmp_id = state.nextTmp();
                        try state.print(
                            "  %_ast8_{d} = zext i1 %_v_{d} to i8\n" ++
                                "  store atomic i8 %_ast8_{d}, ptr %_v_{d} seq_cst, align 1\n",
                            .{ tmp_id, args[1], tmp_id, args[0] },
                        );
                    } else {
                        const val_llvm = try formatLlvmValueType(emitter, val_ty);
                        defer emitter.allocator.free(val_llvm);
                        try state.print(
                            "  store atomic {s} %_v_{d}, ptr %_v_{d} seq_cst, align {d}\n",
                            .{ val_llvm, args[1], args[0], @max(lay.alignBytes(), 1) },
                        );
                    }
                }
            }
            try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
        },

        .atomic_rmw_add, .atomic_rmw_sub, .atomic_rmw_xchg => {
            if (args.len < 2 or (try isZeroSizedType(emitter, inst.type_id))) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const dst_ty = try unwrapTransparentType(emitter, inst.type_id);
            const lay = try emitter.resolver.resolveType(dst_ty);
            const rmw_op = switch (ikind) {
                .atomic_rmw_add => "add",
                .atomic_rmw_sub => "sub",
                else => "xchg",
            };
            if (dst_ty == .bool_ty) {
                const tmp_id = state.nextTmp();
                try state.print(
                    "  %_armwb_{d} = zext i1 %_v_{d} to i8\n" ++
                        "  %_armwr_{d} = atomicrmw {s} ptr %_v_{d}, i8 %_armwb_{d} seq_cst, align 1\n" ++
                        "  %_armwa_{d} = and i8 %_armwr_{d}, 1\n" ++
                        "  %_v_{d} = trunc i8 %_armwa_{d} to i1\n",
                    .{ tmp_id, args[1], tmp_id, rmw_op, args[0], tmp_id, tmp_id, tmp_id, dst_raw, tmp_id },
                );
            } else {
                const val_llvm = try formatLlvmValueType(emitter, dst_ty);
                defer emitter.allocator.free(val_llvm);
                try state.print(
                    "  %_v_{d} = atomicrmw {s} ptr %_v_{d}, {s} %_v_{d} seq_cst, align {d}\n",
                    .{ dst_raw, rmw_op, args[0], val_llvm, args[1], @max(lay.alignBytes(), 1) },
                );
            }
        },

        .atomic_cmpxchg => {
            if (args.len < 3) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const val_ty = try unwrapTransparentType(
                emitter,
                body.getInst(MirValueId.fromInt(args[1])).type_id,
            );
            const val_lay = try emitter.resolver.resolveType(val_ty);
            const tup_ty = try unwrapTransparentType(emitter, inst.type_id);
            const tup_lay = try emitter.resolver.resolveType(tup_ty);
            const tmp_id = state.nextTmp();

            const old_ssa: []u8 = blk: {
                if (val_ty == .bool_ty) {
                    try state.print(
                        "  %_cx_e8_{d} = zext i1 %_v_{d} to i8\n" ++
                            "  %_cx_d8_{d} = zext i1 %_v_{d} to i8\n" ++
                            "  %_cx_pr_{d} = cmpxchg ptr %_v_{d}, i8 %_cx_e8_{d}, i8 %_cx_d8_{d} seq_cst seq_cst, align 1\n" ++
                            "  %_cx_o8_{d} = extractvalue {{ i8, i1 }} %_cx_pr_{d}, 0\n" ++
                            "  %_cx_oa_{d} = and i8 %_cx_o8_{d}, 1\n" ++
                            "  %_cx_old_{d} = trunc i8 %_cx_oa_{d} to i1\n" ++
                            "  %_cx_ok_{d} = extractvalue {{ i8, i1 }} %_cx_pr_{d}, 1\n",
                        .{
                            tmp_id, args[1],
                            tmp_id, args[2],
                            tmp_id, args[0],
                            tmp_id, tmp_id,
                            tmp_id, tmp_id,
                            tmp_id, tmp_id,
                            tmp_id, tmp_id,
                            tmp_id, tmp_id,
                        },
                    );
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_cx_old_{d}", .{tmp_id});
                }
                const val_llvm = try formatLlvmValueType(emitter, val_ty);
                defer emitter.allocator.free(val_llvm);
                try state.print(
                    "  %_cx_pr_{d} = cmpxchg ptr %_v_{d}, {s} %_v_{d}, {s} %_v_{d} seq_cst seq_cst, align {d}\n" ++
                        "  %_cx_old_{d} = extractvalue {{ {s}, i1 }} %_cx_pr_{d}, 0\n" ++
                        "  %_cx_ok_{d} = extractvalue {{ {s}, i1 }} %_cx_pr_{d}, 1\n",
                    .{
                        tmp_id, args[0],  val_llvm, args[1], val_llvm, args[2], @max(val_lay.alignBytes(), 1),
                        tmp_id, val_llvm, tmp_id,   tmp_id,  val_llvm, tmp_id,
                    },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_cx_old_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(old_ssa);

            const ok_ssa = try std.fmt.allocPrint(emitter.allocator, "%_cx_ok_{d}", .{tmp_id});
            defer emitter.allocator.free(ok_ssa);

            const tup_slot = try state.allocEntryBytes(tup_lay.size_bytes, tup_lay.alignBytes());
            defer emitter.allocator.free(tup_slot);
            try emitMemsetZero(emitter, state, tup_slot, tup_lay.size_bytes, tup_lay.alignBytes());

            if (try emitter.resolver.getFieldByDeclOrdinal(tup_ty, 0)) |fld0| {
                const p0 = if (fld0.byte_offset == 0)
                    try emitter.allocator.dupe(u8, tup_slot)
                else sub: {
                    try state.print(
                        "  %_cx_f0_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                        .{ tmp_id, tup_slot, ptr_int, fld0.byte_offset },
                    );
                    break :sub try std.fmt.allocPrint(emitter.allocator, "%_cx_f0_{d}", .{tmp_id});
                };
                defer emitter.allocator.free(p0);
                try emitStoreValueToPtr(
                    emitter,
                    state,
                    val_ty,
                    old_ssa,
                    p0,
                    @min(
                        tup_lay.alignBytes(),
                        effectiveOffsetAlign(fld0.byte_offset, @as(u32, 1) << @intCast(fld0.align_log2)),
                    ),
                    0,
                    0,
                    0,
                );
            }
            if (try emitter.resolver.getFieldByDeclOrdinal(tup_ty, 1)) |fld1| {
                const p1 = if (fld1.byte_offset == 0)
                    try emitter.allocator.dupe(u8, tup_slot)
                else sub: {
                    try state.print(
                        "  %_cx_f1_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                        .{ tmp_id, tup_slot, ptr_int, fld1.byte_offset },
                    );
                    break :sub try std.fmt.allocPrint(emitter.allocator, "%_cx_f1_{d}", .{tmp_id});
                };
                defer emitter.allocator.free(p1);
                try emitStoreValueToPtr(emitter, state, .bool_ty, ok_ssa, p1, 1, 0, 0, 0);
            }

            const loaded = try emitLoadValueFromPtr(emitter, state, tup_ty, tup_slot, tup_lay.alignBytes(), null, 0, 0, 0);
            defer emitter.allocator.free(loaded);
            const tup_val_ty = try formatLlvmValueType(emitter, tup_ty);
            defer emitter.allocator.free(tup_val_ty);
            try state.print(
                "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                .{ dst_raw, tup_val_ty, loaded, tup_val_ty, loaded },
            );
        },

        .simd_splat => {
            if (args.len < 1) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const vec_ty = try unwrapTransparentType(emitter, inst.type_id);
            const vec_lay = try emitter.resolver.resolveType(vec_ty);
            const vec_node = emitter.input.pool.getNode(vec_ty);
            const lane_ty = try unwrapTransparentType(emitter, TypeId.fromInt(vec_node.lhs));
            const lanes: u64 = vec_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            const lane_llvm = try formatLlvmValueType(emitter, lane_ty);
            defer emitter.allocator.free(lane_llvm);

            const vec_align = @max(vec_lay.alignBytes(), 16);
            const scratch = try state.allocEntryBytes(vec_lay.size_bytes, vec_align);
            defer emitter.allocator.free(scratch);
            const tmp_id = state.nextTmp();
            try state.print(
                "  %_vsp_i_{d} = insertelement <{d} x {s}> poison, {s} %_v_{d}, i32 0\n" ++
                    "  %_vsp_v_{d} = shufflevector <{d} x {s}> %_vsp_i_{d}, <{d} x {s}> poison, <{d} x i32> zeroinitializer\n" ++
                    "  store <{d} x {s}> %_vsp_v_{d}, ptr {s}, align {d}\n" ++
                    "  %_v_{d} = load [{d} x {s}], ptr {s}, align {d}\n",
                .{
                    tmp_id,    lanes,     lane_llvm, lane_llvm, args[0],
                    tmp_id,    lanes,     lane_llvm, tmp_id,    lanes,
                    lane_llvm, lanes,     lanes,     lane_llvm, tmp_id,
                    scratch,   vec_align, dst_raw,   lanes,     lane_llvm,
                    scratch,   vec_align,
                },
            );
        },

        .simd_add, .simd_sub, .simd_mul => {
            if (args.len < 2) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const vec_ty = try unwrapTransparentType(emitter, inst.type_id);
            const vec_lay = try emitter.resolver.resolveType(vec_ty);
            const vec_node = emitter.input.pool.getNode(vec_ty);
            const lane_ty = try unwrapTransparentType(emitter, TypeId.fromInt(vec_node.lhs));
            const lanes: u64 = vec_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            const lane_llvm = try formatLlvmValueType(emitter, lane_ty);
            defer emitter.allocator.free(lane_llvm);
            const is_flt = lane_ty == .f32_ty or lane_ty == .f64_ty;
            const vop = switch (ikind) {
                .simd_add => if (is_flt) "fadd" else "add",
                .simd_sub => if (is_flt) "fsub" else "sub",
                else => if (is_flt) "fmul" else "mul",
            };

            const vec_align = @max(vec_lay.alignBytes(), 16);
            const slot_l = try state.allocEntryBytes(vec_lay.size_bytes, vec_align);
            defer emitter.allocator.free(slot_l);
            const slot_r = try state.allocEntryBytes(vec_lay.size_bytes, vec_align);
            defer emitter.allocator.free(slot_r);
            const tmp_id = state.nextTmp();
            try state.print(
                "  store [{d} x {s}] %_v_{d}, ptr {s}, align {d}\n" ++
                    "  store [{d} x {s}] %_v_{d}, ptr {s}, align {d}\n" ++
                    "  %_vbl_{d} = load <{d} x {s}>, ptr {s}, align {d}\n" ++
                    "  %_vbr_{d} = load <{d} x {s}>, ptr {s}, align {d}\n",
                .{
                    lanes,  lane_llvm, args[0],   slot_l, vec_align,
                    lanes,  lane_llvm, args[1],   slot_r, vec_align,
                    tmp_id, lanes,     lane_llvm, slot_l, vec_align,
                    tmp_id, lanes,     lane_llvm, slot_r, vec_align,
                },
            );
            try state.print(
                "  %_vbo_{d} = {s} <{d} x {s}> %_vbl_{d}, %_vbr_{d}\n" ++
                    "  store <{d} x {s}> %_vbo_{d}, ptr {s}, align {d}\n" ++
                    "  %_v_{d} = load [{d} x {s}], ptr {s}, align {d}\n",
                .{
                    tmp_id, vop,       lanes,  lane_llvm, tmp_id,    tmp_id,
                    lanes,  lane_llvm, tmp_id, slot_l,    vec_align, dst_raw,
                    lanes,  lane_llvm, slot_l, vec_align,
                },
            );
        },

        .simd_reduce_add => {
            if (args.len < 1) {
                try state.print("  %_v_{d} = add i8 0, 0\n", .{dst_raw});
                return;
            }
            const vec_ty = try unwrapTransparentType(
                emitter,
                body.getInst(MirValueId.fromInt(args[0])).type_id,
            );
            const vec_lay = try emitter.resolver.resolveType(vec_ty);
            const vec_node = emitter.input.pool.getNode(vec_ty);
            const lane_ty = try unwrapTransparentType(emitter, TypeId.fromInt(vec_node.lhs));
            const lanes: u64 = vec_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            const lane_llvm = try formatLlvmValueType(emitter, lane_ty);
            defer emitter.allocator.free(lane_llvm);

            const vec_align = @max(vec_lay.alignBytes(), 16);
            const slot_v = try state.allocEntryBytes(vec_lay.size_bytes, vec_align);
            defer emitter.allocator.free(slot_v);
            const tmp_id = state.nextTmp();
            try state.print(
                "  store [{d} x {s}] %_v_{d}, ptr {s}, align {d}\n" ++
                    "  %_vrd_v_{d} = load <{d} x {s}>, ptr {s}, align {d}\n",
                .{
                    lanes,  lane_llvm, args[0],   slot_v, vec_align,
                    tmp_id, lanes,     lane_llvm, slot_v, vec_align,
                },
            );

            if (lane_ty == .f32_ty or lane_ty == .f64_ty) {
                const mangled_f = if (lane_ty == .f32_ty) "f32" else "f64";
                const decl = try std.fmt.allocPrint(
                    emitter.allocator,
                    "declare {s} @llvm.vector.reduce.fadd.v{d}{s}({s}, <{d} x {s}>)",
                    .{ lane_llvm, lanes, mangled_f, lane_llvm, lanes, lane_llvm },
                );
                defer emitter.allocator.free(decl);
                try emitter.requireIntrinsicDecl(decl);
                try state.print(
                    "  %_v_{d} = call {s} @llvm.vector.reduce.fadd.v{d}{s}({s} -0.0, <{d} x {s}> %_vrd_v_{d})\n",
                    .{ dst_raw, lane_llvm, lanes, mangled_f, lane_llvm, lanes, lane_llvm, tmp_id },
                );
            } else if (resolveIntegerInfo(emitter, lane_ty)) |l_info| {
                const decl = try std.fmt.allocPrint(
                    emitter.allocator,
                    "declare i{d} @llvm.vector.reduce.add.v{d}i{d}(<{d} x i{d}>)",
                    .{ l_info.bits, lanes, l_info.bits, lanes, l_info.bits },
                );
                defer emitter.allocator.free(decl);
                try emitter.requireIntrinsicDecl(decl);
                try state.print(
                    "  %_v_{d} = call i{d} @llvm.vector.reduce.add.v{d}i{d}(<{d} x i{d}> %_vrd_v_{d})\n",
                    .{ dst_raw, l_info.bits, lanes, l_info.bits, lanes, l_info.bits, tmp_id },
                );
            }
            _ = access_grp;
        },

        .poll_reload => {
            if (emitter.input.is_dev_got_enabled) {
                const tmp_id = state.nextTmp();
                try state.print(
                    "  %_pr_pend_{d} = load atomic i64, ptr @_cx_reload_ctrl seq_cst, align 8\n" ++
                        "  %_pr_app_p_{d} = getelementptr inbounds {{ i64, i64, i64, i32, i32, i32, i32, i64, i32, i32, i64 }}, " ++
                        "ptr @_cx_reload_ctrl, i32 0, i32 1\n" ++
                        "  %_pr_app_{d} = load atomic i64, ptr %_pr_app_p_{d} seq_cst, align 8\n" ++
                        "  %_pr_has_{d} = icmp ugt i64 %_pr_pend_{d}, %_pr_app_{d}\n" ++
                        "  br i1 %_pr_has_{d}, label %_pr_upd_{d}, label %_pr_join_{d}\n" ++
                        "_pr_upd_{d}:\n" ++
                        "  store atomic i64 %_pr_pend_{d}, ptr %_pr_app_p_{d} seq_cst, align 8\n" ++
                        "  br label %_pr_join_{d}\n" ++
                        "_pr_join_{d}:\n" ++
                        "  %_v_{d} = or i1 %_pr_has_{d}, false\n",
                    .{
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        tmp_id,
                        dst_raw,
                        tmp_id,
                    },
                );
                state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_pr_join_{d}", .{tmp_id}));
            } else {
                try state.print("  %_v_{d} = or i1 false, false\n", .{dst_raw});
            }
        },

        .panic => {
            if (args.len >= 1) {
                const span_s = try emitExtractByteSpanLlvm(emitter, state, body, MirValueId.fromInt(args[0]));
                defer emitter.allocator.free(span_s.ptr_ssa);
                defer emitter.allocator.free(span_s.len_ssa);
                try state.print(
                    "  call void @_cx_rt_panic(ptr {s}, {s} {s})\n",
                    .{ span_s.ptr_ssa, ptr_int, span_s.len_ssa },
                );
            } else {
                try state.print("  call void @_cx_rt_panic(ptr null, {s} 0)\n", .{ptr_int});
            }
            try emitUnreachableAndDeadBlock(emitter, state, dst_raw);
        },

        .trap => {
            try state.writeAll("  call void @_cx_rt_trap(i32 0)\n");
            try emitUnreachableAndDeadBlock(emitter, state, dst_raw);
        },

        .sys_write => {
            if (args.len < 2) {
                try state.print("  %_v_{d} = add {s} 0, 0\n", .{ dst_raw, ptr_int });
                return;
            }
            const fd_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
            const fd_info = resolveIntegerInfo(emitter, fd_ty) orelse
                IntScalarInfo{ .bits = 32, .is_signed = true };
            const tmp_id = state.nextTmp();
            const fd32_s = if (fd_info.bits == 32)
                try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{args[0]})
            else blk: {
                const op_s = if (fd_info.bits < 32)
                    (if (fd_info.is_signed) "sext" else "zext")
                else
                    "trunc";
                try state.print(
                    "  %_sw_fd_{d} = {s} i{d} %_v_{d} to i32\n",
                    .{ tmp_id, op_s, fd_info.bits, args[0] },
                );
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_sw_fd_{d}", .{tmp_id});
            };
            defer emitter.allocator.free(fd32_s);

            const span_s = try emitExtractByteSpanLlvm(emitter, state, body, MirValueId.fromInt(args[1]));
            defer emitter.allocator.free(span_s.ptr_ssa);
            defer emitter.allocator.free(span_s.len_ssa);
            try state.print(
                "  %_sw_res_{d} = call {s} @_cx_rt_sys_write(i32 {s}, ptr {s}, {s} {s})\n",
                .{ tmp_id, ptr_int, fd32_s, span_s.ptr_ssa, ptr_int, span_s.len_ssa },
            );
            const dst_info = resolveIntegerInfo(emitter, inst.type_id) orelse
                IntScalarInfo{ .bits = @as(u16, emitter.cfg.target.ptrBytes()) * 8, .is_signed = true };
            const ptr_bits: u16 = @as(u16, emitter.cfg.target.ptrBytes()) * 8;
            if (dst_info.bits == ptr_bits) {
                try state.print("  %_v_{d} = add {s} %_sw_res_{d}, 0\n", .{ dst_raw, ptr_int, tmp_id });
            } else if (dst_info.bits > ptr_bits) {
                try state.print(
                    "  %_v_{d} = sext {s} %_sw_res_{d} to i{d}\n",
                    .{ dst_raw, ptr_int, tmp_id, dst_info.bits },
                );
            } else {
                try state.print(
                    "  %_v_{d} = trunc {s} %_sw_res_{d} to i{d}\n",
                    .{ dst_raw, ptr_int, tmp_id, dst_info.bits },
                );
            }
        },

        .sys_exit => {
            if (args.len >= 1) {
                const code_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
                const code_info = resolveIntegerInfo(emitter, code_ty) orelse
                    IntScalarInfo{ .bits = 32, .is_signed = true };
                const tmp_id = state.nextTmp();
                const code32_s = if (code_info.bits == 32)
                    try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{args[0]})
                else blk: {
                    const op_s = if (code_info.bits < 32)
                        (if (code_info.is_signed) "sext" else "zext")
                    else
                        "trunc";
                    try state.print(
                        "  %_sx_c_{d} = {s} i{d} %_v_{d} to i32\n",
                        .{ tmp_id, op_s, code_info.bits, args[0] },
                    );
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_sx_c_{d}", .{tmp_id});
                };
                defer emitter.allocator.free(code32_s);
                try state.print("  call void @_cx_rt_sys_exit(i32 {s})\n", .{code32_s});
            } else {
                try state.writeAll("  call void @_cx_rt_sys_exit(i32 0)\n");
            }
            try emitUnreachableAndDeadBlock(emitter, state, dst_raw);
        },
    }
}

// ----------- DWARF v5 LineTablesOnly Debug Metadata -----------

/// Resolves 1-based `(line, col)` for `(file_id, tok_idx)` without mutating `*const VfsSourceMap`.
fn resolveSourceTokenCoords(
    emitter: *const LlvmModuleEmitter,
    file_id: FileId,
    tok_idx: TokenIndex,
) ?struct { line: u32, col: u32 } {
    if (file_id.isNone() or tok_idx.isNone()) return null;
    const smap = emitter.input.vfs_source_map orelse return null;
    const tok_map = emitter.input.file_tokens orelse return null;
    const tok_buf = tok_map.get(file_id.asInt()) orelse return null;
    if (tok_idx.asInt() >= tok_buf.countTokens()) return null;
    const entry = smap.getFileEntry(file_id) orelse return null;
    const byte_off = tok_buf.getToken(tok_idx).byte_offset;
    if (entry.line_index) |*cached_idx| {
        const resolved = cached_idx.resolveLineCol(entry.content, byte_off);
        return .{ .line = @max(resolved.line, 1), .col = @max(resolved.col_utf8, 1) };
    }
    const clamped_end: usize = @min(@as(usize, byte_off), entry.content.len);
    var line_num: u32 = 1;
    var col_num: u32 = 1;
    for (entry.content[0..clamped_end]) |ch_b| {
        if (ch_b == '\n') {
            line_num += 1;
            col_num = 1;
        } else if (ch_b != '\r') {
            col_num += 1;
        }
    }
    return .{ .line = line_num, .col = col_num };
}

/// Initializes `!DICompileUnit` (`emissionKind: LineTablesOnly`, DWARF v5) when `vfs_source_map` is set.
fn ensureDwarfCompileUnit(emitter: *LlvmModuleEmitter) !void {
    if (emitter.di_cu_md != 0 or emitter.input.vfs_source_map == null) return;
    if (emitter.di_empty_tuple_md == 0) {
        emitter.di_empty_tuple_md = try emitter.addMetadataNode("!{}");
    }
    const esc_mod = try escapeMetadataStringAlloc(emitter.allocator, emitter.input.module_name);
    defer emitter.allocator.free(esc_mod);
    const default_file_rhs = try std.fmt.allocPrint(
        emitter.allocator,
        "!DIFile(filename: \"{s}.cx\", directory: \".\")",
        .{esc_mod},
    );
    defer emitter.allocator.free(default_file_rhs);
    emitter.di_default_file_md = try emitter.addMetadataNode(default_file_rhs);

    const sub_ty_rhs = try std.fmt.allocPrint(
        emitter.allocator,
        "!DISubroutineType(types: !{d})",
        .{emitter.di_empty_tuple_md},
    );
    defer emitter.allocator.free(sub_ty_rhs);
    emitter.di_subroutine_ty_md = try emitter.addMetadataNode(sub_ty_rhs);

    const cu_rhs = try std.fmt.allocPrint(
        emitter.allocator,
        "distinct !DICompileUnit(language: DW_LANG_C99, file: !{d}, " ++
            "producer: \"CoreX Stage-0 LLVM\", isOptimized: {s}, runtimeVersion: 0, " ++
            "emissionKind: LineTablesOnly, splitDebugInlining: false, nameTableKind: None)",
        .{
            emitter.di_default_file_md,
            if (emitter.cfg.opt_level != .debug_o0) "true" else "false",
        },
    );
    defer emitter.allocator.free(cu_rhs);
    emitter.di_cu_md = try emitter.addMetadataNode(cu_rhs);
}

/// Interns or returns the `!DIFile` metadata ID for `file_id`.
fn getOrCreateDiFile(emitter: *LlvmModuleEmitter, file_id: FileId) !u32 {
    try ensureDwarfCompileUnit(emitter);
    if (emitter.di_cu_md == 0) return 0;
    if (file_id.isNone()) return emitter.di_default_file_md;
    if (emitter.di_file_map.get(file_id.asInt())) |existing_md| return existing_md;

    const smap = emitter.input.vfs_source_map orelse return emitter.di_default_file_md;
    const vpath = smap.getFilePath(file_id);
    if (vpath.len == 0) return emitter.di_default_file_md;

    var dir_slice: []const u8 = ".";
    var base_slice: []const u8 = vpath;
    if (std.mem.lastIndexOfScalar(u8, vpath, '/')) |slash_idx| {
        dir_slice = if (slash_idx == 0) "/" else vpath[0..slash_idx];
        base_slice = vpath[slash_idx + 1 ..];
    }
    const esc_base = try escapeMetadataStringAlloc(emitter.allocator, base_slice);
    defer emitter.allocator.free(esc_base);
    const esc_dir = try escapeMetadataStringAlloc(emitter.allocator, dir_slice);
    defer emitter.allocator.free(esc_dir);

    const file_rhs = try std.fmt.allocPrint(
        emitter.allocator,
        "!DIFile(filename: \"{s}\", directory: \"{s}\")",
        .{ esc_base, esc_dir },
    );
    defer emitter.allocator.free(file_rhs);
    const file_md = try emitter.addMetadataNode(file_rhs);
    try emitter.di_file_map.put(emitter.allocator, file_id.asInt(), file_md);
    return file_md;
}

/// Creates a `distinct !DISubprogram` node for `body` when DWARF line tables are active.
fn createBodySubprogramMd(
    emitter: *LlvmModuleEmitter,
    body_idx: u32,
    body: *const MirBody,
) !u32 {
    if (emitter.input.vfs_source_map == null) return 0;
    try ensureDwarfCompileUnit(emitter);
    if (emitter.di_cu_md == 0) return 0;

    const file_md = try getOrCreateDiFile(emitter, body.file_id);
    var first_line: u32 = 1;
    for (body.origin_tokens.items) |tok_idx| {
        if (resolveSourceTokenCoords(emitter, body.file_id, tok_idx)) |coords| {
            first_line = coords.line;
            break;
        }
    }

    const esc_src_name = try escapeMetadataStringAlloc(
        emitter.allocator,
        emitter.input.interner.get(body.name),
    );
    defer emitter.allocator.free(esc_src_name);
    const esc_lnk_name = try escapeMetadataStringAlloc(
        emitter.allocator,
        emitter.body_llvm_names.items[body_idx],
    );
    defer emitter.allocator.free(esc_lnk_name);

    const sp_rhs = try std.fmt.allocPrint(
        emitter.allocator,
        "distinct !DISubprogram(name: \"{s}\", linkageName: \"{s}\", scope: !{d}, file: !{d}, " ++
            "line: {d}, type: !{d}, scopeLine: {d}, spFlags: DISPFlagDefinition{s}, unit: !{d})",
        .{
            esc_src_name,
            esc_lnk_name,
            file_md,
            file_md,
            first_line,
            emitter.di_subroutine_ty_md,
            first_line,
            if (emitter.cfg.opt_level != .debug_o0) " | DISPFlagOptimized" else "",
            emitter.di_cu_md,
        },
    );
    defer emitter.allocator.free(sp_rhs);
    return emitter.addMetadataNode(sp_rhs);
}

/// Resolves or interns a `!DILocation` node for `(subprogram_md, file_id, tok_idx)`.
fn resolveTokenDebugLocMd(
    emitter: *LlvmModuleEmitter,
    subprogram_md: u32,
    file_id: FileId,
    tok_idx: TokenIndex,
) !u32 {
    if (subprogram_md == 0) return 0;
    var clamped_line: u64 = 1;
    var clamped_col: u64 = 1;
    if (resolveSourceTokenCoords(emitter, file_id, tok_idx)) |coords| {
        clamped_line = @min(coords.line, 0xFFFFF);
        clamped_col = @min(coords.col, 0xFFF);
    }
    const cache_key: u64 = (@as(u64, subprogram_md) << 32) | (clamped_line << 12) | clamped_col;
    if (emitter.di_loc_cache.get(cache_key)) |cached_md| return cached_md;

    const loc_rhs = try std.fmt.allocPrint(
        emitter.allocator,
        "!DILocation(line: {d}, column: {d}, scope: !{d})",
        .{ clamped_line, clamped_col, subprogram_md },
    );
    defer emitter.allocator.free(loc_rhs);
    const loc_md = try emitter.addMetadataNode(loc_rhs);
    try emitter.di_loc_cache.put(emitter.allocator, cache_key, loc_md);
    return loc_md;
}

// ------------- MIR Terminator & Two-Pass Body IR --------------

/// Resolves the branch target label for `edge_idx` and records the active predecessor block for `phi` stitching.
fn resolveEdgeTargetAndRecordPred(
    emitter: *const LlvmModuleEmitter,
    state: *BodyEmitState,
    edge_idx: u32,
    target_bb: MirBlockId,
) ![]u8 {
    if (state.edge_trampoline[edge_idx]) |tramp_idx| {
        if (state.edge_pred_labels[edge_idx].len > 0) {
            emitter.allocator.free(state.edge_pred_labels[edge_idx]);
        }
        state.edge_pred_labels[edge_idx] = try std.fmt.allocPrint(
            emitter.allocator,
            "_bb_edge_{d}",
            .{tramp_idx},
        );
        return std.fmt.allocPrint(emitter.allocator, "_bb_edge_{d}", .{tramp_idx});
    }
    if (state.edge_pred_labels[edge_idx].len > 0) {
        emitter.allocator.free(state.edge_pred_labels[edge_idx]);
    }
    state.edge_pred_labels[edge_idx] = try emitter.allocator.dupe(u8, state.cur_label);
    return std.fmt.allocPrint(emitter.allocator, "_bb_{d}", .{target_bb.asInt()});
}

/// Finds `!llvm.loop` metadata ID if `bb_idx -> target_bb` (or via `cond_br`) is a loop-latch back-edge.
fn lookupLatchLoopMd(
    state: *const BodyEmitState,
    bb_idx: u32,
    target_a: MirBlockId,
    maybe_target_b: ?MirBlockId,
) u32 {
    for (state.loop_mds.items) |lmd| {
        if (lmd.latch_bb.asInt() != bb_idx) continue;
        if (lmd.header_bb == target_a) return lmd.loop_md;
        if (maybe_target_b) |tb| {
            if (lmd.header_bb == tb) return lmd.loop_md;
        }
    }
    return 0;
}

/// Appends optional `!llvm.loop` and `!dbg` suffixes to a terminator instruction line.
fn appendTerminatorMetaSuffix(state: *BodyEmitState, loop_md: u32) !void {
    if (loop_md != 0) try state.print(", !llvm.loop !{d}", .{loop_md});
    if (state.active_dbg_loc_md != 0) try state.print(", !dbg !{d}", .{state.active_dbg_loc_md});
    try state.writeAll("\n");
}

/// Encodes `recipe.err_ty` stored at `err_pay_ptr` into a non-null `ptr` stored into `%_cx_err_slot`.
fn emitStoreSwifterrorFromPayloadPtr(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    recipe: *const AbiFnRecipe,
    err_pay_ptr: []const u8,
) !void {
    const ptr_int = ptrIntType(emitter);
    const tmp_id = state.nextTmp();
    switch (recipe.swifterror_kind) {
        .none => {},
        .zst_err => {
            try state.print(
                "  store ptr inttoptr ({s} 1 to ptr), ptr %_cx_err_slot, align 8\n",
                .{ptr_int},
            );
        },
        .nonnull_ptr => {
            try state.print(
                "  %_se_np_{d} = load ptr, ptr {s}, align 1\n" ++
                    "  store ptr %_se_np_{d}, ptr %_cx_err_slot, align 8\n",
                .{ tmp_id, err_pay_ptr, tmp_id },
            );
        },
        .tagged_int56 => {
            const err_ty = try unwrapTransparentType(emitter, recipe.err_ty);
            const err_lay = try emitter.resolver.resolveType(err_ty);
            if (err_ty == .bool_ty) {
                try state.print(
                    "  %_se_b8_{d} = load i8, ptr {s}, align 1\n" ++
                        "  %_se_b1_{d} = and i8 %_se_b8_{d}, 1\n" ++
                        "  %_se_u64_{d} = zext i8 %_se_b1_{d} to i64\n",
                    .{ tmp_id, err_pay_ptr, tmp_id, tmp_id, tmp_id, tmp_id },
                );
            } else if (resolveIntegerInfo(emitter, err_ty)) |e_info| {
                const load_bits: u16 = @min(e_info.bits, 64);
                try state.print(
                    "  %_se_iv_{d} = load i{d}, ptr {s}, align 1\n",
                    .{ tmp_id, load_bits, err_pay_ptr },
                );
                if (load_bits < 64) {
                    try state.print(
                        "  %_se_u64_{d} = zext i{d} %_se_iv_{d} to i64\n",
                        .{ tmp_id, load_bits, tmp_id },
                    );
                } else {
                    try state.print(
                        "  %_se_u64_{d} = and i64 %_se_iv_{d}, 72057594037927935\n",
                        .{ tmp_id, tmp_id },
                    );
                }
            } else {
                const copy_sz = @min(err_lay.size_bytes, 7);
                const raw_slot = try state.allocEntryBytes(8, 8);
                defer emitter.allocator.free(raw_slot);
                try emitMemsetZero(emitter, state, raw_slot, 8, 8);
                try emitMemcpyBytes(emitter, state, raw_slot, 8, err_pay_ptr, 1, copy_sz);
                try state.print(
                    "  %_se_u64_{d} = load i64, ptr {s}, align 8\n",
                    .{ tmp_id, raw_slot },
                );
            }
            try state.print(
                "  %_se_tg_{d} = or i64 %_se_u64_{d}, {d}\n",
                .{ tmp_id, tmp_id, SWIFTERROR_INT56_TAG },
            );
            if (emitter.cfg.target.isWasm()) {
                try state.print(
                    "  %_se_tr32_{d} = trunc i64 %_se_tg_{d} to i32\n" ++
                        "  %_se_ep_{d} = inttoptr i32 %_se_tr32_{d} to ptr\n" ++
                        "  store ptr %_se_ep_{d}, ptr %_cx_err_slot, align 8\n",
                    .{ tmp_id, tmp_id, tmp_id, tmp_id, tmp_id },
                );
            } else {
                try state.print(
                    "  %_se_ep_{d} = inttoptr i64 %_se_tg_{d} to ptr\n" ++
                        "  store ptr %_se_ep_{d}, ptr %_cx_err_slot, align 8\n",
                    .{ tmp_id, tmp_id, tmp_id },
                );
            }
        },
    }
}

/// Decodes a non-null `swifterror` pointer `err_ptr_ssa` into `err_pay_ptr` at a call site (`[CRITICAL-06]`).
fn emitDecodeSwifterrorToPayloadPtr(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    recipe: *const AbiFnRecipe,
    err_ptr_ssa: []const u8,
    err_pay_ptr: []const u8,
) !void {
    const tmp_id = state.nextTmp();
    switch (recipe.swifterror_kind) {
        .none, .zst_err => {},
        .nonnull_ptr => {
            try state.print(
                "  store ptr {s}, ptr {s}, align 1\n",
                .{ err_ptr_ssa, err_pay_ptr },
            );
        },
        .tagged_int56 => {
            const err_ty = try unwrapTransparentType(emitter, recipe.err_ty);
            const err_lay = try emitter.resolver.resolveType(err_ty);
            if (err_lay.size_bytes == 0) return;

            if (emitter.cfg.target.isWasm()) {
                try state.print(
                    "  %_dc_p32_{d} = ptrtoint ptr {s} to i32\n" ++
                        "  %_dc_u64_{d} = zext i32 %_dc_p32_{d} to i64\n",
                    .{ tmp_id, err_ptr_ssa, tmp_id, tmp_id },
                );
            } else {
                try state.print(
                    "  %_dc_p64_{d} = ptrtoint ptr {s} to i64\n" ++
                        "  %_dc_u64_{d} = and i64 %_dc_p64_{d}, 72057594037927935\n",
                    .{ tmp_id, err_ptr_ssa, tmp_id, tmp_id },
                );
            }
            if (err_ty == .bool_ty) {
                try state.print(
                    "  %_dc_b8_{d} = trunc i64 %_dc_u64_{d} to i8\n" ++
                        "  %_dc_b1_{d} = and i8 %_dc_b8_{d}, 1\n" ++
                        "  store i8 %_dc_b1_{d}, ptr {s}, align 1\n",
                    .{ tmp_id, tmp_id, tmp_id, tmp_id, tmp_id, err_pay_ptr },
                );
            } else if (resolveIntegerInfo(emitter, err_ty)) |e_info| {
                const dst_bits: u16 = @min(e_info.bits, 64);
                if (dst_bits < 64) {
                    try state.print(
                        "  %_dc_tr_{d} = trunc i64 %_dc_u64_{d} to i{d}\n" ++
                            "  store i{d} %_dc_tr_{d}, ptr {s}, align 1\n",
                        .{ tmp_id, tmp_id, dst_bits, dst_bits, tmp_id, err_pay_ptr },
                    );
                } else {
                    try state.print(
                        "  store i64 %_dc_u64_{d}, ptr {s}, align 1\n",
                        .{ tmp_id, err_pay_ptr },
                    );
                }
            } else {
                const copy_sz = @min(err_lay.size_bytes, 7);
                const raw_slot = try state.allocEntryBytes(8, 8);
                defer emitter.allocator.free(raw_slot);
                try state.print(
                    "  store i64 %_dc_u64_{d}, ptr {s}, align 8\n",
                    .{ tmp_id, raw_slot },
                );
                try emitMemcpyBytes(emitter, state, err_pay_ptr, 1, raw_slot, 8, copy_sz);
            }
        },
    }
}

/// Emits LLVM 20–23 terminator instructions (`ret`, `br`, `switch`, `call` + `swifterror`) for `term`.
fn emitMirTerminatorLlvm(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body_idx: u32,
    body: *const MirBody,
    bb_idx: u32,
    term: mir.MirTerminator,
) !void {
    const ptr_int = ptrIntType(emitter);

    switch (term.kind) {
        .unreachable_term => {
            try state.writeAll("  unreachable");
            try appendTerminatorMetaSuffix(state, 0);
        },

        .trap => {
            try state.print("  call void @_cx_rt_trap(i32 {d})", .{term.aux_u8});
            try appendTerminatorMetaSuffix(state, 0);
            try state.writeAll("  unreachable\n");
        },

        .ret => {
            const recipe = &emitter.body_recipes.items[body_idx];
            const ret_decl = try formatAbiReturnDecl(emitter, body.ret_ty, recipe);
            defer emitter.allocator.free(ret_decl.full_decl);
            defer emitter.allocator.free(ret_decl.bare_ty);

            const is_zst_ret = try isZeroSizedType(emitter, body.ret_ty);
            if (is_zst_ret and recipe.calling_conv != .cx_result_cc) {
                try state.writeAll("  ret void");
                try appendTerminatorMetaSuffix(state, 0);
                return;
            }

            const unwrapped_ret = emitter.input.pool.unwrapUnderlyingType(body.ret_ty);
            const ret_lay = try emitter.resolver.resolveType(unwrapped_ret);
            const is_result_ret = !unwrapped_ret.isPrimitiveOrSentinel() and
                emitter.input.pool.getNode(unwrapped_ret).tag == .result_ty;
            const needs_mem_view = recipe.calling_conv == .cx_result_cc or
                recipe.has_sret or
                (!emitter.cfg.is_release_mode and is_result_ret);

            var ret_val_ssa: []u8 = &.{};
            defer if (ret_val_ssa.len > 0) emitter.allocator.free(ret_val_ssa);
            var ret_mem_ptr: []u8 = &.{};
            defer if (ret_mem_ptr.len > 0) emitter.allocator.free(ret_mem_ptr);

            if (!is_zst_ret) {
                if (term.cond_or_val != mir.NONE_U32) {
                    ret_val_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{term.cond_or_val});
                    if (needs_mem_view) {
                        ret_mem_ptr = try state.allocEntryBytes(ret_lay.size_bytes, ret_lay.alignBytes());
                        try emitMemsetZero(emitter, state, ret_mem_ptr, ret_lay.size_bytes, ret_lay.alignBytes());
                        try emitStoreValueToPtr(
                            emitter,
                            state,
                            unwrapped_ret,
                            ret_val_ssa,
                            ret_mem_ptr,
                            ret_lay.alignBytes(),
                            0,
                            0,
                            0,
                        );
                    }
                } else {
                    const loc0_ptr = state.local_ptrs[0];
                    if (needs_mem_view) {
                        ret_mem_ptr = try emitter.allocator.dupe(u8, loc0_ptr);
                    }
                    if (recipe.calling_conv != .cx_result_cc and !recipe.has_sret) {
                        ret_val_ssa = try emitLoadValueFromPtr(
                            emitter,
                            state,
                            unwrapped_ret,
                            loc0_ptr,
                            ret_lay.alignBytes(),
                            null,
                            0,
                            0,
                            0,
                        );
                    }
                }
            }

            // `--dev` 16-slot `ErrorReturnTrace` recording (`0` bytes in `--release`, `D-06B`).
            if (!emitter.cfg.is_release_mode and is_result_ret and ret_mem_ptr.len > 0) {
                const discr_s = try emitReadSumDiscriminantFromPtr(
                    emitter,
                    state,
                    unwrapped_ret,
                    ret_mem_ptr,
                    ret_lay.alignBytes(),
                );
                defer emitter.allocator.free(discr_s);
                const site_tag: u64 = (@as(u64, body_idx + 1) << 16) | @as(u64, bb_idx);
                const tr_id = state.nextTmp();
                try state.print(
                    "  %_ert_is_{d} = icmp eq i32 {s}, 1\n" ++
                        "  br i1 %_ert_is_{d}, label %_ert_rec_{d}, label %_ert_cont_{d}\n" ++
                        "_ert_rec_{d}:\n" ++
                        "  call void @_cx_record_err_ret({s} {d})\n" ++
                        "  br label %_ert_cont_{d}\n" ++
                        "_ert_cont_{d}:\n",
                    .{ tr_id, discr_s, tr_id, tr_id, tr_id, tr_id, ptr_int, site_tag, tr_id, tr_id },
                );
                state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_ert_cont_{d}", .{tr_id}));
            }

            if (recipe.calling_conv == .cx_result_cc) {
                const sum_detail = (try emitter.resolver.getSumDetail(unwrapped_ret)).?;
                const discr_s = if (ret_mem_ptr.len > 0)
                    try emitReadSumDiscriminantFromPtr(
                        emitter,
                        state,
                        unwrapped_ret,
                        ret_mem_ptr,
                        ret_lay.alignBytes(),
                    )
                else
                    try emitter.allocator.dupe(u8, "0");
                defer emitter.allocator.free(discr_s);

                const tmp_id = state.nextTmp();
                try state.print(
                    "  %_rc_is_err_{d} = icmp ne i32 {s}, 0\n" ++
                        "  br i1 %_rc_is_err_{d}, label %_rc_err_{d}, label %_rc_ok_{d}\n" ++
                        "_rc_err_{d}:\n",
                    .{ tmp_id, discr_s, tmp_id, tmp_id, tmp_id, tmp_id },
                );

                const err_pay_ptr = if (ret_mem_ptr.len == 0)
                    try std.fmt.allocPrint(emitter.allocator, "inttoptr ({s} 1 to ptr)", .{ptr_int})
                else if (sum_detail.payload_offset == 0)
                    try emitter.allocator.dupe(u8, ret_mem_ptr)
                else blk: {
                    try state.print(
                        "  %_rc_ep_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                        .{ tmp_id, ret_mem_ptr, ptr_int, sum_detail.payload_offset },
                    );
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_rc_ep_{d}", .{tmp_id});
                };
                defer emitter.allocator.free(err_pay_ptr);

                try emitStoreSwifterrorFromPayloadPtr(emitter, state, recipe, err_pay_ptr);
                if (std.mem.eql(u8, ret_decl.bare_ty, "void")) {
                    try state.writeAll("  ret void\n");
                } else {
                    try state.print(
                        "  ret {s} {s}\n",
                        .{ ret_decl.bare_ty, resolveZeroLiteralForLlvmType(ret_decl.bare_ty) },
                    );
                }

                try state.print("_rc_ok_{d}:\n", .{tmp_id});
                state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_rc_ok_{d}", .{tmp_id}));
                if (std.mem.eql(u8, ret_decl.bare_ty, "void") or
                    (try isZeroSizedType(emitter, recipe.ok_ty)))
                {
                    try state.writeAll("  ret void");
                    try appendTerminatorMetaSuffix(state, 0);
                } else {
                    const ok_lay = try emitter.resolver.resolveType(recipe.ok_ty);
                    const ok_pay_ptr = if (sum_detail.payload_offset == 0)
                        try emitter.allocator.dupe(u8, ret_mem_ptr)
                    else blk: {
                        try state.print(
                            "  %_rc_op_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                            .{ tmp_id, ret_mem_ptr, ptr_int, sum_detail.payload_offset },
                        );
                        break :blk try std.fmt.allocPrint(emitter.allocator, "%_rc_op_{d}", .{tmp_id});
                    };
                    defer emitter.allocator.free(ok_pay_ptr);

                    const ok_val_s = try emitLoadValueFromPtr(
                        emitter,
                        state,
                        recipe.ok_ty,
                        ok_pay_ptr,
                        @min(ret_lay.alignBytes(), ok_lay.alignBytes()),
                        null,
                        0,
                        0,
                        0,
                    );
                    defer emitter.allocator.free(ok_val_s);
                    const coerced_ok = try emitCoerceValueToAbi(
                        emitter,
                        state,
                        recipe.ok_ty,
                        ok_val_s,
                        ret_decl.bare_ty,
                    );
                    defer emitter.allocator.free(coerced_ok);
                    try state.print("  ret {s} {s}", .{ ret_decl.bare_ty, coerced_ok });
                    try appendTerminatorMetaSuffix(state, 0);
                }
                return;
            }

            if (recipe.has_sret) {
                try emitMemcpyBytes(
                    emitter,
                    state,
                    "%_sret",
                    recipe.sret_recipe.pointee_align_bytes,
                    ret_mem_ptr,
                    ret_lay.alignBytes(),
                    ret_lay.size_bytes,
                );
                try state.writeAll("  ret void");
                try appendTerminatorMetaSuffix(state, 0);
                return;
            }

            if (std.mem.eql(u8, ret_decl.bare_ty, "void")) {
                try state.writeAll("  ret void");
                try appendTerminatorMetaSuffix(state, 0);
                return;
            }

            const coerced_ret = try emitCoerceValueToAbi(
                emitter,
                state,
                body.ret_ty,
                ret_val_ssa,
                ret_decl.bare_ty,
            );
            defer emitter.allocator.free(coerced_ret);
            try state.print("  ret {s} {s}", .{ ret_decl.bare_ty, coerced_ret });
            try appendTerminatorMetaSuffix(state, 0);
        },

        .br => {
            const edge = body.extra_edges.items[term.edge_start];
            const dest_lbl = try resolveEdgeTargetAndRecordPred(
                emitter,
                state,
                term.edge_start,
                edge.target_bb,
            );
            defer emitter.allocator.free(dest_lbl);
            const loop_md = lookupLatchLoopMd(state, bb_idx, edge.target_bb, null);
            try state.print("  br label %{s}", .{dest_lbl});
            try appendTerminatorMetaSuffix(state, loop_md);
        },

        .cond_br => {
            const then_edge = body.extra_edges.items[term.edge_start];
            const else_edge = body.extra_edges.items[term.edge_start + 1];
            const then_lbl = try resolveEdgeTargetAndRecordPred(
                emitter,
                state,
                term.edge_start,
                then_edge.target_bb,
            );
            defer emitter.allocator.free(then_lbl);
            const else_lbl = try resolveEdgeTargetAndRecordPred(
                emitter,
                state,
                term.edge_start + 1,
                else_edge.target_bb,
            );
            defer emitter.allocator.free(else_lbl);

            const loop_md = lookupLatchLoopMd(
                state,
                bb_idx,
                then_edge.target_bb,
                else_edge.target_bb,
            );
            try state.print(
                "  br i1 %_v_{d}, label %{s}, label %{s}",
                .{ term.cond_or_val, then_lbl, else_lbl },
            );
            try appendTerminatorMetaSuffix(state, loop_md);
        },

        .switch_int => {
            const discr_val = MirValueId.fromInt(term.cond_or_val);
            const discr_ty = emitter.input.pool.unwrapUnderlyingType(body.getInst(discr_val).type_id);
            var switch_bits: u16 = 64;
            var discr_ssa: []u8 = undefined;
            if (discr_ty == .bool_ty) {
                switch_bits = 8;
                const tmp_id = state.nextTmp();
                try state.print("  %_sw_b8_{d} = zext i1 %_v_{d} to i8\n", .{ tmp_id, term.cond_or_val });
                discr_ssa = try std.fmt.allocPrint(emitter.allocator, "%_sw_b8_{d}", .{tmp_id});
            } else {
                const d_info = resolveIntegerInfo(emitter, discr_ty) orelse
                    IntScalarInfo{ .bits = 64, .is_signed = false };
                switch_bits = d_info.bits;
                discr_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{term.cond_or_val});
            }
            defer emitter.allocator.free(discr_ssa);

            const def_edge_idx: u32 = term.edge_start + term.edge_len - 1;
            const def_edge = body.extra_edges.items[def_edge_idx];
            const def_lbl = try resolveEdgeTargetAndRecordPred(
                emitter,
                state,
                def_edge_idx,
                def_edge.target_bb,
            );
            defer emitter.allocator.free(def_lbl);

            try state.print(
                "  switch i{d} {s}, label %{s} [\n",
                .{ switch_bits, discr_ssa, def_lbl },
            );

            var seen_cases: std.AutoHashMapUnmanaged(u128, void) = .empty;
            defer seen_cases.deinit(emitter.allocator);
            const bit_mask: u128 = if (switch_bits >= 128)
                std.math.maxInt(u128)
            else
                (@as(u128, 1) << @intCast(switch_bits)) - 1;

            var case_i: u32 = 0;
            while (case_i + 1 < term.edge_len) : (case_i += 1) {
                const edge_idx: u32 = term.edge_start + case_i;
                const edge = body.extra_edges.items[edge_idx];
                const raw_i128 = body.switch_values.items[edge.case_tag_idx];
                const masked_u128: u128 = (@as(u128, @bitCast(raw_i128))) & bit_mask;
                if ((try seen_cases.getOrPut(emitter.allocator, masked_u128)).found_existing) continue;

                const case_lbl = try resolveEdgeTargetAndRecordPred(
                    emitter,
                    state,
                    edge_idx,
                    edge.target_bb,
                );
                defer emitter.allocator.free(case_lbl);
                if (switch_bits == 128) {
                    try state.print(
                        "    i128 {d}, label %{s}\n",
                        .{ raw_i128, case_lbl },
                    );
                } else {
                    try state.print(
                        "    i{d} {d}, label %{s}\n",
                        .{ switch_bits, masked_u128, case_lbl },
                    );
                }
            }
            try state.writeAll("  ]");
            try appendTerminatorMetaSuffix(state, 0);
        },

        .call => {
            const call_site = body.calls.items[term.cond_or_val];
            if (!call_site.origin_token.isNone() and state.subprogram_md != 0) {
                state.active_dbg_loc_md = try resolveTokenDebugLocMd(
                    emitter,
                    state.subprogram_md,
                    body.file_id,
                    call_site.origin_token,
                );
            }

            var owned_recipe: ?AbiFnRecipe = null;
            defer if (owned_recipe) |*owned| owned.deinit(emitter.allocator);

            var callee_recipe: *const AbiFnRecipe = undefined;
            var callee_ret_ty: TypeId = call_site.ret_ty;
            var callee_sig_view: ?FnSignatureView = null;
            var is_closure_call = false;
            var closure_env_ssa: ?[]u8 = null;
            defer if (closure_env_ssa) |env_s| emitter.allocator.free(env_s);

            const callee_op: []u8 = if (resolveBodyIndex(
                emitter,
                call_site.direct_def_id,
                call_site.direct_symbol,
            )) |target_b| blk: {
                callee_recipe = &emitter.body_recipes.items[target_b];
                callee_ret_ty = emitter.input.bodies[target_b].ret_ty;
                if (emitter.input.is_dev_got_enabled) {
                    const got_id = state.nextTmp();
                    try state.print(
                        "  %_cgot_p_{d} = getelementptr inbounds [{d} x ptr], " ++
                            "ptr @_cx_dev_got, {s} 0, {s} {d}\n" ++
                            "  %_cgot_f_{d} = load ptr, ptr %_cgot_p_{d}, align {d}\n",
                        .{
                            got_id,
                            @max(emitter.input.bodies.len, 1),
                            ptr_int,
                            ptr_int,
                            target_b,
                            got_id,
                            got_id,
                            emitter.cfg.target.ptrBytes(),
                        },
                    );
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_cgot_f_{d}", .{got_id});
                }
                break :blk try formatLlvmGlobalIdent(
                    emitter.allocator,
                    emitter.body_llvm_names.items[target_b],
                );
            } else if (!call_site.direct_symbol.isNone() and
                call_site.direct_symbol.asInt() < emitter.input.sym_table.symbols.items.len)
            blk: {
                const sym_rec = emitter.input.sym_table.getSymbol(call_site.direct_symbol).*;
                const ext_name = if (sym_rec.contract_flags.has_link_name and sym_rec.link_name_text.len > 0)
                    sym_rec.link_name_text
                else
                    sym_rec.name_text;
                callee_sig_view = emitter.input.pool.getFnSignatureView(sym_rec.type_id);
                if (callee_sig_view) |sv| callee_ret_ty = sv.ret_ty;
                owned_recipe = try classifyFnTypeAbi(emitter, sym_rec.type_id, true, true);
                callee_recipe = &owned_recipe.?;
                break :blk try formatLlvmGlobalIdent(emitter.allocator, ext_name);
            } else blk: {
                const callee_ty = emitter.input.pool.unwrapUnderlyingType(
                    body.getInst(call_site.callee_val).type_id,
                );
                callee_sig_view = emitter.input.pool.getFnSignatureView(callee_ty);
                if (callee_sig_view) |sv| callee_ret_ty = sv.ret_ty;
                is_closure_call = emitter.input.pool.getNode(callee_ty).tag == .closure_ty;
                owned_recipe = try classifyFnTypeAbi(
                    emitter,
                    callee_ty,
                    false,
                    if (is_closure_call) true else null,
                );
                callee_recipe = &owned_recipe.?;
                if (is_closure_call) {
                    const cl_id = state.nextTmp();
                    try state.print(
                        "  %_cl_env_{d} = extractvalue {{ ptr, ptr }} %_v_{d}, 0\n" ++
                            "  %_cl_fn_{d} = extractvalue {{ ptr, ptr }} %_v_{d}, 1\n",
                        .{ cl_id, call_site.callee_val.asInt(), cl_id, call_site.callee_val.asInt() },
                    );
                    closure_env_ssa = try std.fmt.allocPrint(emitter.allocator, "%_cl_env_{d}", .{cl_id});
                    break :blk try std.fmt.allocPrint(emitter.allocator, "%_cl_fn_{d}", .{cl_id});
                }
                break :blk try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{call_site.callee_val.asInt()});
            };
            defer emitter.allocator.free(callee_op);

            var call_args_buf: std.ArrayListUnmanaged(u8) = .empty;
            defer call_args_buf.deinit(emitter.allocator);
            var emitted_arg_count: usize = 0;

            var sret_slot: ?[]u8 = null;
            defer if (sret_slot) |s_ptr| emitter.allocator.free(s_ptr);
            if (callee_recipe.has_sret) {
                const ret_lay = try emitter.resolver.resolveType(callee_ret_ty);
                const slot = try state.allocEntryBytes(
                    ret_lay.size_bytes,
                    @max(ret_lay.alignBytes(), callee_recipe.sret_recipe.pointee_align_bytes),
                );
                try emitMemsetZero(
                    emitter,
                    state,
                    slot,
                    ret_lay.size_bytes,
                    @max(ret_lay.alignBytes(), callee_recipe.sret_recipe.pointee_align_bytes),
                );
                const sret_piece = try formatAbiParamDeclPiece(
                    emitter,
                    callee_ret_ty,
                    callee_recipe.sret_recipe,
                    slot,
                );
                defer emitter.allocator.free(sret_piece);
                try call_args_buf.appendSlice(emitter.allocator, sret_piece);
                emitted_arg_count += 1;
                sret_slot = slot;
            }

            if (is_closure_call) {
                if (emitted_arg_count > 0) try call_args_buf.appendSlice(emitter.allocator, ", ");
                const env_piece = try std.fmt.allocPrint(
                    emitter.allocator,
                    "ptr nonnull noundef {s}",
                    .{closure_env_ssa.?},
                );
                defer emitter.allocator.free(env_piece);
                try call_args_buf.appendSlice(emitter.allocator, env_piece);
                emitted_arg_count += 1;
            } else if (callee_recipe.has_implicit_context) {
                const caller_has_ctx = emitter.body_recipes.items[body_idx].has_implicit_context;
                const ctx_op = if (caller_has_ctx) "%_cx_ctx" else "@_cx_default_ctx";
                const ctx_piece = try formatAbiParamDeclPiece(
                    emitter,
                    .usize_ty,
                    callee_recipe.context_recipe,
                    ctx_op,
                );
                defer emitter.allocator.free(ctx_piece);
                if (emitted_arg_count > 0) try call_args_buf.appendSlice(emitter.allocator, ", ");
                try call_args_buf.appendSlice(emitter.allocator, ctx_piece);
                emitted_arg_count += 1;
            }

            var inout_writebacks: std.ArrayListUnmanaged(InoutBounceWriteback) = .empty;
            defer {
                for (inout_writebacks.items) |wb| {
                    emitter.allocator.free(wb.bounce_ptr);
                    emitter.allocator.free(wb.dst_ptr);
                }
                inout_writebacks.deinit(emitter.allocator);
            }

            const direct_target_body = resolveBodyIndex(
                emitter,
                call_site.direct_def_id,
                call_site.direct_symbol,
            );
            var arg_i: usize = 0;
            while (arg_i < call_site.args_len and arg_i < callee_recipe.param_recipes.len) : (arg_i += 1) {
                const p_rec = callee_recipe.param_recipes[arg_i];
                if (p_rec.pass_mode == .ignore_zst) continue;

                const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                const word = body.extra_args.items[call_site.args_start + arg_i];
                const formal_ty: TypeId = if (direct_target_body) |tb_idx|
                    emitter.input.bodies[tb_idx].locals.items[1 + arg_i].type_id
                else if (callee_sig_view) |sv|
                    sv.getParamType(arg_i)
                else if (mode == .let_mode or mode == .sink_mode)
                    body.getInst(MirValueId.fromInt(word)).type_id
                else
                    resolvePlaceResultType(emitter, body, PlaceId.fromInt(word));

                const arg_operand_s: []u8 = if (mode == .inout_mode or mode == .set_mode) blk: {
                    switch (try lowerPlaceLlvm(emitter, state, body, PlaceId.fromInt(word))) {
                        .const_len => break :blk try std.fmt.allocPrint(
                            emitter.allocator,
                            "inttoptr ({s} 1 to ptr)",
                            .{ptr_int},
                        ),
                        .addr_val => |av| {
                            if (try isZeroSizedType(emitter, av.pointee_ty)) {
                                emitter.allocator.free(av.ptr_str);
                                const z_lay = try emitter.resolver.resolveType(av.pointee_ty);
                                break :blk try std.fmt.allocPrint(
                                    emitter.allocator,
                                    "inttoptr ({s} {d} to ptr)",
                                    .{ ptr_int, z_lay.alignBytes() },
                                );
                            }
                            if (av.align_bytes < p_rec.pointee_align_bytes) {
                                const p_lay = try emitter.resolver.resolveType(av.pointee_ty);
                                const bounce_align = @max(p_lay.alignBytes(), p_rec.pointee_align_bytes);
                                const bounce_slot = try state.allocEntryBytes(p_lay.size_bytes, bounce_align);
                                if (mode == .inout_mode) {
                                    try emitMemcpyBytes(
                                        emitter,
                                        state,
                                        bounce_slot,
                                        bounce_align,
                                        av.ptr_str,
                                        av.align_bytes,
                                        p_lay.size_bytes,
                                    );
                                } else {
                                    try emitMemsetZero(emitter, state, bounce_slot, p_lay.size_bytes, bounce_align);
                                }
                                try inout_writebacks.append(emitter.allocator, .{
                                    .bounce_ptr = try emitter.allocator.dupe(u8, bounce_slot),
                                    .bounce_align = bounce_align,
                                    .dst_ptr = av.ptr_str,
                                    .dst_align = av.align_bytes,
                                    .size_bytes = p_lay.size_bytes,
                                });
                                break :blk bounce_slot;
                            }
                            break :blk av.ptr_str;
                        },
                    }
                } else blk: {
                    const val_ty = body.getInst(MirValueId.fromInt(word)).type_id;
                    const val_ssa = try std.fmt.allocPrint(emitter.allocator, "%_v_{d}", .{word});
                    defer emitter.allocator.free(val_ssa);
                    if (p_rec.pass_mode == .indirect_by_ref or p_rec.pass_mode == .indirect_byval) {
                        const v_lay = try emitter.resolver.resolveType(val_ty);
                        const copy_align = @max(v_lay.alignBytes(), p_rec.pointee_align_bytes);
                        const copy_slot = try state.allocEntryBytes(v_lay.size_bytes, copy_align);
                        try emitMemsetZero(emitter, state, copy_slot, v_lay.size_bytes, copy_align);
                        try emitStoreValueToPtr(emitter, state, val_ty, val_ssa, copy_slot, copy_align, 0, 0, 0);
                        break :blk copy_slot;
                    }
                    const abi_ty = try formatAbiParamOrRetType(emitter, formal_ty, p_rec);
                    defer emitter.allocator.free(abi_ty);
                    break :blk try emitCoerceValueToAbi(emitter, state, val_ty, val_ssa, abi_ty);
                };
                defer emitter.allocator.free(arg_operand_s);

                const arg_piece = try formatAbiParamDeclPiece(emitter, formal_ty, p_rec, arg_operand_s);
                defer emitter.allocator.free(arg_piece);
                if (emitted_arg_count > 0) try call_args_buf.appendSlice(emitter.allocator, ", ");
                try call_args_buf.appendSlice(emitter.allocator, arg_piece);
                emitted_arg_count += 1;
            }

            if (callee_recipe.swifterror_kind != .none) {
                try state.ensureSwifterrorCallSlot();
                if (emitted_arg_count > 0) try call_args_buf.appendSlice(emitter.allocator, ", ");
                try call_args_buf.appendSlice(emitter.allocator, "ptr swifterror %_cx_call_err");
                try state.writeAll("  store ptr null, ptr %_cx_call_err, align 8\n");
            }

            const ret_decl = try formatAbiReturnDecl(emitter, callee_ret_ty, callee_recipe);
            defer emitter.allocator.free(ret_decl.full_decl);
            defer emitter.allocator.free(ret_decl.bare_ty);
            const is_void_abi = std.mem.eql(u8, ret_decl.bare_ty, "void");

            const normal_edge = body.extra_edges.items[term.edge_start];
            const dst_params = body.getBlockParams(normal_edge.target_bb);
            const has_ret_dest = !(try isZeroSizedType(emitter, call_site.ret_ty)) and
                dst_params.len >= 1 and
                !(try isZeroSizedType(emitter, body.getInst(dst_params[0]).type_id));

            // Check Pentagon `!range` on direct scalar integer call returns (`[MAJOR-08]`).
            var call_range_md: ?u32 = null;
            if (!is_void_abi and callee_recipe.swifterror_kind == .none and has_ret_dest) {
                const dst_ty = body.getInst(dst_params[0]).type_id;
                if (resolveIntegerInfo(emitter, dst_ty)) |d_info| {
                    if (d_info.bits <= 64) {
                        const expect_abi = try std.fmt.allocPrint(emitter.allocator, "i{d}", .{d_info.bits});
                        defer emitter.allocator.free(expect_abi);
                        if (std.mem.eql(u8, ret_decl.bare_ty, expect_abi)) {
                            if (lookupProvenRange(emitter, body_idx, dst_params[0].asInt())) |prov_r| {
                                if (prov_r.bit_width == d_info.bits) {
                                    call_range_md = try getOrInternValidRangeMd(emitter, prov_r);
                                }
                            }
                        }
                    }
                }
            }

            const call_tmp = state.nextTmp();
            if (is_void_abi) {
                try state.print(
                    "  call {s}void {s}({s})",
                    .{ resolveCallingConvPrefix(callee_recipe), callee_op, call_args_buf.items },
                );
            } else {
                try state.print(
                    "  %_call_rv_{d} = call {s}{s} {s}({s})",
                    .{
                        call_tmp,
                        resolveCallingConvPrefix(callee_recipe),
                        ret_decl.full_decl,
                        callee_op,
                        call_args_buf.items,
                    },
                );
            }
            if (call_range_md) |r_md| {
                if (emitter.di_empty_tuple_md == 0) {
                    emitter.di_empty_tuple_md = try emitter.addMetadataNode("!{}");
                }
                try state.print(", !range !{d}, !noundef !{d}", .{ r_md, emitter.di_empty_tuple_md });
            }
            if (state.active_dbg_loc_md != 0) {
                try state.print(", !dbg !{d}", .{state.active_dbg_loc_md});
            }
            try state.writeAll("\n");

            for (inout_writebacks.items) |wb| {
                try emitMemcpyBytes(
                    emitter,
                    state,
                    wb.dst_ptr,
                    wb.dst_align,
                    wb.bounce_ptr,
                    wb.bounce_align,
                    wb.size_bytes,
                );
            }

            if (callee_recipe.swifterror_kind != .none) {
                // LLVM `SwiftErrorVerifier` invariant: load `%_cx_call_err` immediately in the same block!
                try state.print(
                    "  %_cerr_v_{d} = load ptr, ptr %_cx_call_err, align 8\n",
                    .{call_tmp},
                );
                if (has_ret_dest) {
                    const dst_ty = try unwrapTransparentType(emitter, body.getInst(dst_params[0]).type_id);
                    const res_lay = try emitter.resolver.resolveType(dst_ty);
                    const sum_detail = (try emitter.resolver.getSumDetail(dst_ty)).?;
                    const res_slot = try state.allocEntryBytes(res_lay.size_bytes, res_lay.alignBytes());
                    defer emitter.allocator.free(res_slot);
                    try emitMemsetZero(emitter, state, res_slot, res_lay.size_bytes, res_lay.alignBytes());

                    try state.print(
                        "  %_has_ce_{d} = icmp ne ptr %_cerr_v_{d}, null\n" ++
                            "  br i1 %_has_ce_{d}, label %_ce_err_{d}, label %_ce_ok_{d}\n" ++
                            "_ce_err_{d}:\n",
                        .{ call_tmp, call_tmp, call_tmp, call_tmp, call_tmp, call_tmp },
                    );
                    const res_pay_ptr = if (sum_detail.payload_offset == 0)
                        try emitter.allocator.dupe(u8, res_slot)
                    else blk: {
                        try state.print(
                            "  %_ce_pp_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                            .{ call_tmp, res_slot, ptr_int, sum_detail.payload_offset },
                        );
                        break :blk try std.fmt.allocPrint(emitter.allocator, "%_ce_pp_{d}", .{call_tmp});
                    };
                    defer emitter.allocator.free(res_pay_ptr);

                    const cerr_name = try std.fmt.allocPrint(emitter.allocator, "%_cerr_v_{d}", .{call_tmp});
                    defer emitter.allocator.free(cerr_name);
                    try emitDecodeSwifterrorToPayloadPtr(emitter, state, callee_recipe, cerr_name, res_pay_ptr);
                    try emitWriteSumDiscriminantToPtr(emitter, state, dst_ty, res_slot, res_lay.alignBytes(), 1);
                    try state.print("  br label %_ce_join_{d}\n_ce_ok_{d}:\n", .{ call_tmp, call_tmp });

                    if (!is_void_abi and !(try isZeroSizedType(emitter, callee_recipe.ok_ty))) {
                        const ok_pay_ptr = if (sum_detail.payload_offset == 0)
                            try emitter.allocator.dupe(u8, res_slot)
                        else blk: {
                            try state.print(
                                "  %_co_pp_{d} = getelementptr inbounds i8, ptr {s}, {s} {d}\n",
                                .{ call_tmp, res_slot, ptr_int, sum_detail.payload_offset },
                            );
                            break :blk try std.fmt.allocPrint(emitter.allocator, "%_co_pp_{d}", .{call_tmp});
                        };
                        defer emitter.allocator.free(ok_pay_ptr);

                        const raw_rv_s = try std.fmt.allocPrint(emitter.allocator, "%_call_rv_{d}", .{call_tmp});
                        defer emitter.allocator.free(raw_rv_s);
                        const unpacked_ok = try emitCoerceAbiToValue(
                            emitter,
                            state,
                            callee_recipe.ok_ty,
                            ret_decl.bare_ty,
                            raw_rv_s,
                        );
                        defer emitter.allocator.free(unpacked_ok);
                        const ok_lay = try emitter.resolver.resolveType(callee_recipe.ok_ty);
                        try emitStoreValueToPtr(
                            emitter,
                            state,
                            callee_recipe.ok_ty,
                            unpacked_ok,
                            ok_pay_ptr,
                            @min(res_lay.alignBytes(), ok_lay.alignBytes()),
                            0,
                            0,
                            0,
                        );
                    }
                    try emitWriteSumDiscriminantToPtr(emitter, state, dst_ty, res_slot, res_lay.alignBytes(), 0);
                    try state.print("  br label %_ce_join_{d}\n_ce_join_{d}:\n", .{ call_tmp, call_tmp });
                    state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_ce_join_{d}", .{call_tmp}));

                    state.edge_call_ret_vals[term.edge_start] = try emitLoadValueFromPtr(
                        emitter,
                        state,
                        dst_ty,
                        res_slot,
                        res_lay.alignBytes(),
                        null,
                        0,
                        0,
                        0,
                    );
                }
            } else if (has_ret_dest) {
                const dst_ty = try unwrapTransparentType(emitter, body.getInst(dst_params[0]).type_id);
                if (callee_recipe.has_sret) {
                    const ret_lay = try emitter.resolver.resolveType(dst_ty);
                    state.edge_call_ret_vals[term.edge_start] = try emitLoadValueFromPtr(
                        emitter,
                        state,
                        dst_ty,
                        sret_slot.?,
                        ret_lay.alignBytes(),
                        null,
                        0,
                        0,
                        0,
                    );
                } else {
                    const raw_rv_s = try std.fmt.allocPrint(emitter.allocator, "%_call_rv_{d}", .{call_tmp});
                    defer emitter.allocator.free(raw_rv_s);
                    state.edge_call_ret_vals[term.edge_start] = try emitCoerceAbiToValue(
                        emitter,
                        state,
                        dst_ty,
                        ret_decl.bare_ty,
                        raw_rv_s,
                    );
                }
            }

            const dest_lbl = try resolveEdgeTargetAndRecordPred(
                emitter,
                state,
                term.edge_start,
                normal_edge.target_bb,
            );
            defer emitter.allocator.free(dest_lbl);
            try state.print("  br label %{s}\n", .{dest_lbl});
        },
    }
}

/// Returns `true` when formal parameter `loc_decl` / `p_rec` participates in MVS `!alias.scope` metadata.
fn isMvsAliasScopedParam(
    emitter: *const LlvmModuleEmitter,
    loc_decl: mir.LocalDecl,
    p_rec: AbiParamRecipe,
) bool {
    const mode = loc_decl.mode();
    if (mode == .inout_mode or mode == .set_mode) return true;
    if (p_rec.pass_mode == .indirect_by_ref) return true;
    const unwrapped = emitter.input.pool.unwrapUnderlyingType(loc_decl.type_id);
    if (unwrapped.isPrimitiveOrSentinel()) return false;
    return switch (emitter.input.pool.getNode(unwrapped).tag) {
        .ref_ty, .mut_ref_ty, .slice_ty, .soa_slice_ty => true,
        else => false,
    };
}

/// Builds MVS `!alias.scope` / `!noalias` metadata nodes (`DR-09` §4.1) for `body_idx`.
fn buildFunctionMvsAliasScopes(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body_idx: u32,
    body: *const MirBody,
    recipe: *const AbiFnRecipe,
) !void {
    var scoped_locals: std.ArrayListUnmanaged(u32) = .empty;
    defer scoped_locals.deinit(emitter.allocator);

    var param_i: u32 = 0;
    while (param_i < body.param_count and param_i < recipe.param_recipes.len) : (param_i += 1) {
        const p_rec = recipe.param_recipes[param_i];
        if (p_rec.pass_mode == .ignore_zst) continue;
        const loc_idx = 1 + param_i;
        if (isMvsAliasScopedParam(emitter, body.locals.items[loc_idx], p_rec)) {
            try scoped_locals.append(emitter.allocator, loc_idx);
        }
    }
    if (scoped_locals.items.len == 0) return;

    const esc_dom_name = try escapeMetadataStringAlloc(
        emitter.allocator,
        emitter.body_llvm_names.items[body_idx],
    );
    defer emitter.allocator.free(esc_dom_name);

    const domain_md = emitter.reserveMetadataId();
    const dom_rhs = try std.fmt.allocPrint(
        emitter.allocator,
        "distinct !{{!{d}, !\"{s}:mvs_domain\"}}",
        .{ domain_md, esc_dom_name },
    );
    defer emitter.allocator.free(dom_rhs);
    try emitter.defineReservedMetadata(domain_md, dom_rhs);

    var raw_scope_mds = try emitter.allocator.alloc(u32, scoped_locals.items.len);
    defer emitter.allocator.free(raw_scope_mds);
    var scope_list_mds = try emitter.allocator.alloc(u32, scoped_locals.items.len);
    defer emitter.allocator.free(scope_list_mds);
    var is_exclusive = try emitter.allocator.alloc(bool, scoped_locals.items.len);
    defer emitter.allocator.free(is_exclusive);

    for (scoped_locals.items, 0..) |loc_idx, idx| {
        const loc_decl = body.locals.items[loc_idx];
        const mode = loc_decl.mode();
        const unwrapped = emitter.input.pool.unwrapUnderlyingType(loc_decl.type_id);
        const is_mut_ref = !unwrapped.isPrimitiveOrSentinel() and
            emitter.input.pool.getNode(unwrapped).tag == .mut_ref_ty;
        is_exclusive[idx] = (mode == .inout_mode or mode == .set_mode or is_mut_ref);

        const sc_md = emitter.reserveMetadataId();
        raw_scope_mds[idx] = sc_md;
        const sc_rhs = try std.fmt.allocPrint(
            emitter.allocator,
            "distinct !{{!{d}, !{d}, !\"param_{d}\"}}",
            .{ sc_md, domain_md, loc_idx },
        );
        defer emitter.allocator.free(sc_rhs);
        try emitter.defineReservedMetadata(sc_md, sc_rhs);

        const list_rhs = try std.fmt.allocPrint(emitter.allocator, "!{{!{d}}}", .{sc_md});
        defer emitter.allocator.free(list_rhs);
        scope_list_mds[idx] = try emitter.addMetadataNode(list_rhs);
    }

    for (scoped_locals.items, 0..) |loc_idx, idx| {
        var noalias_md: u32 = 0;
        if (scoped_locals.items.len >= 2) {
            var list_buf: std.ArrayListUnmanaged(u8) = .empty;
            defer list_buf.deinit(emitter.allocator);
            try list_buf.appendSlice(emitter.allocator, "!{");
            var emitted_other: usize = 0;
            for (raw_scope_mds, 0..) |other_sc, other_idx| {
                if (other_idx == idx) continue;
                if (!is_exclusive[idx] and !is_exclusive[other_idx]) continue;
                if (emitted_other > 0) try list_buf.appendSlice(emitter.allocator, ", ");
                const elem_s = try std.fmt.allocPrint(emitter.allocator, "!{d}", .{other_sc});
                defer emitter.allocator.free(elem_s);
                try list_buf.appendSlice(emitter.allocator, elem_s);
                emitted_other += 1;
            }
            if (emitted_other > 0) {
                try list_buf.append(emitter.allocator, '}');
                noalias_md = try emitter.addMetadataNode(list_buf.items);
            }
        }
        try state.mvs_scopes.append(emitter.allocator, .{
            .local_idx = loc_idx,
            .scope_list_md = scope_list_mds[idx],
            .noalias_list_md = noalias_md,
        });
    }
}

/// Builds `!llvm.access.group` and `!llvm.loop` metadata nodes for `body.loop_contracts`.
fn buildFunctionLoopMetadata(
    emitter: *LlvmModuleEmitter,
    state: *BodyEmitState,
    body: *const MirBody,
) !void {
    const block_count = body.blocks.items.len;
    var in_loop = try emitter.allocator.alloc(bool, block_count);
    defer emitter.allocator.free(in_loop);
    var worklist: std.ArrayListUnmanaged(usize) = .empty;
    defer worklist.deinit(emitter.allocator);

    for (body.loop_contracts.items) |lc| {
        if (!lc.meta.contract_flags.is_must_vectorize and lc.meta.min_lanes == 0) continue;

        const access_grp_md = emitter.reserveMetadataId();
        try emitter.defineReservedMetadata(access_grp_md, "distinct !{}");

        const header_idx: usize = lc.header_bb.asInt();
        const latch_idx: usize = lc.latch_bb.asInt();
        if (header_idx < block_count and latch_idx < block_count and latch_idx < state.block_access_group.len) {
            @memset(in_loop, false);
            worklist.clearRetainingCapacity();
            in_loop[header_idx] = true;
            state.block_access_group[header_idx] = access_grp_md;
            if (!in_loop[latch_idx]) {
                in_loop[latch_idx] = true;
                state.block_access_group[latch_idx] = access_grp_md;
                try worklist.append(emitter.allocator, latch_idx);
            }
            while (worklist.pop()) |curr_bb| {
                for (body.blocks.items, 0..) |pred_blk, pred_i| {
                    if (in_loop[pred_i]) continue;
                    const p_term = pred_blk.terminator;
                    var e_off: u32 = 0;
                    while (e_off < p_term.edge_len) : (e_off += 1) {
                        const e_idx = p_term.edge_start + e_off;
                        if (e_idx < body.extra_edges.items.len and
                            body.extra_edges.items[e_idx].target_bb.asInt() == curr_bb)
                        {
                            in_loop[pred_i] = true;
                            state.block_access_group[pred_i] = access_grp_md;
                            try worklist.append(emitter.allocator, pred_i);
                            break;
                        }
                    }
                }
            }
        }

        const mp_md = try emitter.addMetadataNode("!{!\"llvm.loop.mustprogress\"}");
        const loop_md = emitter.reserveMetadataId();
        const ve_md = try emitter.addMetadataNode("!{!\"llvm.loop.vectorize.enable\", i1 true}");
        const pa_rhs = try std.fmt.allocPrint(
            emitter.allocator,
            "!{{!\"llvm.loop.parallel_accesses\", !{d}}}",
            .{access_grp_md},
        );
        defer emitter.allocator.free(pa_rhs);
        const pa_md = try emitter.addMetadataNode(pa_rhs);

        if (lc.meta.min_lanes > 0) {
            const vw_rhs = try std.fmt.allocPrint(
                emitter.allocator,
                "!{{!\"llvm.loop.vectorize.width\", i32 {d}}}",
                .{lc.meta.min_lanes},
            );
            defer emitter.allocator.free(vw_rhs);
            const vw_md = try emitter.addMetadataNode(vw_rhs);
            const loop_rhs = try std.fmt.allocPrint(
                emitter.allocator,
                "distinct !{{!{d}, !{d}, !{d}, !{d}, !{d}}}",
                .{ loop_md, mp_md, ve_md, pa_md, vw_md },
            );
            defer emitter.allocator.free(loop_rhs);
            try emitter.defineReservedMetadata(loop_md, loop_rhs);
        } else {
            const loop_rhs = try std.fmt.allocPrint(
                emitter.allocator,
                "distinct !{{!{d}, !{d}, !{d}, !{d}}}",
                .{ loop_md, mp_md, ve_md, pa_md },
            );
            defer emitter.allocator.free(loop_rhs);
            try emitter.defineReservedMetadata(loop_md, loop_rhs);
        }

        try state.loop_mds.append(emitter.allocator, .{
            .header_bb = lc.header_bb,
            .latch_bb = lc.latch_bb,
            .access_group_md = access_grp_md,
            .loop_md = loop_md,
        });
    }
}

/// Pre-scans multi-way terminators (`cond_br`, `switch_int`) for duplicate targets and registers `_bb_edge_*`.
fn precomputeDuplicateEdgeTrampolines(
    emitter: *const LlvmModuleEmitter,
    body: *const MirBody,
    state: *BodyEmitState,
) !void {
    const allocator = emitter.allocator;
    for (body.blocks.items) |bb| {
        const term = bb.terminator;
        if (term.kind == .cond_br) {
            const e0 = body.extra_edges.items[term.edge_start];
            const e1 = body.extra_edges.items[term.edge_start + 1];
            if (e0.target_bb == e1.target_bb) {
                const tramp_idx: u32 = @intCast(state.trampolines.items.len);
                state.edge_trampoline[term.edge_start + 1] = tramp_idx;
                try state.trampolines.append(allocator, .{
                    .tramp_idx = tramp_idx,
                    .edge_idx = term.edge_start + 1,
                    .target_bb = e1.target_bb,
                });
            }
        } else if (term.kind == .switch_int and term.edge_len > 1) {
            var seen_targets: std.AutoHashMapUnmanaged(u32, void) = .empty;
            defer seen_targets.deinit(allocator);
            var seen_cases: std.AutoHashMapUnmanaged(u128, void) = .empty;
            defer seen_cases.deinit(allocator);

            const discr_ty = emitter.input.pool.unwrapUnderlyingType(
                body.getInst(MirValueId.fromInt(term.cond_or_val)).type_id,
            );
            const switch_bits: u16 = if (discr_ty == .bool_ty)
                8
            else
                (resolveIntegerInfo(emitter, discr_ty) orelse
                    IntScalarInfo{ .bits = 64, .is_signed = false }).bits;
            const bit_mask: u128 = if (switch_bits >= 128)
                std.math.maxInt(u128)
            else
                (@as(u128, 1) << @intCast(switch_bits)) - 1;

            // Default arm (`edge_start + edge_len - 1`) claims its target first, then unique cases.
            const def_idx: u32 = term.edge_start + term.edge_len - 1;
            const def_target = body.extra_edges.items[def_idx].target_bb;
            try seen_targets.put(allocator, def_target.asInt(), {});

            var case_i: u32 = 0;
            while (case_i + 1 < term.edge_len) : (case_i += 1) {
                const edge_idx: u32 = term.edge_start + case_i;
                const edge = body.extra_edges.items[edge_idx];
                const raw_i128 = body.switch_values.items[edge.case_tag_idx];
                const masked_u128: u128 = (@as(u128, @bitCast(raw_i128))) & bit_mask;
                if ((try seen_cases.getOrPut(allocator, masked_u128)).found_existing) continue;

                const target_bb = edge.target_bb;
                if ((try seen_targets.getOrPut(allocator, target_bb.asInt())).found_existing) {
                    const tramp_idx: u32 = @intCast(state.trampolines.items.len);
                    state.edge_trampoline[edge_idx] = tramp_idx;
                    try state.trampolines.append(allocator, .{
                        .tramp_idx = tramp_idx,
                        .edge_idx = edge_idx,
                        .target_bb = target_bb,
                    });
                }
            }
        }
    }
}

/// Emits a complete `MirBody` as an LLVM 20–23 `define` function using two-pass `PHINode` stitching.
fn emitMirBody(emitter: *LlvmModuleEmitter, body_idx: u32, body: *const MirBody) !void {
    const recipe = &emitter.body_recipes.items[body_idx];
    const ret_decl = try formatAbiReturnDecl(emitter, body.ret_ty, recipe);
    defer emitter.allocator.free(ret_decl.full_decl);
    defer emitter.allocator.free(ret_decl.bare_ty);

    const local_count = body.locals.items.len;
    const edge_count = body.extra_edges.items.len;
    const block_count = body.blocks.items.len;

    const local_ptrs = try emitter.allocator.alloc([]u8, local_count);
    @memset(local_ptrs, &[_]u8{});
    const local_aligns = try emitter.allocator.alloc(u32, local_count);
    @memset(local_aligns, 1);
    const edge_pred_labels = try emitter.allocator.alloc([]u8, edge_count);
    @memset(edge_pred_labels, &[_]u8{});
    const edge_call_ret_vals = try emitter.allocator.alloc([]u8, edge_count);
    @memset(edge_call_ret_vals, &[_]u8{});
    const edge_trampoline = try emitter.allocator.alloc(?u32, edge_count);
    @memset(edge_trampoline, null);
    const block_access_group = try emitter.allocator.alloc(u32, block_count);
    @memset(block_access_group, 0);

    var state = BodyEmitState{
        .allocator = emitter.allocator,
        .cur_label = try emitter.allocator.dupe(u8, "_bb_0"),
        .local_ptrs = local_ptrs,
        .local_aligns = local_aligns,
        .edge_pred_labels = edge_pred_labels,
        .edge_call_ret_vals = edge_call_ret_vals,
        .edge_trampoline = edge_trampoline,
        .block_access_group = block_access_group,
        .subprogram_md = try createBodySubprogramMd(emitter, body_idx, body),
    };
    defer state.deinit();

    try buildFunctionMvsAliasScopes(emitter, &state, body_idx, body, recipe);
    try buildFunctionLoopMetadata(emitter, &state, body);
    try precomputeDuplicateEdgeTrampolines(emitter, body, &state);

    // [1] Emit `define` header with exact `AbiFnRecipe` attributes.
    const linkage_kw = if (isBodyExternallyVisible(emitter, body)) "" else "internal ";
    const fn_ident = try formatLlvmGlobalIdent(emitter.allocator, emitter.body_llvm_names.items[body_idx]);
    defer emitter.allocator.free(fn_ident);
    try emitter.print(
        "define {s}{s}{s} {s}(",
        .{ linkage_kw, resolveCallingConvPrefix(recipe), ret_decl.full_decl, fn_ident },
    );

    var sig_arg_count: usize = 0;
    if (recipe.has_sret) {
        const sret_s = try formatAbiParamDeclPiece(emitter, body.ret_ty, recipe.sret_recipe, "%_sret");
        defer emitter.allocator.free(sret_s);
        try emitter.writeAll(sret_s);
        sig_arg_count += 1;
    }
    if (recipe.has_implicit_context) {
        const ctx_s = try formatAbiParamDeclPiece(emitter, .usize_ty, recipe.context_recipe, "%_cx_ctx");
        defer emitter.allocator.free(ctx_s);
        if (sig_arg_count > 0) try emitter.writeAll(", ");
        try emitter.writeAll(ctx_s);
        sig_arg_count += 1;
    }
    var param_i: u32 = 0;
    while (param_i < body.param_count and param_i < recipe.param_recipes.len) : (param_i += 1) {
        const p_rec = recipe.param_recipes[param_i];
        if (p_rec.pass_mode == .ignore_zst) continue;
        const p_ty = body.locals.items[1 + param_i].type_id;
        const p_name = try std.fmt.allocPrint(emitter.allocator, "%_arg_p{d}", .{param_i});
        defer emitter.allocator.free(p_name);
        const piece_s = try formatAbiParamDeclPiece(emitter, p_ty, p_rec, p_name);
        defer emitter.allocator.free(piece_s);
        if (sig_arg_count > 0) try emitter.writeAll(", ");
        try emitter.writeAll(piece_s);
        sig_arg_count += 1;
    }
    if (recipe.swifterror_kind != .none) {
        if (sig_arg_count > 0) try emitter.writeAll(", ");
        try emitter.writeAll("ptr swifterror %_cx_err_slot");
    }
    try emitter.print(") {s}", .{fnUnwindAttrs(emitter)});
    if (state.subprogram_md != 0) {
        try emitter.print(" !dbg !{d}", .{state.subprogram_md});
    }
    try emitter.writeAll(" {\n");

    // [2] Allocate frame locals (`%_loc_0..N`) and entry prologue setup (`_bb_0` prologue buffer).
    var entry_prologue = BodyEmitState{
        .allocator = emitter.allocator,
        .cur_label = try emitter.allocator.dupe(u8, "_bb_0"),
        .local_ptrs = try emitter.allocator.alloc([]u8, 0),
        .local_aligns = try emitter.allocator.alloc(u32, 0),
        .edge_pred_labels = try emitter.allocator.alloc([]u8, 0),
        .edge_call_ret_vals = try emitter.allocator.alloc([]u8, 0),
        .edge_trampoline = try emitter.allocator.alloc(?u32, 0),
        .block_access_group = try emitter.allocator.alloc(u32, 0),
    };
    defer entry_prologue.deinit();

    // Hoist MVS `@llvm.experimental.noalias.scope.decl` strictly into `_bb_0` (`DR-09` §4.1).
    if (state.mvs_scopes.items.len > 0) {
        try emitter.requireIntrinsicDecl("declare void @llvm.experimental.noalias.scope.decl(metadata)");
        for (state.mvs_scopes.items) |mvs_sc| {
            try entry_prologue.print(
                "  call void @llvm.experimental.noalias.scope.decl(metadata !{d})\n",
                .{mvs_sc.scope_list_md},
            );
        }
    }

    for (body.locals.items, 0..) |loc_decl, loc_i| {
        const is_zst = try isZeroSizedType(emitter, loc_decl.type_id);
        const lay = try emitter.resolver.resolveType(loc_decl.type_id);
        state.local_aligns[loc_i] = lay.alignBytes();
        if (is_zst) continue;

        const is_param = loc_i >= 1 and loc_i <= body.param_count;
        const p_mode = loc_decl.mode();
        if (is_param and (p_mode == .inout_mode or p_mode == .set_mode)) {
            state.local_ptrs[loc_i] = try std.fmt.allocPrint(
                emitter.allocator,
                "%_arg_p{d}",
                .{loc_i - 1},
            );
            continue;
        }

        const mem_ty = try formatLlvmMemoryType(emitter, loc_decl.type_id);
        defer emitter.allocator.free(mem_ty);
        const eff_align = @max(lay.alignBytes(), 8);
        state.local_aligns[loc_i] = eff_align;
        const alloca_line = try std.fmt.allocPrint(
            emitter.allocator,
            "  %_loc_{d} = alloca {s}, align {d}\n",
            .{ loc_i, mem_ty, eff_align },
        );
        defer emitter.allocator.free(alloca_line);
        try state.entry_allocas.appendSlice(emitter.allocator, alloca_line);
        state.local_ptrs[loc_i] = try std.fmt.allocPrint(emitter.allocator, "%_loc_{d}", .{loc_i});

        try emitMemsetZero(emitter, &entry_prologue, state.local_ptrs[loc_i], lay.size_bytes, eff_align);

        if (is_param and (loc_i - 1) < recipe.param_recipes.len) {
            const p_idx = loc_i - 1;
            const p_rec = recipe.param_recipes[p_idx];
            const arg_name = try std.fmt.allocPrint(emitter.allocator, "%_arg_p{d}", .{p_idx});
            defer emitter.allocator.free(arg_name);
            if (p_rec.pass_mode == .indirect_by_ref or p_rec.pass_mode == .indirect_byval) {
                try emitMemcpyBytes(
                    emitter,
                    &entry_prologue,
                    state.local_ptrs[loc_i],
                    eff_align,
                    arg_name,
                    p_rec.pointee_align_bytes,
                    lay.size_bytes,
                );
            } else if (p_rec.pass_mode != .ignore_zst) {
                const abi_ty = try formatAbiParamOrRetType(emitter, loc_decl.type_id, p_rec);
                defer emitter.allocator.free(abi_ty);
                const unpacked_v = try emitCoerceAbiToValue(
                    emitter,
                    &entry_prologue,
                    loc_decl.type_id,
                    abi_ty,
                    arg_name,
                );
                defer emitter.allocator.free(unpacked_v);
                try emitStoreValueToPtr(
                    emitter,
                    &entry_prologue,
                    loc_decl.type_id,
                    unpacked_v,
                    state.local_ptrs[loc_i],
                    eff_align,
                    0,
                    0,
                    0,
                );
            }
        }
    }

    // Merge any scratch allocas allocated while unpacking direct ABI aggregates in `entry_prologue`.
    if (entry_prologue.entry_allocas.items.len > 0) {
        try state.entry_allocas.appendSlice(emitter.allocator, entry_prologue.entry_allocas.items);
    }
    state.next_tmp_id = entry_prologue.next_tmp_id;

    // [3] Pass 1 – Emit each basic block's instructions + terminator into `per_block_ir[bb_i]`.
    var per_block_ir = try emitter.allocator.alloc([]u8, block_count);
    @memset(per_block_ir, &[_]u8{});
    defer {
        for (per_block_ir) |buf_s| {
            if (buf_s.len > 0) emitter.allocator.free(buf_s);
        }
        emitter.allocator.free(per_block_ir);
    }

    for (body.blocks.items, 0..) |bb, bb_i| {
        state.cur_buf.clearRetainingCapacity();
        state.setLabelOwned(try std.fmt.allocPrint(emitter.allocator, "_bb_{d}", .{bb_i}));
        state.active_dbg_loc_md = 0;

        // Bind `_bb_0` block_params if any exist on the entry block.
        if (bb_i == 0) {
            for (body.getBlockParams(MirBlockId.fromInt(0)), 0..) |bp_val, bp_idx| {
                const bp_ty = body.getInst(bp_val).type_id;
                if (try isZeroSizedType(emitter, bp_ty)) {
                    try state.print("  %_v_{d} = add i8 0, 0\n", .{bp_val.asInt()});
                } else if (1 + bp_idx < state.local_ptrs.len and state.local_ptrs[1 + bp_idx].len > 0) {
                    const loaded_p = try emitLoadValueFromPtr(
                        emitter,
                        &state,
                        bp_ty,
                        state.local_ptrs[1 + bp_idx],
                        state.local_aligns[1 + bp_idx],
                        lookupProvenRange(emitter, body_idx, bp_val.asInt()),
                        0,
                        0,
                        0,
                    );
                    defer emitter.allocator.free(loaded_p);
                    const val_ty = try formatLlvmValueType(emitter, bp_ty);
                    defer emitter.allocator.free(val_ty);
                    try state.print(
                        "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                        .{ bp_val.asInt(), val_ty, loaded_p, val_ty, loaded_p },
                    );
                }
            }
        }

        // Emit Pentagon `@llvm.assume` pointer facts on `block_param` pointers (entry `_bb_0` + `phi` headers).
        for (body.getBlockParams(MirBlockId.fromInt(@intCast(bb_i)))) |bp_val| {
            const bp_ty = try unwrapTransparentType(emitter, body.getInst(bp_val).type_id);
            if (!bp_ty.isPrimitiveOrSentinel()) {
                const bp_tag = emitter.input.pool.getNode(bp_ty).tag;
                if (bp_tag == .ref_ty or bp_tag == .mut_ref_ty or bp_tag == .raw_ptr_ty) {
                    if (lookupProvenRange(emitter, body_idx, bp_val.asInt())) |prov_r| {
                        const bp_ssa = try std.fmt.allocPrint(
                            emitter.allocator,
                            "%_v_{d}",
                            .{bp_val.asInt()},
                        );
                        defer emitter.allocator.free(bp_ssa);
                        try maybeEmitPointerAssume(emitter, &state, bp_ssa, prov_r);
                    }
                }
            }
        }

        for (body.getBlockInsts(MirBlockId.fromInt(@intCast(bb_i)))) |val_id| {
            const tok_idx = if (val_id.asInt() < body.origin_tokens.items.len)
                body.origin_tokens.items[val_id.asInt()]
            else
                TokenIndex.none;
            if (!tok_idx.isNone() and state.subprogram_md != 0) {
                state.active_dbg_loc_md = try resolveTokenDebugLocMd(
                    emitter,
                    state.subprogram_md,
                    body.file_id,
                    tok_idx,
                );
            }
            try emitMirInstLlvm(emitter, &state, body_idx, body, @intCast(bb_i), val_id);
        }

        try emitMirTerminatorLlvm(emitter, &state, body_idx, body, @intCast(bb_i), bb.terminator);
        per_block_ir[bb_i] = try emitter.allocator.dupe(u8, state.cur_buf.items);
    }

    // [4] Pass 2 – Stitch `_bb_0` (`entry_allocas` + `entry_prologue`), `_bb_1..N` (`phi` headers), and trampolines.
    for (0..block_count) |bb_i| {
        try emitter.print("_bb_{d}:\n", .{bb_i});
        if (bb_i == 0) {
            if (state.entry_allocas.items.len > 0) {
                try emitter.writeAll(state.entry_allocas.items);
            }
            if (entry_prologue.cur_buf.items.len > 0) {
                try emitter.writeAll(entry_prologue.cur_buf.items);
            }
        } else {
            const bb_id = MirBlockId.fromInt(@intCast(bb_i));
            const bb_params = body.getBlockParams(bb_id);
            if (bb_params.len > 0) {
                // Collect active syntactic predecessor edges targeting `bb_id`.
                var pred_edge_indices: std.ArrayListUnmanaged(usize) = .empty;
                defer pred_edge_indices.deinit(emitter.allocator);
                for (body.extra_edges.items, 0..) |edge, e_idx| {
                    if (edge.target_bb == bb_id and state.edge_pred_labels[e_idx].len > 0) {
                        try pred_edge_indices.append(emitter.allocator, e_idx);
                    }
                }

                for (bb_params, 0..) |bp_val, param_k| {
                    const bp_ty = body.getInst(bp_val).type_id;
                    if (try isZeroSizedType(emitter, bp_ty)) continue;
                    const val_ty = try formatLlvmValueType(emitter, bp_ty);
                    defer emitter.allocator.free(val_ty);

                    if (pred_edge_indices.items.len == 0) {
                        const zero_s = resolveZeroLiteralForLlvmType(val_ty);
                        try emitter.print(
                            "  %_v_{d} = select i1 true, {s} {s}, {s} {s}\n",
                            .{ bp_val.asInt(), val_ty, zero_s, val_ty, zero_s },
                        );
                        continue;
                    }

                    try emitter.print("  %_v_{d} = phi {s} ", .{ bp_val.asInt(), val_ty });
                    for (pred_edge_indices.items, 0..) |e_idx, p_ord| {
                        if (p_ord > 0) try emitter.writeAll(", ");
                        const edge = body.extra_edges.items[e_idx];
                        const pred_lbl = state.edge_pred_labels[e_idx];
                        if (param_k == 0 and state.edge_call_ret_vals[e_idx].len > 0) {
                            try emitter.print(
                                "[ {s}, %{s} ]",
                                .{ state.edge_call_ret_vals[e_idx], pred_lbl },
                            );
                        } else if (param_k < edge.args_len) {
                            const arg_v = body.extra_args.items[edge.args_start + param_k];
                            try emitter.print("[ %_v_{d}, %{s} ]", .{ arg_v, pred_lbl });
                        } else {
                            try emitter.print(
                                "[ {s}, %{s} ]",
                                .{ resolveZeroLiteralForLlvmType(val_ty), pred_lbl },
                            );
                        }
                    }
                    try emitter.writeAll("\n");
                }

                // Emit ZST placeholder definitions after all `phi` nodes in the block header.
                for (bb_params) |bp_val| {
                    if (try isZeroSizedType(emitter, body.getInst(bp_val).type_id)) {
                        try emitter.print("  %_v_{d} = add i8 0, 0\n", .{bp_val.asInt()});
                    }
                }
            }
        }
        try emitter.writeAll(per_block_ir[bb_i]);
    }

    // Emit synthetic `_bb_edge_<tramp_idx>` trampolines for duplicate multi-way branches (`[CRITICAL-05]`).
    for (state.trampolines.items) |tramp| {
        try emitter.print(
            "_bb_edge_{d}:\n  br label %_bb_{d}\n",
            .{ tramp.tramp_idx, tramp.target_bb.asInt() },
        );
    }

    try emitter.writeAll("}\n\n");
}

/// Emits the C-ABI `define i32 @main()` wrapper invoking CoreX `main` (`cx_native` or `cx_result_cc`).
fn emitMainEntrypointWrapperLlvm(emitter: *LlvmModuleEmitter) !void {
    const main_b = emitter.entry_main_body_idx orelse return;
    const main_body = &emitter.input.bodies[main_b];
    if (main_body.param_count != 0) return;

    const main_rec = &emitter.body_recipes.items[main_b];
    const ptr_int = ptrIntType(emitter);
    const fn_attrs = fnUnwindAttrs(emitter);

    try emitter.print("define i32 @main() {s} {{\nentry:\n", .{fn_attrs});

    var state = BodyEmitState{
        .allocator = emitter.allocator,
        .cur_label = try emitter.allocator.dupe(u8, "entry"),
        .local_ptrs = try emitter.allocator.alloc([]u8, 0),
        .local_aligns = try emitter.allocator.alloc(u32, 0),
        .edge_pred_labels = try emitter.allocator.alloc([]u8, 0),
        .edge_call_ret_vals = try emitter.allocator.alloc([]u8, 0),
        .edge_trampoline = try emitter.allocator.alloc(?u32, 0),
        .block_access_group = try emitter.allocator.alloc(u32, 0),
    };
    defer state.deinit();

    try state.writeAll("  call void @_cx_rt_init()\n");

    const callee_op: []u8 = if (emitter.input.is_dev_got_enabled) blk: {
        const got_t = state.nextTmp();
        try state.print(
            "  %_mgot_p_{d} = getelementptr inbounds [{d} x ptr], ptr @_cx_dev_got, {s} 0, {s} {d}\n" ++
                "  %_mgot_f_{d} = load ptr, ptr %_mgot_p_{d}, align {d}\n",
            .{
                got_t,
                @max(emitter.input.bodies.len, 1),
                ptr_int,
                ptr_int,
                main_b,
                got_t,
                got_t,
                emitter.cfg.target.ptrBytes(),
            },
        );
        break :blk try std.fmt.allocPrint(emitter.allocator, "%_mgot_f_{d}", .{got_t});
    } else try formatLlvmGlobalIdent(emitter.allocator, emitter.body_llvm_names.items[main_b]);
    defer emitter.allocator.free(callee_op);

    var args_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer args_buf.deinit(emitter.allocator);
    var arg_cnt: usize = 0;

    var sret_slot: ?[]u8 = null;
    defer if (sret_slot) |s_ptr| emitter.allocator.free(s_ptr);
    if (main_rec.has_sret) {
        const ret_lay = try emitter.resolver.resolveType(main_body.ret_ty);
        const slot = try state.allocEntryBytes(
            ret_lay.size_bytes,
            @max(ret_lay.alignBytes(), main_rec.sret_recipe.pointee_align_bytes),
        );
        try emitMemsetZero(
            emitter,
            &state,
            slot,
            ret_lay.size_bytes,
            @max(ret_lay.alignBytes(), main_rec.sret_recipe.pointee_align_bytes),
        );
        const sret_piece = try formatAbiParamDeclPiece(emitter, main_body.ret_ty, main_rec.sret_recipe, slot);
        defer emitter.allocator.free(sret_piece);
        try args_buf.appendSlice(emitter.allocator, sret_piece);
        arg_cnt += 1;
        sret_slot = slot;
    }
    if (main_rec.has_implicit_context) {
        const ctx_piece = try formatAbiParamDeclPiece(
            emitter,
            .usize_ty,
            main_rec.context_recipe,
            "@_cx_default_ctx",
        );
        defer emitter.allocator.free(ctx_piece);
        if (arg_cnt > 0) try args_buf.appendSlice(emitter.allocator, ", ");
        try args_buf.appendSlice(emitter.allocator, ctx_piece);
        arg_cnt += 1;
    }
    if (main_rec.swifterror_kind != .none) {
        try state.ensureSwifterrorCallSlot();
        if (arg_cnt > 0) try args_buf.appendSlice(emitter.allocator, ", ");
        try args_buf.appendSlice(emitter.allocator, "ptr swifterror %_cx_call_err");
        try state.writeAll("  store ptr null, ptr %_cx_call_err, align 8\n");
    }

    const ret_decl = try formatAbiReturnDecl(emitter, main_body.ret_ty, main_rec);
    defer emitter.allocator.free(ret_decl.full_decl);
    defer emitter.allocator.free(ret_decl.bare_ty);
    const is_void_abi = std.mem.eql(u8, ret_decl.bare_ty, "void");

    if (is_void_abi) {
        try state.print(
            "  call {s}void {s}({s})\n",
            .{ resolveCallingConvPrefix(main_rec), callee_op, args_buf.items },
        );
    } else {
        try state.print(
            "  %_m_rv = call {s}{s} {s}({s})\n",
            .{ resolveCallingConvPrefix(main_rec), ret_decl.full_decl, callee_op, args_buf.items },
        );
    }

    if (main_rec.swifterror_kind != .none) {
        try state.print(
            "  %_m_err = load ptr, ptr %_cx_call_err, align 8\n" ++
                "  %_m_he = icmp ne ptr %_m_err, null\n" ++
                "  br i1 %_m_he, label %m_ret_err, label %m_ret_ok\n" ++
                "m_ret_err:\n" ++
                "  call void @_cx_rt_trace_append(ptr @.cx_msg_err1, {s} 6)\n" ++
                "  ret i32 1\n" ++
                "m_ret_ok:\n" ++
                "  call void @_cx_rt_trace_append(ptr @.cx_msg_ret0, {s} 6)\n" ++
                "  ret i32 0\n",
            .{ ptr_int, ptr_int },
        );
    } else {
        const ret_ty = emitter.input.pool.unwrapUnderlyingType(main_body.ret_ty);
        if (try isZeroSizedType(emitter, ret_ty)) {
            try state.print(
                "  call void @_cx_rt_trace_append(ptr @.cx_msg_ret0, {s} 6)\n" ++
                    "  ret i32 0\n",
                .{ptr_int},
            );
        } else if (resolveIntegerInfo(emitter, ret_ty)) |int_info| {
            if (int_info.bits <= 64) {
                const unpacked_s = try emitCoerceAbiToValue(
                    emitter,
                    &state,
                    ret_ty,
                    ret_decl.bare_ty,
                    "%_m_rv",
                );
                defer emitter.allocator.free(unpacked_s);
                const rbuf = try state.allocEntryBytes(64, 8);
                defer emitter.allocator.free(rbuf);
                if (int_info.bits == 64) {
                    try state.print("  %_mr64 = add i64 {s}, 0\n", .{unpacked_s});
                } else {
                    const ext_s = if (int_info.is_signed) "sext" else "zext";
                    try state.print("  %_mr64 = {s} i{d} {s} to i64\n", .{ ext_s, int_info.bits, unpacked_s });
                }
                const fmt_sym = if (int_info.is_signed) "@.cx_fmt_ret_s" else "@.cx_fmt_ret_u";
                try state.print(
                    "  %_mn32 = call i32 (ptr, {s}, ptr, ...) @snprintf(ptr {s}, {s} 64, ptr {s}, i64 %_mr64)\n" ++
                        "  %_mok = icmp sgt i32 %_mn32, 0\n" ++
                        "  %_mcl = select i1 %_mok, i32 %_mn32, i32 0\n",
                    .{ ptr_int, rbuf, ptr_int, fmt_sym },
                );
                if (emitter.cfg.target.isWasm()) {
                    try state.print("  call void @_cx_rt_trace_append(ptr {s}, i32 %_mcl)\n", .{rbuf});
                } else {
                    try state.print(
                        "  %_mln = zext i32 %_mcl to i64\n" ++
                            "  call void @_cx_rt_trace_append(ptr {s}, i64 %_mln)\n",
                        .{rbuf},
                    );
                }
                if (int_info.bits == 32) {
                    try state.print("  ret i32 {s}\n", .{unpacked_s});
                } else if (int_info.bits < 32) {
                    const ext32 = if (int_info.is_signed) "sext" else "zext";
                    try state.print(
                        "  %_mr32 = {s} i{d} {s} to i32\n  ret i32 %_mr32\n",
                        .{ ext32, int_info.bits, unpacked_s },
                    );
                } else {
                    try state.writeAll("  %_mr32 = trunc i64 %_mr64 to i32\n  ret i32 %_mr32\n");
                }
            } else {
                try state.print(
                    "  call void @_cx_rt_trace_append(ptr @.cx_msg_ret0, {s} 6)\n  ret i32 0\n",
                    .{ptr_int},
                );
            }
        } else if (!ret_ty.isPrimitiveOrSentinel() and
            emitter.input.pool.getNode(ret_ty).tag == .result_ty)
        {
            const ret_lay = try emitter.resolver.resolveType(ret_ty);
            const mem_ptr = if (main_rec.has_sret)
                try emitter.allocator.dupe(u8, sret_slot.?)
            else blk: {
                const slot = try state.allocEntryBytes(ret_lay.size_bytes, ret_lay.alignBytes());
                try emitMemsetZero(emitter, &state, slot, ret_lay.size_bytes, ret_lay.alignBytes());
                const unpacked = try emitCoerceAbiToValue(
                    emitter,
                    &state,
                    ret_ty,
                    ret_decl.bare_ty,
                    "%_m_rv",
                );
                defer emitter.allocator.free(unpacked);
                try emitStoreValueToPtr(emitter, &state, ret_ty, unpacked, slot, ret_lay.alignBytes(), 0, 0, 0);
                break :blk slot;
            };
            defer emitter.allocator.free(mem_ptr);
            const discr_s = try emitReadSumDiscriminantFromPtr(
                emitter,
                &state,
                ret_ty,
                mem_ptr,
                ret_lay.alignBytes(),
            );
            defer emitter.allocator.free(discr_s);
            try state.print(
                "  %_m_ise = icmp eq i32 {s}, 1\n" ++
                    "  br i1 %_m_ise, label %m_res_err, label %m_res_ok\n" ++
                    "m_res_err:\n" ++
                    "  call void @_cx_rt_trace_append(ptr @.cx_msg_err1, {s} 6)\n" ++
                    "  ret i32 1\n" ++
                    "m_res_ok:\n" ++
                    "  call void @_cx_rt_trace_append(ptr @.cx_msg_ret0, {s} 6)\n" ++
                    "  ret i32 0\n",
                .{ discr_s, ptr_int, ptr_int },
            );
        } else {
            try state.print(
                "  call void @_cx_rt_trace_append(ptr @.cx_msg_ret0, {s} 6)\n  ret i32 0\n",
                .{ptr_int},
            );
        }
    }

    if (state.entry_allocas.items.len > 0) {
        try emitter.writeAll(state.entry_allocas.items);
    }
    try emitter.writeAll(state.cur_buf.items);
    try emitter.writeAll("}\n\n");
}

// ------------ LLVM Bridge & `zig cc` Driver Layer -------------

/// Returns the `clang` / `zig cc` optimization flag corresponding to `opt_level`.
fn resolveOptLevelDriverFlag(opt_level: codegen_abi.OptLevel) []const u8 {
    return switch (opt_level) {
        .debug_o0 => "-O0",
        .release_fast_o2 => "-O2",
        .release_aggressive_o3 => "-O3",
        .release_small_oz => "-Oz",
    };
}

/// Returns target-specific SIMD CPU feature flags for `corex_llvm` or `zig cc`.
fn resolveTargetFeatureFlag(spec: TargetSpec) []const u8 {
    if (spec.arch == .x86_64) {
        return switch (spec.simd_level) {
            .avx2 => "+avx2,+fma",
            .avx512 => "+avx512f,+avx512bw,+avx512dq,+avx512vl",
            else => "",
        };
    }
    if (spec.arch == .wasm32 and spec.simd_level != .none) {
        return "+simd128";
    }
    return "";
}

/// Compiles `ir_source` to `.object_file` or `.executable` via `corex_llvm` bridge and/or `zig cc`.
fn compileLlvmIrWithDriver(
    allocator: std.mem.Allocator,
    cfg: LlvmBackendConfig,
    input: CodegenModuleInput,
    has_dwarf_tables: bool,
    ir_source: []const u8,
) LlvmCodegenError![]u8 {
    const out_path = input.output_path orelse return error.MissingOutputConfig;
    const io = input.io orelse return error.MissingOutputConfig;

    const seq_id = next_llvm_scratch_seq.fetchAdd(1, .monotonic);
    const scratch_dir = std.fmt.allocPrint(
        allocator,
        ".zig-cache/cx_llvm_drv_{d}",
        .{seq_id},
    ) catch return error.OutOfMemory;
    defer allocator.free(scratch_dir);
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};

    const mod_obj_path = std.fmt.allocPrint(
        allocator,
        "{s}/module{s}",
        .{ scratch_dir, cfg.target.objectExtension() },
    ) catch return error.OutOfMemory;
    defer allocator.free(mod_obj_path);

    var is_built_via_cpp_bridge = false;
    if (build_options.has_llvm_cpp_bridge and cfg.is_static_llvm_bridge_enabled) {
        std.Io.Dir.cwd().createDirPath(io, scratch_dir) catch return error.BackendFailure;
        const c_triple = allocator.dupeZ(u8, cfg.target.asLlvmTargetTriple()) catch return error.OutOfMemory;
        defer allocator.free(c_triple);
        const c_feats = allocator.dupeZ(u8, resolveTargetFeatureFlag(cfg.target)) catch
            return error.OutOfMemory;
        defer allocator.free(c_feats);
        const c_mod = allocator.dupeZ(u8, input.module_name) catch return error.OutOfMemory;
        defer allocator.free(c_mod);
        const c_obj = allocator.dupeZ(u8, mod_obj_path) catch return error.OutOfMemory;
        defer allocator.free(c_obj);

        var err_buf: [2048]u8 = @splat(0);
        const req = c_llvm_bridge.CxLlvmCompileRequest{
            .target_triple = c_triple.ptr,
            .target_cpu = "generic",
            .target_features = c_feats.ptr,
            .module_name = c_mod.ptr,
            .ir_text_ptr = ir_source.ptr,
            .ir_text_len = ir_source.len,
            .output_obj_path = c_obj.ptr,
            .opt_level = @backingInt(cfg.opt_level),
            .is_fuzz_sancov = if (cfg.is_fuzz_instrumented) 1 else 0,
            .is_pic = 1,
            ._pad = 0,
        };
        const status = c_llvm_bridge.cx_llvm_compile_ir_to_object(&req, &err_buf, err_buf.len);
        if (status != c_llvm_bridge.CX_LLVM_OK) {
            if (input.diagnostic_sink) |sink| {
                const msg_len = std.mem.indexOfScalar(u8, &err_buf, 0) orelse err_buf.len;
                codegen_abi.emitBackendFailureDiagnostic(
                    sink,
                    Span.ZERO,
                    "tier_b_llvm",
                    err_buf[0..msg_len],
                ) catch {};
            }
            return error.BackendFailure;
        }
        is_built_via_cpp_bridge = true;
    }

    if (is_built_via_cpp_bridge and input.artifact_kind == .object_file) {
        codegen_abi.publishStagedFileAtomic(io, allocator, mod_obj_path, out_path) catch
            return error.BackendFailure;
        return allocator.dupe(u8, out_path) catch return error.OutOfMemory;
    }

    const zig_exe = codegen_abi.resolveZigExecutable(io, allocator, input.environ_map) catch
        return error.OutOfMemory;
    defer allocator.free(zig_exe);

    const zig_triple = cfg.target.asZigTargetTriple();
    const opt_flag = resolveOptLevelDriverFlag(cfg.opt_level);
    const is_linux_elf = cfg.target.os == .linux;

    if (!is_built_via_cpp_bridge) {
        const ir_path = std.fmt.allocPrint(allocator, "{s}/module.ll", .{scratch_dir}) catch
            return error.OutOfMemory;
        defer allocator.free(ir_path);
        codegen_abi.atomicWriteOutputFile(io, allocator, ir_path, ir_source) catch
            return error.BackendFailure;

        var obj_argv: std.ArrayListUnmanaged([]const u8) = .empty;
        defer obj_argv.deinit(allocator);
        obj_argv.appendSlice(allocator, &.{
            zig_exe,
            "cc",
            "-c",
            "-target",
            zig_triple,
            "-Wno-override-module",
            opt_flag,
        }) catch return error.OutOfMemory;

        if (cfg.target.arch == .x86_64) {
            if (cfg.target.simd_level == .avx2) {
                obj_argv.appendSlice(allocator, &.{ "-mavx2", "-mfma" }) catch return error.OutOfMemory;
            } else if (cfg.target.simd_level == .avx512) {
                obj_argv.appendSlice(
                    allocator,
                    &.{ "-mavx512f", "-mavx512bw", "-mavx512dq", "-mavx512vl" },
                ) catch return error.OutOfMemory;
            }
        } else if (cfg.target.arch == .wasm32 and cfg.target.simd_level != .none) {
            obj_argv.append(allocator, "-msimd128") catch return error.OutOfMemory;
        }
        if (has_dwarf_tables and is_linux_elf) {
            obj_argv.append(allocator, "-gz=zstd") catch return error.OutOfMemory;
        }
        if (cfg.is_fuzz_instrumented) {
            obj_argv.append(
                allocator,
                "-fsanitize-coverage=inline-8bit-counters,pc-table,trace-cmp,trace-div",
            ) catch return error.OutOfMemory;
        }
        obj_argv.appendSlice(allocator, &.{ ir_path, "-o", mod_obj_path }) catch return error.OutOfMemory;

        codegen_c.runZigCcCommand(
            allocator,
            io,
            input.environ_map,
            input.diagnostic_sink,
            obj_argv.items,
        ) catch return error.CompilerDriverFailed;
    }

    if (input.artifact_kind == .object_file) {
        codegen_abi.publishStagedFileAtomic(io, allocator, mod_obj_path, out_path) catch
            return error.BackendFailure;
        return allocator.dupe(u8, out_path) catch return error.OutOfMemory;
    }

    const tmp_exe_path = std.fmt.allocPrint(
        allocator,
        "{s}/out{s}",
        .{ scratch_dir, cfg.target.executableExtension() },
    ) catch return error.OutOfMemory;
    defer allocator.free(tmp_exe_path);

    var link_argv: std.ArrayListUnmanaged([]const u8) = .empty;
    defer link_argv.deinit(allocator);
    link_argv.appendSlice(allocator, &.{ zig_exe, "cc", "-target", zig_triple }) catch
        return error.OutOfMemory;

    if (has_dwarf_tables and is_linux_elf) {
        link_argv.append(allocator, "-Wl,--compress-debug-sections=zstd") catch return error.OutOfMemory;
    }
    link_argv.append(allocator, mod_obj_path) catch return error.OutOfMemory;

    var shim_obj_owned: ?[]u8 = null;
    defer if (shim_obj_owned) |so_p| allocator.free(so_p);
    if (cfg.is_fuzz_instrumented) {
        const shim_c_path = std.fmt.allocPrint(allocator, "{s}/sancov_shim.c", .{scratch_dir}) catch
            return error.OutOfMemory;
        defer allocator.free(shim_c_path);
        const shim_obj_path = std.fmt.allocPrint(
            allocator,
            "{s}/sancov_shim{s}",
            .{ scratch_dir, cfg.target.objectExtension() },
        ) catch return error.OutOfMemory;
        shim_obj_owned = shim_obj_path;

        codegen_abi.atomicWriteOutputFile(io, allocator, shim_c_path, codegen_c.SANCOV_SHIM_C_SOURCE) catch
            return error.BackendFailure;
        codegen_c.runZigCcCommand(allocator, io, input.environ_map, input.diagnostic_sink, &.{
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
        }) catch return error.CompilerDriverFailed;
        link_argv.append(allocator, shim_obj_path) catch return error.OutOfMemory;
    }

    link_argv.appendSlice(allocator, &.{ "-o", tmp_exe_path }) catch return error.OutOfMemory;
    codegen_c.runZigCcCommand(
        allocator,
        io,
        input.environ_map,
        input.diagnostic_sink,
        link_argv.items,
    ) catch return error.CompilerDriverFailed;

    codegen_abi.publishStagedFileAtomic(io, allocator, tmp_exe_path, out_path) catch
        return error.BackendFailure;
    return allocator.dupe(u8, out_path) catch return error.OutOfMemory;
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Emits deterministic LLVM 20–23 opaque-pointer `.ll` IR and optionally compiles/links via driver.
pub fn emitModule(
    allocator: std.mem.Allocator,
    cfg: LlvmBackendConfig,
    input: CodegenModuleInput,
) LlvmCodegenError!CodegenArtifact {
    var emitter = LlvmModuleEmitter.init(allocator, cfg, input);
    defer emitter.deinit();

    var dev_seam_bytes: ?[]u8 = null;
    errdefer if (dev_seam_bytes) |buf| allocator.free(buf);

    // Reserve `!0 = !{}` up front so `0` is an unambiguous absent sentinel for all metadata IDs.
    _ = emitter.addMetadataNode("!{}") catch return error.OutOfMemory;
    emitter.di_empty_tuple_md = emitter.addMetadataNode("!{}") catch return error.OutOfMemory;

    const esc_mod_name = escapeMetadataStringAlloc(allocator, input.module_name) catch
        return error.OutOfMemory;
    defer allocator.free(esc_mod_name);

    emitter.print("; ModuleID = '{s}'\n", .{esc_mod_name}) catch return error.OutOfMemory;
    emitter.print("source_filename = \"{s}.cx\"\n", .{esc_mod_name}) catch return error.OutOfMemory;
    emitter.print("target datalayout = \"{s}\"\n", .{cfg.target.asLlvmDataLayout()}) catch
        return error.OutOfMemory;
    emitter.print("target triple = \"{s}\"\n\n", .{cfg.target.asLlvmTargetTriple()}) catch
        return error.OutOfMemory;

    indexModuleEntities(&emitter) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };
    emitCompositeTypeDeclarations(&emitter) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };
    emitRodataAndRuntimeHelpers(&emitter, &dev_seam_bytes) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };
    emitExternDeclarations(&emitter) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };
    emitDropHelpersAndClosureThunks(&emitter) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };

    for (input.bodies, 0..) |*body_ptr, b_idx| {
        emitMirBody(&emitter, @intCast(b_idx), body_ptr) catch |err| {
            return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
        };
    }

    emitMainEntrypointWrapperLlvm(&emitter) catch |err| {
        return if (@as(anyerror, err) == error.OutOfMemory) error.OutOfMemory else error.BackendFailure;
    };

    if (emitter.synth_globals.items.len > 0) {
        emitter.writeAll(emitter.synth_globals.items) catch return error.OutOfMemory;
        emitter.writeAll("\n") catch return error.OutOfMemory;
    }

    // Emit sorted `@llvm.*` intrinsic declarations collected across the module.
    if (emitter.owned_intrinsic_decls.items.len > 0) {
        std.mem.sort([]u8, emitter.owned_intrinsic_decls.items, {}, struct {
            /// Orders two LLVM `declare` lines lexicographically.
            fn lessThan(_: void, lhs_s: []u8, rhs_s: []u8) bool {
                return std.mem.order(u8, lhs_s, rhs_s) == .lt;
            }
        }.lessThan);
        for (emitter.owned_intrinsic_decls.items) |decl_s| {
            emitter.print("{s}\n", .{decl_s}) catch return error.OutOfMemory;
        }
        emitter.writeAll("\n") catch return error.OutOfMemory;
    }

    // Emit DWARF v5 `LineTablesOnly` module flags when debug info was generated.
    const has_dwarf = emitter.di_cu_md != 0;
    if (has_dwarf) {
        const dwarf_ver_md = emitter.addMetadataNode("!{i32 7, !\"Dwarf Version\", i32 5}") catch
            return error.OutOfMemory;
        const dbg_info_md = emitter.addMetadataNode("!{i32 2, !\"Debug Info Version\", i32 3}") catch
            return error.OutOfMemory;
        emitter.print(
            "!llvm.dbg.cu = !{{!{d}}}\n!llvm.module.flags = !{{!{d}, !{d}}}\n\n",
            .{ emitter.di_cu_md, dwarf_ver_md, dbg_info_md },
        ) catch return error.OutOfMemory;
    }

    if (emitter.meta_lines.items.len > 0) {
        emitter.writeAll(emitter.meta_lines.items) catch return error.OutOfMemory;
    }

    const emitted_ll = emitter.out.toOwnedSlice(allocator) catch return error.OutOfMemory;
    errdefer allocator.free(emitted_ll);

    var written_path: ?[]u8 = null;
    if (input.artifact_kind == .source_text) {
        if (input.output_path) |out_path| {
            const io = input.io orelse return error.MissingOutputConfig;
            codegen_abi.atomicWriteOutputFile(io, allocator, out_path, emitted_ll) catch
                return error.BackendFailure;
            written_path = allocator.dupe(u8, out_path) catch return error.OutOfMemory;
        }
    } else {
        written_path = try compileLlvmIrWithDriver(allocator, cfg, input, has_dwarf, emitted_ll);
    }

    return .{
        .emitted_text = emitted_ll,
        .dev_seam_bytes = dev_seam_bytes,
        .written_output_path = written_path,
    };
}

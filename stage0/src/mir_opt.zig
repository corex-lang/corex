//! Dual-Mode `MIR` Optimization Pipeline, Monomorphizer, `LayoutShapeKey` & `ICF`.
//!
//! Architectural Role:
//! - Implements the `DR-13` Deliverables 5–6 dual-mode optimization pipeline over canonical
//!   Block-Argument SSA `MirBody`s:
//!   - `--dev` 5-pass pipeline (`D1` `@inline(always)` splicing, `D2` reachable-only constant
//!     folding & `E0502`/`E0507` traps, `D3` Ghost instruction strip gate, `D4` constant branch
//!     folding & unreachable block pruning, `D5` FIFO monomorphization + Tarjan SCC `contextless`
//!     promotion + sound 16-byte `LayoutShapeKey` deduplication).
//!   - `--release` extending 6-pass pipeline (`R1` bounded cost-model inliner with `W0501`,
//!     `R2` `MirSsaBuilder.initFromExistingBody` SROA promotion, `R3` dominator-scoped VRP &
//!     redundant assertion folding, `R4` Wegman-Zadeck SCCP + `switch_int` fusion + commutative
//!     GVN, `R5` `MirProjection`-aware DCE + Call-Continuation-safe jump-threading/block-merging,
//!     and `R6` `Wyhash(0)` structural Identical Code Folding).
//! - Enforces `mir.verifyMirBody` (`V1`–`V6`) after **every single pass** (`D1`..`D5`, `R1`..`R6`).
//!
//! Key Design Choices:
//! - `D2` evaluates constant expressions strictly along constant-aware reachable CFG paths from
//!   `^bb0`, guaranteeing `if false { 1 / 0 }` never emits bogus compile-time traps.
//! - `D5` (`[CRITICAL-09]`) merges monomorphizations only when `(generic_def_id, LayoutShapeKey,
//!   OpSemanticsTag, field_offsets_digest, resolved_callees)` all match identically.
//! - `R5` preserves the Call Continuation Split-Edge Invariant (`[CRITICAL-05]`) and visits
//!   `MirProjection.index` operands (`[CRITICAL-06]`).

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const diagnostic = @import("diag/diagnostic.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const query_db = @import("query_db.zig");
const hir = @import("hir.zig");
const mir = @import("mir.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const MirBlockId = mem_foundation.MirBlockId;
const MirValueId = mem_foundation.MirValueId;
const TypeId = mem_foundation.TypeId;
const DefId = query_db.DefId;

const TokenBuffer = syntax_arenas.TokenBuffer;
const LosslessCstArena = syntax_arenas.LosslessCstArena;

const DiagnosticSink = diagnostic.DiagnosticSink;
const DiagCode = diagnostic.DiagnosticCode;
const LabeledSpan = diagnostic.LabeledSpan;

const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolTable = symbol_resolver.SymbolTable;

const InternPool = type_system.InternPool;
const ParamMode = type_system.ParamMode;
const TargetLayout = type_system.TargetLayout;
const TypeTag = type_system.TypeTag;

const LocalId = mir.LocalId;
const PlaceId = mir.PlaceId;
const EdgeId = mir.EdgeId;
const LocalDecl = mir.LocalDecl;
const LocalFlags = mir.LocalFlags;
const MirPlace = mir.MirPlace;
const MirProjection = mir.MirProjection;
const ProjKind = mir.ProjKind;
const MirOp = mir.MirOp;
const BinOpKind = mir.BinOpKind;
const UnaryOpKind = mir.UnaryOpKind;
const AggregateKind = mir.AggregateKind;
const MirIntrinsicKind = mir.MirIntrinsicKind;
const MirInst = mir.MirInst;
const InstFlags = mir.InstFlags;
const TerminatorKind = mir.TerminatorKind;
const MirTrapReason = mir.MirTrapReason;
const MirTerminator = mir.MirTerminator;
const MirBasicBlock = mir.MirBasicBlock;
const MirOutgoingEdge = mir.MirOutgoingEdge;
const MirCallSite = mir.MirCallSite;
const MirConst = mir.MirConst;
const MirBody = mir.MirBody;

// ---------------------------------------- TYPES ----------------------------------------

/// ABI register/stack passing classification in `LayoutShapeKey` (`DR-13` §5.3).
pub const AbiPassClass = enum(u8) {
    /// Zero-sized type (`()`, empty struct).
    zst = 0,
    /// Passed in a single general-purpose integer/pointer register (`<= ptr_byte_size`).
    integer_reg = 1,
    /// Passed in a single IEEE-754 floating-point register (`f32`, `f64`).
    float_reg = 2,
    /// Passed in a two-register pair (`<= 2 * ptr_byte_size`, e.g., `str`, `[T]`, `i128`).
    pair_regs = 3,
    /// Passed indirectly via hidden stack pointer / `sret` (`> 2 * ptr_byte_size`).
    indirect_sret = 4,
};

/// Niche bit-pattern representation tag in `LayoutShapeKey` (`DR-13` §5.3).
pub const NicheKind = enum(u8) {
    /// No spare invalid bit-patterns available.
    none = 0,
    /// Boolean `0..1` (`2..255` invalid).
    bool_01 = 1,
    /// Unicode scalar value (`0xD800..0xDFFF` and `> 0x10FFFF` invalid).
    char_unicode = 2,
    /// Non-null reference or function pointer (`0` invalid).
    non_null_ptr = 3,
    /// Enum discriminant ceiling (`>= variant_count` invalid).
    enum_tag_ceil = 4,
};

/// Exact 16-byte physical layout shape descriptor (`DR-13` §5.3, `[CRITICAL-09]`, `[MINOR-03]`).
pub const LayoutShapeKey = extern struct {
    /// Total padded byte size (`4B`).
    size_bytes: u32,
    /// Base-2 logarithm of required alignment (`1B`).
    align_log2: u8,
    /// Register/indirect ABI passing class (`1B`).
    abi_class: AbiPassClass,
    /// `1` if trivially bitwise `Copy`, `0` otherwise (`1B`).
    is_trivial_copy: u8,
    /// Available niche encoding tag (`1B`).
    niche_kind: NicheKind,
    /// Bitmask of pointer-sized words `[0..31]` carrying pointer provenance (`4B`).
    ptr_mask_64: u32,
    /// Explicit zero padding guaranteeing exact 16-byte `extern struct` width (`4B`).
    _pad: u32 = 0,

    /// Returns `true` if `self` and `other` have identical 16-byte layout shapes.
    pub inline fn isEqual(self: LayoutShapeKey, other: LayoutShapeKey) bool {
        return self.size_bytes == other.size_bytes and
            self.align_log2 == other.align_log2 and
            self.abi_class == other.abi_class and
            self.is_trivial_copy == other.is_trivial_copy and
            self.niche_kind == other.niche_kind and
            self.ptr_mask_64 == other.ptr_mask_64;
    }
};

/// Arithmetic/comparison operational semantics tag guarding `LayoutShapeKey` deduplication (`[CRITICAL-09]`).
pub const OpSemanticsTag = enum(u8) {
    /// Unit / zero-sized value.
    unit_sem = 0,
    /// Boolean (`bool`).
    bool_sem = 1,
    /// Two's-complement signed integer (`i8..i128`, `isize`).
    signed_int = 2,
    /// Unsigned modular/checked integer (`u8..u128`, `usize`, `char`, `bit_field`).
    unsigned_int = 3,
    /// IEEE-754 binary32 float (`f32`).
    ieee_f32 = 4,
    /// IEEE-754 binary64 float (`f64`).
    ieee_f64 = 5,
    /// Reference, raw pointer, or function pointer (`&T`, `&mut T`, `*T`, `fn`).
    pointer_or_ref = 6,
    /// Composite struct, tuple, array, slice, string, or tagged union.
    aggregate_bytes = 7,
};

/// Function inline directive parsed from `@inline`, `@inline(always)`, `@inline(never)`, or `@cold`.
pub const InlineDirective = enum(u8) {
    /// Unannotated function (eligible for small auto-inlining in `R1`).
    default_mode = 0,
    /// Annotated `@inline` (higher budget in `R1`; emits `W0501` if budget exceeded or recursive).
    inline_hint = 1,
    /// Annotated `@inline(always)` (spliced in `D1`; emits `W0501` if recursive).
    inline_always = 2,
    /// Annotated `@inline(never)` or `@cold` (never inlined in `D1` or `R1`).
    inline_never = 3,
};

/// Optional per-file CST context allowing `mir_opt` to extract `@inline(...)` / `@cold` directives.
pub const FileSyntaxView = struct {
    /// Raw UTF-8 source buffer of the file.
    source: []const u8,
    /// Lexed token buffer of the file.
    tokens: *const TokenBuffer,
    /// Lossless CST arena of the file.
    cst_arena: *const LosslessCstArena,
};

/// Configuration flags governing `optimizeMirModule`.
pub const MirOptConfig = struct {
    /// `false` runs `--dev` (`D1`–`D5`); `true` runs `--dev` (`D1`–`D5`) followed by `--release` (`R1`–`R6`).
    is_release_mode: bool = false,
    /// When `true`, clones pre-strip `MirBody`s right before `D3` into `MirOptModuleResult.pre_strip_bodies`
    /// so Phase 6 SAST ownership/exclusivity verification can inspect Ghost instructions.
    is_preserving_pre_strip_mir: bool = false,
    /// Target pointer/usize layout (`NATIVE_64` vs `WASM32`).
    target_layout: TargetLayout = TargetLayout.NATIVE_64,
    /// Optional syntax view of the primary file for `@inline` / `@inline(always)` / `@inline(never)` lookup.
    syntax_view: ?FileSyntaxView = null,
    /// Optional explicit inline directive overrides keyed by `DefId.asInt()` (for cross-file / synthetic tests).
    inline_overrides: ?*const std.AutoHashMapUnmanaged(u32, InlineDirective) = null,
    /// Optional set of `comptime fn` `DefId.asInt()`s skipped by runtime monomorphization (`D5`).
    comptime_fn_defs: ?*const std.AutoHashMapUnmanaged(u32, void) = null,
};

/// Output artifact produced by `optimizeMirModule` (`CompilerDb` stage `optimize_mir_module`).
pub const MirOptModuleResult = struct {
    /// Backing allocator owning all optimized and pre-strip `MirBody`s.
    allocator: std.mem.Allocator,
    /// Post-optimization, `V1`–`V6`-verified `MirBody`s ready for `MirVm` or Phase 7 codegen.
    bodies: std.ArrayListUnmanaged(MirBody) = .empty,
    /// Optional pre-`D3` Ghost-bearing `MirBody` clones preserved for Phase 6 SAST when requested.
    pre_strip_bodies: std.ArrayListUnmanaged(MirBody) = .empty,
    /// Count of generic monomorphizations merged by sound `LayoutShapeKey` deduplication (`D5`).
    dedup_merged_count: u32 = 0,
    /// Count of identical bodies folded by `Wyhash(0)` structural `ICF` (`R6`).
    icf_folded_count: u32 = 0,
    /// Deterministic 64-bit `Wyhash(0)` structural fingerprint of `bodies` for `CompilerDb` Early Cutoff.
    fingerprint: u64 = 0,

    /// Releases all `MirBody`s owned by `self`.
    pub fn deinit(self: *MirOptModuleResult) void {
        for (self.bodies.items) |*body_item| {
            body_item.deinit();
        }
        self.bodies.deinit(self.allocator);
        for (self.pre_strip_bodies.items) |*pre_item| {
            pre_item.deinit();
        }
        self.pre_strip_bodies.deinit(self.allocator);
        self.* = undefined;
    }

    /// Finds an optimized `MirBody` by UTF-8 function name (`null` if absent).
    pub fn findBodyByName(
        self: *const MirOptModuleResult,
        interner: *const StringInterner,
        target_name: []const u8,
    ) ?*const MirBody {
        for (self.bodies.items) |*body_item| {
            if (body_item.name != .empty and
                std.mem.eql(u8, interner.get(body_item.name), target_name))
            {
                return body_item;
            }
        }
        return null;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Hard cap on generic specialization nesting depth (`DR-13` §5.1, `E0508`).
pub const MAX_MONOMORPH_DEPTH: u32 = 64;
/// Hard cap on total monomorphized instances per module (`DR-13` §5.1, `E0508`).
pub const MAX_MONOMORPH_INSTANCES: u32 = 65_536;
/// Instruction cost budget for explicit `@inline` functions in `R1` (`W0501` when exceeded).
pub const INLINE_HINT_BUDGET: u32 = 64;
/// Instruction cost budget for unannotated small helper auto-inlining in `R1`.
pub const AUTO_INLINE_BUDGET: u32 = 24;
/// Caller instruction growth ceiling preventing quadratic code blowup during inlining.
pub const MAX_CALLER_INLINE_INSTS: u32 = 2_048;
/// Maximum scalar field count for composite local decomposition in `R2` SROA.
pub const MAX_SROA_COMPOSITE_FIELDS: u32 = 8;

/// Canonical quiet `f64` `NaN` payload matching `mir_vm.CANONICAL_F64_QNAN_BITS`.
const CANONICAL_F64_QNAN_BITS: u64 = 0x7FF8_0000_0000_0000;
/// Canonical quiet `f32` `NaN` payload matching `mir_vm.CANONICAL_F32_QNAN_BITS`.
const CANONICAL_F32_QNAN_BITS: u32 = 0x7FC0_0000;

comptime {
    // Enforce exact Phase 5 `LayoutShapeKey` cache-density byte-size invariants (`[CRITICAL-09]`):
    std.debug.assert(@sizeOf(AbiPassClass) == 1);
    std.debug.assert(@sizeOf(NicheKind) == 1);
    std.debug.assert(@sizeOf(LayoutShapeKey) == 16);
}

// -------------------------------------- INTERNALS --------------------------------------

// -------- Layout Shape, Semantics & Attribute Helpers ---------

/// Resolves signedness and bit-width of an integer/bool/char/bitfield `TypeId`.
const OptIntInfo = struct {
    /// Width in bits (`1..128`).
    bits: u16,
    /// `true` if two's-complement signed.
    is_signed: bool,
};

/// Returns `OptIntInfo` when `raw_ty` is an integer, `bool`, `char`, or `bit_field`.
fn resolveOptIntInfo(
    pool: *const InternPool,
    raw_ty: TypeId,
    target_layout: TargetLayout,
) ?OptIntInfo {
    const ty = pool.unwrapUnderlyingType(raw_ty);
    return switch (ty) {
        .bool_ty => .{ .bits = 1, .is_signed = false },
        .i8_ty => .{ .bits = 8, .is_signed = true },
        .i16_ty => .{ .bits = 16, .is_signed = true },
        .i32_ty => .{ .bits = 32, .is_signed = true },
        .i64_ty, .untyped_int_ty => .{ .bits = 64, .is_signed = true },
        .i128_ty => .{ .bits = 128, .is_signed = true },
        .isize_ty => .{ .bits = @as(u16, target_layout.ptr_byte_size) * 8, .is_signed = true },
        .u8_ty => .{ .bits = 8, .is_signed = false },
        .u16_ty => .{ .bits = 16, .is_signed = false },
        .u32_ty, .char_ty => .{ .bits = 32, .is_signed = false },
        .u64_ty => .{ .bits = 64, .is_signed = false },
        .u128_ty => .{ .bits = 128, .is_signed = false },
        .usize_ty => .{ .bits = @as(u16, target_layout.ptr_byte_size) * 8, .is_signed = false },
        else => blk: {
            const node = pool.getNode(ty);
            if (node.tag == .bit_field_ty) {
                break :blk resolveOptIntInfo(pool, TypeId.fromInt(node.lhs), target_layout);
            }
            break :blk null;
        },
    };
}

/// Classifies `raw_ty` into an `OpSemanticsTag` so `LayoutShapeKey` deduplication never conflates
/// signed, unsigned, and IEEE-754 operations (`[CRITICAL-09]`).
fn classifyOpSemantics(
    pool: *const InternPool,
    raw_ty: TypeId,
    target_layout: TargetLayout,
) OpSemanticsTag {
    const ty = pool.unwrapUnderlyingType(raw_ty);
    if (ty == .unit_ty or ty == .never_ty) return .unit_sem;
    if (ty == .bool_ty) return .bool_sem;
    if (ty == .f32_ty) return .ieee_f32;
    if (ty == .f64_ty or ty == .untyped_float_ty) return .ieee_f64;
    if (resolveOptIntInfo(pool, ty, target_layout)) |info| {
        return if (info.is_signed) .signed_int else .unsigned_int;
    }
    const node = pool.getNode(ty);
    return switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .fn_ty => .pointer_or_ref,
        else => .aggregate_bytes,
    };
}

/// Populates pointer-word bits inside `mask` for words `[0..31]` carrying pointer provenance.
fn populatePtrWordMask(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_ty: TypeId,
    byte_base: u64,
    target_layout: TargetLayout,
    depth: u32,
    mask: *u32,
) void {
    if (depth > 16 or raw_ty.isError()) return;
    const ptr_size: u64 = target_layout.ptr_byte_size;
    const ty = pool.unwrapUnderlyingType(raw_ty);
    if (ty == .str_ty) {
        if (byte_base % ptr_size == 0 and (byte_base / ptr_size) < 32) {
            mask.* |= (@as(u32, 1) << @intCast(byte_base / ptr_size));
        }
        return;
    }
    const node = pool.getNode(ty);
    switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .fn_ty, .slice_ty => {
            if (byte_base % ptr_size == 0 and (byte_base / ptr_size) < 32) {
                mask.* |= (@as(u32, 1) << @intCast(byte_base / ptr_size));
            }
        },
        .tuple_ty => {
            var running: u64 = 0;
            for (pool.getTupleElements(ty)) |elem_raw| {
                const elem_ty = TypeId.fromInt(elem_raw);
                const elem_lay = type_system.computeTypeLayoutWithPool(pool, sym_table, elem_ty, target_layout);
                running = std.mem.alignForward(u64, running, @max(@as(u64, elem_lay.align_bytes), 1));
                populatePtrWordMask(pool, sym_table, elem_ty, byte_base + running, target_layout, depth + 1, mask);
                running += elem_lay.byte_size;
            }
        },
        .struct_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return;
            const sym = sym_table.getSymbol(sym_idx).*;
            if (sym.target_scope.isNone()) return;
            var ord: u32 = 0;
            for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                const mem_sym = sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .field_sym) continue;
                if (type_system.computeStructFieldOffset(pool, sym_table, ty, ord, target_layout)) |off| {
                    populatePtrWordMask(
                        pool,
                        sym_table,
                        mem_sym.type_id,
                        byte_base + off,
                        target_layout,
                        depth + 1,
                        mask,
                    );
                }
                ord += 1;
            }
        },
        .array_ty => {
            const elem_ty = TypeId.fromInt(node.lhs);
            const elem_lay = type_system.computeTypeLayoutWithPool(pool, sym_table, elem_ty, target_layout);
            if (elem_lay.byte_size == 0) return;
            const arr_len: u64 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            const max_elems = @min(arr_len, 32);
            for (0..@intCast(max_elems)) |elem_i| {
                populatePtrWordMask(
                    pool,
                    sym_table,
                    elem_ty,
                    byte_base + @as(u64, elem_i) * elem_lay.byte_size,
                    target_layout,
                    depth + 1,
                    mask,
                );
            }
        },
        else => {},
    }
}

/// Extracts `@inline`, `@inline(always)`, `@inline(never)`, or `@cold` from CST or `inline_overrides`.
fn extractInlineDirective(
    def_id: DefId,
    sym_idx: SymbolIndex,
    sym_table: *const SymbolTable,
    config: MirOptConfig,
) InlineDirective {
    if (!def_id.isNone()) {
        if (config.inline_overrides) |overrides| {
            if (overrides.get(def_id.asInt())) |dir| return dir;
        }
    }
    const syntax = config.syntax_view orelse return .default_mode;
    var resolved_sym = sym_idx;
    if (resolved_sym.isNone() and !def_id.isNone()) {
        if (sym_table.def_to_symbol.get(def_id.asInt())) |mapped_sym| {
            resolved_sym = mapped_sym;
        }
    }
    if (resolved_sym.isNone() or resolved_sym.asInt() >= sym_table.symbols.items.len) return .default_mode;
    const fn_sym = sym_table.getSymbol(resolved_sym).*;
    if (fn_sym.cst_node.isNone() or fn_sym.cst_node.asInt() >= syntax.cst_arena.countNodes()) {
        return .default_mode;
    }

    const start_idx: usize = fn_sym.cst_node.asInt();
    const rec = syntax.cst_arena.getNode(fn_sym.cst_node);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, rec.subtree_size), 1),
        syntax.cst_arena.countNodes(),
    );
    var directive: InlineDirective = .default_mode;
    var cur = start_idx + 1;
    while (cur < end_idx) : (cur += 1) {
        const sub = syntax.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
        if (sub.kind == .fn_introducer or sub.kind == .block) break;
        if (sub.kind == .attribute) {
            const attr_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
            var has_inline_kw = false;
            var has_always_kw = false;
            var has_never_kw = false;
            var has_cold_kw = false;
            var leaf_cur = cur + 1;
            while (leaf_cur < attr_end) : (leaf_cur += 1) {
                const leaf = syntax.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(leaf_cur)));
                if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                    leaf.token.asInt() < syntax.tokens.countTokens())
                {
                    const lex = symbol_resolver.extractTokenSlice(syntax.source, syntax.tokens, leaf.token);
                    if (std.mem.eql(u8, lex, "inline")) has_inline_kw = true;
                    if (std.mem.eql(u8, lex, "always")) has_always_kw = true;
                    if (std.mem.eql(u8, lex, "never")) has_never_kw = true;
                    if (std.mem.eql(u8, lex, "cold")) has_cold_kw = true;
                }
            }
            if (has_cold_kw or (has_inline_kw and has_never_kw)) return .inline_never;
            if (has_inline_kw and has_always_kw) directive = .inline_always;
            if (has_inline_kw and !has_always_kw and directive == .default_mode) directive = .inline_hint;
        }
    }
    return directive;
}

/// Resolves the best source `Span` for a `TokenIndex` on `file_id`.
fn resolveOptDiagSpan(
    file_id: FileId,
    tok: TokenIndex,
    sym_idx: SymbolIndex,
    sym_table: *const SymbolTable,
    config: MirOptConfig,
) Span {
    if (!tok.isNone()) {
        if (config.syntax_view) |syntax| {
            if (tok.asInt() < syntax.tokens.countTokens()) {
                const tok_rec = syntax.tokens.getToken(tok);
                return Span.init(
                    file_id,
                    tok_rec.byte_offset,
                    tok_rec.byte_offset + tok_rec.byte_len,
                );
            }
        }
    }
    if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
        const sp = sym_table.getSymbol(sym_idx).decl_span;
        if (!sp.file_id.isNone()) return sp;
    }
    return Span.init(file_id, 0, 0);
}

/// Emits a structured diagnostic (`W0501`, `E0502`, `E0507`, `E0508`) into `sink` when present.
fn emitOptDiagnostic(
    sink: ?*DiagnosticSink,
    code: DiagCode,
    severity: diagnostic.Severity,
    span: Span,
    message: []const u8,
    label_text: []const u8,
) !void {
    const diag_sink = sink orelse return;
    const labels = [1]LabeledSpan{.{
        .span = span,
        .label = label_text,
        .style = .primary,
    }};
    try diag_sink.emit(.{
        .code = code,
        .severity = severity,
        .primary_span = span,
        .message = message,
        .labels = &labels,
    });
}

// ------------ CFG Edge, Pruning & Value Rewriters -------------

/// Rebuilds `body.pred_edges` and `bb.pred_start` / `bb.pred_len` strictly from reachable blocks,
/// clearing unreachable blocks (`inst_len = 0, param_len = 0, terminator = .unreachable_term`).
fn rebuildPredsAndSweepUnreachable(allocator: std.mem.Allocator, body: *MirBody) !void {
    const block_count = body.blocks.items.len;
    if (block_count == 0) return;

    const is_reachable = try allocator.alloc(bool, block_count);
    defer allocator.free(is_reachable);
    @memset(is_reachable, false);

    const bfs_queue = try allocator.alloc(u32, block_count);
    defer allocator.free(bfs_queue);
    var q_head: usize = 0;
    var q_tail: usize = 0;
    is_reachable[0] = true;
    bfs_queue[0] = 0;
    q_tail = 1;

    while (q_head < q_tail) : (q_head += 1) {
        const bb_idx = bfs_queue[q_head];
        const term = body.blocks.items[bb_idx].terminator;
        for (body.extra_edges.items[term.edge_start .. term.edge_start + term.edge_len]) |edge| {
            const dst = edge.target_bb.asInt();
            if (dst < block_count and !is_reachable[dst]) {
                is_reachable[dst] = true;
                bfs_queue[q_tail] = dst;
                q_tail += 1;
            }
        }
    }

    const pred_lists = try allocator.alloc(std.ArrayListUnmanaged(EdgeId), block_count);
    defer {
        for (pred_lists) |*pl| pl.deinit(allocator);
        allocator.free(pred_lists);
    }
    for (pred_lists) |*pl| pl.* = .empty;

    for (0..block_count) |bb_i| {
        if (!is_reachable[bb_i]) {
            body.blocks.items[bb_i].inst_len = 0;
            body.blocks.items[bb_i].setParamLen(0);
            body.blocks.items[bb_i].pred_start = 0;
            body.blocks.items[bb_i].pred_len = 0;
            body.blocks.items[bb_i].terminator = .{ .kind = .unreachable_term };
            continue;
        }
        const term = body.blocks.items[bb_i].terminator;
        for (0..term.edge_len) |off| {
            const eid = EdgeId.fromInt(term.edge_start + @as(u32, @intCast(off)));
            const dst = body.extra_edges.items[eid.asInt()].target_bb.asInt();
            if (dst < block_count and is_reachable[dst]) {
                try pred_lists[dst].append(allocator, eid);
            }
        }
    }

    body.pred_edges.clearRetainingCapacity();
    for (0..block_count) |bb_i| {
        if (!is_reachable[bb_i]) continue;
        const start: u32 = @intCast(body.pred_edges.items.len);
        try body.pred_edges.appendSlice(body.allocator, pred_lists[bb_i].items);
        body.blocks.items[bb_i].pred_start = start;
        body.blocks.items[bb_i].pred_len = @intCast(pred_lists[bb_i].items.len);
    }
}

///Applies a map `old_val_raw -> new_val_raw` transitively across every SSA value use in `body`
/// (including `MirProjection.index` via `forEachInstAndProjValueMut`, `[CRITICAL-06]`).
fn applyValueRewriteMap(
    body: *MirBody,
    replacements: *const std.AutoHashMapUnmanaged(u32, u32),
) void {
    if (replacements.count() == 0) return;
    const RewriteCtx = struct {
        map: *const std.AutoHashMapUnmanaged(u32, u32),

        fn rewrite(ctx: @This(), slot: *u32) void {
            var cur = slot.*;
            var guard: usize = 0;
            while (guard < 64) : (guard += 1) {
                if (ctx.map.get(cur)) |next_val| {
                    if (next_val == cur) break;
                    cur = next_val;
                } else {
                    break;
                }
            }
            slot.* = cur;
        }
    };
    body.forEachInstAndProjValueMut(RewriteCtx{ .map = replacements }, RewriteCtx.rewrite);
}

// ------- Pass `D1` & `R1` Shared Verified Call Splicer --------

/// Interns or appends a `MirPlace` `(base_local, projs)` inside `body`.
fn internBodyPlace(body: *MirBody, base_local: LocalId, projs: []const MirProjection) !PlaceId {
    if (base_local == .return_slot and projs.len == 0 and body.places.items.len > 0) {
        return .return_place;
    }
    for (body.places.items, 0..) |cand, idx| {
        if (cand.base == base_local.asInt() and cand.proj_len == projs.len) {
            const existing_projs = body.projections.items[cand.proj_start .. cand.proj_start + cand.proj_len];
            var is_all_equal = true;
            for (existing_projs, projs) |proj_a, proj_b| {
                if (proj_a.kind != proj_b.kind or proj_a.payload != proj_b.payload) {
                    is_all_equal = false;
                    break;
                }
            }
            if (is_all_equal) return PlaceId.fromInt(@intCast(idx));
        }
    }
    const proj_start: u24 = @intCast(body.projections.items.len);
    if (projs.len > 0) {
        try body.projections.appendSlice(body.allocator, projs);
    }
    const new_idx: u32 = @intCast(body.places.items.len);
    try body.places.append(body.allocator, .{
        .base = base_local.asInt(),
        .proj_start = proj_start,
        .proj_len = @intCast(projs.len),
    });
    return PlaceId.fromInt(new_idx);
}

/// Splices a single direct `.call` in `caller` (`call_bb_idx`) with a deep-remapped clone of `callee`,
/// preserving `V1`–`V6` both pre-strip (`D1`) and post-strip (`R1`).
fn spliceDirectCallSite(
    allocator: std.mem.Allocator,
    caller: *MirBody,
    call_bb_idx: u32,
    callee: *const MirBody,
) !void {
    const call_term = caller.blocks.items[call_bb_idx].terminator;
    if (call_term.kind != .call or call_term.edge_len < 1) return;
    const call_site = caller.calls.items[call_term.cond_or_val];
    const normal_edge = caller.extra_edges.items[call_term.edge_start];
    const normal_bb_id = normal_edge.target_bb;
    const normal_bb_idx = normal_bb_id.asInt();

    if (callee.blocks.items.len == 0 or call_site.args_len != callee.param_count) return;

    // Pre-validate `[CRITICAL-15]` combined `MirPlace` projection depth before mutating `caller`:
    for (callee.places.items) |cal_pl| {
        var base_proj_len: usize = 0;
        if (cal_pl.base >= 1 and cal_pl.base <= callee.param_count) {
            const arg_idx = cal_pl.base - 1;
            const arg_mode = caller.call_arg_modes.items[call_site.modes_start + arg_idx];
            if (arg_mode == .inout_mode or arg_mode == .set_mode) {
                const caller_pl = PlaceId.fromInt(caller.extra_args.items[call_site.args_start + arg_idx]);
                base_proj_len = caller.places.items[caller_pl.asInt()].proj_len;
            }
        }
        if (base_proj_len + @as(usize, cal_pl.proj_len) > mir.MAX_PLACE_PROJ_DEPTH) {
            return error.ProjectionDepthExceeded;
        }
    }

    const is_pre_strip = !caller.is_ghost_stripped and caller.has_ghost_instructions;
    const call_tok = call_site.origin_token;

    // [1] Map `callee` locals: `let`/`sink` & body locals get fresh slots in `caller`;
    //     `inout`/`set` parameters alias the caller's argument `PlaceId` directly:
    const callee_local_count = callee.locals.items.len;
    const local_remap = try allocator.alloc(LocalId, callee_local_count);
    defer allocator.free(local_remap);
    const param_alias_place = try allocator.alloc(PlaceId, callee_local_count);
    defer allocator.free(param_alias_place);
    @memset(param_alias_place, .none);

    for (callee.locals.items, 0..) |cal_loc, loc_i| {
        if (loc_i >= 1 and loc_i <= callee.param_count) {
            const arg_i = loc_i - 1;
            const mode = caller.call_arg_modes.items[call_site.modes_start + arg_i];
            if (mode == .inout_mode or mode == .set_mode) {
                const caller_pl = PlaceId.fromInt(caller.extra_args.items[call_site.args_start + arg_i]);
                param_alias_place[loc_i] = caller_pl;
                local_remap[loc_i] = LocalId.fromInt(caller.places.items[caller_pl.asInt()].base);
                continue;
            }
        }
        var cloned_flags = cal_loc.flags();
        cloned_flags.is_return_slot = false;
        cloned_flags.is_arg = false;
        cloned_flags.is_synthetic_temp = true;
        const new_lid = LocalId.fromInt(@intCast(caller.locals.items.len));
        try caller.locals.append(
            caller.allocator,
            LocalDecl.init(
                cal_loc.name,
                cal_loc.type_id,
                cal_loc.origin_token,
                cal_loc.region_raw,
                .let_mode,
                cloned_flags,
            ),
        );
        local_remap[loc_i] = new_lid;
    }

    // [2] Pre-allocate remapped `MirValueId`s (`inst_offset + old_val`) and `MirBlockId`s (`bb_offset + old_bb`):
    const inst_offset: u32 = @intCast(caller.insts.len);
    const callee_inst_len = callee.insts.len;
    try caller.insts.ensureTotalCapacity(caller.allocator, caller.insts.len + callee_inst_len);
    for (0..callee_inst_len) |i| {
        caller.insts.appendAssumeCapacity(callee.insts.get(i));
    }
    try caller.origin_tokens.appendSlice(caller.allocator, callee.origin_tokens.items);

    const const_offset: u32 = @intCast(caller.consts.items.len);
    try caller.consts.appendSlice(caller.allocator, callee.consts.items);

    // Map `callee` places into `caller` places (updating `.index` projection `MirValueId`s by `inst_offset`):
    const place_remap = try allocator.alloc(PlaceId, callee.places.items.len);
    defer allocator.free(place_remap);
    for (callee.places.items, 0..) |cal_pl, pl_i| {
        const cal_projs = callee.projections.items[cal_pl.proj_start .. cal_pl.proj_start + cal_pl.proj_len];
        var mapped_projs: [mir.MAX_PLACE_PROJ_DEPTH]MirProjection = undefined;
        var out_len: usize = 0;

        if (!param_alias_place[cal_pl.base].isNone()) {
            const base_caller_pl = param_alias_place[cal_pl.base];
            const base_projs = caller.getPlaceProjections(base_caller_pl);
            @memcpy(mapped_projs[0..base_projs.len], base_projs);
            out_len = base_projs.len;
            for (cal_projs) |pr| {
                var p_copy = pr;
                if (p_copy.kind == .index and p_copy.payload != mir.NONE_U32) {
                    p_copy.payload += inst_offset;
                }
                mapped_projs[out_len] = p_copy;
                out_len += 1;
            }
            const root_local = LocalId.fromInt(caller.places.items[base_caller_pl.asInt()].base);
            place_remap[pl_i] = try internBodyPlace(caller, root_local, mapped_projs[0..out_len]);
        } else {
            for (cal_projs) |pr| {
                var p_copy = pr;
                if (p_copy.kind == .index and p_copy.payload != mir.NONE_U32) {
                    p_copy.payload += inst_offset;
                }
                mapped_projs[out_len] = p_copy;
                out_len += 1;
            }
            place_remap[pl_i] = try internBodyPlace(caller, local_remap[cal_pl.base], mapped_projs[0..out_len]);
        }
    }

    const bb_offset: u32 = @intCast(caller.blocks.items.len);

    // [3] Patch operands of every cloned instruction at `inst_offset .. inst_offset + callee_inst_len`:
    for (0..callee_inst_len) |old_i| {
        const new_val = MirValueId.fromInt(inst_offset + @as(u32, @intCast(old_i)));
        var inst = caller.getInst(new_val);
        switch (inst.op) {
            .block_param => {
                inst.operands.lhs += bb_offset;
            },
            .const_scalar => {
                inst.operands.lhs += const_offset;
            },
            .fn_addr => {},
            .ghost_storage_init, .ghost_storage_deinit => {
                inst.operands.lhs = local_remap[inst.operands.lhs].asInt();
            },
            .ghost_access_let,
            .ghost_access_inout,
            .ghost_access_set,
            .ghost_storage_move,
            .place_load,
            .place_discriminant,
            .place_set_discrim,
            .place_addr,
            .soa_column_slice,
            => {
                inst.operands.lhs = place_remap[inst.operands.lhs].asInt();
            },
            .place_store => {
                inst.operands.lhs = place_remap[inst.operands.lhs].asInt();
                inst.operands.rhs += inst_offset;
            },
            .ghost_access_end,
            .copy_val,
            .unary_op,
            .aggregate_extract,
            .bitfield_extract,
            => {
                if (inst.operands.lhs != mir.NONE_U32) inst.operands.lhs += inst_offset;
            },
            .bin_op => {
                if (inst.operands.lhs != mir.NONE_U32) inst.operands.lhs += inst_offset;
                if (inst.operands.rhs != mir.NONE_U32) inst.operands.rhs += inst_offset;
            },
            .aggregate_insert => {
                if (inst.operands.lhs != mir.NONE_U32) inst.operands.lhs += inst_offset;
                const old_ex = inst.operands.rhs;
                const new_ex: u32 = @intCast(caller.extra_args.items.len);
                try caller.extra_args.appendSlice(caller.allocator, &.{
                    callee.extra_args.items[old_ex],
                    callee.extra_args.items[old_ex + 1] + inst_offset,
                });
                inst.operands.rhs = new_ex;
            },
            .bitfield_insert => {
                const old_ex = inst.operands.lhs;
                const new_ex: u32 = @intCast(caller.extra_args.items.len);
                try caller.extra_args.appendSlice(caller.allocator, &.{
                    callee.extra_args.items[old_ex] + inst_offset,
                    callee.extra_args.items[old_ex + 1] + inst_offset,
                });
                inst.operands.lhs = new_ex;
            },
            .aggregate_make => {
                const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                switch (agg_kind) {
                    .array_repeat => {
                        if (inst.operands.lhs != mir.NONE_U32) inst.operands.lhs += inst_offset;
                    },
                    .tagged_variant => {
                        const elem_len = inst.operands.rhs & 0xFFFF;
                        const new_ex: u32 = @intCast(caller.extra_args.items.len);
                        for (callee.extra_args.items[inst.operands.lhs .. inst.operands.lhs + elem_len]) |v_raw| {
                            try caller.extra_args.append(caller.allocator, v_raw + inst_offset);
                        }
                        inst.operands.lhs = new_ex;
                    },
                    .closure_make => {
                        const cap_len = callee.extra_args.items[inst.operands.rhs];
                        const cap_start = inst.operands.rhs + 1;
                        const new_ex: u32 = @intCast(caller.extra_args.items.len);
                        try caller.extra_args.append(caller.allocator, cap_len);
                        for (callee.extra_args.items[cap_start .. cap_start + cap_len]) |v_raw| {
                            try caller.extra_args.append(caller.allocator, v_raw + inst_offset);
                        }
                        inst.operands.rhs = new_ex;
                    },
                    .tuple_agg, .struct_agg, .array_elems, .str_concat => {
                        const new_ex: u32 = @intCast(caller.extra_args.items.len);
                        for (callee.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |v_raw| {
                            try caller.extra_args.append(caller.allocator, v_raw + inst_offset);
                        }
                        inst.operands.lhs = new_ex;
                    },
                }
            },
            .intrinsic_op => {
                if (inst.operands.rhs > 0) {
                    const new_ex: u32 = @intCast(caller.extra_args.items.len);
                    for (callee.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |v_raw| {
                        try caller.extra_args.append(caller.allocator, v_raw + inst_offset);
                    }
                    inst.operands.lhs = new_ex;
                }
            },
        }
        caller.insts.set(new_val.asInt(), inst);
    }

    // [4] Prepare `call_bb` prologue (`let`/`sink` stores) and close pre-strip `call_borrows` LIFO,
    //     stripping their matching `ghost_access_end`s from `normal_bb`:
    var call_bb_insts: std.ArrayListUnmanaged(MirValueId) = .empty;
    defer call_bb_insts.deinit(allocator);
    try call_bb_insts.appendSlice(allocator, caller.getBlockInsts(MirBlockId.fromInt(call_bb_idx)));

    for (0..call_site.args_len) |arg_i| {
        const mode = caller.call_arg_modes.items[call_site.modes_start + arg_i];
        if (mode == .let_mode or mode == .sink_mode) {
            const arg_val_raw = caller.extra_args.items[call_site.args_start + arg_i];
            const dst_lid = local_remap[1 + arg_i];
            const dst_pl = try internBodyPlace(caller, dst_lid, &.{});
            if (is_pre_strip) {
                const g_init = try caller.appendInst(.{
                    .op = .ghost_storage_init,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = dst_lid.asInt(), .rhs = 0 },
                }, call_tok);
                try call_bb_insts.append(allocator, g_init);
            }
            const st_inst = try caller.appendInst(.{
                .op = .place_store,
                .flags = .{ .has_side_effects = true, .is_synthetic = true },
                .type_id = .unit_ty,
                .operands = .{ .lhs = dst_pl.asInt(), .rhs = arg_val_raw },
            }, call_tok);
            try call_bb_insts.append(allocator, st_inst);
        }
    }

    if (is_pre_strip and call_site.call_borrows_len > 0) {
        const borrow_tokens = try allocator.dupe(
            u32,
            caller.extra_args.items[call_site.call_borrows_start .. call_site.call_borrows_start + call_site.call_borrows_len],
        );
        defer allocator.free(borrow_tokens);

        var bor_i = borrow_tokens.len;
        while (bor_i > 0) {
            bor_i -= 1;
            const g_end = try caller.appendInst(.{
                .op = .ghost_access_end,
                .flags = .{ .has_side_effects = true, .is_synthetic = true },
                .type_id = .unit_ty,
                .operands = .{ .lhs = borrow_tokens[bor_i], .rhs = 0 },
            }, call_tok);
            try call_bb_insts.append(allocator, g_end);
        }

        // Strip those exact `ghost_access_end` instructions from the top of `normal_bb`:
        var norm_filtered: std.ArrayListUnmanaged(MirValueId) = .empty;
        defer norm_filtered.deinit(allocator);
        for (caller.getBlockInsts(normal_bb_id)) |n_inst_id| {
            const n_inst = caller.getInst(n_inst_id);
            if (n_inst.op == .ghost_access_end) {
                var is_call_borrow = false;
                for (borrow_tokens) |btok| {
                    if (n_inst.operands.lhs == btok) {
                        is_call_borrow = true;
                        break;
                    }
                }
                if (is_call_borrow) continue;
            }
            try norm_filtered.append(allocator, n_inst_id);
        }
        const norm_start: u32 = @intCast(caller.block_insts.items.len);
        try caller.block_insts.appendSlice(caller.allocator, norm_filtered.items);
        caller.blocks.items[normal_bb_idx].inst_start = norm_start;
        caller.blocks.items[normal_bb_idx].inst_len = @intCast(norm_filtered.items.len);
    }

    const new_call_inst_start: u32 = @intCast(caller.block_insts.items.len);
    try caller.block_insts.appendSlice(caller.allocator, call_bb_insts.items);
    caller.blocks.items[call_bb_idx].inst_start = new_call_inst_start;
    caller.blocks.items[call_bb_idx].inst_len = @intCast(call_bb_insts.items.len);

    // [5] Append cloned `callee` blocks (`bb_offset .. bb_offset + callee.blocks.len - 1`):
    try caller.blocks.ensureTotalCapacity(caller.allocator, bb_offset + callee.blocks.items.len);
    for (callee.blocks.items, 0..) |cal_bb, cal_bb_i| {
        const new_bb_id = MirBlockId.fromInt(bb_offset + @as(u32, @intCast(cal_bb_i)));
        const p_start: u32 = @intCast(caller.block_params.items.len);
        for (callee.getBlockParams(MirBlockId.fromInt(@intCast(cal_bb_i)))) |old_p| {
            try caller.block_params.append(caller.allocator, MirValueId.fromInt(inst_offset + old_p.asInt()));
        }

        var mapped_insts: std.ArrayListUnmanaged(MirValueId) = .empty;
        defer mapped_insts.deinit(allocator);
        for (callee.getBlockInsts(MirBlockId.fromInt(@intCast(cal_bb_i)))) |old_inst_val| {
            const old_inst = callee.getInst(old_inst_val);
            // Skip synthetic `ghost_storage_init`/`deinit` on aliased `inout` parameters (`caller` already owns them):
            if (old_inst.op == .ghost_storage_init or old_inst.op == .ghost_storage_deinit) {
                const old_lid = old_inst.operands.lhs;
                if (old_lid >= 1 and old_lid <= callee.param_count and !param_alias_place[old_lid].isNone()) {
                    const alias_pl = caller.places.items[param_alias_place[old_lid].asInt()];
                    const param_mode = callee.locals.items[old_lid].mode();
                    if (old_inst.op == .ghost_storage_deinit or param_mode == .inout_mode or alias_pl.proj_len > 0) {
                        continue;
                    }
                }
            }
            if (!is_pre_strip and old_inst.op.isGhost()) continue;
            try mapped_insts.append(allocator, MirValueId.fromInt(inst_offset + old_inst_val.asInt()));
        }

        // Convert `callee`'s `.ret` into `.br -> normal_bb([ret_val])`:
        var new_term = cal_bb.terminator;
        switch (cal_bb.terminator.kind) {
            .ret => {
                var ret_ssa_raw: u32 = mir.NONE_U32;
                if (cal_bb.terminator.cond_or_val != mir.NONE_U32) {
                    ret_ssa_raw = inst_offset + cal_bb.terminator.cond_or_val;
                } else {
                    const ret_pl = try internBodyPlace(caller, local_remap[0], &.{});
                    const ld_val = try caller.appendInst(.{
                        .op = .place_load,
                        .type_id = callee.ret_ty,
                        .operands = .{ .lhs = ret_pl.asInt(), .rhs = 0 },
                    }, call_tok);
                    try mapped_insts.append(allocator, ld_val);
                    ret_ssa_raw = ld_val.asInt();
                }
                const arg_start: u32 = @intCast(caller.extra_args.items.len);
                try caller.extra_args.append(caller.allocator, ret_ssa_raw);
                const ret_edge_idx: u32 = @intCast(caller.extra_edges.items.len);
                try caller.extra_edges.append(caller.allocator, .{
                    .src_bb = new_bb_id,
                    .target_bb = normal_bb_id,
                    .args_start = arg_start,
                    .args_len = 1,
                });
                new_term = .{
                    .kind = .br,
                    .edge_len = 1,
                    .edge_start = ret_edge_idx,
                };
            },
            .br, .cond_br, .switch_int => {
                if (cal_bb.terminator.kind == .cond_br or cal_bb.terminator.kind == .switch_int) {
                    new_term.cond_or_val = inst_offset + cal_bb.terminator.cond_or_val;
                }
                const new_edge_start: u32 = @intCast(caller.extra_edges.items.len);
                for (callee.extra_edges.items[cal_bb.terminator.edge_start .. cal_bb.terminator.edge_start + cal_bb.terminator.edge_len]) |c_edge| {
                    const e_arg_start: u32 = @intCast(caller.extra_args.items.len);
                    for (callee.extra_args.items[c_edge.args_start .. c_edge.args_start + c_edge.args_len]) |ea| {
                        try caller.extra_args.append(caller.allocator, inst_offset + ea);
                    }
                    var case_idx = c_edge.case_tag_idx;
                    if (case_idx != std.math.maxInt(u16)) {
                        const new_sw_idx: u16 = @intCast(caller.switch_values.items.len);
                        try caller.switch_values.append(caller.allocator, callee.switch_values.items[case_idx]);
                        case_idx = new_sw_idx;
                    }
                    try caller.extra_edges.append(caller.allocator, .{
                        .src_bb = new_bb_id,
                        .target_bb = MirBlockId.fromInt(bb_offset + c_edge.target_bb.asInt()),
                        .args_start = e_arg_start,
                        .args_len = c_edge.args_len,
                        .case_tag_idx = case_idx,
                    });
                }
                new_term.edge_start = new_edge_start;
            },
            .call => {
                const old_cs = callee.calls.items[cal_bb.terminator.cond_or_val];
                const new_cs_args: u32 = @intCast(caller.extra_args.items.len);
                const new_cs_modes: u32 = @intCast(caller.call_arg_modes.items.len);
                for (0..old_cs.args_len) |ai| {
                    const amode = callee.call_arg_modes.items[old_cs.modes_start + ai];
                    try caller.call_arg_modes.append(caller.allocator, amode);
                    const aword = callee.extra_args.items[old_cs.args_start + ai];
                    if (amode == .let_mode or amode == .sink_mode) {
                        try caller.extra_args.append(caller.allocator, inst_offset + aword);
                    } else {
                        try caller.extra_args.append(caller.allocator, place_remap[aword].asInt());
                    }
                }
                const new_bor_start: u32 = @intCast(caller.extra_args.items.len);
                const new_bor_len: u16 = if (is_pre_strip) old_cs.call_borrows_len else 0;
                if (is_pre_strip) {
                    for (0..old_cs.call_borrows_len) |bi| {
                        try caller.extra_args.append(
                            caller.allocator,
                            inst_offset + callee.extra_args.items[old_cs.call_borrows_start + bi],
                        );
                    }
                }
                const new_cs_idx: u32 = @intCast(caller.calls.items.len);
                try caller.calls.append(caller.allocator, .{
                    .callee_val = MirValueId.fromInt(inst_offset + old_cs.callee_val.asInt()),
                    .direct_def_id = old_cs.direct_def_id,
                    .direct_symbol = old_cs.direct_symbol,
                    .args_start = new_cs_args,
                    .args_len = old_cs.args_len,
                    .modes_start = new_cs_modes,
                    .call_borrows_start = new_bor_start,
                    .call_borrows_len = new_bor_len,
                    .ret_ty = old_cs.ret_ty,
                    .is_callee_contextless = old_cs.is_callee_contextless,
                    .origin_token = old_cs.origin_token,
                });
                const old_ne = callee.extra_edges.items[cal_bb.terminator.edge_start];
                const new_ne_idx: u32 = @intCast(caller.extra_edges.items.len);
                try caller.extra_edges.append(caller.allocator, .{
                    .src_bb = new_bb_id,
                    .target_bb = MirBlockId.fromInt(bb_offset + old_ne.target_bb.asInt()),
                    .args_start = 0,
                    .args_len = 0,
                });
                new_term = .{
                    .kind = .call,
                    .edge_len = 1,
                    .cond_or_val = new_cs_idx,
                    .edge_start = new_ne_idx,
                };
            },
            .unreachable_term, .trap => {},
        }

        const i_start: u32 = @intCast(caller.block_insts.items.len);
        try caller.block_insts.appendSlice(caller.allocator, mapped_insts.items);

        var new_bb = MirBasicBlock{
            .param_start = p_start,
            .inst_start = i_start,
            .inst_len = @intCast(mapped_insts.items.len),
            .terminator = new_term,
        };
        new_bb.setParamLen(cal_bb.paramLen());
        new_bb.setSealed(true);
        new_bb.setCleanupPad(cal_bb.isCleanupPad());
        caller.blocks.appendAssumeCapacity(new_bb);
    }

    // [6] Redirect `call_bb` from `.call` to `.br -> cloned_callee_entry_bb` (`bb_offset`):
    const entry_edge_idx: u32 = @intCast(caller.extra_edges.items.len);
    try caller.extra_edges.append(caller.allocator, .{
        .src_bb = MirBlockId.fromInt(call_bb_idx),
        .target_bb = MirBlockId.fromInt(bb_offset),
        .args_start = 0,
        .args_len = 0,
    });
    caller.blocks.items[call_bb_idx].terminator = .{
        .kind = .br,
        .edge_len = 1,
        .edge_start = entry_edge_idx,
    };

    try rebuildPredsAndSweepUnreachable(allocator, caller);
}

// ----------- Pass `D1`: Mandatory `@inline(always)` -----------

/// $O(1)$ lookup table mapping `DefId` and `SymbolIndex` to their `MirBody` slice index (`[MAJOR-19]`).
const BodyDefMap = struct {
    /// Hash map from `DefId.asInt()` to first matching `bodies` index.
    def_to_body: std.AutoHashMapUnmanaged(u32, usize) = .empty,
    /// Hash map from `SymbolIndex.asInt()` to first matching `bodies` index (for `impl` / `@derive` methods).
    sym_to_body: std.AutoHashMapUnmanaged(u32, usize) = .empty,

    /// Builds `def_to_body` and `sym_to_body` in $O(B)$ over `bodies`.
    fn initFromBodies(allocator: std.mem.Allocator, bodies: []const MirBody) !BodyDefMap {
        var body_map = BodyDefMap{};
        errdefer body_map.deinit(allocator);
        try body_map.def_to_body.ensureTotalCapacity(allocator, @intCast(bodies.len));
        try body_map.sym_to_body.ensureTotalCapacity(allocator, @intCast(bodies.len));
        for (bodies, 0..) |cand, idx| {
            if (!cand.def_id.isNone() and !body_map.def_to_body.contains(cand.def_id.asInt())) {
                body_map.def_to_body.putAssumeCapacity(cand.def_id.asInt(), idx);
            }
            if (!cand.symbol_index.isNone() and !body_map.sym_to_body.contains(cand.symbol_index.asInt())) {
                body_map.sym_to_body.putAssumeCapacity(cand.symbol_index.asInt(), idx);
            }
        }
        return body_map;
    }

    /// Releases backing hash map storage.
    fn deinit(self: *BodyDefMap, allocator: std.mem.Allocator) void {
        self.def_to_body.deinit(allocator);
        self.sym_to_body.deinit(allocator);
    }

    /// Resolves `(def_id, sym_idx)` to a `bodies` index in $O(1)$.
    fn lookup(
        self: *const BodyDefMap,
        def_id: DefId,
        sym_idx: SymbolIndex,
        sym_table: *const SymbolTable,
    ) ?usize {
        if (!sym_idx.isNone()) {
            if (self.sym_to_body.get(sym_idx.asInt())) |idx| return idx;
        }
        if (!def_id.isNone()) {
            if (self.def_to_body.get(def_id.asInt())) |idx| return idx;
        }
        if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
            const sym_def = sym_table.getSymbol(sym_idx).def_id;
            if (!sym_def.isNone()) {
                return self.def_to_body.get(sym_def.asInt());
            }
        }
        return null;
    }
};

/// Checks if `start_idx` can reach `goal_idx` along direct calls (`true` = direct/mutual recursion).
fn hasCallGraphPath(
    allocator: std.mem.Allocator,
    bodies: []const MirBody,
    body_map: *const BodyDefMap,
    start_idx: usize,
    goal_idx: usize,
    sym_table: *const SymbolTable,
) !bool {
    const is_visited = try allocator.alloc(bool, bodies.len);
    defer allocator.free(is_visited);
    @memset(is_visited, false);

    var stack: std.ArrayListUnmanaged(usize) = .empty;
    defer stack.deinit(allocator);
    try stack.append(allocator, start_idx);
    is_visited[start_idx] = true;

    while (stack.items.len > 0) {
        const cur = stack.pop().?;
        for (bodies[cur].blocks.items) |bb| {
            if (bb.terminator.kind != .call) continue;
            const cs = bodies[cur].calls.items[bb.terminator.cond_or_val];
            const next_idx = body_map.lookup(cs.direct_def_id, cs.direct_symbol, sym_table) orelse
                continue;
            if (next_idx == goal_idx) return true;
            if (!is_visited[next_idx]) {
                is_visited[next_idx] = true;
                try stack.append(allocator, next_idx);
            }
        }
    }
    return false;
}

/// Pass `D1`: Splices mandatory `@inline(always)` calls, emitting `W0501` on recursive `@inline(always)`.
fn runPassD1InlineAlways(
    allocator: std.mem.Allocator,
    bodies: []MirBody,
    sym_table: *const SymbolTable,
    config: MirOptConfig,
    sink: ?*DiagnosticSink,
) !void {
    const directives = try allocator.alloc(InlineDirective, bodies.len);
    defer allocator.free(directives);
    var has_any_always = false;
    for (bodies, 0..) |cand, idx| {
        directives[idx] = extractInlineDirective(cand.def_id, cand.symbol_index, sym_table, config);
        if (directives[idx] == .inline_always) has_any_always = true;
    }
    if (!has_any_always) return;

    var body_map = try BodyDefMap.initFromBodies(allocator, bodies);
    defer body_map.deinit(allocator);

    var warned_recursive: std.AutoHashMapUnmanaged(u64, void) = .empty;
    defer warned_recursive.deinit(allocator);
    var warned_proj_depth: std.AutoHashMapUnmanaged(u64, void) = .empty;
    defer warned_proj_depth.deinit(allocator);

    for (0..bodies.len) |caller_idx| {
        var rounds: usize = 0;
        while (rounds < 16) : (rounds += 1) {
            var has_spliced_one = false;
            for (0..bodies[caller_idx].blocks.items.len) |bb_i| {
                const term = bodies[caller_idx].blocks.items[bb_i].terminator;
                if (term.kind != .call) continue;
                const cs = bodies[caller_idx].calls.items[term.cond_or_val];
                const callee_idx = body_map.lookup(cs.direct_def_id, cs.direct_symbol, sym_table) orelse
                    continue;
                if (directives[callee_idx] != .inline_always) continue;
                // Do not inline unspecialized generic templates prior to `D5`:
                if (isGenericTemplateBody(&bodies[callee_idx], null, sym_table)) continue;

                const is_recursive = (callee_idx == caller_idx) or
                    try hasCallGraphPath(allocator, bodies, &body_map, callee_idx, caller_idx, sym_table);
                if (is_recursive) {
                    const warn_key = (@as(u64, @intCast(caller_idx)) << 32) | @as(u64, @intCast(callee_idx));
                    if (!warned_recursive.contains(warn_key)) {
                        try warned_recursive.put(allocator, warn_key, {});
                        const span = resolveOptDiagSpan(
                            bodies[caller_idx].file_id,
                            cs.origin_token,
                            cs.direct_symbol,
                            sym_table,
                            config,
                        );
                        try emitOptDiagnostic(
                            sink,
                            .w0501_inlining_budget_exceeded,
                            .warning,
                            span,
                            "cannot inline recursive `@inline(always)` function; keeping direct call",
                            "recursive `@inline(always)` call site",
                        );
                    }
                    continue;
                }
                if (bodies[caller_idx].insts.len + bodies[callee_idx].insts.len > MAX_CALLER_INLINE_INSTS) {
                    continue;
                }

                var callee_snapshot = try bodies[callee_idx].clone(allocator);
                defer callee_snapshot.deinit();
                spliceDirectCallSite(allocator, &bodies[caller_idx], @intCast(bb_i), &callee_snapshot) catch |err| switch (err) {
                    error.ProjectionDepthExceeded => {
                        const site_key = (@as(u64, @intCast(caller_idx)) << 32) | @as(u64, term.cond_or_val);
                        if (!warned_proj_depth.contains(site_key)) {
                            try warned_proj_depth.put(allocator, site_key, {});
                            const span = resolveOptDiagSpan(
                                bodies[caller_idx].file_id,
                                cs.origin_token,
                                cs.direct_symbol,
                                sym_table,
                                config,
                            );
                            try emitOptDiagnostic(
                                sink,
                                .e0508_comptime_resource_limit_exceeded,
                                .err,
                                span,
                                std.fmt.comptimePrint(
                                    "`@inline(always)` call splicing exceeded `MAX_PLACE_PROJ_DEPTH` ({d})",
                                    .{mir.MAX_PLACE_PROJ_DEPTH},
                                ),
                                "projection depth limit exceeded during `@inline(always)` splicing",
                            );
                        }
                        continue;
                    },
                    else => return err,
                };
                has_spliced_one = true;
                break;
            }
            if (!has_spliced_one) break;
        }
    }
}

// --------- Pass `D2`: Reachable-Only Constant Folding ---------

/// Outcome of folding a constant binary or unary operation in `D2` / `R4`.
const ConstEvalResult = union(enum) {
    /// Successfully folded to a `MirConst`.
    folded: MirConst,
    /// Cannot fold statically (non-scalar or unsupported opcode).
    not_foldable,
    /// Traps with `E0502` (checked integer/shift overflow).
    trap_overflow: []const u8,
    /// Traps with `E0507` (division/remainder by zero or invalid float-to-int cast).
    trap_arithmetic: []const u8,
};

/// Sign-extends the low `bits` of `raw_u` (`i128` bit-cast to `u128`) into a signed `i128`.
fn sextConstInt(raw_val: i128, bits: u16) i128 {
    if (bits >= 128) return raw_val;
    const raw_u: u128 = @bitCast(raw_val);
    const shift: u7 = @intCast(128 - bits);
    const shifted: i128 = @bitCast(raw_u << shift);
    return shifted >> shift;
}

/// Zero-masks `raw_val` to the low `bits` as unsigned `u128`.
fn zextConstInt(raw_val: i128, bits: u16) u128 {
    const raw_u: u128 = @bitCast(raw_val);
    if (bits >= 128) return raw_u;
    const mask: u128 = (@as(u128, 1) << @intCast(bits)) - 1;
    return raw_u & mask;
}

/// Extracts an `i128` scalar from a `MirConst` (`bool`, `char`, `int`).
fn constToI128(mc: MirConst) ?i128 {
    return switch (mc) {
        .bool_val => |flag| @intFromBool(flag),
        .char_val => |cp| @as(i128, cp),
        .int_val => |iv| iv,
        else => null,
    };
}

/// Canonicalizes `f64` quiet `NaN` bit-patterns deterministically.
inline fn canonOptF64(val: f64) f64 {
    if (std.math.isNan(val)) return @bitCast(CANONICAL_F64_QNAN_BITS);
    return val;
}

/// Canonicalizes `f32` quiet `NaN` bit-patterns deterministically and widens to `f64`.
inline fn canonOptF32AsF64(val: f32) f64 {
    if (std.math.isNan(val)) {
        const qnan_f32: f32 = @bitCast(CANONICAL_F32_QNAN_BITS);
        return @floatCast(qnan_f32);
    }
    return @floatCast(val);
}

/// Wraps a folded integer bit-pattern into the appropriate `MirConst` for `dst_ty`.
fn makeTypedIntMirConst(pool: *const InternPool, dst_ty: TypeId, bits_u: u128, target_layout: TargetLayout) MirConst {
    const ty = pool.unwrapUnderlyingType(dst_ty);
    if (ty == .bool_ty) return .{ .bool_val = (bits_u & 1) != 0 };
    if (ty == .char_ty) return .{ .char_val = @truncate(bits_u) };
    if (resolveOptIntInfo(pool, ty, target_layout)) |info| {
        if (info.is_signed) {
            return .{ .int_val = sextConstInt(@bitCast(bits_u), info.bits) };
        }
        return .{ .int_val = @bitCast(zextConstInt(@bitCast(bits_u), info.bits)) };
    }
    return .{ .int_val = @bitCast(bits_u) };
}

/// Evaluates `BinOpKind` on two constant `MirConst` operands (`E0502` / `E0507` on checked traps).
fn foldConstBinOp(
    pool: *const InternPool,
    kind: BinOpKind,
    lhs_mc: MirConst,
    rhs_mc: MirConst,
    operand_ty: TypeId,
    rhs_ty: TypeId,
    res_ty: TypeId,
    target_layout: TargetLayout,
) ConstEvalResult {
    const op_ty = pool.unwrapUnderlyingType(operand_ty);
    switch (kind) {
        .fadd, .fsub, .fmul, .fdiv, .frem, .flt, .fle, .fgt, .fge => {
            const lf = switch (lhs_mc) {
                .float_val => |fv| fv,
                else => return .not_foldable,
            };
            const rf = switch (rhs_mc) {
                .float_val => |fv| fv,
                else => return .not_foldable,
            };
            if (op_ty == .f32_ty) {
                const l32: f32 = @floatCast(lf);
                const r32: f32 = @floatCast(rf);
                return switch (kind) {
                    .fadd => .{ .folded = .{ .float_val = canonOptF32AsF64(l32 + r32) } },
                    .fsub => .{ .folded = .{ .float_val = canonOptF32AsF64(l32 - r32) } },
                    .fmul => .{ .folded = .{ .float_val = canonOptF32AsF64(l32 * r32) } },
                    .fdiv => .{ .folded = .{ .float_val = canonOptF32AsF64(l32 / r32) } },
                    .frem => .{ .folded = .{ .float_val = canonOptF32AsF64(@rem(l32, r32)) } },
                    .flt => .{ .folded = .{ .bool_val = l32 < r32 } },
                    .fle => .{ .folded = .{ .bool_val = l32 <= r32 } },
                    .fgt => .{ .folded = .{ .bool_val = l32 > r32 } },
                    .fge => .{ .folded = .{ .bool_val = l32 >= r32 } },
                    else => .not_foldable,
                };
            }
            return switch (kind) {
                .fadd => .{ .folded = .{ .float_val = canonOptF64(lf + rf) } },
                .fsub => .{ .folded = .{ .float_val = canonOptF64(lf - rf) } },
                .fmul => .{ .folded = .{ .float_val = canonOptF64(lf * rf) } },
                .fdiv => .{ .folded = .{ .float_val = canonOptF64(lf / rf) } },
                .frem => .{ .folded = .{ .float_val = canonOptF64(@rem(lf, rf)) } },
                .flt => .{ .folded = .{ .bool_val = lf < rf } },
                .fle => .{ .folded = .{ .bool_val = lf <= rf } },
                .fgt => .{ .folded = .{ .bool_val = lf > rf } },
                .fge => .{ .folded = .{ .bool_val = lf >= rf } },
                else => .not_foldable,
            };
        },
        .eq, .ne => {
            if (op_ty == .f32_ty or op_ty == .f64_ty or op_ty == .untyped_float_ty) {
                const lf = switch (lhs_mc) {
                    .float_val => |fv| fv,
                    else => return .not_foldable,
                };
                const rf = switch (rhs_mc) {
                    .float_val => |fv| fv,
                    else => return .not_foldable,
                };
                return .{ .folded = .{ .bool_val = if (kind == .eq) (lf == rf) else (lf != rf) } };
            }
            if (op_ty == .str_ty) {
                if (lhs_mc == .str_val and rhs_mc == .str_val) {
                    const is_same_str = lhs_mc.str_val == rhs_mc.str_val;
                    return .{ .folded = .{ .bool_val = if (kind == .eq) is_same_str else !is_same_str } };
                }
                return .not_foldable;
            }
            const li = constToI128(lhs_mc) orelse return .not_foldable;
            const ri = constToI128(rhs_mc) orelse return .not_foldable;
            const info = resolveOptIntInfo(pool, op_ty, target_layout) orelse return .not_foldable;
            const lu = zextConstInt(li, info.bits);
            const ru = zextConstInt(ri, info.bits);
            return .{ .folded = .{ .bool_val = if (kind == .eq) (lu == ru) else (lu != ru) } };
        },
        else => {},
    }

    const info = resolveOptIntInfo(pool, op_ty, target_layout) orelse return .not_foldable;
    const raw_l = constToI128(lhs_mc) orelse return .not_foldable;
    const raw_r = constToI128(rhs_mc) orelse return .not_foldable;
    const lu = zextConstInt(raw_l, info.bits);
    const ru = zextConstInt(raw_r, info.bits);
    const ls = sextConstInt(raw_l, info.bits);
    const rs = sextConstInt(raw_r, info.bits);

    const min_s: i128 = if (info.bits >= 128)
        std.math.minInt(i128)
    else
        -(@as(i128, 1) << @intCast(info.bits - 1));
    const max_s: i128 = if (info.bits >= 128)
        std.math.maxInt(i128)
    else
        (@as(i128, 1) << @intCast(info.bits - 1)) - 1;
    const max_u: u128 = if (info.bits >= 128)
        std.math.maxInt(u128)
    else
        (@as(u128, 1) << @intCast(info.bits)) - 1;

    switch (kind) {
        .sadd_checked => {
            const ov = @addWithOverflow(ls, rs);
            if (ov[1] != 0 or ov[0] < min_s or ov[0] > max_s) {
                return .{ .trap_overflow = "signed integer addition overflowed at compile time" };
            }
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, @bitCast(ov[0]), target_layout) };
        },
        .uadd_checked => {
            const ov = @addWithOverflow(lu, ru);
            if (ov[1] != 0 or ov[0] > max_u) {
                return .{ .trap_overflow = "unsigned integer addition overflowed at compile time" };
            }
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, ov[0], target_layout) };
        },
        .ssub_checked => {
            const ov = @subWithOverflow(ls, rs);
            if (ov[1] != 0 or ov[0] < min_s or ov[0] > max_s) {
                return .{ .trap_overflow = "signed integer subtraction overflowed at compile time" };
            }
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, @bitCast(ov[0]), target_layout) };
        },
        .usub_checked => {
            if (lu < ru) {
                return .{ .trap_overflow = "unsigned integer subtraction underflowed at compile time" };
            }
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, lu - ru, target_layout) };
        },
        .smul_checked => {
            const ov = @mulWithOverflow(ls, rs);
            if (ov[1] != 0 or ov[0] < min_s or ov[0] > max_s) {
                return .{ .trap_overflow = "signed integer multiplication overflowed at compile time" };
            }
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, @bitCast(ov[0]), target_layout) };
        },
        .umul_checked => {
            const ov = @mulWithOverflow(lu, ru);
            if (ov[1] != 0 or ov[0] > max_u) {
                return .{ .trap_overflow = "unsigned integer multiplication overflowed at compile time" };
            }
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, ov[0], target_layout) };
        },
        .sdiv_checked => {
            if (rs == 0) return .{ .trap_arithmetic = "division by zero detected in reachable expression" };
            if (ls == min_s and rs == -1) {
                return .{ .trap_overflow = "signed `MIN / -1` division overflowed at compile time" };
            }
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, @bitCast(@divTrunc(ls, rs)), target_layout) };
        },
        .udiv_checked => {
            if (ru == 0) return .{ .trap_arithmetic = "division by zero detected in reachable expression" };
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, lu / ru, target_layout) };
        },
        .srem_checked => {
            if (rs == 0) return .{ .trap_arithmetic = "remainder by zero detected in reachable expression" };
            if (ls == min_s and rs == -1) {
                return .{ .trap_overflow = "signed `MIN % -1` remainder overflowed at compile time" };
            }
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, @bitCast(@rem(ls, rs)), target_layout) };
        },
        .urem_checked => {
            if (ru == 0) return .{ .trap_arithmetic = "remainder by zero detected in reachable expression" };
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, lu % ru, target_layout) };
        },
        .shl_checked, .ashr_checked, .lshr_checked => {
            const rhs_info = resolveOptIntInfo(pool, pool.unwrapUnderlyingType(rhs_ty), target_layout) orelse info;
            const rhs_u = zextConstInt(raw_r, rhs_info.bits);
            const rhs_s = sextConstInt(raw_r, rhs_info.bits);
            if ((rhs_info.is_signed and rhs_s < 0) or rhs_u >= info.bits) {
                return .{ .trap_overflow = "shift count out of range `[0, bit_width)` at compile time" };
            }
            const shift_amt: u7 = @intCast(rhs_u);
            const res_u: u128 = switch (kind) {
                .shl_checked => (lu << shift_amt) & max_u,
                .lshr_checked => lu >> shift_amt,
                .ashr_checked => @bitCast(ls >> shift_amt),
                else => unreachable,
            };
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, res_u, target_layout) };
        },
        .add_wrap => return .{ .folded = makeTypedIntMirConst(pool, res_ty, (lu +% ru) & max_u, target_layout) },
        .sub_wrap => return .{ .folded = makeTypedIntMirConst(pool, res_ty, (lu -% ru) & max_u, target_layout) },
        .mul_wrap => return .{ .folded = makeTypedIntMirConst(pool, res_ty, (lu *% ru) & max_u, target_layout) },
        .shl_wrap => {
            const rhs_info = resolveOptIntInfo(pool, pool.unwrapUnderlyingType(rhs_ty), target_layout) orelse info;
            const shift_amt: u7 = @intCast(zextConstInt(raw_r, rhs_info.bits) % info.bits);
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, (lu << shift_amt) & max_u, target_layout) };
        },
        .lshr_wrap => {
            const rhs_info = resolveOptIntInfo(pool, pool.unwrapUnderlyingType(rhs_ty), target_layout) orelse info;
            const shift_amt: u7 = @intCast(zextConstInt(raw_r, rhs_info.bits) % info.bits);
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, lu >> shift_amt, target_layout) };
        },
        .ashr_wrap => {
            const rhs_info = resolveOptIntInfo(pool, pool.unwrapUnderlyingType(rhs_ty), target_layout) orelse info;
            const shift_amt: u7 = @intCast(zextConstInt(raw_r, rhs_info.bits) % info.bits);
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, @bitCast(ls >> shift_amt), target_layout) };
        },
        .sadd_sat => {
            const ov = @addWithOverflow(ls, rs);
            const sat: i128 = if (ov[1] != 0)
                (if (ls < 0) min_s else max_s)
            else
                std.math.clamp(ov[0], min_s, max_s);
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, @bitCast(sat), target_layout) };
        },
        .uadd_sat => {
            const ov = @addWithOverflow(lu, ru);
            const sat: u128 = if (ov[1] != 0 or ov[0] > max_u) max_u else ov[0];
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, sat, target_layout) };
        },
        .ssub_sat => {
            const ov = @subWithOverflow(ls, rs);
            const sat: i128 = if (ov[1] != 0)
                (if (ls < 0) min_s else max_s)
            else
                std.math.clamp(ov[0], min_s, max_s);
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, @bitCast(sat), target_layout) };
        },
        .usub_sat => {
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, if (lu < ru) 0 else lu - ru, target_layout) };
        },
        .smul_sat => {
            const ov = @mulWithOverflow(ls, rs);
            const sat: i128 = if (ov[1] != 0)
                (if ((ls < 0) != (rs < 0)) min_s else max_s)
            else
                std.math.clamp(ov[0], min_s, max_s);
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, @bitCast(sat), target_layout) };
        },
        .umul_sat => {
            const ov = @mulWithOverflow(lu, ru);
            const sat: u128 = if (ov[1] != 0 or ov[0] > max_u) max_u else ov[0];
            return .{ .folded = makeTypedIntMirConst(pool, res_ty, sat, target_layout) };
        },
        .bit_and => return .{ .folded = makeTypedIntMirConst(pool, res_ty, lu & ru, target_layout) },
        .bit_or => return .{ .folded = makeTypedIntMirConst(pool, res_ty, lu | ru, target_layout) },
        .bit_xor => return .{ .folded = makeTypedIntMirConst(pool, res_ty, (lu ^ ru) & max_u, target_layout) },
        .slt => return .{ .folded = .{ .bool_val = ls < rs } },
        .ult => return .{ .folded = .{ .bool_val = lu < ru } },
        .sle => return .{ .folded = .{ .bool_val = ls <= rs } },
        .ule => return .{ .folded = .{ .bool_val = lu <= ru } },
        .sgt => return .{ .folded = .{ .bool_val = ls > rs } },
        .ugt => return .{ .folded = .{ .bool_val = lu > ru } },
        .sge => return .{ .folded = .{ .bool_val = ls >= rs } },
        .uge => return .{ .folded = .{ .bool_val = lu >= ru } },
        else => return .not_foldable,
    }
}

/// Evaluates `UnaryOpKind` on a constant `MirConst` operand (`E0502` / `E0507` on checked traps).
fn foldConstUnaryOp(
    pool: *const InternPool,
    kind: UnaryOpKind,
    src_mc: MirConst,
    src_ty_raw: TypeId,
    dst_ty_raw: TypeId,
    target_layout: TargetLayout,
) ConstEvalResult {
    const src_ty = pool.unwrapUnderlyingType(src_ty_raw);
    const dst_ty = pool.unwrapUnderlyingType(dst_ty_raw);

    switch (kind) {
        .sneg_checked => {
            const info = resolveOptIntInfo(pool, src_ty, target_layout) orelse return .not_foldable;
            const ls = sextConstInt(constToI128(src_mc) orelse return .not_foldable, info.bits);
            const min_s: i128 = if (info.bits >= 128)
                std.math.minInt(i128)
            else
                -(@as(i128, 1) << @intCast(info.bits - 1));
            if (ls == min_s) return .{ .trap_overflow = "signed negation of `MIN` overflowed at compile time" };
            return .{ .folded = makeTypedIntMirConst(pool, dst_ty, @bitCast(-ls), target_layout) };
        },
        .neg_wrap => {
            const info = resolveOptIntInfo(pool, src_ty, target_layout) orelse return .not_foldable;
            const lu = zextConstInt(constToI128(src_mc) orelse return .not_foldable, info.bits);
            return .{ .folded = makeTypedIntMirConst(pool, dst_ty, 0 -% lu, target_layout) };
        },
        .fneg => {
            const fv = switch (src_mc) {
                .float_val => |fl| fl,
                else => return .not_foldable,
            };
            if (src_ty == .f32_ty) return .{ .folded = .{ .float_val = canonOptF32AsF64(-@as(f32, @floatCast(fv))) } };
            return .{ .folded = .{ .float_val = canonOptF64(-fv) } };
        },
        .bool_not => {
            const bv = constToI128(src_mc) orelse return .not_foldable;
            return .{ .folded = .{ .bool_val = (bv & 1) == 0 } };
        },
        .bit_not => {
            const info = resolveOptIntInfo(pool, src_ty, target_layout) orelse return .not_foldable;
            const lu = zextConstInt(constToI128(src_mc) orelse return .not_foldable, info.bits);
            return .{ .folded = makeTypedIntMirConst(pool, dst_ty, ~lu, target_layout) };
        },
        .int_sext => {
            const info = resolveOptIntInfo(pool, src_ty, target_layout) orelse return .not_foldable;
            const ls = sextConstInt(constToI128(src_mc) orelse return .not_foldable, info.bits);
            return .{ .folded = makeTypedIntMirConst(pool, dst_ty, @bitCast(ls), target_layout) };
        },
        .int_zext, .int_trunc => {
            const info = resolveOptIntInfo(pool, src_ty, target_layout) orelse return .not_foldable;
            const lu = zextConstInt(constToI128(src_mc) orelse return .not_foldable, info.bits);
            return .{ .folded = makeTypedIntMirConst(pool, dst_ty, lu, target_layout) };
        },
        .int_to_float_signed => {
            const info = resolveOptIntInfo(pool, src_ty, target_layout) orelse return .not_foldable;
            const ls = sextConstInt(constToI128(src_mc) orelse return .not_foldable, info.bits);
            if (dst_ty == .f32_ty) return .{ .folded = .{ .float_val = canonOptF32AsF64(@floatFromInt(ls)) } };
            return .{ .folded = .{ .float_val = canonOptF64(@floatFromInt(ls)) } };
        },
        .int_to_float_unsigned => {
            const info = resolveOptIntInfo(pool, src_ty, target_layout) orelse return .not_foldable;
            const lu = zextConstInt(constToI128(src_mc) orelse return .not_foldable, info.bits);
            if (dst_ty == .f32_ty) return .{ .folded = .{ .float_val = canonOptF32AsF64(@floatFromInt(lu)) } };
            return .{ .folded = .{ .float_val = canonOptF64(@floatFromInt(lu)) } };
        },
        .float_to_int_signed => {
            const fv = switch (src_mc) {
                .float_val => |fl| fl,
                else => return .not_foldable,
            };
            if (std.math.isNan(fv) or std.math.isInf(fv)) {
                return .{ .trap_arithmetic = "cannot cast `NaN` or `Inf` float to integer" };
            }
            const dst_info = resolveOptIntInfo(pool, dst_ty, target_layout) orelse return .not_foldable;
            const trunc_v = @trunc(fv);
            const min_f: f64 = if (dst_info.bits >= 128)
                @floatFromInt(std.math.minInt(i128))
            else
                -@as(f64, @floatFromInt(@as(u128, 1) << @intCast(dst_info.bits - 1)));
            const max_excl_f: f64 = if (dst_info.bits >= 128)
                170141183460469231731687303715884105728.0
            else
                @floatFromInt(@as(u128, 1) << @intCast(dst_info.bits - 1));
            if (trunc_v < min_f or trunc_v >= max_excl_f) {
                return .{ .trap_arithmetic = "float-to-signed-integer cast out of target range" };
            }
            const int_s: i128 = @intFromFloat(trunc_v);
            return .{ .folded = makeTypedIntMirConst(pool, dst_ty, @bitCast(int_s), target_layout) };
        },
        .float_to_int_unsigned => {
            const fv = switch (src_mc) {
                .float_val => |fl| fl,
                else => return .not_foldable,
            };
            if (std.math.isNan(fv) or std.math.isInf(fv)) {
                return .{ .trap_arithmetic = "cannot cast `NaN` or `Inf` float to unsigned integer" };
            }
            const dst_info = resolveOptIntInfo(pool, dst_ty, target_layout) orelse return .not_foldable;
            const trunc_v = @trunc(fv);
            const max_excl_f: f64 = if (dst_info.bits >= 128)
                340282366920938463463374607431768211456.0
            else
                @floatFromInt(@as(u128, 1) << @intCast(dst_info.bits));
            if (trunc_v < 0.0 or trunc_v >= max_excl_f) {
                return .{ .trap_arithmetic = "float-to-unsigned-integer cast out of target range" };
            }
            const int_u: u128 = @intFromFloat(trunc_v);
            return .{ .folded = makeTypedIntMirConst(pool, dst_ty, int_u, target_layout) };
        },
        .float_promote => {
            const fv = switch (src_mc) {
                .float_val => |fl| fl,
                else => return .not_foldable,
            };
            return .{ .folded = .{ .float_val = canonOptF64(fv) } };
        },
        .float_demote => {
            const fv = switch (src_mc) {
                .float_val => |fl| fl,
                else => return .not_foldable,
            };
            return .{ .folded = .{ .float_val = canonOptF32AsF64(@floatCast(fv)) } };
        },
        else => return .not_foldable,
    }
}

/// Selects the matching outgoing edge offset (`0 .. term.edge_len - 1`) on `.switch_int` for `discr_mc`.
fn selectConstSwitchEdgeOffset(body: *const MirBody, term: MirTerminator, discr_mc: MirConst) ?usize {
    if (term.edge_len == 0) return null;
    const discr_int = constToI128(discr_mc) orelse return null;
    const case_count = term.edge_len - 1;
    for (0..case_count) |off| {
        const edge = body.extra_edges.items[term.edge_start + off];
        if (edge.case_tag_idx < body.switch_values.items.len and
            body.switch_values.items[edge.case_tag_idx] == discr_int)
        {
            return off;
        }
    }
    return case_count;
}

/// Pass `D2`: Reachable-only local constant folding & `E0502`/`E0507` compile-time traps.
///
/// Crucially tracks constant-aware CFG reachability from `^bb0` so dead arms like `if false { 1 / 0 }`
/// are never visited and never emit false-positive compile-time overflow/div-zero traps!
fn runPassD2ReachableConstFold(
    allocator: std.mem.Allocator,
    body: *MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    config: MirOptConfig,
    sink: ?*DiagnosticSink,
) !void {
    const block_count = body.blocks.items.len;
    if (block_count == 0) return;

    // Skip constant-trap emission on unspecialized generic templates prior to `D5`:
    if (isGenericTemplateBody(body, pool, sym_table)) return;

    var dom = try mir.computeDominators(allocator, body);
    defer dom.deinit();

    const known_consts = try allocator.alloc(?MirConst, body.insts.len);
    defer allocator.free(known_consts);
    @memset(known_consts, null);

    const has_emitted_trap = try allocator.alloc(bool, body.insts.len);
    defer allocator.free(has_emitted_trap);
    @memset(has_emitted_trap, false);

    const exec_edge = try allocator.alloc(bool, body.extra_edges.items.len);
    defer allocator.free(exec_edge);
    @memset(exec_edge, false);

    const exec_block = try allocator.alloc(bool, block_count);
    defer allocator.free(exec_block);
    @memset(exec_block, false);
    exec_block[0] = true;

    var has_changed = true;
    while (has_changed) {
        has_changed = false;
        for (dom.rpo_blocks) |bb_idx| {
            if (!exec_block[bb_idx]) continue;
            const bb_id = MirBlockId.fromInt(bb_idx);

            for (body.getBlockInsts(bb_id)) |inst_val| {
                const raw = inst_val.asInt();
                if (raw >= known_consts.len or has_emitted_trap[raw]) continue;
                const inst = body.getInst(inst_val);
                switch (inst.op) {
                    .const_scalar => {
                        if (known_consts[raw] == null and inst.operands.lhs < body.consts.items.len) {
                            known_consts[raw] = body.consts.items[inst.operands.lhs];
                            has_changed = true;
                        }
                    },
                    .copy_val => {
                        if (known_consts[raw] == null and inst.operands.lhs < known_consts.len) {
                            if (known_consts[inst.operands.lhs]) |mc| {
                                known_consts[raw] = mc;
                                has_changed = true;
                            }
                        }
                    },
                    .bin_op => {
                        if (known_consts[raw] != null) continue;
                        if (inst.operands.lhs >= known_consts.len or inst.operands.rhs >= known_consts.len) continue;
                        const l_mc = known_consts[inst.operands.lhs] orelse continue;
                        const r_mc = known_consts[inst.operands.rhs] orelse continue;
                        const bkind: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                        const op_ty = body.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id;
                        const rhs_ty = body.getInst(MirValueId.fromInt(inst.operands.rhs)).type_id;
                        switch (foldConstBinOp(pool, bkind, l_mc, r_mc, op_ty, rhs_ty, inst.type_id, config.target_layout)) {
                            .folded => |mc| {
                                const c_idx = try body.appendConst(mc);
                                body.insts.set(raw, .{
                                    .op = .const_scalar,
                                    .flags = .{},
                                    .type_id = inst.type_id,
                                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                                });
                                known_consts[raw] = mc;
                                has_changed = true;
                            },
                            .trap_overflow => |msg| {
                                const tok = body.origin_tokens.items[raw];
                                const span = resolveOptDiagSpan(body.file_id, tok, .none, sym_table, config);
                                try emitOptDiagnostic(
                                    sink,
                                    .e0502_integer_constant_overflow,
                                    .err,
                                    span,
                                    msg,
                                    "compile-time integer overflow here",
                                );
                                has_emitted_trap[raw] = true;
                            },
                            .trap_arithmetic => |msg| {
                                const tok = body.origin_tokens.items[raw];
                                const span = resolveOptDiagSpan(body.file_id, tok, .none, sym_table, config);
                                try emitOptDiagnostic(
                                    sink,
                                    .e0507_comptime_arithmetic_trap,
                                    .err,
                                    span,
                                    msg,
                                    "compile-time arithmetic trap here",
                                );
                                has_emitted_trap[raw] = true;
                            },
                            .not_foldable => {},
                        }
                    },
                    .unary_op => {
                        if (known_consts[raw] != null) continue;
                        if (inst.operands.lhs >= known_consts.len) continue;
                        const s_mc = known_consts[inst.operands.lhs] orelse continue;
                        const ukind: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                        const s_ty = body.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id;
                        switch (foldConstUnaryOp(pool, ukind, s_mc, s_ty, inst.type_id, config.target_layout)) {
                            .folded => |mc| {
                                const c_idx = try body.appendConst(mc);
                                body.insts.set(raw, .{
                                    .op = .const_scalar,
                                    .flags = .{},
                                    .type_id = inst.type_id,
                                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                                });
                                known_consts[raw] = mc;
                                has_changed = true;
                            },
                            .trap_overflow => |msg| {
                                const tok = body.origin_tokens.items[raw];
                                const span = resolveOptDiagSpan(body.file_id, tok, .none, sym_table, config);
                                try emitOptDiagnostic(
                                    sink,
                                    .e0502_integer_constant_overflow,
                                    .err,
                                    span,
                                    msg,
                                    "compile-time integer overflow here",
                                );
                                has_emitted_trap[raw] = true;
                            },
                            .trap_arithmetic => |msg| {
                                const tok = body.origin_tokens.items[raw];
                                const span = resolveOptDiagSpan(body.file_id, tok, .none, sym_table, config);
                                try emitOptDiagnostic(
                                    sink,
                                    .e0507_comptime_arithmetic_trap,
                                    .err,
                                    span,
                                    msg,
                                    "compile-time arithmetic trap here",
                                );
                                has_emitted_trap[raw] = true;
                            },
                            .not_foldable => {},
                        }
                    },
                    else => {},
                }
            }

            // Propagate constant-aware outgoing CFG edges:
            const term = body.blocks.items[bb_idx].terminator;
            switch (term.kind) {
                .cond_br => {
                    const maybe_cond = if (term.cond_or_val < known_consts.len)
                        known_consts[term.cond_or_val]
                    else
                        null;
                    if (maybe_cond) |cond_mc| {
                        if (cond_mc == .bool_val) {
                            const chosen_off: u32 = if (cond_mc.bool_val) 0 else 1;
                            const eid = term.edge_start + chosen_off;
                            if (!exec_edge[eid]) {
                                exec_edge[eid] = true;
                                exec_block[body.extra_edges.items[eid].target_bb.asInt()] = true;
                                has_changed = true;
                            }
                            continue;
                        }
                    }
                },
                .switch_int => {
                    const maybe_discr = if (term.cond_or_val < known_consts.len)
                        known_consts[term.cond_or_val]
                    else
                        null;
                    if (maybe_discr) |discr_mc| {
                        if (selectConstSwitchEdgeOffset(body, term, discr_mc)) |chosen_off| {
                            const eid = term.edge_start + @as(u32, @intCast(chosen_off));
                            if (!exec_edge[eid]) {
                                exec_edge[eid] = true;
                                exec_block[body.extra_edges.items[eid].target_bb.asInt()] = true;
                                has_changed = true;
                            }
                            continue;
                        }
                    }
                },
                else => {},
            }

            for (0..term.edge_len) |off| {
                const eid = term.edge_start + @as(u32, @intCast(off));
                if (!exec_edge[eid]) {
                    exec_edge[eid] = true;
                    exec_block[body.extra_edges.items[eid].target_bb.asInt()] = true;
                    has_changed = true;
                }
            }
        }
    }
}

// ---------- Pass `D3`: Ghost Instruction Strip Gate -----------

/// Pass `D3`: Strips all Phase 6 Ghost Lifetime & Ghost Storage instructions (`1..7`),
/// clearing `call_borrows_len` and flipping `has_ghost_instructions = false, is_ghost_stripped = true`.
fn runPassD3StripGhostInstructions(allocator: std.mem.Allocator, body: *MirBody) !void {
    if (body.is_ghost_stripped) {
        body.has_ghost_instructions = false;
        return;
    }

    var new_block_insts: std.ArrayListUnmanaged(MirValueId) = .empty;
    errdefer new_block_insts.deinit(body.allocator);
    try new_block_insts.ensureTotalCapacity(body.allocator, body.block_insts.items.len);

    for (body.blocks.items, 0..) |*bb, bb_i| {
        const old_slice = body.getBlockInsts(MirBlockId.fromInt(@intCast(bb_i)));
        const start: u32 = @intCast(new_block_insts.items.len);
        var kept: u32 = 0;
        for (old_slice) |inst_val| {
            if (body.getInst(inst_val).op.isGhost()) continue;
            new_block_insts.appendAssumeCapacity(inst_val);
            kept += 1;
        }
        bb.inst_start = start;
        bb.inst_len = kept;
    }

    body.block_insts.deinit(body.allocator);
    body.block_insts = new_block_insts;

    for (body.calls.items) |*call_site| {
        call_site.call_borrows_len = 0;
    }

    body.has_ghost_instructions = false;
    body.is_ghost_stripped = true;
    _ = allocator;
}

// --------- Pass `D4`: Constant Branch & Block Pruning ---------

/// Extracts a `MirConst` if `raw_val` is a `MirOp.const_scalar` (following `.copy_val` chains).
fn extractKnownScalarConst(body: *const MirBody, raw_val: u32) ?MirConst {
    var cur = raw_val;
    var guard: usize = 0;
    while (cur < body.insts.len and guard < 16) : (guard += 1) {
        const inst = body.getInst(MirValueId.fromInt(cur));
        if (inst.op == .const_scalar and inst.operands.lhs < body.consts.items.len) {
            return body.consts.items[inst.operands.lhs];
        }
        if (inst.op == .copy_val) {
            cur = inst.operands.lhs;
            continue;
        }
        break;
    }
    return null;
}

/// Pass `D4`: Folds constant `cond_br` / `switch_int` terminators into unconditional `.br`,
/// detaches untaken `EdgeId`s, and prunes unreachable basic blocks in a single BFS sweep (`[MAJOR-01]`).
fn runPassD4BranchFoldAndPrune(allocator: std.mem.Allocator, body: *MirBody) !void {
    for (body.blocks.items) |*bb| {
        switch (bb.terminator.kind) {
            .cond_br => {
                if (extractKnownScalarConst(body, bb.terminator.cond_or_val)) |cond_mc| {
                    if (cond_mc == .bool_val and bb.terminator.edge_len == 2) {
                        const chosen_off: u32 = if (cond_mc.bool_val) 0 else 1;
                        const kept_eid = bb.terminator.edge_start + chosen_off;
                        body.extra_edges.items[kept_eid].case_tag_idx = std.math.maxInt(u16);
                        bb.terminator = .{
                            .kind = .br,
                            .edge_len = 1,
                            .edge_start = kept_eid,
                        };
                    }
                }
            },
            .switch_int => {
                if (extractKnownScalarConst(body, bb.terminator.cond_or_val)) |discr_mc| {
                    if (selectConstSwitchEdgeOffset(body, bb.terminator, discr_mc)) |chosen_off| {
                        const kept_eid = bb.terminator.edge_start + @as(u32, @intCast(chosen_off));
                        body.extra_edges.items[kept_eid].case_tag_idx = std.math.maxInt(u16);
                        bb.terminator = .{
                            .kind = .br,
                            .edge_len = 1,
                            .edge_start = kept_eid,
                        };
                    }
                }
            },
            else => {},
        }
    }

    try rebuildPredsAndSweepUnreachable(allocator, body);
}


// -------- Pass `D5`: Monomorphization & `contextless` ---------

/// Returns `true` if `ty` contains unresolved generic `type_param` or Type Group variables.
fn hasGenericVarsInType(pool: *const InternPool, ty: TypeId) bool {
    if (ty.isError()) return false;
    const node = pool.getNode(ty);
    if (node.flags.has_type_vars) return true;
    return switch (node.tag) {
        .builtin_group,
        .user_group,
        .type_param,
        .bind_once_group_var,
        .bind_many_any_var,
        .associated_ty,
        => true,
        else => false,
    };
}

/// Returns `true` if `body` represents an unspecialized generic / Type-Group template function.
fn isGenericTemplateBody(
    body: *const MirBody,
    maybe_pool: ?*const InternPool,
    sym_table: *const SymbolTable,
) bool {
    if (maybe_pool) |pool| {
        if (hasGenericVarsInType(pool, body.ret_ty)) return true;
        for (body.locals.items) |loc| {
            if (hasGenericVarsInType(pool, loc.type_id)) return true;
        }
    }
    const sym_idx: SymbolIndex = if (!body.symbol_index.isNone())
        body.symbol_index
    else if (!body.def_id.isNone())
        (sym_table.def_to_symbol.get(body.def_id.asInt()) orelse .none)
    else
        .none;
    if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
        const sym = sym_table.getSymbol(sym_idx).*;
        if (sym.kind == .fn_sym) {
            if (!sym.target_scope.isNone()) {
                for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                    const mem_kind = sym_table.getSymbol(mem_idx).kind;
                    if (mem_kind == .type_param_sym or mem_kind == .const_param_sym) return true;
                }
            }
            if (maybe_pool) |pool| {
                if (hasGenericVarsInType(pool, sym.type_id)) return true;
            }
        }
    }
    return false;
}

/// Returns `true` if `body` is a `comptime fn` excluded from runtime monomorphization (`DR-13` §5.1).
fn isComptimeOnlyBody(
    body: *const MirBody,
    sym_table: *const SymbolTable,
    config: MirOptConfig,
) bool {
    if (!body.def_id.isNone()) {
        if (config.comptime_fn_defs) |ct_map| {
            if (ct_map.contains(body.def_id.asInt())) return true;
        }
    }
    const sym_idx: SymbolIndex = if (!body.symbol_index.isNone())
        body.symbol_index
    else if (!body.def_id.isNone())
        (sym_table.def_to_symbol.get(body.def_id.asInt()) orelse .none)
    else
        .none;
    if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
        const sym = sym_table.getSymbol(sym_idx).*;
        if (sym.kind == .fn_sym) return sym.flags.is_comptime;
    }
    return false;
}

/// Resolves the concrete `TypeId` of `place_id` in `body` for generic call-site unification.
fn inferPlaceTypeInBody(
    body: *const MirBody,
    place_id: PlaceId,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
) TypeId {
    if (place_id.isNone() or place_id.asInt() >= body.places.items.len) return .err_ty;
    const place = body.places.items[place_id.asInt()];
    if (place.base >= body.locals.items.len) return .err_ty;
    var cur_ty = pool.unwrapUnderlyingType(body.locals.items[place.base].type_id);
    var active_soa_field_ty: ?TypeId = null;
    for (body.getPlaceProjections(place_id)) |proj| {
        if (active_soa_field_ty) |soa_field_ty| {
            active_soa_field_ty = null;
            if (proj.kind == .index) {
                cur_ty = soa_field_ty;
                continue;
            } else if (proj.kind == .slice_len) {
                cur_ty = .usize_ty;
                continue;
            }
            return .err_ty;
        }
        if (cur_ty.isError()) return .err_ty;
        const node = pool.getNode(cur_ty);
        switch (proj.kind) {
            .deref => cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs)),
            .index => cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs)),
            .slice_len => cur_ty = .usize_ty,
            .field => {
                if (node.tag == .tuple_ty) {
                    const elems = pool.getTupleElements(cur_ty);
                    if (proj.payload < elems.len) {
                        cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(elems[proj.payload]));
                    }
                } else if (node.tag == .struct_ty or node.tag == .union_ty) {
                    const sym = sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                    if (!sym.target_scope.isNone()) {
                        var ord: u32 = 0;
                        for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                            const mem = sym_table.getSymbol(mem_idx).*;
                            if (mem.kind != .field_sym) continue;
                            if (ord == proj.payload) {
                                cur_ty = pool.unwrapUnderlyingType(mem.type_id);
                                break;
                            }
                            ord += 1;
                        }
                    }
                }
            },
            .soa_elem => {
                const elem_ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const elem_node = pool.getNode(elem_ty);
                if (elem_node.tag == .struct_ty) {
                    const sym = sym_table.getSymbol(SymbolIndex.fromInt(elem_node.rhs)).*;
                    if (!sym.target_scope.isNone()) {
                        var ord: u32 = 0;
                        for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                            const mem = sym_table.getSymbol(mem_idx).*;
                            if (mem.kind != .field_sym) continue;
                            if (ord == proj.payload) {
                                active_soa_field_ty = pool.unwrapUnderlyingType(mem.type_id);
                                break;
                            }
                            ord += 1;
                        }
                    }
                }
            },
            .downcast => {},
        }
    }
    return cur_ty;
}

/// Unifies `pattern_ty` (from a generic template) with `concrete_ty` (from a caller), recording
/// `type_var_raw -> concrete_ty` bindings into `subst`.
fn unifyTemplateTypeBinding(
    allocator: std.mem.Allocator,
    pool: *InternPool,
    pattern_ty: TypeId,
    concrete_ty: TypeId,
    subst: *std.AutoHashMapUnmanaged(u32, TypeId),
    ordered_vars: *std.ArrayListUnmanaged(u32),
    depth: u32,
) !void {
    if (depth > 24 or pattern_ty.isError() or concrete_ty.isError() or pattern_ty == concrete_ty) return;
    const p_node = pool.getNode(pattern_ty);
    switch (p_node.tag) {
        .type_param,
        .bind_once_group_var,
        .bind_many_any_var,
        .builtin_group,
        .user_group,
        => {
            if (!subst.contains(pattern_ty.toU32())) {
                try subst.put(allocator, pattern_ty.toU32(), concrete_ty);
                try ordered_vars.append(allocator, pattern_ty.toU32());
            }
            return;
        },
        else => {},
    }

    const c_unwrapped = pool.unwrapUnderlyingType(concrete_ty);
    const c_node = pool.getNode(c_unwrapped);
    if (p_node.tag != c_node.tag) return;

    switch (p_node.tag) {
        .ref_ty,
        .mut_ref_ty,
        .raw_ptr_ty,
        .slice_ty,
        .soa_slice_ty,
        .optional_ty,
        .tilde_approx,
        => {
            try unifyTemplateTypeBinding(
                allocator,
                pool,
                TypeId.fromInt(p_node.lhs),
                TypeId.fromInt(c_node.lhs),
                subst,
                ordered_vars,
                depth + 1,
            );
        },
        .array_ty,
        .soa_array_ty,
        => {
            if ((p_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) != 0 and
                (c_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) == 0)
            {
                const const_sym = SymbolId.fromInt(p_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG);
                const len_key = try pool.internSymbolicArray(.unit_ty, const_sym, false);
                if (!subst.contains(len_key.toU32())) {
                    const concrete_len_ty = try pool.internArray(.unit_ty, c_node.rhs, false);
                    try subst.put(allocator, len_key.toU32(), concrete_len_ty);
                    try ordered_vars.append(allocator, len_key.toU32());
                }
            }
            try unifyTemplateTypeBinding(
                allocator,
                pool,
                TypeId.fromInt(p_node.lhs),
                TypeId.fromInt(c_node.lhs),
                subst,
                ordered_vars,
                depth + 1,
            );
        },
        .result_ty => {
            try unifyTemplateTypeBinding(
                allocator,
                pool,
                TypeId.fromInt(p_node.lhs),
                TypeId.fromInt(c_node.lhs),
                subst,
                ordered_vars,
                depth + 1,
            );
            try unifyTemplateTypeBinding(
                allocator,
                pool,
                TypeId.fromInt(p_node.rhs),
                TypeId.fromInt(c_node.rhs),
                subst,
                ordered_vars,
                depth + 1,
            );
        },
        .tuple_ty => {
            const p_elems = pool.getTupleElements(pattern_ty);
            const c_elems = pool.getTupleElements(c_unwrapped);
            const n = @min(p_elems.len, c_elems.len);
            for (0..n) |i| {
                try unifyTemplateTypeBinding(
                    allocator,
                    pool,
                    TypeId.fromInt(p_elems[i]),
                    TypeId.fromInt(c_elems[i]),
                    subst,
                    ordered_vars,
                    depth + 1,
                );
            }
        },
        else => {},
    }
}

/// Substitutes generic/group variables inside `ty` using `subst`, interning new structural types in `pool`.
fn substituteMirType(
    allocator: std.mem.Allocator,
    pool: *InternPool,
    ty: TypeId,
    subst: *const std.AutoHashMapUnmanaged(u32, TypeId),
    depth: u32,
) !TypeId {
    if (depth > 24 or ty.isError()) return ty;
    if (subst.get(ty.toU32())) |mapped| return mapped;
    if (!hasGenericVarsInType(pool, ty)) return ty;

    const node = pool.getNode(ty);
    switch (node.tag) {
        .ref_ty => {
            const inner = try substituteMirType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1);
            return pool.internRef(inner, false);
        },
        .mut_ref_ty => {
            const inner = try substituteMirType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1);
            return pool.internRef(inner, true);
        },
        .raw_ptr_ty => {
            const inner = try substituteMirType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1);
            return pool.internRawPtr(inner, node.rhs != 0);
        },
        .slice_ty => {
            const inner = try substituteMirType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1);
            return pool.internSlice(inner, false);
        },
        .soa_slice_ty => {
            const inner = try substituteMirType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1);
            return pool.internSlice(inner, true);
        },
        .array_ty, .soa_array_ty => {
            const inner = try substituteMirType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1);
            const is_soa = (node.tag == .soa_array_ty);
            if ((node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) != 0) {
                const const_sym = mem_foundation.SymbolId.fromInt(node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG);
                const len_key = try pool.internSymbolicArray(.unit_ty, const_sym, false);
                if (subst.get(len_key.toU32())) |bound_len_ty| {
                    const bound_node = pool.getNode(bound_len_ty);
                    if (bound_node.tag == .array_ty and (bound_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) == 0) {
                        return pool.internArray(inner, bound_node.rhs, is_soa);
                    }
                }
                return pool.internSymbolicArray(inner, const_sym, is_soa);
            }
            return pool.internArray(inner, node.rhs, is_soa);
        },
        .optional_ty => {
            const inner = try substituteMirType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1);
            return pool.internOptional(inner);
        },
        .result_ty => {
            const ok_ty = try substituteMirType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1);
            const err_ty = try substituteMirType(allocator, pool, TypeId.fromInt(node.rhs), subst, depth + 1);
            return pool.internResult(ok_ty, err_ty);
        },
        .tuple_ty => {
            const old_elems = pool.getTupleElements(ty);
            const new_elems = try allocator.alloc(TypeId, old_elems.len);
            defer allocator.free(new_elems);
            for (old_elems, 0..) |raw_e, i| {
                new_elems[i] = try substituteMirType(allocator, pool, TypeId.fromInt(raw_e), subst, depth + 1);
            }
            return pool.internTuple(new_elems);
        },
        else => return ty,
    }
}

/// Adapts signed/unsigned/float `BinOpKind` after generic / Type-Group substitution (`[CRITICAL-09]`).
fn specializeBinOpForSemantics(kind: BinOpKind, sem: OpSemanticsTag) BinOpKind {
    return switch (sem) {
        .unsigned_int => switch (kind) {
            .sadd_checked => .uadd_checked,
            .ssub_checked => .usub_checked,
            .smul_checked => .umul_checked,
            .sdiv_checked => .udiv_checked,
            .srem_checked => .urem_checked,
            .ashr_checked => .lshr_checked,
            .ashr_wrap => .lshr_wrap,
            .sadd_sat => .uadd_sat,
            .ssub_sat => .usub_sat,
            .smul_sat => .umul_sat,
            .slt => .ult,
            .sle => .ule,
            .sgt => .ugt,
            .sge => .uge,
            else => kind,
        },
        .ieee_f32, .ieee_f64 => switch (kind) {
            .sadd_checked, .uadd_checked, .add_wrap => .fadd,
            .ssub_checked, .usub_checked, .sub_wrap => .fsub,
            .smul_checked, .umul_checked, .mul_wrap => .fmul,
            .sdiv_checked, .udiv_checked => .fdiv,
            .srem_checked, .urem_checked => .frem,
            .slt, .ult => .flt,
            .sle, .ule => .fle,
            .sgt, .ugt => .fgt,
            .sge, .uge => .fge,
            else => kind,
        },
        .signed_int => switch (kind) {
            .uadd_checked => .sadd_checked,
            .usub_checked => .ssub_checked,
            .umul_checked => .smul_checked,
            .udiv_checked => .sdiv_checked,
            .urem_checked => .srem_checked,
            .ult => .slt,
            .ule => .sle,
            .ugt => .sgt,
            .uge => .sge,
            else => kind,
        },
        else => kind,
    };
}

/// Adapts `UnaryOpKind` after generic / Type-Group substitution (`[CRITICAL-09]`).
fn specializeUnaryOpForSemantics(kind: UnaryOpKind, sem: OpSemanticsTag) UnaryOpKind {
    if (sem == .ieee_f32 or sem == .ieee_f64) {
        if (kind == .sneg_checked or kind == .neg_wrap) return .fneg;
    }
    return kind;
}

/// Resolved byte offset and member `TypeId` of a composite field projection step.
const OptFieldStep = struct {
    /// Byte offset from the base composite start.
    byte_offset: u64,
    /// Unwrapped or raw member `TypeId` at `ordinal`.
    field_ty: TypeId,
};

/// Resolves the byte offset and member `TypeId` of `field_ordinal` inside `.struct_ty`, `.tuple_ty`, or `.union_ty`.
fn resolveOptCompositeFieldStep(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_comp_ty: TypeId,
    field_ordinal: u32,
    target_layout: TargetLayout,
) ?OptFieldStep {
    const comp_ty = pool.unwrapUnderlyingType(raw_comp_ty);
    if (comp_ty.isError()) return null;
    const node = pool.getNode(comp_ty);
    switch (node.tag) {
        .tuple_ty => {
            const elems = pool.getTupleElements(comp_ty);
            if (field_ordinal >= elems.len) return null;
            var cur_offset: u64 = 0;
            for (elems, 0..) |raw_elem, idx| {
                const elem_ty = TypeId.fromInt(raw_elem);
                const elem_lay = type_system.computeTypeLayoutWithPool(pool, sym_table, elem_ty, target_layout);
                cur_offset = std.mem.alignForward(u64, cur_offset, @max(@as(u64, elem_lay.align_bytes), 1));
                if (idx == field_ordinal) {
                    return .{ .byte_offset = cur_offset, .field_ty = elem_ty };
                }
                cur_offset += elem_lay.byte_size;
            }
            return null;
        },
        .struct_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return null;
            const st_sym = sym_table.getSymbol(sym_idx).*;
            if (st_sym.target_scope.isNone()) return null;
            var ord: u32 = 0;
            for (sym_table.getScopeMembers(st_sym.target_scope)) |mem_idx| {
                const mem_sym = sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .field_sym) continue;
                if (ord == field_ordinal) {
                    const byte_off: u64 = type_system.computeStructFieldOffset(
                        pool,
                        sym_table,
                        comp_ty,
                        field_ordinal,
                        target_layout,
                    ) orelse 0;
                    return .{ .byte_offset = byte_off, .field_ty = mem_sym.type_id };
                }
                ord += 1;
            }
            return null;
        },
        .union_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return null;
            const un_sym = sym_table.getSymbol(sym_idx).*;
            if (un_sym.target_scope.isNone()) return null;
            var ord: u32 = 0;
            for (sym_table.getScopeMembers(un_sym.target_scope)) |mem_idx| {
                const mem_sym = sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .field_sym) continue;
                if (ord == field_ordinal) {
                    return .{ .byte_offset = 0, .field_ty = mem_sym.type_id };
                }
                ord += 1;
            }
            return null;
        },
        else => return null,
    }
}

/// Computes the payload byte offset of `.optional_ty`, `.result_ty`, or `.enum_ty` under `target_layout`.
fn computeOptSumPayloadOffset(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_sum_ty: TypeId,
    target_layout: TargetLayout,
) u64 {
    const sum_ty = pool.unwrapUnderlyingType(raw_sum_ty);
    if (sum_ty.isError()) return 0;
    const node = pool.getNode(sum_ty);
    switch (node.tag) {
        .optional_ty => {
            const inner_lay = type_system.computeTypeLayoutWithPool(
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                target_layout,
            );
            return std.mem.alignForward(u64, 1, @max(@as(u64, inner_lay.align_bytes), 1));
        },
        .result_ty => {
            const ok_lay = type_system.computeTypeLayoutWithPool(
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                target_layout,
            );
            const err_lay = type_system.computeTypeLayoutWithPool(
                pool,
                sym_table,
                TypeId.fromInt(node.rhs),
                target_layout,
            );
            return std.mem.alignForward(u64, 1, @max(@max(ok_lay.align_bytes, err_lay.align_bytes), 1));
        },
        .enum_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            var variant_count: u32 = 0;
            var max_pay_align: u32 = 1;
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                const enum_sym = sym_table.getSymbol(sym_idx).*;
                if (!enum_sym.target_scope.isNone()) {
                    for (sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
                        const mem_sym = sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .enum_variant_sym) continue;
                        variant_count += 1;
                        if (mem_sym.type_id != .unit_ty and !mem_sym.type_id.isError()) {
                            const var_lay = type_system.computeTypeLayoutWithPool(
                                pool,
                                sym_table,
                                mem_sym.type_id,
                                target_layout,
                            );
                            if (var_lay.align_bytes > max_pay_align) max_pay_align = var_lay.align_bytes;
                        }
                    }
                }
            }
            const tag_bytes: u64 = if (variant_count <= 256) 1 else if (variant_count <= 65_536) 2 else 4;
            return std.mem.alignForward(u64, tag_bytes, max_pay_align);
        },
        else => return 0,
    }
}

/// Resolves the payload `TypeId` of variant `tag_ordinal` inside `.optional_ty`, `.result_ty`, or `.enum_ty`.
fn resolveOptVariantPayloadType(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_sum_ty: TypeId,
    tag_ordinal: u32,
) TypeId {
    const sum_ty = pool.unwrapUnderlyingType(raw_sum_ty);
    if (sum_ty.isError()) return .unit_ty;
    const node = pool.getNode(sum_ty);
    return switch (node.tag) {
        .optional_ty => if (tag_ordinal == 1) TypeId.fromInt(node.lhs) else .unit_ty,
        .result_ty => if (tag_ordinal == 0) TypeId.fromInt(node.lhs) else TypeId.fromInt(node.rhs),
        .enum_ty => blk: {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                const enum_sym = sym_table.getSymbol(sym_idx).*;
                if (!enum_sym.target_scope.isNone()) {
                    var ord: u32 = 0;
                    for (sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
                        const mem_sym = sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .enum_variant_sym) continue;
                        if (ord == tag_ordinal) break :blk mem_sym.type_id;
                        ord += 1;
                    }
                }
            }
            break :blk .unit_ty;
        },
        else => .unit_ty,
    };
}

/// Rewrites `body.calls[call_idx]` and its backing `fn_addr` instruction to target `target_def`.
fn redirectDirectCallSite(body: *MirBody, call_idx: usize, target_def: DefId) void {
    var cs = &body.calls.items[call_idx];
    cs.direct_def_id = target_def;
    cs.direct_symbol = .none;
    if (!cs.callee_val.isNone() and cs.callee_val.asInt() < body.insts.len) {
        var callee_inst = body.getInst(cs.callee_val);
        if (callee_inst.op == .fn_addr) {
            callee_inst.operands.lhs = target_def.asInt();
            callee_inst.operands.rhs = SymbolIndex.none.asInt();
            body.insts.set(cs.callee_val.asInt(), callee_inst);
        }
    }
}

/// Hashes `(raw_def, raw_sym)` canonically without `SymbolTable` slot-order dependence.
fn hashCalleeTargetCanonical(
    hasher: *std.hash.Wyhash,
    raw_def: u32,
    raw_sym: u32,
    sym_table: *const SymbolTable,
    interner: ?*const StringInterner,
) void {
    var canon_def = DefId.fromInt(raw_def);
    const sym_idx = SymbolIndex.fromInt(raw_sym);
    if (canon_def.isNone() and !sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
        const sym = sym_table.getSymbol(sym_idx).*;
        if (!sym.def_id.isNone()) {
            canon_def = sym.def_id;
        } else {
            const zero_def: u32 = DefId.NONE.asInt();
            hasher.update(std.mem.asBytes(&zero_def));
            hasher.update(&[_]u8{@intFromEnum(sym.kind)});
            const file_raw = sym.decl_span.file_id.asInt();
            hasher.update(std.mem.asBytes(&file_raw));
            hasher.update(std.mem.asBytes(&sym.member_ordinal));
            if (interner) |str_pool| {
                const text = str_pool.get(sym.name);
                const text_len: u32 = @intCast(text.len);
                hasher.update(std.mem.asBytes(&text_len));
                hasher.update(text);
            } else {
                const name_raw = sym.name.asInt();
                hasher.update(std.mem.asBytes(&name_raw));
            }
            return;
        }
    }
    const def_bits = canon_def.asInt();
    hasher.update(std.mem.asBytes(&def_bits));
}

/// Compares two callee `(DefId, SymbolIndex)` targets canonically without `SymbolTable` slot-order sensitivity.
fn isCalleeTargetEqual(
    def_a: DefId,
    sym_a: SymbolIndex,
    def_b: DefId,
    sym_b: SymbolIndex,
    sym_table: *const SymbolTable,
) bool {
    var canon_a = def_a;
    if (canon_a.isNone() and !sym_a.isNone() and sym_a.asInt() < sym_table.symbols.items.len) {
        canon_a = sym_table.getSymbol(sym_a).def_id;
    }
    var canon_b = def_b;
    if (canon_b.isNone() and !sym_b.isNone() and sym_b.asInt() < sym_table.symbols.items.len) {
        canon_b = sym_table.getSymbol(sym_b).def_id;
    }
    if (!canon_a.isNone() or !canon_b.isNone()) {
        return canon_a == canon_b;
    }
    if (sym_a == sym_b) return true;
    if (sym_a.isNone() or sym_b.isNone() or
        sym_a.asInt() >= sym_table.symbols.items.len or
        sym_b.asInt() >= sym_table.symbols.items.len)
    {
        return false;
    }
    const rec_a = sym_table.getSymbol(sym_a).*;
    const rec_b = sym_table.getSymbol(sym_b).*;
    return rec_a.kind == rec_b.kind and
        rec_a.decl_span.file_id == rec_b.decl_span.file_id and
        rec_a.member_ordinal == rec_b.member_ordinal and
        rec_a.name == rec_b.name;
}

/// Computes a 64-bit `Wyhash(0)` digest of all projected field byte offsets, interior field shapes,
/// folded constants, and resolved callees inside a specialized `MirBody` (`[CRITICAL-09]`, `[CRITICAL-12]`).
fn computeFieldOffsetsAndCalleesDigest(
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner: ?*const StringInterner,
    target_layout: TargetLayout,
) u64 {
    var hasher = std.hash.Wyhash.init(0);
    for (body.places.items) |pl| {
        if (pl.base >= body.locals.items.len or pl.proj_len == 0) continue;
        var cur_ty = pool.unwrapUnderlyingType(body.locals.items[pl.base].type_id);
        var active_downcast: ?u32 = null;
        var active_soa_field_ty: ?TypeId = null;
        for (body.projections.items[pl.proj_start .. pl.proj_start + pl.proj_len]) |proj| {
            hasher.update(&[_]u8{@backingInt(proj.kind)});
            const node = pool.getNode(cur_ty);
            switch (proj.kind) {
                .deref => {
                    active_downcast = null;
                    active_soa_field_ty = null;
                    cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                    const step_shape = computeLayoutShapeKey(pool, sym_table, cur_ty, target_layout);
                    hasher.update(std.mem.asBytes(&step_shape));
                    hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, cur_ty, target_layout))});
                },
                .index => {
                    active_downcast = null;
                    const elem_ty = if (active_soa_field_ty) |soa_f| blk: {
                        active_soa_field_ty = null;
                        break :blk soa_f;
                    } else pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                    const elem_shape = computeLayoutShapeKey(pool, sym_table, elem_ty, target_layout);
                    hasher.update(std.mem.asBytes(&elem_shape));
                    hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, elem_ty, target_layout))});
                    cur_ty = elem_ty;
                },
                .downcast => {
                    active_soa_field_ty = null;
                    active_downcast = proj.payload;
                    hasher.update(std.mem.asBytes(&proj.payload));
                },
                .field => {
                    active_soa_field_ty = null;
                    if (active_downcast) |tag_ord| {
                        active_downcast = null;
                        var total_off = computeOptSumPayloadOffset(pool, sym_table, cur_ty, target_layout);
                        var pay_ty = pool.unwrapUnderlyingType(
                            resolveOptVariantPayloadType(pool, sym_table, cur_ty, tag_ord),
                        );
                        if (proj.payload > 0) {
                            if (resolveOptCompositeFieldStep(pool, sym_table, pay_ty, proj.payload, target_layout)) |sub| {
                                total_off += sub.byte_offset;
                                pay_ty = pool.unwrapUnderlyingType(sub.field_ty);
                            }
                        }
                        hasher.update(std.mem.asBytes(&total_off));
                        const pay_shape = computeLayoutShapeKey(pool, sym_table, pay_ty, target_layout);
                        hasher.update(std.mem.asBytes(&pay_shape));
                        hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, pay_ty, target_layout))});
                        cur_ty = pay_ty;
                    } else if (resolveOptCompositeFieldStep(pool, sym_table, cur_ty, proj.payload, target_layout)) |step| {
                        hasher.update(std.mem.asBytes(&step.byte_offset));
                        cur_ty = pool.unwrapUnderlyingType(step.field_ty);
                        const field_shape = computeLayoutShapeKey(pool, sym_table, cur_ty, target_layout);
                        hasher.update(std.mem.asBytes(&field_shape));
                        hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, cur_ty, target_layout))});
                    } else {
                        hasher.update(std.mem.asBytes(&proj.payload));
                    }
                },
                .soa_elem => {
                    active_downcast = null;
                    const base_elem_ty = TypeId.fromInt(node.lhs);
                    if (resolveOptCompositeFieldStep(pool, sym_table, base_elem_ty, proj.payload, target_layout)) |step| {
                        hasher.update(std.mem.asBytes(&step.byte_offset));
                        const col_ty = pool.unwrapUnderlyingType(step.field_ty);
                        active_soa_field_ty = col_ty;
                        const col_shape = computeLayoutShapeKey(pool, sym_table, col_ty, target_layout);
                        hasher.update(std.mem.asBytes(&col_shape));
                        hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, col_ty, target_layout))});
                    } else {
                        active_soa_field_ty = null;
                        hasher.update(std.mem.asBytes(&proj.payload));
                    }
                },
                .slice_len => {
                    active_downcast = null;
                    active_soa_field_ty = null;
                    cur_ty = .usize_ty;
                },
            }
        }
    }
    for (body.consts.items) |mc| {
        hasher.update(&[_]u8{@intFromEnum(mc)});
        switch (mc) {
            .unit_val => {},
            .bool_val => |bv| hasher.update(&[_]u8{@intFromBool(bv)}),
            .char_val => |cv| hasher.update(std.mem.asBytes(&cv)),
            .int_val => |iv| hasher.update(std.mem.asBytes(&iv)),
            .float_val => |fv| {
                const flt_bits: u64 = @bitCast(fv);
                hasher.update(std.mem.asBytes(&flt_bits));
            },
            .str_val => |sv| {
                if (interner) |str_pool| {
                    const str_bytes = str_pool.get(sv);
                    const str_len: u32 = @intCast(str_bytes.len);
                    hasher.update(std.mem.asBytes(&str_len));
                    hasher.update(str_bytes);
                } else {
                    hasher.update(std.mem.asBytes(&sv));
                }
            },
            .bytes_val => |bv| {
                if (interner) |str_pool| {
                    const raw_bytes = str_pool.get(bv);
                    const raw_len: u32 = @intCast(raw_bytes.len);
                    hasher.update(std.mem.asBytes(&raw_len));
                    hasher.update(raw_bytes);
                } else {
                    hasher.update(std.mem.asBytes(&bv));
                }
            },
        }
    }
    for (body.calls.items) |cs| {
        hashCalleeTargetCanonical(
            &hasher,
            cs.direct_def_id.asInt(),
            cs.direct_symbol.asInt(),
            sym_table,
            interner,
        );
        const ret_shape = computeLayoutShapeKey(pool, sym_table, cs.ret_ty, target_layout);
        hasher.update(std.mem.asBytes(&ret_shape));
        hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, cs.ret_ty, target_layout))});
        for (0..cs.args_len) |arg_i| {
            const arg_mode = body.call_arg_modes.items[cs.modes_start + arg_i];
            const word = body.extra_args.items[cs.args_start + arg_i];
            const arg_ty = if (arg_mode == .let_mode or arg_mode == .sink_mode)
                body.getInst(MirValueId.fromInt(word)).type_id
            else
                inferPlaceTypeInBody(body, PlaceId.fromInt(word), pool, sym_table);
            const arg_shape = computeLayoutShapeKey(pool, sym_table, arg_ty, target_layout);
            hasher.update(std.mem.asBytes(&arg_shape));
            hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, arg_ty, target_layout))});
        }
    }
    return hasher.final();
}

/// Worklist item in `runPassD5MonomorphizeAndPromote`.
const MonoWorkItem = struct {
    /// Index of caller body in `out_bodies`.
    caller_idx: usize,
    /// Index of `MirCallSite` inside `out_bodies[caller_idx].calls`.
    call_idx: usize,
    /// Specialization chain depth (`<= MAX_MONOMORPH_DEPTH`).
    depth: u32,
};

/// Sound deduplication record for `LayoutShapeKey`-equivalent monomorphizations (`[CRITICAL-09]`, `[CRITICAL-12]`).
const MonoDedupEntry = struct {
    /// Originating generic template `(DefId, SymbolIndex)` packed 64-bit key.
    template_key: u64,
    /// Index of canonical specialized `MirBody` inside `concrete_bodies`.
    specialized_body_idx: usize,
    /// Assigned synthetic `DefId` of the specialized `MirBody`.
    specialized_def_id: DefId,
    /// Owned slice of exact concrete `TypeId`s bound to `ordered_vars`.
    param_type_ids: []TypeId,
    /// Per-parameter `(LayoutShapeKey, OpSemanticsTag)` signature digest + field-offset/callee digest.
    shape_digest: u64,
    /// Owned slice of per-parameter `LayoutShapeKey`s for exact collision verification.
    param_shapes: []LayoutShapeKey,
    /// Owned slice of per-parameter `OpSemanticsTag`s for exact collision verification.
    param_semantics: []OpSemanticsTag,
    /// Exact field-offset and resolved-callee digest.
    offsets_and_callees: u64,
};

/// Runs Tarjan's Strongly Connected Components (SCC) algorithm bottom-up over `bodies` to infer
/// `is_contextless = true` (`DR-13` §5.2) and propagate `is_callee_contextless` onto all callers (`V6`).
fn promoteContextlessTarjanScc(
    allocator: std.mem.Allocator,
    bodies: []MirBody,
    sym_table: *const SymbolTable,
) !void {
    const count = bodies.len;
    if (count == 0) return;

    var body_map = try BodyDefMap.initFromBodies(allocator, bodies);
    defer body_map.deinit(allocator);

    const index_arr = try allocator.alloc(u32, count);
    defer allocator.free(index_arr);
    @memset(index_arr, mir.NONE_U32);

    const lowlink = try allocator.alloc(u32, count);
    defer allocator.free(lowlink);
    @memset(lowlink, mir.NONE_U32);

    const is_on_stack = try allocator.alloc(bool, count);
    defer allocator.free(is_on_stack);
    @memset(is_on_stack, false);

    var tarjan_stack: std.ArrayListUnmanaged(usize) = .empty;
    defer tarjan_stack.deinit(allocator);

    const SccCtx = struct {
        alloc: std.mem.Allocator,
        b_slice: []MirBody,
        b_map: *const BodyDefMap,
        syms: *const SymbolTable,
        idx_arr: []u32,
        low_arr: []u32,
        in_stk: []bool,
        stk: *std.ArrayListUnmanaged(usize),
        next_dfs: u32 = 0,

        fn strongConnect(ctx: *@This(), v_idx: usize) !void {
            ctx.idx_arr[v_idx] = ctx.next_dfs;
            ctx.low_arr[v_idx] = ctx.next_dfs;
            ctx.next_dfs += 1;
            try ctx.stk.append(ctx.alloc, v_idx);
            ctx.in_stk[v_idx] = true;

            for (ctx.b_slice[v_idx].blocks.items) |bb| {
                if (bb.terminator.kind != .call) continue;
                const cs = ctx.b_slice[v_idx].calls.items[bb.terminator.cond_or_val];
                const w_idx = ctx.b_map.lookup(cs.direct_def_id, cs.direct_symbol, ctx.syms) orelse
                    continue;
                if (ctx.idx_arr[w_idx] == mir.NONE_U32) {
                    try ctx.strongConnect(w_idx);
                    ctx.low_arr[v_idx] = @min(ctx.low_arr[v_idx], ctx.low_arr[w_idx]);
                } else if (ctx.in_stk[w_idx]) {
                    ctx.low_arr[v_idx] = @min(ctx.low_arr[v_idx], ctx.idx_arr[w_idx]);
                }
            }

            if (ctx.low_arr[v_idx] == ctx.idx_arr[v_idx]) {
                // Pop complete SCC; children SCCs are already promoted in bottom-up topological order:
                var scc_members: std.ArrayListUnmanaged(usize) = .empty;
                defer scc_members.deinit(ctx.alloc);
                while (true) {
                    const w_idx = ctx.stk.pop().?;
                    ctx.in_stk[w_idx] = false;
                    try scc_members.append(ctx.alloc, w_idx);
                    if (w_idx == v_idx) break;
                }

                var is_promotable = true;
                for (scc_members.items) |m_idx| {
                    for (ctx.b_slice[m_idx].blocks.items) |bb| {
                        if (bb.terminator.kind != .call) continue;
                        const cs = ctx.b_slice[m_idx].calls.items[bb.terminator.cond_or_val];
                        if (cs.is_callee_contextless) continue;
                        if (ctx.b_map.lookup(cs.direct_def_id, cs.direct_symbol, ctx.syms)) |cal_idx| {
                            var is_in_same_scc = false;
                            for (scc_members.items) |other| {
                                if (other == cal_idx) {
                                    is_in_same_scc = true;
                                    break;
                                }
                            }
                            if (!is_in_same_scc and !ctx.b_slice[cal_idx].is_contextless) {
                                is_promotable = false;
                                break;
                            }
                        } else {
                            // Indirect call or external FFI prototype without `contextless` proof:
                            is_promotable = false;
                            break;
                        }
                    }
                    if (!is_promotable) break;
                }

                if (is_promotable) {
                    for (scc_members.items) |m_idx| {
                        ctx.b_slice[m_idx].is_contextless = true;
                    }
                }
            }
        }
    };

    var scc_ctx = SccCtx{
        .alloc = allocator,
        .b_slice = bodies,
        .b_map = &body_map,
        .syms = sym_table,
        .idx_arr = index_arr,
        .low_arr = lowlink,
        .in_stk = is_on_stack,
        .stk = &tarjan_stack,
    };

    for (0..count) |i| {
        if (scc_ctx.idx_arr[i] == mir.NONE_U32) {
            try scc_ctx.strongConnect(i);
        }
    }

    // Propagate promoted `is_contextless` onto every caller's `MirCallSite.is_callee_contextless` (`V6`):
    for (bodies) |*caller| {
        for (caller.calls.items) |*cs| {
            if (body_map.lookup(cs.direct_def_id, cs.direct_symbol, sym_table)) |cal_idx| {
                if (bodies[cal_idx].is_contextless) {
                    cs.is_callee_contextless = true;
                }
            }
        }
    }
}

/// Pass `D5`: FIFO worklist monomorphization (`MAX_MONOMORPH_DEPTH = 64`, `MAX_MONOMORPH_INSTANCES = 65,536`),
/// sound `LayoutShapeKey` deduplication (`[CRITICAL-09]`, `[CRITICAL-12]`), and Tarjan SCC `contextless` promotion.
fn runPassD5MonomorphizeAndPromote(
    allocator: std.mem.Allocator,
    in_bodies: *std.ArrayListUnmanaged(MirBody),
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *StringInterner,
    config: MirOptConfig,
    sink: ?*DiagnosticSink,
    dedup_merged_out: *u32,
) !void {
    var templates: std.ArrayListUnmanaged(MirBody) = .empty;
    defer {
        for (templates.items) |*tb| tb.deinit();
        templates.deinit(allocator);
    }

    var concrete_bodies: std.ArrayListUnmanaged(MirBody) = .empty;
    errdefer {
        for (concrete_bodies.items) |*cb| cb.deinit();
        concrete_bodies.deinit(allocator);
    }

    for (in_bodies.items) |*b_ptr| {
        if (isComptimeOnlyBody(b_ptr, sym_table, config)) {
            b_ptr.deinit();
            continue;
        }
        if (isGenericTemplateBody(b_ptr, pool, sym_table)) {
            try templates.append(allocator, b_ptr.*);
        } else {
            try concrete_bodies.append(allocator, b_ptr.*);
        }
    }
    in_bodies.clearRetainingCapacity();

    if (templates.items.len > 0) {
        var tmpl_map = try BodyDefMap.initFromBodies(allocator, templates.items);
        defer tmpl_map.deinit(allocator);

        var worklist: std.ArrayListUnmanaged(MonoWorkItem) = .empty;
        defer worklist.deinit(allocator);

        var dedup_entries: std.ArrayListUnmanaged(MonoDedupEntry) = .empty;
        defer {
            for (dedup_entries.items) |de| {
                if (de.param_type_ids.len > 0) allocator.free(de.param_type_ids);
                if (de.param_shapes.len > 0) allocator.free(de.param_shapes);
                if (de.param_semantics.len > 0) allocator.free(de.param_semantics);
            }
            dedup_entries.deinit(allocator);
        }

        // Seed worklist with all generic calls from concrete root bodies:
        for (concrete_bodies.items, 0..) |cb, c_idx| {
            for (cb.blocks.items) |bb| {
                if (bb.terminator.kind != .call) continue;
                const call_idx = bb.terminator.cond_or_val;
                const cs = cb.calls.items[call_idx];
                if (tmpl_map.lookup(cs.direct_def_id, cs.direct_symbol, sym_table) != null) {
                    try worklist.append(allocator, .{ .caller_idx = c_idx, .call_idx = call_idx, .depth = 1 });
                }
            }
        }

        var next_synth_def_raw: u32 = 0x7000_0000;
        var instance_count: u32 = 0;
        var q_head: usize = 0;

        while (q_head < worklist.items.len) : (q_head += 1) {
            const item = worklist.items[q_head];
            if (item.depth > MAX_MONOMORPH_DEPTH) {
                const cs = concrete_bodies.items[item.caller_idx].calls.items[item.call_idx];
                const span = resolveOptDiagSpan(
                    concrete_bodies.items[item.caller_idx].file_id,
                    cs.origin_token,
                    cs.direct_symbol,
                    sym_table,
                    config,
                );
                try emitOptDiagnostic(
                    sink,
                    .e0508_comptime_resource_limit_exceeded,
                    .err,
                    span,
                    "generic monomorphization depth exceeded `MAX_MONOMORPH_DEPTH` (64)",
                    "polymorphic recursion limit exceeded here",
                );
                break;
            }

            const cs_snapshot = concrete_bodies.items[item.caller_idx].calls.items[item.call_idx];
            const tmpl_idx = tmpl_map.lookup(
                cs_snapshot.direct_def_id,
                cs_snapshot.direct_symbol,
                sym_table,
            ) orelse continue;
            const tmpl = &templates.items[tmpl_idx];

            // Unify template parameter & return types with concrete caller argument & return types:
            var subst: std.AutoHashMapUnmanaged(u32, TypeId) = .empty;
            defer subst.deinit(allocator);
            var ordered_vars: std.ArrayListUnmanaged(u32) = .empty;
            defer ordered_vars.deinit(allocator);

            const caller_ref = &concrete_bodies.items[item.caller_idx];
            const arg_n = @min(@as(usize, cs_snapshot.args_len), tmpl.param_count);
            for (0..arg_n) |ai| {
                const tmpl_p_ty = tmpl.locals.items[1 + ai].type_id;
                const mode = caller_ref.call_arg_modes.items[cs_snapshot.modes_start + ai];
                const word = caller_ref.extra_args.items[cs_snapshot.args_start + ai];
                const caller_arg_ty = if (mode == .let_mode or mode == .sink_mode)
                    caller_ref.getInst(MirValueId.fromInt(word)).type_id
                else
                    inferPlaceTypeInBody(caller_ref, PlaceId.fromInt(word), pool, sym_table);
                try unifyTemplateTypeBinding(
                    allocator,
                    pool,
                    tmpl_p_ty,
                    caller_arg_ty,
                    &subst,
                    &ordered_vars,
                    0,
                );
            }
            try unifyTemplateTypeBinding(
                allocator,
                pool,
                tmpl.ret_ty,
                cs_snapshot.ret_ty,
                &subst,
                &ordered_vars,
                0,
            );

            // Clone and specialize `tmpl`:
            var spec = try tmpl.clone(allocator);
            errdefer spec.deinit();

            spec.ret_ty = try substituteMirType(allocator, pool, spec.ret_ty, &subst, 0);
            for (spec.locals.items) |*loc| {
                loc.type_id = try substituteMirType(allocator, pool, loc.type_id, &subst, 0);
            }
            for (0..spec.insts.len) |inst_i| {
                var inst = spec.insts.get(inst_i);
                inst.type_id = try substituteMirType(allocator, pool, inst.type_id, &subst, 0);
                if (inst.op == .fn_addr and inst.operands.rhs < sym_table.symbols.items.len) {
                    const ref_sym = sym_table.getSymbol(SymbolIndex.fromInt(inst.operands.rhs)).*;
                    if (ref_sym.kind == .const_param_sym) {
                        const len_key = try pool.internSymbolicArray(.unit_ty, ref_sym.name, false);
                        if (subst.get(len_key.toU32())) |bound_len_ty| {
                            const bound_node = pool.getNode(bound_len_ty);
                            if (bound_node.tag == .array_ty and
                                (bound_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) == 0)
                            {
                                const c_idx = try spec.appendConst(.{ .int_val = @as(i128, bound_node.rhs) });
                                inst = .{
                                    .op = .const_scalar,
                                    .flags = .{},
                                    .type_id = inst.type_id,
                                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                                };
                            }
                        }
                    }
                } else if (inst.op == .intrinsic_op and inst.operands.rhs == 0) {
                    const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                    if (ikind == .size_of or ikind == .align_of or ikind == .type_name) {
                        const subst_ty = try substituteMirType(
                            allocator,
                            pool,
                            TypeId.fromInt(inst.operands.lhs),
                            &subst,
                            0,
                        );
                        inst.operands.lhs = subst_ty.asInt();
                        if (!subst_ty.isError() and !hasGenericVarsInType(pool, subst_ty)) {
                            switch (ikind) {
                                .size_of => {
                                    const lay = type_system.computeTypeLayoutWithPool(
                                        pool,
                                        sym_table,
                                        subst_ty,
                                        config.target_layout,
                                    );
                                    if (lay.is_sized) {
                                        const c_idx = try spec.appendConst(.{ .int_val = @as(i128, lay.byte_size) });
                                        inst = .{
                                            .op = .const_scalar,
                                            .flags = .{},
                                            .type_id = inst.type_id,
                                            .operands = .{ .lhs = c_idx, .rhs = 0 },
                                        };
                                    }
                                },
                                .align_of => {
                                    const lay = type_system.computeTypeLayoutWithPool(
                                        pool,
                                        sym_table,
                                        subst_ty,
                                        config.target_layout,
                                    );
                                    const c_idx = try spec.appendConst(.{ .int_val = @as(i128, lay.align_bytes) });
                                    inst = .{
                                        .op = .const_scalar,
                                        .flags = .{},
                                        .type_id = inst.type_id,
                                        .operands = .{ .lhs = c_idx, .rhs = 0 },
                                    };
                                },
                                .type_name => {
                                    var type_name_buf: [512]u8 = undefined;
                                    const formatted_name = pool.formatType(subst_ty, sym_table, &type_name_buf);
                                    const sym_id = try interner.intern(formatted_name);
                                    const c_idx = try spec.appendConst(.{ .str_val = sym_id });
                                    inst = .{
                                        .op = .const_scalar,
                                        .flags = .{},
                                        .type_id = inst.type_id,
                                        .operands = .{ .lhs = c_idx, .rhs = 0 },
                                    };
                                },
                                else => {},
                            }
                        }
                    }
                }
                spec.insts.set(inst_i, inst);
            }
            // Second pass over `spec.insts` now that operand `type_id`s are concrete: adapt `BinOpKind` / `UnaryOpKind`:
            for (0..spec.insts.len) |inst_i| {
                var inst = spec.insts.get(inst_i);
                if (inst.op == .bin_op and inst.operands.lhs < spec.insts.len) {
                    const op_ty = spec.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id;
                    const sem = classifyOpSemantics(pool, op_ty, config.target_layout);
                    const bkind: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                    inst.aux_u16 = @backingInt(specializeBinOpForSemantics(bkind, sem));
                    spec.insts.set(inst_i, inst);
                } else if (inst.op == .unary_op and inst.operands.lhs < spec.insts.len) {
                    const op_ty = spec.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id;
                    const sem = classifyOpSemantics(pool, op_ty, config.target_layout);
                    const ukind: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                    inst.aux_u16 = @backingInt(specializeUnaryOpForSemantics(ukind, sem));
                    spec.insts.set(inst_i, inst);
                }
            }
            var has_nested_generic_call = false;
            for (spec.calls.items) |*sub_cs| {
                sub_cs.ret_ty = try substituteMirType(allocator, pool, sub_cs.ret_ty, &subst, 0);
                if (tmpl_map.lookup(sub_cs.direct_def_id, sub_cs.direct_symbol, sym_table) != null) {
                    has_nested_generic_call = true;
                }
            }

            // Run `D2`–`D4` on `spec` so specialized body matches module post-strip invariants:
            try runPassD2ReachableConstFold(allocator, &spec, pool, sym_table, config, sink);
            try runPassD3StripGhostInstructions(allocator, &spec);
            try runPassD4BranchFoldAndPrune(allocator, &spec);

            // Compute sound `[CRITICAL-09]` / `[CRITICAL-12]` deduplication signature:
            const p_type_ids = try allocator.alloc(TypeId, ordered_vars.items.len);
            errdefer allocator.free(p_type_ids);
            const p_shapes = try allocator.alloc(LayoutShapeKey, ordered_vars.items.len);
            errdefer allocator.free(p_shapes);
            const p_sems = try allocator.alloc(OpSemanticsTag, ordered_vars.items.len);
            errdefer allocator.free(p_sems);

            var shape_hasher = std.hash.Wyhash.init(0);
            const tmpl_key: u64 = (@as(u64, tmpl.def_id.asInt()) << 32) | @as(u64, tmpl.symbol_index.asInt());
            shape_hasher.update(std.mem.asBytes(&tmpl_key));
            for (ordered_vars.items, 0..) |var_raw, vi| {
                const conc_ty = subst.get(var_raw) orelse .unit_ty;
                p_type_ids[vi] = conc_ty;
                p_shapes[vi] = computeLayoutShapeKey(pool, sym_table, conc_ty, config.target_layout);
                p_sems[vi] = classifyOpSemantics(pool, conc_ty, config.target_layout);
                shape_hasher.update(std.mem.asBytes(&p_shapes[vi]));
                shape_hasher.update(&[_]u8{@backingInt(p_sems[vi])});
            }
            const offsets_callees = computeFieldOffsetsAndCalleesDigest(
                &spec,
                pool,
                sym_table,
                interner,
                config.target_layout,
            );
            shape_hasher.update(std.mem.asBytes(&offsets_callees));
            const shape_digest = shape_hasher.final();

            // Check if an existing monomorphization matches all `[CRITICAL-09]` / `[CRITICAL-12]` soundness criteria:
            var matched_def: ?DefId = null;
            for (dedup_entries.items) |entry| {
                if (entry.template_key != tmpl_key or entry.param_type_ids.len != p_type_ids.len) {
                    continue;
                }
                var is_exact_type_match = true;
                for (entry.param_type_ids, p_type_ids) |ty_a, ty_b| {
                    if (ty_a != ty_b) {
                        is_exact_type_match = false;
                        break;
                    }
                }
                if (is_exact_type_match) {
                    matched_def = entry.specialized_def_id;
                    break;
                }
                if (has_nested_generic_call) continue;
                if (entry.shape_digest != shape_digest or
                    entry.offsets_and_callees != offsets_callees or
                    entry.param_shapes.len != p_shapes.len)
                {
                    continue;
                }
                var is_all_matching = true;
                for (entry.param_shapes, p_shapes, entry.param_semantics, p_sems) |shape_a, shape_b, sem_a, sem_b| {
                    if (!shape_a.isEqual(shape_b) or sem_a != sem_b) {
                        is_all_matching = false;
                        break;
                    }
                }
                if (is_all_matching and try isMirBodyStructurallyEqual(
                    allocator,
                    &concrete_bodies.items[entry.specialized_body_idx],
                    &spec,
                    pool,
                    sym_table,
                    config.target_layout,
                )) {
                    matched_def = entry.specialized_def_id;
                    break;
                }
            }

            if (matched_def) |canon_def| {
                spec.deinit();
                allocator.free(p_type_ids);
                allocator.free(p_shapes);
                allocator.free(p_sems);
                redirectDirectCallSite(&concrete_bodies.items[item.caller_idx], item.call_idx, canon_def);
                dedup_merged_out.* += 1;
                continue;
            }

            instance_count += 1;
            if (instance_count > MAX_MONOMORPH_INSTANCES) {
                spec.deinit();
                allocator.free(p_type_ids);
                allocator.free(p_shapes);
                allocator.free(p_sems);
                const span = resolveOptDiagSpan(
                    concrete_bodies.items[item.caller_idx].file_id,
                    cs_snapshot.origin_token,
                    cs_snapshot.direct_symbol,
                    sym_table,
                    config,
                );
                try emitOptDiagnostic(
                    sink,
                    .e0508_comptime_resource_limit_exceeded,
                    .err,
                    span,
                    "generic monomorphization count exceeded `MAX_MONOMORPH_INSTANCES` (65,536)",
                    "monomorphization instance cap exceeded here",
                );
                break;
            }

            const spec_def = DefId.fromInt(next_synth_def_raw);
            next_synth_def_raw += 1;
            spec.def_id = spec_def;
            spec.symbol_index = .none;
            var name_buf: [128]u8 = undefined;
            const base_name = if (tmpl.name != .empty) interner.get(tmpl.name) else "anon";
            const mangled = std.fmt.bufPrint(&name_buf, "{s}$mono{d}", .{ base_name, instance_count }) catch base_name;
            spec.name = try interner.intern(mangled);

            const new_body_idx = concrete_bodies.items.len;
            try concrete_bodies.append(allocator, spec);
            try dedup_entries.append(allocator, .{
                .template_key = tmpl_key,
                .specialized_body_idx = new_body_idx,
                .specialized_def_id = spec_def,
                .param_type_ids = p_type_ids,
                .shape_digest = shape_digest,
                .param_shapes = p_shapes,
                .param_semantics = p_sems,
                .offsets_and_callees = offsets_callees,
            });

            redirectDirectCallSite(&concrete_bodies.items[item.caller_idx], item.call_idx, spec_def);

            // Enqueue any nested generic calls inside the newly specialized body:
            for (concrete_bodies.items[new_body_idx].blocks.items) |sub_bb| {
                if (sub_bb.terminator.kind != .call) continue;
                const sub_call_idx = sub_bb.terminator.cond_or_val;
                const sub_cs = concrete_bodies.items[new_body_idx].calls.items[sub_call_idx];
                if (tmpl_map.lookup(sub_cs.direct_def_id, sub_cs.direct_symbol, sym_table) != null) {
                    try worklist.append(allocator, .{
                        .caller_idx = new_body_idx,
                        .call_idx = sub_call_idx,
                        .depth = item.depth + 1,
                    });
                }
            }
        }

        // Post-resolution deduplication pass for specializations that originally had nested generic calls:
        if (dedup_entries.items.len > 1) {
            const is_removed_entry = try allocator.alloc(bool, concrete_bodies.items.len);
            defer allocator.free(is_removed_entry);
            @memset(is_removed_entry, false);

            var has_merged_nested = true;
            while (has_merged_nested) {
                has_merged_nested = false;
                var mono_remap: std.AutoHashMapUnmanaged(u32, DefId) = .empty;
                defer mono_remap.deinit(allocator);

                for (0..dedup_entries.items.len) |i| {
                    const entry_a = dedup_entries.items[i];
                    if (is_removed_entry[entry_a.specialized_body_idx]) continue;
                    const digest_a = computeFieldOffsetsAndCalleesDigest(
                        &concrete_bodies.items[entry_a.specialized_body_idx],
                        pool,
                        sym_table,
                        interner,
                        config.target_layout,
                    );
                    for ((i + 1)..dedup_entries.items.len) |j| {
                        const entry_b = dedup_entries.items[j];
                        if (is_removed_entry[entry_b.specialized_body_idx]) continue;
                        if (entry_a.template_key != entry_b.template_key or
                            entry_a.param_shapes.len != entry_b.param_shapes.len)
                        {
                            continue;
                        }
                        var is_all_matching = true;
                        for (
                            entry_a.param_shapes,
                            entry_b.param_shapes,
                            entry_a.param_semantics,
                            entry_b.param_semantics,
                        ) |shape_a, shape_b, sem_a, sem_b| {
                            if (!shape_a.isEqual(shape_b) or sem_a != sem_b) {
                                is_all_matching = false;
                                break;
                            }
                        }
                        if (!is_all_matching) continue;
                        const digest_b = computeFieldOffsetsAndCalleesDigest(
                            &concrete_bodies.items[entry_b.specialized_body_idx],
                            pool,
                            sym_table,
                            interner,
                            config.target_layout,
                        );
                        if (digest_a != digest_b) continue;
                        if (try isMirBodyStructurallyEqual(
                            allocator,
                            &concrete_bodies.items[entry_a.specialized_body_idx],
                            &concrete_bodies.items[entry_b.specialized_body_idx],
                            pool,
                            sym_table,
                            config.target_layout,
                        )) {
                            try mono_remap.put(allocator, entry_b.specialized_def_id.asInt(), entry_a.specialized_def_id);
                            is_removed_entry[entry_b.specialized_body_idx] = true;
                            dedup_merged_out.* += 1;
                            has_merged_nested = true;
                        }
                    }
                }

                if (mono_remap.count() > 0) {
                    for (concrete_bodies.items, 0..) |*cb_ptr, cb_idx| {
                        if (is_removed_entry[cb_idx]) continue;
                        for (cb_ptr.calls.items) |*cs| {
                            if (mono_remap.get(cs.direct_def_id.asInt())) |mapped_def| {
                                cs.direct_def_id = mapped_def;
                            }
                        }
                        for (0..cb_ptr.insts.len) |inst_i| {
                            var inst = cb_ptr.insts.get(inst_i);
                            if (inst.op == .fn_addr) {
                                if (mono_remap.get(inst.operands.lhs)) |mapped_def| {
                                    inst.operands.lhs = mapped_def.asInt();
                                    cb_ptr.insts.set(inst_i, inst);
                                }
                            }
                        }
                    }
                }
            }

            var write_idx: usize = 0;
            for (concrete_bodies.items, 0..) |*cb_ptr, read_idx| {
                if (is_removed_entry[read_idx]) {
                    cb_ptr.deinit();
                } else {
                    concrete_bodies.items[write_idx] = cb_ptr.*;
                    write_idx += 1;
                }
            }
            concrete_bodies.items.len = write_idx;
        }
    }

    try promoteContextlessTarjanScc(allocator, concrete_bodies.items, sym_table);

    in_bodies.deinit(allocator);
    in_bodies.* = concrete_bodies;
}

// ------ Pass `R1`: Bounded Cost-Model Inliner (`W0501`) -------

/// Estimates the post-strip execution cost of `body` (`non_const_insts + 3 * direct_or_indirect_calls`).
fn estimateInlineBodyCost(body: *const MirBody) u32 {
    var cost: u32 = 0;
    for (body.blocks.items, 0..) |bb, bb_i| {
        for (body.getBlockInsts(MirBlockId.fromInt(@intCast(bb_i)))) |inst_val| {
            const op = body.getInst(inst_val).op;
            if (op == .const_scalar or op == .copy_val or op == .fn_addr) continue;
            cost += 1;
        }
        if (bb.terminator.kind == .call) cost += 3;
    }
    return cost;
}

/// Pass `R1`: Inlines small functions (`<= AUTO_INLINE_BUDGET`) and `@inline` functions (`<= INLINE_HINT_BUDGET`),
/// emitting `W0501` (`w0501_inlining_budget_exceeded`) when an explicit `@inline` function exceeds budget or recurses.
fn runPassR1CostModelInliner(
    allocator: std.mem.Allocator,
    bodies: []MirBody,
    sym_table: *const SymbolTable,
    config: MirOptConfig,
    sink: ?*DiagnosticSink,
) !void {
    const directives = try allocator.alloc(InlineDirective, bodies.len);
    defer allocator.free(directives);
    for (bodies, 0..) |cand, idx| {
        directives[idx] = extractInlineDirective(cand.def_id, cand.symbol_index, sym_table, config);
    }

    var body_map = try BodyDefMap.initFromBodies(allocator, bodies);
    defer body_map.deinit(allocator);

    var warned_w0501: std.AutoHashMapUnmanaged(u64, void) = .empty;
    defer warned_w0501.deinit(allocator);

    for (0..bodies.len) |caller_idx| {
        var rounds: usize = 0;
        while (rounds < 16) : (rounds += 1) {
            var has_spliced_one = false;
            for (0..bodies[caller_idx].blocks.items.len) |bb_i| {
                const term = bodies[caller_idx].blocks.items[bb_i].terminator;
                if (term.kind != .call) continue;
                const cs = bodies[caller_idx].calls.items[term.cond_or_val];
                const callee_idx = body_map.lookup(cs.direct_def_id, cs.direct_symbol, sym_table) orelse
                    continue;
                const dir = directives[callee_idx];
                if (dir == .inline_never) continue;

                const is_recursive = (callee_idx == caller_idx) or
                    try hasCallGraphPath(allocator, bodies, &body_map, callee_idx, caller_idx, sym_table);
                const cost = estimateInlineBodyCost(&bodies[callee_idx]);
                const budget: u32 = switch (dir) {
                    .inline_always => MAX_CALLER_INLINE_INSTS,
                    .inline_hint => INLINE_HINT_BUDGET,
                    .default_mode => AUTO_INLINE_BUDGET,
                    .inline_never => 0,
                };
                const has_caller_overflow = bodies[caller_idx].insts.len + bodies[callee_idx].insts.len >
                    MAX_CALLER_INLINE_INSTS;

                if (is_recursive or cost > budget or has_caller_overflow) {
                    if (dir == .inline_hint) {
                        const warn_key = (@as(u64, @intCast(caller_idx)) << 32) | @as(u64, @intCast(callee_idx));
                        if (!warned_w0501.contains(warn_key)) {
                            try warned_w0501.put(allocator, warn_key, {});
                            const span = resolveOptDiagSpan(
                                bodies[caller_idx].file_id,
                                cs.origin_token,
                                cs.direct_symbol,
                                sym_table,
                                config,
                            );
                            try emitOptDiagnostic(
                                sink,
                                .w0501_inlining_budget_exceeded,
                                .warning,
                                span,
                                "explicit `@inline` function exceeded inlining cost budget or recursion check",
                                "`@inline` budget exceeded here",
                            );
                        }
                    }
                    continue;
                }

                var callee_snapshot = try bodies[callee_idx].clone(allocator);
                defer callee_snapshot.deinit();
                spliceDirectCallSite(allocator, &bodies[caller_idx], @intCast(bb_i), &callee_snapshot) catch |err| switch (err) {
                    error.ProjectionDepthExceeded => {
                        if (dir == .inline_hint) {
                            const warn_key = (@as(u64, @intCast(caller_idx)) << 32) | @as(u64, @intCast(callee_idx));
                            if (!warned_w0501.contains(warn_key)) {
                                try warned_w0501.put(allocator, warn_key, {});
                                const span = resolveOptDiagSpan(
                                    bodies[caller_idx].file_id,
                                    cs.origin_token,
                                    cs.direct_symbol,
                                    sym_table,
                                    config,
                                );
                                try emitOptDiagnostic(
                                    sink,
                                    .w0501_inlining_budget_exceeded,
                                    .warning,
                                    span,
                                    "explicit `@inline` function exceeded `MAX_PLACE_PROJ_DEPTH` (64); keeping call",
                                    "`@inline` projection depth exceeded here",
                                );
                            }
                        }
                        continue;
                    },
                    else => return err,
                };
                has_spliced_one = true;
                break;
            }
            if (!has_spliced_one) break;
        }
    }
}

// --------- Pass `R2`: SROA (`Place`-to-SSA Promotion) ---------

/// Composite field breakdown for non-address-taken small struct/tuple locals in `R2`.
const SroaCompositePlan = struct {
    /// Starting SSA `var_id` inside `sroa_var_types`.
    first_var_id: u32,
    /// Number of scalar fields (`1 .. MAX_SROA_COMPOSITE_FIELDS`).
    field_count: u8,
    /// `true` for `.struct_agg`, `false` for `.tuple_agg`.
    is_struct: bool,
};

/// Returns `true` if `ty` can live directly in an SSA register without stack place aliasing.
fn isSroaRegisterType(pool: *const InternPool, raw_ty: TypeId) bool {
    const ty = pool.unwrapUnderlyingType(raw_ty);
    if (ty.isError()) return false;
    switch (ty) {
        .unit_ty,
        .bool_ty,
        .i8_ty,
        .i16_ty,
        .i32_ty,
        .i64_ty,
        .i128_ty,
        .isize_ty,
        .u8_ty,
        .u16_ty,
        .u32_ty,
        .u64_ty,
        .u128_ty,
        .usize_ty,
        .f32_ty,
        .f64_ty,
        .char_ty,
        .str_ty,
        => return true,
        else => {},
    }
    const tag = pool.getNode(ty).tag;
    return tag == .ref_ty or tag == .mut_ref_ty or tag == .raw_ptr_ty or tag == .fn_ty or tag == .bit_field_ty;
}

/// Extracts scalar field `TypeId`s if `raw_ty` is a small struct/tuple (`<= MAX_SROA_COMPOSITE_FIELDS`).
fn decomposeSmallCompositeFields(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_ty: TypeId,
    out_fields: *[MAX_SROA_COMPOSITE_FIELDS]TypeId,
) ?struct { count: u8, is_struct: bool } {
    const ty = pool.unwrapUnderlyingType(raw_ty);
    const node = pool.getNode(ty);
    if (node.tag == .tuple_ty) {
        const elems = pool.getTupleElements(ty);
        if (elems.len == 0 or elems.len > MAX_SROA_COMPOSITE_FIELDS) return null;
        for (elems, 0..) |eraw, i| {
            const f_ty = pool.unwrapUnderlyingType(TypeId.fromInt(eraw));
            if (!isSroaRegisterType(pool, f_ty)) return null;
            out_fields[i] = f_ty;
        }
        return .{ .count = @intCast(elems.len), .is_struct = false };
    }
    if (node.tag == .struct_ty) {
        const sym_idx = SymbolIndex.fromInt(node.rhs);
        if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return null;
        const sym = sym_table.getSymbol(sym_idx).*;
        if (sym.target_scope.isNone()) return null;
        var count: usize = 0;
        for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
            const mem = sym_table.getSymbol(mem_idx).*;
            if (mem.kind != .field_sym) continue;
            if (count >= MAX_SROA_COMPOSITE_FIELDS) return null;
            const f_ty = pool.unwrapUnderlyingType(mem.type_id);
            if (!isSroaRegisterType(pool, f_ty)) return null;
            out_fields[count] = f_ty;
            count += 1;
        }
        if (count == 0) return null;
        return .{ .count = @intCast(count), .is_struct = true };
    }
    return null;
}

/// Pass `R2`: Scalar Replacement of Aggregates (`Place`-to-SSA promotion) using
/// `MirSsaBuilder.initFromExistingBody` (`[MAJOR-01]`).
fn runPassR2SroaPromotion(
    allocator: std.mem.Allocator,
    body: *MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    sink: ?*DiagnosticSink,
) !void {
    const local_count = body.locals.items.len;
    const first_body_local: usize = 1 + body.param_count;
    if (local_count <= first_body_local or body.blocks.items.len == 0) return;

    const is_disqualified = try allocator.alloc(bool, local_count);
    defer allocator.free(is_disqualified);
    @memset(is_disqualified, false);
    for (0..first_body_local) |li| is_disqualified[li] = true;

    // Scan all reachable instructions and `.call` sites to disqualify address-taken or dynamically projected locals:
    var dom = try mir.computeDominators(allocator, body);
    defer dom.deinit();

    for (dom.rpo_blocks) |bb_idx| {
        const bb_id = MirBlockId.fromInt(bb_idx);
        for (body.getBlockInsts(bb_id)) |inst_val| {
            const inst = body.getInst(inst_val);
            switch (inst.op) {
                .place_addr, .place_discriminant, .place_set_discrim, .soa_column_slice => {
                    const base = body.places.items[inst.operands.lhs].base;
                    if (base < local_count) is_disqualified[base] = true;
                },
                .place_load, .place_store => {
                    const pl = body.places.items[inst.operands.lhs];
                    if (pl.base >= local_count) continue;
                    if (pl.proj_len > 1) {
                        is_disqualified[pl.base] = true;
                    } else if (pl.proj_len == 1) {
                        const proj = body.projections.items[pl.proj_start];
                        if (proj.kind != .field) is_disqualified[pl.base] = true;
                    }
                },
                else => {},
            }
        }
        const term = body.blocks.items[bb_idx].terminator;
        if (term.kind == .call) {
            const cs = body.calls.items[term.cond_or_val];
            for (0..cs.args_len) |ai| {
                const mode = body.call_arg_modes.items[cs.modes_start + ai];
                if (mode == .inout_mode or mode == .set_mode) {
                    const pl_id = body.extra_args.items[cs.args_start + ai];
                    if (pl_id < body.places.items.len) {
                        const base = body.places.items[pl_id].base;
                        if (base < local_count) is_disqualified[base] = true;
                    }
                }
            }
        }
    }

    // Build promotion plans for eligible scalar & small composite locals:
    const scalar_var_map = try allocator.alloc(u32, local_count);
    defer allocator.free(scalar_var_map);
    @memset(scalar_var_map, mir.NONE_U32);

    const comp_plans = try allocator.alloc(?SroaCompositePlan, local_count);
    defer allocator.free(comp_plans);
    @memset(comp_plans, null);

    var sroa_var_types: std.ArrayListUnmanaged(TypeId) = .empty;
    defer sroa_var_types.deinit(allocator);

    for (first_body_local..local_count) |li| {
        if (is_disqualified[li]) continue;
        const loc_ty = body.locals.items[li].type_id;

        // Check if any projected (`proj_len == 1`) access exists on `li`:
        var has_field_proj = false;
        var has_any_access = false;
        for (dom.rpo_blocks) |bb_idx| {
            for (body.getBlockInsts(MirBlockId.fromInt(bb_idx))) |inst_val| {
                const inst = body.getInst(inst_val);
                if (inst.op == .place_load or inst.op == .place_store) {
                    const pl = body.places.items[inst.operands.lhs];
                    if (pl.base == li) {
                        has_any_access = true;
                        if (pl.proj_len > 0) has_field_proj = true;
                    }
                }
            }
        }
        if (!has_any_access) continue;

        if (!has_field_proj and isSroaRegisterType(pool, loc_ty)) {
            const v_id: u32 = @intCast(sroa_var_types.items.len);
            try sroa_var_types.append(allocator, loc_ty);
            scalar_var_map[li] = v_id;
            var fl = body.locals.items[li].flags();
            fl.is_address_taken = false;
            body.locals.items[li].setFlags(fl);
        } else {
            var field_tys: [MAX_SROA_COMPOSITE_FIELDS]TypeId = undefined;
            if (decomposeSmallCompositeFields(pool, sym_table, loc_ty, &field_tys)) |decomp| {
                const first_v: u32 = @intCast(sroa_var_types.items.len);
                try sroa_var_types.appendSlice(allocator, field_tys[0..decomp.count]);
                comp_plans[li] = .{
                    .first_var_id = first_v,
                    .field_count = decomp.count,
                    .is_struct = decomp.is_struct,
                };
                var fl = body.locals.items[li].flags();
                fl.is_address_taken = false;
                body.locals.items[li].setFlags(fl);
            }
        }
    }

    if (sroa_var_types.items.len == 0) return;

    var ssa = try mir.MirSsaBuilder.initFromExistingBody(
        allocator,
        body,
        sroa_var_types.items,
        sink,
    );
    defer ssa.deinit();

    // Unseal loop headers (`[CRITICAL-10]`: back-edges `dom.rpo_index[src] >= dom.rpo_index[dst]`)
    // and seal each block only after all reachable predecessors are rewritten in RPO:
    const unvisited_preds = try allocator.alloc(u32, body.blocks.items.len);
    defer allocator.free(unvisited_preds);
    @memset(unvisited_preds, 0);

    for (dom.rpo_blocks) |src_bb| {
        for (body.getOutgoingEdges(MirBlockId.fromInt(src_bb))) |edge| {
            if (!dom.isReachable(edge.target_bb)) continue;
            const dst_bb = edge.target_bb.asInt();
            unvisited_preds[dst_bb] += 1;
            if (dom.rpo_index[src_bb] >= dom.rpo_index[dst_bb]) {
                try ssa.setBlockSealed(edge.target_bb, false);
            }
        }
    }

    // Walk reachable blocks in RPO, promoting `place_store` / `place_load` into Braun SSA registers:
    for (dom.rpo_blocks) |bb_idx| {
        const bb_id = MirBlockId.fromInt(bb_idx);
        const orig_insts = try allocator.dupe(MirValueId, ssa.blocks_scratch.items[bb_idx].insts.items);
        defer allocator.free(orig_insts);
        ssa.blocks_scratch.items[bb_idx].insts.clearRetainingCapacity();

        for (orig_insts) |inst_val| {
            const inst = body.getInst(inst_val);
            const tok = body.origin_tokens.items[inst_val.asInt()];
            if (inst.op == .place_store) {
                const pl = body.places.items[inst.operands.lhs];
                if (pl.base < local_count and scalar_var_map[pl.base] != mir.NONE_U32) {
                    try ssa.writeVariable(
                        scalar_var_map[pl.base],
                        bb_id,
                        MirValueId.fromInt(inst.operands.rhs),
                    );
                    continue;
                }
                if (pl.base < local_count) {
                    if (comp_plans[pl.base]) |plan| {
                        if (pl.proj_len == 1) {
                            const ord = body.projections.items[pl.proj_start].payload;
                            if (ord < plan.field_count) {
                                try ssa.writeVariable(
                                    plan.first_var_id + ord,
                                    bb_id,
                                    MirValueId.fromInt(inst.operands.rhs),
                                );
                                continue;
                            }
                        } else if (pl.proj_len == 0) {
                            for (0..plan.field_count) |fi| {
                                const f_var = plan.first_var_id + @as(u32, @intCast(fi));
                                const ext_val = try body.appendInst(.{
                                    .op = .aggregate_extract,
                                    .flags = .{ .is_synthetic = true },
                                    .type_id = sroa_var_types.items[f_var],
                                    .operands = .{ .lhs = inst.operands.rhs, .rhs = @intCast(fi) },
                                }, tok);
                                try ssa.blocks_scratch.items[bb_idx].insts.append(allocator, ext_val);
                                try ssa.writeVariable(f_var, bb_id, ext_val);
                            }
                            continue;
                        }
                    }
                }
            } else if (inst.op == .place_load) {
                const pl = body.places.items[inst.operands.lhs];
                if (pl.base < local_count and scalar_var_map[pl.base] != mir.NONE_U32) {
                    const cur_val = try ssa.readVariable(scalar_var_map[pl.base], bb_id);
                    body.insts.set(inst_val.asInt(), .{
                        .op = .copy_val,
                        .flags = .{},
                        .type_id = inst.type_id,
                        .operands = .{ .lhs = cur_val.asInt(), .rhs = 0 },
                    });
                    try ssa.blocks_scratch.items[bb_idx].insts.append(allocator, inst_val);
                    continue;
                }
                if (pl.base < local_count) {
                    if (comp_plans[pl.base]) |plan| {
                        if (pl.proj_len == 1) {
                            const ord = body.projections.items[pl.proj_start].payload;
                            if (ord < plan.field_count) {
                                const cur_val = try ssa.readVariable(plan.first_var_id + ord, bb_id);
                                body.insts.set(inst_val.asInt(), .{
                                    .op = .copy_val,
                                    .flags = .{},
                                    .type_id = inst.type_id,
                                    .operands = .{ .lhs = cur_val.asInt(), .rhs = 0 },
                                });
                                try ssa.blocks_scratch.items[bb_idx].insts.append(allocator, inst_val);
                                continue;
                            }
                        } else if (pl.proj_len == 0) {
                            const ex_start: u32 = @intCast(body.extra_args.items.len);
                            for (0..plan.field_count) |fi| {
                                const fv = try ssa.readVariable(plan.first_var_id + @as(u32, @intCast(fi)), bb_id);
                                try body.extra_args.append(body.allocator, fv.asInt());
                            }
                            const agg_kind: AggregateKind = if (plan.is_struct) .struct_agg else .tuple_agg;
                            body.insts.set(inst_val.asInt(), .{
                                .op = .aggregate_make,
                                .flags = .{},
                                .aux_u16 = @backingInt(agg_kind),
                                .type_id = inst.type_id,
                                .operands = .{ .lhs = ex_start, .rhs = plan.field_count },
                            });
                            try ssa.blocks_scratch.items[bb_idx].insts.append(allocator, inst_val);
                            continue;
                        }
                    }
                }
            }

            try ssa.blocks_scratch.items[bb_idx].insts.append(allocator, inst_val);
        }

        for (body.getOutgoingEdges(bb_id)) |edge| {
            if (!dom.isReachable(edge.target_bb)) continue;
            const dst_bb = edge.target_bb.asInt();
            unvisited_preds[dst_bb] -= 1;
            if (unvisited_preds[dst_bb] == 0 and !ssa.blocks_scratch.items[dst_bb].is_sealed) {
                try ssa.sealBlock(edge.target_bb);
            }
        }
    }

    try ssa.finish();
}

// -------- Pass `R3`: Dominator-Scoped VRP & Check Fold --------

/// Closed integer interval `[min_val, max_val]` in `i128` used by `R3`.
const IntRange = struct {
    /// Inclusive lower bound.
    min_val: i128,
    /// Inclusive upper bound.
    max_val: i128,
};

/// Undo entry restoring `ranges[val_raw]` when leaving a dominator subtree in `R3`.
const RangeUndoEntry = struct {
    /// Target `MirValueId.asInt()`.
    val_raw: u32,
    /// Previous `IntRange` before narrowing.
    prev: ?IntRange,
};

/// Computes the natural `[MIN, MAX]` range of an integer/bool/char `TypeId` (`bits <= 127` or signed `128`).
fn fullTypeIntRange(pool: *const InternPool, raw_ty: TypeId, target_layout: TargetLayout) ?IntRange {
    const info = resolveOptIntInfo(pool, raw_ty, target_layout) orelse return null;
    if (info.is_signed) {
        if (info.bits >= 128) return .{ .min_val = std.math.minInt(i128), .max_val = std.math.maxInt(i128) };
        const half: i128 = @as(i128, 1) << @intCast(info.bits - 1);
        return .{ .min_val = -half, .max_val = half - 1 };
    }
    if (info.bits >= 128) return null; // Full `u128` exceeds `maxInt(i128)`.
    return .{ .min_val = 0, .max_val = (@as(i128, 1) << @intCast(info.bits)) - 1 };
}

/// Evaluates whether a relational `BinOpKind` is tautologically `true` or `false` over `[la, ra]`.
fn tryFoldRelationalByRange(kind: BinOpKind, lhs_r: IntRange, rhs_r: IntRange) ?bool {
    return switch (kind) {
        .eq => if (lhs_r.min_val == lhs_r.max_val and rhs_r.min_val == rhs_r.max_val and
            lhs_r.min_val == rhs_r.min_val)
            true
        else if (lhs_r.max_val < rhs_r.min_val or rhs_r.max_val < lhs_r.min_val)
            false
        else
            null,
        .ne => if (lhs_r.max_val < rhs_r.min_val or rhs_r.max_val < lhs_r.min_val)
            true
        else if (lhs_r.min_val == lhs_r.max_val and rhs_r.min_val == rhs_r.max_val and
            lhs_r.min_val == rhs_r.min_val)
            false
        else
            null,
        .slt, .ult => if (lhs_r.max_val < rhs_r.min_val)
            true
        else if (lhs_r.min_val >= rhs_r.max_val)
            false
        else
            null,
        .sle, .ule => if (lhs_r.max_val <= rhs_r.min_val)
            true
        else if (lhs_r.min_val > rhs_r.max_val)
            false
        else
            null,
        .sgt, .ugt => if (lhs_r.min_val > rhs_r.max_val)
            true
        else if (lhs_r.max_val <= rhs_r.min_val)
            false
        else
            null,
        .sge, .uge => if (lhs_r.min_val >= rhs_r.max_val)
            true
        else if (lhs_r.max_val < rhs_r.min_val)
            false
        else
            null,
        else => null,
    };
}

/// Pass `R3`: Dominator-scoped value-range propagation (VRP), folding tautological comparisons,
/// statically proven `@compile_assert`s, and provably non-overflowing checked integer operations.
fn runPassR3ValueRangeProp(
    allocator: std.mem.Allocator,
    body: *MirBody,
    pool: *const InternPool,
    target_layout: TargetLayout,
) !void {
    const block_count = body.blocks.items.len;
    if (block_count == 0 or body.insts.len == 0) return;

    var dom = try mir.computeDominators(allocator, body);
    defer dom.deinit();

    // Build dominator tree children adjacency lists:
    const dom_children = try allocator.alloc(std.ArrayListUnmanaged(u32), block_count);
    defer {
        for (dom_children) |*ch| ch.deinit(allocator);
        allocator.free(dom_children);
    }
    for (dom_children) |*ch| ch.* = .empty;
    for (dom.rpo_blocks) |bb_idx| {
        if (bb_idx == 0) continue;
        const parent = dom.idom[bb_idx];
        if (parent < block_count) {
            try dom_children[parent].append(allocator, bb_idx);
        }
    }

    const ranges = try allocator.alloc(?IntRange, body.insts.len);
    defer allocator.free(ranges);
    @memset(ranges, null);

    var undo_log: std.ArrayListUnmanaged(RangeUndoEntry) = .empty;
    defer undo_log.deinit(allocator);

    const VrpCtx = struct {
        alloc: std.mem.Allocator,
        m_body: *MirBody,
        intern_pool: *const InternPool,
        layout: TargetLayout,
        children: []const std.ArrayListUnmanaged(u32),
        cur_ranges: []?IntRange,
        undo: *std.ArrayListUnmanaged(RangeUndoEntry),

        fn setScopedRange(ctx: *@This(), val_raw: u32, new_r: IntRange) !void {
            if (val_raw >= ctx.cur_ranges.len or new_r.min_val > new_r.max_val) return;
            try ctx.undo.append(ctx.alloc, .{ .val_raw = val_raw, .prev = ctx.cur_ranges[val_raw] });
            if (ctx.cur_ranges[val_raw]) |old_r| {
                const merged = IntRange{
                    .min_val = @max(old_r.min_val, new_r.min_val),
                    .max_val = @min(old_r.max_val, new_r.max_val),
                };
                if (merged.min_val <= merged.max_val) {
                    ctx.cur_ranges[val_raw] = merged;
                }
            } else {
                ctx.cur_ranges[val_raw] = new_r;
            }
        }

        fn applyBranchNarrowing(ctx: *@This(), pred_bb: u32, is_true_arm: bool) !void {
            const term = ctx.m_body.blocks.items[pred_bb].terminator;
            if (term.kind != .cond_br or term.cond_or_val >= ctx.m_body.insts.len) return;
            const cond_inst = ctx.m_body.getInst(MirValueId.fromInt(term.cond_or_val));
            if (cond_inst.op != .bin_op) return;
            const bkind: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(cond_inst.aux_u16))));
            const lhs_raw = cond_inst.operands.lhs;
            const rhs_raw = cond_inst.operands.rhs;
            if (lhs_raw >= ctx.cur_ranges.len or rhs_raw >= ctx.cur_ranges.len) return;

            const rhs_r = ctx.cur_ranges[rhs_raw] orelse return;
            if (rhs_r.min_val != rhs_r.max_val) return;
            const k_val = rhs_r.min_val;
            const lhs_base = ctx.cur_ranges[lhs_raw] orelse
                fullTypeIntRange(ctx.intern_pool, ctx.m_body.getInst(MirValueId.fromInt(lhs_raw)).type_id, ctx.layout) orelse
                return;

            const eff_kind: BinOpKind = if (is_true_arm) bkind else switch (bkind) {
                .eq => .ne,
                .ne => .eq,
                .slt => .sge,
                .ult => .uge,
                .sle => .sgt,
                .ule => .ugt,
                .sgt => .sle,
                .ugt => .ule,
                .sge => .slt,
                .uge => .ult,
                else => return,
            };

            switch (eff_kind) {
                .eq => try ctx.setScopedRange(lhs_raw, .{ .min_val = k_val, .max_val = k_val }),
                .slt, .ult => if (k_val > std.math.minInt(i128)) {
                    try ctx.setScopedRange(lhs_raw, .{ .min_val = lhs_base.min_val, .max_val = k_val - 1 });
                },
                .sle, .ule => try ctx.setScopedRange(lhs_raw, .{ .min_val = lhs_base.min_val, .max_val = k_val }),
                .sgt, .ugt => if (k_val < std.math.maxInt(i128)) {
                    try ctx.setScopedRange(lhs_raw, .{ .min_val = k_val + 1, .max_val = lhs_base.max_val });
                },
                .sge, .uge => try ctx.setScopedRange(lhs_raw, .{ .min_val = k_val, .max_val = lhs_base.max_val }),
                else => {},
            }
        }

        fn visitDomBlock(ctx: *@This(), bb_idx: u32) !void {
            const checkpoint = ctx.undo.items.len;
            defer {
                while (ctx.undo.items.len > checkpoint) {
                    const entry = ctx.undo.pop().?;
                    ctx.cur_ranges[entry.val_raw] = entry.prev;
                }
            }

            const bb_id = MirBlockId.fromInt(bb_idx);

            // If `bb_idx` has a single incoming edge from a `cond_br`, narrow intervals on that arm:
            if (ctx.m_body.blocks.items[bb_idx].pred_len == 1) {
                const pred_eid = ctx.m_body.getPredEdges(bb_id)[0];
                const edge = ctx.m_body.extra_edges.items[pred_eid.asInt()];
                const src_term = ctx.m_body.blocks.items[edge.src_bb.asInt()].terminator;
                if (src_term.kind == .cond_br and src_term.edge_len == 2) {
                    const e0 = ctx.m_body.extra_edges.items[src_term.edge_start];
                    const e1 = ctx.m_body.extra_edges.items[src_term.edge_start + 1];
                    if (e0.target_bb != e1.target_bb) {
                        try ctx.applyBranchNarrowing(edge.src_bb.asInt(), pred_eid.asInt() == src_term.edge_start);
                    }
                }
            }

            for (ctx.m_body.getBlockParams(bb_id)) |p_val| {
                if (fullTypeIntRange(ctx.intern_pool, ctx.m_body.getInst(p_val).type_id, ctx.layout)) |tr| {
                    try ctx.setScopedRange(p_val.asInt(), tr);
                }
            }

            for (ctx.m_body.getBlockInsts(bb_id)) |inst_val| {
                const raw = inst_val.asInt();
                if (raw >= ctx.cur_ranges.len) continue;
                const inst = ctx.m_body.getInst(inst_val);
                if (fullTypeIntRange(ctx.intern_pool, inst.type_id, ctx.layout)) |tr| {
                    try ctx.setScopedRange(raw, tr);
                }

                switch (inst.op) {
                    .const_scalar => {
                        if (inst.operands.lhs < ctx.m_body.consts.items.len) {
                            if (constToI128(ctx.m_body.consts.items[inst.operands.lhs])) |iv| {
                                if (resolveOptIntInfo(ctx.intern_pool, inst.type_id, ctx.layout)) |info| {
                                    if (info.is_signed) {
                                        const norm = sextConstInt(iv, info.bits);
                                        try ctx.setScopedRange(raw, .{ .min_val = norm, .max_val = norm });
                                    } else if (info.bits < 128) {
                                        const norm: i128 = @intCast(zextConstInt(iv, info.bits));
                                        try ctx.setScopedRange(raw, .{ .min_val = norm, .max_val = norm });
                                    } else if (iv >= 0) {
                                        // Unsigned `128`-bit constants `< 2^127` fit in `[0, maxInt(i128)]`;
                                        // values `>= 2^127` wrap negative in `i128` (`[CRITICAL-13]`) and stay unconstrained:
                                        try ctx.setScopedRange(raw, .{ .min_val = iv, .max_val = iv });
                                    }
                                }
                            }
                        }
                    },
                    .copy_val => {
                        if (inst.operands.lhs < ctx.cur_ranges.len) {
                            if (ctx.cur_ranges[inst.operands.lhs]) |sr| {
                                try ctx.setScopedRange(raw, sr);
                            }
                        }
                    },
                    .bin_op => {
                        if (inst.operands.lhs >= ctx.cur_ranges.len or inst.operands.rhs >= ctx.cur_ranges.len) continue;
                        const lr = ctx.cur_ranges[inst.operands.lhs] orelse continue;
                        const rr = ctx.cur_ranges[inst.operands.rhs] orelse continue;
                        const bkind: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                        if (tryFoldRelationalByRange(bkind, lr, rr)) |folded_bool| {
                            const c_idx = try ctx.m_body.appendConst(.{ .bool_val = folded_bool });
                            ctx.m_body.insts.set(raw, .{
                                .op = .const_scalar,
                                .flags = .{},
                                .type_id = .bool_ty,
                                .operands = .{ .lhs = c_idx, .rhs = 0 },
                            });
                            const b_int: i128 = @intFromBool(folded_bool);
                            try ctx.setScopedRange(raw, .{ .min_val = b_int, .max_val = b_int });
                            continue;
                        }

                        // Downgrade provably non-overflowing checked add/sub to non-trapping wrap:
                        if (bkind == .sadd_checked or bkind == .uadd_checked) {
                            if (fullTypeIntRange(ctx.intern_pool, inst.type_id, ctx.layout)) |ty_bounds| {
                                const min_ov = @addWithOverflow(lr.min_val, rr.min_val);
                                const max_ov = @addWithOverflow(lr.max_val, rr.max_val);
                                if (min_ov[1] == 0 and max_ov[1] == 0 and
                                    min_ov[0] >= ty_bounds.min_val and max_ov[0] <= ty_bounds.max_val)
                                {
                                    var updated = inst;
                                    updated.aux_u16 = @backingInt(BinOpKind.add_wrap);
                                    updated.flags.has_trap_risk = false;
                                    ctx.m_body.insts.set(raw, updated);
                                    try ctx.setScopedRange(raw, .{ .min_val = min_ov[0], .max_val = max_ov[0] });
                                }
                            }
                        } else if (bkind == .ssub_checked or bkind == .usub_checked) {
                            if (fullTypeIntRange(ctx.intern_pool, inst.type_id, ctx.layout)) |ty_bounds| {
                                const min_ov = @subWithOverflow(lr.min_val, rr.max_val);
                                const max_ov = @subWithOverflow(lr.max_val, rr.min_val);
                                if (min_ov[1] == 0 and max_ov[1] == 0 and
                                    min_ov[0] >= ty_bounds.min_val and max_ov[0] <= ty_bounds.max_val)
                                {
                                    var updated = inst;
                                    updated.aux_u16 = @backingInt(BinOpKind.sub_wrap);
                                    updated.flags.has_trap_risk = false;
                                    ctx.m_body.insts.set(raw, updated);
                                    try ctx.setScopedRange(raw, .{ .min_val = min_ov[0], .max_val = max_ov[0] });
                                }
                            }
                        }
                    },
                    .intrinsic_op => {
                        const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                        if (ikind == .compile_assert and inst.operands.rhs >= 1) {
                            const cond_raw = ctx.m_body.extra_args.items[inst.operands.lhs];
                            if (cond_raw < ctx.cur_ranges.len) {
                                if (ctx.cur_ranges[cond_raw]) |cr| {
                                    if (cr.min_val == 1 and cr.max_val == 1) {
                                        const c_idx = try ctx.m_body.appendConst(.unit_val);
                                        ctx.m_body.insts.set(raw, .{
                                            .op = .const_scalar,
                                            .flags = .{},
                                            .type_id = .unit_ty,
                                            .operands = .{ .lhs = c_idx, .rhs = 0 },
                                        });
                                    }
                                }
                            }
                        }
                    },
                    else => {},
                }
            }

            for (ctx.children[bb_idx].items) |child_bb| {
                try ctx.visitDomBlock(child_bb);
            }
        }
    };

    var ctx = VrpCtx{
        .alloc = allocator,
        .m_body = body,
        .intern_pool = pool,
        .layout = target_layout,
        .children = dom_children,
        .cur_ranges = ranges,
        .undo = &undo_log,
    };
    try ctx.visitDomBlock(0);
}


// ------------ Pass `R4`: SCCP, Switch Fusion & GVN ------------

/// Three-level Wegman-Zadeck SCCP lattice state (`Top -> constant -> Bottom`).
const SccpLattice = union(enum) {
    /// Unreached / optimistic top ($\top$).
    top,
    /// Known scalar constant.
    constant: MirConst,
    /// Overdefined / dynamic ($\bot$).
    bottom,
};

/// Returns `true` if `mc_a` and `mc_b` represent the exact same `MirConst` bit-pattern.
fn isMirConstExactEqual(mc_a: MirConst, mc_b: MirConst) bool {
    return switch (mc_a) {
        .unit_val => mc_b == .unit_val,
        .bool_val => |ba| mc_b == .bool_val and ba == mc_b.bool_val,
        .char_val => |ca| mc_b == .char_val and ca == mc_b.char_val,
        .int_val => |ia| mc_b == .int_val and ia == mc_b.int_val,
        .float_val => |fa| mc_b == .float_val and
            @as(u64, @bitCast(fa)) == @as(u64, @bitCast(mc_b.float_val)),
        .str_val => |sa| mc_b == .str_val and sa == mc_b.str_val,
        .bytes_val => |bya| mc_b == .bytes_val and bya == mc_b.bytes_val,
    };
}

/// Meets `cur` with `incoming` on the Wegman-Zadeck lattice (`true` if `cur` changed).
fn meetSccpLattice(cur: *SccpLattice, incoming: SccpLattice) bool {
    return switch (incoming) {
        .top => false,
        .bottom => blk: {
            if (cur.* == .bottom) break :blk false;
            cur.* = .bottom;
            break :blk true;
        },
        .constant => |inc_mc| switch (cur.*) {
            .top => blk: {
                cur.* = .{ .constant = inc_mc };
                break :blk true;
            },
            .constant => |cur_mc| blk: {
                if (isMirConstExactEqual(cur_mc, inc_mc)) break :blk false;
                cur.* = .bottom;
                break :blk true;
            },
            .bottom => false,
        },
    };
}

/// Fuses cascaded `switch_int` terminators along single-predecessor pure default edges (`DR-13` §6.2 `R4`).
fn fuseAdjacentSwitchIntBlocks(allocator: std.mem.Allocator, body: *MirBody) !void {
    const block_count = body.blocks.items.len;
    for (0..block_count) |bb_i| {
        const term = body.blocks.items[bb_i].terminator;
        if (term.kind != .switch_int or term.edge_len < 1) continue;
        const def_eid = term.edge_start + term.edge_len - 1;
        const def_edge = body.extra_edges.items[def_eid];
        if (def_edge.args_len != 0) continue;

        const next_bb_idx = def_edge.target_bb.asInt();
        if (next_bb_idx == bb_i or next_bb_idx >= block_count) continue;
        const next_bb = body.blocks.items[next_bb_idx];
        if (next_bb.pred_len != 1 or next_bb.paramLen() != 0 or next_bb.inst_len != 0) continue;
        if (next_bb.terminator.kind != .switch_int or
            next_bb.terminator.cond_or_val != term.cond_or_val or
            next_bb.terminator.edge_len < 1)
        {
            continue;
        }

        // Merge `next_bb`'s non-duplicate case edges + default edge into `bb_i`:
        var seen_cases: std.AutoHashMapUnmanaged(i128, void) = .empty;
        defer seen_cases.deinit(allocator);

        var merged_edges: std.ArrayListUnmanaged(MirOutgoingEdge) = .empty;
        defer merged_edges.deinit(allocator);

        for (0..(term.edge_len - 1)) |off| {
            const ce = body.extra_edges.items[term.edge_start + off];
            if (ce.case_tag_idx < body.switch_values.items.len) {
                try seen_cases.put(allocator, body.switch_values.items[ce.case_tag_idx], {});
            }
            try merged_edges.append(allocator, ce);
        }

        const next_term = next_bb.terminator;
        for (0..(next_term.edge_len - 1)) |off| {
            var ce = body.extra_edges.items[next_term.edge_start + off];
            if (ce.case_tag_idx < body.switch_values.items.len) {
                const sw_val = body.switch_values.items[ce.case_tag_idx];
                if (seen_cases.contains(sw_val)) continue;
                try seen_cases.put(allocator, sw_val, {});
            }
            ce.src_bb = MirBlockId.fromInt(@intCast(bb_i));
            try merged_edges.append(allocator, ce);
        }

        var final_def = body.extra_edges.items[next_term.edge_start + next_term.edge_len - 1];
        final_def.src_bb = MirBlockId.fromInt(@intCast(bb_i));
        final_def.case_tag_idx = std.math.maxInt(u16);
        try merged_edges.append(allocator, final_def);

        if (merged_edges.items.len > std.math.maxInt(u16)) continue;
        const new_edge_start: u32 = @intCast(body.extra_edges.items.len);
        try body.extra_edges.appendSlice(body.allocator, merged_edges.items);
        body.blocks.items[bb_i].terminator = .{
            .kind = .switch_int,
            .edge_len = @intCast(merged_edges.items.len),
            .cond_or_val = term.cond_or_val,
            .edge_start = new_edge_start,
        };
    }
    try rebuildPredsAndSweepUnreachable(allocator, body);
}

/// Canonical value-numbering key for dominator-scoped commutative GVN in `R4`.
const GvnKey = struct {
    /// Opcode (`const_scalar`, `bin_op`, `unary_op`, `aggregate_extract`, `bitfield_extract`, `fn_addr`).
    op: MirOp,
    /// Normalized sub-opcode (`BinOpKind`, `UnaryOpKind`, etc.).
    aux_u16: u16,
    /// Result `TypeId.toU32()`.
    type_raw: u32,
    /// Normalized primary operand or constant tag digest.
    lhs: u64,
    /// Normalized secondary operand or constant payload digest.
    rhs: u64,
};

/// Resolves `.copy_val` chains and previously numbered GVN aliases to a canonical `MirValueId.asInt()`.
fn resolveCanonicalSsaVal(
    body: *const MirBody,
    raw_val: u32,
    replacements: *const std.AutoHashMapUnmanaged(u32, u32),
) u32 {
    var cur = raw_val;
    var guard: usize = 0;
    while (cur < body.insts.len and guard < 32) : (guard += 1) {
        if (replacements.get(cur)) |rep| {
            if (rep != cur) {
                cur = rep;
                continue;
            }
        }
        const inst = body.getInst(MirValueId.fromInt(cur));
        if (inst.op == .copy_val and inst.operands.lhs != cur) {
            cur = inst.operands.lhs;
            continue;
        }
        break;
    }
    return cur;
}

/// Builds a normalized `GvnKey` for pure, deterministic instructions (`null` if stateful/impure).
fn makeGvnKey(
    body: *const MirBody,
    inst: MirInst,
    replacements: *const std.AutoHashMapUnmanaged(u32, u32),
) ?GvnKey {
    if (inst.flags.has_side_effects) return null;
    switch (inst.op) {
        .const_scalar => {
            if (inst.operands.lhs >= body.consts.items.len) return null;
            const mc = body.consts.items[inst.operands.lhs];
            var tag_word: u64 = @intFromEnum(mc);
            var pay_word: u64 = 0;
            switch (mc) {
                .unit_val => {},
                .bool_val => |bv| pay_word = @intFromBool(bv),
                .char_val => |cv| pay_word = cv,
                .int_val => |iv| {
                    const u_bits: u128 = @bitCast(iv);
                    tag_word |= (@as(u64, @truncate(u_bits >> 64)) << 8);
                    pay_word = @truncate(u_bits);
                    if ((u_bits >> 56) != 0 and (u_bits >> 56) != std.math.maxInt(u72)) return null;
                },
                .float_val => |fv| pay_word = @bitCast(fv),
                .str_val => |sv| pay_word = sv.asInt(),
                .bytes_val => |bv| pay_word = bv.asInt(),
            }
            return .{
                .op = .const_scalar,
                .aux_u16 = 0,
                .type_raw = inst.type_id.toU32(),
                .lhs = tag_word,
                .rhs = pay_word,
            };
        },
        .bin_op => {
            var bkind: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            var l_can = resolveCanonicalSsaVal(body, inst.operands.lhs, replacements);
            var r_can = resolveCanonicalSsaVal(body, inst.operands.rhs, replacements);
            if (l_can > r_can) {
                switch (bkind) {
                    .sadd_checked,
                    .uadd_checked,
                    .smul_checked,
                    .umul_checked,
                    .add_wrap,
                    .mul_wrap,
                    .sadd_sat,
                    .uadd_sat,
                    .smul_sat,
                    .umul_sat,
                    .bit_and,
                    .bit_or,
                    .bit_xor,
                    .eq,
                    .ne,
                    => std.mem.swap(u32, &l_can, &r_can),
                    .slt => {
                        std.mem.swap(u32, &l_can, &r_can);
                        bkind = .sgt;
                    },
                    .sgt => {
                        std.mem.swap(u32, &l_can, &r_can);
                        bkind = .slt;
                    },
                    .ult => {
                        std.mem.swap(u32, &l_can, &r_can);
                        bkind = .ugt;
                    },
                    .ugt => {
                        std.mem.swap(u32, &l_can, &r_can);
                        bkind = .ult;
                    },
                    .sle => {
                        std.mem.swap(u32, &l_can, &r_can);
                        bkind = .sge;
                    },
                    .sge => {
                        std.mem.swap(u32, &l_can, &r_can);
                        bkind = .sle;
                    },
                    .ule => {
                        std.mem.swap(u32, &l_can, &r_can);
                        bkind = .uge;
                    },
                    .uge => {
                        std.mem.swap(u32, &l_can, &r_can);
                        bkind = .ule;
                    },
                    else => {},
                }
            }
            return .{
                .op = .bin_op,
                .aux_u16 = @backingInt(bkind),
                .type_raw = inst.type_id.toU32(),
                .lhs = l_can,
                .rhs = r_can,
            };
        },
        .unary_op, .aggregate_extract, .bitfield_extract => {
            const l_can = resolveCanonicalSsaVal(body, inst.operands.lhs, replacements);
            return .{
                .op = inst.op,
                .aux_u16 = inst.aux_u16,
                .type_raw = inst.type_id.toU32(),
                .lhs = l_can,
                .rhs = inst.operands.rhs,
            };
        },
        .fn_addr => {
            return .{
                .op = .fn_addr,
                .aux_u16 = inst.aux_u16,
                .type_raw = inst.type_id.toU32(),
                .lhs = inst.operands.lhs,
                .rhs = inst.operands.rhs,
            };
        },
        else => return null,
    }
}

/// Pass `R4`: Wegman-Zadeck Sparse Conditional Constant Propagation (SCCP), adjacent `switch_int`
/// fusion, and dominator-scoped commutative Global Value Numbering (GVN).
fn runPassR4SccpSwitchFusionAndGvn(
    allocator: std.mem.Allocator,
    body: *MirBody,
    pool: *const InternPool,
    target_layout: TargetLayout,
) !void {
    const block_count = body.blocks.items.len;
    if (block_count == 0 or body.insts.len == 0) return;

    // [Part A] Wegman-Zadeck Lattice SCCP:
    {
        var dom_sccp = try mir.computeDominators(allocator, body);
        defer dom_sccp.deinit();

        const val_lat = try allocator.alloc(SccpLattice, body.insts.len);
        defer allocator.free(val_lat);
        @memset(val_lat, .top);

        const exec_edge = try allocator.alloc(bool, body.extra_edges.items.len);
        defer allocator.free(exec_edge);
        @memset(exec_edge, false);

        const exec_bb = try allocator.alloc(bool, block_count);
        defer allocator.free(exec_bb);
        @memset(exec_bb, false);
        exec_bb[0] = true;

        // Detect `.call` continuation `normal_bb`s whose `%ret_val` parameter is `.bottom`:
        const is_call_cont = try allocator.alloc(bool, block_count);
        defer allocator.free(is_call_cont);
        @memset(is_call_cont, false);
        for (body.blocks.items) |bb| {
            if (bb.terminator.kind == .call and bb.terminator.edge_len >= 1) {
                const dst = body.extra_edges.items[bb.terminator.edge_start].target_bb.asInt();
                if (dst < block_count) is_call_cont[dst] = true;
            }
        }

        var has_progressed = true;
        while (has_progressed) {
            has_progressed = false;
            for (dom_sccp.rpo_blocks) |bb_idx| {
                if (!exec_bb[bb_idx]) continue;
                const bb_id = MirBlockId.fromInt(bb_idx);

                // Meet incoming executable edge arguments for `block_param`s:
                const b_params = body.getBlockParams(bb_id);
                if (is_call_cont[bb_idx]) {
                    for (b_params) |pv| {
                        if (meetSccpLattice(&val_lat[pv.asInt()], .bottom)) has_progressed = true;
                    }
                } else {
                    for (b_params, 0..) |pv, p_pos| {
                        for (body.getPredEdges(bb_id)) |peid| {
                            if (!exec_edge[peid.asInt()]) continue;
                            const pedge = body.extra_edges.items[peid.asInt()];
                            if (p_pos < pedge.args_len) {
                                const arg_raw = body.extra_args.items[pedge.args_start + p_pos];
                                if (arg_raw < val_lat.len) {
                                    if (meetSccpLattice(&val_lat[pv.asInt()], val_lat[arg_raw])) has_progressed = true;
                                }
                            }
                        }
                    }
                }

                // Evaluate sequential instructions:
                for (body.getBlockInsts(bb_id)) |inst_val| {
                    const raw = inst_val.asInt();
                    const inst = body.getInst(inst_val);
                    switch (inst.op) {
                        .const_scalar => {
                            if (inst.operands.lhs < body.consts.items.len) {
                                if (meetSccpLattice(&val_lat[raw], .{ .constant = body.consts.items[inst.operands.lhs] })) {
                                    has_progressed = true;
                                }
                            }
                        },
                        .copy_val => {
                            if (inst.operands.lhs < val_lat.len) {
                                if (meetSccpLattice(&val_lat[raw], val_lat[inst.operands.lhs])) has_progressed = true;
                            }
                        },
                        .bin_op => {
                            if (inst.operands.lhs >= val_lat.len or inst.operands.rhs >= val_lat.len) continue;
                            const ll = val_lat[inst.operands.lhs];
                            const rl = val_lat[inst.operands.rhs];
                            if (ll == .bottom or rl == .bottom) {
                                if (meetSccpLattice(&val_lat[raw], .bottom)) has_progressed = true;
                            } else if (ll == .constant and rl == .constant) {
                                const bkind: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                                const op_ty = body.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id;
                                const rhs_ty = body.getInst(MirValueId.fromInt(inst.operands.rhs)).type_id;
                                const eval_res = foldConstBinOp(
                                    pool,
                                    bkind,
                                    ll.constant,
                                    rl.constant,
                                    op_ty,
                                    rhs_ty,
                                    inst.type_id,
                                    target_layout,
                                );
                                const next_lat: SccpLattice = switch (eval_res) {
                                    .folded => |mc| .{ .constant = mc },
                                    else => .bottom,
                                };
                                if (meetSccpLattice(&val_lat[raw], next_lat)) has_progressed = true;
                            }
                        },
                        .unary_op => {
                            if (inst.operands.lhs >= val_lat.len) continue;
                            const sl = val_lat[inst.operands.lhs];
                            if (sl == .bottom) {
                                if (meetSccpLattice(&val_lat[raw], .bottom)) has_progressed = true;
                            } else if (sl == .constant) {
                                const ukind: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                                const s_ty = body.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id;
                                const eval_res = foldConstUnaryOp(
                                    pool,
                                    ukind,
                                    sl.constant,
                                    s_ty,
                                    inst.type_id,
                                    target_layout,
                                );
                                const next_lat: SccpLattice = switch (eval_res) {
                                    .folded => |mc| .{ .constant = mc },
                                    else => .bottom,
                                };
                                if (meetSccpLattice(&val_lat[raw], next_lat)) has_progressed = true;
                            }
                        },
                        else => {
                            if (meetSccpLattice(&val_lat[raw], .bottom)) has_progressed = true;
                        },
                    }
                }

                // Propagate executable CFG edges:
                const term = body.blocks.items[bb_idx].terminator;
                if (term.kind == .cond_br and term.cond_or_val < val_lat.len) {
                    const cl = val_lat[term.cond_or_val];
                    if (cl == .top) continue;
                    if (cl == .constant and cl.constant == .bool_val) {
                        const eid = term.edge_start + @as(u32, if (cl.constant.bool_val) 0 else 1);
                        if (!exec_edge[eid]) {
                            exec_edge[eid] = true;
                            exec_bb[body.extra_edges.items[eid].target_bb.asInt()] = true;
                            has_progressed = true;
                        }
                        continue;
                    }
                } else if (term.kind == .switch_int and term.cond_or_val < val_lat.len) {
                    const dl = val_lat[term.cond_or_val];
                    if (dl == .top) continue;
                    if (dl == .constant) {
                        if (selectConstSwitchEdgeOffset(body, term, dl.constant)) |off| {
                            const eid = term.edge_start + @as(u32, @intCast(off));
                            if (!exec_edge[eid]) {
                                exec_edge[eid] = true;
                                exec_bb[body.extra_edges.items[eid].target_bb.asInt()] = true;
                                has_progressed = true;
                            }
                            continue;
                        }
                    }
                }

                for (0..term.edge_len) |off| {
                    const eid = term.edge_start + @as(u32, @intCast(off));
                    if (!exec_edge[eid]) {
                        exec_edge[eid] = true;
                        exec_bb[body.extra_edges.items[eid].target_bb.asInt()] = true;
                        has_progressed = true;
                    }
                }
            }
        }

        // Materialize SCCP constants in executable blocks and fold constant branches:
        var sccp_param_rewrites: std.AutoHashMapUnmanaged(u32, u32) = .empty;
        defer sccp_param_rewrites.deinit(allocator);

        for (0..block_count) |bb_i| {
            if (!exec_bb[bb_i]) continue;
            const bb_id = MirBlockId.fromInt(@intCast(bb_i));
            if (!is_call_cont[bb_i]) {
                for (body.getBlockParams(bb_id)) |pv| {
                    if (val_lat[pv.asInt()] == .constant) {
                        const c_idx = try body.appendConst(val_lat[pv.asInt()].constant);
                        const c_val = try body.appendInst(.{
                            .op = .const_scalar,
                            .flags = .{ .is_synthetic = true },
                            .type_id = body.getInst(pv).type_id,
                            .operands = .{ .lhs = c_idx, .rhs = 0 },
                        }, .none);
                        // Prepend `c_val` to `^bb0` so it dominates all blocks (`V1`):
                        var bb0_list: std.ArrayListUnmanaged(MirValueId) = .empty;
                        defer bb0_list.deinit(allocator);
                        try bb0_list.append(allocator, c_val);
                        try bb0_list.appendSlice(allocator, body.getBlockInsts(MirBlockId.fromInt(0)));
                        const n_start: u32 = @intCast(body.block_insts.items.len);
                        try body.block_insts.appendSlice(body.allocator, bb0_list.items);
                        body.blocks.items[0].inst_start = n_start;
                        body.blocks.items[0].inst_len = @intCast(bb0_list.items.len);
                        try sccp_param_rewrites.put(allocator, pv.asInt(), c_val.asInt());
                    }
                }
            }

            for (body.getBlockInsts(bb_id)) |iv| {
                const raw = iv.asInt();
                if (raw >= val_lat.len) continue;
                const inst = body.getInst(iv);
                if (inst.op == .const_scalar or inst.flags.has_side_effects) continue;
                if (val_lat[raw] == .constant) {
                    const c_idx = try body.appendConst(val_lat[raw].constant);
                    body.insts.set(raw, .{
                        .op = .const_scalar,
                        .flags = .{},
                        .type_id = inst.type_id,
                        .operands = .{ .lhs = c_idx, .rhs = 0 },
                    });
                }
            }

            const term = body.blocks.items[bb_i].terminator;
            if (term.kind == .cond_br and term.cond_or_val < val_lat.len) {
                if (val_lat[term.cond_or_val] == .constant and val_lat[term.cond_or_val].constant == .bool_val) {
                    const kept_eid = term.edge_start + @as(u32, if (val_lat[term.cond_or_val].constant.bool_val) 0 else 1);
                    body.extra_edges.items[kept_eid].case_tag_idx = std.math.maxInt(u16);
                    body.blocks.items[bb_i].terminator = .{
                        .kind = .br,
                        .edge_len = 1,
                        .edge_start = kept_eid,
                    };
                }
            } else if (term.kind == .switch_int and term.cond_or_val < val_lat.len) {
                if (val_lat[term.cond_or_val] == .constant) {
                    if (selectConstSwitchEdgeOffset(body, term, val_lat[term.cond_or_val].constant)) |off| {
                        const kept_eid = term.edge_start + @as(u32, @intCast(off));
                        body.extra_edges.items[kept_eid].case_tag_idx = std.math.maxInt(u16);
                        body.blocks.items[bb_i].terminator = .{
                            .kind = .br,
                            .edge_len = 1,
                            .edge_start = kept_eid,
                        };
                    }
                }
            }
        }

        applyValueRewriteMap(body, &sccp_param_rewrites);
        try rebuildPredsAndSweepUnreachable(allocator, body);
    }

    // [Part B] Cascaded `switch_int` fusion:
    try fuseAdjacentSwitchIntBlocks(allocator, body);

    // [Part C] Dominator-Scoped Commutative Global Value Numbering (GVN):
    {
        var dom_gvn = try mir.computeDominators(allocator, body);
        defer dom_gvn.deinit();

        const dom_children = try allocator.alloc(std.ArrayListUnmanaged(u32), body.blocks.items.len);
        defer {
            for (dom_children) |*ch| ch.deinit(allocator);
            allocator.free(dom_children);
        }
        for (dom_children) |*ch| ch.* = .empty;
        for (dom_gvn.rpo_blocks) |bb_idx| {
            if (bb_idx == 0) continue;
            const parent = dom_gvn.idom[bb_idx];
            if (parent < dom_children.len) {
                try dom_children[parent].append(allocator, bb_idx);
            }
        }

        var gvn_table: std.AutoHashMapUnmanaged(GvnKey, u32) = .empty;
        defer gvn_table.deinit(allocator);
        var inserted_keys: std.ArrayListUnmanaged(GvnKey) = .empty;
        defer inserted_keys.deinit(allocator);
        var replacements: std.AutoHashMapUnmanaged(u32, u32) = .empty;
        defer replacements.deinit(allocator);

        const GvnWalk = struct {
            alloc: std.mem.Allocator,
            m_body: *MirBody,
            children: []const std.ArrayListUnmanaged(u32),
            table: *std.AutoHashMapUnmanaged(GvnKey, u32),
            key_stack: *std.ArrayListUnmanaged(GvnKey),
            rep_map: *std.AutoHashMapUnmanaged(u32, u32),

            fn visit(ctx: *@This(), bb_idx: u32) !void {
                const checkpoint = ctx.key_stack.items.len;
                defer {
                    while (ctx.key_stack.items.len > checkpoint) {
                        _ = ctx.table.remove(ctx.key_stack.pop().?);
                    }
                }

                for (ctx.m_body.getBlockInsts(MirBlockId.fromInt(bb_idx))) |iv| {
                    const raw = iv.asInt();
                    const inst = ctx.m_body.getInst(iv);
                    if (inst.op == .copy_val) {
                        const target = resolveCanonicalSsaVal(ctx.m_body, inst.operands.lhs, ctx.rep_map);
                        if (target != raw) {
                            try ctx.rep_map.put(ctx.alloc, raw, target);
                        }
                        continue;
                    }
                    if (makeGvnKey(ctx.m_body, inst, ctx.rep_map)) |key| {
                        if (ctx.table.get(key)) |dom_val| {
                            if (dom_val != raw) {
                                try ctx.rep_map.put(ctx.alloc, raw, dom_val);
                                if (inst.flags.has_trap_risk) {
                                    var non_trapping_inst = inst;
                                    non_trapping_inst.flags.has_trap_risk = false;
                                    ctx.m_body.insts.set(raw, non_trapping_inst);
                                }
                            }
                        } else {
                            try ctx.table.put(ctx.alloc, key, raw);
                            try ctx.key_stack.append(ctx.alloc, key);
                        }
                    }
                }

                for (ctx.children[bb_idx].items) |child_bb| {
                    try ctx.visit(child_bb);
                }
            }
        };

        var walk = GvnWalk{
            .alloc = allocator,
            .m_body = body,
            .children = dom_children,
            .table = &gvn_table,
            .key_stack = &inserted_keys,
            .rep_map = &replacements,
        };
        try walk.visit(0);
        applyValueRewriteMap(body, &replacements);
    }
}

// -------- Pass `R5`: Projection-Aware DCE & CFG Merge ---------

/// Marks all dynamic `ProjKind.index` operands of `place_raw` live on `worklist` (`[CRITICAL-06]`).
fn markPlaceIndicesLive(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    place_raw: u32,
    is_live: []bool,
    worklist: *std.ArrayListUnmanaged(u32),
) !void {
    if (place_raw >= body.places.items.len) return;
    for (body.getPlaceProjections(PlaceId.fromInt(place_raw))) |proj| {
        if (proj.kind == .index and proj.payload < is_live.len and !is_live[proj.payload]) {
            is_live[proj.payload] = true;
            try worklist.append(allocator, proj.payload);
        }
    }
}

/// Marks a single SSA `val_raw` live on `worklist`.
inline fn markSsaValLive(
    allocator: std.mem.Allocator,
    val_raw: u32,
    is_live: []bool,
    worklist: *std.ArrayListUnmanaged(u32),
) !void {
    if (val_raw < is_live.len and !is_live[val_raw]) {
        is_live[val_raw] = true;
        try worklist.append(allocator, val_raw);
    }
}

/// Eliminates dead side-effect-free non-trapping instructions across reachable blocks (`[CRITICAL-06]`).
fn eliminateDeadSsaInstructions(allocator: std.mem.Allocator, body: *MirBody) !void {
    const inst_total = body.insts.len;
    if (inst_total == 0 or body.blocks.items.len == 0) return;

    var dom = try mir.computeDominators(allocator, body);
    defer dom.deinit();

    const is_live = try allocator.alloc(bool, inst_total);
    defer allocator.free(is_live);
    @memset(is_live, false);

    var worklist: std.ArrayListUnmanaged(u32) = .empty;
    defer worklist.deinit(allocator);

    // [1] Seed live roots from reachable blocks (effectful/trapping insts, terminators, edges, calls):
    for (dom.rpo_blocks) |bb_idx| {
        const bb_id = MirBlockId.fromInt(bb_idx);
        for (body.getBlockParams(bb_id)) |pv| {
            is_live[pv.asInt()] = true;
        }
        for (body.getBlockInsts(bb_id)) |iv| {
            const inst = body.getInst(iv);
            if (inst.flags.has_side_effects or inst.flags.has_trap_risk or inst.op == .place_store or
                inst.op == .place_set_discrim or inst.op.isGhost())
            {
                try markSsaValLive(allocator, iv.asInt(), is_live, &worklist);
            }
        }
        const term = body.blocks.items[bb_idx].terminator;
        switch (term.kind) {
            .ret => if (term.cond_or_val != mir.NONE_U32) {
                try markSsaValLive(allocator, term.cond_or_val, is_live, &worklist);
            },
            .cond_br, .switch_int => {
                try markSsaValLive(allocator, term.cond_or_val, is_live, &worklist);
            },
            .call => {
                const cs = body.calls.items[term.cond_or_val];
                try markSsaValLive(allocator, cs.callee_val.asInt(), is_live, &worklist);
                for (0..cs.args_len) |ai| {
                    const mode = body.call_arg_modes.items[cs.modes_start + ai];
                    const word = body.extra_args.items[cs.args_start + ai];
                    if (mode == .let_mode or mode == .sink_mode) {
                        try markSsaValLive(allocator, word, is_live, &worklist);
                    } else {
                        try markPlaceIndicesLive(allocator, body, word, is_live, &worklist);
                    }
                }
                for (0..cs.call_borrows_len) |bi| {
                    try markSsaValLive(
                        allocator,
                        body.extra_args.items[cs.call_borrows_start + bi],
                        is_live,
                        &worklist,
                    );
                }
            },
            else => {},
        }
        for (body.getOutgoingEdges(bb_id)) |edge| {
            for (body.extra_args.items[edge.args_start .. edge.args_start + edge.args_len]) |ea| {
                try markSsaValLive(allocator, ea, is_live, &worklist);
            }
        }
    }

    // [2] Propagate liveness backward to operands and dynamic `MirProjection.index` values:
    while (worklist.items.len > 0) {
        const val_raw = worklist.pop().?;
        const inst = body.getInst(MirValueId.fromInt(val_raw));
        switch (inst.op) {
            .block_param, .const_scalar, .fn_addr, .ghost_storage_init, .ghost_storage_deinit => {},
            .ghost_access_let,
            .ghost_access_inout,
            .ghost_access_set,
            .ghost_storage_move,
            .place_load,
            .place_discriminant,
            .place_set_discrim,
            .place_addr,
            .soa_column_slice,
            => {
                try markPlaceIndicesLive(allocator, body, inst.operands.lhs, is_live, &worklist);
            },
            .place_store => {
                try markPlaceIndicesLive(allocator, body, inst.operands.lhs, is_live, &worklist);
                try markSsaValLive(allocator, inst.operands.rhs, is_live, &worklist);
            },
            .ghost_access_end, .copy_val, .unary_op, .aggregate_extract, .bitfield_extract => {
                try markSsaValLive(allocator, inst.operands.lhs, is_live, &worklist);
            },
            .bin_op => {
                try markSsaValLive(allocator, inst.operands.lhs, is_live, &worklist);
                try markSsaValLive(allocator, inst.operands.rhs, is_live, &worklist);
            },
            .aggregate_insert => {
                try markSsaValLive(allocator, inst.operands.lhs, is_live, &worklist);
                if (inst.operands.rhs + 2 <= body.extra_args.items.len) {
                    try markSsaValLive(allocator, body.extra_args.items[inst.operands.rhs + 1], is_live, &worklist);
                }
            },
            .bitfield_insert => {
                if (inst.operands.lhs + 2 <= body.extra_args.items.len) {
                    try markSsaValLive(allocator, body.extra_args.items[inst.operands.lhs], is_live, &worklist);
                    try markSsaValLive(allocator, body.extra_args.items[inst.operands.lhs + 1], is_live, &worklist);
                }
            },
            .aggregate_make => {
                const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                switch (agg_kind) {
                    .array_repeat => try markSsaValLive(allocator, inst.operands.lhs, is_live, &worklist),
                    .tagged_variant => {
                        const elem_len = inst.operands.rhs & 0xFFFF;
                        for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + elem_len]) |v_id| {
                            try markSsaValLive(allocator, v_id, is_live, &worklist);
                        }
                    },
                    .closure_make => {
                        const cap_len = body.extra_args.items[inst.operands.rhs];
                        const cap_start = inst.operands.rhs + 1;
                        for (body.extra_args.items[cap_start .. cap_start + cap_len]) |v_id| {
                            try markSsaValLive(allocator, v_id, is_live, &worklist);
                        }
                    },
                    .tuple_agg, .struct_agg, .array_elems, .str_concat => {
                        for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |v_id| {
                            try markSsaValLive(allocator, v_id, is_live, &worklist);
                        }
                    },
                }
            },
            .intrinsic_op => {
                if (inst.operands.rhs > 0) {
                    for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |v_id| {
                        try markSsaValLive(allocator, v_id, is_live, &worklist);
                    }
                }
            },
        }
    }

    // [3] Sweep dead instructions from `block_insts`:
    var compacted: std.ArrayListUnmanaged(MirValueId) = .empty;
    errdefer compacted.deinit(body.allocator);
    try compacted.ensureTotalCapacity(body.allocator, body.block_insts.items.len);

    for (body.blocks.items, 0..) |*bb, bb_i| {
        const old_slice = body.getBlockInsts(MirBlockId.fromInt(@intCast(bb_i)));
        const start: u32 = @intCast(compacted.items.len);
        var kept: u32 = 0;
        for (old_slice) |iv| {
            if (!is_live[iv.asInt()]) continue;
            compacted.appendAssumeCapacity(iv);
            kept += 1;
        }
        bb.inst_start = start;
        bb.inst_len = kept;
    }

    body.block_insts.deinit(body.allocator);
    body.block_insts = compacted;
}

/// Pass `R5`: `MirProjection`-aware DCE (`[CRITICAL-06]`), empty-trampoline jump-threading, and
/// single-predecessor/single-successor block merging respecting Call Continuation Split-Edge (`[CRITICAL-05]`).
fn runPassR5DceJumpThreadAndMerge(allocator: std.mem.Allocator, body: *MirBody) !void {
    if (body.blocks.items.len == 0) return;

    // [1] Run initial DCE + collapse `cond_br(c, X, args, X, args)` with identical target & args into `.br`:
    for (body.blocks.items) |*bb| {
        if (bb.terminator.kind == .cond_br and bb.terminator.edge_len == 2) {
            const e0 = body.extra_edges.items[bb.terminator.edge_start];
            const e1 = body.extra_edges.items[bb.terminator.edge_start + 1];
            if (e0.target_bb == e1.target_bb and e0.args_len == e1.args_len) {
                const a0 = body.extra_args.items[e0.args_start .. e0.args_start + e0.args_len];
                const a1 = body.extra_args.items[e1.args_start .. e1.args_start + e1.args_len];
                if (std.mem.eql(u32, a0, a1)) {
                    bb.terminator = .{
                        .kind = .br,
                        .edge_len = 1,
                        .edge_start = bb.terminator.edge_start,
                    };
                }
            }
        }
    }
    try rebuildPredsAndSweepUnreachable(allocator, body);

    // [2] Jump-thread parameterless empty trampolines (`mid_bb` not a `.call` `normal_bb` and `dst.paramLen() == 0`):
    const block_count = body.blocks.items.len;
    const is_call_normal = try allocator.alloc(bool, block_count);
    defer allocator.free(is_call_normal);
    @memset(is_call_normal, false);
    for (body.blocks.items) |bb| {
        if (bb.terminator.kind == .call and bb.terminator.edge_len >= 1) {
            const dst = body.extra_edges.items[bb.terminator.edge_start].target_bb.asInt();
            if (dst < block_count) is_call_normal[dst] = true;
        }
    }

    for (0..block_count) |src_i| {
        const src_term = body.blocks.items[src_i].terminator;
        if (src_term.kind == .call) continue; // Never redirect `.call` `normal_bb` (`[CRITICAL-05]`).
        for (0..src_term.edge_len) |off| {
            const eid = src_term.edge_start + off;
            var cur_dst = body.extra_edges.items[eid].target_bb.asInt();
            var hops: usize = 0;
            while (cur_dst != 0 and cur_dst != src_i and cur_dst < block_count and hops < 16) : (hops += 1) {
                if (is_call_normal[cur_dst]) break;
                const mid_bb = body.blocks.items[cur_dst];
                if (mid_bb.inst_len != 0 or mid_bb.paramLen() != 0 or mid_bb.terminator.kind != .br) break;
                const mid_edge = body.extra_edges.items[mid_bb.terminator.edge_start];
                if (mid_edge.args_len != 0 or mid_edge.target_bb.asInt() == cur_dst) break;
                const next_dst = mid_edge.target_bb.asInt();
                if (body.blocks.items[next_dst].paramLen() != 0 or is_call_normal[next_dst]) break;
                cur_dst = next_dst;
            }
            body.extra_edges.items[eid].target_bb = MirBlockId.fromInt(@intCast(cur_dst));
        }
    }
    try rebuildPredsAndSweepUnreachable(allocator, body);

    // [3] Merge `pred_bb --br--> succ_bb` when `succ_bb != ^bb0`, `succ_bb != pred_bb`, `succ_bb.pred_len == 1`,
    //     and `!is_call_normal[succ_bb]` (`pred_bb` may be a `.call` `normal_bb`, preserving its Split-Edge header):
    var has_merged_any = true;
    while (has_merged_any) {
        has_merged_any = false;
        var param_rewrites: std.AutoHashMapUnmanaged(u32, u32) = .empty;
        defer param_rewrites.deinit(allocator);

        for (0..body.blocks.items.len) |pred_i| {
            const pred_term = body.blocks.items[pred_i].terminator;
            if (pred_term.kind != .br or pred_term.edge_len != 1) continue;
            const br_edge = body.extra_edges.items[pred_term.edge_start];
            const succ_i = br_edge.target_bb.asInt();
            if (succ_i == 0 or succ_i == pred_i or succ_i >= body.blocks.items.len) continue;
            if (is_call_normal[succ_i]) continue;
            const succ_bb = body.blocks.items[succ_i];
            if (succ_bb.pred_len != 1) continue;

            // Bind `succ_bb`'s formal block parameters directly to `br_edge` arguments (`[MAJOR-01]`):
            const succ_params = body.getBlockParams(MirBlockId.fromInt(@intCast(succ_i)));
            if (succ_params.len != br_edge.args_len) continue;
            for (succ_params, 0..) |sp, pi| {
                const arg_raw = body.extra_args.items[br_edge.args_start + pi];
                try param_rewrites.put(allocator, sp.asInt(), arg_raw);
            }

            // Concatenate `pred_i` + `succ_i` instruction lists:
            var combined_insts: std.ArrayListUnmanaged(MirValueId) = .empty;
            defer combined_insts.deinit(allocator);
            try combined_insts.appendSlice(allocator, body.getBlockInsts(MirBlockId.fromInt(@intCast(pred_i))));
            try combined_insts.appendSlice(allocator, body.getBlockInsts(MirBlockId.fromInt(@intCast(succ_i))));

            const new_start: u32 = @intCast(body.block_insts.items.len);
            try body.block_insts.appendSlice(body.allocator, combined_insts.items);
            body.blocks.items[pred_i].inst_start = new_start;
            body.blocks.items[pred_i].inst_len = @intCast(combined_insts.items.len);

            // Adopt `succ_bb`'s terminator and re-home its outgoing edges' `src_bb` to `pred_i`:
            const succ_term = succ_bb.terminator;
            for (0..succ_term.edge_len) |off| {
                body.extra_edges.items[succ_term.edge_start + off].src_bb = MirBlockId.fromInt(@intCast(pred_i));
            }
            body.blocks.items[pred_i].terminator = succ_term;

            // Clear absorbed `succ_i`:
            body.blocks.items[succ_i].inst_len = 0;
            body.blocks.items[succ_i].setParamLen(0);
            body.blocks.items[succ_i].pred_len = 0;
            body.blocks.items[succ_i].terminator = .{ .kind = .unreachable_term };

            has_merged_any = true;
            break;
        }

        if (param_rewrites.count() > 0) {
            applyValueRewriteMap(body, &param_rewrites);
        }
        if (has_merged_any) {
            try rebuildPredsAndSweepUnreachable(allocator, body);
        }
    }

    // [4] Final DCE sweep after jump-threading & block merging:
    try eliminateDeadSsaInstructions(allocator, body);
}

// -------- Pass `R6`: `Wyhash(0)` Structural `MIR` ICF ---------

/// Computes a `Wyhash` digest of a single `MirPlace` including normalized dynamic `.index` SSA operands
/// and exact composite/variant byte offsets (`[CRITICAL-09]`, `[CRITICAL-11]`).
fn computeSinglePlaceByteDigest(
    body: *const MirBody,
    place_id: PlaceId,
    val_norm: []const u32,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    target_layout: TargetLayout,
) u64 {
    if (place_id.isNone() or place_id.asInt() >= body.places.items.len) return 0;
    const pl = body.places.items[place_id.asInt()];
    var place_hasher = std.hash.Wyhash.init(pl.base);
    const proj_count: u32 = pl.proj_len;
    place_hasher.update(std.mem.asBytes(&proj_count));
    if (pl.base >= body.locals.items.len) return place_hasher.final();

    var cur_ty = pool.unwrapUnderlyingType(body.locals.items[pl.base].type_id);
    var active_downcast: ?u32 = null;
    var active_soa_field_ty: ?TypeId = null;
    for (body.getPlaceProjections(place_id)) |proj| {
        place_hasher.update(&[_]u8{@backingInt(proj.kind)});
        const node = pool.getNode(cur_ty);
        switch (proj.kind) {
            .deref => {
                active_downcast = null;
                active_soa_field_ty = null;
                cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const deref_shape = computeLayoutShapeKey(pool, sym_table, cur_ty, target_layout);
                place_hasher.update(std.mem.asBytes(&deref_shape));
                place_hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, cur_ty, target_layout))});
            },
            .index => {
                active_downcast = null;
                const norm_idx = if (proj.payload < val_norm.len) val_norm[proj.payload] else mir.NONE_U32;
                place_hasher.update(std.mem.asBytes(&norm_idx));
                const elem_ty = if (active_soa_field_ty) |soa_f| blk: {
                    active_soa_field_ty = null;
                    break :blk soa_f;
                } else pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const elem_shape = computeLayoutShapeKey(pool, sym_table, elem_ty, target_layout);
                place_hasher.update(std.mem.asBytes(&elem_shape));
                place_hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, elem_ty, target_layout))});
                cur_ty = elem_ty;
            },
            .downcast => {
                active_soa_field_ty = null;
                active_downcast = proj.payload;
                place_hasher.update(std.mem.asBytes(&proj.payload));
            },
            .field => {
                active_soa_field_ty = null;
                if (active_downcast) |tag_ord| {
                    active_downcast = null;
                    var total_off = computeOptSumPayloadOffset(pool, sym_table, cur_ty, target_layout);
                    var pay_ty = pool.unwrapUnderlyingType(
                        resolveOptVariantPayloadType(pool, sym_table, cur_ty, tag_ord),
                    );
                    if (proj.payload > 0) {
                        if (resolveOptCompositeFieldStep(pool, sym_table, pay_ty, proj.payload, target_layout)) |sub| {
                            total_off += sub.byte_offset;
                            pay_ty = pool.unwrapUnderlyingType(sub.field_ty);
                        }
                    }
                    place_hasher.update(std.mem.asBytes(&total_off));
                    const pay_shape = computeLayoutShapeKey(pool, sym_table, pay_ty, target_layout);
                    place_hasher.update(std.mem.asBytes(&pay_shape));
                    place_hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, pay_ty, target_layout))});
                    cur_ty = pay_ty;
                } else if (resolveOptCompositeFieldStep(pool, sym_table, cur_ty, proj.payload, target_layout)) |step| {
                    place_hasher.update(std.mem.asBytes(&step.byte_offset));
                    cur_ty = pool.unwrapUnderlyingType(step.field_ty);
                    const field_shape = computeLayoutShapeKey(pool, sym_table, cur_ty, target_layout);
                    place_hasher.update(std.mem.asBytes(&field_shape));
                    place_hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, cur_ty, target_layout))});
                } else {
                    place_hasher.update(std.mem.asBytes(&proj.payload));
                }
            },
            .soa_elem => {
                active_downcast = null;
                const base_elem_ty = TypeId.fromInt(node.lhs);
                if (resolveOptCompositeFieldStep(pool, sym_table, base_elem_ty, proj.payload, target_layout)) |step| {
                    place_hasher.update(std.mem.asBytes(&step.byte_offset));
                    const col_ty = pool.unwrapUnderlyingType(step.field_ty);
                    active_soa_field_ty = col_ty;
                    const col_shape = computeLayoutShapeKey(pool, sym_table, col_ty, target_layout);
                    place_hasher.update(std.mem.asBytes(&col_shape));
                    place_hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, col_ty, target_layout))});
                } else {
                    active_soa_field_ty = null;
                    place_hasher.update(std.mem.asBytes(&proj.payload));
                }
            },
            .slice_len => {
                active_downcast = null;
                active_soa_field_ty = null;
                cur_ty = .usize_ty;
                place_hasher.update(std.mem.asBytes(&proj.payload));
            },
        }
    }
    return place_hasher.final();
}

/// Collision-free structural equality predicate for two `MirPlace`s (`[CRITICAL-11]`).
fn isPlaceStructurallyEqual(
    body_a: *const MirBody,
    place_a_id: PlaceId,
    val_a: []const u32,
    body_b: *const MirBody,
    place_b_id: PlaceId,
    val_b: []const u32,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    target_layout: TargetLayout,
) bool {
    if (place_a_id.isNone() or place_b_id.isNone()) return place_a_id.isNone() and place_b_id.isNone();
    if (place_a_id.asInt() >= body_a.places.items.len or place_b_id.asInt() >= body_b.places.items.len) {
        return false;
    }
    const pl_a = body_a.places.items[place_a_id.asInt()];
    const pl_b = body_b.places.items[place_b_id.asInt()];
    if (pl_a.base != pl_b.base or pl_a.proj_len != pl_b.proj_len) return false;
    if (pl_a.base >= body_a.locals.items.len or pl_b.base >= body_b.locals.items.len) return false;

    var cur_ty_a = pool.unwrapUnderlyingType(body_a.locals.items[pl_a.base].type_id);
    var cur_ty_b = pool.unwrapUnderlyingType(body_b.locals.items[pl_b.base].type_id);
    var down_a: ?u32 = null;
    var down_b: ?u32 = null;
    var soa_field_a: ?TypeId = null;
    var soa_field_b: ?TypeId = null;

    const projs_a = body_a.getPlaceProjections(place_a_id);
    const projs_b = body_b.getPlaceProjections(place_b_id);
    for (projs_a, projs_b) |proj_a, proj_b| {
        if (proj_a.kind != proj_b.kind) return false;
        const node_a = pool.getNode(cur_ty_a);
        const node_b = pool.getNode(cur_ty_b);
        switch (proj_a.kind) {
            .deref => {
                down_a = null;
                down_b = null;
                soa_field_a = null;
                soa_field_b = null;
                cur_ty_a = pool.unwrapUnderlyingType(TypeId.fromInt(node_a.lhs));
                cur_ty_b = pool.unwrapUnderlyingType(TypeId.fromInt(node_b.lhs));
                if (!computeLayoutShapeKey(pool, sym_table, cur_ty_a, target_layout).isEqual(
                    computeLayoutShapeKey(pool, sym_table, cur_ty_b, target_layout),
                ) or classifyOpSemantics(pool, cur_ty_a, target_layout) !=
                    classifyOpSemantics(pool, cur_ty_b, target_layout))
                {
                    return false;
                }
            },
            .index => {
                down_a = null;
                down_b = null;
                const idx_norm_a = if (proj_a.payload < val_a.len) val_a[proj_a.payload] else mir.NONE_U32;
                const idx_norm_b = if (proj_b.payload < val_b.len) val_b[proj_b.payload] else mir.NONE_U32;
                if (idx_norm_a != idx_norm_b) return false;
                cur_ty_a = if (soa_field_a) |sf_a| blk: {
                    soa_field_a = null;
                    break :blk sf_a;
                } else pool.unwrapUnderlyingType(TypeId.fromInt(node_a.lhs));
                cur_ty_b = if (soa_field_b) |sf_b| blk: {
                    soa_field_b = null;
                    break :blk sf_b;
                } else pool.unwrapUnderlyingType(TypeId.fromInt(node_b.lhs));
                if (!computeLayoutShapeKey(pool, sym_table, cur_ty_a, target_layout).isEqual(
                    computeLayoutShapeKey(pool, sym_table, cur_ty_b, target_layout),
                ) or classifyOpSemantics(pool, cur_ty_a, target_layout) !=
                    classifyOpSemantics(pool, cur_ty_b, target_layout))
                {
                    return false;
                }
            },
            .downcast => {
                soa_field_a = null;
                soa_field_b = null;
                if (proj_a.payload != proj_b.payload) return false;
                down_a = proj_a.payload;
                down_b = proj_b.payload;
            },
            .field => {
                soa_field_a = null;
                soa_field_b = null;
                if ((down_a != null) != (down_b != null)) return false;
                if (down_a) |tag_a| {
                    const tag_b = down_b.?;
                    down_a = null;
                    down_b = null;
                    if (tag_a != tag_b or proj_a.payload != proj_b.payload) return false;
                    var off_a = computeOptSumPayloadOffset(pool, sym_table, cur_ty_a, target_layout);
                    var off_b = computeOptSumPayloadOffset(pool, sym_table, cur_ty_b, target_layout);
                    var pay_a = pool.unwrapUnderlyingType(
                        resolveOptVariantPayloadType(pool, sym_table, cur_ty_a, tag_a),
                    );
                    var pay_b = pool.unwrapUnderlyingType(
                        resolveOptVariantPayloadType(pool, sym_table, cur_ty_b, tag_b),
                    );
                    if (proj_a.payload > 0) {
                        const sub_a = resolveOptCompositeFieldStep(pool, sym_table, pay_a, proj_a.payload, target_layout) orelse
                            return false;
                        const sub_b = resolveOptCompositeFieldStep(pool, sym_table, pay_b, proj_b.payload, target_layout) orelse
                            return false;
                        off_a += sub_a.byte_offset;
                        off_b += sub_b.byte_offset;
                        pay_a = pool.unwrapUnderlyingType(sub_a.field_ty);
                        pay_b = pool.unwrapUnderlyingType(sub_b.field_ty);
                    }
                    if (off_a != off_b) return false;
                    if (!computeLayoutShapeKey(pool, sym_table, pay_a, target_layout).isEqual(
                        computeLayoutShapeKey(pool, sym_table, pay_b, target_layout),
                    ) or classifyOpSemantics(pool, pay_a, target_layout) !=
                        classifyOpSemantics(pool, pay_b, target_layout))
                    {
                        return false;
                    }
                    cur_ty_a = pay_a;
                    cur_ty_b = pay_b;
                } else {
                    const step_a = resolveOptCompositeFieldStep(pool, sym_table, cur_ty_a, proj_a.payload, target_layout);
                    const step_b = resolveOptCompositeFieldStep(pool, sym_table, cur_ty_b, proj_b.payload, target_layout);
                    if ((step_a != null) != (step_b != null)) return false;
                    if (step_a) |fa| {
                        const fb = step_b.?;
                        if (fa.byte_offset != fb.byte_offset) return false;
                        cur_ty_a = pool.unwrapUnderlyingType(fa.field_ty);
                        cur_ty_b = pool.unwrapUnderlyingType(fb.field_ty);
                        if (!computeLayoutShapeKey(pool, sym_table, cur_ty_a, target_layout).isEqual(
                            computeLayoutShapeKey(pool, sym_table, cur_ty_b, target_layout),
                        ) or classifyOpSemantics(pool, cur_ty_a, target_layout) !=
                            classifyOpSemantics(pool, cur_ty_b, target_layout))
                        {
                            return false;
                        }
                    } else if (proj_a.payload != proj_b.payload) {
                        return false;
                    }
                }
            },
            .soa_elem => {
                down_a = null;
                down_b = null;
                if (proj_a.payload != proj_b.payload) return false;
                const step_a = resolveOptCompositeFieldStep(
                    pool,
                    sym_table,
                    TypeId.fromInt(node_a.lhs),
                    proj_a.payload,
                    target_layout,
                );
                const step_b = resolveOptCompositeFieldStep(
                    pool,
                    sym_table,
                    TypeId.fromInt(node_b.lhs),
                    proj_b.payload,
                    target_layout,
                );
                if ((step_a != null) != (step_b != null)) return false;
                if (step_a) |fa| {
                    const fb = step_b.?;
                    if (fa.byte_offset != fb.byte_offset) return false;
                    const col_a = pool.unwrapUnderlyingType(fa.field_ty);
                    const col_b = pool.unwrapUnderlyingType(fb.field_ty);
                    soa_field_a = col_a;
                    soa_field_b = col_b;
                    if (!computeLayoutShapeKey(pool, sym_table, col_a, target_layout).isEqual(
                        computeLayoutShapeKey(pool, sym_table, col_b, target_layout),
                    ) or classifyOpSemantics(pool, col_a, target_layout) !=
                        classifyOpSemantics(pool, col_b, target_layout))
                    {
                        return false;
                    }
                } else {
                    soa_field_a = null;
                    soa_field_b = null;
                }
            },
            .slice_len => {
                down_a = null;
                down_b = null;
                soa_field_a = null;
                soa_field_b = null;
                if (proj_a.payload != proj_b.payload) return false;
                cur_ty_a = .usize_ty;
                cur_ty_b = .usize_ty;
            },
        }
    }
    return true;
}

/// Computes an alpha-normalized 64-bit `Wyhash(0)` structural digest of `body` (`R6` & Early Cutoff).
pub fn computeMirBodyStructuralHash(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    target_layout: TargetLayout,
) !u64 {
    return computeMirBodyStructuralHashWithInterner(
        allocator,
        body,
        pool,
        sym_table,
        null,
        target_layout,
    );
}

/// Computes an alpha-normalized 64-bit `Wyhash(0)` structural digest of `body` with canonical string resolution.
fn computeMirBodyStructuralHashWithInterner(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner: ?*const StringInterner,
    target_layout: TargetLayout,
) !u64 {
    var hasher = std.hash.Wyhash.init(0);
    hasher.update(std.mem.asBytes(&body.param_count));
    hasher.update(&[_]u8{
        @intFromBool(body.is_contextless),
        @intFromBool(body.is_ghost_stripped),
        target_layout.ptr_byte_size,
    });
    const ret_shape = computeLayoutShapeKey(pool, sym_table, body.ret_ty, target_layout);
    hasher.update(std.mem.asBytes(&ret_shape));
    hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, body.ret_ty, target_layout))});

    for (body.locals.items) |loc| {
        const loc_shape = computeLayoutShapeKey(pool, sym_table, loc.type_id, target_layout);
        hasher.update(std.mem.asBytes(&loc_shape));
        hasher.update(&[_]u8{
            loc.mode_raw,
            @backingInt(classifyOpSemantics(pool, loc.type_id, target_layout)),
        });
    }

    if (body.blocks.items.len == 0) return hasher.final();

    var dom = try mir.computeDominators(allocator, body);
    defer dom.deinit();

    const val_norm = try allocator.alloc(u32, body.insts.len);
    defer allocator.free(val_norm);
    @memset(val_norm, mir.NONE_U32);
    var next_val_ord: u32 = 0;

    const bb_norm = try allocator.alloc(u32, body.blocks.items.len);
    defer allocator.free(bb_norm);
    @memset(bb_norm, mir.NONE_U32);
    for (dom.rpo_blocks, 0..) |bb_idx, ord| {
        bb_norm[bb_idx] = @intCast(ord);
        const bb_id = MirBlockId.fromInt(bb_idx);
        for (body.getBlockParams(bb_id)) |pv| {
            val_norm[pv.asInt()] = next_val_ord;
            next_val_ord += 1;
        }
        for (body.getBlockInsts(bb_id)) |iv| {
            val_norm[iv.asInt()] = next_val_ord;
            next_val_ord += 1;
        }
    }

    for (dom.rpo_blocks) |bb_idx| {
        const bb_id = MirBlockId.fromInt(bb_idx);
        const p_len: u32 = body.blocks.items[bb_idx].paramLen();
        const i_len: u32 = body.blocks.items[bb_idx].inst_len;
        hasher.update(std.mem.asBytes(&p_len));
        hasher.update(std.mem.asBytes(&i_len));

        for (body.getBlockParams(bb_id)) |pv| {
            const param_ty = body.getInst(pv).type_id;
            const param_shape = computeLayoutShapeKey(pool, sym_table, param_ty, target_layout);
            hasher.update(std.mem.asBytes(&param_shape));
            hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, param_ty, target_layout))});
        }

        for (body.getBlockInsts(bb_id)) |iv| {
            const inst = body.getInst(iv);
            hasher.update(&[_]u8{
                @backingInt(inst.op),
                @bitCast(inst.flags),
                @backingInt(classifyOpSemantics(pool, inst.type_id, target_layout)),
            });
            hasher.update(std.mem.asBytes(&inst.aux_u16));
            const inst_shape = computeLayoutShapeKey(pool, sym_table, inst.type_id, target_layout);
            hasher.update(std.mem.asBytes(&inst_shape));

            switch (inst.op) {
                .block_param => {
                    const nb = if (inst.operands.lhs < bb_norm.len) bb_norm[inst.operands.lhs] else mir.NONE_U32;
                    hasher.update(std.mem.asBytes(&nb));
                    hasher.update(std.mem.asBytes(&inst.operands.rhs));
                },
                .const_scalar => {
                    if (inst.operands.lhs < body.consts.items.len) {
                        const mc = body.consts.items[inst.operands.lhs];
                        hasher.update(&[_]u8{@intFromEnum(mc)});
                        switch (mc) {
                            .unit_val => {},
                            .bool_val => |bv| hasher.update(&[_]u8{@intFromBool(bv)}),
                            .char_val => |cv| hasher.update(std.mem.asBytes(&cv)),
                            .int_val => |iv_c| hasher.update(std.mem.asBytes(&iv_c)),
                            .float_val => |fv| {
                                const bits: u64 = @bitCast(fv);
                                hasher.update(std.mem.asBytes(&bits));
                            },
                            .str_val => |sv| {
                                if (interner) |str_pool| {
                                    const str_bytes = str_pool.get(sv);
                                    const str_len: u32 = @intCast(str_bytes.len);
                                    hasher.update(std.mem.asBytes(&str_len));
                                    hasher.update(str_bytes);
                                } else {
                                    hasher.update(std.mem.asBytes(&sv));
                                }
                            },
                            .bytes_val => |bv| {
                                if (interner) |str_pool| {
                                    const raw_bytes = str_pool.get(bv);
                                    const raw_len: u32 = @intCast(raw_bytes.len);
                                    hasher.update(std.mem.asBytes(&raw_len));
                                    hasher.update(raw_bytes);
                                } else {
                                    hasher.update(std.mem.asBytes(&bv));
                                }
                            },
                        }
                    }
                },
                .bin_op => {
                    const nl = if (inst.operands.lhs < val_norm.len) val_norm[inst.operands.lhs] else mir.NONE_U32;
                    const nr = if (inst.operands.rhs < val_norm.len) val_norm[inst.operands.rhs] else mir.NONE_U32;
                    hasher.update(std.mem.asBytes(&nl));
                    hasher.update(std.mem.asBytes(&nr));
                },
                .copy_val, .unary_op, .bitfield_extract, .ghost_access_end => {
                    const nl = if (inst.operands.lhs < val_norm.len) val_norm[inst.operands.lhs] else mir.NONE_U32;
                    hasher.update(std.mem.asBytes(&nl));
                    hasher.update(std.mem.asBytes(&inst.operands.rhs));
                },
                .aggregate_extract => {
                    const nl = if (inst.operands.lhs < val_norm.len) val_norm[inst.operands.lhs] else mir.NONE_U32;
                    hasher.update(std.mem.asBytes(&nl));
                    hasher.update(std.mem.asBytes(&inst.operands.rhs));
                    if (inst.operands.lhs < body.insts.len) {
                        const base_ty = body.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id;
                        if (resolveOptCompositeFieldStep(pool, sym_table, base_ty, inst.operands.rhs, target_layout)) |step| {
                            hasher.update(std.mem.asBytes(&step.byte_offset));
                        }
                    }
                },
                .aggregate_insert => {
                    const nl = if (inst.operands.lhs < val_norm.len) val_norm[inst.operands.lhs] else mir.NONE_U32;
                    hasher.update(std.mem.asBytes(&nl));
                    if (inst.operands.rhs + 2 <= body.extra_args.items.len) {
                        const ord = body.extra_args.items[inst.operands.rhs];
                        const elem_raw = body.extra_args.items[inst.operands.rhs + 1];
                        const ne = if (elem_raw < val_norm.len) val_norm[elem_raw] else mir.NONE_U32;
                        hasher.update(std.mem.asBytes(&ord));
                        hasher.update(std.mem.asBytes(&ne));
                        if (resolveOptCompositeFieldStep(pool, sym_table, inst.type_id, ord, target_layout)) |step| {
                            hasher.update(std.mem.asBytes(&step.byte_offset));
                            const f_shape = computeLayoutShapeKey(pool, sym_table, step.field_ty, target_layout);
                            hasher.update(std.mem.asBytes(&f_shape));
                        }
                    }
                },
                .bitfield_insert => {
                    hasher.update(std.mem.asBytes(&inst.operands.rhs));
                    if (inst.operands.lhs + 2 <= body.extra_args.items.len) {
                        const base_raw = body.extra_args.items[inst.operands.lhs];
                        const val_raw = body.extra_args.items[inst.operands.lhs + 1];
                        const nb = if (base_raw < val_norm.len) val_norm[base_raw] else mir.NONE_U32;
                        const nv = if (val_raw < val_norm.len) val_norm[val_raw] else mir.NONE_U32;
                        hasher.update(std.mem.asBytes(&nb));
                        hasher.update(std.mem.asBytes(&nv));
                    }
                },
                .aggregate_make => {
                    const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                    switch (agg_kind) {
                        .array_repeat => {
                            const nl = if (inst.operands.lhs < val_norm.len) val_norm[inst.operands.lhs] else mir.NONE_U32;
                            hasher.update(std.mem.asBytes(&nl));
                            hasher.update(std.mem.asBytes(&inst.operands.rhs));
                        },
                        .tagged_variant => {
                            const tag_ord: u32 = inst.operands.rhs >> 16;
                            const elem_len: u32 = inst.operands.rhs & 0xFFFF;
                            const pay_off = computeOptSumPayloadOffset(pool, sym_table, inst.type_id, target_layout);
                            const pay_ty = resolveOptVariantPayloadType(pool, sym_table, inst.type_id, tag_ord);
                            const pay_shape = computeLayoutShapeKey(pool, sym_table, pay_ty, target_layout);
                            hasher.update(std.mem.asBytes(&tag_ord));
                            hasher.update(std.mem.asBytes(&elem_len));
                            hasher.update(std.mem.asBytes(&pay_off));
                            hasher.update(std.mem.asBytes(&pay_shape));
                            if (inst.operands.lhs + elem_len <= body.extra_args.items.len) {
                                for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + elem_len]) |v_raw| {
                                    const nv = if (v_raw < val_norm.len) val_norm[v_raw] else mir.NONE_U32;
                                    hasher.update(std.mem.asBytes(&nv));
                                }
                            }
                        },
                        .closure_make => {
                            hasher.update(std.mem.asBytes(&inst.operands.lhs));
                            if (inst.operands.rhs < body.extra_args.items.len) {
                                const cap_len = body.extra_args.items[inst.operands.rhs];
                                const cap_start = inst.operands.rhs + 1;
                                hasher.update(std.mem.asBytes(&cap_len));
                                if (cap_start + cap_len <= body.extra_args.items.len) {
                                    for (body.extra_args.items[cap_start .. cap_start + cap_len]) |v_raw| {
                                        const nv = if (v_raw < val_norm.len) val_norm[v_raw] else mir.NONE_U32;
                                        hasher.update(std.mem.asBytes(&nv));
                                    }
                                }
                            }
                        },
                        .tuple_agg, .struct_agg => {
                            hasher.update(std.mem.asBytes(&inst.operands.rhs));
                            if (inst.operands.lhs + inst.operands.rhs <= body.extra_args.items.len) {
                                for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs], 0..) |v_raw, f_idx| {
                                    const nv = if (v_raw < val_norm.len) val_norm[v_raw] else mir.NONE_U32;
                                    hasher.update(std.mem.asBytes(&nv));
                                    if (resolveOptCompositeFieldStep(
                                        pool,
                                        sym_table,
                                        inst.type_id,
                                        @intCast(f_idx),
                                        target_layout,
                                    )) |step| {
                                        const f_shape = computeLayoutShapeKey(pool, sym_table, step.field_ty, target_layout);
                                        hasher.update(std.mem.asBytes(&step.byte_offset));
                                        hasher.update(std.mem.asBytes(&f_shape));
                                        hasher.update(&[_]u8{@backingInt(classifyOpSemantics(pool, step.field_ty, target_layout))});
                                    }
                                }
                            }
                        },
                        .array_elems, .str_concat => {
                            hasher.update(std.mem.asBytes(&inst.operands.rhs));
                            if (inst.operands.lhs + inst.operands.rhs <= body.extra_args.items.len) {
                                for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |v_raw| {
                                    const nv = if (v_raw < val_norm.len) val_norm[v_raw] else mir.NONE_U32;
                                    hasher.update(std.mem.asBytes(&nv));
                                }
                            }
                        },
                    }
                },
                .intrinsic_op => {
                    const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                    hasher.update(std.mem.asBytes(&inst.operands.rhs));
                    if (inst.operands.rhs == 0) {
                        const ty_arg = TypeId.fromInt(inst.operands.lhs);
                        switch (ikind) {
                            .size_of, .align_of => {
                                const lay = type_system.computeTypeLayoutWithPool(pool, sym_table, ty_arg, target_layout);
                                hasher.update(std.mem.asBytes(&lay.byte_size));
                                hasher.update(std.mem.asBytes(&lay.align_bytes));
                            },
                            .type_name => {
                                var tbuf: [512]u8 = undefined;
                                hasher.update(pool.formatType(ty_arg, sym_table, &tbuf));
                            },
                            else => hasher.update(std.mem.asBytes(&inst.operands.lhs)),
                        }
                    } else if (inst.operands.lhs + inst.operands.rhs <= body.extra_args.items.len) {
                        for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |v_raw| {
                            const nv = if (v_raw < val_norm.len) val_norm[v_raw] else mir.NONE_U32;
                            hasher.update(std.mem.asBytes(&nv));
                        }
                        if (ikind == .derive_debug_fmt) {
                            const first_raw = body.extra_args.items[inst.operands.lhs];
                            if (first_raw < body.insts.len) {
                                const arg_ty = body.getInst(MirValueId.fromInt(first_raw)).type_id;
                                var tbuf: [512]u8 = undefined;
                                hasher.update(pool.formatType(arg_ty, sym_table, &tbuf));
                            }
                        }
                    }
                },
                .place_load,
                .place_discriminant,
                .place_set_discrim,
                .place_addr,
                .soa_column_slice,
                .ghost_access_let,
                .ghost_access_inout,
                .ghost_access_set,
                .ghost_storage_move,
                => {
                    const pdig = computeSinglePlaceByteDigest(
                        body,
                        PlaceId.fromInt(inst.operands.lhs),
                        val_norm,
                        pool,
                        sym_table,
                        target_layout,
                    );
                    hasher.update(std.mem.asBytes(&pdig));
                    hasher.update(std.mem.asBytes(&inst.operands.rhs));
                },
                .place_store => {
                    const pdig = computeSinglePlaceByteDigest(
                        body,
                        PlaceId.fromInt(inst.operands.lhs),
                        val_norm,
                        pool,
                        sym_table,
                        target_layout,
                    );
                    const nr = if (inst.operands.rhs < val_norm.len) val_norm[inst.operands.rhs] else mir.NONE_U32;
                    hasher.update(std.mem.asBytes(&pdig));
                    hasher.update(std.mem.asBytes(&nr));
                },
                .fn_addr => {
                    hashCalleeTargetCanonical(
                        &hasher,
                        inst.operands.lhs,
                        inst.operands.rhs,
                        sym_table,
                        interner,
                    );
                },
                .ghost_storage_init, .ghost_storage_deinit => {
                    hasher.update(std.mem.asBytes(&inst.operands.lhs));
                    hasher.update(std.mem.asBytes(&inst.operands.rhs));
                },
            }
        }

        const term = body.blocks.items[bb_idx].terminator;
        hasher.update(&[_]u8{ @backingInt(term.kind), term.aux_u8 });
        hasher.update(std.mem.asBytes(&term.edge_len));
        if (term.kind == .call) {
            const cs = body.calls.items[term.cond_or_val];
            const callee_norm = if (!cs.callee_val.isNone() and cs.callee_val.asInt() < val_norm.len)
                val_norm[cs.callee_val.asInt()]
            else
                mir.NONE_U32;
            const cs_ret_shape = computeLayoutShapeKey(pool, sym_table, cs.ret_ty, target_layout);
            hashCalleeTargetCanonical(
                &hasher,
                cs.direct_def_id.asInt(),
                cs.direct_symbol.asInt(),
                sym_table,
                interner,
            );
            hasher.update(std.mem.asBytes(&callee_norm));
            hasher.update(&[_]u8{
                @intFromBool(cs.is_callee_contextless),
                @backingInt(classifyOpSemantics(pool, cs.ret_ty, target_layout)),
            });
            hasher.update(std.mem.asBytes(&cs_ret_shape));
            hasher.update(std.mem.asBytes(&cs.args_len));
            for (0..cs.args_len) |arg_i| {
                const arg_mode = body.call_arg_modes.items[cs.modes_start + arg_i];
                const arg_word = body.extra_args.items[cs.args_start + arg_i];
                hasher.update(&[_]u8{@backingInt(arg_mode)});
                if (arg_mode == .let_mode or arg_mode == .sink_mode) {
                    const na = if (arg_word < val_norm.len) val_norm[arg_word] else mir.NONE_U32;
                    hasher.update(std.mem.asBytes(&na));
                } else {
                    const pdig = computeSinglePlaceByteDigest(
                        body,
                        PlaceId.fromInt(arg_word),
                        val_norm,
                        pool,
                        sym_table,
                        target_layout,
                    );
                    hasher.update(std.mem.asBytes(&pdig));
                }
            }
            hasher.update(std.mem.asBytes(&cs.call_borrows_len));
            for (0..cs.call_borrows_len) |bor_i| {
                const bor_word = body.extra_args.items[cs.call_borrows_start + bor_i];
                const nb = if (bor_word < val_norm.len) val_norm[bor_word] else mir.NONE_U32;
                hasher.update(std.mem.asBytes(&nb));
            }
        } else if (term.cond_or_val < val_norm.len) {
            const nc = val_norm[term.cond_or_val];
            hasher.update(std.mem.asBytes(&nc));
        }
        for (body.getOutgoingEdges(bb_id)) |edge| {
            const ndst = if (edge.target_bb.asInt() < bb_norm.len) bb_norm[edge.target_bb.asInt()] else mir.NONE_U32;
            hasher.update(std.mem.asBytes(&ndst));
            for (body.extra_args.items[edge.args_start .. edge.args_start + edge.args_len]) |ea| {
                const na = if (ea < val_norm.len) val_norm[ea] else mir.NONE_U32;
                hasher.update(std.mem.asBytes(&na));
            }
        }
    }

    return hasher.final();
}

/// Deterministic collision-free structural comparator guarding `D5` & `R6` ICF (`[CRITICAL-09]`, `[CRITICAL-11]`).
pub fn isMirBodyStructurallyEqual(
    allocator: std.mem.Allocator,
    body_a: *const MirBody,
    body_b: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    target_layout: TargetLayout,
) !bool {
    if (body_a.param_count != body_b.param_count or
        body_a.is_contextless != body_b.is_contextless or
        body_a.is_ghost_stripped != body_b.is_ghost_stripped or
        body_a.locals.items.len != body_b.locals.items.len)
    {
        return false;
    }
    if (!computeLayoutShapeKey(pool, sym_table, body_a.ret_ty, target_layout).isEqual(
        computeLayoutShapeKey(pool, sym_table, body_b.ret_ty, target_layout),
    ) or classifyOpSemantics(pool, body_a.ret_ty, target_layout) !=
        classifyOpSemantics(pool, body_b.ret_ty, target_layout))
    {
        return false;
    }

    for (body_a.locals.items, body_b.locals.items) |loc_a, loc_b| {
        if (loc_a.mode_raw != loc_b.mode_raw or
            !computeLayoutShapeKey(pool, sym_table, loc_a.type_id, target_layout).isEqual(
                computeLayoutShapeKey(pool, sym_table, loc_b.type_id, target_layout),
            ) or
            classifyOpSemantics(pool, loc_a.type_id, target_layout) !=
                classifyOpSemantics(pool, loc_b.type_id, target_layout))
        {
            return false;
        }
    }

    if (body_a.blocks.items.len == 0 or body_b.blocks.items.len == 0) {
        return body_a.blocks.items.len == body_b.blocks.items.len;
    }

    var dom_a = try mir.computeDominators(allocator, body_a);
    defer dom_a.deinit();
    var dom_b = try mir.computeDominators(allocator, body_b);
    defer dom_b.deinit();
    if (dom_a.rpo_blocks.len != dom_b.rpo_blocks.len) return false;

    const val_a = try allocator.alloc(u32, body_a.insts.len);
    defer allocator.free(val_a);
    @memset(val_a, mir.NONE_U32);
    const val_b = try allocator.alloc(u32, body_b.insts.len);
    defer allocator.free(val_b);
    @memset(val_b, mir.NONE_U32);

    const bb_a = try allocator.alloc(u32, body_a.blocks.items.len);
    defer allocator.free(bb_a);
    @memset(bb_a, mir.NONE_U32);
    const bb_b = try allocator.alloc(u32, body_b.blocks.items.len);
    defer allocator.free(bb_b);
    @memset(bb_b, mir.NONE_U32);

    var ord_val: u32 = 0;
    for (dom_a.rpo_blocks, dom_b.rpo_blocks, 0..) |idx_a, idx_b, b_ord| {
        bb_a[idx_a] = @intCast(b_ord);
        bb_b[idx_b] = @intCast(b_ord);
        const pa = body_a.getBlockParams(MirBlockId.fromInt(idx_a));
        const pb = body_b.getBlockParams(MirBlockId.fromInt(idx_b));
        const ia = body_a.getBlockInsts(MirBlockId.fromInt(idx_a));
        const ib = body_b.getBlockInsts(MirBlockId.fromInt(idx_b));
        if (pa.len != pb.len or ia.len != ib.len) return false;
        for (pa, pb) |va, vb| {
            const param_ty_a = body_a.getInst(va).type_id;
            const param_ty_b = body_b.getInst(vb).type_id;
            if (!computeLayoutShapeKey(pool, sym_table, param_ty_a, target_layout).isEqual(
                computeLayoutShapeKey(pool, sym_table, param_ty_b, target_layout),
            ) or classifyOpSemantics(pool, param_ty_a, target_layout) !=
                classifyOpSemantics(pool, param_ty_b, target_layout))
            {
                return false;
            }
            val_a[va.asInt()] = ord_val;
            val_b[vb.asInt()] = ord_val;
            ord_val += 1;
        }
        for (ia, ib) |va, vb| {
            val_a[va.asInt()] = ord_val;
            val_b[vb.asInt()] = ord_val;
            ord_val += 1;
        }
    }

    for (dom_a.rpo_blocks, dom_b.rpo_blocks) |idx_a, idx_b| {
        const ia = body_a.getBlockInsts(MirBlockId.fromInt(idx_a));
        const ib = body_b.getBlockInsts(MirBlockId.fromInt(idx_b));
        for (ia, ib) |va, vb| {
            const inst_a = body_a.getInst(va);
            const inst_b = body_b.getInst(vb);
            if (inst_a.op != inst_b.op or
                @as(u8, @bitCast(inst_a.flags)) != @as(u8, @bitCast(inst_b.flags)) or
                inst_a.aux_u16 != inst_b.aux_u16)
            {
                return false;
            }
            if (!computeLayoutShapeKey(pool, sym_table, inst_a.type_id, target_layout).isEqual(
                computeLayoutShapeKey(pool, sym_table, inst_b.type_id, target_layout),
            ) or classifyOpSemantics(pool, inst_a.type_id, target_layout) !=
                classifyOpSemantics(pool, inst_b.type_id, target_layout))
            {
                return false;
            }

            switch (inst_a.op) {
                .block_param => {
                    if (inst_a.operands.lhs >= bb_a.len or inst_b.operands.lhs >= bb_b.len) return false;
                    if (bb_a[inst_a.operands.lhs] != bb_b[inst_b.operands.lhs] or
                        inst_a.operands.rhs != inst_b.operands.rhs) return false;
                },
                .const_scalar => {
                    if (inst_a.operands.lhs >= body_a.consts.items.len or
                        inst_b.operands.lhs >= body_b.consts.items.len) return false;
                    if (!isMirConstExactEqual(
                        body_a.consts.items[inst_a.operands.lhs],
                        body_b.consts.items[inst_b.operands.lhs],
                    )) return false;
                },
                .bin_op => {
                    if (val_a[inst_a.operands.lhs] != val_b[inst_b.operands.lhs] or
                        val_a[inst_a.operands.rhs] != val_b[inst_b.operands.rhs]) return false;
                },
                .copy_val, .unary_op, .bitfield_extract, .ghost_access_end => {
                    if (val_a[inst_a.operands.lhs] != val_b[inst_b.operands.lhs] or
                        inst_a.operands.rhs != inst_b.operands.rhs) return false;
                },
                .aggregate_extract => {
                    if (val_a[inst_a.operands.lhs] != val_b[inst_b.operands.lhs] or
                        inst_a.operands.rhs != inst_b.operands.rhs) return false;
                    const base_ty_a = body_a.getInst(MirValueId.fromInt(inst_a.operands.lhs)).type_id;
                    const base_ty_b = body_b.getInst(MirValueId.fromInt(inst_b.operands.lhs)).type_id;
                    const step_a = resolveOptCompositeFieldStep(pool, sym_table, base_ty_a, inst_a.operands.rhs, target_layout);
                    const step_b = resolveOptCompositeFieldStep(pool, sym_table, base_ty_b, inst_b.operands.rhs, target_layout);
                    if ((step_a != null) != (step_b != null)) return false;
                    if (step_a != null and step_a.?.byte_offset != step_b.?.byte_offset) return false;
                },
                .aggregate_insert => {
                    if (val_a[inst_a.operands.lhs] != val_b[inst_b.operands.lhs]) return false;
                    if (inst_a.operands.rhs + 2 > body_a.extra_args.items.len or
                        inst_b.operands.rhs + 2 > body_b.extra_args.items.len) return false;
                    const ord_a = body_a.extra_args.items[inst_a.operands.rhs];
                    const ord_b = body_b.extra_args.items[inst_b.operands.rhs];
                    const elem_a = body_a.extra_args.items[inst_a.operands.rhs + 1];
                    const elem_b = body_b.extra_args.items[inst_b.operands.rhs + 1];
                    if (ord_a != ord_b or val_a[elem_a] != val_b[elem_b]) return false;
                    const step_a = resolveOptCompositeFieldStep(pool, sym_table, inst_a.type_id, ord_a, target_layout);
                    const step_b = resolveOptCompositeFieldStep(pool, sym_table, inst_b.type_id, ord_b, target_layout);
                    if ((step_a != null) != (step_b != null)) return false;
                    if (step_a) |fa| {
                        const fb = step_b.?;
                        if (fa.byte_offset != fb.byte_offset or
                            !computeLayoutShapeKey(pool, sym_table, fa.field_ty, target_layout).isEqual(
                                computeLayoutShapeKey(pool, sym_table, fb.field_ty, target_layout),
                            )) return false;
                    }
                },
                .bitfield_insert => {
                    if (inst_a.operands.rhs != inst_b.operands.rhs) return false;
                    if (inst_a.operands.lhs + 2 > body_a.extra_args.items.len or
                        inst_b.operands.lhs + 2 > body_b.extra_args.items.len) return false;
                    const base_a = body_a.extra_args.items[inst_a.operands.lhs];
                    const base_b = body_b.extra_args.items[inst_b.operands.lhs];
                    const fv_a = body_a.extra_args.items[inst_a.operands.lhs + 1];
                    const fv_b = body_b.extra_args.items[inst_b.operands.lhs + 1];
                    if (val_a[base_a] != val_b[base_b] or val_a[fv_a] != val_b[fv_b]) return false;
                },
                .aggregate_make => {
                    const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst_a.aux_u16))));
                    switch (agg_kind) {
                        .array_repeat => {
                            if (val_a[inst_a.operands.lhs] != val_b[inst_b.operands.lhs] or
                                inst_a.operands.rhs != inst_b.operands.rhs) return false;
                        },
                        .tagged_variant => {
                            if (inst_a.operands.rhs != inst_b.operands.rhs) return false;
                            const tag_ord: u32 = inst_a.operands.rhs >> 16;
                            const elem_len: u32 = inst_a.operands.rhs & 0xFFFF;
                            const off_a = computeOptSumPayloadOffset(pool, sym_table, inst_a.type_id, target_layout);
                            const off_b = computeOptSumPayloadOffset(pool, sym_table, inst_b.type_id, target_layout);
                            if (off_a != off_b) return false;
                            const pay_a = resolveOptVariantPayloadType(pool, sym_table, inst_a.type_id, tag_ord);
                            const pay_b = resolveOptVariantPayloadType(pool, sym_table, inst_b.type_id, tag_ord);
                            if (!computeLayoutShapeKey(pool, sym_table, pay_a, target_layout).isEqual(
                                computeLayoutShapeKey(pool, sym_table, pay_b, target_layout),
                            ) or classifyOpSemantics(pool, pay_a, target_layout) !=
                                classifyOpSemantics(pool, pay_b, target_layout))
                            {
                                return false;
                            }
                            if (inst_a.operands.lhs + elem_len > body_a.extra_args.items.len or
                                inst_b.operands.lhs + elem_len > body_b.extra_args.items.len) return false;
                            for (0..elem_len) |elem_i| {
                                const ea = body_a.extra_args.items[inst_a.operands.lhs + elem_i];
                                const eb = body_b.extra_args.items[inst_b.operands.lhs + elem_i];
                                if (val_a[ea] != val_b[eb]) return false;
                            }
                        },
                        .closure_make => {
                            if (inst_a.operands.lhs != inst_b.operands.lhs) return false;
                            if (inst_a.operands.rhs >= body_a.extra_args.items.len or
                                inst_b.operands.rhs >= body_b.extra_args.items.len) return false;
                            const cap_len_a = body_a.extra_args.items[inst_a.operands.rhs];
                            const cap_len_b = body_b.extra_args.items[inst_b.operands.rhs];
                            if (cap_len_a != cap_len_b) return false;
                            const start_a = inst_a.operands.rhs + 1;
                            const start_b = inst_b.operands.rhs + 1;
                            if (start_a + cap_len_a > body_a.extra_args.items.len or
                                start_b + cap_len_b > body_b.extra_args.items.len) return false;
                            for (0..cap_len_a) |cap_i| {
                                const ca = body_a.extra_args.items[start_a + cap_i];
                                const cb = body_b.extra_args.items[start_b + cap_i];
                                if (val_a[ca] != val_b[cb]) return false;
                            }
                        },
                        .tuple_agg, .struct_agg => {
                            if (inst_a.operands.rhs != inst_b.operands.rhs) return false;
                            const elem_len = inst_a.operands.rhs;
                            if (inst_a.operands.lhs + elem_len > body_a.extra_args.items.len or
                                inst_b.operands.lhs + elem_len > body_b.extra_args.items.len) return false;
                            for (0..elem_len) |f_idx| {
                                const ea = body_a.extra_args.items[inst_a.operands.lhs + f_idx];
                                const eb = body_b.extra_args.items[inst_b.operands.lhs + f_idx];
                                if (val_a[ea] != val_b[eb]) return false;
                                const step_a = resolveOptCompositeFieldStep(
                                    pool,
                                    sym_table,
                                    inst_a.type_id,
                                    @intCast(f_idx),
                                    target_layout,
                                );
                                const step_b = resolveOptCompositeFieldStep(
                                    pool,
                                    sym_table,
                                    inst_b.type_id,
                                    @intCast(f_idx),
                                    target_layout,
                                );
                                if ((step_a != null) != (step_b != null)) return false;
                                if (step_a) |fa| {
                                    const fb = step_b.?;
                                    if (fa.byte_offset != fb.byte_offset or
                                        !computeLayoutShapeKey(pool, sym_table, fa.field_ty, target_layout).isEqual(
                                            computeLayoutShapeKey(pool, sym_table, fb.field_ty, target_layout),
                                        ) or
                                        classifyOpSemantics(pool, fa.field_ty, target_layout) !=
                                            classifyOpSemantics(pool, fb.field_ty, target_layout))
                                    {
                                        return false;
                                    }
                                }
                            }
                        },
                        .array_elems, .str_concat => {
                            if (inst_a.operands.rhs != inst_b.operands.rhs) return false;
                            const elem_len = inst_a.operands.rhs;
                            if (inst_a.operands.lhs + elem_len > body_a.extra_args.items.len or
                                inst_b.operands.lhs + elem_len > body_b.extra_args.items.len) return false;
                            for (0..elem_len) |elem_i| {
                                const ea = body_a.extra_args.items[inst_a.operands.lhs + elem_i];
                                const eb = body_b.extra_args.items[inst_b.operands.lhs + elem_i];
                                if (val_a[ea] != val_b[eb]) return false;
                            }
                        },
                    }
                },
                .intrinsic_op => {
                    if (inst_a.operands.rhs != inst_b.operands.rhs) return false;
                    const ikind: MirIntrinsicKind = @fromBackingInt(inst_a.aux_u16);
                    if (inst_a.operands.rhs == 0) {
                        const ty_a = TypeId.fromInt(inst_a.operands.lhs);
                        const ty_b = TypeId.fromInt(inst_b.operands.lhs);
                        switch (ikind) {
                            .size_of => {
                                const lay_a = type_system.computeTypeLayoutWithPool(pool, sym_table, ty_a, target_layout);
                                const lay_b = type_system.computeTypeLayoutWithPool(pool, sym_table, ty_b, target_layout);
                                if (lay_a.byte_size != lay_b.byte_size) return false;
                            },
                            .align_of => {
                                const lay_a = type_system.computeTypeLayoutWithPool(pool, sym_table, ty_a, target_layout);
                                const lay_b = type_system.computeTypeLayoutWithPool(pool, sym_table, ty_b, target_layout);
                                if (lay_a.align_bytes != lay_b.align_bytes) return false;
                            },
                            .type_name => {
                                var buf_a: [512]u8 = undefined;
                                var buf_b: [512]u8 = undefined;
                                if (!std.mem.eql(
                                    u8,
                                    pool.formatType(ty_a, sym_table, &buf_a),
                                    pool.formatType(ty_b, sym_table, &buf_b),
                                )) return false;
                            },
                            else => if (inst_a.operands.lhs != inst_b.operands.lhs) return false,
                        }
                    } else {
                        const arg_len = inst_a.operands.rhs;
                        if (inst_a.operands.lhs + arg_len > body_a.extra_args.items.len or
                            inst_b.operands.lhs + arg_len > body_b.extra_args.items.len) return false;
                        for (0..arg_len) |arg_i| {
                            const aa = body_a.extra_args.items[inst_a.operands.lhs + arg_i];
                            const ab = body_b.extra_args.items[inst_b.operands.lhs + arg_i];
                            if (val_a[aa] != val_b[ab]) return false;
                        }
                        if (ikind == .derive_debug_fmt) {
                            const raw_a = body_a.extra_args.items[inst_a.operands.lhs];
                            const raw_b = body_b.extra_args.items[inst_b.operands.lhs];
                            var buf_a: [512]u8 = undefined;
                            var buf_b: [512]u8 = undefined;
                            if (!std.mem.eql(
                                u8,
                                pool.formatType(body_a.getInst(MirValueId.fromInt(raw_a)).type_id, sym_table, &buf_a),
                                pool.formatType(body_b.getInst(MirValueId.fromInt(raw_b)).type_id, sym_table, &buf_b),
                            )) return false;
                        }
                    }
                },
                .place_load,
                .place_discriminant,
                .place_set_discrim,
                .place_addr,
                .soa_column_slice,
                .ghost_access_let,
                .ghost_access_inout,
                .ghost_access_set,
                .ghost_storage_move,
                => {
                    if (!isPlaceStructurallyEqual(
                        body_a,
                        PlaceId.fromInt(inst_a.operands.lhs),
                        val_a,
                        body_b,
                        PlaceId.fromInt(inst_b.operands.lhs),
                        val_b,
                        pool,
                        sym_table,
                        target_layout,
                    ) or inst_a.operands.rhs != inst_b.operands.rhs) return false;
                },
                .place_store => {
                    if (!isPlaceStructurallyEqual(
                        body_a,
                        PlaceId.fromInt(inst_a.operands.lhs),
                        val_a,
                        body_b,
                        PlaceId.fromInt(inst_b.operands.lhs),
                        val_b,
                        pool,
                        sym_table,
                        target_layout,
                    ) or val_a[inst_a.operands.rhs] != val_b[inst_b.operands.rhs]) return false;
                },
                .fn_addr => {
                    if (!isCalleeTargetEqual(
                        DefId.fromInt(inst_a.operands.lhs),
                        SymbolIndex.fromInt(inst_a.operands.rhs),
                        DefId.fromInt(inst_b.operands.lhs),
                        SymbolIndex.fromInt(inst_b.operands.rhs),
                        sym_table,
                    )) return false;
                },
                .ghost_storage_init, .ghost_storage_deinit => {
                    if (inst_a.operands.lhs != inst_b.operands.lhs or
                        inst_a.operands.rhs != inst_b.operands.rhs) return false;
                },
            }
        }

        const ta = body_a.blocks.items[idx_a].terminator;
        const tb = body_b.blocks.items[idx_b].terminator;
        if (ta.kind != tb.kind or ta.aux_u8 != tb.aux_u8 or ta.edge_len != tb.edge_len) return false;
        switch (ta.kind) {
            .ret => {
                if ((ta.cond_or_val == mir.NONE_U32) != (tb.cond_or_val == mir.NONE_U32)) return false;
                if (ta.cond_or_val != mir.NONE_U32 and val_a[ta.cond_or_val] != val_b[tb.cond_or_val]) return false;
            },
            .cond_br, .switch_int => {
                if (val_a[ta.cond_or_val] != val_b[tb.cond_or_val]) return false;
            },
            .call => {
                const csa = body_a.calls.items[ta.cond_or_val];
                const csb = body_b.calls.items[tb.cond_or_val];
                if (!isCalleeTargetEqual(
                    csa.direct_def_id,
                    csa.direct_symbol,
                    csb.direct_def_id,
                    csb.direct_symbol,
                    sym_table,
                ) or
                    csa.is_callee_contextless != csb.is_callee_contextless or
                    csa.args_len != csb.args_len or
                    csa.call_borrows_len != csb.call_borrows_len or
                    csa.callee_val.isNone() != csb.callee_val.isNone()) return false;
                if (!csa.callee_val.isNone() and val_a[csa.callee_val.asInt()] != val_b[csb.callee_val.asInt()]) {
                    return false;
                }
                if (!computeLayoutShapeKey(pool, sym_table, csa.ret_ty, target_layout).isEqual(
                    computeLayoutShapeKey(pool, sym_table, csb.ret_ty, target_layout),
                ) or classifyOpSemantics(pool, csa.ret_ty, target_layout) !=
                    classifyOpSemantics(pool, csb.ret_ty, target_layout))
                {
                    return false;
                }
                for (0..csa.args_len) |ai| {
                    const ma = body_a.call_arg_modes.items[csa.modes_start + ai];
                    const mb = body_b.call_arg_modes.items[csb.modes_start + ai];
                    if (ma != mb) return false;
                    const wa = body_a.extra_args.items[csa.args_start + ai];
                    const wb = body_b.extra_args.items[csb.args_start + ai];
                    if (ma == .let_mode or ma == .sink_mode) {
                        if (val_a[wa] != val_b[wb]) return false;
                    } else if (!isPlaceStructurallyEqual(
                        body_a,
                        PlaceId.fromInt(wa),
                        val_a,
                        body_b,
                        PlaceId.fromInt(wb),
                        val_b,
                        pool,
                        sym_table,
                        target_layout,
                    )) {
                        return false;
                    }
                }
                for (0..csa.call_borrows_len) |bor_i| {
                    const ba = body_a.extra_args.items[csa.call_borrows_start + bor_i];
                    const bb_tok = body_b.extra_args.items[csb.call_borrows_start + bor_i];
                    if (val_a[ba] != val_b[bb_tok]) return false;
                }
            },
            else => {},
        }

        const edges_a = body_a.getOutgoingEdges(MirBlockId.fromInt(idx_a));
        const edges_b = body_b.getOutgoingEdges(MirBlockId.fromInt(idx_b));
        for (edges_a, edges_b) |ea, eb| {
            if (bb_a[ea.target_bb.asInt()] != bb_b[eb.target_bb.asInt()] or ea.args_len != eb.args_len) {
                return false;
            }
            if ((ea.case_tag_idx == std.math.maxInt(u16)) != (eb.case_tag_idx == std.math.maxInt(u16))) {
                return false;
            }
            if (ea.case_tag_idx != std.math.maxInt(u16)) {
                if (body_a.switch_values.items[ea.case_tag_idx] != body_b.switch_values.items[eb.case_tag_idx]) {
                    return false;
                }
            }
            for (0..ea.args_len) |ai| {
                const va_arg = body_a.extra_args.items[ea.args_start + ai];
                const vb_arg = body_b.extra_args.items[eb.args_start + ai];
                if (val_a[va_arg] != val_b[vb_arg]) return false;
            }
        }
    }

    return true;
}

/// Pass `R6`: `Wyhash(0)` structural Identical Code Folding (ICF) backed by full deterministic
/// `isMirBodyStructurallyEqual` (`[CRITICAL-09]`).
fn runPassR6StructuralIcf(
    allocator: std.mem.Allocator,
    bodies: *std.ArrayListUnmanaged(MirBody),
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    target_layout: TargetLayout,
    icf_folded_out: *u32,
) !void {
    const count = bodies.items.len;
    if (count <= 1) return;

    const hashes = try allocator.alloc(u64, count);
    defer allocator.free(hashes);
    for (bodies.items, 0..) |*b_ptr, idx| {
        hashes[idx] = try computeMirBodyStructuralHashWithInterner(
            allocator,
            b_ptr,
            pool,
            sym_table,
            interner,
            target_layout,
        );
    }

    // Protect functions whose addresses are explicitly taken via `MirOp.fn_addr` inside non-call SSA positions
    // so function-pointer address identity is never altered unless solely used as direct call targets:
    var addr_taken_defs: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer addr_taken_defs.deinit(allocator);
    for (bodies.items) |b_item| {
        var call_callee_vals: std.AutoHashMapUnmanaged(u32, void) = .empty;
        defer call_callee_vals.deinit(allocator);
        for (b_item.calls.items) |cs| {
            if (!cs.direct_def_id.isNone()) {
                try call_callee_vals.put(allocator, cs.callee_val.asInt(), {});
            }
        }
        for (b_item.blocks.items, 0..) |_, bb_i| {
            for (b_item.getBlockInsts(MirBlockId.fromInt(@intCast(bb_i)))) |iv| {
                const inst = b_item.getInst(iv);
                if (inst.op == .fn_addr and !call_callee_vals.contains(iv.asInt())) {
                    try addr_taken_defs.put(allocator, inst.operands.lhs, {});
                }
            }
        }
    }

    var def_remap: std.AutoHashMapUnmanaged(u32, DefId) = .empty;
    defer def_remap.deinit(allocator);
    const is_folded_away = try allocator.alloc(bool, count);
    defer allocator.free(is_folded_away);
    @memset(is_folded_away, false);

    for (0..count) |i| {
        if (is_folded_away[i]) continue;
        const canon_def = bodies.items[i].def_id;
        if (canon_def.isNone() or addr_taken_defs.contains(canon_def.asInt())) continue;

        for ((i + 1)..count) |j| {
            if (is_folded_away[j] or hashes[i] != hashes[j]) continue;
            const cand_def = bodies.items[j].def_id;
            if (cand_def.isNone() or addr_taken_defs.contains(cand_def.asInt())) continue;

            if (try isMirBodyStructurallyEqual(
                allocator,
                &bodies.items[i],
                &bodies.items[j],
                pool,
                sym_table,
                target_layout,
            )) {
                try def_remap.put(allocator, cand_def.asInt(), canon_def);
                icf_folded_out.* += 1;
                // Remove synthetic/monomorphized duplicate bodies (`def_id >= 0x7000_0000`) immediately;
                // for user-named functions, redirect all module-wide direct call sites to `canon_def`:
                if (cand_def.asInt() >= 0x7000_0000) {
                    is_folded_away[j] = true;
                }
            }
        }
    }

    if (def_remap.count() == 0) return;

    for (bodies.items, 0..) |*b_ptr, idx| {
        if (is_folded_away[idx]) continue;
        for (0..b_ptr.calls.items.len) |call_idx| {
            const direct_def = b_ptr.calls.items[call_idx].direct_def_id;
            if (def_remap.get(direct_def.asInt())) |canon_def| {
                redirectDirectCallSite(b_ptr, call_idx, canon_def);
            }
        }
    }

    var write_idx: usize = 0;
    for (0..count) |read_idx| {
        if (is_folded_away[read_idx]) {
            bodies.items[read_idx].deinit();
        } else {
            bodies.items[write_idx] = bodies.items[read_idx];
            write_idx += 1;
        }
    }
    bodies.items.len = write_idx;
}

/// Verifies `V1`–`V6` across every non-template `MirBody` in `bodies` (`DR-13` mandatory pass gate).
fn verifyAllConcreteBodies(
    allocator: std.mem.Allocator,
    bodies: []const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    sink: ?*DiagnosticSink,
) !void {
    for (bodies) |*body_item| {
        if (body_item.has_overflowed_limits) continue;
        if (isGenericTemplateBody(body_item, pool, sym_table)) continue;
        try mir.verifyMirBody(allocator, body_item, pool, sym_table, sink);
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Computes the canonical 16-byte `LayoutShapeKey` of `raw_ty` for `target_layout` (`DR-13` §5.3).
pub fn computeLayoutShapeKey(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_ty: TypeId,
    target_layout: TargetLayout,
) LayoutShapeKey {
    const ty = pool.unwrapUnderlyingType(raw_ty);
    const lay = type_system.computeTypeLayoutWithPool(pool, sym_table, ty, target_layout);
    const size_u32: u32 = @intCast(@min(lay.byte_size, std.math.maxInt(u32)));
    const ptr_size: u64 = target_layout.ptr_byte_size;

    const abi_class: AbiPassClass = if (lay.byte_size == 0)
        .zst
    else if (ty == .f32_ty or ty == .f64_ty or ty == .untyped_float_ty)
        .float_reg
    else if (lay.byte_size <= ptr_size)
        .integer_reg
    else if (lay.byte_size <= 2 * ptr_size)
        .pair_regs
    else
        .indirect_sret;

    const node = pool.getNode(ty);
    const is_copy: u8 = @intFromBool(
        node.flags.is_copy or node.tag == .primitive or node.tag == .ref_ty or
            node.tag == .raw_ptr_ty or node.tag == .fn_ty or node.tag == .bit_field_ty,
    );

    const niche_kind: NicheKind = if (ty == .bool_ty)
        .bool_01
    else if (ty == .char_ty)
        .char_unicode
    else if (node.tag == .ref_ty or node.tag == .mut_ref_ty or node.tag == .fn_ty)
        .non_null_ptr
    else if (node.tag == .enum_ty)
        .enum_tag_ceil
    else
        .none;

    var ptr_mask: u32 = 0;
    populatePtrWordMask(pool, sym_table, ty, 0, target_layout, 0, &ptr_mask);

    return .{
        .size_bytes = size_u32,
        .align_log2 = lay.align_log2,
        .abi_class = abi_class,
        .is_trivial_copy = is_copy,
        .niche_kind = niche_kind,
        .ptr_mask_64 = ptr_mask,
        ._pad = 0,
    };
}

/// Executes the dual-mode `MIR` optimization pipeline (`D1`–`D5` in `--dev`; `D1`–`D5` + `R1`–`R6`
/// in `--release`), invoking `mir.verifyMirBody` (`V1`–`V6`) after **every single pass**.
pub fn optimizeMirModule(
    allocator: std.mem.Allocator,
    input_bodies: []const MirBody,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *StringInterner,
    config: MirOptConfig,
    diagnostic_sink: ?*DiagnosticSink,
) !MirOptModuleResult {
    var result = MirOptModuleResult{ .allocator = allocator };
    errdefer result.deinit();

    try result.bodies.ensureTotalCapacity(allocator, input_bodies.len);
    for (input_bodies) |*src_body| {
        var cloned = try src_body.clone(allocator);
        errdefer cloned.deinit();
        try result.bodies.append(allocator, cloned);
    }

    // Execute `--dev` 5-pass pipeline (`D1`–`D5`):

    // [D1] Mandatory `@inline(always)` call splicing:
    try runPassD1InlineAlways(allocator, result.bodies.items, sym_table, config, diagnostic_sink);
    try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);

    // [D2] Reachable-only local constant folding & `E0502`/`E0507` compile-time traps:
    for (result.bodies.items) |*body_item| {
        try runPassD2ReachableConstFold(allocator, body_item, pool, sym_table, config, diagnostic_sink);
    }
    try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);

    // [D3] Ghost instruction strip gate (preserving pre-strip clones when requested for Phase 6 SAST):
    if (config.is_preserving_pre_strip_mir) {
        try result.pre_strip_bodies.ensureTotalCapacity(allocator, result.bodies.items.len);
        for (result.bodies.items) |*body_item| {
            var pre_clone = try body_item.clone(allocator);
            errdefer pre_clone.deinit();
            try result.pre_strip_bodies.append(allocator, pre_clone);
        }
    }
    for (result.bodies.items) |*body_item| {
        try runPassD3StripGhostInstructions(allocator, body_item);
    }
    try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);

    // [D4] Constant branch/switch folding + single-pass unreachable block pruning:
    for (result.bodies.items) |*body_item| {
        try runPassD4BranchFoldAndPrune(allocator, body_item);
    }
    try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);

    // [D5] Monomorphization + Tarjan SCC `contextless` promotion + `LayoutShapeKey` deduplication:
    try runPassD5MonomorphizeAndPromote(
        allocator,
        &result.bodies,
        pool,
        sym_table,
        interner,
        config,
        diagnostic_sink,
        &result.dedup_merged_count,
    );
    try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);

    // Execute `--release` 6-pass pipeline (`R1`–`R6`):
    if (config.is_release_mode) {
        // [R1] Bounded cost-model inliner (`W0501` on explicit `@inline` overflow/recursion):
        try runPassR1CostModelInliner(allocator, result.bodies.items, sym_table, config, diagnostic_sink);
        try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);

        // [R2] SROA (`Place`-to-SSA promotion via `MirSsaBuilder.initFromExistingBody`):
        for (result.bodies.items) |*body_item| {
            try runPassR2SroaPromotion(allocator, body_item, pool, sym_table, diagnostic_sink);
        }
        try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);

        // [R3] Dominator-scoped value-range propagation & redundant check folding:
        for (result.bodies.items) |*body_item| {
            try runPassR3ValueRangeProp(allocator, body_item, pool, config.target_layout);
        }
        try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);

        // [R4] Wegman-Zadeck SCCP + `switch_int` fusion + dominator-scoped commutative GVN:
        for (result.bodies.items) |*body_item| {
            try runPassR4SccpSwitchFusionAndGvn(allocator, body_item, pool, config.target_layout);
        }
        try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);

        // [R5] `MirProjection`-aware DCE + Call-Continuation-safe jump-threading & block merging:
        for (result.bodies.items) |*body_item| {
            try runPassR5DceJumpThreadAndMerge(allocator, body_item);
        }
        try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);

        // [R6] `Wyhash(0)` structural `MIR` Identical Code Folding (ICF):
        try runPassR6StructuralIcf(
            allocator,
            &result.bodies,
            pool,
            sym_table,
            interner,
            config.target_layout,
            &result.icf_folded_count,
        );
        try verifyAllConcreteBodies(allocator, result.bodies.items, pool, sym_table, diagnostic_sink);
    }

    // Compute deterministic module-wide structural fingerprint for `CompilerDb` Early Cutoff:
    var mod_hasher = std.hash.Wyhash.init(0);
    for (result.bodies.items) |*body_item| {
        const bh = try computeMirBodyStructuralHashWithInterner(
            allocator,
            body_item,
            pool,
            sym_table,
            interner,
            config.target_layout,
        );
        const def_raw = body_item.def_id.asInt();
        mod_hasher.update(std.mem.asBytes(&def_raw));
        const name_bytes = interner.get(body_item.name);
        const name_len: u32 = @intCast(name_bytes.len);
        mod_hasher.update(std.mem.asBytes(&name_len));
        mod_hasher.update(name_bytes);
        mod_hasher.update(std.mem.asBytes(&bh));
    }
    result.fingerprint = mod_hasher.final();

    return result;
}

// ---------------------------------------- MAIN -----------------------------------------

test "LayoutShapeKey 16-byte layout invariant and pointer-shape classification" {
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(AbiPassClass));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(NicheKind));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(LayoutShapeKey));

    const allocator = std.testing.allocator;
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();
    var pool = try InternPool.init(allocator);
    defer pool.deinit();

    const ref_i32 = try pool.internRef(.i32_ty, false);
    const ref_f64 = try pool.internRef(.f64_ty, false);
    const shape_ref_i32 = computeLayoutShapeKey(&pool, &sym_table, ref_i32, TargetLayout.NATIVE_64);
    const shape_ref_f64 = computeLayoutShapeKey(&pool, &sym_table, ref_f64, TargetLayout.NATIVE_64);
    try std.testing.expect(shape_ref_i32.isEqual(shape_ref_f64));
    try std.testing.expectEqual(@as(u32, 8), shape_ref_i32.size_bytes);
    try std.testing.expectEqual(NicheKind.non_null_ptr, shape_ref_i32.niche_kind);
    try std.testing.expectEqual(@as(u32, 0x1), shape_ref_i32.ptr_mask_64);

    const shape_wasm = computeLayoutShapeKey(&pool, &sym_table, ref_i32, TargetLayout.WASM32);
    try std.testing.expectEqual(@as(u32, 4), shape_wasm.size_bytes);
}

test "mir_opt D1-D5 dev pipeline: @inline(always), unreachable 1/0 safety, ghost strip, and contextless promotion" {
    const allocator = std.testing.allocator;
    const mir_vm = @import("mir_vm.zig");

    const source =
        \\@inline(always)
        \\pub fn step_add(val: i64) -> i64 {
        \\    return val + 10;
        \\}
        \\
        \\pub fn safe_branch(input: i64) -> i64 {
        \\    if false {
        \\        return 1 / 0;
        \\    }
        \\    return step_add(input) + (3 * 4);
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(10),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var opt_sink = DiagnosticSink.init(allocator);
    defer opt_sink.deinit();

    var dev_res = try optimizeMirModule(
        allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &bundle.hir_bundle.interner,
        .{
            .is_release_mode = false,
            .is_preserving_pre_strip_mir = true,
            .syntax_view = .{
                .source = source,
                .tokens = &bundle.hir_bundle.tokens,
                .cst_arena = &bundle.hir_bundle.cst_arena,
            },
        },
        &opt_sink,
    );
    defer dev_res.deinit();

    // `if false { 1 / 0 }` MUST NOT emit `E0507`:
    try std.testing.expect(!opt_sink.hasErrors());
    // Pre-strip clones preserved for Phase 6 SAST still carry ghost flags:
    try std.testing.expectEqual(dev_res.bodies.items.len, dev_res.pre_strip_bodies.items.len);
    try std.testing.expect(!dev_res.pre_strip_bodies.items[0].is_ghost_stripped);

    const safe_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "safe_branch").?;
    try std.testing.expect(safe_body.is_ghost_stripped);
    try std.testing.expect(!safe_body.has_ghost_instructions);
    try std.testing.expect(safe_body.is_contextless);

    // `@inline(always)` `step_add` was spliced into `safe_branch` (`0` remaining `.call` terminators):
    for (safe_body.blocks.items) |bb| {
        try std.testing.expect(bb.terminator.kind != .call);
    }

    // Verify semantic equivalence in `MirVm` before vs. after `--dev`:
    var rodata_pool = mir_vm.RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var vm = try mir_vm.MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &opt_sink,
        .{},
    );
    defer vm.deinit();

    const out_val = try vm.evalBody(safe_body, &.{.{ .scalar_i64 = 5 }});
    try std.testing.expectEqual(@as(i64, 27), out_val.slot.scalar_i64);
}

test "mir_opt R1-R6 release pipeline: W0501 budget warning, SROA, SCCP/GVN/DCE, and Wyhash ICF" {
    const allocator = std.testing.allocator;
    const mir_vm = @import("mir_vm.zig");

    const source =
        \\pub struct Point {
        \\    pub px: i64,
        \\    pub py: i64,
        \\}
        \\
        \\@inline
        \\pub fn rec_fib(num: i64) -> i64 {
        \\    if num <= 1 {
        \\        return num;
        \\    }
        \\    return rec_fib(num - 1) + rec_fib(num - 2);
        \\}
        \\
        \\pub fn dup_alpha(val: i64) -> i64 {
        \\    let pt_a = Point { px: val + 1, py: val + 1 };
        \\    return pt_a.px + pt_a.py;
        \\}
        \\
        \\pub fn dup_beta(item: i64) -> i64 {
        \\    let pt_b = Point { px: item + 1, py: item + 1 };
        \\    return pt_b.px + pt_b.py;
        \\}
        \\
        \\pub fn entry_calc(seed: i64) -> i64 {
        \\    return dup_alpha(seed) + dup_beta(seed) + rec_fib(4);
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(11),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var rel_sink = DiagnosticSink.init(allocator);
    defer rel_sink.deinit();

    var rel_res = try optimizeMirModule(
        allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &bundle.hir_bundle.interner,
        .{
            .is_release_mode = true,
            .syntax_view = .{
                .source = source,
                .tokens = &bundle.hir_bundle.tokens,
                .cst_arena = &bundle.hir_bundle.cst_arena,
            },
        },
        &rel_sink,
    );
    defer rel_res.deinit();

    try std.testing.expect(!rel_sink.hasErrors());
    // Recursive `@inline fn rec_fib` MUST emit `W0501`:
    var has_seen_w0501 = false;
    for (rel_sink.diagnostics.items) |diag_item| {
        if (diag_item.code == .w0501_inlining_budget_exceeded) has_seen_w0501 = true;
    }
    try std.testing.expect(has_seen_w0501);

    // `dup_alpha` and `dup_beta` are structurally identical after SROA + GVN + DCE -> folded by `R6` ICF:
    try std.testing.expect(rel_res.icf_folded_count >= 1);

    // Verify `MirVm` produces identical results on unoptimized vs `--release` optimized `entry_calc`:
    var rodata_pool = mir_vm.RodataPool.init(allocator);
    defer rodata_pool.deinit();

    var vm_raw = try mir_vm.MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{},
    );
    defer vm_raw.deinit();
    for (bundle.mir_bundle.bodies.items) |*b_ptr| {
        _ = try vm_raw.registerBody(b_ptr, .none);
    }
    const raw_entry = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "entry_calc").?;
    const expected = try vm_raw.evalBody(raw_entry, &.{.{ .scalar_i64 = 9 }});

    var vm_opt = try mir_vm.MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{},
    );
    defer vm_opt.deinit();
    for (rel_res.bodies.items) |*b_ptr| {
        _ = try vm_opt.registerBody(b_ptr, .none);
    }
    const opt_entry = rel_res.findBodyByName(&bundle.hir_bundle.interner, "entry_calc").?;
    const actual = try vm_opt.evalBody(opt_entry, &.{.{ .scalar_i64 = 9 }});

    try std.testing.expectEqual(@as(i64, 43), expected.slot.scalar_i64);
    try std.testing.expectEqual(expected.slot.scalar_i64, actual.slot.scalar_i64);
}

test "test_mir_opt_r2_sroa_loop_header_unsealing_accumulates_sum_ten_45" {
    const allocator = std.testing.allocator;
    const mir_vm = @import("mir_vm.zig");

    const source =
        \\pub struct Acc {
        \\    pub total: i64,
        \\    pub count: i64,
        \\}
        \\
        \\pub fn sum_ten() -> i64 {
        \\    var acc = Acc { total: 0, count: 0 };
        \\    var idx: i64 = 0;
        \\    while idx < 10 {
        \\        acc.total = acc.total + idx;
        \\        acc.count = acc.count + 1;
        \\        idx = idx + 1;
        \\    }
        \\    return acc.total;
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(30),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var rel_sink = DiagnosticSink.init(allocator);
    defer rel_sink.deinit();

    var rel_res = try optimizeMirModule(
        allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &bundle.hir_bundle.interner,
        .{ .is_release_mode = true },
        &rel_sink,
    );
    defer rel_res.deinit();
    try std.testing.expect(!rel_sink.hasErrors());

    var rodata_pool = mir_vm.RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var vm = try mir_vm.MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (rel_res.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, .none);
    }

    const opt_sum = rel_res.findBodyByName(&bundle.hir_bundle.interner, "sum_ten").?;
    const eval_out = try vm.evalBody(opt_sum, &.{});
    try std.testing.expectEqual(@as(i64, 45), eval_out.slot.scalar_i64);
}

test "test_mir_opt_r6_icf_never_folds_distinct_aggregates_indices_or_struct_field_shapes" {
    const allocator = std.testing.allocator;
    const mir_vm = @import("mir_vm.zig");

    const source =
        \\pub struct ShapeOne {
        \\    pub wide: u32,
        \\    pub mid: u16,
        \\    pub low: u16,
        \\}
        \\
        \\pub struct ShapeTwo {
        \\    pub low: u16,
        \\    pub mid: u16,
        \\    pub wide: u32,
        \\}
        \\
        \\pub fn make_pair_alpha(first: i64, second: i64, shared: i64) -> [i64; 2] {
        \\    let _ = second;
        \\    return [first, shared];
        \\}
        \\
        \\pub fn make_pair_beta(first: i64, second: i64, shared: i64) -> [i64; 2] {
        \\    let _ = first;
        \\    return [second, shared];
        \\}
        \\
        \\pub fn load_idx_alpha(arr: &[i64; 4], idx_a: usize, idx_b: usize) -> i64 {
        \\    let _ = idx_b;
        \\    return arr[idx_a];
        \\}
        \\
        \\pub fn load_idx_beta(arr: &[i64; 4], idx_a: usize, idx_b: usize) -> i64 {
        \\    let _ = idx_a;
        \\    return arr[idx_b];
        \\}
        \\
        \\pub fn pack_shape_one(part_a: u32, part_b: u16, part_c: u16) -> ShapeOne {
        \\    return ShapeOne { wide: part_a, mid: part_b, low: part_c };
        \\}
        \\
        \\pub fn pack_shape_two(part_a: u16, part_b: u16, part_c: u32) -> ShapeTwo {
        \\    return ShapeTwo { low: part_a, mid: part_b, wide: part_c };
        \\}
        \\
        \\pub fn verify_distinct_calls() -> i64 {
        \\    let pair_a = make_pair_alpha(10, 20, 99);
        \\    let pair_b = make_pair_beta(10, 20, 99);
        \\    let table: [i64; 4] = [100, 200, 300, 400];
        \\    let elem_a = load_idx_alpha(&table, 1, 3);
        \\    let elem_b = load_idx_beta(&table, 1, 3);
        \\    return (pair_b[0] - pair_a[0]) + (elem_b - elem_a);
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(31),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var rel_sink = DiagnosticSink.init(allocator);
    defer rel_sink.deinit();

    var rel_res = try optimizeMirModule(
        allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &bundle.hir_bundle.interner,
        .{ .is_release_mode = true },
        &rel_sink,
    );
    defer rel_res.deinit();
    try std.testing.expect(!rel_sink.hasErrors());
    // None of the three non-equivalent pairs may fold together in `R6` ICF:
    try std.testing.expectEqual(@as(u32, 0), rel_res.icf_folded_count);

    var rodata_pool = mir_vm.RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var vm = try mir_vm.MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (rel_res.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, .none);
    }

    const verify_body = rel_res.findBodyByName(&bundle.hir_bundle.interner, "verify_distinct_calls").?;
    const diff_out = try vm.evalBody(verify_body, &.{});
    // `(20 - 10) + (400 - 200) == 210`:
    try std.testing.expectEqual(@as(i64, 210), diff_out.slot.scalar_i64);
}

test "test_mir_opt_d5_monomorphize_preserves_type_name_and_interior_field_signedness" {
    const allocator = std.testing.allocator;
    const mir_vm = @import("mir_vm.zig");

    const source =
        \\pub fn type_label[T](val: T) -> str {
        \\    let _ = val;
        \\    return @type_name[T]();
        \\}
        \\
        \\pub fn is_first_less[T: Integer](pair: (T, i32), rhs: T) -> bool {
        \\    return pair.0 < rhs;
        \\}
        \\
        \\pub fn get_signed_label() -> str {
        \\    let signed_val: i32 = 7;
        \\    return type_label(signed_val);
        \\}
        \\
        \\pub fn get_unsigned_label() -> str {
        \\    let unsigned_val: u32 = 7;
        \\    return type_label(unsigned_val);
        \\}
        \\
        \\pub fn check_interior_signedness() -> i32 {
        \\    let neg_val: i32 = -5;
        \\    let one_i32: i32 = 1;
        \\    let neg_pair: (i32, i32) = (neg_val, 0);
        \\    let big_val: u32 = 4294967291;
        \\    let one_u32: u32 = 1;
        \\    let big_pair: (u32, i32) = (big_val, 0);
        \\    var score: i32 = 0;
        \\    if is_first_less(neg_pair, one_i32) {
        \\        score = score + 10;
        \\    }
        \\    if !is_first_less(big_pair, one_u32) {
        \\        score = score + 20;
        \\    }
        \\    return score;
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(32),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var opt_sink = DiagnosticSink.init(allocator);
    defer opt_sink.deinit();

    var dev_res = try optimizeMirModule(
        allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &bundle.hir_bundle.interner,
        .{ .is_release_mode = false },
        &opt_sink,
    );
    defer dev_res.deinit();
    try std.testing.expect(!opt_sink.hasErrors());
    try std.testing.expectEqual(@as(u32, 0), dev_res.dedup_merged_count);

    var rodata_pool = mir_vm.RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var vm = try mir_vm.MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (dev_res.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, .none);
    }

    const signed_lbl_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "get_signed_label").?;
    const signed_lbl_out = try vm.evalBody(signed_lbl_body, &.{});
    const signed_lbl_val = try vm.resultToComptimeValue(signed_lbl_out, null);
    try std.testing.expectEqualStrings("i32", bundle.hir_bundle.interner.get(signed_lbl_val.str_val));

    const unsigned_lbl_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "get_unsigned_label").?;
    const unsigned_lbl_out = try vm.evalBody(unsigned_lbl_body, &.{});
    const unsigned_lbl_val = try vm.resultToComptimeValue(unsigned_lbl_out, null);
    try std.testing.expectEqualStrings("u32", bundle.hir_bundle.interner.get(unsigned_lbl_val.str_val));

    const sign_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "check_interior_signedness").?;
    const sign_out = try vm.evalBody(sign_body, &.{});
    try std.testing.expectEqual(@as(i64, 30), sign_out.slot.scalar_i64);
}

test "test_mir_opt_r3_u128_top_bit_vrp_and_d2_shift_rhs_type_e0502_without_cascade" {
    const allocator = std.testing.allocator;
    const mir_vm = @import("mir_vm.zig");

    // [1] `[CRITICAL-13]`: `u128` value `>= 2^127` MUST NOT misfold `wide_val < 10` to `true` in `R3` VRP:
    const u128_src =
        \\pub fn check_high_u128(is_top_bit: bool) -> bool {
        \\    var wide_val: u128 = 170141183460469231731687303715884105728;
        \\    if !is_top_bit {
        \\        wide_val = 20;
        \\    }
        \\    return wide_val < 10;
        \\}
    ;
    var u128_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(33),
        u128_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer u128_bundle.deinit();
    try std.testing.expect(!u128_bundle.hir_bundle.diagnostics.hasErrors());

    var u128_sink = DiagnosticSink.init(allocator);
    defer u128_sink.deinit();
    var u128_rel = try optimizeMirModule(
        allocator,
        u128_bundle.mir_bundle.bodies.items,
        &u128_bundle.hir_bundle.pool,
        &u128_bundle.hir_bundle.sym_table,
        &u128_bundle.hir_bundle.interner,
        .{ .is_release_mode = true },
        &u128_sink,
    );
    defer u128_rel.deinit();
    try std.testing.expect(!u128_sink.hasErrors());

    var rodata_pool = mir_vm.RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var vm = try mir_vm.MirVm.init(
        allocator,
        &u128_bundle.hir_bundle.interner,
        &u128_bundle.hir_bundle.pool,
        &u128_bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (u128_rel.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, .none);
    }
    const high_body = u128_rel.findBodyByName(&u128_bundle.hir_bundle.interner, "check_high_u128").?;
    const high_out = try vm.evalBody(high_body, &.{.{ .scalar_u64 = 1 }});
    try std.testing.expectEqual(@as(u64, 0), high_out.slot.scalar_u64);

    // [2] `[CRITICAL-14]`: `foldConstBinOp` uses `rhs_ty` (`1_i8 << 256_u32` and `1_u8 << -256_i32` trap `E0502`):
    var pool = try InternPool.init(allocator);
    defer pool.deinit();
    const shl_u32_fold = foldConstBinOp(
        &pool,
        .shl_checked,
        .{ .int_val = 1 },
        .{ .int_val = 256 },
        .i8_ty,
        .u32_ty,
        .i8_ty,
        TargetLayout.NATIVE_64,
    );
    try std.testing.expect(shl_u32_fold == .trap_overflow);

    const shl_neg_i32_fold = foldConstBinOp(
        &pool,
        .shl_checked,
        .{ .int_val = 1 },
        .{ .int_val = -256 },
        .u8_ty,
        .i32_ty,
        .u8_ty,
        TargetLayout.NATIVE_64,
    );
    try std.testing.expect(shl_neg_i32_fold == .trap_overflow);

    // [3] `[MAJOR-16]`: `10_i8 / (127_i8 + 1_i8)` emits `E0502` once without cascading bogus `E0507`:
    const cascade_src =
        \\pub fn overflow_then_div() -> i8 {
        \\    let max_byte: i8 = 127;
        \\    return 10 / (max_byte + 1);
        \\}
    ;
    var cascade_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(34),
        cascade_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer cascade_bundle.deinit();

    var cascade_sink = DiagnosticSink.init(allocator);
    defer cascade_sink.deinit();
    var cascade_opt = try optimizeMirModule(
        allocator,
        cascade_bundle.mir_bundle.bodies.items,
        &cascade_bundle.hir_bundle.pool,
        &cascade_bundle.hir_bundle.sym_table,
        &cascade_bundle.hir_bundle.interner,
        .{ .is_release_mode = false },
        &cascade_sink,
    );
    defer cascade_opt.deinit();

    try std.testing.expectEqual(@as(usize, 1), cascade_sink.diagnostics.items.len);
    try std.testing.expectEqual(
        DiagCode.e0502_integer_constant_overflow,
        cascade_sink.diagnostics.items[0].code,
    );
}

test "test_mir_opt_d1_inliner_guards_max_place_proj_depth_with_e0508" {
    const allocator = std.testing.allocator;
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();
    var pool = try InternPool.init(allocator);
    defer pool.deinit();

    const file_id = FileId.fromInt(35);
    const callee_def = DefId.init(file_id, 1);
    const caller_def = DefId.init(file_id, 2);
    const callee_name = try interner.intern("deep_callee");
    const caller_name = try interner.intern("deep_caller");
    const fn_ty = try pool.internFn(.fn_ty, &.{.i32_ty}, &.{.inout_mode}, .unit_ty, true);

    const mod_scope = try sym_table.scope_arena.allocScope(.module_scope, .none, .NONE, file_id, .{});
    var empty_sink = DiagnosticSink.init(allocator);
    defer empty_sink.deinit();

    const callee_sym = try sym_table.defineSymbol(.{
        .name = callee_name,
        .name_text = interner.get(callee_name),
        .kind = .fn_sym,
        .namespace = .value_ns,
        .visibility = .public,
        .flags = .{},
        .scope_id = mod_scope,
        .def_id = callee_def,
        .decl_span = Span.init(file_id, 0, 0),
        .type_id = fn_ty,
    }, &empty_sink);

    var bodies: std.ArrayListUnmanaged(MirBody) = .empty;
    defer {
        for (bodies.items) |*body_item| body_item.deinit();
        bodies.deinit(allocator);
    }

    // Build `deep_callee(mut slot: inout ...)` with a 150-step `.field` projection on param local `1`:
    var callee_body = MirBody.init(allocator, file_id, callee_def);
    callee_body.name = callee_name;
    callee_body.ret_ty = .unit_ty;
    callee_body.param_count = 1;
    callee_body.is_contextless = true;
    try callee_body.locals.append(
        allocator,
        mir.LocalDecl.init(.empty, .unit_ty, .none, 0, .let_mode, .{ .is_return_slot = true }),
    );
    try callee_body.locals.append(
        allocator,
        mir.LocalDecl.init(.empty, .i32_ty, .none, 0, .inout_mode, .{ .is_arg = true, .is_mut = true }),
    );
    const callee_proj_start: u24 = @intCast(callee_body.projections.items.len);
    for (0..150) |_| {
        try callee_body.projections.append(allocator, .{ .kind = .field, .payload = 0 });
    }
    const callee_place = PlaceId.fromInt(@intCast(callee_body.places.items.len));
    try callee_body.places.append(allocator, .{
        .base = 1,
        .proj_start = callee_proj_start,
        .proj_len = 150,
    });
    const c_idx = try callee_body.appendConst(.{ .int_val = 1 });
    try callee_body.insts.append(allocator, .{
        .op = .const_scalar,
        .type_id = .i32_ty,
        .operands = .{ .lhs = c_idx, .rhs = 0 },
    });
    try callee_body.origin_tokens.append(allocator, .none);
    try callee_body.insts.append(allocator, .{
        .op = .place_store,
        .flags = .{ .has_side_effects = true },
        .type_id = .unit_ty,
        .operands = .{ .lhs = callee_place.asInt(), .rhs = 0 },
    });
    try callee_body.origin_tokens.append(allocator, .none);
    try callee_body.block_insts.appendSlice(allocator, &.{ MirValueId.fromInt(0), MirValueId.fromInt(1) });
    try callee_body.blocks.append(allocator, .{
        .param_start = 0,
        .inst_start = 0,
        .inst_len = 2,
        .terminator = .{ .kind = .ret, .cond_or_val = mir.NONE_U32, .edge_start = 0, .edge_len = 0 },
    });
    try bodies.append(allocator, callee_body);

    // Build `deep_caller` passing a 150-step `.field` `MirPlace` (`150 + 150 = 300 > MAX_PLACE_PROJ_DEPTH`):
    var caller_body = MirBody.init(allocator, file_id, caller_def);
    caller_body.name = caller_name;
    caller_body.ret_ty = .unit_ty;
    caller_body.is_contextless = true;
    try caller_body.locals.append(
        allocator,
        mir.LocalDecl.init(.empty, .unit_ty, .none, 0, .let_mode, .{ .is_return_slot = true }),
    );
    try caller_body.locals.append(
        allocator,
        mir.LocalDecl.init(.empty, .i32_ty, .none, 0, .let_mode, .{ .is_mut = true, .is_address_taken = true }),
    );
    const caller_proj_start: u24 = @intCast(caller_body.projections.items.len);
    for (0..150) |_| {
        try caller_body.projections.append(allocator, .{ .kind = .field, .payload = 0 });
    }
    const caller_place = PlaceId.fromInt(@intCast(caller_body.places.items.len));
    try caller_body.places.append(allocator, .{
        .base = 1,
        .proj_start = caller_proj_start,
        .proj_len = 150,
    });
    try caller_body.extra_args.append(allocator, caller_place.asInt());
    try caller_body.call_arg_modes.append(allocator, .inout_mode);
    try caller_body.calls.append(allocator, .{
        .callee_val = .none,
        .direct_def_id = callee_def,
        .direct_symbol = callee_sym,
        .args_start = 0,
        .args_len = 1,
        .modes_start = 0,
        .ret_ty = .unit_ty,
        .is_callee_contextless = true,
        .origin_token = .none,
    });
    try caller_body.extra_edges.append(allocator, .{
        .src_bb = MirBlockId.fromInt(0),
        .target_bb = MirBlockId.fromInt(1),
        .args_start = 0,
        .args_len = 0,
    });
    try caller_body.blocks.append(allocator, .{
        .param_start = 0,
        .inst_start = 0,
        .inst_len = 0,
        .terminator = .{ .kind = .call, .cond_or_val = 0, .edge_start = 0, .edge_len = 1 },
    });
    try caller_body.blocks.append(allocator, .{
        .param_start = 0,
        .inst_start = 0,
        .inst_len = 0,
        .terminator = .{ .kind = .ret, .cond_or_val = mir.NONE_U32, .edge_start = 0, .edge_len = 0 },
    });
    try bodies.append(allocator, caller_body);

    var overrides: std.AutoHashMapUnmanaged(u32, InlineDirective) = .empty;
    defer overrides.deinit(allocator);
    try overrides.put(allocator, callee_def.asInt(), .inline_always);

    var d1_sink = DiagnosticSink.init(allocator);
    defer d1_sink.deinit();
    try runPassD1InlineAlways(allocator, bodies.items, &sym_table, .{ .inline_overrides = &overrides }, &d1_sink);
    try std.testing.expectEqual(@as(usize, 1), d1_sink.diagnostics.items.len);
    try std.testing.expectEqual(
        DiagCode.e0508_comptime_resource_limit_exceeded,
        d1_sink.diagnostics.items[0].code,
    );
}

//! Mid-Level Intermediate Representation (`MIR`), Braun SSA Builder & Ownership Verifier.
//!
//! Architectural Role:
//! - Defines the canonical target-independent Block-Argument SSA `MirBody` (`DR-13` §3) with
//!   `comptime`-enforced cache-dense layouts: `LocalDecl` (`16B`), `MirPlace` (`8B`),
//!   `MirProjection` (`8B`), `MirInst` (`16B` SoA), `MirTerminator` (`12B`),
//!   `MirBasicBlock` (`32B`), and `MirOutgoingEdge` (`16B`).
//! - Preserves pre-strip Ghost Lifetime (`ghost_access_let`, `ghost_access_inout`,
//!   `ghost_access_set`, `ghost_access_end`) and Ghost Storage (`ghost_storage_init`,
//!   `ghost_storage_move`, `ghost_storage_deinit`) instructions (`DR-02` Deliverable 3) so
//!   Phase 6 SAST ownership/exclusivity verification operates without CFG reconstruction.
//! - Implements Braun et al.'s single-pass forward `MirSsaBuilder` (`DR-13` §3.4) over an
//!   edge-indexed CFG, supporting both fresh `HIR -> MIR` lowering and pre-seeded `MirBody`
//!   promotion for Wave 2C's `R2` SROA pass.
//! - Splices non-recursive `subscript … yield` projections, lowers pattern
//!   matrices via Maranget + Jacobs decision trees (`DR-13` §4.1), synthesizes shared cold LIFO
//!   `defer` / `errdefer` cleanup pads with mid-expression borrow closing,
//!   and enforces formal `MirVerifier` invariants `V1`–`V6` (`DR-13` §4.4).
//!
//! Key Design Choices:
//! - Outgoing CFG edges are first-class `EdgeId` records (`MirOutgoingEdge`) referenced by both
//!   source `MirTerminator`s and target `pred_edges`, guaranteeing distinct per-edge block
//!   argument lists even when `cond_br` or `switch_int` targets the same block twice.
//! - Call continuations strictly obey the Split-Edge Invariant: every `call`
//!   terminator's `normal_bb` has `pred_len == 1`, `paramLen() == 1` (`%ret_val`), and
//!   `normal_edge.args_len == 0`.
//! - SSA `MirValueId`s index `MirBody.insts` directly (`0 .. insts.len - 1`); `.none`
//!   (`maxInt(u32)`) is the sole sentinel for absent SSA values.

const std = @import("std");
const builtin = @import("builtin");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const diagnostic = @import("diag/diagnostic.zig");
const parser = @import("parser.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const query_db = @import("query_db.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const hir = @import("hir.zig");

const FileId = mem_foundation.FileId;
const PackageId = vfs_sourcemap.PackageId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
/// Re-exported canonical 32-bit `MirBlockId` handle.
pub const MirBlockId = mem_foundation.MirBlockId;
/// Re-exported canonical 32-bit `MirValueId` handle.
pub const MirValueId = mem_foundation.MirValueId;
const TypeId = mem_foundation.TypeId;
const RegionId = mem_foundation.RegionId;
const DefId = query_db.DefId;

const TokenBuffer = syntax_arenas.TokenBuffer;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstArena = syntax_arenas.AstArena;

const DiagnosticSink = diagnostic.DiagnosticSink;
const DiagnosticCode = diagnostic.DiagnosticCode;
const LabeledSpan = diagnostic.LabeledSpan;

const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolTable = symbol_resolver.SymbolTable;

const InternPool = type_system.InternPool;
const ParamMode = type_system.ParamMode;
const TargetLayout = type_system.TargetLayout;
const BodySemanticSideTables = type_system.BodySemanticSideTables;

const HirIndex = hir.HirIndex;
const HirTag = hir.HirTag;
const HirNode = hir.HirNode;
const HirStore = hir.HirStore;
const HirFnMeta = hir.HirFnMeta;
const HirPat = hir.HirPat;
const HirMatchArm = hir.HirMatchArm;
const BitSpec = hir.BitSpec;
const ComptimeValue = hir.ComptimeValue;
const ReturnErrorKind = hir.ReturnErrorKind;

// ---------------------------------------- TYPES ----------------------------------------

// -------------- Strongly Typed MIR Index Handles --------------

/// Strongly typed 32-bit index into `MirBody.locals` (`_0` is the return slot).
pub const LocalId = enum(u32) {
    /// Reserved return-value slot `_0` (`0`).
    return_slot = 0,
    /// Sentinel representing no local slot (`maxInt(u32)`).
    none = std.math.maxInt(u32),
    _,

    /// Constructs a `LocalId` from a raw `u32`.
    pub inline fn fromInt(raw_index: u32) LocalId {
        return @fromBackingInt(@intCast(raw_index));
    }

    /// Extracts the underlying `u32` slot index.
    pub inline fn asInt(self: LocalId) u32 {
        return @backingInt(self);
    }

    /// Returns `true` if `self == .none`.
    pub inline fn isNone(self: LocalId) bool {
        return self == .none;
    }
};

/// Strongly typed 32-bit index into `MirBody.places` (`0` is the unprojected `_0` return place).
pub const PlaceId = enum(u32) {
    /// Canonical unprojected return place (`base = 0, proj_len = 0`).
    return_place = 0,
    /// Sentinel representing no place (`maxInt(u32)`).
    none = std.math.maxInt(u32),
    _,

    /// Constructs a `PlaceId` from a raw `u32`.
    pub inline fn fromInt(raw_index: u32) PlaceId {
        return @fromBackingInt(@intCast(raw_index));
    }

    /// Extracts the underlying `u32` place index.
    pub inline fn asInt(self: PlaceId) u32 {
        return @backingInt(self);
    }

    /// Returns `true` if `self == .none`.
    pub inline fn isNone(self: PlaceId) bool {
        return self == .none;
    }
};

/// Strongly typed 32-bit index into `MirBody.extra_edges`.
pub const EdgeId = enum(u32) {
    /// Sentinel representing no CFG edge (`maxInt(u32)`).
    none = std.math.maxInt(u32),
    _,

    /// Constructs an `EdgeId` from a raw `u32`.
    pub inline fn fromInt(raw_index: u32) EdgeId {
        return @fromBackingInt(@intCast(raw_index));
    }

    /// Extracts the underlying `u32` edge index.
    pub inline fn asInt(self: EdgeId) u32 {
        return @backingInt(self);
    }

    /// Returns `true` if `self == .none`.
    pub inline fn isNone(self: EdgeId) bool {
        return self == .none;
    }
};

// ---------------- Locals, Places & Projections ----------------

/// Packed 1-byte property flags on a `LocalDecl` (`DR-13` §3.2).
pub const LocalFlags = packed struct(u8) {
    /// `true` if declared mutable (`let mut` / `var` / `inout` / `set`).
    is_mut: bool = false,
    /// `true` if this local is a formal function/closure parameter (`1 .. arg_count`).
    is_arg: bool = false,
    /// `true` if synthesized by `HIR` or `MIR` lowering.
    is_synthetic_temp: bool = false,
    /// `true` if its address is taken (`place_addr`), borrowed across blocks, or dynamically indexed;
    /// `false` if eligible for Braun SSA register promotion.
    is_address_taken: bool = false,
    /// `true` if this local holds a stack-pinned `@local` non-escaping closure (`V6`).
    is_local_closure: bool = false,
    /// `true` if this local is the `_0` return slot.
    is_return_slot: bool = false,
    /// Reserved zero padding bits.
    _pad: u2 = 0,
};

/// 16-byte local slot descriptor in `MirBody.locals` (`DR-13` §3.2).
pub const LocalDecl = extern struct {
    /// Interned variable name (`SymbolId.empty` for anonymous temporaries).
    name: SymbolId,
    /// Concrete monomorphic `TypeId` of this local slot.
    type_id: TypeId,
    /// Source token for ownership/SAST diagnostics.
    origin_token: TokenIndex,
    /// Enclosing lexical region ordinal (`0` when unannotated).
    region_raw: u16 = 0,
    /// Raw `ParamMode` byte (`0..3`).
    mode_raw: u8 = 0,
    /// Bit-cast `LocalFlags` byte.
    flags_raw: u8 = 0,

    /// Constructs a `LocalDecl` from typed `ParamMode` and `LocalFlags`.
    pub inline fn init(
        name: SymbolId,
        type_id: TypeId,
        origin_token: TokenIndex,
        region_raw: u16,
        param_mode: ParamMode,
        local_flags: LocalFlags,
    ) LocalDecl {
        return .{
            .name = name,
            .type_id = type_id,
            .origin_token = origin_token,
            .region_raw = region_raw,
            .mode_raw = @backingInt(param_mode),
            .flags_raw = @bitCast(local_flags),
        };
    }

    /// Decodes the `ParamMode` of `self`.
    pub inline fn mode(self: LocalDecl) ParamMode {
        return @fromBackingInt(@intCast(@as(u2, @truncate(self.mode_raw))));
    }

    /// Decodes the `LocalFlags` of `self`.
    pub inline fn flags(self: LocalDecl) LocalFlags {
        return @bitCast(self.flags_raw);
    }

    /// Updates the `LocalFlags` of `self`.
    pub inline fn setFlags(self: *LocalDecl, new_flags: LocalFlags) void {
        self.flags_raw = @bitCast(new_flags);
    }
};

/// 8-byte memory access path (`base` local + slice of `MirProjection`s in `MirBody.projections`).
pub const MirPlace = packed struct(u64) {
    /// Base `LocalId` (`0 .. locals.len - 1`).
    base: u32,
    /// Start offset inside `MirBody.projections` (`< MAX_MIR_PROJECTIONS`).
    proj_start: u24 = 0,
    /// Number of chained projections (`<= MAX_PLACE_PROJ_DEPTH`).
    proj_len: u8 = 0,

    /// Returns the base `LocalId`.
    pub inline fn baseLocal(self: MirPlace) LocalId {
        return LocalId.fromInt(self.base);
    }
};

/// Projection step kind in `MirBody.projections` (`DR-13` §3.2).
pub const ProjKind = enum(u8) {
    /// Dereferences a `&T`, `&mut T`, `*T`, or `*mut T` base (`payload = 0`).
    deref = 0,
    /// Projects struct or tuple field at zero-based `payload = field_ordinal`.
    field = 1,
    /// Indexes array, slice, or `#soa` column at dynamic SSA `payload = index_val_id.asInt()`.
    index = 2,
    /// Narrows an enum/Option/Result place to variant `payload = variant_ordinal` before `.field`.
    downcast = 3,
    /// Projects `#soa [S]` / `#soa [S; N]` to virtual column slice `[FieldTy]` for `payload = field_ordinal`.
    soa_elem = 4,
    /// Projects the `usize` length metadata of a slice or `#soa` slice (`payload = 0`).
    slice_len = 5,
};

/// 8-byte projection step stored in `MirBody.projections` (`DR-13` §3.2).
pub const MirProjection = extern struct {
    /// Projection discriminant.
    kind: ProjKind,
    /// Explicit zero padding preserving 4-byte alignment for `payload`.
    _pad: [3]u8 = .{ 0, 0, 0 },
    /// Kind-specific 32-bit operand (`field_ordinal`, `variant_ordinal`, or `MirValueId.asInt()`).
    payload: u32 = 0,
};

// --------------- MIR Opcodes, Operators & Flags ---------------

/// Canonical `MIR` instruction opcode (`0..24`, `DR-13` §3.3 & `DR-02` Deliverable 3).
pub const MirOp = enum(u8) {
    /// Formal basic-block SSA parameter (`lhs = block_id.asInt(), rhs = param_ordinal`).
    block_param = 0,

    // Ghost Lifetime Bracket Instructions (`1..4`, zero runtime cost; stripped after Phase 6):
    /// Opens an immutable `let` borrow access over `PlaceId(lhs)` (`rhs = BorrowMode`).
    ghost_access_let = 1,
    /// Opens an exclusive `inout` read-write access over `PlaceId(lhs)` (`rhs = BorrowMode`).
    ghost_access_inout = 2,
    /// Opens an uninitialized `set` write-must-init access over `PlaceId(lhs)` (`rhs = BorrowMode`).
    ghost_access_set = 3,
    /// Closes the Ghost access token `MirValueId(lhs)` in strict LIFO bracket order.
    ghost_access_end = 4,

    // Ghost Storage State Instructions (`5..7`, zero runtime cost; stripped after Phase 6):
    /// Marks `LocalId(lhs)` as initialized.
    ghost_storage_init = 5,
    /// Marks `PlaceId(lhs)` as moved-from (`uninitialized` for non-`Copy` types).
    ghost_storage_move = 6,
    /// Marks `LocalId(lhs)` as dead / deinitialized on scope exit.
    ghost_storage_deinit = 7,

    // Pure SSA Value Instructions (`8..17`):
    /// Materializes scalar or interned constant `MirBody.consts[lhs]`.
    const_scalar = 8,
    /// Pure SSA identity copy (`lhs = src_val_id`, `aux_u16 = 0`).
    copy_val = 9,
    /// Typed binary arithmetic, bitwise, or comparison op (`aux_u16 = BinOpKind`, `lhs, rhs = MirValueId`).
    bin_op = 10,
    /// Typed unary arithmetic, logical, or cast op (`aux_u16 = UnaryOpKind`, `lhs = src_val_id`).
    unary_op = 11,
    /// Constructs a tuple, array, struct, or enum/Option/Result SSA value (`aux_u16 = AggregateKind`).
    aggregate_make = 12,
    /// Extracts field/element `rhs` from aggregate SSA value `MirValueId(lhs)`.
    aggregate_extract = 13,
    /// Functional aggregate update (`lhs = agg_val_id`, `rhs = extra_args_idx` `[ordinal, val_id]`).
    aggregate_insert = 14,
    /// Extracts LSB bit-slice `BitSpec.fromU32(rhs)` from backing integer `MirValueId(lhs)`.
    bitfield_extract = 15,
    /// Functional LSB bit-slice update (`lhs = extra_args_idx` `[backing_val, new_val]`, `rhs = BitSpec`).
    bitfield_insert = 16,
    /// Resolves function item `DefId(lhs)` / `SymbolIndex(rhs)` into a callable value.
    fn_addr = 17,

    // Memory Place & Intrinsic Instructions (`18..24`):
    /// Loads a value from `PlaceId(lhs)`.
    place_load = 18,
    /// Stores `MirValueId(rhs)` into `PlaceId(lhs)`.
    place_store = 19,
    /// Reads the active integer variant tag of enum/Option/Result `PlaceId(lhs)`.
    place_discriminant = 20,
    /// Writes integer variant tag `rhs` into enum/Option/Result `PlaceId(lhs)`.
    place_set_discrim = 21,
    /// Materializes `&place` (`rhs = 0`) or `&mut place` (`rhs = 1`) for `PlaceId(lhs)`.
    place_addr = 22,
    /// Extracts homogeneous column slice `[FieldTy]` for field `rhs` from `#soa` `PlaceId(lhs)`.
    soa_column_slice = 23,
    /// Compiler intrinsic (`aux_u16 = MirIntrinsicKind`, `lhs = extra_start, rhs = extra_len`).
    intrinsic_op = 24,

    /// Returns `true` if `self` is a Phase 6 Ghost Lifetime or Ghost Storage instruction (`1..7`).
    pub inline fn isGhost(self: MirOp) bool {
        const raw = @backingInt(self);
        return raw >= @backingInt(MirOp.ghost_access_let) and
            raw <= @backingInt(MirOp.ghost_storage_deinit);
    }

    /// Returns `true` if `self` opens a Ghost Lifetime bracket (`let`, `inout`, or `set`).
    pub inline fn isGhostAccessOpen(self: MirOp) bool {
        return self == .ghost_access_let or
            self == .ghost_access_inout or
            self == .ghost_access_set;
    }
};

/// Ghost access sub-classification encoded in `MirInst.operands.rhs` on `ghost_access_*`.
pub const GhostBorrowKind = enum(u8) {
    /// Scoped Hylo parameter or temporary value projection.
    scoped_projection = 0,
    /// Explicit `&place` or `&mut place` reference creation.
    addr_borrow = 1,
    /// Guard evaluation temporary immutable borrow (`DR-13` §4.1.6).
    match_guard = 2,
};

/// Explicit signed, unsigned, and IEEE-754 binary opcodes in `MIR`.
pub const BinOpKind = enum(u8) {
    // Checked integer arithmetic (`0..12`, traps / `E0507` on overflow or div-by-zero):
    /// Checked signed integer addition (`+`).
    sadd_checked = 0,
    /// Checked unsigned integer addition (`+`).
    uadd_checked = 1,
    /// Checked signed integer subtraction (`-`).
    ssub_checked = 2,
    /// Checked unsigned integer subtraction (`-`).
    usub_checked = 3,
    /// Checked signed integer multiplication (`*`).
    smul_checked = 4,
    /// Checked unsigned integer multiplication (`*`).
    umul_checked = 5,
    /// Checked signed integer division (`/`, traps on zero or `MIN / -1`).
    sdiv_checked = 6,
    /// Checked unsigned integer division (`/`, traps on zero).
    udiv_checked = 7,
    /// Checked signed integer remainder (`%`, traps on zero or `MIN % -1`).
    srem_checked = 8,
    /// Checked unsigned integer remainder (`%`, traps on zero).
    urem_checked = 9,
    /// Checked left shift (`<<`, traps if shift >= bit width).
    shl_checked = 10,
    /// Checked arithmetic right shift (`>>` signed, traps if shift >= bit width).
    ashr_checked = 11,
    /// Checked logical right shift (`>>` unsigned, traps if shift >= bit width).
    lshr_checked = 12,

    // Wrapping modular integer arithmetic (`13..18`):
    /// Wrapping modular integer addition (`+%`).
    add_wrap = 13,
    /// Wrapping modular integer subtraction (`-%`).
    sub_wrap = 14,
    /// Wrapping modular integer multiplication (`*%`).
    mul_wrap = 15,
    /// Wrapping modular left shift (`<<%`).
    shl_wrap = 16,
    /// Wrapping modular arithmetic right shift (`>>%` signed).
    ashr_wrap = 17,
    /// Wrapping modular logical right shift (`>>%` unsigned).
    lshr_wrap = 18,

    // Saturating integer arithmetic (`19..24`):
    /// Saturating signed integer addition (`+|`).
    sadd_sat = 19,
    /// Saturating unsigned integer addition (`+|`).
    uadd_sat = 20,
    /// Saturating signed integer subtraction (`-|`).
    ssub_sat = 21,
    /// Saturating unsigned integer subtraction (`-|`).
    usub_sat = 22,
    /// Saturating signed integer multiplication (`*|`).
    smul_sat = 23,
    /// Saturating unsigned integer multiplication (`*|`).
    umul_sat = 24,

    // IEEE-754 floating-point arithmetic (`25..29`):
    /// IEEE-754 floating-point addition (`+`).
    fadd = 25,
    /// IEEE-754 floating-point subtraction (`-`).
    fsub = 26,
    /// IEEE-754 floating-point multiplication (`*`).
    fmul = 27,
    /// IEEE-754 floating-point division (`/`).
    fdiv = 28,
    /// IEEE-754 floating-point remainder (`%`).
    frem = 29,

    // Bitwise integer/boolean operations (`30..32`):
    /// Bitwise or non-short-circuiting boolean AND (`&`).
    bit_and = 30,
    /// Bitwise or non-short-circuiting boolean OR (`|`).
    bit_or = 31,
    /// Bitwise or boolean XOR (`^`).
    bit_xor = 32,

    // Relational & equality comparisons (`33..46`, yielding `.bool_ty`):
    /// Equality comparison (`==`).
    eq = 33,
    /// Inequality comparison (`!=`).
    ne = 34,
    /// Signed integer less-than (`<`).
    slt = 35,
    /// Unsigned integer less-than (`<`).
    ult = 36,
    /// IEEE-754 floating-point less-than (`<`).
    flt = 37,
    /// Signed integer less-than-or-equal (`<=`).
    sle = 38,
    /// Unsigned integer less-than-or-equal (`<=`).
    ule = 39,
    /// IEEE-754 floating-point less-than-or-equal (`<=`).
    fle = 40,
    /// Signed integer greater-than (`>`).
    sgt = 41,
    /// Unsigned integer greater-than (`>`).
    ugt = 42,
    /// IEEE-754 floating-point greater-than (`>`).
    fgt = 43,
    /// Signed integer greater-than-or-equal (`>=`).
    sge = 44,
    /// Unsigned integer greater-than-or-equal (`>=`).
    uge = 45,
    /// IEEE-754 floating-point greater-than-or-equal (`>=`).
    fge = 46,
};

/// Explicit unary arithmetic, logical, and conversion opcodes in `MIR`.
pub const UnaryOpKind = enum(u8) {
    /// Checked signed integer negation (`-x`, traps on `MIN`).
    sneg_checked = 0,
    /// Wrapping modular integer negation (`0 -% x`).
    neg_wrap = 1,
    /// IEEE-754 floating-point negation (`-x`).
    fneg = 2,
    /// Boolean logical negation (`!b` / `not b`).
    bool_not = 3,
    /// Bitwise integer complement (`~x`).
    bit_not = 4,
    /// Signed integer sign-extension (`i8 -> i32`, etc.).
    int_sext = 5,
    /// Unsigned integer or `bool`/`char` zero-extension (`u8 -> u32`, `bool -> u8`, etc.).
    int_zext = 6,
    /// Integer truncation (`i64 -> i32`, etc.).
    int_trunc = 7,
    /// Signed integer to IEEE-754 float conversion (`i32 -> f64`).
    int_to_float_signed = 8,
    /// Unsigned integer to IEEE-754 float conversion (`u32 -> f64`).
    int_to_float_unsigned = 9,
    /// IEEE-754 float to signed integer truncating conversion (`f64 -> i32`).
    float_to_int_signed = 10,
    /// IEEE-754 float to unsigned integer truncating conversion (`f64 -> u32`).
    float_to_int_unsigned = 11,
    /// `f32 -> f64` lossless promotion.
    float_promote = 12,
    /// `f64 -> f32` round-to-nearest-even demotion.
    float_demote = 13,
    /// Equal-width value bitcast (forbidden on pointers in `MirVm` -> `E0503`).
    bitcast_op = 14,
    /// Pointer-to-pointer or pointer-to-integer cast (pointer-to-int forbidden in `MirVm` -> `E0503`).
    ptr_cast = 15,
    /// Extracts the active integer discriminant tag from an SSA enum/Option/Result value.
    ssa_discriminant = 16,
    /// Extracts payload for variant ordinal `rhs` from an SSA enum/Option/Result value.
    ssa_variant_payload = 17,
};

/// Sub-kind encoded in `MirInst.aux_u16` on `MirOp.aggregate_make`.
pub const AggregateKind = enum(u8) {
    /// Tuple value `(e0, e1, …)` (`lhs = extra_start, rhs = extra_len`).
    tuple_agg = 0,
    /// Struct value `S { f0, f1, … }` in canonical field order (`lhs = extra_start, rhs = extra_len`).
    struct_agg = 1,
    /// Fixed array `[e0, e1, …]` (`lhs = extra_start, rhs = extra_len`).
    array_elems = 2,
    /// Fixed array repeat `[elem; count]` (`lhs = elem_val_id, rhs = repeat_count`).
    array_repeat = 3,
    /// Tagged union / enum / `Option` / `Result` (`lhs = extra_start, rhs = (tag_ord << 16) | extra_len`).
    tagged_variant = 4,
    /// String interpolation concatenation (`lhs = extra_start, rhs = extra_len`).
    str_concat = 5,
    /// Closure value packaging (`lhs = fn_def_id, rhs = extra_len_prefixed_captures`).
    closure_make = 6,
    /// Stack-borrowed `FmtArgs` construction (`lhs = extra_start, rhs = extra_len`, `SE-12`).
    fmt_args_make = 7,
};

/// Compiler intrinsic sub-kind encoded in `MirInst.aux_u16` on `MirOp.intrinsic_op`.
pub const MirIntrinsicKind = enum(u16) {
    /// `@compile_assert(cond, msg)` runtime/comptime assertion check.
    compile_assert = 0,
    /// `@compile_error(msg)` unconditional trap.
    compile_error = 1,
    /// `@embed_bytes(path)` embedded byte slice load.
    embed_bytes = 2,
    /// Derived `Debug.debug(&self) -> str` formatting intrinsic.
    derive_debug_fmt = 3,
    /// Polymorphic `@size_of[T]()` (`operands.lhs = TypeId.asInt()`, `operands.rhs = 0`).
    size_of = 4,
    /// Polymorphic `@align_of[T]()` (`operands.lhs = TypeId.asInt()`, `operands.rhs = 0`).
    align_of = 5,
    /// Polymorphic `@type_name[T]()` (`operands.lhs = TypeId.asInt()`, `operands.rhs = 0`).
    type_name = 6,
    /// `@as_bytes(&val)` / `val.as_bytes()` wire slice view (`extra_args = [ref_val]`).
    as_bytes = 7,
    /// `@bit_cast[Dst](src)` layout-checked bitwise reinterpretation (`extra_args = [src_val]`).
    bit_cast = 8,
    /// `@from_bytes[T](bytes)` fallible wire deserialization (`extra_args = [bytes_val]`).
    from_bytes = 9,
    /// `@view_bytes[T](bytes)` aligned zero-copy wire view (`extra_args = [bytes_val]`).
    view_bytes = 10,
    /// `@drop_trace(id)` deterministic destructor execution breadcrumb (`extra_args = [id_val]`).
    drop_trace = 11,
    /// Dynamic index bounds check (`extra_args = [idx_val, len_val, container_kind_val]`).
    bounds_check = 12,
    /// Dynamic slice sub-range check (`extra_args = [lo_val, hi_val, len_val]`).
    slice_range_check = 13,
    /// Checked `.narrow[Dst]()` integer narrowing (`extra_args = [src_val, min_val, max_val]`).
    narrow_check = 14,
    /// Fallible `.try_narrow[Dst]()` integer narrowing (`extra_args = [src_val, min_val, max_val]`).
    try_narrow = 15,
    /// Zero-fills full `sizeof(T)` bytes of a `@zero_pad` destination (`lhs = PlaceId, rhs = NONE_U32`).
    zero_pad = 16,
    /// Unconditional in-place destructor execution (`lhs = PlaceId, rhs = NONE_U32`).
    drop_in_place = 17,
    /// Flag-guarded conditional destructor execution (`lhs = PlaceId, rhs = flag_val`).
    drop_if_live = 18,
    /// Immediate non-unwinding abort guard inside a vacated `inout` `subscript` (`lhs = NONE_U32, rhs = NONE_U32`).
    abort_vacated_panic = 19,
    /// Ghost manual deallocation marker stripped in Pass `D3` (`lhs = PlaceId, rhs = region_or_none`).
    ghost_storage_free = 20,
    /// `@atomic_load[T](ptr, ordering) -> T` (`extra_args = [ptr_val, ordering_val]`).
    atomic_load = 21,
    /// `@atomic_store[T](ptr, val, ordering) -> unit` (`extra_args = [ptr_val, val, ordering_val]`).
    atomic_store = 22,
    /// `@atomic_rmw_add[T](ptr, val, ordering) -> T` (`extra_args = [ptr_val, val, ordering_val]`).
    atomic_rmw_add = 23,
    /// `@atomic_rmw_sub[T](ptr, val, ordering) -> T` (`extra_args = [ptr_val, val, ordering_val]`).
    atomic_rmw_sub = 24,
    /// `@atomic_rmw_xchg[T](ptr, val, ordering) -> T` (`extra_args = [ptr_val, val, ordering_val]`).
    atomic_rmw_xchg = 25,
    /// `@atomic_cmpxchg[T](ptr, exp, des, succ, fail, is_weak?) -> (T, bool)` (`extra_args = [ptr, exp, des, succ, fail, is_weak?]`).
    atomic_cmpxchg = 26,
    /// `@atomic_fence(ordering) -> unit` (`extra_args = [ordering_val]`).
    atomic_fence = 27,
    /// `@simd_splat[V](scalar) -> V` (`extra_args = [scalar_val]`).
    simd_splat = 28,
    /// `@simd_add[V](lhs, rhs) -> V` (`extra_args = [lhs_val, rhs_val]`).
    simd_add = 29,
    /// `@simd_sub[V](lhs, rhs) -> V` (`extra_args = [lhs_val, rhs_val]`).
    simd_sub = 30,
    /// `@simd_mul[V](lhs, rhs) -> V` (`extra_args = [lhs_val, rhs_val]`).
    simd_mul = 31,
    /// `@simd_reduce_add[V](vec) -> Lane` (`extra_args = [vec_val]`).
    simd_reduce_add = 32,
    /// `@panic(msg) -> never` (`extra_args = [msg_val]`).
    panic = 33,
    /// `@trap() -> never` (`extra_args = []`).
    trap = 34,
    /// `@poll_reload(&mut state) -> bool` (`extra_args = [state_ref_val]`).
    poll_reload = 35,
    /// `@sys_write(fd, buf) -> isize` (`extra_args = [fd_val, buf_val]`).
    sys_write = 36,
    /// `@sys_exit(code) -> never` (`extra_args = [code_val]`).
    sys_exit = 37,
    /// Subslice view construction (`extra_args = [base_val, lo_val, hi_val]`, `SE-04` / `SE-05`).
    subslice_make = 38,
    /// Implicit `context.<field>` slot read (`extra_args = [slot_ord_val]`, `SE-08`).
    ctx_get = 39,
    /// Implicit `context.<field>` slot write (`extra_args = [slot_ord_val, new_val]`, `SE-08`).
    ctx_set = 40,
    /// Ghost `with context.<allocator>` region push (`extra_args = [slot_ord_val, region_val]`, `SE-08`).
    ghost_ctx_region_push = 41,
    /// Ghost `with context.<allocator>` region pop (`extra_args = [slot_ord_val]`, `SE-08`).
    ghost_ctx_region_pop = 42,
    /// Synthesis-mode single-hole string formatting (`extra_args = [val_id, spec_lo_id, spec_hi_id]`, `SE-12`).
    fmt_value = 43,
    /// Inline `Future[T]` frame construction (`extra_args = [def_val, sym_val, callee_val, args…]`, `DR-08`).
    async_future_make = 44,
    /// Structured `TaskGroup` nursery scope entry (`extra_args = []`, `DR-08`).
    async_task_group_enter = 45,
    /// Nursery child task spawn (`extra_args = [is_local_val, group_ref_val, task_fut_val, loan_vals…]`, `DR-08`).
    async_spawn = 46,
    /// Linear `TaskHandle.join()` future construction (`extra_args = [handle_val]`, `DR-08`).
    async_join = 47,
    /// Linear `TaskHandle.cancel()` or `TaskGroup.cancel_all()` (`extra_args = [target_val, opt_query_val]`, `DR-08`).
    async_cancel = 48,
    /// Structured `TaskGroup` nursery exit barrier (`extra_args = [group_val]`, `DR-08`).
    async_task_group_exit = 49,
    /// Cooperative reactor yield future construction (`extra_args = []`, `DR-08`).
    async_yield = 50,
    /// Synchronous root executor entry (`block_on(fut)`, `extra_args = [fut_val]`, `DR-08`).
    async_block_on = 51,
    /// Polymorphic `@implements[T, Bound]()` (`operands.lhs = T.asInt()`, `operands.rhs = Bound.asInt()`).
    implements = 52,
    /// Polymorphic `T.MIN` scalar bound (`operands.lhs = T.asInt()`, `operands.rhs = 0`).
    int_min = 53,
    /// Polymorphic `T.MAX` scalar bound (`operands.lhs = T.asInt()`, `operands.rhs = 0`).
    int_max = 54,
    /// Polymorphic `T.BITS` bit width (`operands.lhs = T.asInt()`, `operands.rhs = 0`).
    int_bits = 55,
    /// Count leading zero bits (`extra_args = [val]`).
    scalar_clz = 56,
    /// Count trailing zero bits (`extra_args = [val]`).
    scalar_ctz = 57,
    /// Count set `1` bits (`extra_args = [val]`).
    scalar_popcnt = 58,
    /// Byte-order reversal (`extra_args = [val]`).
    scalar_bswap = 59,
    /// Bitwise rotate left (`extra_args = [val, count]`).
    scalar_rotl = 60,
    /// Bitwise rotate right (`extra_args = [val, count]`).
    scalar_rotr = 61,
    /// Raw pointer null check (`extra_args = [ptr]`).
    ptr_is_null = 62,
    /// Raw pointer element offset (`extra_args = [ptr, delta, is_sub_flag]`).
    ptr_offset = 63,
    /// Checked slice split (`extra_args = [slice_val, mid_val, is_mut_flag]`).
    slice_split_at = 64,
    /// In-place slice element reversal (`extra_args = [mut_slice_val]`).
    slice_reverse = 65,
    /// `#soa Vec[S].new()` / `.in_arena(&mut arena)` (`extra_args = []` or `[arena_handle]`).
    soa_vec_new = 66,
    /// `#soa Vec[S].with_capacity(cap)` / `.try_with_capacity(cap)` (`extra_args = [alloc_val, cap, is_try]`).
    soa_vec_with_cap = 67,
    /// `#soa Vec[S].len(&self) -> usize` (`extra_args = [ref_val]`).
    soa_vec_len = 68,
    /// `#soa Vec[S].capacity(&self) -> usize` (`extra_args = [ref_val]`).
    soa_vec_cap = 69,
    /// `#soa Vec[S].push(&mut self, val)` / `.try_push` (`extra_args = [mut_ref_val, elem_val, is_try]`).
    soa_vec_push = 70,
    /// `#soa Vec[S].pop(&mut self) -> S?` (`extra_args = [mut_ref_val]`).
    soa_vec_pop = 71,
    /// `#soa Vec[S].clear(&mut self)` (`extra_args = [mut_ref_val]`).
    soa_vec_clear = 72,
    /// `#soa Vec[S].reserve(&mut self, add)` / `.try_reserve` (`extra_args = [mut_ref_val, add_val, is_try]`).
    soa_vec_reserve = 73,
    /// `#soa Vec[S].as_soa_slice` / `.as_mut_soa_slice` (`extra_args = [ref_val, is_mut]`).
    soa_vec_as_slice = 74,
    /// `#soa Vec[S]` column slice projection (`extra_args = [ref_val, field_ord, is_mut]`).
    soa_vec_col_slice = 75,
    /// `@ctx_next_rng_seed() -> u64` (`extra_args = []`).
    ctx_next_rng_seed = 76,
    /// `@tls_scratch_ptr() -> *mut opaque` (`extra_args = []`, `64 B` zero-init TLS).
    tls_scratch_ptr = 77,
    /// `@tls_alloc_state() -> *mut opaque` (`extra_args = []`, `256 B` zero-init TLS).
    tls_alloc_state = 78,
    /// `@fmt_write(writer, args) -> unit!FmtError` (`extra_args = [writer_mut_ref, fmt_args]`).
    fmt_write = 79,
    /// `@memcpy(dst, src, byte_len) -> unit` (`extra_args = [dst, src, byte_len]`).
    memcpy = 80,
    /// `@memmove(dst, src, byte_len) -> unit` (`extra_args = [dst, src, byte_len]`).
    memmove = 81,
    /// `@memset(dst, byte, byte_len) -> unit` (`extra_args = [dst, byte, byte_len]`).
    memset = 82,
    /// `@ptr_copy[T](src, dst, count) -> unit` (`extra_args = [src, dst, count]`).
    ptr_copy = 83,
    /// `@ptr_copy_nonoverlapping[T](src, dst, count) -> unit` (`extra_args = [src, dst, count]`).
    ptr_copy_nonoverlapping = 84,
    /// `@ptr_read[T](src) -> T` (`extra_args = [src]`).
    ptr_read = 85,
    /// `@ptr_write[T](dst, val) -> unit` (`extra_args = [dst, val]`).
    ptr_write = 86,
    /// `@ptr_drop_in_place[T](ptr) -> unit` (`extra_args = [ptr]`).
    ptr_drop_in_place = 87,
    /// `@forget[T](val) -> unit` (`extra_args = [val]`).
    forget = 88,
    /// `@slice_from_raw_parts[T](ptr, len) -> &[T]` / `&mut [T]` (`extra_args = [ptr, len]`).
    slice_from_raw_parts = 89,
    /// `@str_from_utf8_unchecked(bytes) -> str` (`extra_args = [bytes]`).
    str_from_utf8_unchecked = 90,
    /// `@from_le_bytes[T](bytes) -> T` (`extra_args = [bytes]`).
    from_le_bytes = 91,
    /// `@from_be_bytes[T](bytes) -> T` (`extra_args = [bytes]`).
    from_be_bytes = 92,
    /// `@to_le_bytes[T](val) -> [u8; sizeof(T)]` (`extra_args = [val]`).
    to_le_bytes = 93,
    /// `@to_be_bytes[T](val) -> [u8; sizeof(T)]` (`extra_args = [val]`).
    to_be_bytes = 94,
    /// `@sqrt[T](val) -> T` (`extra_args = [val]`).
    sqrt = 95,
    /// `@sys_mmap(len, align) -> *mut u8` (`extra_args = [len, align]`).
    sys_mmap = 96,
    /// `@sys_munmap(ptr, len) -> unit` (`extra_args = [ptr, len]`).
    sys_munmap = 97,
    /// `@wasm_memory_grow(mem_idx, delta_pages) -> usize` (`extra_args = [mem_idx, delta_pages]`).
    wasm_memory_grow = 98,
    /// `@simd_load_unaligned[V](ptr) -> V` (`extra_args = [ptr]`).
    simd_load_unaligned = 99,
    /// `@simd_and[V](lhs, rhs) -> V` (`extra_args = [lhs, rhs]`).
    simd_and = 100,
    /// `@simd_or[V](lhs, rhs) -> V` (`extra_args = [lhs, rhs]`).
    simd_or = 101,
    /// `@simd_xor[V](lhs, rhs) -> V` (`extra_args = [lhs, rhs]`).
    simd_xor = 102,
    /// `@simd_eq[V](lhs, rhs) -> Mask` (`extra_args = [lhs, rhs]`).
    simd_eq = 103,
    /// `@simd_gt_s8[V](lhs, rhs) -> V` (`extra_args = [lhs, rhs]`).
    simd_gt_s8 = 104,
    /// `@simd_lt_s8[V](lhs, rhs) -> V` (`extra_args = [lhs, rhs]`).
    simd_lt_s8 = 105,
    /// `@simd_swizzle[V](table, indices) -> V` (`extra_args = [table, indices]`).
    simd_swizzle = 106,
    /// `@simd_shl_u8[V](vec, shift) -> V` (`extra_args = [vec, shift]`).
    simd_shl_u8 = 107,
    /// `@simd_shr_u8[V](vec, shift) -> V` (`extra_args = [vec, shift]`).
    simd_shr_u8 = 108,
    /// `@simd_bitmask[V](vec) -> u32` (`extra_args = [vec]`).
    simd_bitmask = 109,

    /// Returns `true` when `operands.lhs` encodes a `PlaceId` rather than `extra_args` or `TypeId`.
    pub inline fn hasPlaceInLhs(self: MirIntrinsicKind) bool {
        return switch (self) {
            .zero_pad, .drop_in_place, .drop_if_live, .ghost_storage_free => true,
            else => false,
        };
    }

    /// Returns `true` when `operands.rhs` encodes an SSA `MirValueId` liveness flag (`drop_if_live`).
    pub inline fn hasSsaFlagInRhs(self: MirIntrinsicKind) bool {
        return self == .drop_if_live;
    }

    /// Returns `true` when `operands.lhs` encodes a reflected `TypeId` (`size_of`, `align_of`, `type_name`, `implements`, `int_*`).
    pub inline fn hasTypeIdInLhs(self: MirIntrinsicKind) bool {
        return switch (self) {
            .size_of, .align_of, .type_name, .implements, .int_min, .int_max, .int_bits => true,
            else => false,
        };
    }

    /// Returns `true` when `operands` slices `MirBody.extra_args[lhs .. lhs + rhs]`.
    pub inline fn hasExtraArgs(self: MirIntrinsicKind) bool {
        return !self.hasPlaceInLhs() and !self.hasTypeIdInLhs() and self != .abort_vacated_panic;
    }

    /// Returns `true` when `R5` DCE must treat this intrinsic as a live side-effecting root.
    pub inline fn isSideEffectingRoot(self: MirIntrinsicKind) bool {
        return switch (self) {
            .compile_assert,
            .compile_error,
            .drop_trace,
            .bounds_check,
            .slice_range_check,
            .narrow_check,
            .zero_pad,
            .drop_in_place,
            .drop_if_live,
            .abort_vacated_panic,
            .ghost_storage_free,
            .atomic_load,
            .atomic_store,
            .atomic_rmw_add,
            .atomic_rmw_sub,
            .atomic_rmw_xchg,
            .atomic_cmpxchg,
            .atomic_fence,
            .panic,
            .trap,
            .poll_reload,
            .sys_write,
            .sys_exit,
            .ctx_set,
            .ghost_ctx_region_push,
            .ghost_ctx_region_pop,
            .async_task_group_enter,
            .async_spawn,
            .async_join,
            .async_cancel,
            .async_task_group_exit,
            .async_block_on,
            .slice_split_at,
            .slice_reverse,
            .soa_vec_with_cap,
            .soa_vec_push,
            .soa_vec_pop,
            .soa_vec_clear,
            .soa_vec_reserve,
            .ctx_next_rng_seed,
            .fmt_write,
            .memcpy,
            .memmove,
            .memset,
            .ptr_copy,
            .ptr_copy_nonoverlapping,
            .ptr_read,
            .ptr_write,
            .ptr_drop_in_place,
            .forget,
            .sys_mmap,
            .sys_munmap,
            .wasm_memory_grow,
            => true,
            else => false,
        };
    }

    /// Returns `true` when Pass `D3` Ghost stripping erases this intrinsic (`ghost_storage_free` / `ghost_ctx_region_*`).
    pub inline fn isGhostIntrinsic(self: MirIntrinsicKind) bool {
        return switch (self) {
            .ghost_storage_free, .ghost_ctx_region_push, .ghost_ctx_region_pop => true,
            else => false,
        };
    }

    /// Returns `true` when this intrinsic reads or mutates the implicit `Context` parameter (`V6` / `SE-08`).
    pub inline fn isContextIntrinsic(self: MirIntrinsicKind) bool {
        return switch (self) {
            .ctx_get,
            .ctx_set,
            .ghost_ctx_region_push,
            .ghost_ctx_region_pop,
            .async_task_group_enter,
            .async_spawn,
            .async_join,
            .async_cancel,
            .async_task_group_exit,
            .async_yield,
            .async_block_on,
            .ctx_next_rng_seed,
            .soa_vec_new,
            .soa_vec_with_cap,
            .fmt_write,
            => true,
            else => false,
        };
    }
};

/// Packed 1-byte instruction property flags in `MirInst` (`DR-13` §3.3).
pub const InstFlags = packed struct(u8) {
    /// `true` if executing this instruction has observable side effects or memory writes.
    has_side_effects: bool = false,
    /// `true` if emitted inside an `unsafe` block.
    is_unsafe: bool = false,
    /// `true` if synthesized by compiler lowering (cleanup pads, projections, bounds checks).
    is_synthetic: bool = false,
    /// `true` if this instruction can trap on overflow or division by zero.
    has_trap_risk: bool = false,
    /// `true` if this instruction constructs a stack-pinned `@local` / regional closure (`V6`).
    is_local_closure: bool = false,
    /// `true` if any trap raised by this instruction inside a `Fix-06B` vacated window must abort immediately.
    is_abort_on_panic: bool = false,
    /// `true` if this `.usub_checked` / `.sub_wrap` computes a `$ - expr` sequence length offset (`SE-04`).
    is_dollar_sub: bool = false,
    /// Reserved zero padding bit.
    _pad: u1 = 0,
};

/// 16-byte SoA instruction record in `MirBody.insts` (`1 + 1 + 2 + 4 + 8 = 16B`, `DR-13` §3.3).
pub const MirInst = struct {
    /// Instruction opcode (`1B`).
    op: MirOp,
    /// Property bitflags (`1B`).
    flags: InstFlags = .{},
    /// Auxiliary 16-bit sub-opcode (`BinOpKind`, `UnaryOpKind`, `AggregateKind`, `MirIntrinsicKind`).
    aux_u16: u16 = 0,
    /// Result `TypeId` produced by this instruction (`.unit_ty` for void/store/ghost ops, `4B`).
    type_id: TypeId,
    /// Dual 32-bit operand words (`8B`).
    operands: Operands = .{},

    /// 8-byte operand payload of a `MirInst`.
    pub const Operands = extern struct {
        /// Primary 32-bit operand (`MirValueId`, `PlaceId`, `LocalId`, `const_idx`, or `extra_start`).
        lhs: u32 = 0,
        /// Secondary 32-bit operand (`MirValueId`, ordinal, `BitSpec`, or `extra_len`).
        rhs: u32 = 0,
    };
};

// ----------- Terminators, Basic Blocks & CFG Edges ------------

/// Control-flow terminator kind ending every `MirBasicBlock` (`DR-13` §3.2).
pub const TerminatorKind = enum(u8) {
    /// Statically unreachable point (`never`, exhausted match).
    unreachable_term = 0,
    /// Function return (`cond_or_val = ret_val_id` or `NONE_U32` when returning `_0`).
    ret = 1,
    /// Unconditional branch (`edge_len = 1`, `extra_edges[edge_start]`).
    br = 2,
    /// Boolean conditional branch (`cond_or_val = cond_val_id`, `edge_len = 2`: `[then_edge, else_edge]`).
    cond_br = 3,
    /// Multi-way integer/tag switch (`cond_or_val = discr_val_id`, `edge_len = cases + 1`, last is default).
    switch_int = 4,
    /// Direct or indirect call (`cond_or_val = call_site_idx`, `extra_edges[edge_start]` = `normal_bb` edge).
    call = 5,
    /// Deterministic trap (`aux_u8 = MirTrapReason`).
    trap = 6,
    /// Structured `.await` suspension (`cond_or_val = fut_val_id`, `edge_len = 2`: `[resume_edge, cancel_edge]`).
    coro_suspend = 7,
};

/// Trap classification encoded in `MirTerminator.aux_u8` when `kind == .trap`.
pub const MirTrapReason = enum(u8) {
    /// Unreachable code executed at runtime/comptime.
    unreachable_reached = 0,
    /// Integer overflow or division by zero (`E0507` in `MirVm`).
    arithmetic_overflow = 1,
    /// Slice or array bounds check failure (`E0504` in `MirVm`).
    bounds_check = 2,
    /// Explicit `@compile_assert` / `@compile_error` failure (`E0510` in `MirVm`).
    assertion_failed = 3,
};

/// 12-byte control-flow terminator embedded at the end of `MirBasicBlock`.
pub const MirTerminator = extern struct {
    /// Terminator discriminant (`1B`).
    kind: TerminatorKind = .unreachable_term,
    /// Trap reason or auxiliary tag (`1B`).
    aux_u8: u8 = 0,
    /// Count of outgoing `MirOutgoingEdge`s in `MirBody.extra_edges[edge_start .. edge_start + edge_len]` (`2B`).
    edge_len: u16 = 0,
    /// Condition `MirValueId`, return `MirValueId`, switch discriminant, or `MirCallSite` index (`4B`).
    cond_or_val: u32 = NONE_U32,
    /// Starting `EdgeId` index in `MirBody.extra_edges` (`4B`).
    edge_start: u32 = 0,
};

/// 32-byte basic block record in `MirBody.blocks`.
///
/// Packs `param_len: u14` (bits `0..13`), `is_sealed: bool` (bit `14`), and `is_cleanup_pad: bool`
/// (bit `15`) into `meta_bits: u16` so the entire `extern struct` is exactly 32 bytes with zero
/// hidden alignment padding.
pub const MirBasicBlock = extern struct {
    /// Start index of `MirOp.block_param` `MirValueId`s in `MirBody.block_params` (`4B`).
    param_start: u32 = 0,
    /// Start index of non-param instructions in `MirBody.block_insts` (`4B`).
    inst_start: u32 = 0,
    /// Number of instructions in `MirBody.block_insts[inst_start .. inst_start + inst_len]` (`4B`).
    inst_len: u32 = 0,
    /// Start index of incoming `EdgeId`s in `MirBody.pred_edges` (`4B`).
    pred_start: u32 = 0,
    /// Number of incoming `EdgeId`s (`<= MAX_BLOCK_PREDS = 65,534`, `2B`).
    pred_len: u16 = 0,
    /// Packed `param_len: u14 | (is_sealed << 14) | (is_cleanup_pad << 15)` (`2B`).
    meta_bits: u16 = 0,
    /// Outgoing control-flow terminator (`12B`).
    terminator: MirTerminator = .{},

    /// Returns the number of formal block parameters (`0 .. 16,383`).
    pub inline fn paramLen(self: MirBasicBlock) u14 {
        return @truncate(self.meta_bits & BLOCK_PARAM_LEN_MASK);
    }

    /// Sets the formal block parameter count (`param_count <= MAX_BLOCK_PARAMS`).
    pub inline fn setParamLen(self: *MirBasicBlock, param_count: u14) void {
        self.meta_bits = (self.meta_bits & ~BLOCK_PARAM_LEN_MASK) | @as(u16, param_count);
    }

    /// Returns `true` if all CFG predecessors of this block are known (`MirSsaBuilder`).
    pub inline fn isSealed(self: MirBasicBlock) bool {
        return (self.meta_bits & BLOCK_SEALED_BIT) != 0;
    }

    /// Updates the `is_sealed` flag bit.
    pub inline fn setSealed(self: *MirBasicBlock, is_sealed: bool) void {
        if (is_sealed) {
            self.meta_bits |= BLOCK_SEALED_BIT;
        } else {
            self.meta_bits &= ~BLOCK_SEALED_BIT;
        }
    }

    /// Returns `true` if this block is a shared cold `errdefer` / `defer` cleanup pad.
    pub inline fn isCleanupPad(self: MirBasicBlock) bool {
        return (self.meta_bits & BLOCK_CLEANUP_PAD_BIT) != 0;
    }

    /// Updates the `is_cleanup_pad` flag bit.
    pub inline fn setCleanupPad(self: *MirBasicBlock, is_cleanup: bool) void {
        if (is_cleanup) {
            self.meta_bits |= BLOCK_CLEANUP_PAD_BIT;
        } else {
            self.meta_bits &= ~BLOCK_CLEANUP_PAD_BIT;
        }
    }
};

/// 16-byte first-class outgoing CFG edge record in `MirBody.extra_edges`.
pub const MirOutgoingEdge = extern struct {
    /// Originating basic block (`4B`).
    src_bb: MirBlockId,
    /// Destination basic block (`4B`).
    target_bb: MirBlockId,
    /// Start index in `MirBody.extra_args` holding `MirValueId` block arguments (`4B`).
    args_start: u32 = 0,
    /// Number of `MirValueId` arguments passed along this edge (`2B`).
    args_len: u16 = 0,
    /// Index into `MirBody.switch_values` for `switch_int` case edges (`MAX_U16` otherwise, `2B`).
    case_tag_idx: u16 = std.math.maxInt(u16),
};

/// Call-site metadata side record referenced by `MirTerminator.cond_or_val` when `kind == .call`.
pub const MirCallSite = struct {
    /// Callee SSA value (`MirOp.fn_addr` or indirect function/closure `MirValueId`).
    callee_val: MirValueId,
    /// Direct target `DefId` when statically resolved (`DefId.NONE` for indirect calls).
    direct_def_id: DefId = .NONE,
    /// Direct target `SymbolIndex` when statically resolved (`.none` for indirect calls).
    direct_symbol: SymbolIndex = .none,
    /// Start index in `MirBody.extra_args` of call argument `MirValueId`s (or `PlaceId`s for `inout`/`set`).
    args_start: u32 = 0,
    /// Number of arguments passed to this call.
    args_len: u16 = 0,
    /// Start index in `MirBody.call_arg_modes` of `ParamMode` per argument.
    modes_start: u32 = 0,
    /// Start index in `MirBody.extra_args` of Ghost token `MirValueId`s opened strictly for this call
    /// and automatically closed at the top of `normal_bb` / cleanup pad.
    call_borrows_start: u32 = 0,
    /// Count of call-scoped Ghost tokens to close immediately after the call returns.
    call_borrows_len: u16 = 0,
    /// Start index in `MirBody.extra_args` of instantiated generic `TypeId` words for this call.
    type_args_start: u32 = 0,
    /// Count of instantiated generic `TypeId` words recorded for this call (`0` for non-generic calls).
    type_args_len: u16 = 0,
    /// Concrete return `TypeId` received by `normal_bb`'s single formal `%ret_val` parameter.
    ret_ty: TypeId,
    /// `true` if callee is marked `@noalloc` / `contextless` or built-in pure (`V6`).
    is_callee_contextless: bool = false,
    /// `true` if any panic raised during this call inside a `Fix-06B` vacated window must abort immediately.
    is_abort_on_panic: bool = false,
    /// `true` when calling a C ABI variadic prototype (`extern "C" fn(fixed…, ...)`, `SE-13`).
    is_c_variadic: bool = false,
    /// `true` when the call expression lies inside an `unsafe { … }` block or `unsafe fn` body.
    is_unsafe_call: bool = false,
    /// Number of fixed non-variadic parameters when `is_c_variadic` is `true` (`SE-13`).
    fixed_arity: u16 = 0,
    /// Source token of the call expression.
    origin_token: TokenIndex = .none,
};

/// Re-exported 1-byte `@must_vectorize` / `@vectorize_width` contract flags (`DR-20` Seam #4).
pub const LoopContractMask = hir.LoopContractMask;

/// Re-exported 8-byte SIMD loop contract descriptor (`DR-19` §1, `DR-20` Seam #4).
pub const LoopContractMeta = hir.LoopContractMeta;

/// 16-byte sparse loop-vectorization contract stored in `MirBody.loop_contracts` (`@sizeOf(MirBasicBlock) == 32`).
pub const MirLoopContractEntry = extern struct {
    /// Canonical loop header block ID (`4B`).
    header_bb: MirBlockId,
    /// Canonical loop back-edge latch block ID (`4B`).
    latch_bb: MirBlockId,
    /// Lowered `@must_vectorize` / `@vectorize_width(N)` contract metadata (`8B`).
    meta: LoopContractMeta = .{},
};

/// 16-byte `$O(1)$` embedded binary blob descriptor stored in `MirConst.raw_blob` (`DR-20` `D-03`).
pub const RawBlobConst = extern struct {
    /// Zero-based index into `MirBlobStore.blobs`.
    blob_id: u32,
    /// Log2 byte alignment of the embedded payload (`0` = 1-byte aligned).
    align_log2: u8 = 0,
    /// Explicit zero padding (`3B`).
    _pad: [3]u8 = .{ 0, 0, 0 },
    /// Exact byte length of the embedded payload.
    byte_len: u64,
};

/// 16-byte `@caller_location()` `SourceLoc` constant payload stored in `MirConst.source_loc` (`SE-17`).
pub const SourceLocConst = extern struct {
    /// Interned `.rodata` caller file path (`str`).
    file_sym: SymbolId,
    /// Interned `.rodata` caller function/item name (`str`).
    fn_sym: SymbolId,
    /// 1-based source line number (`u32`).
    line: u32,
    /// 1-based UTF-8 byte column number (`u32`).
    col: u32,
};

comptime {
    std.debug.assert(@sizeOf(SourceLocConst) == 16);
}

/// Constant scalar or aggregate literal stored in `MirBody.consts`.
pub const MirConst = union(enum) {
    /// Unit `()`.
    unit_val,
    /// Boolean scalar.
    bool_val: bool,
    /// Unicode codepoint scalar (`char`).
    char_val: u21,
    /// Signed or unsigned 128-bit integer scalar (interpreted via instruction `type_id`).
    int_val: i128,
    /// IEEE-754 64-bit float scalar.
    float_val: f64,
    /// Interned UTF-8 string literal (`SymbolId`).
    str_val: SymbolId,
    /// Byte slice literal (`SymbolId` into `StringInterner`).
    bytes_val: SymbolId,
    /// Pre-materialized `$O(1)$` `@embed_bytes` blob bypassing `StringInterner` (`DR-20` `D-03`).
    raw_blob: RawBlobConst,
    /// Materialized `@caller_location()` `SourceLoc` constant (`SE-17`).
    source_loc: SourceLocConst,
};

/// Deduplicated binary blob store populated by `materializeModuleEmbedBytes` prior to codegen.
pub const MirBlobStore = struct {
    /// Backing allocator owning all allocated byte slices and hash tables.
    allocator: std.mem.Allocator,
    /// Contiguous owned byte slices indexed by `RawBlobConst.blob_id`.
    blobs: std.ArrayListUnmanaged([]u8) = .empty,
    /// Relative path to `blob_id` deduplication map so identical `@embed_bytes` paths share one `.rodata` array.
    path_to_blob_id: std.StringHashMapUnmanaged(u32) = .empty,
    /// Owned relative path keys stored in `path_to_blob_id`.
    owned_paths: std.ArrayListUnmanaged([]u8) = .empty,

    /// Initializes an empty `MirBlobStore`.
    pub fn init(allocator: std.mem.Allocator) MirBlobStore {
        return .{ .allocator = allocator };
    }

    /// Releases all owned blob buffers and path keys.
    pub fn deinit(self: *MirBlobStore) void {
        for (self.blobs.items) |buf| {
            self.allocator.free(buf);
        }
        self.blobs.deinit(self.allocator);
        for (self.owned_paths.items) |path_key| {
            self.allocator.free(path_key);
        }
        self.owned_paths.deinit(self.allocator);
        self.path_to_blob_id.deinit(self.allocator);
        self.* = undefined;
    }

    /// Interns `bytes` under `rel_path` (or appends an anonymous blob when `rel_path.len == 0`) and returns `blob_id`.
    pub fn internBlob(self: *MirBlobStore, rel_path: []const u8, bytes: []const u8) !u32 {
        if (rel_path.len > 0) {
            if (self.path_to_blob_id.get(rel_path)) |existing_id| {
                if (existing_id < self.blobs.items.len and
                    std.mem.eql(u8, self.blobs.items[existing_id], bytes))
                {
                    return existing_id;
                }
            }
        }
        const blob_id: u32 = @intCast(self.blobs.items.len);
        const duped_bytes = try self.allocator.dupe(u8, bytes);
        errdefer self.allocator.free(duped_bytes);
        try self.blobs.append(self.allocator, duped_bytes);
        if (rel_path.len > 0 and !self.path_to_blob_id.contains(rel_path)) {
            const duped_path = try self.allocator.dupe(u8, rel_path);
            errdefer self.allocator.free(duped_path);
            try self.owned_paths.append(self.allocator, duped_path);
            try self.path_to_blob_id.put(self.allocator, duped_path, blob_id);
        }
        return blob_id;
    }

    /// Fetches the byte slice of `blob_id` in $O(1)$ time, or `null` if out of range.
    pub inline fn getBytes(self: *const MirBlobStore, blob_id: u32) ?[]const u8 {
        if (blob_id >= self.blobs.items.len) return null;
        return self.blobs.items[blob_id];
    }
};

/// Per-package sandbox policy governing `@embed_bytes` resolution (`DR-17` §5, `Fix-17` Gate D).
pub const EmbedPackageJail = union(enum) {
    /// Legacy single-file mode resolving through `virtual_files` or `workspace_root`.
    unrestricted_legacy,
    /// Host directory jail (`PackageId.root` or local `path` dependency) rejecting symlinks (`E0326`).
    host_dir_jailed: []const u8,
    /// Pure virtual `.cxtree` lookup (`PackageId >= 2` external packages); never touches host disk.
    cxtree_only: struct {
        /// Owning external `PackageId`.
        pkg_id: PackageId,
        /// Optional virtual root prefix (e.g., `"/cx/http@1.2.0"`, or `""` to infer from `origin_file_id`).
        virtual_root_prefix: []const u8 = "",
    },
};

/// Result of reading a host-directory-jailed `@embed_bytes` file via segment-by-segment `O_NOFOLLOW`.
pub const HostEmbedReadResult = union(enum) {
    /// Verified regular file contents allocated in caller `allocator`.
    ok: []u8,
    /// Path escaped sandbox, traversed a symlink/reparse point, targeted a non-regular file, or exceeded `max_bytes` (`E0326`).
    sandbox_escape: struct {
        /// Primary diagnostic message.
        message: []const u8,
        /// Primary span underline label.
        label: []const u8,
    },
    /// Regular missing-file or read error (`E0004` in jailed package mode / `E0503` in legacy mode).
    io_error: struct {
        /// `true` when the target file or intermediate directory does not exist.
        is_not_found: bool,
        /// Primary diagnostic message.
        message: []const u8,
        /// Primary span underline label.
        label: []const u8,
    },
};

/// Sandbox configuration passed to `materializeBodyEmbedBytes` and `materializeModuleEmbedBytes`.
pub const EmbedMaterializeOptions = struct {
    /// Optional workspace root directory path for disk-backed `@embed_bytes`.
    workspace_root: ?[]const u8 = null,
    /// Optional Zig `Io` handle for disk-backed `@embed_bytes` inside `workspace_root`.
    io: ?std.Io = null,
    /// Optional in-memory VFS file map (`relative_path -> bytes`) checked before `workspace_root`.
    virtual_files: ?*const std.StringHashMapUnmanaged([]const u8) = null,
    /// Optional `CompilerDb` to record incremental file-read dependencies.
    compiler_db: ?*query_db.CompilerDb = null,
    /// Maximum single `@embed_bytes` file size (`64 MiB` default per `DR-20` `D-03`).
    max_blob_bytes: u64 = MAX_EMBED_BLOB_BYTES,
    /// Optional `SymbolTable` mapping lexical `origin_file_id -> PackageId`.
    sym_table: ?*const SymbolTable = null,
    /// Optional per-`PackageId` `@embed_bytes` sandbox jail policy table (`DR-17` §5).
    package_jails: ?*const std.AutoHashMapUnmanaged(PackageId, EmbedPackageJail) = null,
    /// Optional `VfsSourceMap` resolving `.cxtree_only` assets without touching host disk.
    vfs_source_map: ?*const vfs_sourcemap.VfsSourceMap = null,
};

// -------------------- Canonical `MirBody` ---------------------

/// CFG window `[start_block .. end_block]` where an `inout` `subscript` vacates `self` (`DR-20` `Fix-06B`).
pub const VacatedProjectionWindow = struct {
    /// Basic block where the `inout` `subscript` projection opened.
    start_block: MirBlockId,
    /// Basic block where the `subscript` writeback epilogue closed.
    end_block: MirBlockId,
    /// Ghost access token bounding the projection scope (`.none` if closed inline without Ghost token).
    access_token: MirValueId,
    /// Yielded caller-side `PlaceId`.
    yielded_place: PlaceId,
    /// Concrete `TypeId` of the yielded projection.
    yielded_ty: TypeId,
    /// Originating `subscript` call-site `TokenIndex` for diagnostics.
    site_token: TokenIndex,
};

/// Recorded 3-phase parallel assignment target group `(lhs_0, lhs_1, …) = rhs` (`SE-15`).
pub const ParallelAssignGroup = struct {
    /// Basic block where Phase-3 commit stores occur (`Pentagon` range lookup anchor).
    block_id: MirBlockId,
    /// Start index in `MirBody.parallel_assign_places`.
    places_start: u32,
    /// Number of parallel LHS target `PlaceId`s in this group (`>= 2`).
    places_len: u32,
    /// Originating assignment statement `TokenIndex` for `E0305` diagnostics.
    origin_token: TokenIndex,
};

/// Self-contained Block-Argument SSA representation of a single lowered function or constant body.
pub const MirBody = struct {
    /// Backing allocator owning all arenas and arrays in `self`.
    allocator: std.mem.Allocator,
    /// Owning `DefId` (`DefId.NONE` for synthetic closures, constants, and `impl`/`@derive` methods).
    def_id: DefId = .NONE,
    /// Resolved `SymbolIndex` in `SymbolTable` (`SymbolIndex.none` for closures/specialized clones).
    symbol_index: SymbolIndex = .none,
    /// Owning `FileId`.
    file_id: FileId = .none,
    /// Interned function/item identifier.
    name: SymbolId = .empty,
    /// Return `TypeId` (stored in `locals[0]`).
    ret_ty: TypeId = .unit_ty,
    /// Number of formal function parameters (`locals[1 .. 1 + param_count]`).
    param_count: u32 = 0,
    /// Target pointer width/alignment configuration.
    target_layout: TargetLayout = TargetLayout.NATIVE_64,

    /// Explicit ghost lifecycle flags (`DR-02` Deliverable 3):
    /// `true` while `ghost_access_*` / `ghost_storage_*` instructions are present in `insts`.
    has_ghost_instructions: bool = true,
    /// `true` after Phase 6 SAST strips all ghost instructions (`V4` post-strip mode).
    is_ghost_stripped: bool = false,
    /// `true` when annotated `@noalloc` / `contextless` (`V6` verification).
    is_contextless: bool = false,
    /// `true` when lowered from an `async fn`, `async |…|`, `async { … }`, `async test`, or `task_group` nursery.
    is_async: bool = false,
    /// `true` if `MAX_MIR_INSTRUCTIONS`, `MAX_MIR_BLOCKS`, or projection caps overflowed (`E0508`).
    has_overflowed_limits: bool = false,
    /// `true` once Phase 6 `ElaborateDrops` has materialized destructors on this body.
    is_sast_elaborated: bool = false,
    /// `true` when lowered solely to verify default parameter/field expressions during Phase 6 `mir_sast`.
    is_sast_default_probe: bool = false,
    /// `true` when lowered from a standalone `subscript` arm solely for Phase 6 `mir_sast` verification.
    is_sast_subscript_probe: bool = false,
    /// Owning `DefId` attributed for SAST summary roll-up on synthetic `is_sast_*_probe` bodies.
    sast_owner_def_id: DefId = .NONE,
    /// Owning `SymbolIndex` attributed for SAST summary roll-up on synthetic `is_sast_*_probe` bodies.
    sast_owner_symbol: SymbolIndex = .none,

    /// Local slot declarations (`_0` is always the return slot).
    locals: std.ArrayListUnmanaged(LocalDecl) = .empty,
    /// Parallel lexical block nesting depths per local (`0` for `_0`/params, `>= 1` for body scopes).
    local_scope_depths: std.ArrayListUnmanaged(u16) = .empty,
    /// Interned/appended `MirPlace` table (`PlaceId(0)` is unprojected `_0`).
    places: std.ArrayListUnmanaged(MirPlace) = .empty,
    /// Flat projection element pool sliced by `MirPlace.[proj_start .. proj_start + proj_len]`.
    projections: std.ArrayListUnmanaged(MirProjection) = .empty,

    /// SoA instruction arena (`MirValueId` indexes `0 .. insts.len - 1`).
    insts: std.MultiArrayList(MirInst) = .empty,
    /// Parallel origin token table (`origin_tokens.items.len == insts.len`).
    origin_tokens: std.ArrayListUnmanaged(TokenIndex) = .empty,

    /// Contiguous basic-block table (`MirBlockId(0)` is always the entry block `^bb0`).
    blocks: std.ArrayListUnmanaged(MirBasicBlock) = .empty,
    /// Packed `MirValueId`s of `MirOp.block_param` instructions per block.
    block_params: std.ArrayListUnmanaged(MirValueId) = .empty,
    /// Packed `MirValueId`s of body instructions executed sequentially in each block.
    block_insts: std.ArrayListUnmanaged(MirValueId) = .empty,
    /// First-class outgoing CFG edges (`EdgeId` indexes `0 .. extra_edges.items.len - 1`).
    extra_edges: std.ArrayListUnmanaged(MirOutgoingEdge) = .empty,
    /// Packed incoming `EdgeId` lists per block (`blocks[bb].pred_start .. + pred_len`).
    pred_edges: std.ArrayListUnmanaged(EdgeId) = .empty,

    /// Shared 32-bit operand/argument pool (edge arguments, aggregate elements, call arguments).
    extra_args: std.ArrayListUnmanaged(u32) = .empty,
    /// Case scalar values (`i128`) referenced by `MirOutgoingEdge.case_tag_idx` on `switch_int`.
    switch_values: std.ArrayListUnmanaged(i128) = .empty,
    /// Call-site descriptors referenced by `MirTerminator.cond_or_val` on `.call`.
    calls: std.ArrayListUnmanaged(MirCallSite) = .empty,
    /// Per-call-argument `ParamMode` array sliced by `MirCallSite.modes_start`.
    call_arg_modes: std.ArrayListUnmanaged(ParamMode) = .empty,
    /// Constant pool referenced by `MirOp.const_scalar`.
    consts: std.ArrayListUnmanaged(MirConst) = .empty,
    /// Recorded `inout` `subscript` vacated-`self` windows inspected by `mir_sast` (`DR-20` `Fix-06B`).
    vacated_windows: std.ArrayListUnmanaged(VacatedProjectionWindow) = .empty,
    /// Sparse `@must_vectorize` / `@vectorize_width(N)` loop contracts (`@sizeOf(MirBasicBlock) == 32`).
    loop_contracts: std.ArrayListUnmanaged(MirLoopContractEntry) = .empty,
    /// Parallel-assignment target groups inspected by `mir_sast` Pass 2 for pairwise LHS overlap (`SE-15`).
    parallel_assign_groups: std.ArrayListUnmanaged(ParallelAssignGroup) = .empty,
    /// Flat `PlaceId` slice referenced by `ParallelAssignGroup.[places_start .. + places_len]` (`SE-15`).
    parallel_assign_places: std.ArrayListUnmanaged(PlaceId) = .empty,

    /// Initializes an empty `MirBody` with pre-strip ghost tracking active.
    pub fn init(allocator: std.mem.Allocator, file_id: FileId, def_id: DefId) MirBody {
        return .{
            .allocator = allocator,
            .file_id = file_id,
            .def_id = def_id,
            .has_ghost_instructions = true,
            .is_ghost_stripped = false,
        };
    }

    /// Releases all memory owned by `self`.
    pub fn deinit(self: *MirBody) void {
        self.locals.deinit(self.allocator);
        self.local_scope_depths.deinit(self.allocator);
        self.places.deinit(self.allocator);
        self.projections.deinit(self.allocator);
        self.insts.deinit(self.allocator);
        self.origin_tokens.deinit(self.allocator);
        self.blocks.deinit(self.allocator);
        self.block_params.deinit(self.allocator);
        self.block_insts.deinit(self.allocator);
        self.extra_edges.deinit(self.allocator);
        self.pred_edges.deinit(self.allocator);
        self.extra_args.deinit(self.allocator);
        self.switch_values.deinit(self.allocator);
        self.calls.deinit(self.allocator);
        self.call_arg_modes.deinit(self.allocator);
        self.consts.deinit(self.allocator);
        self.vacated_windows.deinit(self.allocator);
        self.loop_contracts.deinit(self.allocator);
        self.parallel_assign_groups.deinit(self.allocator);
        self.parallel_assign_places.deinit(self.allocator);
        self.* = undefined;
    }

    /// Deep-clones `self` into an independent `MirBody` owned by `allocator`.
    pub fn clone(self: *const MirBody, allocator: std.mem.Allocator) !MirBody {
        var copy = MirBody{
            .allocator = allocator,
            .def_id = self.def_id,
            .symbol_index = self.symbol_index,
            .file_id = self.file_id,
            .name = self.name,
            .ret_ty = self.ret_ty,
            .param_count = self.param_count,
            .target_layout = self.target_layout,
            .has_ghost_instructions = self.has_ghost_instructions,
            .is_ghost_stripped = self.is_ghost_stripped,
            .is_contextless = self.is_contextless,
            .is_async = self.is_async,
            .has_overflowed_limits = self.has_overflowed_limits,
            .is_sast_elaborated = self.is_sast_elaborated,
        };
        errdefer copy.deinit();

        try copy.locals.appendSlice(allocator, self.locals.items);
        try copy.local_scope_depths.appendSlice(allocator, self.local_scope_depths.items);
        try copy.places.appendSlice(allocator, self.places.items);
        try copy.projections.appendSlice(allocator, self.projections.items);
        try copy.insts.ensureTotalCapacity(allocator, self.insts.len);
        for (0..self.insts.len) |i| {
            copy.insts.appendAssumeCapacity(self.insts.get(i));
        }
        try copy.origin_tokens.appendSlice(allocator, self.origin_tokens.items);
        try copy.blocks.appendSlice(allocator, self.blocks.items);
        try copy.block_params.appendSlice(allocator, self.block_params.items);
        try copy.block_insts.appendSlice(allocator, self.block_insts.items);
        try copy.extra_edges.appendSlice(allocator, self.extra_edges.items);
        try copy.pred_edges.appendSlice(allocator, self.pred_edges.items);
        try copy.extra_args.appendSlice(allocator, self.extra_args.items);
        try copy.switch_values.appendSlice(allocator, self.switch_values.items);
        try copy.calls.appendSlice(allocator, self.calls.items);
        try copy.call_arg_modes.appendSlice(allocator, self.call_arg_modes.items);
        try copy.consts.appendSlice(allocator, self.consts.items);
        try copy.vacated_windows.appendSlice(allocator, self.vacated_windows.items);
        try copy.loop_contracts.appendSlice(allocator, self.loop_contracts.items);
        try copy.parallel_assign_groups.appendSlice(allocator, self.parallel_assign_groups.items);
        try copy.parallel_assign_places.appendSlice(allocator, self.parallel_assign_places.items);
        return copy;
    }

    /// Reads a single `MirInst` by `val_id` in $O(1)$ time.
    pub inline fn getInst(self: *const MirBody, val_id: MirValueId) MirInst {
        return self.insts.get(val_id.asInt());
    }

    /// Returns the projection slice belonging to `place_id`.
    pub inline fn getPlaceProjections(self: *const MirBody, place_id: PlaceId) []const MirProjection {
        const place = self.places.items[place_id.asInt()];
        const start: usize = place.proj_start;
        return self.projections.items[start .. start + place.proj_len];
    }

    /// Returns the formal `MirValueId` block parameters of `block_id`.
    pub inline fn getBlockParams(self: *const MirBody, block_id: MirBlockId) []const MirValueId {
        const bb = self.blocks.items[block_id.asInt()];
        return self.block_params.items[bb.param_start .. bb.param_start + bb.paramLen()];
    }

    /// Returns the sequential `MirValueId` instructions of `block_id`.
    pub inline fn getBlockInsts(self: *const MirBody, block_id: MirBlockId) []const MirValueId {
        const bb = self.blocks.items[block_id.asInt()];
        return self.block_insts.items[bb.inst_start .. bb.inst_start + bb.inst_len];
    }

    /// Returns the incoming `EdgeId` slice of `block_id`.
    pub inline fn getPredEdges(self: *const MirBody, block_id: MirBlockId) []const EdgeId {
        const bb = self.blocks.items[block_id.asInt()];
        return self.pred_edges.items[bb.pred_start .. bb.pred_start + bb.pred_len];
    }

    /// Returns the outgoing `MirOutgoingEdge` slice of `block_id`.
    pub inline fn getOutgoingEdges(self: *const MirBody, block_id: MirBlockId) []const MirOutgoingEdge {
        const term = self.blocks.items[block_id.asInt()].terminator;
        return self.extra_edges.items[term.edge_start .. term.edge_start + term.edge_len];
    }

    /// Appends a `MirInst` with `origin_token` and returns its `MirValueId`.
    pub fn appendInst(self: *MirBody, inst: MirInst, origin_token: TokenIndex) !MirValueId {
        const next_idx: u32 = @intCast(self.insts.len);
        try self.insts.append(self.allocator, inst);
        try self.origin_tokens.append(self.allocator, origin_token);
        return MirValueId.fromInt(next_idx);
    }

    /// Appends a `MirConst` into `self.consts` and returns its `u32` pool index.
    pub fn appendConst(self: *MirBody, const_val: MirConst) !u32 {
        const idx: u32 = @intCast(self.consts.items.len);
        try self.consts.append(self.allocator, const_val);
        return idx;
    }

    /// Visits every mutable SSA `MirValueId` use across all instructions, terminators, outgoing
    /// edge arguments, call sites, AND dynamic `MirProjection.index` operands.
    ///
    /// Used by `MirSsaBuilder.finish()` and Wave 2C optimization passes (`R1` SCCP / `R3` GVN)
    /// so trivial block-parameter / copy rewrites never leave stale `MirValueId`s in projections!
    pub fn forEachInstAndProjValueMut(
        self: *MirBody,
        ctx: anytype,
        comptime rewriteFn: fn (@TypeOf(ctx), *u32) void,
    ) void {
        const ops = self.insts.items(.op);
        const aux_slice = self.insts.items(.aux_u16);
        const operands_slice = self.insts.items(.operands);

        // [1] Rewrite instruction SSA value operands:
        for (ops, aux_slice, operands_slice) |op, aux, *opnd| {
            switch (op) {
                .block_param,
                .ghost_access_let,
                .ghost_access_inout,
                .ghost_access_set,
                .ghost_storage_init,
                .ghost_storage_move,
                .ghost_storage_deinit,
                .const_scalar,
                .fn_addr,
                .place_load,
                .place_discriminant,
                .place_set_discrim,
                .place_addr,
                .soa_column_slice,
                => {},
                .ghost_access_end,
                .copy_val,
                .unary_op,
                .aggregate_extract,
                .bitfield_extract,
                => {
                    if (opnd.lhs != NONE_U32) rewriteFn(ctx, &opnd.lhs);
                },
                .bin_op => {
                    if (opnd.lhs != NONE_U32) rewriteFn(ctx, &opnd.lhs);
                    if (opnd.rhs != NONE_U32) rewriteFn(ctx, &opnd.rhs);
                },
                .place_store => {
                    if (opnd.rhs != NONE_U32) rewriteFn(ctx, &opnd.rhs);
                },
                .aggregate_insert => {
                    if (opnd.lhs != NONE_U32) rewriteFn(ctx, &opnd.lhs);
                    if (opnd.rhs + 2 <= self.extra_args.items.len) {
                        rewriteFn(ctx, &self.extra_args.items[opnd.rhs + 1]);
                    }
                },
                .bitfield_insert => {
                    if (opnd.lhs + 2 <= self.extra_args.items.len) {
                        rewriteFn(ctx, &self.extra_args.items[opnd.lhs]);
                        rewriteFn(ctx, &self.extra_args.items[opnd.lhs + 1]);
                    }
                },
                .aggregate_make => {
                    const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(aux))));
                    switch (agg_kind) {
                        .array_repeat => {
                            if (opnd.lhs != NONE_U32) rewriteFn(ctx, &opnd.lhs);
                        },
                        .tagged_variant => {
                            const elem_len = opnd.rhs & 0xFFFF;
                            for (self.extra_args.items[opnd.lhs .. opnd.lhs + elem_len]) |*slot| {
                                if (slot.* != NONE_U32) rewriteFn(ctx, slot);
                            }
                        },
                        .closure_make => {
                            if (opnd.rhs < self.extra_args.items.len) {
                                const cap_len = self.extra_args.items[opnd.rhs];
                                const cap_start = opnd.rhs + 1;
                                for (self.extra_args.items[cap_start .. cap_start + cap_len]) |*slot| {
                                    if (slot.* != NONE_U32) rewriteFn(ctx, slot);
                                }
                            }
                        },
                        .tuple_agg, .struct_agg, .array_elems, .str_concat, .fmt_args_make => {
                            for (self.extra_args.items[opnd.lhs .. opnd.lhs + opnd.rhs]) |*slot| {
                                if (slot.* != NONE_U32) rewriteFn(ctx, slot);
                            }
                        },
                    }
                },
                .intrinsic_op => {
                    const ikind: MirIntrinsicKind = @fromBackingInt(aux);
                    if (ikind.hasPlaceInLhs()) {
                        if (ikind.hasSsaFlagInRhs() and opnd.rhs != NONE_U32) {
                            rewriteFn(ctx, &opnd.rhs);
                        }
                    } else if (ikind.hasExtraArgs() and opnd.rhs > 0) {
                        for (self.extra_args.items[opnd.lhs .. opnd.lhs + opnd.rhs]) |*slot| {
                            if (slot.* != NONE_U32) rewriteFn(ctx, slot);
                        }
                    }
                },
            }
        }

        // [2] Rewrite dynamic `ProjKind.index` operands in `self.projections`:
        for (self.projections.items) |*proj| {
            if (proj.kind == .index and proj.payload != NONE_U32) {
                rewriteFn(ctx, &proj.payload);
            }
        }

        // [3] Rewrite terminator condition/return values and outgoing edge argument slices:
        for (self.blocks.items) |*bb| {
            switch (bb.terminator.kind) {
                .ret, .cond_br, .switch_int, .coro_suspend => {
                    if (bb.terminator.cond_or_val != NONE_U32) {
                        rewriteFn(ctx, &bb.terminator.cond_or_val);
                    }
                },
                else => {},
            }
        }
        for (self.extra_edges.items) |edge| {
            for (self.extra_args.items[edge.args_start .. edge.args_start + edge.args_len]) |*arg_slot| {
                if (arg_slot.* != NONE_U32) rewriteFn(ctx, arg_slot);
            }
        }

        // [4] Rewrite `MirCallSite` callee, value arguments (`let`/`sink`), and call-scoped Ghost tokens:
        for (self.calls.items) |*call_site| {
            if (!call_site.callee_val.isNone()) {
                var raw_callee = call_site.callee_val.asInt();
                rewriteFn(ctx, &raw_callee);
                call_site.callee_val = MirValueId.fromInt(raw_callee);
            }
            for (0..call_site.args_len) |arg_i| {
                const mode = self.call_arg_modes.items[call_site.modes_start + arg_i];
                if (mode == .let_mode or mode == .sink_mode) {
                    const slot = &self.extra_args.items[call_site.args_start + arg_i];
                    if (slot.* != NONE_U32) rewriteFn(ctx, slot);
                }
            }
            for (0..call_site.call_borrows_len) |bor_i| {
                const tok_slot = &self.extra_args.items[call_site.call_borrows_start + bor_i];
                if (tok_slot.* != NONE_U32) rewriteFn(ctx, tok_slot);
            }
        }
        for (self.vacated_windows.items) |*win| {
            if (!win.access_token.isNone()) {
                var raw_tok = win.access_token.asInt();
                rewriteFn(ctx, &raw_tok);
                win.access_token = MirValueId.fromInt(raw_tok);
            }
        }
    }
};

/// Active subscript body frame on `MirLowerer.subscript_splice_stack` preventing recursive inline expansion.
const SubscriptSpliceFrame = struct {
    /// Owning `HirStore` of the active `subscript` body (`null` when slot is unused).
    store: ?*const HirStore = null,
    /// Index into `store.functions.items` for the active `subscript` definition.
    fn_meta_idx: usize = 0,
};

// --------------------------------------- CONSTS ----------------------------------------

/// 32-bit `none` sentinel matching `MirValueId.none` / `MirBlockId.none`.
pub const NONE_U32: u32 = std.math.maxInt(u32);
/// Hard resource cap on `MirInst` count per `MirBody` (`4,194,304`, `E0508`).
pub const MAX_MIR_INSTRUCTIONS: u32 = 4_194_304;
/// Hard resource cap on `MirBasicBlock` count per `MirBody` (`262,144`, `E0508`).
pub const MAX_MIR_BLOCKS: u32 = 262_144;
/// Hard resource cap on `MirBody.projections.items.len` (`2^24 - 1 = 16,777,215`, `E0508`).
pub const MAX_MIR_PROJECTIONS: u32 = (1 << 24) - 1;
/// Hard resource cap on projection chain depth per `MirPlace` (`255`, `E0508`).
pub const MAX_PLACE_PROJ_DEPTH: u32 = 255;
/// Hard resource cap on predecessors per `MirBasicBlock` (`65,534`, `E0508`).
pub const MAX_BLOCK_PREDS: u32 = 65_534;
/// Hard resource cap on formal block parameters per `MirBasicBlock` (`16,383`, `E0508`).
pub const MAX_BLOCK_PARAMS: u32 = 16_383;
/// Hard resource cap on Maranget decision-tree specialization nodes per `match` (`16,384`, `E0508`).
pub const MAX_DECISION_NODES: u32 = 16_384;
/// Bitflag in `MirTerminator.aux_u8` (`kind == .trap`) forcing immediate `abort` inside a vacated projection window.
pub const TRAP_ABORT_ON_PANIC_FLAG: u8 = 0x80;

/// Bitmask extracting `param_len: u14` from `MirBasicBlock.meta_bits`.
const BLOCK_PARAM_LEN_MASK: u16 = 0x3FFF;
/// Bitflag marking `is_sealed` (`bit 14`) in `MirBasicBlock.meta_bits`.
const BLOCK_SEALED_BIT: u16 = 1 << 14;
/// Bitflag marking `is_cleanup_pad` (`bit 15`) in `MirBasicBlock.meta_bits`.
const BLOCK_CLEANUP_PAD_BIT: u16 = 1 << 15;

/// Default maximum `@embed_bytes` file size (`64 MiB`, `DR-20` `D-03`).
pub const MAX_EMBED_BLOB_BYTES: u64 = 64 * 1024 * 1024;
/// Canonical alias for `MAX_EMBED_BLOB_BYTES` (`DR-17` §5).
pub const MAX_EMBED_BYTES: u64 = MAX_EMBED_BLOB_BYTES;

comptime {
    // Enforce exact Phase 5 & Phase 7 MIR cache-density byte-size invariants:
    std.debug.assert(@sizeOf(LocalFlags) == 1);
    std.debug.assert(@sizeOf(LocalDecl) == 16);
    std.debug.assert(@sizeOf(MirPlace) == 8);
    std.debug.assert(@sizeOf(MirProjection) == 8);
    std.debug.assert(@sizeOf(InstFlags) == 1);
    std.debug.assert(
        @sizeOf(MirOp) + @sizeOf(InstFlags) + @sizeOf(u16) +
            @sizeOf(TypeId) + @sizeOf(MirInst.Operands) == 16,
    );
    std.debug.assert(@sizeOf(MirTerminator) == 12);
    std.debug.assert(@sizeOf(MirBasicBlock) == 32);
    std.debug.assert(@sizeOf(MirOutgoingEdge) == 16);
    std.debug.assert(@sizeOf(LoopContractMask) == 1);
    std.debug.assert(@sizeOf(LoopContractMeta) == 8);
    std.debug.assert(@sizeOf(MirLoopContractEntry) == 16);
    std.debug.assert(@sizeOf(RawBlobConst) == 16);
}

// -------------------------------------- INTERNALS --------------------------------------

// -------- Braun et al. Block-Argument `MirSsaBuilder` ---------

/// Unsealed block-parameter placeholder awaiting `sealBlock` (`DR-13` §3.4).
const IncompletePhi = struct {
    /// Promoted local variable index (`0 .. var_types.len - 1`).
    var_id: u32,
    /// Placeholder `MirOp.block_param` `MirValueId` created in the unsealed block.
    param_val: MirValueId,
};

/// Per-block mutable construction state inside `MirSsaBuilder`.
const SsaBlockScratch = struct {
    /// Formal `MirOp.block_param` `MirValueId`s attached to this block.
    params: std.ArrayListUnmanaged(MirValueId) = .empty,
    /// Sequential body instruction `MirValueId`s in this block.
    insts: std.ArrayListUnmanaged(MirValueId) = .empty,
    /// Incoming `EdgeId`s targeting this block.
    preds: std.ArrayListUnmanaged(EdgeId) = .empty,
    /// Deferred phi operands to wire once `sealBlock` is invoked.
    incomplete_phis: std.ArrayListUnmanaged(IncompletePhi) = .empty,
    /// `true` once all CFG predecessors of this block have been registered.
    is_sealed: bool = false,
    /// `true` if this block is a shared cold `errdefer`/`defer` cleanup pad.
    is_cleanup_pad: bool = false,
    /// `true` if `params[0]` is a `call` continuation `%ret_val` (`normal_edge.args_len == 0`).
    has_call_ret_param: bool = false,
    /// `true` once `setTerminator` has finalized this block's outgoing control flow.
    has_terminator: bool = false,
};

/// Single-pass forward Block-Argument SSA builder (Braun et al., CC 2013, `DR-13` §3.4).
///
/// Supports both fresh `HIR -> MIR` lowering (`init`) and in-place SSA variable promotion over an
/// existing `MirBody` (`initFromExistingBody` for Wave 2C's `R2` SROA pass).
pub const MirSsaBuilder = struct {
    /// Backing scratch allocator.
    allocator: std.mem.Allocator,
    /// Target `MirBody` receiving instructions, blocks, edges, and constants.
    body: *MirBody,
    /// Concrete `TypeId` of each SSA-promotable variable (`var_id` indexes this slice).
    var_types: []const TypeId,
    /// Optional diagnostic sink for resource-limit (`E0508`) reporting.
    diagnostic_sink: ?*DiagnosticSink = null,

    /// Per-block mutable lists (`blocks_scratch.items.len == body.blocks.items.len`).
    blocks_scratch: std.ArrayListUnmanaged(SsaBlockScratch) = .empty,
    /// Per-edge outgoing block-argument `MirValueId` lists (`edge_args_scratch.items.len == body.extra_edges.items.len`).
    edge_args_scratch: std.ArrayListUnmanaged(std.ArrayListUnmanaged(MirValueId)) = .empty,

    /// Map `(var_id << 32 | block_id) -> MirValueId` tracking latest local definitions.
    current_def: std.AutoHashMapUnmanaged(u64, MirValueId) = .empty,
    /// Map `eliminated_param_val_id -> replacement_val_id` for trivial phi cascading.
    trivial_replacements: std.AutoHashMapUnmanaged(u32, MirValueId) = .empty,
    /// Set of explicit non-phi block parameters (`%ret_val`, `%err_payload`, pre-seeded params)
    /// that must never be eliminated as trivial Braun phis.
    pinned_params: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Reverse use list `operand_param_val_id -> [dependent_phi_param_val_ids…]` for cascading removal.
    param_users: std.AutoHashMapUnmanaged(u32, std.ArrayListUnmanaged(MirValueId)) = .empty,
    /// Owning `MirBlockId` of every Braun-synthesized phi `MirValueId`.
    phi_owner_block: std.AutoHashMapUnmanaged(u32, MirBlockId) = .empty,

    /// Initializes a fresh `MirSsaBuilder` over an empty `MirBody`.
    pub fn init(
        allocator: std.mem.Allocator,
        body: *MirBody,
        var_types: []const TypeId,
        diagnostic_sink: ?*DiagnosticSink,
    ) MirSsaBuilder {
        return .{
            .allocator = allocator,
            .body = body,
            .var_types = var_types,
            .diagnostic_sink = diagnostic_sink,
        };
    }

    /// Initializes a `MirSsaBuilder` pre-seeded with `body`'s existing blocks, block parameters,
    /// instructions, predecessor edges, and per-edge block arguments (`R2` SROA).
    pub fn initFromExistingBody(
        allocator: std.mem.Allocator,
        body: *MirBody,
        var_types: []const TypeId,
        diagnostic_sink: ?*DiagnosticSink,
    ) !MirSsaBuilder {
        var builder = MirSsaBuilder.init(allocator, body, var_types, diagnostic_sink);
        errdefer builder.deinit();

        // [1] Detect which blocks are `call` `normal_bb`s or `coro_suspend` `resume_bb`s (`has_call_ret_param`):
        var call_cont_blocks: std.AutoHashMapUnmanaged(u32, void) = .empty;
        defer call_cont_blocks.deinit(allocator);
        for (body.blocks.items) |bb| {
            if ((bb.terminator.kind == .call or bb.terminator.kind == .coro_suspend) and
                bb.terminator.edge_len >= 1)
            {
                const normal_edge = body.extra_edges.items[bb.terminator.edge_start];
                try call_cont_blocks.put(allocator, normal_edge.target_bb.asInt(), {});
            }
        }

        // [2] Pre-seed per-block params, instructions, and predecessor `EdgeId`s:
        try builder.blocks_scratch.ensureTotalCapacity(allocator, body.blocks.items.len);
        for (body.blocks.items, 0..) |bb, bb_idx| {
            const bb_id = MirBlockId.fromInt(@intCast(bb_idx));
            var scratch = SsaBlockScratch{
                .is_sealed = bb.isSealed(),
                .is_cleanup_pad = bb.isCleanupPad(),
                .has_call_ret_param = call_cont_blocks.contains(@intCast(bb_idx)),
                .has_terminator = true,
            };
            errdefer {
                scratch.params.deinit(allocator);
                scratch.insts.deinit(allocator);
                scratch.preds.deinit(allocator);
                scratch.incomplete_phis.deinit(allocator);
            }
            const existing_params = body.getBlockParams(bb_id);
            try scratch.params.appendSlice(allocator, existing_params);
            for (existing_params) |pinned_id| {
                try builder.pinned_params.put(allocator, pinned_id.asInt(), {});
            }
            try scratch.insts.appendSlice(allocator, body.getBlockInsts(bb_id));
            try scratch.preds.appendSlice(allocator, body.getPredEdges(bb_id));
            builder.blocks_scratch.appendAssumeCapacity(scratch);
        }

        // [3] Pre-seed per-edge outgoing argument lists:
        try builder.edge_args_scratch.ensureTotalCapacity(allocator, body.extra_edges.items.len);
        for (body.extra_edges.items) |edge| {
            var arg_list: std.ArrayListUnmanaged(MirValueId) = .empty;
            errdefer arg_list.deinit(allocator);
            try arg_list.ensureTotalCapacity(allocator, edge.args_len);
            for (body.extra_args.items[edge.args_start .. edge.args_start + edge.args_len]) |raw_val| {
                arg_list.appendAssumeCapacity(MirValueId.fromInt(raw_val));
            }
            builder.edge_args_scratch.appendAssumeCapacity(arg_list);
        }

        return builder;
    }

    /// Releases all temporary SSA construction tables owned by `self`.
    pub fn deinit(self: *MirSsaBuilder) void {
        for (self.blocks_scratch.items) |*blk| {
            blk.params.deinit(self.allocator);
            blk.insts.deinit(self.allocator);
            blk.preds.deinit(self.allocator);
            blk.incomplete_phis.deinit(self.allocator);
        }
        self.blocks_scratch.deinit(self.allocator);

        for (self.edge_args_scratch.items) |*arg_list| {
            arg_list.deinit(self.allocator);
        }
        self.edge_args_scratch.deinit(self.allocator);

        self.current_def.deinit(self.allocator);
        self.trivial_replacements.deinit(self.allocator);
        self.pinned_params.deinit(self.allocator);

        var user_iter = self.param_users.valueIterator();
        while (user_iter.next()) |list_ptr| {
            list_ptr.deinit(self.allocator);
        }
        self.param_users.deinit(self.allocator);
        self.phi_owner_block.deinit(self.allocator);
        self.* = undefined;
    }

    /// Allocates a new basic block in `self.body` (enforcing `MAX_MIR_BLOCKS` -> `E0508`).
    pub fn createBlock(self: *MirSsaBuilder, is_sealed: bool, is_cleanup_pad: bool) !MirBlockId {
        if (self.body.blocks.items.len >= MAX_MIR_BLOCKS) {
            try self.reportResourceOverflow("MIR basic block count exceeded `MAX_MIR_BLOCKS` (262,144)");
            return MirBlockId.fromInt(@intCast(self.body.blocks.items.len - 1));
        }
        const raw_idx: u32 = @intCast(self.body.blocks.items.len);
        var bb = MirBasicBlock{};
        bb.setSealed(is_sealed);
        bb.setCleanupPad(is_cleanup_pad);
        try self.body.blocks.append(self.body.allocator, bb);
        try self.blocks_scratch.append(self.allocator, .{
            .is_sealed = is_sealed,
            .is_cleanup_pad = is_cleanup_pad,
        });
        return MirBlockId.fromInt(raw_idx);
    }

    /// Appends an explicit pinned `MirOp.block_param` (e.g., `%ret_val` on `normal_bb` or `%err` on a cleanup pad).
    pub fn addExplicitBlockParam(
        self: *MirSsaBuilder,
        block_id: MirBlockId,
        param_ty: TypeId,
        origin_token: TokenIndex,
        is_call_ret_param: bool,
    ) !MirValueId {
        var blk = &self.blocks_scratch.items[block_id.asInt()];
        if (blk.params.items.len >= MAX_BLOCK_PARAMS) {
            try self.reportResourceOverflow("MIR block parameter count exceeded `MAX_BLOCK_PARAMS` (16,383)");
        }
        const ordinal: u32 = @intCast(blk.params.items.len);
        const param_val = try self.allocRawInst(.{
            .op = .block_param,
            .flags = .{ .is_synthetic = true },
            .type_id = param_ty,
            .operands = .{ .lhs = block_id.asInt(), .rhs = ordinal },
        }, origin_token);
        try blk.params.append(self.allocator, param_val);
        if (is_call_ret_param and ordinal == 0) {
            blk.has_call_ret_param = true;
        }
        try self.pinned_params.put(self.allocator, param_val.asInt(), {});
        return param_val;
    }

    /// Appends an instruction into `block_id` and returns its `MirValueId` (`E0508` if `>= MAX_MIR_INSTRUCTIONS`).
    pub fn emitInst(
        self: *MirSsaBuilder,
        block_id: MirBlockId,
        inst: MirInst,
        origin_token: TokenIndex,
    ) !MirValueId {
        const val_id = try self.allocRawInst(inst, origin_token);
        try self.blocks_scratch.items[block_id.asInt()].insts.append(self.allocator, val_id);
        return val_id;
    }

    /// Allocates a `MirInst` in `self.body.insts` without attaching it to a block's body list.
    fn allocRawInst(self: *MirSsaBuilder, inst: MirInst, origin_token: TokenIndex) !MirValueId {
        if (self.body.insts.len >= MAX_MIR_INSTRUCTIONS) {
            try self.reportResourceOverflow("MIR instruction count exceeded `MAX_MIR_INSTRUCTIONS` (4,194,304)");
            if (self.body.insts.len > 0) {
                return MirValueId.fromInt(@intCast(self.body.insts.len - 1));
            }
        }
        return self.body.appendInst(inst, origin_token);
    }

    /// Registers an outgoing CFG edge `src_bb -> target_bb` with optional explicit initial arguments.
    pub fn addOutgoingEdge(
        self: *MirSsaBuilder,
        src_bb: MirBlockId,
        target_bb: MirBlockId,
        explicit_args: []const MirValueId,
        case_tag_idx: u16,
    ) !EdgeId {
        var dst_scratch = &self.blocks_scratch.items[target_bb.asInt()];
        if (dst_scratch.preds.items.len >= MAX_BLOCK_PREDS) {
            try self.reportResourceOverflow("MIR block predecessor count exceeded `MAX_BLOCK_PREDS` (65,534)");
        }
        const raw_edge: u32 = @intCast(self.body.extra_edges.items.len);
        try self.body.extra_edges.append(self.body.allocator, .{
            .src_bb = src_bb,
            .target_bb = target_bb,
            .args_start = 0,
            .args_len = 0,
            .case_tag_idx = case_tag_idx,
        });
        var edge_args: std.ArrayListUnmanaged(MirValueId) = .empty;
        errdefer edge_args.deinit(self.allocator);
        if (explicit_args.len > 0) {
            try edge_args.appendSlice(self.allocator, explicit_args);
        }
        try self.edge_args_scratch.append(self.allocator, edge_args);

        const edge_id = EdgeId.fromInt(raw_edge);
        try dst_scratch.preds.append(self.allocator, edge_id);
        return edge_id;
    }

    /// Returns `true` if `block_id` already has a finalized control-flow terminator.
    pub inline fn isBlockTerminated(self: *const MirSsaBuilder, block_id: MirBlockId) bool {
        return self.blocks_scratch.items[block_id.asInt()].has_terminator;
    }

    /// Sets the `MirTerminator` of `block_id`.
    pub inline fn setTerminator(
        self: *MirSsaBuilder,
        block_id: MirBlockId,
        terminator: MirTerminator,
    ) void {
        self.body.blocks.items[block_id.asInt()].terminator = terminator;
        self.blocks_scratch.items[block_id.asInt()].has_terminator = true;
    }

    /// Updates `is_sealed` on `block_id` (used by `R2` SROA when unsealing/sealing existing blocks).
    pub fn setBlockSealed(self: *MirSsaBuilder, block_id: MirBlockId, is_sealed: bool) !void {
        if (is_sealed) {
            try self.sealBlock(block_id);
        } else {
            self.blocks_scratch.items[block_id.asInt()].is_sealed = false;
            self.body.blocks.items[block_id.asInt()].setSealed(false);
        }
    }

    /// Records `val_id` as the latest SSA definition of `var_id` in `block_id` (`Braun Algorithm 1`).
    pub fn writeVariable(
        self: *MirSsaBuilder,
        var_id: u32,
        block_id: MirBlockId,
        val_id: MirValueId,
    ) !void {
        const key = (@as(u64, var_id) << 32) | @as(u64, block_id.asInt());
        try self.current_def.put(self.allocator, key, self.resolveValue(val_id));
    }

    /// Reads the active SSA `MirValueId` of `var_id` in `block_id` (`Braun Algorithm 1`).
    pub fn readVariable(self: *MirSsaBuilder, var_id: u32, block_id: MirBlockId) anyerror!MirValueId {
        const key = (@as(u64, var_id) << 32) | @as(u64, block_id.asInt());
        if (self.current_def.get(key)) |found_val| {
            return self.resolveValue(found_val);
        }
        return self.readVariableRecursive(var_id, block_id);
    }

    /// Recursively queries predecessors of `block_id`, inserting `MirOp.block_param` phis on join points.
    fn readVariableRecursive(
        self: *MirSsaBuilder,
        var_id: u32,
        block_id: MirBlockId,
    ) anyerror!MirValueId {
        const var_ty = if (var_id < self.var_types.len) self.var_types[var_id] else TypeId.unit_ty;
        const blk_idx = block_id.asInt();

        var resolved_val: MirValueId = .none;
        if (!self.blocks_scratch.items[blk_idx].is_sealed) {
            // [1] Unsealed loop header: create placeholder `block_param` and defer wiring to `sealBlock`:
            const phi_val = try self.allocBraunPhiParam(block_id, var_ty);
            try self.blocks_scratch.items[blk_idx].incomplete_phis.append(self.allocator, .{
                .var_id = var_id,
                .param_val = phi_val,
            });
            resolved_val = phi_val;
        } else if (self.blocks_scratch.items[blk_idx].preds.items.len == 0) {
            // [2] Entry block or unreachable orphan block: synthesize typed zero/unit scalar fallback:
            resolved_val = try self.emitDefaultScalarInBlock(block_id, var_ty);
        } else if (self.blocks_scratch.items[blk_idx].preds.items.len == 1) {
            // [3] Single predecessor fast-path (preserves Call Continuation Split-Edge `param_len == 1`!):
            const pred_edge_id = self.blocks_scratch.items[blk_idx].preds.items[0];
            const pred_bb = self.body.extra_edges.items[pred_edge_id.asInt()].src_bb;
            resolved_val = try self.readVariable(var_id, pred_bb);
        } else {
            // [4] Multi-predecessor join: insert `block_param` first to break cyclic predecessor lookups:
            const phi_val = try self.allocBraunPhiParam(block_id, var_ty);
            try self.writeVariable(var_id, block_id, phi_val);
            resolved_val = try self.addBlockParamOperands(var_id, block_id, phi_val);
        }

        try self.writeVariable(var_id, block_id, resolved_val);
        return self.resolveValue(resolved_val);
    }

    /// Allocates a synthetic Braun `MirOp.block_param` on `block_id` and aligns existing incoming edges.
    fn allocBraunPhiParam(self: *MirSsaBuilder, block_id: MirBlockId, param_ty: TypeId) !MirValueId {
        var blk = &self.blocks_scratch.items[block_id.asInt()];
        if (blk.params.items.len >= MAX_BLOCK_PARAMS) {
            try self.reportResourceOverflow("MIR block parameter count exceeded `MAX_BLOCK_PARAMS` (16,383)");
        }
        const ordinal: u32 = @intCast(blk.params.items.len);
        const phi_val = try self.allocRawInst(.{
            .op = .block_param,
            .flags = .{ .is_synthetic = true },
            .type_id = param_ty,
            .operands = .{ .lhs = block_id.asInt(), .rhs = ordinal },
        }, .none);
        try blk.params.append(self.allocator, phi_val);
        try self.phi_owner_block.put(self.allocator, phi_val.asInt(), block_id);
        return phi_val;
    }

    /// Populates outgoing edge arguments for `param_val` across all incoming `EdgeId`s of `block_id`,
    /// then invokes `tryRemoveTrivialBlockParam` (`Braun Algorithm 2`).
    fn addBlockParamOperands(
        self: *MirSsaBuilder,
        var_id: u32,
        block_id: MirBlockId,
        param_val: MirValueId,
    ) anyerror!MirValueId {
        const blk_idx = block_id.asInt();
        const pred_count = self.blocks_scratch.items[blk_idx].preds.items.len;

        // Snapshot incoming `EdgeId`s on stack/heap in case recursive `readVariable` reallocates:
        const pred_snapshot = try self.allocator.alloc(EdgeId, pred_count);
        defer self.allocator.free(pred_snapshot);
        @memcpy(pred_snapshot, self.blocks_scratch.items[blk_idx].preds.items);

        // Compute the edge-argument slot index corresponding to `param_val`:
        const param_pos = self.findParamPosition(block_id, param_val) orelse return param_val;
        const call_offset: usize = @intFromBool(self.blocks_scratch.items[blk_idx].has_call_ret_param);
        const edge_slot_idx = param_pos - call_offset;

        for (pred_snapshot) |edge_id| {
            const src_bb = self.body.extra_edges.items[edge_id.asInt()].src_bb;
            const incoming_val = self.resolveValue(try self.readVariable(var_id, src_bb));
            var edge_args = &self.edge_args_scratch.items[edge_id.asInt()];
            while (edge_args.items.len <= edge_slot_idx) {
                try edge_args.append(self.allocator, .none);
            }
            edge_args.items[edge_slot_idx] = incoming_val;
            try self.recordParamUser(incoming_val, param_val);
        }

        return self.tryRemoveTrivialBlockParam(param_val);
    }

    /// Eliminates `param_val` if all non-self incoming edge operands resolve to a single `MirValueId`,
    /// cascading removal to any dependent Braun block parameters (`Braun Algorithm 3`).
    fn tryRemoveTrivialBlockParam(self: *MirSsaBuilder, param_val: MirValueId) anyerror!MirValueId {
        if (self.pinned_params.contains(param_val.asInt())) return param_val;
        if (self.trivial_replacements.get(param_val.asInt())) |already| {
            return self.resolveValue(already);
        }
        const block_id = self.phi_owner_block.get(param_val.asInt()) orelse return param_val;
        const blk_idx = block_id.asInt();
        if (!self.blocks_scratch.items[blk_idx].is_sealed) return param_val;

        const param_pos = self.findParamPosition(block_id, param_val) orelse return param_val;
        const call_offset: usize = @intFromBool(self.blocks_scratch.items[blk_idx].has_call_ret_param);
        if (param_pos < call_offset) return param_val;
        const edge_slot_idx = param_pos - call_offset;

        var same: MirValueId = .none;
        for (self.blocks_scratch.items[blk_idx].preds.items) |edge_id| {
            const edge_args = self.edge_args_scratch.items[edge_id.asInt()].items;
            if (edge_slot_idx >= edge_args.len or edge_args[edge_slot_idx].isNone()) {
                // Still awaiting operand population during nested `sealBlock` loop:
                return param_val;
            }
            const op_val = self.resolveValue(edge_args[edge_slot_idx]);
            if (op_val == param_val or op_val == same) continue;
            if (!same.isNone()) return param_val; // Non-trivial merge of >= 2 distinct SSA values.
            same = op_val;
        }

        if (same.isNone()) {
            // Unreachable or self-referential dead loop: materialize typed zero fallback:
            const param_ty = self.body.getInst(param_val).type_id;
            same = try self.emitDefaultScalarInBlock(.fromInt(0), param_ty);
        }

        try self.trivial_replacements.put(self.allocator, param_val.asInt(), same);

        // Cascade triviality check to any other Braun `block_param`s that consumed `param_val`:
        if (self.param_users.get(param_val.asInt())) |users_list| {
            const snapshot = try self.allocator.dupe(MirValueId, users_list.items);
            defer self.allocator.free(snapshot);
            for (snapshot) |user_phi| {
                if (user_phi != param_val and !self.trivial_replacements.contains(user_phi.asInt())) {
                    _ = try self.tryRemoveTrivialBlockParam(user_phi);
                }
            }
        }

        return self.resolveValue(same);
    }

    /// Seals `block_id` once all of its CFG predecessors have been wired (`Braun Algorithm 4`).
    pub fn sealBlock(self: *MirSsaBuilder, block_id: MirBlockId) !void {
        const blk_idx = block_id.asInt();
        if (self.blocks_scratch.items[blk_idx].is_sealed) return;

        self.blocks_scratch.items[blk_idx].is_sealed = true;
        self.body.blocks.items[blk_idx].setSealed(true);

        const pending = try self.allocator.dupe(
            IncompletePhi,
            self.blocks_scratch.items[blk_idx].incomplete_phis.items,
        );
        defer self.allocator.free(pending);
        self.blocks_scratch.items[blk_idx].incomplete_phis.clearRetainingCapacity();

        for (pending) |inc_phi| {
            _ = try self.addBlockParamOperands(inc_phi.var_id, block_id, inc_phi.param_val);
        }
    }

    /// Finalizes `self.body`: seals any remaining blocks, sweeps unreachable blocks from `^bb0`,
    /// collapses post-prune trivial phis, packs contiguous block/edge arrays, and rewrites all uses.
    pub fn finish(self: *MirSsaBuilder) !void {
        const block_count = self.body.blocks.items.len;
        if (block_count == 0) return;

        // [1] Seal any remaining unsealed blocks:
        for (0..block_count) |bb_i| {
            if (!self.blocks_scratch.items[bb_i].is_sealed) {
                try self.sealBlock(MirBlockId.fromInt(@intCast(bb_i)));
            }
        }

        // [2] Compute CFG reachability from entry block `^bb0` via bounded BFS queue:
        var is_reachable = try self.allocator.alloc(bool, block_count);
        defer self.allocator.free(is_reachable);
        @memset(is_reachable, false);

        var bfs_queue = try self.allocator.alloc(u32, block_count);
        defer self.allocator.free(bfs_queue);
        var q_head: usize = 0;
        var q_tail: usize = 0;
        is_reachable[0] = true;
        bfs_queue[q_tail] = 0;
        q_tail += 1;

        while (q_head < q_tail) : (q_head += 1) {
            const cur_bb = bfs_queue[q_head];
            const term = self.body.blocks.items[cur_bb].terminator;
            for (self.body.extra_edges.items[term.edge_start .. term.edge_start + term.edge_len]) |edge| {
                const dst = edge.target_bb.asInt();
                if (dst < block_count and !is_reachable[dst]) {
                    is_reachable[dst] = true;
                    bfs_queue[q_tail] = dst;
                    q_tail += 1;
                }
            }
        }

        // [3] Clear unreachable blocks & prune dead incoming `EdgeId`s on reachable blocks:
        for (0..block_count) |bb_i| {
            if (!is_reachable[bb_i]) {
                self.blocks_scratch.items[bb_i].params.clearRetainingCapacity();
                self.blocks_scratch.items[bb_i].insts.clearRetainingCapacity();
                self.blocks_scratch.items[bb_i].preds.clearRetainingCapacity();
                self.blocks_scratch.items[bb_i].has_call_ret_param = false;
                self.body.blocks.items[bb_i].terminator = .{ .kind = .unreachable_term };
            } else {
                var preds = &self.blocks_scratch.items[bb_i].preds;
                var write_i: usize = 0;
                for (preds.items) |edge_id| {
                    const src_idx = self.body.extra_edges.items[edge_id.asInt()].src_bb.asInt();
                    if (src_idx < block_count and is_reachable[src_idx]) {
                        preds.items[write_i] = edge_id;
                        write_i += 1;
                    }
                }
                preds.items.len = write_i;
            }
        }

        // [4] Re-run trivial block-param collapse on reachable blocks after dead-predecessor pruning:
        var has_collapsed_more = true;
        while (has_collapsed_more) {
            has_collapsed_more = false;
            for (0..block_count) |bb_i| {
                if (!is_reachable[bb_i]) continue;
                for (self.blocks_scratch.items[bb_i].params.items) |param_val| {
                    if (self.pinned_params.contains(param_val.asInt()) or
                        self.trivial_replacements.contains(param_val.asInt()))
                    {
                        continue;
                    }
                    const after = try self.tryRemoveTrivialBlockParam(param_val);
                    if (after != param_val) has_collapsed_more = true;
                }
            }
        }

        // [5] Pack surviving `block_params`, `block_insts`, `extra_edges`, `pred_edges`, and edge args:
        self.body.block_params.clearRetainingCapacity();
        self.body.block_insts.clearRetainingCapacity();
        self.body.pred_edges.clearRetainingCapacity();

        // Compact `extra_edges` so only edges from reachable blocks remain (`V2` bijection):
        var old_to_new_edge = try self.allocator.alloc(EdgeId, self.body.extra_edges.items.len);
        defer self.allocator.free(old_to_new_edge);
        @memset(old_to_new_edge, .none);

        var new_edges: std.ArrayListUnmanaged(MirOutgoingEdge) = .empty;
        errdefer new_edges.deinit(self.body.allocator);

        for (0..block_count) |bb_i| {
            if (!is_reachable[bb_i]) continue;
            var term = &self.body.blocks.items[bb_i].terminator;
            const old_start = term.edge_start;
            const old_len = term.edge_len;
            const new_start: u32 = @intCast(new_edges.items.len);

            for (0..old_len) |offset| {
                const old_eid = old_start + @as(u32, @intCast(offset));
                const old_edge = self.body.extra_edges.items[old_eid];
                const dst_bb = old_edge.target_bb.asInt();
                const dst_scratch = &self.blocks_scratch.items[dst_bb];
                const call_offset: usize = @intFromBool(dst_scratch.has_call_ret_param);
                const raw_edge_args = self.edge_args_scratch.items[old_eid].items;

                const packed_args_start: u32 = @intCast(self.body.extra_args.items.len);
                var packed_args_len: u16 = 0;

                for (dst_scratch.params.items, 0..) |dst_param, param_pos| {
                    if (param_pos < call_offset) continue;
                    if (self.trivial_replacements.contains(dst_param.asInt())) continue;
                    const edge_arg_pos = param_pos - call_offset;
                    const arg_val = if (edge_arg_pos < raw_edge_args.len and
                        !raw_edge_args[edge_arg_pos].isNone())
                        self.resolveValue(raw_edge_args[edge_arg_pos])
                    else
                        try self.emitDefaultScalarInBlock(.fromInt(0), self.body.getInst(dst_param).type_id);
                    try self.body.extra_args.append(self.body.allocator, arg_val.asInt());
                    packed_args_len += 1;
                }

                const new_eid = EdgeId.fromInt(@intCast(new_edges.items.len));
                old_to_new_edge[old_eid] = new_eid;
                try new_edges.append(self.body.allocator, .{
                    .src_bb = old_edge.src_bb,
                    .target_bb = old_edge.target_bb,
                    .args_start = packed_args_start,
                    .args_len = packed_args_len,
                    .case_tag_idx = old_edge.case_tag_idx,
                });
            }
            term.edge_start = new_start;
        }

        self.body.extra_edges.deinit(self.body.allocator);
        self.body.extra_edges = new_edges;

        // Pack per-block `block_params`, `block_insts`, and remapped `pred_edges`:
        const operands_col = self.body.insts.items(.operands);
        for (0..block_count) |bb_i| {
            var bb_rec = &self.body.blocks.items[bb_i];
            const scratch = &self.blocks_scratch.items[bb_i];

            bb_rec.param_start = @intCast(self.body.block_params.items.len);
            var kept_params: u14 = 0;
            for (scratch.params.items) |param_val| {
                if (self.trivial_replacements.contains(param_val.asInt())) continue;
                operands_col[param_val.asInt()] = .{
                    .lhs = @intCast(bb_i),
                    .rhs = kept_params,
                };
                try self.body.block_params.append(self.body.allocator, param_val);
                kept_params += 1;
            }
            bb_rec.setParamLen(kept_params);

            bb_rec.inst_start = @intCast(self.body.block_insts.items.len);
            bb_rec.inst_len = @intCast(scratch.insts.items.len);
            try self.body.block_insts.appendSlice(self.body.allocator, scratch.insts.items);

            bb_rec.pred_start = @intCast(self.body.pred_edges.items.len);
            var kept_preds: u16 = 0;
            for (scratch.preds.items) |old_pred_eid| {
                if (old_pred_eid.asInt() < old_to_new_edge.len) {
                    const mapped_eid = old_to_new_edge[old_pred_eid.asInt()];
                    if (!mapped_eid.isNone()) {
                        try self.body.pred_edges.append(self.body.allocator, mapped_eid);
                        kept_preds += 1;
                    }
                }
            }
            bb_rec.pred_len = kept_preds;
            bb_rec.setSealed(true);
            bb_rec.setCleanupPad(scratch.is_cleanup_pad);
        }

        // [6] Rewrite all SSA `MirValueId` uses across instructions, projections, terminators, and calls:
        self.body.forEachInstAndProjValueMut(self, rewriteValueSlot);
    }

    /// Callback passed to `MirBody.forEachInstAndProjValueMut` resolving eliminated phis.
    fn rewriteValueSlot(self: *MirSsaBuilder, raw_slot: *u32) void {
        if (raw_slot.* == NONE_U32) return;
        raw_slot.* = self.resolveValue(MirValueId.fromInt(raw_slot.*)).asInt();
    }

    /// Chases `trivial_replacements` chains to the canonical surviving `MirValueId`.
    pub fn resolveValue(self: *const MirSsaBuilder, initial_val: MirValueId) MirValueId {
        var cur = initial_val;
        var guard_steps: usize = 0;
        while (!cur.isNone() and guard_steps < 1024) : (guard_steps += 1) {
            if (self.trivial_replacements.get(cur.asInt())) |next_val| {
                if (next_val == cur) break;
                cur = next_val;
            } else {
                break;
            }
        }
        return cur;
    }

    /// Finds the index of `param_val` inside `blocks_scratch[block_id].params`.
    fn findParamPosition(self: *const MirSsaBuilder, block_id: MirBlockId, param_val: MirValueId) ?usize {
        for (self.blocks_scratch.items[block_id.asInt()].params.items, 0..) |cand, i| {
            if (cand == param_val) return i;
        }
        return null;
    }

    /// Records that `dependent_phi` reads `operand_val` so cascading trivial removal wakes `dependent_phi`.
    fn recordParamUser(self: *MirSsaBuilder, operand_val: MirValueId, dependent_phi: MirValueId) !void {
        if (operand_val.isNone() or operand_val == dependent_phi) return;
        if (self.body.getInst(operand_val).op != .block_param) return;
        const gop = try self.param_users.getOrPut(self.allocator, operand_val.asInt());
        if (!gop.found_existing) {
            gop.value_ptr.* = .empty;
        }
        for (gop.value_ptr.items) |existing| {
            if (existing == dependent_phi) return;
        }
        try gop.value_ptr.append(self.allocator, dependent_phi);
    }

    /// Synthesizes a zero/unit `const_scalar` at the front of `block_id` (`^bb0`) so it dominates all blocks (`V1`).
    fn emitDefaultScalarInBlock(
        self: *MirSsaBuilder,
        block_id: MirBlockId,
        val_ty: TypeId,
    ) !MirValueId {
        const mir_const: MirConst = switch (val_ty) {
            .unit_ty, .never_ty => .unit_val,
            .bool_ty => .{ .bool_val = false },
            .char_ty => .{ .char_val = 0 },
            .f32_ty, .f64_ty, .untyped_float_ty => .{ .float_val = 0.0 },
            .str_ty => .{ .str_val = .empty },
            else => .{ .int_val = 0 },
        };
        const const_idx = try self.body.appendConst(mir_const);
        const val_id = try self.allocRawInst(.{
            .op = .const_scalar,
            .flags = .{ .is_synthetic = true },
            .type_id = val_ty,
            .operands = .{ .lhs = const_idx, .rhs = 0 },
        }, .none);
        if (self.blocks_scratch.items.len > 0) {
            const target_idx = if (!block_id.isNone() and block_id.asInt() < self.blocks_scratch.items.len)
                block_id.asInt()
            else
                0;
            try self.blocks_scratch.items[target_idx].insts.insert(self.allocator, 0, val_id);
        }
        return val_id;
    }

    /// Emits `E0508` (`comptime_resource_limit_exceeded`) once when a `MirBody` cap overflows.
    fn reportResourceOverflow(self: *MirSsaBuilder, message: []const u8) !void {
        if (self.body.has_overflowed_limits) return;
        self.body.has_overflowed_limits = true;
        if (self.diagnostic_sink) |sink| {
            const span = Span.init(self.body.file_id, 0, 0);
            const labels = [1]LabeledSpan{.{
                .span = span,
                .label = "MIR resource limit exceeded here",
                .style = .primary,
            }};
            try sink.emit(.{
                .code = .e0508_comptime_resource_limit_exceeded,
                .severity = .err,
                .primary_span = span,
                .message = message,
                .labels = &labels,
            });
        }
    }
};

// ---------- `HIR -> MIR` Lowering Context & Helpers -----------

/// Active `defer` or `errdefer |err|` scope entry on `MirLowerer.cleanup_stack` (`DR-13` §4.2).
const CleanupEntry = struct {
    /// `true` for `errdefer`, `false` for unconditional `defer`.
    is_errdefer: bool,
    /// Optional `HirStore` local slot capturing `|err|` (`NONE_U32` when absent).
    hir_err_local: u32,
    /// Cleanup body `HirIndex` executed on scope exit / unwinding.
    body_hir: HirIndex,
    /// Lexical block nesting depth at registration time.
    scope_depth: u32,
    /// Enclosing `hir_loop` nesting depth at registration time.
    loop_depth: u32,
    /// Prefix count of `MirLowerer.storage_locals` active when this cleanup entry was registered.
    storage_floor: usize = 0,
    /// Lazily constructed shared cold error cleanup pad (`is_cleanup_pad = true`).
    cached_err_pad: MirBlockId = .none,
};

/// Saved `(hir_slot -> LocalId)` mapping for `subscript` post-`yield` execution.
const SubscriptLocalBinding = struct {
    /// `HirStore` local slot inside the `subscript` function.
    hir_slot: u32,
    /// Mapped caller-side temporary `LocalId`.
    local_id: LocalId,
};

/// Saved `(hir_slot -> PlaceId)` mapping for `subscript` post-`yield` execution.
const SubscriptPlaceBinding = struct {
    /// `HirStore` local slot inside the `subscript` function.
    hir_slot: u32,
    /// Mapped caller-side aliased `PlaceId`.
    place_id: PlaceId,
};

/// Deferred post-`yield` `subscript` cleanup triggered when `trigger_tok` closes (`Fix-06B`).
const DeferredSubscriptCleanup = struct {
    /// Ghost access token (`yield_ghost_tok`) whose close executes `post_yield_stmts`.
    trigger_tok: MirValueId,
    /// Owning `HirStore` of `post_yield_stmts` (`null` uses `MirLowerer.hir_store`).
    sub_store: ?*const HirStore = null,
    /// Optional index in `MirBody.vacated_windows` updated with `end_block` on close.
    vacated_window_idx: ?usize = null,
    /// Post-`yield` trailing `HirIndex` statements and subscript `defer`s from the `subscript` body.
    post_yield_stmts: std.ArrayListUnmanaged(HirIndex) = .empty,
    /// Captured `hir_local_remap` pairs for `post_yield_stmts`.
    local_bindings: std.ArrayListUnmanaged(SubscriptLocalBinding) = .empty,
    /// Captured `hir_place_remap` pairs for `post_yield_stmts`.
    place_bindings: std.ArrayListUnmanaged(SubscriptPlaceBinding) = .empty,

    /// Releases lists owned by `self`.
    fn deinit(self: *DeferredSubscriptCleanup, allocator: std.mem.Allocator) void {
        self.post_yield_stmts.deinit(allocator);
        self.local_bindings.deinit(allocator);
        self.place_bindings.deinit(allocator);
    }
};

/// Active address-taken / non-`Copy` local requiring `ghost_storage_deinit` on scope exit.
const ActiveStorageLocal = struct {
    /// Target `LocalId` in `MirBody.locals`.
    local_id: LocalId,
    /// Lexical block depth where this local was initialized.
    scope_depth: u32,
    /// Loop nesting depth where this local was initialized.
    loop_depth: u32,
    /// Originating token for `ghost_storage_deinit`.
    origin_token: TokenIndex,
};

/// Active `hir_loop` break/continue targets on `MirLowerer.loop_stack`.
const LoopTargets = struct {
    /// Canonical `loop_id` matching `HirNode.data.rhs` on `hir_loop` / `hir_break` / `hir_continue`.
    loop_id: u32,
    /// Unsealed loop header block (`continue` target).
    header_bb: MirBlockId,
    /// Loop exit join block (`break` target).
    exit_bb: MirBlockId,
    /// SSA variable holding the `break expr` value when `loop` produces a non-unit value (`NONE_U32` if unit).
    break_var_id: u32,
    /// Lexical `scope_depth` outside the loop body (cleanup boundary for `break` / `continue`).
    outer_scope_depth: u32,
    /// `loop_depth` of this loop (`cleanup_stack` filter boundary).
    loop_depth: u32,
    /// `active_expr_borrows` length outside the loop.
    outer_borrow_depth: usize,
};

/// Active labeled `fsm: match` transition target for `continue :fsm next_state;` (`SE-23`).
const FsmMatchTargets = struct {
    /// Unflagged FSM identifier (`fsm_meta.fsm_id & ~LABELED_MATCH_CONTINUE_FLAG`) matched by `findFsmTargets`.
    fsm_id: u32,
    /// Unsealed dispatch header block re-entered on every `continue :fsm` transition.
    dispatch_bb: MirBlockId,
    /// Mutable scrutinee `PlaceId` overwritten with `next_state` prior to jumping to `dispatch_bb`.
    scrut_place: PlaceId,
    /// Static `TypeId` of `scrut_place`.
    scrut_ty: TypeId,
    /// Lexical `scope_depth` outside the `match` arms (arm cleanup boundary).
    outer_scope_depth: u32,
    /// `active_expr_borrows` depth at `dispatch_bb` entry.
    outer_borrow_depth: usize,
};

/// Returns the shared slice element `TypeId` when `raw_ty` is an `SE-09` union-bounded type parameter
/// (`[Data: str | &[u8]]`), or `null` otherwise.
pub fn unionSliceElemType(pool: *const InternPool, raw_ty: TypeId) ?TypeId {
    if (raw_ty.isError()) return null;
    const unwrapped = pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped.isError()) return null;
    const node = pool.getNode(unwrapped);
    if (node.tag != .type_param and node.tag != .bind_once_group_var and node.tag != .bind_many_any_var) {
        return null;
    }
    const grp_ty = TypeId.fromInt(node.lhs);
    if (grp_ty.isError()) return null;
    const grp_node = pool.getNode(grp_ty);
    if (grp_node.tag != .user_group or grp_node.rhs == type_system.INTERSECT_GROUP_SENTINEL) return null;
    const view = pool.getUserGroupView(grp_ty) orelse return null;

    var member_count: usize = 0;
    var shared_elem: ?TypeId = null;

    const combined_prim_mask = view.prim_mask | view.tilde_prim_mask;
    var prim_idx: u32 = 0;
    while (prim_idx <= 18) : (prim_idx += 1) {
        const prim_tid = TypeId.fromInt(prim_idx);
        if (!type_system.TypeGroupMask.containsPrimitive(combined_prim_mask, prim_tid)) continue;
        if (prim_tid != .str_ty) return null;
        if (shared_elem) |prev| {
            if (prev != .u8_ty) return null;
        } else {
            shared_elem = .u8_ty;
        }
        member_count += 1;
    }

    const lists = [2][]const u32{ view.exact_members, view.tilde_members };
    for (lists) |mem_list| {
        for (mem_list) |raw_mem| {
            const mem_ty = pool.unwrapUnderlyingType(TypeId.fromInt(raw_mem));
            if (mem_ty.isError()) return null;
            const elem_ty: TypeId = if (mem_ty == .str_ty)
                .u8_ty
            else blk_elem: {
                const mem_node = pool.getNode(mem_ty);
                const inner_ty = if (mem_node.tag == .ref_ty or mem_node.tag == .mut_ref_ty)
                    pool.unwrapUnderlyingType(TypeId.fromInt(mem_node.lhs))
                else
                    mem_ty;
                const inner_node = pool.getNode(inner_ty);
                if (inner_node.tag != .slice_ty and inner_node.tag != .array_ty) return null;
                break :blk_elem pool.unwrapUnderlyingType(TypeId.fromInt(inner_node.lhs));
            };
            if (shared_elem) |prev| {
                if (prev != elem_ty) return null;
            } else {
                shared_elem = elem_ty;
            }
            member_count += 1;
        }
    }
    return if (member_count >= 2) shared_elem else null;
}

/// Resolved `subscript` template metadata and its owning `HirStore`.
const ResolvedSubscriptMeta = struct {
    /// `HirStore` owning `functions[fn_meta_idx]` and its body HIR nodes/locals.
    store: *const HirStore,
    /// Index into `store.functions`.
    fn_meta_idx: usize,
};

/// Saved shadowed `(hir_slot -> prev_local / prev_place)` entry restored when exiting a `subscript` splice.
const SubscriptRemapShadow = struct {
    /// Shadowed `HirStore` local slot key.
    hir_slot: u32,
    /// Previous `hir_local_remap` binding (`null` if absent).
    prev_local: ?LocalId = null,
    /// Previous `hir_place_remap` binding (`null` if absent).
    prev_place: ?PlaceId = null,
};

/// Result of splicing a `subscript … yield` call site into a caller `MirPlace`.
const SplicedSubscriptAccess = struct {
    /// Lowered `PlaceId` yielded by the `subscript` body.
    place_id: PlaceId,
    /// Owning `HirStore` of `post_yield_stmts` (`null` uses `MirLowerer.hir_store`).
    sub_store: ?*const HirStore = null,
    /// Ghost access token opened on the yielded place (`.none` if pure rvalue temp).
    yield_ghost_tok: MirValueId = .none,
    /// Optional index in `MirBody.vacated_windows` tracking this `inout` vacated projection (`Fix-06B`).
    vacated_window_idx: ?usize = null,
    /// Post-`yield` trailing `HirIndex` statements inside the `subscript` body to run on close.
    post_yield_stmts: std.ArrayListUnmanaged(HirIndex) = .empty,
    /// Ghost tokens opened for the `subscript` call arguments themselves.
    arg_ghost_tokens: std.ArrayListUnmanaged(MirValueId) = .empty,
    /// Captured `hir_local_remap` pairs for `post_yield_stmts`.
    local_bindings: std.ArrayListUnmanaged(SubscriptLocalBinding) = .empty,
    /// Captured `hir_place_remap` pairs for `post_yield_stmts`.
    place_bindings: std.ArrayListUnmanaged(SubscriptPlaceBinding) = .empty,

    /// Releases lists owned by `self`.
    fn deinit(self: *SplicedSubscriptAccess, allocator: std.mem.Allocator) void {
        self.post_yield_stmts.deinit(allocator);
        self.arg_ghost_tokens.deinit(allocator);
        self.local_bindings.deinit(allocator);
        self.place_bindings.deinit(allocator);
    }
};

/// Stateful `HIR -> MIR` lowering engine for a single function or constant body.
const MirLowerer = struct {
    /// Scratch allocator for temporary lowering tables.
    allocator: std.mem.Allocator,
    /// Source `HirStore`.
    hir_store: *const HirStore,
    /// Additional `HirStore`s searched when splicing cross-`DefId` / cross-file `subscript` templates.
    extra_hir_stores: []const *const HirStore = &.{},
    /// Canonical type pool.
    pool: *InternPool,
    /// Resolved symbol table.
    sym_table: *const SymbolTable,
    /// String interner.
    interner: *const StringInterner,
    /// Target `MirBody` under construction.
    body: *MirBody,
    /// Braun single-pass SSA builder bound to `body`.
    ssa: MirSsaBuilder,
    /// Optional diagnostic sink.
    diagnostic_sink: ?*DiagnosticSink,

    /// Base offset in `hir_store.locals` corresponding to `LocalId(0)` of the root function.
    base_hir_local: u32 = 0,
    /// Number of locals in the root function (`hir_local_to_mir` base range).
    root_local_len: u32 = 0,
    /// Dynamic remapping table `(hir_local_id -> LocalId)` used during `subscript` splicing & errdefers.
    hir_local_remap: std.AutoHashMapUnmanaged(u32, LocalId) = .empty,
    /// Dynamic place alias table `(hir_local_id -> PlaceId)` used when splicing `subscript` place params.
    hir_place_remap: std.AutoHashMapUnmanaged(u32, PlaceId) = .empty,
    /// Concrete types of all `LocalId`s (`var_types` slice backing `MirSsaBuilder`).
    local_var_types: std.ArrayListUnmanaged(TypeId) = .empty,

    /// Current insertion basic block (`.none` after an unconditional jump until a join block starts).
    cur_bb: MirBlockId = .none,
    /// Current lexical `{ … }` scope nesting depth.
    scope_depth: u32 = 0,
    /// Enclosing non-synthetic `{ … }` block depth so walrus `:=` wrappers bind to statement scope (`SE-01`).
    enclosing_real_block_depth: u32 = 0,
    /// Active `ConditionScope` depth while lowering `hir_cond_if` / `hir_cond_while` clauses (`SE-01`).
    active_cond_scope_depth: u32 = 0,
    /// Current `hir_loop` nesting depth.
    loop_depth: u32 = 0,
    /// True while lowering cleanup pad instructions (suppresses nested errdefer registration).
    is_lowering_cleanup: bool = false,
    /// True while lowering a mutable target place (`&mut p`, `p = v`, `inout p`, `set p`).
    is_mut_place_context: bool = false,

    /// Active mid-expression Ghost access tokens (closed LIFO on early exit).
    active_expr_borrows: std.ArrayListUnmanaged(MirValueId) = .empty,
    /// Unified LIFO `defer` / `errdefer` stack (`DR-13` §4.2).
    cleanup_stack: std.ArrayListUnmanaged(CleanupEntry) = .empty,
    /// Active memory-backed locals requiring `ghost_storage_deinit` on scope exit.
    storage_locals: std.ArrayListUnmanaged(ActiveStorageLocal) = .empty,
    /// Active loop targets stack for `hir_break` / `hir_continue`.
    loop_stack: std.ArrayListUnmanaged(LoopTargets) = .empty,
    /// Active labeled `fsm: match` targets stack for `continue :fsm next_state;` (`SE-23`).
    fsm_stack: std.ArrayListUnmanaged(FsmMatchTargets) = .empty,
    /// Per-arm pattern storage capture list active while compiling a labeled `fsm: match` leaf (`SE-23`).
    active_fsm_arm_storage: ?*std.ArrayListUnmanaged(LocalId) = null,
    /// Most recent LHS `PlaceId` written by `hir_assign` / `hir_bitfield_rmw` for `SE-15` group tracking.
    last_assigned_place: PlaceId = .none,
    /// Deferred `subscript` post-`yield` cleanups awaiting `yield_ghost_tok` close.
    deferred_subscript_cleanups: std.ArrayListUnmanaged(DeferredSubscriptCleanup) = .empty,
    /// Active `(store, fn_meta_idx)` recursion guard frames preventing cyclic `subscript` splicing.
    subscript_splice_stack: [16]SubscriptSpliceFrame = @splat(.{}),
    /// Current depth of `subscript_splice_stack`.
    subscript_splice_depth: usize = 0,
    /// Counter of Maranget decision-tree nodes synthesized in the current `match` (`MAX_DECISION_NODES`).
    decision_node_count: u32 = 0,
    /// `true` when lowering for Phase 6 `mir_sast` so mutable `&T`, `*T`, and `str` bindings keep place stores.
    is_for_sast: bool = false,
    /// `true` when lowering a standalone `subscript` arm in `is_for_sast` mode.
    is_sast_subscript_body: bool = false,
    /// `true` when the active standalone `subscript` arm in `is_for_sast` mode is `inout`.
    is_sast_subscript_inout: bool = false,

    /// Releases all temporary lowering buffers owned by `self`.
    fn deinit(self: *MirLowerer) void {
        for (self.deferred_subscript_cleanups.items) |*def_sub| {
            def_sub.deinit(self.allocator);
        }
        self.deferred_subscript_cleanups.deinit(self.allocator);
        self.ssa.deinit();
        self.hir_local_remap.deinit(self.allocator);
        self.hir_place_remap.deinit(self.allocator);
        self.local_var_types.deinit(self.allocator);
        self.active_expr_borrows.deinit(self.allocator);
        self.cleanup_stack.deinit(self.allocator);
        self.storage_locals.deinit(self.allocator);
        self.loop_stack.deinit(self.allocator);
        self.fsm_stack.deinit(self.allocator);
        self.* = undefined;
    }

    // ---------------- Address-Taken & Local Setup -----------------

    /// Pre-scans `root_hir` to mark locals that require stack/place identity (`is_address_taken = true`).
    fn scanAddressTakenLocals(self: *MirLowerer, root_hir: HirIndex) void {
        if (root_hir.isNone() or root_hir.asInt() >= self.hir_store.nodes.len) return;

        // First mark formal `inout`/`set` parameters and non-`Copy` / aggregate-scrutinized locals:
        for (self.body.locals.items, 0..) |*loc, i| {
            var fl = loc.flags();
            if (i == 0) {
                fl.is_address_taken = true;
            } else if (loc.mode() == .inout_mode or loc.mode() == .set_mode) {
                fl.is_address_taken = true;
            } else if (!self.isSsaScalarEligibleType(loc.type_id)) {
                fl.is_address_taken = true;
            } else if (self.is_for_sast and fl.is_mut and !fl.is_arg) {
                const unwrapped = self.pool.unwrapUnderlyingType(loc.type_id);
                if (!unwrapped.isError()) {
                    const tag = self.pool.getNode(unwrapped).tag;
                    if (unwrapped == .str_ty or tag == .ref_ty or tag == .raw_ptr_ty) {
                        fl.is_address_taken = true;
                    }
                }
            }
            loc.setFlags(fl);
        }

        self.scanHirSubtreeForPlaces(root_hir);
    }

    /// Returns `true` if `ty` is a `Copy` scalar/pointer/shared-reference eligible for pure Braun SSA registers.
    fn isSsaScalarEligibleType(self: *const MirLowerer, ty: TypeId) bool {
        if (ty.isError()) return true;
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
            .untyped_int_ty,
            .untyped_float_ty,
            => return true,
            else => {},
        }
        const unwrapped = self.pool.unwrapUnderlyingType(ty);
        if (unwrapped != ty) return self.isSsaScalarEligibleType(unwrapped);
        const node = self.pool.getNode(ty);
        return switch (node.tag) {
            .ref_ty, .raw_ptr_ty, .fn_ty => true,
            .bit_field_ty => self.isSsaScalarEligibleType(TypeId.fromInt(node.lhs)),
            else => false,
        };
    }

    /// Returns `true` if values of `ty` can retain borrowed references or stack-pinned regions.
    fn hasTypeRegions(self: *const MirLowerer, ty: TypeId) bool {
        return self.hasTypeRegionsDepth(ty, 0);
    }

    /// Bounded recursive check for borrowed references or slices inside `ty`.
    fn hasTypeRegionsDepth(self: *const MirLowerer, ty: TypeId, depth: u8) bool {
        if (ty.isError()) return false;
        const unwrapped = self.pool.unwrapUnderlyingType(ty);
        if (depth >= 8) return true;
        if (self.pool.getFlags(unwrapped).has_regions) return true;
        switch (unwrapped) {
            .unit_ty,
            .never_ty,
            .bool_ty,
            .char_ty,
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
            .untyped_int_ty,
            .untyped_float_ty,
            .source_loc_ty,
            .fmt_spec_ty,
            => return false,
            .str_ty, .fmt_args_ty => return true,
            else => {},
        }
        const node = self.pool.getNode(unwrapped);
        return switch (node.tag) {
            .ref_ty,
            .mut_ref_ty,
            .slice_ty,
            .soa_slice_ty,
            .closure_ty,
            .future_ty,
            .dyn_trait_ty,
            .type_param,
            .bind_once_group_var,
            .bind_many_any_var,
            .associated_ty,
            => true,
            .raw_ptr_ty, .fn_ty, .bit_field_ty => false,
            .optional_ty => self.hasTypeRegionsDepth(TypeId.fromInt(node.lhs), depth + 1),
            .result_ty => self.hasTypeRegionsDepth(TypeId.fromInt(node.lhs), depth + 1) or
                self.hasTypeRegionsDepth(TypeId.fromInt(node.rhs), depth + 1),
            .array_ty, .soa_array_ty, .soa_vec_ty => self.hasTypeRegionsDepth(TypeId.fromInt(node.lhs), depth + 1),
            .tuple_ty => blk: {
                for (self.pool.getTupleElements(unwrapped)) |raw_elem| {
                    if (self.hasTypeRegionsDepth(TypeId.fromInt(raw_elem), depth + 1)) break :blk true;
                }
                break :blk false;
            },
            .struct_ty, .union_ty => blk: {
                const sym = self.sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                if (sym.target_scope.isNone()) break :blk false;
                const nom_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, unwrapped);
                for (self.sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                    const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                    if (mem_sym.kind == .field_sym and
                        self.hasTypeRegionsDepth(nom_subst.resolve(mem_sym.type_id), depth + 1))
                    {
                        break :blk true;
                    }
                }
                break :blk false;
            },
            .enum_ty => blk: {
                const sym = self.sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                if (sym.target_scope.isNone()) break :blk false;
                const nom_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, unwrapped);
                for (self.sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                    const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                    if (mem_sym.kind == .enum_variant_sym and mem_sym.type_id != .unit_ty and
                        self.hasTypeRegionsDepth(nom_subst.resolve(mem_sym.type_id), depth + 1))
                    {
                        break :blk true;
                    }
                }
                break :blk false;
            },
            else => false,
        };
    }

    /// Walks `hir_id` marking any local whose address is taken, projected as lvalue, or mutably borrowed.
    fn scanHirSubtreeForPlaces(self: *MirLowerer, hir_id: HirIndex) void {
        if (hir_id.isNone() or hir_id.asInt() >= self.hir_store.nodes.len) return;
        const node = self.hir_store.getNode(hir_id);

        switch (node.tag) {
            .hir_unary_op => {
                const uop: hir.HirUnaryOp = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))));
                const sub = HirIndex.fromInt(node.data.rhs);
                if (uop == .addr_of or uop == .addr_of_mut or
                    uop == .addr_of_raw or uop == .addr_of_raw_mut or uop == .deref)
                {
                    self.markRootLocalAddressTaken(sub);
                }
                self.scanHirSubtreeForPlaces(sub);
            },
            .hir_project_arg => {
                const mode: ParamMode = @fromBackingInt(@intCast(@as(u2, @truncate(node.data.lhs))));
                const sub = HirIndex.fromInt(node.data.rhs);
                if (mode == .inout_mode or mode == .set_mode) {
                    self.markRootLocalAddressTaken(sub);
                }
                self.scanHirSubtreeForPlaces(sub);
            },
            .hir_assign => {
                const lhs = HirIndex.fromInt(node.data.lhs);
                if (!lhs.isNone() and self.hir_store.getNode(lhs).tag != .hir_var_ref) {
                    self.markRootLocalAddressTaken(lhs);
                }
                self.scanHirSubtreeForPlaces(lhs);
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.rhs));
            },
            .hir_bitfield_rmw => {
                const lhs = HirIndex.fromInt(node.data.lhs);
                if (!lhs.isNone() and self.hir_store.getNode(lhs).tag != .hir_var_ref) {
                    self.markRootLocalAddressTaken(lhs);
                }
                self.scanHirSubtreeForPlaces(lhs);
                if (node.data.rhs + 2 <= self.hir_store.extra_data.items.len) {
                    self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs + 1]));
                }
            },
            .hir_field_proj, .hir_bitfield_read, .hir_cast, .hir_return, .hir_yield, .hir_await => {
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.lhs));
            },
            .hir_index_proj => {
                self.markRootLocalAddressTaken(HirIndex.fromInt(node.data.lhs));
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.lhs));
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.rhs));
            },
            .hir_soa_field_ptr => {
                self.markRootLocalAddressTaken(HirIndex.fromInt(node.data.lhs));
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.lhs));
                if (node.data.rhs + 2 <= self.hir_store.extra_data.items.len) {
                    self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs + 1]));
                }
            },
            .hir_local_decl => {
                const rhs = HirIndex.fromInt(node.data.rhs);
                if (rhs.isNone()) {
                    const lid = self.mapHirLocal(node.data.lhs);
                    if (!lid.isNone()) {
                        var fl = self.body.locals.items[lid.asInt()].flags();
                        fl.is_address_taken = true;
                        self.body.locals.items[lid.asInt()].setFlags(fl);
                    }
                } else {
                    self.scanHirSubtreeForPlaces(rhs);
                }
            },
            .hir_const_decl, .hir_defer => {
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.rhs));
            },
            .hir_binary_op => {
                if (node.data.lhs + 2 <= self.hir_store.extra_data.items.len) {
                    self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[node.data.lhs]));
                    self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[node.data.lhs + 1]));
                }
            },
            .hir_block => {
                const stmts = self.hir_store.getLenPrefixedExtra(node.data.lhs);
                if (self.hir_store.parallel_assign_blocks.get(hir_id.asInt())) |pa_span| {
                    const start_i: usize = pa_span.first_assign_idx;
                    const end_i: usize = @min(start_i + pa_span.assign_count, stmts.len);
                    for (stmts[start_i..end_i]) |raw_assign| {
                        const assign_hir = HirIndex.fromInt(raw_assign);
                        if (!assign_hir.isNone() and assign_hir.asInt() < self.hir_store.nodes.len) {
                            const assign_node = self.hir_store.getNode(assign_hir);
                            if (assign_node.tag == .hir_assign or assign_node.tag == .hir_bitfield_rmw) {
                                self.markRootLocalAddressTaken(HirIndex.fromInt(assign_node.data.lhs));
                            }
                        }
                    }
                }
                for (stmts) |raw_stmt| {
                    self.scanHirSubtreeForPlaces(HirIndex.fromInt(raw_stmt));
                }
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.rhs));
            },
            .hir_if => {
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.lhs));
                if (node.data.rhs + 2 <= self.hir_store.extra_data.items.len) {
                    self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs]));
                    self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs + 1]));
                }
            },
            .hir_match => {
                if (self.hir_store.labeled_matches.get(hir_id.asInt())) |fsm_meta| {
                    const scrut_lid = self.mapHirLocal(fsm_meta.scrutinee_local);
                    if (!scrut_lid.isNone()) {
                        var fl = self.body.locals.items[scrut_lid.asInt()].flags();
                        fl.is_address_taken = true;
                        self.body.locals.items[scrut_lid.asInt()].setFlags(fl);
                    }
                }
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.lhs));
                if (node.data.rhs + 2 <= self.hir_store.extra_data.items.len) {
                    const arm_start = self.hir_store.extra_data.items[node.data.rhs];
                    const arm_len = self.hir_store.extra_data.items[node.data.rhs + 1];
                    for (self.hir_store.match_arms.items[arm_start .. arm_start + arm_len]) |arm| {
                        self.scanPatternForRefBinds(arm.pat_idx);
                        self.scanHirSubtreeForPlaces(arm.guard_hir);
                        self.scanHirSubtreeForPlaces(arm.body_hir);
                    }
                }
            },
            .hir_cond_if, .hir_cond_while => {
                var cursor = node.data.lhs;
                if (cursor < self.hir_store.extra_data.items.len) {
                    const clause_count = self.hir_store.extra_data.items[cursor];
                    cursor += 1;
                    var clause_i: u32 = 0;
                    while (clause_i < clause_count and cursor < self.hir_store.extra_data.items.len) : (clause_i += 1) {
                        const kind_raw = self.hir_store.extra_data.items[cursor];
                        cursor += 1;
                        if (kind_raw == @backingInt(hir.HirCondClauseKind.is_match)) {
                            if (cursor + 2 <= self.hir_store.extra_data.items.len) {
                                const scrut_hir = HirIndex.fromInt(self.hir_store.extra_data.items[cursor]);
                                const pat_idx = self.hir_store.extra_data.items[cursor + 1];
                                cursor += 2;
                                self.markRootLocalAddressTaken(scrut_hir);
                                self.scanHirSubtreeForPlaces(scrut_hir);
                                self.scanPatternForRefBinds(pat_idx);
                            }
                        } else if (cursor < self.hir_store.extra_data.items.len) {
                            self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[cursor]));
                            cursor += 1;
                        }
                    }
                    if (cursor < self.hir_store.extra_data.items.len) {
                        self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[cursor]));
                    }
                    if (node.tag == .hir_cond_if and cursor + 1 < self.hir_store.extra_data.items.len) {
                        self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[cursor + 1]));
                    }
                }
            },
            .hir_orelse => {
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.lhs));
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.rhs));
            },
            .hir_ctx_set, .hir_ctx_region_push => {
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.rhs));
            },
            .hir_slice_range => {
                self.markRootLocalAddressTaken(HirIndex.fromInt(node.data.lhs));
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.lhs));
                if (node.data.rhs + 3 <= self.hir_store.extra_data.items.len) {
                    self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs]));
                    self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs + 1]));
                }
            },
            .hir_loop => {
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.lhs));
            },
            .hir_break, .hir_continue => {
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.rhs));
            },
            .hir_call, .hir_subscript_call => {
                self.scanHirSubtreeForPlaces(HirIndex.fromInt(node.data.lhs));
                for (self.hir_store.getLenPrefixedExtra(node.data.rhs)) |raw_arg| {
                    self.scanHirSubtreeForPlaces(HirIndex.fromInt(raw_arg));
                }
            },
            .hir_construct => {
                const ckind: hir.HirConstructKind = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))));
                if (ckind == .array_repeat) {
                    if (node.data.rhs + 2 <= self.hir_store.extra_data.items.len) {
                        self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs + 1]));
                    }
                } else if (ckind == .fmt_args) {
                    if (node.data.rhs + 2 <= self.hir_store.extra_data.items.len) {
                        const piece_len = self.hir_store.extra_data.items[node.data.rhs];
                        const hole_len = self.hir_store.extra_data.items[node.data.rhs + 1];
                        const pieces_start = node.data.rhs + 2;
                        const holes_start = pieces_start + piece_len;
                        if (holes_start + hole_len * 3 <= self.hir_store.extra_data.items.len) {
                            for (self.hir_store.extra_data.items[pieces_start .. pieces_start + piece_len]) |raw_piece| {
                                self.scanHirSubtreeForPlaces(HirIndex.fromInt(raw_piece));
                            }
                            for (0..hole_len) |hole_i| {
                                const hole_hir = HirIndex.fromInt(
                                    self.hir_store.extra_data.items[holes_start + hole_i * 3],
                                );
                                self.markRootLocalAddressTaken(hole_hir);
                                self.scanHirSubtreeForPlaces(hole_hir);
                            }
                        }
                    }
                } else if (ckind == .fmt_value) {
                    if (node.data.rhs < self.hir_store.extra_data.items.len) {
                        self.scanHirSubtreeForPlaces(HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs]));
                    }
                } else if (ckind != .bitfield_zero) {
                    for (self.hir_store.getLenPrefixedExtra(node.data.rhs)) |raw_elem| {
                        self.scanHirSubtreeForPlaces(HirIndex.fromInt(raw_elem));
                    }
                }
            },
            .hir_intrinsic_call => {
                if (node.data.rhs + 2 <= self.hir_store.extra_data.items.len) {
                    const type_len = self.hir_store.extra_data.items[node.data.rhs];
                    const val_len = self.hir_store.extra_data.items[node.data.rhs + 1];
                    const val_start = node.data.rhs + 2 + type_len;
                    if (val_start + val_len <= self.hir_store.extra_data.items.len) {
                        for (self.hir_store.extra_data.items[val_start .. val_start + val_len]) |raw_arg| {
                            self.scanHirSubtreeForPlaces(HirIndex.fromInt(raw_arg));
                        }
                    }
                }
            },
            else => {},
        }
    }

    /// Marks pattern-bound locals that require address-taken storage if non-scalar or `ref`-bound.
    fn scanPatternForRefBinds(self: *MirLowerer, pat_idx: u32) void {
        if (pat_idx == NONE_U32 or pat_idx >= self.hir_store.patterns.items.len) return;
        const pat = self.hir_store.patterns.items[pat_idx];
        switch (pat.kind) {
            .bind => |bind_pat| {
                const lid = self.mapHirLocal(bind_pat.local_id);
                if (!lid.isNone() and (!self.isSsaScalarEligibleType(pat.type_id) or bind_pat.is_ref)) {
                    var fl = self.body.locals.items[lid.asInt()].flags();
                    fl.is_address_taken = true;
                    self.body.locals.items[lid.asInt()].setFlags(fl);
                }
            },
            .at_pat => |ap| {
                const lid = self.mapHirLocal(ap.local_id);
                if (!lid.isNone() and (!self.isSsaScalarEligibleType(pat.type_id) or ap.is_ref)) {
                    var fl = self.body.locals.items[lid.asInt()].flags();
                    fl.is_address_taken = true;
                    self.body.locals.items[lid.asInt()].setFlags(fl);
                }
                self.scanPatternForRefBinds(ap.sub_pat);
            },
            .slice_pat => |sp| {
                const sub_total = @as(u32, sp.prefix_len) + @as(u32, sp.suffix_len);
                if (sp.prefix_start + sub_total <= self.hir_store.extra_data.items.len) {
                    for (self.hir_store.extra_data.items[sp.prefix_start .. sp.prefix_start + sub_total]) |raw_pat| {
                        self.scanPatternForRefBinds(raw_pat);
                    }
                }
                if (sp.has_rest and sp.rest_local_id != NONE_U32) {
                    const lid = self.mapHirLocal(sp.rest_local_id);
                    if (!lid.isNone()) {
                        const rest_ty = self.body.locals.items[lid.asInt()].type_id;
                        if (!self.isSsaScalarEligibleType(rest_ty)) {
                            var fl = self.body.locals.items[lid.asInt()].flags();
                            fl.is_address_taken = true;
                            self.body.locals.items[lid.asInt()].setFlags(fl);
                        }
                    }
                }
            },
            .tuple => |sub| {
                for (self.hir_store.extra_data.items[sub.sub_start .. sub.sub_start + sub.sub_len]) |raw_pat| {
                    self.scanPatternForRefBinds(raw_pat);
                }
            },
            .struct_pat => |sp| {
                for (0..sp.field_len) |i| {
                    const pair_idx = sp.field_start + @as(u32, @intCast(i * 2));
                    if (pair_idx + 2 <= self.hir_store.extra_data.items.len) {
                        self.scanPatternForRefBinds(self.hir_store.extra_data.items[pair_idx + 1]);
                    }
                }
            },
            .variant => |vp| {
                for (self.hir_store.extra_data.items[vp.sub_start .. vp.sub_start + vp.sub_len]) |raw_pat| {
                    self.scanPatternForRefBinds(raw_pat);
                }
            },
            .or_pat => |op| {
                self.scanPatternForRefBinds(op.lhs_pat);
                self.scanPatternForRefBinds(op.rhs_pat);
            },
            else => {},
        }
    }

    /// Peels projections on `expr_hir` and marks the underlying base `LocalId` as `is_address_taken`.
    fn markRootLocalAddressTaken(self: *MirLowerer, expr_hir: HirIndex) void {
        var cur = expr_hir;
        var guard: usize = 0;
        while (!cur.isNone() and cur.asInt() < self.hir_store.nodes.len and guard < 64) : (guard += 1) {
            const node = self.hir_store.getNode(cur);
            switch (node.tag) {
                .hir_var_ref => {
                    const lid = self.mapHirLocal(node.data.lhs);
                    if (!lid.isNone()) {
                        var fl = self.body.locals.items[lid.asInt()].flags();
                        fl.is_address_taken = true;
                        self.body.locals.items[lid.asInt()].setFlags(fl);
                    }
                    return;
                },
                .hir_field_proj, .hir_index_proj, .hir_soa_field_ptr, .hir_bitfield_read => {
                    cur = HirIndex.fromInt(node.data.lhs);
                },
                .hir_block => {
                    cur = HirIndex.fromInt(node.data.rhs);
                },
                .hir_unary_op => {
                    const uop: hir.HirUnaryOp = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))));
                    if (uop == .deref) return; // Dereference writes to pointee, not pointer slot itself.
                    cur = HirIndex.fromInt(node.data.rhs);
                },
                else => return,
            }
        }
    }

    /// Maps a `HirStore` local slot index into a `MirBody` `LocalId`.
    fn mapHirLocal(self: *const MirLowerer, hir_local_id: u32) LocalId {
        if (self.hir_local_remap.get(hir_local_id)) |mapped| return mapped;
        if (hir_local_id >= self.base_hir_local and
            hir_local_id < self.base_hir_local + self.root_local_len)
        {
            return LocalId.fromInt(hir_local_id - self.base_hir_local);
        }
        return .none;
    }

    /// Appends a synthetic `LocalDecl` to `self.body.locals` and `self.local_var_types`.
    fn allocTempLocal(
        self: *MirLowerer,
        val_ty: TypeId,
        origin_token: TokenIndex,
        is_address_taken: bool,
        is_local_closure: bool,
    ) !LocalId {
        const raw_id: u32 = @intCast(self.body.locals.items.len);
        try self.body.locals.append(
            self.body.allocator,
            LocalDecl.init(
                .empty,
                val_ty,
                origin_token,
                0,
                .let_mode,
                .{
                    .is_mut = true,
                    .is_synthetic_temp = true,
                    .is_address_taken = is_address_taken,
                    .is_local_closure = is_local_closure,
                },
            ),
        );
        try self.body.local_scope_depths.append(
            self.body.allocator,
            @intCast(@min(@max(self.scope_depth, 1), std.math.maxInt(u16))),
        );
        try self.local_var_types.append(self.allocator, val_ty);
        self.ssa.var_types = self.local_var_types.items;
        return LocalId.fromInt(raw_id);
    }

    /// Interns/appends a `MirPlace` `(base_local, projs)` enforcing `MAX_MIR_PROJECTIONS` & `MAX_PLACE_PROJ_DEPTH`.
    fn makePlace(self: *MirLowerer, base_local: LocalId, projs: []const MirProjection) !PlaceId {
        if (base_local == .return_slot and projs.len == 0 and self.body.places.items.len > 0) {
            return .return_place;
        }
        if (projs.len == 0) {
            for (self.body.places.items, 0..) |existing, idx| {
                if (existing.base == base_local.asInt() and existing.proj_len == 0) {
                    return PlaceId.fromInt(@intCast(idx));
                }
            }
        }
        if (projs.len > MAX_PLACE_PROJ_DEPTH) {
            try self.ssa.reportResourceOverflow("MIR place projection chain exceeded `MAX_PLACE_PROJ_DEPTH` (255)");
            return PlaceId.fromInt(0);
        }
        if (self.body.projections.items.len + projs.len > MAX_MIR_PROJECTIONS) {
            try self.ssa.reportResourceOverflow("MIR projection pool exceeded `MAX_MIR_PROJECTIONS` (16,777,215)");
            return PlaceId.fromInt(0);
        }
        const proj_start: u24 = @intCast(self.body.projections.items.len);
        if (projs.len > 0) {
            try self.body.projections.appendSlice(self.body.allocator, projs);
        }
        const place_idx: u32 = @intCast(self.body.places.items.len);
        try self.body.places.append(self.body.allocator, .{
            .base = base_local.asInt(),
            .proj_start = proj_start,
            .proj_len = @intCast(projs.len),
        });
        return PlaceId.fromInt(place_idx);
    }

    /// Appends one or more `MirProjection`s onto an existing `base_place`.
    fn extendPlace(
        self: *MirLowerer,
        base_place: PlaceId,
        extra_projs: []const MirProjection,
    ) !PlaceId {
        if (extra_projs.len == 0) return base_place;
        const existing_place = self.body.places.items[base_place.asInt()];
        const existing_len: usize = existing_place.proj_len;
        if (existing_len + extra_projs.len > MAX_PLACE_PROJ_DEPTH) {
            try self.ssa.reportResourceOverflow("MIR place projection chain exceeded `MAX_PLACE_PROJ_DEPTH` (255)");
            return base_place;
        }
        var combined: [256]MirProjection = undefined;
        const old_slice = self.body.getPlaceProjections(base_place);
        @memcpy(combined[0..existing_len], old_slice);
        @memcpy(combined[existing_len .. existing_len + extra_projs.len], extra_projs);
        return self.makePlace(
            LocalId.fromInt(existing_place.base),
            combined[0 .. existing_len + extra_projs.len],
        );
    }

    // -------------- Ghost Instructions & CFG Helpers --------------

    /// Emits a `ghost_access_*` open instruction and returns its token `MirValueId`.
    fn emitGhostOpen(
        self: *MirLowerer,
        op: MirOp,
        place_id: PlaceId,
        borrow_kind: GhostBorrowKind,
        tok: TokenIndex,
    ) !MirValueId {
        return self.ssa.emitInst(self.cur_bb, .{
            .op = op,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = place_id.asInt(), .rhs = @backingInt(borrow_kind) },
        }, tok);
    }

    /// Emits `ghost_access_end` closing `open_tok`.
    fn emitGhostEnd(self: *MirLowerer, open_tok: MirValueId, tok: TokenIndex) !void {
        if (open_tok.isNone()) return;
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .ghost_access_end,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = open_tok.asInt(), .rhs = 0 },
        }, tok);
    }

    /// Closes active mid-expression borrows in `[target_borrow_depth .. active_expr_borrows.len)`
    /// in strict reverse (LIFO) order without mutating `active_expr_borrows`.
    fn emitBorrowEndsAboveDepth(
        self: *MirLowerer,
        target_borrow_depth: usize,
        tok: TokenIndex,
    ) anyerror!void {
        var idx = self.active_expr_borrows.items.len;
        while (idx > target_borrow_depth) {
            idx -= 1;
            const closing_tok = self.active_expr_borrows.items[idx];
            try self.emitGhostEnd(closing_tok, tok);
            try self.runDeferredSubscriptCleanupForToken(closing_tok, false);
        }
    }

    /// Pops and emits `ghost_access_end` in LIFO order back to `target_borrow_depth`.
    fn popAndCloseBorrowsTo(self: *MirLowerer, target_borrow_depth: usize, tok: TokenIndex) anyerror!void {
        while (self.active_expr_borrows.items.len > target_borrow_depth) {
            const top_tok = self.active_expr_borrows.pop().?;
            try self.emitGhostEnd(top_tok, tok);
            try self.runDeferredSubscriptCleanupForToken(top_tok, true);
        }
    }

    /// Executes any deferred `subscript` `post_yield_stmts` bound to `closed_tok` (`Fix-06B`).
    fn runDeferredSubscriptCleanupForToken(
        self: *MirLowerer,
        closed_tok: MirValueId,
        is_consuming_entry: bool,
    ) anyerror!void {
        if (closed_tok.isNone() or self.deferred_subscript_cleanups.items.len == 0) return;
        var idx = self.deferred_subscript_cleanups.items.len;
        while (idx > 0) {
            idx -= 1;
            if (self.deferred_subscript_cleanups.items[idx].trigger_tok != closed_tok) continue;
            if (is_consuming_entry) {
                var entry = self.deferred_subscript_cleanups.orderedRemove(idx);
                defer entry.deinit(self.allocator);
                try self.executeSubscriptPostYield(&entry);
                if (entry.vacated_window_idx) |win_idx| {
                    if (win_idx < self.body.vacated_windows.items.len and !self.cur_bb.isNone()) {
                        self.body.vacated_windows.items[win_idx].end_block = self.cur_bb;
                    }
                }
            } else {
                const snapshot = self.deferred_subscript_cleanups.items[idx];
                try self.executeSubscriptPostYield(&snapshot);
            }
            return;
        }
    }

    /// Runs `entry.post_yield_stmts` with its captured `subscript` parameter/local remap bindings active.
    fn executeSubscriptPostYield(
        self: *MirLowerer,
        entry: *const DeferredSubscriptCleanup,
    ) anyerror!void {
        const saved_hir_store = self.hir_store;
        const saved_root_local_len = self.root_local_len;
        const active_store = entry.sub_store orelse saved_hir_store;
        if (active_store != saved_hir_store) {
            self.hir_store = active_store;
            self.root_local_len = 0;
        }
        defer {
            self.hir_store = saved_hir_store;
            self.root_local_len = saved_root_local_len;
        }

        var shadows: std.ArrayListUnmanaged(SubscriptRemapShadow) = .empty;
        defer {
            var rev_idx = shadows.items.len;
            while (rev_idx > 0) {
                rev_idx -= 1;
                const shadow = shadows.items[rev_idx];
                if (shadow.prev_local) |prev_local| {
                    self.hir_local_remap.putAssumeCapacity(shadow.hir_slot, prev_local);
                } else {
                    _ = self.hir_local_remap.remove(shadow.hir_slot);
                }
                if (shadow.prev_place) |prev_place| {
                    self.hir_place_remap.putAssumeCapacity(shadow.hir_slot, prev_place);
                } else {
                    _ = self.hir_place_remap.remove(shadow.hir_slot);
                }
            }
            shadows.deinit(self.allocator);
        }

        for (entry.local_bindings.items) |bind_pair| {
            try shadows.append(self.allocator, .{
                .hir_slot = bind_pair.hir_slot,
                .prev_local = self.hir_local_remap.get(bind_pair.hir_slot),
                .prev_place = self.hir_place_remap.get(bind_pair.hir_slot),
            });
            _ = self.hir_place_remap.remove(bind_pair.hir_slot);
            try self.hir_local_remap.put(self.allocator, bind_pair.hir_slot, bind_pair.local_id);
        }
        for (entry.place_bindings.items) |place_pair| {
            try shadows.append(self.allocator, .{
                .hir_slot = place_pair.hir_slot,
                .prev_local = self.hir_local_remap.get(place_pair.hir_slot),
                .prev_place = self.hir_place_remap.get(place_pair.hir_slot),
            });
            _ = self.hir_local_remap.remove(place_pair.hir_slot);
            try self.hir_place_remap.put(self.allocator, place_pair.hir_slot, place_pair.place_id);
        }

        for (entry.post_yield_stmts.items) |post_stmt| {
            if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) break;
            _ = try self.lowerRValue(post_stmt);
        }
    }

    /// Resolves the target lexical scope depth for a `HirStore` local (`ConditionScope` / walrus-aware).
    fn resolveLocalDeclScopeDepth(self: *const MirLowerer, hir_slot: u32) u32 {
        if (hir_slot < self.hir_store.locals.items.len) {
            const h_loc = self.hir_store.locals.items[hir_slot];
            if (h_loc.is_cond_binding and self.active_cond_scope_depth != 0) {
                return self.active_cond_scope_depth;
            }
            if (!h_loc.is_temp and self.enclosing_real_block_depth != 0) {
                return self.enclosing_real_block_depth;
            }
        }
        return self.scope_depth;
    }

    /// Registers `local_id` at `target_depth` for scope-exit `ghost_storage_deinit` without initializing yet.
    fn registerStorageLocalAtDepth(
        self: *MirLowerer,
        local_id: LocalId,
        target_depth: u32,
        tok: TokenIndex,
    ) !void {
        const decl = self.body.locals.items[local_id.asInt()];
        if (decl.flags().is_return_slot or decl.flags().is_arg) return;
        if (self.active_fsm_arm_storage) |arm_list| {
            for (arm_list.items) |existing_lid| {
                if (existing_lid == local_id) return;
            }
            try arm_list.append(self.allocator, local_id);
            return;
        }
        for (self.storage_locals.items) |existing| {
            if (existing.local_id == local_id) return;
        }
        try self.storage_locals.append(self.allocator, .{
            .local_id = local_id,
            .scope_depth = target_depth,
            .loop_depth = self.loop_depth,
            .origin_token = tok,
        });
    }

    /// Registers `local_id` for scope-exit `ghost_storage_deinit` without marking it initialized yet.
    fn registerStorageLocalInCurrentScope(
        self: *MirLowerer,
        local_id: LocalId,
        tok: TokenIndex,
    ) !void {
        try self.registerStorageLocalAtDepth(local_id, self.scope_depth, tok);
    }

    /// Emits `ghost_storage_init` and registers `local_id` at `target_depth` for `ghost_storage_deinit`.
    fn markStorageInitAtDepth(
        self: *MirLowerer,
        local_id: LocalId,
        target_depth: u32,
        tok: TokenIndex,
    ) !void {
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .ghost_storage_init,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = local_id.asInt(), .rhs = 0 },
        }, tok);
        try self.registerStorageLocalAtDepth(local_id, target_depth, tok);
    }

    /// Emits `ghost_storage_init` and registers `local_id` for scope-exit `ghost_storage_deinit`.
    fn markStorageInit(self: *MirLowerer, local_id: LocalId, tok: TokenIndex) !void {
        try self.markStorageInitAtDepth(local_id, self.scope_depth, tok);
    }

    /// Emits `ghost_storage_deinit` in reverse LIFO order for `storage_locals[from_floor .. to_ceil]`.
    fn emitStorageDeinitsInRange(
        self: *MirLowerer,
        from_floor: usize,
        to_ceil: usize,
        tok: TokenIndex,
    ) !void {
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return;
        var s_idx = @min(to_ceil, self.storage_locals.items.len);
        const floor = @min(from_floor, s_idx);
        while (s_idx > floor) {
            s_idx -= 1;
            const sloc = self.storage_locals.items[s_idx];
            _ = try self.ssa.emitInst(self.cur_bb, .{
                .op = .ghost_storage_deinit,
                .flags = .{ .has_side_effects = true, .is_synthetic = true },
                .type_id = .unit_ty,
                .operands = .{ .lhs = sloc.local_id.asInt(), .rhs = 0 },
            }, tok);
        }
    }

    /// Emits an unconditional `br` edge `cur_bb -> target_bb` with optional explicit block args.
    fn emitBr(self: *MirLowerer, target_bb: MirBlockId, explicit_args: []const MirValueId) !void {
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return;
        const edge_id = try self.ssa.addOutgoingEdge(
            self.cur_bb,
            target_bb,
            explicit_args,
            std.math.maxInt(u16),
        );
        self.ssa.setTerminator(self.cur_bb, .{
            .kind = .br,
            .edge_len = 1,
            .edge_start = edge_id.asInt(),
        });
    }

    /// Emits a boolean `cond_br` `cur_bb -> [then_bb, else_bb]`.
    fn emitCondBr(
        self: *MirLowerer,
        cond_val: MirValueId,
        then_bb: MirBlockId,
        else_bb: MirBlockId,
    ) !void {
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return;
        const then_edge = try self.ssa.addOutgoingEdge(self.cur_bb, then_bb, &.{}, std.math.maxInt(u16));
        _ = try self.ssa.addOutgoingEdge(self.cur_bb, else_bb, &.{}, std.math.maxInt(u16));
        self.ssa.setTerminator(self.cur_bb, .{
            .kind = .cond_br,
            .edge_len = 2,
            .cond_or_val = cond_val.asInt(),
            .edge_start = then_edge.asInt(),
        });
    }

    /// Materializes a unit `()` SSA constant in `self.cur_bb`.
    fn emitUnitVal(self: *MirLowerer, tok: TokenIndex) !MirValueId {
        const c_idx = try self.body.appendConst(.unit_val);
        return self.ssa.emitInst(self.cur_bb, .{
            .op = .const_scalar,
            .flags = .{ .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = c_idx, .rhs = 0 },
        }, tok);
    }

    /// Materializes a boolean SSA constant in `self.cur_bb`.
    fn emitBoolVal(self: *MirLowerer, is_true: bool, tok: TokenIndex) !MirValueId {
        const c_idx = try self.body.appendConst(.{ .bool_val = is_true });
        return self.ssa.emitInst(self.cur_bb, .{
            .op = .const_scalar,
            .flags = .{ .is_synthetic = true },
            .type_id = .bool_ty,
            .operands = .{ .lhs = c_idx, .rhs = 0 },
        }, tok);
    }

    // --------- Shared Cold LIFO `defer` / `errdefer` Pads ---------

    /// Executes inline unconditional `defer`s and `ghost_storage_deinit`s down to `min_scope_depth`
    /// without popping the stacks (used by `return`, `break`, and `continue`).
    fn emitInlineNormalCleanupsAbove(
        self: *MirLowerer,
        min_scope_depth: u32,
        tok: TokenIndex,
    ) anyerror!void {
        const saved_cleanup = self.is_lowering_cleanup;
        self.is_lowering_cleanup = true;
        defer self.is_lowering_cleanup = saved_cleanup;

        var c_idx = self.cleanup_stack.items.len;
        while (c_idx > 0) {
            c_idx -= 1;
            const entry = self.cleanup_stack.items[c_idx];
            if (entry.scope_depth <= min_scope_depth) break;
            if (!entry.is_errdefer) {
                _ = try self.lowerRValue(entry.body_hir);
                if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return;
            }
        }

        var s_idx = self.storage_locals.items.len;
        while (s_idx > 0) {
            s_idx -= 1;
            const sloc = self.storage_locals.items[s_idx];
            if (sloc.scope_depth <= min_scope_depth) break;
            _ = try self.ssa.emitInst(self.cur_bb, .{
                .op = .ghost_storage_deinit,
                .flags = .{ .has_side_effects = true, .is_synthetic = true },
                .type_id = .unit_ty,
                .operands = .{ .lhs = sloc.local_id.asInt(), .rhs = 0 },
            }, tok);
        }
    }

    /// Pops scope-exiting `defer`/`errdefer` entries, runs unconditional `defer`s on fallthrough,
    /// seals any shared cold `cached_err_pad`s, and emits `ghost_storage_deinit`s.
    fn exitLexicalScopeCleanups(
        self: *MirLowerer,
        exiting_depth: u32,
        is_fallthrough_live: bool,
        tok: TokenIndex,
    ) anyerror!void {
        while (self.cleanup_stack.items.len > 0 and
            self.cleanup_stack.items[self.cleanup_stack.items.len - 1].scope_depth >= exiting_depth)
        {
            const entry = self.cleanup_stack.pop().?;
            if (!entry.cached_err_pad.isNone()) {
                try self.ssa.sealBlock(entry.cached_err_pad);
            }
            if (is_fallthrough_live and !entry.is_errdefer and
                !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb))
            {
                const saved_cleanup = self.is_lowering_cleanup;
                self.is_lowering_cleanup = true;
                defer self.is_lowering_cleanup = saved_cleanup;
                _ = try self.lowerRValue(entry.body_hir);
            }
        }

        while (self.storage_locals.items.len > 0 and
            self.storage_locals.items[self.storage_locals.items.len - 1].scope_depth >= exiting_depth)
        {
            const sloc = self.storage_locals.pop().?;
            if (is_fallthrough_live and !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                _ = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .ghost_storage_deinit,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = sloc.local_id.asInt(), .rhs = 0 },
                }, tok);
            }
        }
    }

    /// Lazily constructs and returns the shared cold `^err_pad_k(%ret_pkg)` block for `cleanup_stack[idx]`
    /// (`is_cleanup_pad = true`, unsealed until lexical scope exit so multiple `?` sites share it!).
    fn getOrBuildErrCleanupPad(
        self: *MirLowerer,
        idx: usize,
        tok: TokenIndex,
    ) anyerror!MirBlockId {
        if (!self.cleanup_stack.items[idx].cached_err_pad.isNone()) {
            return self.cleanup_stack.items[idx].cached_err_pad;
        }

        const saved_bb = self.cur_bb;
        const saved_borrows_len = self.active_expr_borrows.items.len;
        const saved_storage_len = self.storage_locals.items.len;
        const saved_cleanup = self.is_lowering_cleanup;
        defer {
            self.cur_bb = saved_bb;
            self.active_expr_borrows.items.len = saved_borrows_len;
            self.storage_locals.items.len = saved_storage_len;
            self.is_lowering_cleanup = saved_cleanup;
        }
        self.is_lowering_cleanup = true;

        // Keep `pad_bb` unsealed so subsequent `?` / `return .Err` sites in this scope can add edges:
        const pad_bb = try self.ssa.createBlock(false, true);
        self.cleanup_stack.items[idx].cached_err_pad = pad_bb;
        const ret_pkg_param = try self.ssa.addExplicitBlockParam(pad_bb, self.body.ret_ty, tok, false);

        self.cur_bb = pad_bb;
        const entry = self.cleanup_stack.items[idx];

        // Bind `|err|` capture local when `entry.is_errdefer` has an error capture:
        if (entry.is_errdefer and entry.hir_err_local != NONE_U32) {
            const ret_node = self.pool.getNode(self.pool.unwrapUnderlyingType(self.body.ret_ty));
            const err_ty = if (ret_node.tag == .result_ty) TypeId.fromInt(ret_node.rhs) else TypeId.unit_ty;
            const err_payload = try self.ssa.emitInst(self.cur_bb, .{
                .op = .unary_op,
                .flags = .{ .is_synthetic = true },
                .aux_u16 = @backingInt(UnaryOpKind.ssa_variant_payload),
                .type_id = err_ty,
                .operands = .{ .lhs = ret_pkg_param.asInt(), .rhs = 1 },
            }, tok);

            const mapped_err_local = self.mapHirLocal(entry.hir_err_local);
            if (!mapped_err_local.isNone()) {
                if (self.body.locals.items[mapped_err_local.asInt()].flags().is_address_taken) {
                    const err_place = try self.makePlace(mapped_err_local, &.{});
                    try self.markStorageInit(mapped_err_local, tok);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_store,
                        .flags = .{ .has_side_effects = true, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = err_place.asInt(), .rhs = err_payload.asInt() },
                    }, tok);
                } else {
                    try self.ssa.writeVariable(mapped_err_local.asInt(), self.cur_bb, err_payload);
                }
            }
        }

        // Lower cleanup body inside `pad_bb`:
        _ = try self.lowerRValue(entry.body_hir);

        if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
            // Deinitialize any pad-local `|err|` capture + storage locals in `(prev_floor .. entry.storage_floor]`:
            try self.emitStorageDeinitsInRange(saved_storage_len, self.storage_locals.items.len, tok);
            const prev_floor: usize = if (idx > 0) self.cleanup_stack.items[idx - 1].storage_floor else 0;
            try self.emitStorageDeinitsInRange(prev_floor, entry.storage_floor, tok);
            if (idx > 0) {
                const next_pad = try self.getOrBuildErrCleanupPad(idx - 1, tok);
                const explicit_arg = [1]MirValueId{ret_pkg_param};
                try self.emitBr(next_pad, &explicit_arg);
            } else {
                try self.emitFinalReturnTerminator(ret_pkg_param, tok);
            }
        }

        return pad_bb;
    }

    /// Emits `MirIntrinsicKind.zero_pad` on `dest_place` when `val_ty` carries `@zero_pad` (`DR-20` `D-01`).
    fn emitZeroPadIfRequired(
        self: *MirLowerer,
        dest_place: PlaceId,
        val_ty: TypeId,
        tok: TokenIndex,
    ) !void {
        if (!isZeroPadNominalType(self.pool, self.sym_table, val_ty)) return;
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .intrinsic_op,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .aux_u16 = @backingInt(MirIntrinsicKind.zero_pad),
            .type_id = .unit_ty,
            .operands = .{ .lhs = dest_place.asInt(), .rhs = NONE_U32 },
        }, tok);
    }

    /// Emits `MirIntrinsicKind.bounds_check` immediately prior to dynamic `.index` projection.
    fn emitIndexBoundsCheck(
        self: *MirLowerer,
        peeled_place: PlaceId,
        unwrapped_base: TypeId,
        idx_val: MirValueId,
        is_soa: bool,
        tok: TokenIndex,
    ) !void {
        if (unwrapped_base.isError()) return;
        const base_node = self.pool.getNode(unwrapped_base);
        const is_fixed_array = base_node.tag == .array_ty or base_node.tag == .soa_array_ty;
        const is_concrete_len = is_fixed_array and
            (base_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) == 0;

        const len_val: MirValueId = if (is_concrete_len) blk: {
            const len_const_idx = try self.body.appendConst(.{ .int_val = @as(i128, base_node.rhs) });
            break :blk try self.ssa.emitInst(self.cur_bb, .{
                .op = .const_scalar,
                .flags = .{ .is_synthetic = true },
                .type_id = .usize_ty,
                .operands = .{ .lhs = len_const_idx, .rhs = 0 },
            }, tok);
        } else if (base_node.tag == .soa_vec_ty) blk: {
            const ref_ty = try self.pool.internRef(unwrapped_base, false);
            const vec_addr = try self.ssa.emitInst(self.cur_bb, .{
                .op = .place_addr,
                .flags = .{ .is_synthetic = true },
                .type_id = ref_ty,
                .operands = .{ .lhs = peeled_place.asInt(), .rhs = 0 },
            }, tok);
            const a_start: u32 = @intCast(self.body.extra_args.items.len);
            try self.body.extra_args.append(self.body.allocator, vec_addr.asInt());
            break :blk try self.ssa.emitInst(self.cur_bb, .{
                .op = .intrinsic_op,
                .flags = .{ .is_synthetic = true },
                .aux_u16 = @backingInt(MirIntrinsicKind.soa_vec_len),
                .type_id = .usize_ty,
                .operands = .{ .lhs = a_start, .rhs = 1 },
            }, tok);
        } else blk: {
            const len_proj = [1]MirProjection{.{ .kind = .slice_len, .payload = 0 }};
            if (!self.isValidPlaceExtension(peeled_place, &len_proj)) return;
            const len_place = try self.extendPlace(peeled_place, &len_proj);
            break :blk try self.loadPlaceValue(len_place, .usize_ty, tok, false);
        };

        const container_kind: i128 = if (is_soa) 2 else if (is_fixed_array) 1 else 0;
        const kind_const_idx = try self.body.appendConst(.{ .int_val = container_kind });
        const kind_val = try self.ssa.emitInst(self.cur_bb, .{
            .op = .const_scalar,
            .flags = .{ .is_synthetic = true },
            .type_id = .u8_ty,
            .operands = .{ .lhs = kind_const_idx, .rhs = 0 },
        }, tok);

        const args_start: u32 = @intCast(self.body.extra_args.items.len);
        try self.body.extra_args.appendSlice(
            self.body.allocator,
            &[3]u32{ idx_val.asInt(), len_val.asInt(), kind_val.asInt() },
        );
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .intrinsic_op,
            .flags = .{ .has_side_effects = true, .has_trap_risk = true, .is_synthetic = true },
            .aux_u16 = @backingInt(MirIntrinsicKind.bounds_check),
            .type_id = .unit_ty,
            .operands = .{ .lhs = args_start, .rhs = 3 },
        }, tok);
    }

    /// Stores `ret_val` into `_0` (marking `_0` initialized for `V5`) and sets `.ret` terminator.
    fn emitFinalReturnTerminator(
        self: *MirLowerer,
        ret_val: MirValueId,
        tok: TokenIndex,
    ) !void {
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return;
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .ghost_storage_init,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = LocalId.return_slot.asInt(), .rhs = 0 },
        }, tok);
        try self.emitZeroPadIfRequired(.return_place, self.body.ret_ty, tok);
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .place_store,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = PlaceId.return_place.asInt(), .rhs = ret_val.asInt() },
        }, tok);
        self.ssa.setTerminator(self.cur_bb, .{
            .kind = .ret,
            .cond_or_val = ret_val.asInt(),
        });
    }

    /// Lowers `hir_return` routing through `normal`, `explicit_err`, or `dynamic_fallible` cleanups.
    fn lowerReturnNode(self: *MirLowerer, ret_hir_id: HirIndex) anyerror!void {
        const node = self.hir_store.getNode(ret_hir_id);
        const tok = node.origin_token;
        const val_hir = HirIndex.fromInt(node.data.lhs);
        const err_kind: ReturnErrorKind = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.rhs))));

        const ret_val = if (!val_hir.isNone())
            try self.lowerRValue(val_hir)
        else
            try self.emitUnitVal(tok);
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return;

        // [1] Close all mid-expression active Ghost borrows in strict LIFO order:
        try self.emitBorrowEndsAboveDepth(0, tok);

        var has_any_errdefer = false;
        for (self.cleanup_stack.items) |c_entry| {
            if (c_entry.is_errdefer) {
                has_any_errdefer = true;
                break;
            }
        }

        // [2] Route by `ReturnErrorKind`:
        if (self.cleanup_stack.items.len == 0 or (!has_any_errdefer and err_kind != .explicit_err)) {
            try self.emitInlineNormalCleanupsAbove(0, tok);
            if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                try self.emitFinalReturnTerminator(ret_val, tok);
            }
            return;
        }

        switch (err_kind) {
            .normal => {
                try self.emitInlineNormalCleanupsAbove(0, tok);
                if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                    try self.emitFinalReturnTerminator(ret_val, tok);
                }
            },
            .explicit_err => {
                const top_idx = self.cleanup_stack.items.len - 1;
                try self.emitStorageDeinitsInRange(
                    self.cleanup_stack.items[top_idx].storage_floor,
                    self.storage_locals.items.len,
                    tok,
                );
                const top_pad = try self.getOrBuildErrCleanupPad(top_idx, tok);
                const explicit_arg = [1]MirValueId{ret_val};
                try self.emitBr(top_pad, &explicit_arg);
            },
            .dynamic_fallible => {
                // Inspect runtime discriminant of `Result[T, E]` (Err = 1) or `T?` (None = 0):
                const ret_ty_node = self.pool.getNode(self.pool.unwrapUnderlyingType(self.body.ret_ty));
                const err_tag: i128 = if (ret_ty_node.tag == .optional_ty) 0 else 1;
                const discr_val = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .unary_op,
                    .flags = .{ .is_synthetic = true },
                    .aux_u16 = @backingInt(UnaryOpKind.ssa_discriminant),
                    .type_id = .u32_ty,
                    .operands = .{ .lhs = ret_val.asInt(), .rhs = 0 },
                }, tok);
                const err_tag_const = try self.body.appendConst(.{ .int_val = err_tag });
                const err_tag_val = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .flags = .{ .is_synthetic = true },
                    .type_id = .u32_ty,
                    .operands = .{ .lhs = err_tag_const, .rhs = 0 },
                }, tok);
                const is_err_cond = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .bin_op,
                    .flags = .{ .is_synthetic = true },
                    .aux_u16 = @backingInt(BinOpKind.eq),
                    .type_id = .bool_ty,
                    .operands = .{ .lhs = discr_val.asInt(), .rhs = err_tag_val.asInt() },
                }, tok);

                const err_tramp_bb = try self.ssa.createBlock(false, true);
                const ok_exit_bb = try self.ssa.createBlock(false, false);
                try self.emitCondBr(is_err_cond, err_tramp_bb, ok_exit_bb);
                try self.ssa.sealBlock(err_tramp_bb);
                try self.ssa.sealBlock(ok_exit_bb);

                // Error path deinitializes locals above `top_idx.storage_floor`, then jumps to `^err_pad_top`:
                self.cur_bb = err_tramp_bb;
                const top_idx = self.cleanup_stack.items.len - 1;
                try self.emitStorageDeinitsInRange(
                    self.cleanup_stack.items[top_idx].storage_floor,
                    self.storage_locals.items.len,
                    tok,
                );
                const top_pad = try self.getOrBuildErrCleanupPad(top_idx, tok);
                const explicit_arg = [1]MirValueId{ret_val};
                try self.emitBr(top_pad, &explicit_arg);

                // Success path runs unconditional `defer`s only:
                self.cur_bb = ok_exit_bb;
                try self.emitInlineNormalCleanupsAbove(0, tok);
                if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                    try self.emitFinalReturnTerminator(ret_val, tok);
                }
            },
        }
    }

    // --------- Place Lowering & `subscript` Yield Splice ----------

    /// Returns `true` if `ty` unwraps to `&T`, `&mut T`, or `*T` / `*mut T`.
    fn isPtrOrRefType(self: *const MirLowerer, ty: TypeId) bool {
        if (ty.isError()) return false;
        const unwrapped = self.pool.unwrapUnderlyingType(ty);
        const tag = self.pool.getNode(unwrapped).tag;
        return tag == .ref_ty or tag == .mut_ref_ty or tag == .raw_ptr_ty;
    }

    /// Returns `true` if extending `base_place` with `extra_projs` satisfies `V3` place type consistency.
    fn isValidPlaceExtension(
        self: *const MirLowerer,
        base_place: PlaceId,
        extra_projs: []const MirProjection,
    ) bool {
        if (base_place.asInt() >= self.body.places.items.len) return false;
        const existing_place = self.body.places.items[base_place.asInt()];
        const existing_len: usize = existing_place.proj_len;
        if (existing_len + extra_projs.len > MAX_PLACE_PROJ_DEPTH) return false;
        var combined: [256]MirProjection = undefined;
        const old_slice = self.body.getPlaceProjections(base_place);
        @memcpy(combined[0..existing_len], old_slice);
        @memcpy(combined[existing_len .. existing_len + extra_projs.len], extra_projs);
        return isValidProjectionChain(
            self.body,
            existing_place.base,
            combined[0 .. existing_len + extra_projs.len],
            self.pool,
            self.sym_table,
        );
    }

    /// Result of peeling auto-deref reference/pointer layers off a base `PlaceId`.
    const PeeledPlace = struct {
        place_id: PlaceId,
        pointee_ty: TypeId,
    };

    /// Extends `base_place` with `.deref` steps while `running_ty` is a reference or raw pointer.
    fn peelAutoDerefPlace(
        self: *MirLowerer,
        base_place: PlaceId,
        initial_ty: TypeId,
    ) !PeeledPlace {
        var cur_place = base_place;
        var cur_ty = self.pool.unwrapUnderlyingType(initial_ty);
        var depth: usize = 0;
        while (!cur_ty.isError() and depth < 16) : (depth += 1) {
            const node = self.pool.getNode(cur_ty);
            if (self.pool.isOutRef(cur_ty) and cur_place.asInt() < self.body.places.items.len) {
                const place_rec = self.body.places.items[cur_place.asInt()];
                if (place_rec.proj_len == 0 and place_rec.base < self.body.locals.items.len and
                    self.body.locals.items[place_rec.base].mode() == .set_mode)
                {
                    cur_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                    continue;
                }
            }
            const deref_proj = [1]MirProjection{.{ .kind = .deref, .payload = 0 }};
            if ((node.tag == .ref_ty or node.tag == .mut_ref_ty or node.tag == .raw_ptr_ty) and
                self.isValidPlaceExtension(cur_place, &deref_proj))
            {
                cur_place = try self.extendPlace(cur_place, &deref_proj);
                cur_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            } else {
                break;
            }
        }
        return .{ .place_id = cur_place, .pointee_ty = cur_ty };
    }

    /// Returns `true` if `node` is a synthetic destructuring-`let` `hir_match` statement.
    fn isDestructuringLetMatch(self: *const MirLowerer, node: hir.HirNode) bool {
        if (node.tag != .hir_match or !node.flags.is_synthetic or node.type_id != .unit_ty) return false;
        if (node.data.rhs + 1 >= self.hir_store.extra_data.items.len) return false;
        const arm_start = self.hir_store.extra_data.items[node.data.rhs];
        const arm_len = self.hir_store.extra_data.items[node.data.rhs + 1];
        if (arm_len == 0 or arm_len > 2 or arm_start + arm_len > self.hir_store.match_arms.items.len) {
            return false;
        }
        const arms = self.hir_store.match_arms.items[arm_start .. arm_start + arm_len];
        if (self.hir_store.getNode(arms[0].body_hir).tag != .hir_const_val) return false;
        return arm_len == 1 or self.hir_store.getNode(arms[1].body_hir).type_id == .never_ty;
    }

    /// Returns `true` when borrows opened during `stmt_node` must survive until block exit.
    fn isKeepingStmtBorrows(self: *const MirLowerer, stmt_node: hir.HirNode) bool {
        if (stmt_node.tag == .hir_local_decl) {
            const lid = self.mapHirLocal(stmt_node.data.lhs);
            if (!lid.isNone()) {
                const decl = self.body.locals.items[lid.asInt()];
                return decl.flags().is_local_closure or self.hasTypeRegions(decl.type_id);
            }
            return self.hasTypeRegions(stmt_node.type_id);
        }
        if (stmt_node.tag == .hir_block and stmt_node.flags.is_synthetic) {
            for (self.hir_store.getLenPrefixedExtra(stmt_node.data.lhs)) |raw_inner| {
                const inner_node = self.hir_store.getNode(HirIndex.fromInt(raw_inner));
                if (inner_node.tag == .hir_local_decl and
                    inner_node.data.lhs < self.hir_store.locals.items.len and
                    !self.hir_store.locals.items[inner_node.data.lhs].is_temp and
                    self.isKeepingStmtBorrows(inner_node))
                {
                    return true;
                }
            }
        }
        return self.isDestructuringLetMatch(stmt_node);
    }

    /// Lowers `expr_hir` as a mutable target `PlaceId` (`is_mut_place_context = true`).
    fn lowerMutPlace(self: *MirLowerer, expr_hir: HirIndex) anyerror!PlaceId {
        const saved_mut = self.is_mut_place_context;
        self.is_mut_place_context = true;
        defer self.is_mut_place_context = saved_mut;
        return self.lowerPlace(expr_hir);
    }

    /// Synthesizes an initialized poison/fallback `PlaceId` when lowering invalid/error-typed projections.
    fn allocErrorFallbackPlace(self: *MirLowerer, fallback_ty: TypeId, tok: TokenIndex) !PlaceId {
        const safe_ty = if (fallback_ty.isNone()) .err_ty else fallback_ty;
        const tmp_lid = try self.allocTempLocal(safe_ty, tok, true, false);
        try self.markStorageInit(tmp_lid, tok);
        return self.makePlace(tmp_lid, &.{});
    }

    /// Returns the `SymbolRecord` when `node` is a `.hir_global_ref` targeting an `extern static` item.
    fn resolveExternStaticGlobalRef(
        self: *const MirLowerer,
        node: HirNode,
    ) ?*const symbol_resolver.SymbolRecord {
        if (node.tag != .hir_global_ref) return null;
        const sym_idx = SymbolIndex.fromInt(node.data.rhs);
        if (sym_idx.isNone() or sym_idx.asInt() >= self.sym_table.symbols.items.len) return null;
        const sym_rec = self.sym_table.getSymbol(sym_idx);
        return if (sym_rec.kind == .extern_static_sym) sym_rec else null;
    }

    /// Returns `true` when `node` is an immutable `.rodata`-backed `.hir_global_ref` targeting a `.const_sym`.
    fn isConstSymGlobalRef(self: *const MirLowerer, node: HirNode) bool {
        if (node.tag != .hir_global_ref or node.flags.category != .place_imm) return false;
        const sym_idx = SymbolIndex.fromInt(node.data.rhs);
        if (sym_idx.isNone() or sym_idx.asInt() >= self.sym_table.symbols.items.len) return false;
        return self.sym_table.getSymbol(sym_idx).kind == .const_sym;
    }

    /// Lowers an addressable `HIR` expression into a `PlaceId` (`DR-13` §3.2).
    fn lowerPlace(self: *MirLowerer, expr_hir: HirIndex) anyerror!PlaceId {
        if (expr_hir.isNone() or expr_hir.asInt() >= self.hir_store.nodes.len) {
            return self.allocErrorFallbackPlace(.err_ty, .none);
        }
        const node = self.hir_store.getNode(expr_hir);
        const tok = node.origin_token;

        switch (node.tag) {
            .hir_global_ref => {
                if (self.resolveExternStaticGlobalRef(node)) |sym_rec| {
                    const raw_ptr_ty = try self.pool.internRawPtr(node.type_id, sym_rec.flags.is_mut);
                    const addr_val = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .fn_addr,
                        .flags = .{ .is_synthetic = true, .is_unsafe = node.flags.is_unsafe },
                        .type_id = raw_ptr_ty,
                        .operands = .{ .lhs = node.data.lhs, .rhs = node.data.rhs },
                    }, tok);
                    const ptr_slot = try self.allocTempLocal(raw_ptr_ty, tok, true, false);
                    const ptr_place = try self.makePlace(ptr_slot, &.{});
                    try self.markStorageInit(ptr_slot, tok);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_store,
                        .flags = .{ .has_side_effects = true, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = ptr_place.asInt(), .rhs = addr_val.asInt() },
                    }, tok);
                    const deref_proj = [1]MirProjection{.{ .kind = .deref, .payload = 0 }};
                    if (!self.isValidPlaceExtension(ptr_place, &deref_proj)) {
                        return self.allocErrorFallbackPlace(node.type_id, tok);
                    }
                    return self.extendPlace(ptr_place, &deref_proj);
                } else if (self.isConstSymGlobalRef(node)) {
                    const ref_ty = try self.pool.internRef(node.type_id, false);
                    const addr_val = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .fn_addr,
                        .flags = .{ .is_synthetic = true },
                        .type_id = ref_ty,
                        .operands = .{ .lhs = node.data.lhs, .rhs = node.data.rhs },
                    }, tok);
                    const ptr_slot = try self.allocTempLocal(ref_ty, tok, true, false);
                    const ptr_place = try self.makePlace(ptr_slot, &.{});
                    try self.markStorageInit(ptr_slot, tok);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_store,
                        .flags = .{ .has_side_effects = true, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = ptr_place.asInt(), .rhs = addr_val.asInt() },
                    }, tok);
                    const deref_proj = [1]MirProjection{.{ .kind = .deref, .payload = 0 }};
                    if (!self.isValidPlaceExtension(ptr_place, &deref_proj)) {
                        return self.allocErrorFallbackPlace(node.type_id, tok);
                    }
                    return self.extendPlace(ptr_place, &deref_proj);
                }
            },
            .hir_block => {
                const stmts = self.hir_store.getLenPrefixedExtra(node.data.lhs);
                const saved_mut = self.is_mut_place_context;
                self.is_mut_place_context = false;
                for (stmts) |raw_stmt| {
                    if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) break;
                    const stmt_borrow_base = self.active_expr_borrows.items.len;
                    const stmt_hir = HirIndex.fromInt(raw_stmt);
                    const stmt_node = self.hir_store.getNode(stmt_hir);
                    _ = try self.lowerRValue(stmt_hir);
                    if (!self.isKeepingStmtBorrows(stmt_node) and
                        !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb))
                    {
                        try self.popAndCloseBorrowsTo(stmt_borrow_base, stmt_node.origin_token);
                    }
                }
                self.is_mut_place_context = saved_mut;
                return self.lowerPlace(HirIndex.fromInt(node.data.rhs));
            },
            .hir_var_ref => {
                if (self.hir_place_remap.get(node.data.lhs)) |aliased_place| {
                    return aliased_place;
                }
                const lid = self.mapHirLocal(node.data.lhs);
                if (lid.isNone()) {
                    const tmp_lid = try self.allocTempLocal(node.type_id, tok, true, false);
                    try self.markStorageInit(tmp_lid, tok);
                    return self.makePlace(tmp_lid, &.{});
                }
                if (!self.body.locals.items[lid.asInt()].flags().is_address_taken) {
                    const ssa_val = try self.ssa.readVariable(lid.asInt(), self.cur_bb);
                    const spill_lid = try self.allocTempLocal(node.type_id, tok, true, false);
                    const spill_place = try self.makePlace(spill_lid, &.{});
                    try self.markStorageInit(spill_lid, tok);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_store,
                        .flags = .{ .has_side_effects = true, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = spill_place.asInt(), .rhs = ssa_val.asInt() },
                    }, tok);
                    return spill_place;
                }
                return self.makePlace(lid, &.{});
            },
            .hir_field_proj => {
                const base_hir = HirIndex.fromInt(node.data.lhs);
                const raw_base = try self.lowerPlace(base_hir);
                const peeled = try self.peelAutoDerefPlace(
                    raw_base,
                    self.hir_store.getNode(base_hir).type_id,
                );
                const unwrapped_base = self.pool.unwrapUnderlyingType(peeled.pointee_ty);
                const base_node = self.pool.getNode(unwrapped_base);
                const peeled_tag = base_node.tag;
                if (node.data.rhs == hir.FIELD_ORDINAL_LEN) {
                    const len_proj = [1]MirProjection{.{ .kind = .slice_len, .payload = 0 }};
                    if ((!unwrapped_base.isError() and unwrapped_base != .str_ty and
                        peeled_tag != .slice_ty and peeled_tag != .soa_slice_ty and
                        peeled_tag != .array_ty and peeled_tag != .soa_array_ty and
                        unionSliceElemType(self.pool, unwrapped_base) == null) or
                        !self.isValidPlaceExtension(peeled.place_id, &len_proj))
                    {
                        return self.allocErrorFallbackPlace(node.type_id, tok);
                    }
                    return self.extendPlace(peeled.place_id, &len_proj);
                }
                if (peeled_tag == .soa_array_ty or peeled_tag == .soa_slice_ty) {
                    const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(base_node.lhs));
                    const soa_proj = [1]MirProjection{.{ .kind = .soa_elem, .payload = node.data.rhs }};
                    if ((!unwrapped_base.isError() and
                        resolveVerifierFieldType(self.pool, self.sym_table, elem_ty, node.data.rhs) == null) or
                        !self.isValidPlaceExtension(peeled.place_id, &soa_proj))
                    {
                        return self.allocErrorFallbackPlace(node.type_id, tok);
                    }
                    return self.extendPlace(peeled.place_id, &soa_proj);
                }
                const field_proj = [1]MirProjection{.{ .kind = .field, .payload = node.data.rhs }};
                if ((!unwrapped_base.isError() and
                    resolveVerifierFieldType(self.pool, self.sym_table, unwrapped_base, node.data.rhs) == null) or
                    !self.isValidPlaceExtension(peeled.place_id, &field_proj))
                {
                    return self.allocErrorFallbackPlace(node.type_id, tok);
                }
                return self.extendPlace(peeled.place_id, &field_proj);
            },
            .hir_index_proj => {
                const base_hir = HirIndex.fromInt(node.data.lhs);
                const idx_hir = HirIndex.fromInt(node.data.rhs);
                const raw_base = try self.lowerPlace(base_hir);
                const base_hir_ty = self.pool.unwrapUnderlyingType(self.hir_store.getNode(base_hir).type_id);
                const peeled: PeeledPlace = if (!base_hir_ty.isError() and self.pool.getNode(base_hir_ty).tag == .raw_ptr_ty)
                    .{ .place_id = raw_base, .pointee_ty = base_hir_ty }
                else
                    try self.peelAutoDerefPlace(
                        raw_base,
                        self.hir_store.getNode(base_hir).type_id,
                    );
                const saved_mut = self.is_mut_place_context;
                self.is_mut_place_context = false;
                const idx_val = try self.lowerRValue(idx_hir);
                self.is_mut_place_context = saved_mut;
                const unwrapped_base = self.pool.unwrapUnderlyingType(peeled.pointee_ty);
                const base_tag = self.pool.getNode(unwrapped_base).tag;
                const idx_proj = [1]MirProjection{.{ .kind = .index, .payload = idx_val.asInt() }};
                if ((!unwrapped_base.isError() and unwrapped_base != .str_ty and
                    base_tag != .array_ty and base_tag != .slice_ty and
                    base_tag != .soa_array_ty and base_tag != .soa_slice_ty and
                    base_tag != .soa_vec_ty and base_tag != .raw_ptr_ty and
                    unionSliceElemType(self.pool, unwrapped_base) == null) or
                    !self.isValidPlaceExtension(peeled.place_id, &idx_proj))
                {
                    return self.allocErrorFallbackPlace(node.type_id, tok);
                }
                if (base_tag != .raw_ptr_ty) {
                    const is_soa_base = base_tag == .soa_array_ty or
                        base_tag == .soa_slice_ty or
                        base_tag == .soa_vec_ty;
                    try self.emitIndexBoundsCheck(peeled.place_id, unwrapped_base, idx_val, is_soa_base, tok);
                }
                return self.extendPlace(peeled.place_id, &idx_proj);
            },
            .hir_soa_field_ptr => {
                const base_hir = HirIndex.fromInt(node.data.lhs);
                const field_ord = self.hir_store.extra_data.items[node.data.rhs];
                const idx_hir = HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs + 1]);
                const raw_base = try self.lowerPlace(base_hir);
                const peeled = try self.peelAutoDerefPlace(
                    raw_base,
                    self.hir_store.getNode(base_hir).type_id,
                );
                const saved_mut = self.is_mut_place_context;
                self.is_mut_place_context = false;
                const idx_val = try self.lowerRValue(idx_hir);
                self.is_mut_place_context = saved_mut;
                const unwrapped_base = self.pool.unwrapUnderlyingType(peeled.pointee_ty);
                const base_node = self.pool.getNode(unwrapped_base);
                const soa_projs = [2]MirProjection{
                    .{ .kind = .soa_elem, .payload = field_ord },
                    .{ .kind = .index, .payload = idx_val.asInt() },
                };
                if (!unwrapped_base.isError()) {
                    if (base_node.tag != .soa_array_ty and
                        base_node.tag != .soa_slice_ty and
                        base_node.tag != .soa_vec_ty)
                    {
                        return self.allocErrorFallbackPlace(node.type_id, tok);
                    }
                    const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(base_node.lhs));
                    if (resolveVerifierFieldType(self.pool, self.sym_table, elem_ty, field_ord) == null) {
                        return self.allocErrorFallbackPlace(node.type_id, tok);
                    }
                }
                if (!self.isValidPlaceExtension(peeled.place_id, &soa_projs)) {
                    return self.allocErrorFallbackPlace(node.type_id, tok);
                }
                try self.emitIndexBoundsCheck(peeled.place_id, unwrapped_base, idx_val, true, tok);
                return self.extendPlace(peeled.place_id, &soa_projs);
            },
            .hir_unary_op => {
                const uop: hir.HirUnaryOp = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))));
                const sub_hir = HirIndex.fromInt(node.data.rhs);
                if (uop == .deref) {
                    const sub_node = self.hir_store.getNode(sub_hir);
                    const unwrapped_sub = self.pool.unwrapUnderlyingType(sub_node.type_id);
                    const sub_tag = self.pool.getNode(unwrapped_sub).tag;
                    const saved_mut = self.is_mut_place_context;
                    self.is_mut_place_context = false;
                    defer self.is_mut_place_context = saved_mut;
                    if (!unwrapped_sub.isError() and sub_tag != .ref_ty and
                        sub_tag != .mut_ref_ty and sub_tag != .raw_ptr_ty)
                    {
                        _ = try self.lowerRValue(sub_hir);
                        return self.allocErrorFallbackPlace(node.type_id, tok);
                    }
                    const deref_proj = [1]MirProjection{.{ .kind = .deref, .payload = 0 }};
                    if (sub_node.flags.category == .place_imm or sub_node.flags.category == .place_mut) {
                        const ptr_place = try self.lowerPlace(sub_hir);
                        if (self.pool.isOutRef(unwrapped_sub) and ptr_place.asInt() < self.body.places.items.len) {
                            const ptr_rec = self.body.places.items[ptr_place.asInt()];
                            if (ptr_rec.proj_len == 0 and ptr_rec.base < self.body.locals.items.len and
                                self.body.locals.items[ptr_rec.base].mode() == .set_mode)
                            {
                                return ptr_place;
                            }
                        }
                        if (!self.isValidPlaceExtension(ptr_place, &deref_proj)) {
                            return self.allocErrorFallbackPlace(node.type_id, tok);
                        }
                        return self.extendPlace(ptr_place, &deref_proj);
                    }
                    const ptr_val = try self.lowerRValue(sub_hir);
                    const ptr_slot = try self.allocTempLocal(sub_node.type_id, tok, true, false);
                    const ptr_place = try self.makePlace(ptr_slot, &.{});
                    try self.markStorageInit(ptr_slot, tok);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_store,
                        .flags = .{ .has_side_effects = true, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = ptr_place.asInt(), .rhs = ptr_val.asInt() },
                    }, tok);
                    if (!self.isValidPlaceExtension(ptr_place, &deref_proj)) {
                        return self.allocErrorFallbackPlace(node.type_id, tok);
                    }
                    return self.extendPlace(ptr_place, &deref_proj);
                }
            },
            .hir_subscript_call => {
                const is_mut_access = self.is_mut_place_context;
                var spliced = try self.spliceSubscriptCall(
                    expr_hir,
                    if (is_mut_access) .inout_mode else .let_mode,
                    !is_mut_access,
                );
                errdefer spliced.deinit(self.allocator);
                for (spliced.arg_ghost_tokens.items) |arg_tok| {
                    try self.active_expr_borrows.append(self.allocator, arg_tok);
                }
                spliced.arg_ghost_tokens.deinit(self.allocator);

                var cleanup_trigger = spliced.yield_ghost_tok;
                if (!spliced.yield_ghost_tok.isNone()) {
                    try self.active_expr_borrows.append(self.allocator, spliced.yield_ghost_tok);
                    spliced.yield_ghost_tok = .none;
                } else if (spliced.post_yield_stmts.items.len > 0 or spliced.vacated_window_idx != null) {
                    const anchor_lid = try self.allocTempLocal(.unit_ty, tok, true, false);
                    try self.markStorageInit(anchor_lid, tok);
                    const anchor_place = try self.makePlace(anchor_lid, &.{});
                    cleanup_trigger = try self.emitGhostOpen(
                        .ghost_access_let,
                        anchor_place,
                        .scoped_projection,
                        tok,
                    );
                    try self.active_expr_borrows.append(self.allocator, cleanup_trigger);
                }

                if (spliced.vacated_window_idx) |win_idx| {
                    if (win_idx < self.body.vacated_windows.items.len and !cleanup_trigger.isNone()) {
                        self.body.vacated_windows.items[win_idx].access_token = cleanup_trigger;
                    }
                }

                if ((spliced.post_yield_stmts.items.len > 0 or spliced.vacated_window_idx != null) and
                    !cleanup_trigger.isNone())
                {
                    try self.deferred_subscript_cleanups.append(self.allocator, .{
                        .trigger_tok = cleanup_trigger,
                        .sub_store = spliced.sub_store,
                        .post_yield_stmts = spliced.post_yield_stmts,
                        .local_bindings = spliced.local_bindings,
                        .place_bindings = spliced.place_bindings,
                        .vacated_window_idx = spliced.vacated_window_idx,
                    });
                } else {
                    spliced.post_yield_stmts.deinit(self.allocator);
                    spliced.local_bindings.deinit(self.allocator);
                    spliced.place_bindings.deinit(self.allocator);
                }
                return spliced.place_id;
            },
            else => {},
        }

        // Materialize arbitrary RValue into an addressable temporary slot:
        const saved_mut = self.is_mut_place_context;
        self.is_mut_place_context = false;
        const rval = try self.lowerRValue(expr_hir);
        self.is_mut_place_context = saved_mut;
        const temp_lid = try self.allocTempLocal(node.type_id, tok, true, false);
        const temp_place = try self.makePlace(temp_lid, &.{});
        try self.markStorageInit(temp_lid, tok);
        try self.emitZeroPadIfRequired(temp_place, node.type_id, tok);
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .place_store,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = temp_place.asInt(), .rhs = rval.asInt() },
        }, tok);
        return temp_place;
    }

    /// Finds the owning `HirStore` and `HirFnMeta` index of a `subscript` callee (`null` if unresolved).
    fn findSubscriptFnMeta(
        self: *const MirLowerer,
        callee_hir: HirIndex,
        is_inout_needed: bool,
    ) ?ResolvedSubscriptMeta {
        if (callee_hir.isNone() or callee_hir.asInt() >= self.hir_store.nodes.len) return null;
        const callee_node = self.hir_store.getNode(callee_hir);
        if (callee_node.tag != .hir_global_ref) return null;
        const target_def = DefId.fromInt(callee_node.data.lhs);
        const target_sym = SymbolIndex.fromInt(callee_node.data.rhs);

        var fallback: ?ResolvedSubscriptMeta = null;
        for (self.hir_store.functions.items, 0..) |fn_meta, idx| {
            if (!fn_meta.is_subscript or fn_meta.body_hir.isNone()) continue;
            if ((!target_sym.isNone() and fn_meta.symbol_index == target_sym) or
                (!target_def.isNone() and fn_meta.def_id == target_def))
            {
                if (fn_meta.is_subscript_inout_arm == is_inout_needed) {
                    return .{ .store = self.hir_store, .fn_meta_idx = idx };
                }
                if (fallback == null) fallback = .{ .store = self.hir_store, .fn_meta_idx = idx };
            }
        }
        for (self.extra_hir_stores) |ext_store| {
            if (ext_store == self.hir_store) continue;
            for (ext_store.functions.items, 0..) |fn_meta, idx| {
                if (!fn_meta.is_subscript or fn_meta.body_hir.isNone()) continue;
                if ((!target_sym.isNone() and fn_meta.symbol_index == target_sym) or
                    (!target_def.isNone() and fn_meta.def_id == target_def))
                {
                    if (fn_meta.is_subscript_inout_arm == is_inout_needed) {
                        return .{ .store = ext_store, .fn_meta_idx = idx };
                    }
                    if (fallback == null) fallback = .{ .store = ext_store, .fn_meta_idx = idx };
                }
            }
        }
        return fallback;
    }

    /// Unifies a `subscript` template type `pattern_ty` against caller `concrete_ty` into `subst`.
    fn unifySubscriptSpliceTypes(
        allocator: std.mem.Allocator,
        pool: *InternPool,
        pattern_ty: TypeId,
        concrete_ty: TypeId,
        subst: *std.AutoHashMapUnmanaged(u32, TypeId),
        depth: u32,
    ) anyerror!void {
        if (depth > 20 or pattern_ty.isError() or concrete_ty.isError() or pattern_ty == concrete_ty) return;
        const p_node = pool.getNode(pattern_ty);
        switch (p_node.tag) {
            .type_param,
            .bind_once_group_var,
            .bind_many_any_var,
            .builtin_group,
            .user_group,
            .trait_ty,
            => {
                if (!subst.contains(pattern_ty.toU32())) {
                    try subst.put(allocator, pattern_ty.toU32(), concrete_ty);
                }
                return;
            },
            else => {},
        }
        const c_unwrapped = pool.unwrapUnderlyingType(concrete_ty);
        if (p_node.tag == .refined_ty) {
            return unifySubscriptSpliceTypes(
                allocator,
                pool,
                TypeId.fromInt(p_node.rhs),
                c_unwrapped,
                subst,
                depth + 1,
            );
        }
        const c_node = pool.getNode(c_unwrapped);
        if (p_node.tag != c_node.tag) return;
        switch (p_node.tag) {
            .ref_ty, .mut_ref_ty, .raw_ptr_ty, .slice_ty, .soa_slice_ty, .soa_vec_ty, .optional_ty => {
                try unifySubscriptSpliceTypes(
                    allocator,
                    pool,
                    TypeId.fromInt(p_node.lhs),
                    TypeId.fromInt(c_node.lhs),
                    subst,
                    depth + 1,
                );
            },
            .array_ty, .soa_array_ty => {
                if ((p_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) != 0 and
                    (c_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) == 0)
                {
                    const const_sym = SymbolId.fromInt(p_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG);
                    const len_key = try pool.internSymbolicArray(.unit_ty, const_sym, false);
                    if (!subst.contains(len_key.toU32())) {
                        const concrete_len_ty = try pool.internArray(.unit_ty, c_node.rhs, false);
                        try subst.put(allocator, len_key.toU32(), concrete_len_ty);
                    }
                }
                try unifySubscriptSpliceTypes(
                    allocator,
                    pool,
                    TypeId.fromInt(p_node.lhs),
                    TypeId.fromInt(c_node.lhs),
                    subst,
                    depth + 1,
                );
            },
            .result_ty => {
                try unifySubscriptSpliceTypes(
                    allocator,
                    pool,
                    TypeId.fromInt(p_node.lhs),
                    TypeId.fromInt(c_node.lhs),
                    subst,
                    depth + 1,
                );
                try unifySubscriptSpliceTypes(
                    allocator,
                    pool,
                    TypeId.fromInt(p_node.rhs),
                    TypeId.fromInt(c_node.rhs),
                    subst,
                    depth + 1,
                );
            },
            .tuple_ty => {
                const p_elems = pool.getTupleElements(pattern_ty);
                const c_elems = pool.getTupleElements(c_unwrapped);
                const n = @min(p_elems.len, c_elems.len);
                for (0..n) |i| {
                    try unifySubscriptSpliceTypes(
                        allocator,
                        pool,
                        TypeId.fromInt(p_elems[i]),
                        TypeId.fromInt(c_elems[i]),
                        subst,
                        depth + 1,
                    );
                }
            },
            .struct_ty, .enum_ty, .union_ty => {
                if (p_node.rhs == c_node.rhs) {
                    const p_args = pool.getGenericTypeArgs(pattern_ty);
                    const c_args = pool.getGenericTypeArgs(c_unwrapped);
                    const n = @min(p_args.len, c_args.len);
                    for (0..n) |i| {
                        try unifySubscriptSpliceTypes(
                            allocator,
                            pool,
                            TypeId.fromInt(p_args[i]),
                            TypeId.fromInt(c_args[i]),
                            subst,
                            depth + 1,
                        );
                    }
                }
            },
            else => {},
        }
    }

    /// Substitutes generic type/const parameters inside `ty` using `subst` during `subscript` splicing.
    fn substSubscriptSpliceType(
        allocator: std.mem.Allocator,
        pool: *InternPool,
        ty: TypeId,
        subst: *const std.AutoHashMapUnmanaged(u32, TypeId),
        depth: u32,
    ) anyerror!TypeId {
        if (depth > 20 or ty.isError() or subst.count() == 0) return ty;
        if (subst.get(ty.toU32())) |mapped| return mapped;
        const node = pool.getNode(ty);
        if (!node.flags.has_type_vars and node.tag != .trait_ty) return ty;
        return switch (node.tag) {
            .ref_ty => try pool.internRef(
                try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1),
                false,
            ),
            .mut_ref_ty => blk: {
                const inner = try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1);
                if (pool.isOutRef(ty)) break :blk try pool.internOutRef(inner);
                break :blk try pool.internRef(inner, true);
            },
            .raw_ptr_ty => try pool.internRawPtr(
                try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1),
                node.rhs != 0,
            ),
            .slice_ty => try pool.internSlice(
                try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1),
                false,
            ),
            .soa_slice_ty => try pool.internSlice(
                try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1),
                true,
            ),
            .array_ty, .soa_array_ty => blk: {
                const inner = try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1);
                const is_soa = (node.tag == .soa_array_ty);
                if ((node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) != 0) {
                    const const_sym = SymbolId.fromInt(node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG);
                    const len_key = try pool.internSymbolicArray(.unit_ty, const_sym, false);
                    if (subst.get(len_key.toU32())) |bound_len_ty| {
                        const bound_node = pool.getNode(bound_len_ty);
                        if (bound_node.tag == .array_ty and (bound_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) == 0) {
                            break :blk try pool.internArray(inner, bound_node.rhs, is_soa);
                        }
                    }
                    break :blk try pool.internSymbolicArray(inner, const_sym, is_soa);
                }
                break :blk try pool.internArray(inner, node.rhs, is_soa);
            },
            .optional_ty => try pool.internOptional(
                try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1),
            ),
            .result_ty => try pool.internResult(
                try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(node.lhs), subst, depth + 1),
                try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(node.rhs), subst, depth + 1),
            ),
            .tuple_ty => blk: {
                const old_elems = pool.getTupleElements(ty);
                const new_elems = try allocator.alloc(TypeId, old_elems.len);
                defer allocator.free(new_elems);
                for (old_elems, 0..) |raw_el, i| {
                    new_elems[i] = try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(raw_el), subst, depth + 1);
                }
                break :blk try pool.internTuple(new_elems);
            },
            .struct_ty, .enum_ty, .union_ty => blk: {
                const raw_args = pool.getGenericTypeArgs(ty);
                if (raw_args.len == 0) break :blk ty;
                const new_args = try allocator.alloc(TypeId, raw_args.len);
                defer allocator.free(new_args);
                for (raw_args, 0..) |raw_a, i| {
                    new_args[i] = try substSubscriptSpliceType(allocator, pool, TypeId.fromInt(raw_a), subst, depth + 1);
                }
                break :blk try pool.internNominalInstantiation(ty, new_args, node.flags.is_copy, node.flags.has_drop);
            },
            else => ty,
        };
    }

    /// Splices a non-recursive `subscript … yield` call inline.
    fn spliceSubscriptCall(
        self: *MirLowerer,
        call_hir: HirIndex,
        access_mode: ParamMode,
        is_emitting_yield_ghost: bool,
    ) anyerror!SplicedSubscriptAccess {
        const saved_mut = self.is_mut_place_context;
        self.is_mut_place_context = false;
        defer self.is_mut_place_context = saved_mut;

        const call_node = self.hir_store.getNode(call_hir);
        const tok = call_node.origin_token;
        const callee_hir = HirIndex.fromInt(call_node.data.lhs);
        const raw_args = self.hir_store.getLenPrefixedExtra(call_node.data.rhs);

        const is_inout_needed = access_mode == .inout_mode or access_mode == .set_mode;
        const resolved_sub = self.findSubscriptFnMeta(callee_hir, is_inout_needed) orelse {
            const fallback_lid = try self.allocTempLocal(call_node.type_id, tok, true, false);
            try self.markStorageInit(fallback_lid, tok);
            return .{ .place_id = try self.makePlace(fallback_lid, &.{}) };
        };
        const sub_store = resolved_sub.store;
        const fn_meta = sub_store.functions.items[resolved_sub.fn_meta_idx];

        // Guard against recursive or over-deep `subscript` splicing:
        if (self.subscript_splice_depth >= self.subscript_splice_stack.len) {
            const fallback_lid = try self.allocTempLocal(call_node.type_id, tok, true, false);
            try self.markStorageInit(fallback_lid, tok);
            return .{ .place_id = try self.makePlace(fallback_lid, &.{}) };
        }
        for (self.subscript_splice_stack[0..self.subscript_splice_depth]) |active| {
            if (active.store == sub_store and active.fn_meta_idx == resolved_sub.fn_meta_idx) {
                const fallback_lid = try self.allocTempLocal(call_node.type_id, tok, true, false);
                try self.markStorageInit(fallback_lid, tok);
                return .{ .place_id = try self.makePlace(fallback_lid, &.{}) };
            }
        }
        self.subscript_splice_stack[self.subscript_splice_depth] = .{
            .store = sub_store,
            .fn_meta_idx = resolved_sub.fn_meta_idx,
        };
        self.subscript_splice_depth += 1;
        defer self.subscript_splice_depth -= 1;

        var result = SplicedSubscriptAccess{ .place_id = .return_place, .sub_store = sub_store };
        errdefer result.deinit(self.allocator);

        const pre_local_len = self.body.locals.items.len;
        const pre_inst_len = self.body.insts.len;
        const pre_calls_len = self.body.calls.items.len;

        var sub_subst: std.AutoHashMapUnmanaged(u32, TypeId) = .empty;
        defer sub_subst.deinit(self.allocator);

        // [1] Bind formal parameters of the `subscript` in left-to-right Hylo order:
        var bound_hir_slots: std.ArrayListUnmanaged(u32) = .empty;
        defer bound_hir_slots.deinit(self.allocator);
        var remap_shadows: std.ArrayListUnmanaged(SubscriptRemapShadow) = .empty;
        defer {
            var rev_idx = remap_shadows.items.len;
            while (rev_idx > 0) {
                rev_idx -= 1;
                const shadow = remap_shadows.items[rev_idx];
                if (shadow.prev_local) |prev_local| {
                    self.hir_local_remap.putAssumeCapacity(shadow.hir_slot, prev_local);
                } else {
                    _ = self.hir_local_remap.remove(shadow.hir_slot);
                }
                if (shadow.prev_place) |prev_place| {
                    self.hir_place_remap.putAssumeCapacity(shadow.hir_slot, prev_place);
                } else {
                    _ = self.hir_place_remap.remove(shadow.hir_slot);
                }
            }
            remap_shadows.deinit(self.allocator);
        }
        var let_place_args: std.ArrayListUnmanaged(PlaceId) = .empty;
        defer let_place_args.deinit(self.allocator);
        const pre_args_borrow_len = self.active_expr_borrows.items.len;

        const bind_count = @min(raw_args.len, fn_meta.param_len);
        for (0..bind_count) |arg_i| {
            const param_hir_slot = fn_meta.param_local_start + @as(u32, @intCast(arg_i));
            const param_decl = sub_store.locals.items[param_hir_slot];
            var arg_hir = HirIndex.fromInt(raw_args[arg_i]);
            if (!arg_hir.isNone() and self.hir_store.getNode(arg_hir).tag == .hir_project_arg) {
                arg_hir = HirIndex.fromInt(self.hir_store.getNode(arg_hir).data.rhs);
            }
            if (!arg_hir.isNone()) {
                try unifySubscriptSpliceTypes(
                    self.allocator,
                    self.pool,
                    param_decl.type_id,
                    self.hir_store.getNode(arg_hir).type_id,
                    &sub_subst,
                    0,
                );
            }
        }
        try unifySubscriptSpliceTypes(
            self.allocator,
            self.pool,
            fn_meta.ret_ty,
            call_node.type_id,
            &sub_subst,
            0,
        );

        for (0..bind_count) |arg_i| {
            const param_hir_slot = fn_meta.param_local_start + @as(u32, @intCast(arg_i));
            const param_decl = sub_store.locals.items[param_hir_slot];
            const spec_param_ty = try substSubscriptSpliceType(
                self.allocator,
                self.pool,
                param_decl.type_id,
                &sub_subst,
                0,
            );
            var arg_hir = HirIndex.fromInt(raw_args[arg_i]);
            var arg_mode = param_decl.mode;
            if (!arg_hir.isNone() and self.hir_store.getNode(arg_hir).tag == .hir_project_arg) {
                const proj_node = self.hir_store.getNode(arg_hir);
                arg_mode = @fromBackingInt(@intCast(@as(u2, @truncate(proj_node.data.lhs))));
                arg_hir = HirIndex.fromInt(proj_node.data.rhs);
            }

            const arg_cat = self.hir_store.getNode(arg_hir).flags.category;
            if (arg_mode == .inout_mode or arg_mode == .set_mode or
                (!self.isSsaScalarEligibleType(spec_param_ty) and
                    (arg_cat == .place_imm or arg_cat == .place_mut)))
            {
                const arg_place = if (arg_mode == .inout_mode or arg_mode == .set_mode)
                    try self.lowerMutPlace(arg_hir)
                else
                    try self.lowerPlace(arg_hir);
                try bound_hir_slots.append(self.allocator, param_hir_slot);
                try remap_shadows.append(self.allocator, .{
                    .hir_slot = param_hir_slot,
                    .prev_local = self.hir_local_remap.get(param_hir_slot),
                    .prev_place = self.hir_place_remap.get(param_hir_slot),
                });
                _ = self.hir_local_remap.remove(param_hir_slot);
                try self.hir_place_remap.put(self.allocator, param_hir_slot, arg_place);
                const unwrapped_param_ty = self.pool.unwrapUnderlyingType(spec_param_ty);
                if (arg_mode == .let_mode and
                    (unwrapped_param_ty.isError() or self.pool.getNode(unwrapped_param_ty).tag != .mut_ref_ty))
                {
                    try let_place_args.append(self.allocator, arg_place);
                }
            } else {
                const arg_val = try self.lowerRValue(arg_hir);
                const is_place_needed = !self.isSsaScalarEligibleType(spec_param_ty) or param_decl.is_mut;
                const param_lid = try self.allocTempLocal(spec_param_ty, tok, is_place_needed, false);
                try bound_hir_slots.append(self.allocator, param_hir_slot);
                try remap_shadows.append(self.allocator, .{
                    .hir_slot = param_hir_slot,
                    .prev_local = self.hir_local_remap.get(param_hir_slot),
                    .prev_place = self.hir_place_remap.get(param_hir_slot),
                });
                _ = self.hir_place_remap.remove(param_hir_slot);
                try self.hir_local_remap.put(self.allocator, param_hir_slot, param_lid);
                if (is_place_needed) {
                    const param_place = try self.makePlace(param_lid, &.{});
                    try self.markStorageInit(param_lid, tok);
                    try self.emitZeroPadIfRequired(param_place, spec_param_ty, tok);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_store,
                        .flags = .{ .has_side_effects = true, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = param_place.asInt(), .rhs = arg_val.asInt() },
                    }, tok);
                } else {
                    try self.ssa.writeVariable(param_lid.asInt(), self.cur_bb, arg_val);
                }
            }
        }
        if (self.active_expr_borrows.items.len > pre_args_borrow_len) {
            try result.arg_ghost_tokens.appendSlice(
                self.allocator,
                self.active_expr_borrows.items[pre_args_borrow_len..],
            );
            self.active_expr_borrows.items.len = pre_args_borrow_len;
        }

        const saved_hir_store = self.hir_store;
        const saved_root_local_len = self.root_local_len;
        if (sub_store != saved_hir_store) {
            self.hir_store = sub_store;
            self.root_local_len = 0;
        }
        defer {
            self.hir_store = saved_hir_store;
            self.root_local_len = saved_root_local_len;
        }

        // [2] Pre-allocate any body-local variables declared inside `fn_meta`:
        const body_local_start = fn_meta.param_local_start + fn_meta.param_len;
        const body_local_end = fn_meta.return_local_id + fn_meta.total_local_len;
        var slot = body_local_start;
        while (slot < body_local_end) : (slot += 1) {
            const local_meta = self.hir_store.locals.items[slot];
            const spec_local_ty = try substSubscriptSpliceType(
                self.allocator,
                self.pool,
                local_meta.type_id,
                &sub_subst,
                0,
            );
            const fresh_lid = try self.allocTempLocal(
                spec_local_ty,
                tok,
                !self.isSsaScalarEligibleType(spec_local_ty) or local_meta.is_mut,
                false,
            );
            try bound_hir_slots.append(self.allocator, slot);
            try remap_shadows.append(self.allocator, .{
                .hir_slot = slot,
                .prev_local = self.hir_local_remap.get(slot),
                .prev_place = self.hir_place_remap.get(slot),
            });
            _ = self.hir_place_remap.remove(slot);
            try self.hir_local_remap.put(self.allocator, slot, fresh_lid);
        }

        // [3] Walk `fn_meta.body_hir` up to `hir_yield`, lower yielded place, and capture trailing + `defer` stmts (`Fix-06B`):
        var yielded_place: ?PlaceId = null;
        var open_block = self.cur_bb;
        var subscript_defers: std.ArrayListUnmanaged(HirIndex) = .empty;
        defer subscript_defers.deinit(self.allocator);
        const body_node = self.hir_store.getNode(fn_meta.body_hir);
        if (body_node.tag == .hir_block) {
            const stmts = self.hir_store.getLenPrefixedExtra(body_node.data.lhs);
            for (stmts, 0..) |raw_stmt, stmt_i| {
                const stmt_hir = HirIndex.fromInt(raw_stmt);
                const stmt_node = self.hir_store.getNode(stmt_hir);
                if (stmt_node.tag == .hir_yield) {
                    const yield_target = HirIndex.fromInt(stmt_node.data.lhs);
                    yielded_place = if (access_mode == .inout_mode or access_mode == .set_mode)
                        try self.lowerMutPlace(yield_target)
                    else
                        try self.lowerPlace(yield_target);
                    open_block = self.cur_bb;
                    for (stmts[stmt_i + 1 ..]) |trailing_raw| {
                        const trailing_hir = HirIndex.fromInt(trailing_raw);
                        const trailing_node = self.hir_store.getNode(trailing_hir);
                        if (trailing_node.tag == .hir_defer and (trailing_node.data.lhs & 1) == 0) {
                            try subscript_defers.append(self.allocator, HirIndex.fromInt(trailing_node.data.rhs));
                        } else {
                            try result.post_yield_stmts.append(self.allocator, trailing_hir);
                        }
                    }
                    break;
                }
                if (stmt_node.tag == .hir_defer and (stmt_node.data.lhs & 1) == 0) {
                    try subscript_defers.append(self.allocator, HirIndex.fromInt(stmt_node.data.rhs));
                    continue;
                }
                _ = try self.lowerRValue(stmt_hir);
            }
            if (yielded_place == null and !HirIndex.fromInt(body_node.data.rhs).isNone()) {
                const tail_hir = HirIndex.fromInt(body_node.data.rhs);
                const tail_node = self.hir_store.getNode(tail_hir);
                const yield_target = if (tail_node.tag == .hir_yield)
                    HirIndex.fromInt(tail_node.data.lhs)
                else
                    tail_hir;
                yielded_place = if (access_mode == .inout_mode or access_mode == .set_mode)
                    try self.lowerMutPlace(yield_target)
                else
                    try self.lowerPlace(yield_target);
                open_block = self.cur_bb;
            }
        }
        var def_idx = subscript_defers.items.len;
        while (def_idx > 0) {
            def_idx -= 1;
            try result.post_yield_stmts.append(self.allocator, subscript_defers.items[def_idx]);
        }

        // Specialize spliced generic `subscript` locals, instructions, and nested calls (`T`, `const N`):
        if (sub_subst.count() > 0) {
            for (pre_local_len..self.body.locals.items.len) |loc_i| {
                const next_lty = try substSubscriptSpliceType(
                    self.allocator,
                    self.pool,
                    self.body.locals.items[loc_i].type_id,
                    &sub_subst,
                    0,
                );
                self.body.locals.items[loc_i].type_id = next_lty;
                if (loc_i < self.local_var_types.items.len) {
                    self.local_var_types.items[loc_i] = next_lty;
                }
            }
            for (pre_inst_len..self.body.insts.len) |inst_i| {
                var sp_inst = self.body.insts.get(inst_i);
                sp_inst.type_id = try substSubscriptSpliceType(
                    self.allocator,
                    self.pool,
                    sp_inst.type_id,
                    &sub_subst,
                    0,
                );
                if (sp_inst.op == .fn_addr and sp_inst.operands.rhs < self.sym_table.symbols.items.len) {
                    const ref_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(sp_inst.operands.rhs)).*;
                    if (ref_sym.kind == .const_param_sym) {
                        const len_key = try self.pool.internSymbolicArray(.unit_ty, ref_sym.name, false);
                        if (sub_subst.get(len_key.toU32())) |bound_len_ty| {
                            const bound_node = self.pool.getNode(bound_len_ty);
                            if (bound_node.tag == .array_ty and
                                (bound_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) == 0)
                            {
                                const c_idx = try self.body.appendConst(.{ .int_val = @as(i128, bound_node.rhs) });
                                sp_inst = .{
                                    .op = .const_scalar,
                                    .flags = .{},
                                    .type_id = sp_inst.type_id,
                                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                                };
                            }
                        }
                    }
                } else if (sp_inst.op == .intrinsic_op) {
                    const ikind: MirIntrinsicKind = @fromBackingInt(sp_inst.aux_u16);
                    if (ikind.hasTypeIdInLhs()) {
                        const subst_lhs = try substSubscriptSpliceType(
                            self.allocator,
                            self.pool,
                            TypeId.fromInt(sp_inst.operands.lhs),
                            &sub_subst,
                            0,
                        );
                        sp_inst.operands.lhs = subst_lhs.asInt();
                        if (ikind == .implements) {
                            const subst_rhs = try substSubscriptSpliceType(
                                self.allocator,
                                self.pool,
                                TypeId.fromInt(sp_inst.operands.rhs),
                                &sub_subst,
                                0,
                            );
                            sp_inst.operands.rhs = subst_rhs.asInt();
                        }
                    }
                }
                self.body.insts.set(inst_i, sp_inst);
            }
            for (self.body.calls.items[pre_calls_len..]) |*sp_cs| {
                sp_cs.ret_ty = try substSubscriptSpliceType(
                    self.allocator,
                    self.pool,
                    sp_cs.ret_ty,
                    &sub_subst,
                    0,
                );
                if (sp_cs.type_args_len > 0 and
                    sp_cs.type_args_start + sp_cs.type_args_len <= self.body.extra_args.items.len)
                {
                    for (0..sp_cs.type_args_len) |ta_i| {
                        const idx = sp_cs.type_args_start + ta_i;
                        const subst_ta = try substSubscriptSpliceType(
                            self.allocator,
                            self.pool,
                            TypeId.fromInt(self.body.extra_args.items[idx]),
                            &sub_subst,
                            0,
                        );
                        self.body.extra_args.items[idx] = subst_ta.asInt();
                    }
                }
            }
        }

        result.place_id = yielded_place orelse blk: {
            const fallback_lid = try self.allocTempLocal(call_node.type_id, tok, true, false);
            try self.markStorageInit(fallback_lid, tok);
            break :blk try self.makePlace(fallback_lid, &.{});
        };

        const yielded_base = self.body.places.items[result.place_id.asInt()].base;
        for (let_place_args.items) |let_place| {
            if (access_mode == .let_mode or
                self.body.places.items[let_place.asInt()].base != yielded_base)
            {
                const arg_tok = try self.emitGhostOpen(
                    .ghost_access_let,
                    let_place,
                    .scoped_projection,
                    tok,
                );
                try result.arg_ghost_tokens.append(self.allocator, arg_tok);
            }
        }

        if (result.post_yield_stmts.items.len > 0) {
            for (bound_hir_slots.items) |b_slot| {
                if (self.hir_local_remap.get(b_slot)) |mapped_lid| {
                    try result.local_bindings.append(self.allocator, .{
                        .hir_slot = b_slot,
                        .local_id = mapped_lid,
                    });
                }
                if (self.hir_place_remap.get(b_slot)) |mapped_pid| {
                    try result.place_bindings.append(self.allocator, .{
                        .hir_slot = b_slot,
                        .place_id = mapped_pid,
                    });
                }
            }
        }

        if (is_emitting_yield_ghost) {
            const ghost_op: MirOp = switch (access_mode) {
                .inout_mode => .ghost_access_inout,
                .set_mode => .ghost_access_set,
                .let_mode, .sink_mode => .ghost_access_let,
            };
            result.yield_ghost_tok = try self.emitGhostOpen(
                ghost_op,
                result.place_id,
                .scoped_projection,
                tok,
            );
        }

        // [4] Record `VacatedProjectionWindow` when an `inout` `subscript` yields non-`Copy` or vacates `self` (`Fix-06B`):
        const is_self_inout = fn_meta.is_subscript_inout_arm or (fn_meta.param_len > 0 and
            self.hir_store.locals.items[fn_meta.param_local_start].mode == .inout_mode);
        if ((access_mode == .inout_mode or is_self_inout) and !open_block.isNone()) {
            const is_non_copy = !call_node.type_id.isError() and
                type_system.classifyOwnershipTier(self.pool, self.sym_table, call_node.type_id) != .copy_tier;
            const is_self_vacated = if (fn_meta.param_len > 0) blk: {
                const self_hir_slot = fn_meta.param_local_start;
                if (self.hir_place_remap.get(self_hir_slot)) |self_place| {
                    break :blk self.body.places.items[self_place.asInt()].base != yielded_base;
                }
                break :blk false;
            } else false;
            if (is_non_copy or is_self_vacated) {
                const win_idx = self.body.vacated_windows.items.len;
                try self.body.vacated_windows.append(self.body.allocator, .{
                    .start_block = open_block,
                    .end_block = self.cur_bb,
                    .access_token = result.yield_ghost_tok,
                    .yielded_place = result.place_id,
                    .yielded_ty = call_node.type_id,
                    .site_token = tok,
                });
                result.vacated_window_idx = win_idx;
            }
        }
        return result;
    }

    /// Closes a `SplicedSubscriptAccess` after caller read/write completes (`Fix-06B`).
    fn closeSplicedSubscriptAccess(
        self: *MirLowerer,
        spliced: *SplicedSubscriptAccess,
        tok: TokenIndex,
    ) anyerror!void {
        if (!spliced.yield_ghost_tok.isNone()) {
            try self.emitGhostEnd(spliced.yield_ghost_tok, tok);
            spliced.yield_ghost_tok = .none;
        }
        if (spliced.post_yield_stmts.items.len > 0) {
            const cleanup_view = DeferredSubscriptCleanup{
                .trigger_tok = .none,
                .sub_store = spliced.sub_store,
                .post_yield_stmts = spliced.post_yield_stmts,
                .local_bindings = spliced.local_bindings,
                .place_bindings = spliced.place_bindings,
                .vacated_window_idx = spliced.vacated_window_idx,
            };
            try self.executeSubscriptPostYield(&cleanup_view);
        }
        if (spliced.vacated_window_idx) |win_idx| {
            if (win_idx < self.body.vacated_windows.items.len and !self.cur_bb.isNone()) {
                self.body.vacated_windows.items[win_idx].end_block = self.cur_bb;
            }
        }
        var arg_idx = spliced.arg_ghost_tokens.items.len;
        while (arg_idx > 0) {
            arg_idx -= 1;
            try self.emitGhostEnd(spliced.arg_ghost_tokens.items[arg_idx], tok);
        }
        spliced.deinit(self.allocator);
    }

    // ------ Constant, Expression, Statement & Call Lowering -------

    /// Materializes a `ComptimeValue` (including nested aggregates & variants) into an SSA `MirValueId`.
    fn lowerConstVal(
        self: *MirLowerer,
        const_val: ComptimeValue,
        val_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!MirValueId {
        switch (const_val) {
            .unit_val => return self.emitUnitVal(tok),
            .bool_val => |flag| return self.emitBoolVal(flag, tok),
            .char_val => |cp| {
                const c_idx = try self.body.appendConst(.{ .char_val = cp });
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .type_id = val_ty,
                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                }, tok);
            },
            .int_val => |ival| {
                const c_idx = try self.body.appendConst(.{ .int_val = ival });
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .type_id = val_ty,
                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                }, tok);
            },
            .float_val => |fval| {
                const c_idx = try self.body.appendConst(.{ .float_val = fval });
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .type_id = val_ty,
                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                }, tok);
            },
            .str_val => |sym| {
                const c_idx = try self.body.appendConst(.{ .str_val = sym });
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .type_id = val_ty,
                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                }, tok);
            },
            .bytes_val => |sym| {
                const c_idx = try self.body.appendConst(.{ .bytes_val = sym });
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .type_id = val_ty,
                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                }, tok);
            },
            .aggregate => |agg| {
                const agg_ty = if (!agg.type_id.isError()) agg.type_id else val_ty;
                const unwrapped_ty = self.pool.unwrapUnderlyingType(agg_ty);
                if (unwrapped_ty == .source_loc_ty and agg.elem_len == 4 and
                    agg.elem_start + 4 <= self.hir_store.const_elements.items.len)
                {
                    const file_c = self.hir_store.const_pool.items[self.hir_store.const_elements.items[agg.elem_start]];
                    const fn_c = self.hir_store.const_pool.items[self.hir_store.const_elements.items[agg.elem_start + 1]];
                    const line_c = self.hir_store.const_pool.items[self.hir_store.const_elements.items[agg.elem_start + 2]];
                    const col_c = self.hir_store.const_pool.items[self.hir_store.const_elements.items[agg.elem_start + 3]];
                    const c_idx = try self.body.appendConst(.{
                        .source_loc = .{
                            .file_sym = if (file_c == .str_val) file_c.str_val else .empty,
                            .fn_sym = if (fn_c == .str_val) fn_c.str_val else .empty,
                            .line = if (line_c == .int_val and line_c.int_val >= 0) @intCast(@min(line_c.int_val, std.math.maxInt(u32))) else 0,
                            .col = if (col_c == .int_val and col_c.int_val >= 0) @intCast(@min(col_c.int_val, std.math.maxInt(u32))) else 0,
                        },
                    });
                    return self.ssa.emitInst(self.cur_bb, .{
                        .op = .const_scalar,
                        .type_id = agg_ty,
                        .operands = .{ .lhs = c_idx, .rhs = 0 },
                    }, tok);
                }
                const ty_node = self.pool.getNode(unwrapped_ty);
                const agg_kind: AggregateKind = switch (ty_node.tag) {
                    .tuple_ty => .tuple_agg,
                    .array_ty, .soa_array_ty => .array_elems,
                    else => .struct_agg,
                };

                var elem_vals = try self.allocator.alloc(u32, agg.elem_len);
                defer self.allocator.free(elem_vals);
                for (0..agg.elem_len) |elem_i| {
                    const child_const_idx = self.hir_store.const_elements.items[agg.elem_start + elem_i];
                    const child_const = self.hir_store.const_pool.items[child_const_idx];
                    const child_ty = self.resolveAggregateMemberType(unwrapped_ty, @intCast(elem_i));
                    elem_vals[elem_i] = (try self.lowerConstVal(child_const, child_ty, tok)).asInt();
                }
                const extra_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, elem_vals);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .aggregate_make,
                    .aux_u16 = @backingInt(agg_kind),
                    .type_id = agg_ty,
                    .operands = .{ .lhs = extra_start, .rhs = agg.elem_len },
                }, tok);
            },
            .variant => |var_val| {
                const sum_ty = if (!var_val.type_id.isError()) var_val.type_id else val_ty;
                const extra_start: u32 = @intCast(self.body.extra_args.items.len);
                var elem_len: u32 = 0;
                if (var_val.payload_const_idx != NONE_U32 and
                    var_val.payload_const_idx < self.hir_store.const_pool.items.len)
                {
                    const payload_ty = self.resolveVariantPayloadType(sum_ty, var_val.tag_ordinal);
                    const payload_val = try self.lowerConstVal(
                        self.hir_store.const_pool.items[var_val.payload_const_idx],
                        payload_ty,
                        tok,
                    );
                    try self.body.extra_args.append(self.body.allocator, payload_val.asInt());
                    elem_len = 1;
                }
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .aggregate_make,
                    .aux_u16 = @backingInt(AggregateKind.tagged_variant),
                    .type_id = sum_ty,
                    .operands = .{
                        .lhs = extra_start,
                        .rhs = (var_val.tag_ordinal << 16) | (elem_len & 0xFFFF),
                    },
                }, tok);
            },
            .type_info_mirror => |ti| {
                const c_idx = try self.body.appendConst(.{ .int_val = @as(i128, ti.reflected_ty.toU32()) });
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .type_id = val_ty,
                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                }, tok);
            },
            .field_info_mirror => |fi| {
                const c_idx = try self.body.appendConst(.{ .int_val = @as(i128, fi.field_ordinal) });
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .type_id = val_ty,
                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                }, tok);
            },
            .variant_info_mirror => |vi| {
                const c_idx = try self.body.appendConst(.{ .int_val = @as(i128, vi.variant_ordinal) });
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .type_id = val_ty,
                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                }, tok);
            },
        }
    }

    /// Looks up field or element `TypeId` at `ordinal` inside a struct, tuple, or array `agg_ty`.
    fn resolveAggregateMemberType(self: *const MirLowerer, agg_ty: TypeId, ordinal: u32) TypeId {
        if (agg_ty.isError()) return .unit_ty;
        const unwrapped = self.pool.unwrapUnderlyingType(agg_ty);
        if (unwrapped == .source_loc_ty) {
            return switch (ordinal) {
                0, 1 => .str_ty,
                2, 3 => .u32_ty,
                else => .unit_ty,
            };
        }
        if (unwrapped == .fmt_spec_ty) {
            return switch (ordinal) {
                0 => .u32_ty,
                1, 2 => .u16_ty,
                else => .unit_ty,
            };
        }
        const node = self.pool.getNode(unwrapped);
        switch (node.tag) {
            .array_ty, .slice_ty, .soa_array_ty, .soa_slice_ty, .soa_vec_ty => return TypeId.fromInt(node.lhs),
            .tuple_ty => {
                const elems = self.pool.getTupleElements(unwrapped);
                if (ordinal < elems.len) return TypeId.fromInt(elems[ordinal]);
            },
            .struct_ty, .union_ty => {
                const sym = self.sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                if (!sym.target_scope.isNone()) {
                    const nom_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, unwrapped);
                    var cur_ord: u32 = 0;
                    for (self.sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                        const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .field_sym) continue;
                        if (cur_ord == ordinal) return nom_subst.resolve(mem_sym.type_id);
                        cur_ord += 1;
                    }
                }
            },
            else => {},
        }
        return .unit_ty;
    }

    /// Looks up the payload `TypeId` of variant `tag_ordinal` on `Option`, `Result`, or `enum`.
    fn resolveVariantPayloadType(self: *const MirLowerer, sum_ty: TypeId, tag_ordinal: u32) TypeId {
        if (sum_ty.isError()) return .unit_ty;
        const unwrapped = self.pool.unwrapUnderlyingType(sum_ty);
        const node = self.pool.getNode(unwrapped);
        switch (node.tag) {
            .optional_ty => return if (tag_ordinal == 1) TypeId.fromInt(node.lhs) else .unit_ty,
            .result_ty => return if (tag_ordinal == 0) TypeId.fromInt(node.lhs) else TypeId.fromInt(node.rhs),
            .enum_ty => {
                const sym = self.sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                if (!sym.target_scope.isNone()) {
                    const nom_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, unwrapped);
                    var cur_ord: u32 = 0;
                    for (self.sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                        const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .enum_variant_sym) continue;
                        if (cur_ord == tag_ordinal) return nom_subst.resolve(mem_sym.type_id);
                        cur_ord += 1;
                    }
                }
            },
            else => {},
        }
        return .unit_ty;
    }

    /// Returns `true` if `place_id` projects through an immutable shared reference (`&T`).
    fn isPlaceBehindSharedRef(self: *const MirLowerer, place_id: PlaceId) bool {
        const place = self.body.places.items[place_id.asInt()];
        if (place.base >= self.body.locals.items.len) return false;
        var cur_ty = self.pool.unwrapUnderlyingType(self.body.locals.items[place.base].type_id);
        var active_downcast: ?u32 = null;
        var active_soa_field_ty: ?TypeId = null;

        for (self.body.getPlaceProjections(place_id)) |proj| {
            if (active_soa_field_ty) |soa_field_ty| {
                active_soa_field_ty = null;
                if (proj.kind == .index) {
                    cur_ty = soa_field_ty;
                    continue;
                } else if (proj.kind == .slice_len) {
                    cur_ty = .usize_ty;
                    continue;
                }
                return false;
            }
            if (cur_ty.isError()) return false;
            const ty_node = self.pool.getNode(cur_ty);
            switch (proj.kind) {
                .deref => {
                    active_downcast = null;
                    if (ty_node.tag == .ref_ty) return true;
                    if (ty_node.tag == .mut_ref_ty or ty_node.tag == .raw_ptr_ty) {
                        cur_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                    } else {
                        return false;
                    }
                },
                .downcast => active_downcast = proj.payload,
                .field => {
                    if (active_downcast) |tag_ord| {
                        active_downcast = null;
                        cur_ty = self.pool.unwrapUnderlyingType(self.resolveVariantPayloadType(cur_ty, tag_ord));
                        if (proj.payload > 0) {
                            cur_ty = self.pool.unwrapUnderlyingType(
                                self.resolveAggregateMemberType(cur_ty, proj.payload),
                            );
                        }
                    } else {
                        cur_ty = self.pool.unwrapUnderlyingType(
                            self.resolveAggregateMemberType(cur_ty, proj.payload),
                        );
                    }
                },
                .index => {
                    active_downcast = null;
                    if (cur_ty == .str_ty or ty_node.tag == .slice_ty or
                        (ty_node.tag == .raw_ptr_ty and ty_node.rhs == 0))
                    {
                        return true;
                    }
                    cur_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                },
                .soa_elem => {
                    active_downcast = null;
                    if (ty_node.tag == .soa_slice_ty and ty_node.rhs == 0) return true;
                    active_soa_field_ty = self.pool.unwrapUnderlyingType(
                        self.resolveAggregateMemberType(TypeId.fromInt(ty_node.lhs), proj.payload),
                    );
                },
                .slice_len => {
                    active_downcast = null;
                    cur_ty = .usize_ty;
                },
            }
        }
        return false;
    }

    /// Loads `place_id` as an RValue wrapped in a scoped `ghost_access_let` bracket, optionally moving non-`Copy` places.
    fn loadPlaceValue(
        self: *MirLowerer,
        place_id: PlaceId,
        val_ty: TypeId,
        tok: TokenIndex,
        is_move_allowed: bool,
    ) !MirValueId {
        const open_tok = try self.emitGhostOpen(.ghost_access_let, place_id, .scoped_projection, tok);
        const loaded_val = try self.ssa.emitInst(self.cur_bb, .{
            .op = .place_load,
            .type_id = val_ty,
            .operands = .{ .lhs = place_id.asInt(), .rhs = 0 },
        }, tok);
        try self.emitGhostEnd(open_tok, tok);

        if (is_move_allowed and !val_ty.isError() and
            !self.pool.getFlags(val_ty).is_copy and
            !self.isPlaceBehindSharedRef(place_id))
        {
            _ = try self.ssa.emitInst(self.cur_bb, .{
                .op = .ghost_storage_move,
                .flags = .{ .has_side_effects = true, .is_synthetic = true },
                .type_id = .unit_ty,
                .operands = .{ .lhs = place_id.asInt(), .rhs = 0 },
            }, tok);
        }
        return loaded_val;
    }

    /// Lowers `expr_hir` as a non-moving borrowed RValue (used for `ParamMode.let_mode` call projections).
    fn lowerBorrowedValue(self: *MirLowerer, expr_hir: HirIndex) anyerror!MirValueId {
        if (expr_hir.isNone() or expr_hir.asInt() >= self.hir_store.nodes.len) {
            return self.emitUnitVal(.none);
        }
        const node = self.hir_store.getNode(expr_hir);
        switch (node.tag) {
            .hir_var_ref => {
                if (self.hir_place_remap.get(node.data.lhs)) |aliased| {
                    return self.loadPlaceValue(aliased, node.type_id, node.origin_token, false);
                }
                const lid = self.mapHirLocal(node.data.lhs);
                if (!lid.isNone()) {
                    if (self.body.locals.items[lid.asInt()].flags().is_address_taken) {
                        const place = try self.makePlace(lid, &.{});
                        return self.loadPlaceValue(place, node.type_id, node.origin_token, false);
                    }
                    return self.ssa.readVariable(lid.asInt(), self.cur_bb);
                }
            },
            .hir_field_proj => {
                const base_hir = HirIndex.fromInt(node.data.lhs);
                const base_node = self.hir_store.getNode(base_hir);
                const peeled_base_ty = self.unwrapAllRefsType(base_node.type_id);
                const base_ty_tag = self.pool.getNode(peeled_base_ty).tag;
                const unwrapped_dst = self.pool.unwrapUnderlyingType(node.type_id);
                const is_synthetic_slice_ptr = node.flags.is_synthetic and node.data.rhs == 0 and
                    (peeled_base_ty == .str_ty or base_ty_tag == .slice_ty or
                        unionSliceElemType(self.pool, peeled_base_ty) != null) and
                    !unwrapped_dst.isError() and self.pool.getNode(unwrapped_dst).tag == .raw_ptr_ty;
                if (!is_synthetic_slice_ptr and
                    (base_ty_tag != .soa_slice_ty and base_ty_tag != .soa_array_ty) and
                    (base_node.flags.category != .rvalue or self.isPtrOrRefType(base_node.type_id) or
                        node.data.rhs == hir.FIELD_ORDINAL_LEN))
                {
                    const proj_place = try self.lowerPlace(expr_hir);
                    return self.loadPlaceValue(proj_place, node.type_id, node.origin_token, false);
                }
            },
            .hir_index_proj => {
                if (try self.tryGatherSoaElementRValue(node, false)) |gathered_val| {
                    return gathered_val;
                }
                const elem_place = try self.lowerPlace(expr_hir);
                return self.loadPlaceValue(elem_place, node.type_id, node.origin_token, false);
            },
            .hir_soa_field_ptr => {
                const elem_place = try self.lowerPlace(expr_hir);
                return self.loadPlaceValue(elem_place, node.type_id, node.origin_token, false);
            },
            .hir_global_ref => {
                if (self.resolveExternStaticGlobalRef(node) != null or self.isConstSymGlobalRef(node)) {
                    const ext_place = try self.lowerPlace(expr_hir);
                    return self.loadPlaceValue(ext_place, node.type_id, node.origin_token, false);
                }
            },
            .hir_unary_op => {
                const uop: hir.HirUnaryOp = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))));
                if (uop == .deref) {
                    const deref_place = try self.lowerPlace(expr_hir);
                    return self.loadPlaceValue(deref_place, node.type_id, node.origin_token, false);
                }
            },
            .hir_block => {
                const stmts = self.hir_store.getLenPrefixedExtra(node.data.lhs);
                const tail_hir = HirIndex.fromInt(node.data.rhs);
                const is_preserving_walrus_borrows = node.flags.is_synthetic and self.isKeepingStmtBorrows(node);
                self.scope_depth += 1;
                const entered_depth = self.scope_depth;
                const saved_real_depth = self.enclosing_real_block_depth;
                const saved_cond_depth = self.active_cond_scope_depth;
                if (!node.flags.is_synthetic) {
                    self.enclosing_real_block_depth = entered_depth;
                    self.active_cond_scope_depth = 0;
                }
                defer {
                    self.enclosing_real_block_depth = saved_real_depth;
                    self.active_cond_scope_depth = saved_cond_depth;
                }
                const block_borrow_base = self.active_expr_borrows.items.len;
                for (stmts) |raw_stmt| {
                    if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) break;
                    const stmt_borrow_base = self.active_expr_borrows.items.len;
                    const stmt_hir = HirIndex.fromInt(raw_stmt);
                    const stmt_node = self.hir_store.getNode(stmt_hir);
                    _ = try self.lowerRValue(stmt_hir);
                    if (!self.isKeepingStmtBorrows(stmt_node) and
                        !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb))
                    {
                        try self.popAndCloseBorrowsTo(stmt_borrow_base, stmt_node.origin_token);
                    }
                }
                var result_val: MirValueId = .none;
                if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                    result_val = if (!tail_hir.isNone())
                        try self.lowerBorrowedValue(tail_hir)
                    else
                        try self.emitUnitVal(node.origin_token);
                }
                const is_live = !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb);
                if (!is_preserving_walrus_borrows) {
                    if (is_live) {
                        try self.popAndCloseBorrowsTo(block_borrow_base, node.origin_token);
                    } else {
                        self.active_expr_borrows.items.len = block_borrow_base;
                    }
                }
                try self.exitLexicalScopeCleanups(entered_depth, is_live, node.origin_token);
                self.scope_depth -= 1;
                if (result_val.isNone()) {
                    return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
                }
                return result_val;
            },
            else => {},
        }
        return self.lowerRValue(expr_hir);
    }

    /// If `lhs_hir` is `.hir_index_proj` (or `.hir_block`s wrapping `.hir_index_proj`) on `#soa`, returns its tail `HirIndex`.
    fn findTailSoaIndexProj(self: *const MirLowerer, lhs_hir: HirIndex) ?HirIndex {
        var cur = lhs_hir;
        var depth: usize = 0;
        while (!cur.isNone() and cur.asInt() < self.hir_store.nodes.len and depth < 16) : (depth += 1) {
            const node = self.hir_store.getNode(cur);
            if (node.tag == .hir_index_proj) {
                const base_hir = HirIndex.fromInt(node.data.lhs);
                if (!base_hir.isNone() and base_hir.asInt() < self.hir_store.nodes.len) {
                    const peeled_ty = self.unwrapAllRefsType(self.hir_store.getNode(base_hir).type_id);
                    if (!peeled_ty.isError()) {
                        const btag = self.pool.getNode(peeled_ty).tag;
                        if (btag == .soa_vec_ty or btag == .soa_array_ty or btag == .soa_slice_ty) {
                            return cur;
                        }
                    }
                }
                return null;
            }
            if (node.tag == .hir_block) {
                cur = HirIndex.fromInt(node.data.rhs);
                continue;
            }
            break;
        }
        return null;
    }

    /// Gathers all columnar fields of `soa[idx]` into an AoS struct `MirValueId` when `idx_node` indexes `#soa`.
    fn tryGatherSoaElementRValue(
        self: *MirLowerer,
        idx_node: hir.HirNode,
        is_moving_out: bool,
    ) anyerror!?MirValueId {
        const base_hir = HirIndex.fromInt(idx_node.data.lhs);
        const idx_hir = HirIndex.fromInt(idx_node.data.rhs);
        if (base_hir.isNone() or base_hir.asInt() >= self.hir_store.nodes.len) return null;
        const peeled_base_ty = self.unwrapAllRefsType(self.hir_store.getNode(base_hir).type_id);
        if (peeled_base_ty.isError()) return null;
        const base_ty_node = self.pool.getNode(peeled_base_ty);
        if (base_ty_node.tag != .soa_vec_ty and
            base_ty_node.tag != .soa_array_ty and
            base_ty_node.tag != .soa_slice_ty)
        {
            return null;
        }
        const tok = idx_node.origin_token;
        const raw_base = try self.lowerPlace(base_hir);
        const peeled = try self.peelAutoDerefPlace(raw_base, self.hir_store.getNode(base_hir).type_id);
        const saved_mut = self.is_mut_place_context;
        self.is_mut_place_context = false;
        const idx_val = try self.lowerRValue(idx_hir);
        self.is_mut_place_context = saved_mut;
        try self.emitIndexBoundsCheck(peeled.place_id, peeled_base_ty, idx_val, true, tok);

        const elem_struct_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(base_ty_node.lhs));
        var field_vals: std.ArrayListUnmanaged(u32) = .empty;
        defer field_vals.deinit(self.allocator);
        var f_ord: u32 = 0;
        while (resolveVerifierFieldType(self.pool, self.sym_table, elem_struct_ty, f_ord)) |f_ty| : (f_ord += 1) {
            const soa_projs = [2]MirProjection{
                .{ .kind = .soa_elem, .payload = f_ord },
                .{ .kind = .index, .payload = idx_val.asInt() },
            };
            const f_place = try self.extendPlace(peeled.place_id, &soa_projs);
            const f_val = try self.loadPlaceValue(f_place, f_ty, tok, is_moving_out);
            try field_vals.append(self.allocator, f_val.asInt());
        }
        const elems_start: u32 = @intCast(self.body.extra_args.items.len);
        try self.body.extra_args.appendSlice(self.body.allocator, field_vals.items);
        return try self.ssa.emitInst(self.cur_bb, .{
            .op = .aggregate_make,
            .aux_u16 = @backingInt(AggregateKind.struct_agg),
            .type_id = idx_node.type_id,
            .operands = .{ .lhs = elems_start, .rhs = @intCast(field_vals.items.len) },
        }, tok);
    }

    /// If `lhs_hir` is `.hir_subscript_call` (or `.hir_block`s wrapping `.hir_subscript_call`), returns its tail `HirIndex`.
    fn findTailSubscriptCall(self: *const MirLowerer, lhs_hir: HirIndex) ?HirIndex {
        var cur = lhs_hir;
        var depth: usize = 0;
        while (!cur.isNone() and cur.asInt() < self.hir_store.nodes.len and depth < 16) : (depth += 1) {
            const node = self.hir_store.getNode(cur);
            if (node.tag == .hir_subscript_call) return cur;
            if (node.tag == .hir_block) {
                cur = HirIndex.fromInt(node.data.rhs);
                continue;
            }
            break;
        }
        return null;
    }

    /// Lowers prefix statements of any outer `.hir_block`s wrapping a `.hir_subscript_call` assignment LHS.
    fn lowerSubscriptAssignPrefixBlocks(self: *MirLowerer, lhs_hir: HirIndex) anyerror!void {
        var cur = lhs_hir;
        var depth: usize = 0;
        while (!cur.isNone() and cur.asInt() < self.hir_store.nodes.len and depth < 16) : (depth += 1) {
            const node = self.hir_store.getNode(cur);
            if (node.tag != .hir_block) break;
            for (self.hir_store.getLenPrefixedExtra(node.data.lhs)) |raw_stmt| {
                if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return;
                const stmt_borrow_base = self.active_expr_borrows.items.len;
                const stmt_hir = HirIndex.fromInt(raw_stmt);
                const stmt_node = self.hir_store.getNode(stmt_hir);
                _ = try self.lowerRValue(stmt_hir);
                if (!self.isKeepingStmtBorrows(stmt_node) and
                    !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb))
                {
                    try self.popAndCloseBorrowsTo(stmt_borrow_base, stmt_node.origin_token);
                }
            }
            cur = HirIndex.fromInt(node.data.rhs);
        }
    }

    /// Lowers any `HIR` statement or expression node into an SSA `MirValueId`.
    fn lowerRValue(self: *MirLowerer, expr_hir: HirIndex) anyerror!MirValueId {
        if (expr_hir.isNone() or expr_hir.asInt() >= self.hir_store.nodes.len) {
            return self.emitUnitVal(.none);
        }
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
            const dead_bb = try self.ssa.createBlock(true, false);
            self.cur_bb = dead_bb;
        }

        const node = self.hir_store.getNode(expr_hir);
        const tok = node.origin_token;

        switch (node.tag) {
            .hir_const_val => {
                if (node.data.lhs < self.hir_store.const_pool.items.len) {
                    return self.lowerConstVal(
                        self.hir_store.const_pool.items[node.data.lhs],
                        node.type_id,
                        tok,
                    );
                }
                return self.emitUnitVal(tok);
            },
            .hir_var_ref => {
                if (self.hir_place_remap.get(node.data.lhs)) |aliased| {
                    return self.loadPlaceValue(aliased, node.type_id, tok, true);
                }
                const lid = self.mapHirLocal(node.data.lhs);
                if (lid.isNone()) return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
                if (self.body.locals.items[lid.asInt()].flags().is_address_taken) {
                    const place = try self.makePlace(lid, &.{});
                    return self.loadPlaceValue(place, node.type_id, tok, true);
                }
                return self.ssa.readVariable(lid.asInt(), self.cur_bb);
            },
            .hir_global_ref => {
                if (self.resolveExternStaticGlobalRef(node) != null or self.isConstSymGlobalRef(node)) {
                    const ext_place = try self.lowerPlace(expr_hir);
                    return self.loadPlaceValue(ext_place, node.type_id, tok, true);
                }
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .fn_addr,
                    .type_id = node.type_id,
                    .operands = .{ .lhs = node.data.lhs, .rhs = node.data.rhs },
                }, tok);
            },
            .hir_local_decl => {
                const lid = self.mapHirLocal(node.data.lhs);
                const decl_depth = self.resolveLocalDeclScopeDepth(node.data.lhs);
                if (!lid.isNone() and lid.asInt() < self.body.local_scope_depths.items.len) {
                    self.body.local_scope_depths.items[lid.asInt()] =
                        @intCast(@min(@max(decl_depth, 1), std.math.maxInt(u16)));
                }
                const init_hir = HirIndex.fromInt(node.data.rhs);
                if (!init_hir.isNone()) {
                    if (!lid.isNone() and self.hir_store.getNode(init_hir).tag == .hir_closure) {
                        var fl = self.body.locals.items[lid.asInt()].flags();
                        fl.is_local_closure = self.isClosureMarkedLocal(init_hir);
                        self.body.locals.items[lid.asInt()].setFlags(fl);
                    }
                    const init_val = try self.lowerRValue(init_hir);
                    if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                        return self.emitUnitVal(tok);
                    }
                    if (!lid.isNone()) {
                        if (self.body.locals.items[lid.asInt()].flags().is_address_taken) {
                            const place = try self.makePlace(lid, &.{});
                            try self.markStorageInitAtDepth(lid, decl_depth, tok);
                            try self.emitZeroPadIfRequired(place, self.body.locals.items[lid.asInt()].type_id, tok);
                            _ = try self.ssa.emitInst(self.cur_bb, .{
                                .op = .place_store,
                                .flags = .{ .has_side_effects = true },
                                .type_id = .unit_ty,
                                .operands = .{ .lhs = place.asInt(), .rhs = init_val.asInt() },
                            }, tok);
                        } else {
                            try self.ssa.writeVariable(lid.asInt(), self.cur_bb, init_val);
                        }
                    }
                } else if (!lid.isNone() and self.body.locals.items[lid.asInt()].flags().is_address_taken) {
                    try self.registerStorageLocalAtDepth(lid, decl_depth, tok);
                }
                return self.emitUnitVal(tok);
            },
            .hir_assign => {
                const lhs_hir = HirIndex.fromInt(node.data.lhs);
                const rhs_hir = HirIndex.fromInt(node.data.rhs);
                const lhs_node = self.hir_store.getNode(lhs_hir);

                if (lhs_node.tag == .hir_var_ref and !self.hir_place_remap.contains(lhs_node.data.lhs)) {
                    const lid = self.mapHirLocal(lhs_node.data.lhs);
                    if (!lid.isNone() and !self.body.locals.items[lid.asInt()].flags().is_address_taken) {
                        const rhs_val = try self.lowerRValue(rhs_hir);
                        if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                            try self.ssa.writeVariable(lid.asInt(), self.cur_bb, rhs_val);
                        }
                        self.last_assigned_place = .none;
                        return self.emitUnitVal(tok);
                    }
                }

                if (self.findTailSubscriptCall(lhs_hir)) |sub_call_hir| {
                    const assign_borrow_base = self.active_expr_borrows.items.len;
                    const assign_cleanup_base = self.deferred_subscript_cleanups.items.len;
                    try self.lowerSubscriptAssignPrefixBlocks(lhs_hir);
                    if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                        self.active_expr_borrows.items.len = assign_borrow_base;
                        return self.emitUnitVal(tok);
                    }
                    var spliced = try self.spliceSubscriptCall(sub_call_hir, .inout_mode, true);
                    errdefer spliced.deinit(self.allocator);
                    for (spliced.arg_ghost_tokens.items) |arg_tok| {
                        try self.active_expr_borrows.append(self.allocator, arg_tok);
                    }
                    spliced.arg_ghost_tokens.deinit(self.allocator);

                    var cleanup_trigger = spliced.yield_ghost_tok;
                    if (!spliced.yield_ghost_tok.isNone()) {
                        try self.active_expr_borrows.append(self.allocator, spliced.yield_ghost_tok);
                        spliced.yield_ghost_tok = .none;
                    } else if (spliced.post_yield_stmts.items.len > 0 or spliced.vacated_window_idx != null) {
                        const anchor_lid = try self.allocTempLocal(.unit_ty, tok, true, false);
                        try self.markStorageInit(anchor_lid, tok);
                        const anchor_place = try self.makePlace(anchor_lid, &.{});
                        cleanup_trigger = try self.emitGhostOpen(
                            .ghost_access_let,
                            anchor_place,
                            .scoped_projection,
                            tok,
                        );
                        try self.active_expr_borrows.append(self.allocator, cleanup_trigger);
                    }
                    if (spliced.vacated_window_idx) |win_idx| {
                        if (win_idx < self.body.vacated_windows.items.len and !cleanup_trigger.isNone()) {
                            self.body.vacated_windows.items[win_idx].access_token = cleanup_trigger;
                        }
                    }
                    if ((spliced.post_yield_stmts.items.len > 0 or spliced.vacated_window_idx != null) and
                        !cleanup_trigger.isNone())
                    {
                        try self.deferred_subscript_cleanups.append(self.allocator, .{
                            .trigger_tok = cleanup_trigger,
                            .sub_store = spliced.sub_store,
                            .post_yield_stmts = spliced.post_yield_stmts,
                            .local_bindings = spliced.local_bindings,
                            .place_bindings = spliced.place_bindings,
                            .vacated_window_idx = spliced.vacated_window_idx,
                        });
                        spliced.post_yield_stmts = .empty;
                        spliced.local_bindings = .empty;
                        spliced.place_bindings = .empty;
                    } else {
                        spliced.post_yield_stmts.deinit(self.allocator);
                        spliced.local_bindings.deinit(self.allocator);
                        spliced.place_bindings.deinit(self.allocator);
                    }

                    const yielded_place_id = spliced.place_id;
                    const rhs_val = try self.lowerRValue(rhs_hir);
                    if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                        while (self.deferred_subscript_cleanups.items.len > assign_cleanup_base) {
                            var dropped = self.deferred_subscript_cleanups.pop().?;
                            dropped.deinit(self.allocator);
                        }
                        self.active_expr_borrows.items.len = assign_borrow_base;
                        return self.emitUnitVal(tok);
                    }
                    try self.emitZeroPadIfRequired(yielded_place_id, lhs_node.type_id, tok);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_store,
                        .flags = .{ .has_side_effects = true },
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = yielded_place_id.asInt(), .rhs = rhs_val.asInt() },
                    }, tok);
                    self.last_assigned_place = yielded_place_id;
                    try self.popAndCloseBorrowsTo(assign_borrow_base, tok);
                    return self.emitUnitVal(tok);
                }

                if (self.findTailSoaIndexProj(lhs_hir)) |soa_idx_hir| {
                    const rhs_val = try self.lowerRValue(rhs_hir);
                    if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                        return self.emitUnitVal(tok);
                    }
                    const assign_borrow_base = self.active_expr_borrows.items.len;
                    try self.lowerSubscriptAssignPrefixBlocks(lhs_hir);
                    if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                        self.active_expr_borrows.items.len = assign_borrow_base;
                        return self.emitUnitVal(tok);
                    }
                    const soa_idx_node = self.hir_store.getNode(soa_idx_hir);
                    const base_hir = HirIndex.fromInt(soa_idx_node.data.lhs);
                    const idx_hir = HirIndex.fromInt(soa_idx_node.data.rhs);
                    const raw_base = try self.lowerMutPlace(base_hir);
                    const peeled = try self.peelAutoDerefPlace(raw_base, self.hir_store.getNode(base_hir).type_id);
                    const saved_mut = self.is_mut_place_context;
                    self.is_mut_place_context = false;
                    const idx_val = try self.lowerRValue(idx_hir);
                    self.is_mut_place_context = saved_mut;
                    const peeled_base_ty = self.pool.unwrapUnderlyingType(peeled.pointee_ty);
                    try self.emitIndexBoundsCheck(peeled.place_id, peeled_base_ty, idx_val, true, tok);
                    const elem_struct_ty = self.pool.unwrapUnderlyingType(
                        TypeId.fromInt(self.pool.getNode(peeled_base_ty).lhs),
                    );
                    var f_ord: u32 = 0;
                    while (resolveVerifierFieldType(self.pool, self.sym_table, elem_struct_ty, f_ord)) |f_ty| : (f_ord += 1) {
                        const f_val = try self.ssa.emitInst(self.cur_bb, .{
                            .op = .aggregate_extract,
                            .flags = .{ .is_synthetic = true },
                            .type_id = f_ty,
                            .operands = .{ .lhs = rhs_val.asInt(), .rhs = f_ord },
                        }, tok);
                        const soa_projs = [2]MirProjection{
                            .{ .kind = .soa_elem, .payload = f_ord },
                            .{ .kind = .index, .payload = idx_val.asInt() },
                        };
                        const f_place = try self.extendPlace(peeled.place_id, &soa_projs);
                        const write_tok = try self.emitGhostOpen(.ghost_access_set, f_place, .scoped_projection, tok);
                        try self.emitZeroPadIfRequired(f_place, f_ty, tok);
                        _ = try self.ssa.emitInst(self.cur_bb, .{
                            .op = .place_store,
                            .flags = .{ .has_side_effects = true },
                            .type_id = .unit_ty,
                            .operands = .{ .lhs = f_place.asInt(), .rhs = f_val.asInt() },
                        }, tok);
                        try self.emitGhostEnd(write_tok, tok);
                    }
                    try self.popAndCloseBorrowsTo(assign_borrow_base, tok);
                    return self.emitUnitVal(tok);
                }

                const rhs_val = try self.lowerRValue(rhs_hir);
                if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                    return self.emitUnitVal(tok);
                }
                const dest_place = try self.lowerMutPlace(lhs_hir);
                if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                    return self.emitUnitVal(tok);
                }
                const place_rec = self.body.places.items[dest_place.asInt()];
                if (place_rec.proj_len == 0) {
                    try self.markStorageInit(LocalId.fromInt(place_rec.base), tok);
                }
                const write_tok = try self.emitGhostOpen(.ghost_access_set, dest_place, .scoped_projection, tok);
                try self.emitZeroPadIfRequired(dest_place, lhs_node.type_id, tok);
                _ = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .place_store,
                    .flags = .{ .has_side_effects = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = dest_place.asInt(), .rhs = rhs_val.asInt() },
                }, tok);
                self.last_assigned_place = dest_place;
                try self.emitGhostEnd(write_tok, tok);
                return self.emitUnitVal(tok);
            },
            .hir_field_proj => {
                const base_hir = HirIndex.fromInt(node.data.lhs);
                const base_node = self.hir_store.getNode(base_hir);
                const peeled_base_ty = self.unwrapAllRefsType(base_node.type_id);
                const base_ty_tag = self.pool.getNode(peeled_base_ty).tag;

                // Synthetic `.as_ptr()` / `.as_mut_ptr()` data pointer extraction on `str` or `&[T]` (`SE-09`):
                if (node.flags.is_synthetic and node.data.rhs == 0 and
                    (peeled_base_ty == .str_ty or base_ty_tag == .slice_ty or
                        unionSliceElemType(self.pool, peeled_base_ty) != null))
                {
                    const unwrapped_dst = self.pool.unwrapUnderlyingType(node.type_id);
                    if (!unwrapped_dst.isError() and self.pool.getNode(unwrapped_dst).tag == .raw_ptr_ty) {
                        const slice_val = try self.lowerBorrowedValue(base_hir);
                        return self.ssa.emitInst(self.cur_bb, .{
                            .op = .aggregate_extract,
                            .flags = .{ .is_synthetic = true },
                            .type_id = node.type_id,
                            .operands = .{ .lhs = slice_val.asInt(), .rhs = 0 },
                        }, tok);
                    }
                }

                // `#soa` homogeneous column slice extraction (`items.x` -> `soa_column_slice`):
                if ((base_ty_tag == .soa_slice_ty or base_ty_tag == .soa_array_ty) and
                    node.data.rhs != hir.FIELD_ORDINAL_LEN)
                {
                    const raw_place = try self.lowerPlace(base_hir);
                    const peeled = try self.peelAutoDerefPlace(raw_place, base_node.type_id);
                    const open_tok = try self.emitGhostOpen(
                        .ghost_access_let,
                        peeled.place_id,
                        .scoped_projection,
                        tok,
                    );
                    const col_val = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .soa_column_slice,
                        .type_id = node.type_id,
                        .operands = .{ .lhs = peeled.place_id.asInt(), .rhs = node.data.rhs },
                    }, tok);
                    try self.emitGhostEnd(open_tok, tok);
                    return col_val;
                }

                // Pure RValue aggregate field extraction vs. addressable place projection load:
                if (base_node.flags.category == .rvalue and !self.isPtrOrRefType(base_node.type_id) and
                    node.data.rhs != hir.FIELD_ORDINAL_LEN)
                {
                    const agg_val = try self.lowerRValue(base_hir);
                    return self.ssa.emitInst(self.cur_bb, .{
                        .op = .aggregate_extract,
                        .type_id = node.type_id,
                        .operands = .{ .lhs = agg_val.asInt(), .rhs = node.data.rhs },
                    }, tok);
                }

                const proj_place = try self.lowerPlace(expr_hir);
                return self.loadPlaceValue(proj_place, node.type_id, tok, true);
            },
            .hir_index_proj, .hir_soa_field_ptr => {
                if (node.tag == .hir_index_proj) {
                    if (try self.tryGatherSoaElementRValue(node, true)) |gathered_val| {
                        return gathered_val;
                    }
                }
                const elem_place = try self.lowerPlace(expr_hir);
                return self.loadPlaceValue(elem_place, node.type_id, tok, true);
            },
            .hir_subscript_call => {
                var spliced = try self.spliceSubscriptCall(expr_hir, .let_mode, true);
                const loaded_val = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .place_load,
                    .type_id = node.type_id,
                    .operands = .{ .lhs = spliced.place_id.asInt(), .rhs = 0 },
                }, tok);
                try self.closeSplicedSubscriptAccess(&spliced, tok);
                return loaded_val;
            },
            .hir_bitfield_read => {
                const backing_val = try self.lowerRValue(HirIndex.fromInt(node.data.lhs));
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .bitfield_extract,
                    .type_id = node.type_id,
                    .operands = .{ .lhs = backing_val.asInt(), .rhs = node.data.rhs },
                }, tok);
            },
            .hir_bitfield_rmw => {
                const lhs_hir = HirIndex.fromInt(node.data.lhs);
                const bit_spec_raw = self.hir_store.extra_data.items[node.data.rhs];
                const new_val_hir = HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs + 1]);
                const lhs_node = self.hir_store.getNode(lhs_hir);

                if (lhs_node.tag == .hir_var_ref and !self.hir_place_remap.contains(lhs_node.data.lhs)) {
                    const lid = self.mapHirLocal(lhs_node.data.lhs);
                    if (!lid.isNone() and !self.body.locals.items[lid.asInt()].flags().is_address_taken) {
                        const old_backing = try self.ssa.readVariable(lid.asInt(), self.cur_bb);
                        const new_field_val = try self.lowerRValue(new_val_hir);
                        const pair_start: u32 = @intCast(self.body.extra_args.items.len);
                        try self.body.extra_args.appendSlice(
                            self.body.allocator,
                            &[2]u32{ old_backing.asInt(), new_field_val.asInt() },
                        );
                        const updated_backing = try self.ssa.emitInst(self.cur_bb, .{
                            .op = .bitfield_insert,
                            .type_id = lhs_node.type_id,
                            .operands = .{ .lhs = pair_start, .rhs = bit_spec_raw },
                        }, tok);
                        try self.ssa.writeVariable(lid.asInt(), self.cur_bb, updated_backing);
                        return self.emitUnitVal(tok);
                    }
                }

                const dest_place = try self.lowerMutPlace(lhs_hir);
                const new_field_val = try self.lowerRValue(new_val_hir);
                const old_backing = try self.loadPlaceValue(dest_place, lhs_node.type_id, tok, true);
                const pair_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(
                    self.body.allocator,
                    &[2]u32{ old_backing.asInt(), new_field_val.asInt() },
                );
                const updated_backing = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .bitfield_insert,
                    .type_id = lhs_node.type_id,
                    .operands = .{ .lhs = pair_start, .rhs = bit_spec_raw },
                }, tok);
                const rw_tok = try self.emitGhostOpen(
                    .ghost_access_inout,
                    dest_place,
                    .scoped_projection,
                    tok,
                );
                _ = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .place_store,
                    .flags = .{ .has_side_effects = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = dest_place.asInt(), .rhs = updated_backing.asInt() },
                }, tok);
                self.last_assigned_place = dest_place;
                try self.emitGhostEnd(rw_tok, tok);
                return self.emitUnitVal(tok);
            },
            .hir_unary_op => {
                const uop: hir.HirUnaryOp = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))));
                const sub_hir = HirIndex.fromInt(node.data.rhs);
                switch (uop) {
                    .addr_of, .addr_of_mut => {
                        const is_mut = uop == .addr_of_mut;
                        const target_place = if (is_mut)
                            try self.lowerMutPlace(sub_hir)
                        else
                            try self.lowerPlace(sub_hir);
                        const borrow_tok = try self.emitGhostOpen(
                            if (is_mut) .ghost_access_inout else .ghost_access_let,
                            target_place,
                            .addr_borrow,
                            tok,
                        );
                        try self.active_expr_borrows.append(self.allocator, borrow_tok);
                        return self.ssa.emitInst(self.cur_bb, .{
                            .op = .place_addr,
                            .type_id = node.type_id,
                            .operands = .{ .lhs = target_place.asInt(), .rhs = @intFromBool(is_mut) },
                        }, tok);
                    },
                    .addr_of_raw, .addr_of_raw_mut => {
                        const is_mut_raw = uop == .addr_of_raw_mut;
                        const sub_cat = self.hir_store.getNode(sub_hir).flags.category;
                        const target_place = if (is_mut_raw and sub_cat == .place_mut)
                            try self.lowerMutPlace(sub_hir)
                        else
                            try self.lowerPlace(sub_hir);
                        return self.ssa.emitInst(self.cur_bb, .{
                            .op = .place_addr,
                            .type_id = node.type_id,
                            .operands = .{ .lhs = target_place.asInt(), .rhs = if (is_mut_raw) 3 else 2 },
                        }, tok);
                    },
                    .deref => {
                        const deref_place = try self.lowerPlace(expr_hir);
                        return self.loadPlaceValue(deref_place, node.type_id, tok, true);
                    },
                    .neg => {
                        const sub_val = try self.lowerRValue(sub_hir);
                        const is_float = self.isFloatType(node.type_id);
                        const mir_uop: UnaryOpKind = if (is_float) .fneg else .sneg_checked;
                        return self.ssa.emitInst(self.cur_bb, .{
                            .op = .unary_op,
                            .flags = .{ .has_trap_risk = !is_float },
                            .aux_u16 = @backingInt(mir_uop),
                            .type_id = node.type_id,
                            .operands = .{ .lhs = sub_val.asInt(), .rhs = 0 },
                        }, tok);
                    },
                    .logical_not => {
                        const sub_val = try self.lowerRValue(sub_hir);
                        return self.ssa.emitInst(self.cur_bb, .{
                            .op = .unary_op,
                            .aux_u16 = @backingInt(UnaryOpKind.bool_not),
                            .type_id = node.type_id,
                            .operands = .{ .lhs = sub_val.asInt(), .rhs = 0 },
                        }, tok);
                    },
                    .bit_not => {
                        const sub_val = try self.lowerRValue(sub_hir);
                        return self.ssa.emitInst(self.cur_bb, .{
                            .op = .unary_op,
                            .aux_u16 = @backingInt(UnaryOpKind.bit_not),
                            .type_id = node.type_id,
                            .operands = .{ .lhs = sub_val.asInt(), .rhs = 0 },
                        }, tok);
                    },
                }
            },
            .hir_cast => {
                const src_hir = HirIndex.fromInt(node.data.lhs);
                const cast_kind: hir.HirCastKind = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.rhs))));
                const src_node = self.hir_store.getNode(src_hir);
                const src_ty = src_node.type_id;
                const unwrapped_src = self.pool.unwrapUnderlyingType(src_ty);
                const unwrapped_dst = self.pool.unwrapUnderlyingType(node.type_id);

                // [1] Captureless closure literal coerced directly to `fn(…) -> R` (`SE-19`):
                if (cast_kind == .ptr_cast and !unwrapped_src.isError() and !unwrapped_dst.isError() and
                    self.pool.getNode(unwrapped_src).tag == .closure_ty and
                    self.pool.getNode(unwrapped_dst).tag == .fn_ty and
                    src_node.tag == .hir_closure and src_node.data.lhs < self.hir_store.functions.items.len)
                {
                    const fn_meta = self.hir_store.functions.items[src_node.data.lhs];
                    if (fn_meta.capture_len == 0) {
                        return self.ssa.emitInst(self.cur_bb, .{
                            .op = .fn_addr,
                            .flags = .{ .is_synthetic = node.flags.is_synthetic },
                            .type_id = node.type_id,
                            .operands = .{
                                .lhs = fn_meta.def_id.asInt(),
                                .rhs = fn_meta.symbol_index.asInt(),
                            },
                        }, tok);
                    }
                }

                // [2] Backed `enum Name: BackingInt` `as Int` (`ADR-22C`):
                if (cast_kind == .int_to_int and !unwrapped_src.isError() and
                    self.pool.getNode(unwrapped_src).tag == .enum_ty)
                {
                    if (src_node.tag == .hir_construct) {
                        const ck: hir.HirConstructKind = @fromBackingInt(@intCast(@as(u8, @truncate(src_node.data.lhs))));
                        const raw_elems = self.hir_store.getLenPrefixedExtra(src_node.data.rhs);
                        if (ck == .enum_variant and raw_elems.len == 0) {
                            const var_ord: u32 = src_node.data.lhs >> 8;
                            const disc_val = self.pool.getEnumVariantDiscriminant(unwrapped_src, var_ord) orelse
                                @as(i128, var_ord);
                            const c_idx = try self.body.appendConst(.{ .int_val = disc_val });
                            return self.ssa.emitInst(self.cur_bb, .{
                                .op = .const_scalar,
                                .flags = .{ .is_synthetic = node.flags.is_synthetic },
                                .type_id = node.type_id,
                                .operands = .{ .lhs = c_idx, .rhs = 0 },
                            }, tok);
                        }
                    }
                    const enum_val = try self.lowerRValue(src_hir);
                    const discr_u32 = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .unary_op,
                        .flags = .{ .is_synthetic = true },
                        .aux_u16 = @backingInt(UnaryOpKind.ssa_discriminant),
                        .type_id = .u32_ty,
                        .operands = .{ .lhs = enum_val.asInt(), .rhs = 0 },
                    }, tok);
                    const variant_count = self.countSumVariants(unwrapped_src) orelse 0;
                    var is_dense_identity = true;
                    for (0..variant_count) |v_i| {
                        const ord: u32 = @intCast(v_i);
                        const disc_val = self.pool.getEnumVariantDiscriminant(unwrapped_src, ord) orelse
                            @as(i128, ord);
                        if (disc_val != @as(i128, ord)) {
                            is_dense_identity = false;
                            break;
                        }
                    }
                    if (is_dense_identity or variant_count == 0) {
                        if (self.selectMirCastOp(.int_to_int, .u32_ty, node.type_id)) |uop_kind| {
                            return self.ssa.emitInst(self.cur_bb, .{
                                .op = .unary_op,
                                .flags = .{ .is_synthetic = true },
                                .aux_u16 = @backingInt(uop_kind),
                                .type_id = node.type_id,
                                .operands = .{ .lhs = discr_u32.asInt(), .rhs = 0 },
                            }, tok);
                        }
                        return self.ssa.emitInst(self.cur_bb, .{
                            .op = .copy_val,
                            .type_id = node.type_id,
                            .operands = .{ .lhs = discr_u32.asInt(), .rhs = 0 },
                        }, tok);
                    }
                    const res_var = try self.allocTempLocal(node.type_id, tok, false, false);
                    const join_bb = try self.ssa.createBlock(false, false);
                    const src_bb = self.cur_bb;
                    var first_edge: EdgeId = .none;
                    const arm_bbs = try self.allocator.alloc(MirBlockId, variant_count);
                    defer self.allocator.free(arm_bbs);
                    for (0..variant_count) |v_i| {
                        arm_bbs[v_i] = try self.ssa.createBlock(false, false);
                    }
                    for (0..variant_count) |v_i| {
                        const target_bb = arm_bbs[v_i];
                        const sw_idx: u16 = if (v_i + 1 < variant_count) blk_sw: {
                            const idx: u16 = @intCast(self.body.switch_values.items.len);
                            try self.body.switch_values.append(self.body.allocator, @as(i128, v_i));
                            break :blk_sw idx;
                        } else std.math.maxInt(u16);
                        const edge_id = try self.ssa.addOutgoingEdge(src_bb, target_bb, &.{}, sw_idx);
                        if (v_i == 0) first_edge = edge_id;
                    }
                    self.ssa.setTerminator(src_bb, .{
                        .kind = .switch_int,
                        .edge_len = @intCast(variant_count),
                        .cond_or_val = discr_u32.asInt(),
                        .edge_start = first_edge.asInt(),
                    });
                    for (0..variant_count) |v_i| {
                        const ord: u32 = @intCast(v_i);
                        try self.ssa.sealBlock(arm_bbs[v_i]);
                        self.cur_bb = arm_bbs[v_i];
                        const disc_val = self.pool.getEnumVariantDiscriminant(unwrapped_src, ord) orelse
                            @as(i128, ord);
                        const c_idx = try self.body.appendConst(.{ .int_val = disc_val });
                        const c_val = try self.ssa.emitInst(self.cur_bb, .{
                            .op = .const_scalar,
                            .flags = .{ .is_synthetic = true },
                            .type_id = node.type_id,
                            .operands = .{ .lhs = c_idx, .rhs = 0 },
                        }, tok);
                        try self.ssa.writeVariable(res_var.asInt(), self.cur_bb, c_val);
                        try self.emitBr(join_bb, &.{});
                    }
                    try self.ssa.sealBlock(join_bb);
                    self.cur_bb = join_bb;
                    return self.ssa.readVariable(res_var.asInt(), join_bb);
                }

                const src_val = if (cast_kind == .ptr_cast and node.flags.is_synthetic)
                    try self.lowerBorrowedValue(src_hir)
                else
                    try self.lowerRValue(src_hir);
                if (cast_kind == .ptr_cast) {
                    if (!unwrapped_dst.isError() and self.pool.getNode(unwrapped_dst).tag == .struct_ty) {
                        var field_vals: std.ArrayListUnmanaged(u32) = .empty;
                        defer field_vals.deinit(self.allocator);
                        var field_ord: u32 = 0;
                        while (resolveVerifierFieldType(
                            self.pool,
                            self.sym_table,
                            unwrapped_dst,
                            field_ord,
                        )) |field_ty| : (field_ord += 1) {
                            const elem_val = if (field_ord == 0)
                                try self.ssa.emitInst(self.cur_bb, .{
                                    .op = .unary_op,
                                    .flags = .{ .is_synthetic = true },
                                    .aux_u16 = @backingInt(UnaryOpKind.ptr_cast),
                                    .type_id = field_ty,
                                    .operands = .{ .lhs = src_val.asInt(), .rhs = 0 },
                                }, tok)
                            else
                                try self.ssa.emitDefaultScalarInBlock(self.cur_bb, field_ty);
                            try field_vals.append(self.allocator, elem_val.asInt());
                        }
                        const args_start: u32 = @intCast(self.body.extra_args.items.len);
                        try self.body.extra_args.appendSlice(self.body.allocator, field_vals.items);
                        return self.ssa.emitInst(self.cur_bb, .{
                            .op = .aggregate_make,
                            .flags = .{ .is_synthetic = true },
                            .aux_u16 = @backingInt(AggregateKind.struct_agg),
                            .type_id = node.type_id,
                            .operands = .{ .lhs = args_start, .rhs = @intCast(field_vals.items.len) },
                        }, tok);
                    }
                }
                if (self.selectMirCastOp(cast_kind, src_ty, node.type_id)) |uop_kind| {
                    return self.ssa.emitInst(self.cur_bb, .{
                        .op = .unary_op,
                        .flags = .{ .is_synthetic = node.flags.is_synthetic },
                        .aux_u16 = @backingInt(uop_kind),
                        .type_id = node.type_id,
                        .operands = .{ .lhs = src_val.asInt(), .rhs = 0 },
                    }, tok);
                }
                if (src_ty == node.type_id) return src_val;
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .copy_val,
                    .type_id = node.type_id,
                    .operands = .{ .lhs = src_val.asInt(), .rhs = 0 },
                }, tok);
            },
            .hir_binary_op => {
                const lhs_hir = HirIndex.fromInt(self.hir_store.extra_data.items[node.data.lhs]);
                const rhs_hir = HirIndex.fromInt(self.hir_store.extra_data.items[node.data.lhs + 1]);
                const bin_op: hir.HirBinaryOp = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.rhs))));

                // Short-circuiting `and` / `or` CFG diamond lowering:
                if (bin_op == .logical_and or bin_op == .logical_or) {
                    const sc_var = try self.allocTempLocal(.bool_ty, tok, false, false);
                    const lhs_val = try self.lowerRValue(lhs_hir);
                    if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return lhs_val;

                    const short_val = try self.emitBoolVal(bin_op == .logical_or, tok);
                    try self.ssa.writeVariable(sc_var.asInt(), self.cur_bb, short_val);

                    const rhs_bb = try self.ssa.createBlock(false, false);
                    const join_bb = try self.ssa.createBlock(false, false);
                    if (bin_op == .logical_and) {
                        try self.emitCondBr(lhs_val, rhs_bb, join_bb);
                    } else {
                        try self.emitCondBr(lhs_val, join_bb, rhs_bb);
                    }
                    try self.ssa.sealBlock(rhs_bb);

                    self.cur_bb = rhs_bb;
                    const rhs_borrow_base = self.active_expr_borrows.items.len;
                    const rhs_val = try self.lowerRValue(rhs_hir);
                    if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                        try self.popAndCloseBorrowsTo(rhs_borrow_base, tok);
                        try self.ssa.writeVariable(sc_var.asInt(), self.cur_bb, rhs_val);
                        try self.emitBr(join_bb, &.{});
                    } else {
                        self.active_expr_borrows.items.len = rhs_borrow_base;
                    }

                    try self.ssa.sealBlock(join_bb);
                    self.cur_bb = join_bb;
                    return self.ssa.readVariable(sc_var.asInt(), join_bb);
                }

                const lhs_val = try self.lowerRValue(lhs_hir);
                const rhs_val = try self.lowerRValue(rhs_hir);
                const operand_ty = self.hir_store.getNode(lhs_hir).type_id;
                const mir_bin = if (node.flags.is_dollar_sub)
                    BinOpKind.usub_checked
                else
                    self.selectMirBinOp(bin_op, operand_ty);
                const has_trap_risk = @backingInt(mir_bin) <= @backingInt(BinOpKind.lshr_checked);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .bin_op,
                    .flags = .{
                        .has_trap_risk = has_trap_risk,
                        .is_dollar_sub = node.flags.is_dollar_sub,
                    },
                    .aux_u16 = @backingInt(mir_bin),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = lhs_val.asInt(), .rhs = rhs_val.asInt() },
                }, tok);
            },
            .hir_project_arg => {
                const mode: ParamMode = @fromBackingInt(@intCast(@as(u2, @truncate(node.data.lhs))));
                const inner_hir = HirIndex.fromInt(node.data.rhs);
                if (mode == .let_mode) return self.lowerBorrowedValue(inner_hir);
                return self.lowerRValue(inner_hir);
            },
            .hir_call => return self.lowerCallNode(expr_hir),
            .hir_intrinsic_call => return self.lowerIntrinsicNode(expr_hir),
            .hir_construct => return self.lowerConstructNode(expr_hir),
            .hir_closure => return self.lowerClosureNode(expr_hir),
            .hir_block => return self.lowerBlockNode(expr_hir),
            .hir_if => return self.lowerIfNode(expr_hir),
            .hir_cond_if => return self.lowerCondIfNode(expr_hir),
            .hir_cond_while => return self.lowerCondWhileNode(expr_hir),
            .hir_orelse => return self.lowerOrelseNode(expr_hir),
            .hir_unreachable => {
                try self.emitBorrowEndsAboveDepth(0, tok);
                self.ssa.setTerminator(self.cur_bb, .{
                    .kind = .trap,
                    .aux_u8 = @backingInt(MirTrapReason.unreachable_reached),
                });
                return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
            },
            .hir_ctx_get, .hir_ctx_set, .hir_ctx_region_push, .hir_ctx_region_pop => {
                return self.lowerContextIntrinsicNode(expr_hir);
            },
            .hir_slice_range => return self.lowerSliceRangeNode(expr_hir),
            .hir_match => return self.lowerMatchExpr(expr_hir),
            .hir_loop => return self.lowerLoopNode(expr_hir),
            .hir_break => return self.lowerBreakNode(expr_hir),
            .hir_continue => return self.lowerContinueNode(expr_hir),
            .hir_return => {
                try self.lowerReturnNode(expr_hir);
                return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
            },
            .hir_defer => {
                if (!self.is_lowering_cleanup) {
                    const is_errdefer = (node.data.lhs & 1) != 0;
                    const err_local_plus1 = node.data.lhs >> 1;
                    try self.cleanup_stack.append(self.allocator, .{
                        .is_errdefer = is_errdefer,
                        .hir_err_local = if (err_local_plus1 > 0) err_local_plus1 - 1 else NONE_U32,
                        .body_hir = HirIndex.fromInt(node.data.rhs),
                        .scope_depth = self.scope_depth,
                        .loop_depth = self.loop_depth,
                        .storage_floor = self.storage_locals.items.len,
                    });
                }
                return self.emitUnitVal(tok);
            },
            .hir_yield => {
                if (self.is_sast_subscript_body) {
                    const saved_mut = self.is_mut_place_context;
                    self.is_mut_place_context = self.is_sast_subscript_inout;
                    const yielded_place = blk_yield_place: {
                        defer self.is_mut_place_context = saved_mut;
                        break :blk_yield_place try self.lowerPlace(HirIndex.fromInt(node.data.lhs));
                    };
                    const ghost_op: MirOp = if (self.is_sast_subscript_inout)
                        .ghost_access_inout
                    else
                        .ghost_access_let;
                    try self.emitGhostEnd(
                        try self.emitGhostOpen(ghost_op, yielded_place, .scoped_projection, tok),
                        tok,
                    );
                    return self.emitUnitVal(tok);
                }
                const yielded_place = try self.lowerPlace(HirIndex.fromInt(node.data.lhs));
                const yielded_val = try self.loadPlaceValue(yielded_place, node.type_id, tok, false);
                try self.emitBorrowEndsAboveDepth(0, tok);
                try self.emitInlineNormalCleanupsAbove(0, tok);
                try self.emitFinalReturnTerminator(yielded_val, tok);
                return yielded_val;
            },
            .hir_await => return self.lowerAwaitNode(expr_hir),
            else => return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id),
        }
    }

    /// Lowers `hir_await` into `TerminatorKind.coro_suspend -> [resume_bb(%ready_val), cancel_bb]` (`DR-08`).
    fn lowerAwaitNode(self: *MirLowerer, await_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(await_hir);
        const tok = node.origin_token;
        const fut_val = try self.lowerRValue(HirIndex.fromInt(node.data.lhs));
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }

        const suspend_bb = self.cur_bb;
        const resume_bb = try self.ssa.createBlock(false, false);
        const cancel_bb = try self.ssa.createBlock(false, true);
        const ready_val = try self.ssa.addExplicitBlockParam(resume_bb, node.type_id, tok, true);

        const resume_edge = try self.ssa.addOutgoingEdge(
            suspend_bb,
            resume_bb,
            &.{},
            std.math.maxInt(u16),
        );
        _ = try self.ssa.addOutgoingEdge(
            suspend_bb,
            cancel_bb,
            &.{},
            std.math.maxInt(u16),
        );
        self.ssa.setTerminator(suspend_bb, .{
            .kind = .coro_suspend,
            .edge_len = 2,
            .cond_or_val = fut_val.asInt(),
            .edge_start = resume_edge.asInt(),
        });
        try self.ssa.sealBlock(resume_bb);
        try self.ssa.sealBlock(cancel_bb);

        // Populate `cancel_bb`: close active mid-expression Ghost borrows, run LIFO `defer`s + `ghost_storage_deinit`s:
        self.cur_bb = cancel_bb;
        try self.emitBorrowEndsAboveDepth(0, tok);
        const saved_borrows = try self.allocator.dupe(MirValueId, self.active_expr_borrows.items);
        defer if (saved_borrows.len > 0) self.allocator.free(saved_borrows);
        self.active_expr_borrows.clearRetainingCapacity();

        try self.emitInlineNormalCleanupsAbove(0, tok);
        if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
            try self.emitBorrowEndsAboveDepth(0, tok);
            const cancel_ret_val = try self.ssa.emitDefaultScalarInBlock(self.cur_bb, self.body.ret_ty);
            try self.emitFinalReturnTerminator(cancel_ret_val, tok);
        }

        self.active_expr_borrows.clearRetainingCapacity();
        try self.active_expr_borrows.appendSlice(self.allocator, saved_borrows);

        self.cur_bb = resume_bb;
        return ready_val;
    }

    /// Pending call-scoped Ghost borrow opened right before `.call`.
    const PendingCallBorrow = struct {
        /// Ghost access opcode (`.ghost_access_let`, `.ghost_access_inout`, or `.ghost_access_set`).
        op: MirOp,
        /// Target `PlaceId`.
        place_id: PlaceId,
    };

    /// Lowers `hir_call` obeying Hylo post-argument callee order & Call Continuation Split-Edge.
    fn lowerCallNode(self: *MirLowerer, call_hir: HirIndex) anyerror!MirValueId {
        const call_node = self.hir_store.getNode(call_hir);
        const tok = call_node.origin_token;
        const callee_hir = HirIndex.fromInt(call_node.data.lhs);
        const raw_args = self.hir_store.getLenPrefixedExtra(call_node.data.rhs);

        const callee_node = self.hir_store.getNode(callee_hir);
        const sig_view = self.pool.getFnSignatureView(callee_node.type_id);
        const call_expr_borrow_floor = self.active_expr_borrows.items.len;

        var arg_words: std.ArrayListUnmanaged(u32) = .empty;
        defer arg_words.deinit(self.allocator);
        var arg_modes: std.ArrayListUnmanaged(ParamMode) = .empty;
        defer arg_modes.deinit(self.allocator);
        var pending_call_borrows: std.ArrayListUnmanaged(PendingCallBorrow) = .empty;
        defer pending_call_borrows.deinit(self.allocator);
        var call_borrows: std.ArrayListUnmanaged(u32) = .empty;
        defer call_borrows.deinit(self.allocator);
        var set_places: std.ArrayListUnmanaged(PlaceId) = .empty;
        defer set_places.deinit(self.allocator);

        // [1] Evaluate arguments strictly left-to-right (`DR-02` Deliverable 2 §2):
        for (raw_args, 0..) |raw_arg, arg_i| {
            var inner_hir = HirIndex.fromInt(raw_arg);
            var mode: ParamMode = if (sig_view) |sv|
                (if (arg_i < sv.paramCount()) sv.getParamMode(arg_i) else .let_mode)
            else
                .let_mode;

            if (!inner_hir.isNone() and self.hir_store.getNode(inner_hir).tag == .hir_project_arg) {
                const proj_node = self.hir_store.getNode(inner_hir);
                mode = @fromBackingInt(@intCast(@as(u2, @truncate(proj_node.data.lhs))));
                inner_hir = HirIndex.fromInt(proj_node.data.rhs);
            }

            try arg_modes.append(self.allocator, mode);
            switch (mode) {
                .let_mode => {
                    const inner_node = self.hir_store.getNode(inner_hir);
                    if (inner_node.tag == .hir_var_ref) {
                        const lid = self.mapHirLocal(inner_node.data.lhs);
                        if (!lid.isNone() and self.body.locals.items[lid.asInt()].flags().is_address_taken) {
                            const place = try self.makePlace(lid, &.{});
                            const loaded_val = try self.loadPlaceValue(place, inner_node.type_id, tok, false);
                            try pending_call_borrows.append(self.allocator, .{
                                .op = .ghost_access_let,
                                .place_id = place,
                            });
                            try arg_words.append(self.allocator, loaded_val.asInt());
                            if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                                self.active_expr_borrows.items.len = call_expr_borrow_floor;
                                return self.ssa.emitDefaultScalarInBlock(.fromInt(0), call_node.type_id);
                            }
                            continue;
                        }
                    }
                    const borrowed_val = try self.lowerBorrowedValue(inner_hir);
                    try arg_words.append(self.allocator, borrowed_val.asInt());
                },
                .sink_mode => {
                    const moved_val = try self.lowerRValue(inner_hir);
                    try arg_words.append(self.allocator, moved_val.asInt());
                },
                .inout_mode => {
                    const arg_place = try self.lowerMutPlace(inner_hir);
                    try pending_call_borrows.append(self.allocator, .{
                        .op = .ghost_access_inout,
                        .place_id = arg_place,
                    });
                    try arg_words.append(self.allocator, arg_place.asInt());
                },
                .set_mode => {
                    const arg_place = try self.lowerMutPlace(inner_hir);
                    try pending_call_borrows.append(self.allocator, .{
                        .op = .ghost_access_set,
                        .place_id = arg_place,
                    });
                    try set_places.append(self.allocator, arg_place);
                    try arg_words.append(self.allocator, arg_place.asInt());
                },
            }
            if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                self.active_expr_borrows.items.len = call_expr_borrow_floor;
                return self.ssa.emitDefaultScalarInBlock(.fromInt(0), call_node.type_id);
            }
        }

        // [2] Evaluate callee AFTER all arguments (`DR-02` Post-Argument Callee Evaluation):
        const callee_val = try self.lowerRValue(callee_hir);
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
            self.active_expr_borrows.items.len = call_expr_borrow_floor;
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), call_node.type_id);
        }

        // [2b] Open call-scoped Ghost tokens at the top of the Ghost stack right before `.call`:
        for (pending_call_borrows.items) |pending| {
            const open_tok = try self.emitGhostOpen(pending.op, pending.place_id, .scoped_projection, tok);
            try call_borrows.append(self.allocator, open_tok.asInt());
        }

        // [3] Pack `MirCallSite` metadata:
        const args_start: u32 = @intCast(self.body.extra_args.items.len);
        try self.body.extra_args.appendSlice(self.body.allocator, arg_words.items);
        const call_borrows_start: u32 = @intCast(self.body.extra_args.items.len);
        try self.body.extra_args.appendSlice(self.body.allocator, call_borrows.items);
        var type_args_start: u32 = 0;
        var type_args_len: u16 = 0;
        if (self.hir_store.call_type_args.get(call_hir.asInt())) |ta_span| {
            if (ta_span.len > 0 and ta_span.start + ta_span.len <= self.hir_store.extra_data.items.len) {
                type_args_start = @intCast(self.body.extra_args.items.len);
                type_args_len = ta_span.len;
                try self.body.extra_args.appendSlice(
                    self.body.allocator,
                    self.hir_store.extra_data.items[ta_span.start .. ta_span.start + ta_span.len],
                );
            }
        }
        const modes_start: u32 = @intCast(self.body.call_arg_modes.items.len);
        try self.body.call_arg_modes.appendSlice(self.body.allocator, arg_modes.items);

        var direct_def: DefId = DefId.NONE;
        var direct_sym: SymbolIndex = .none;
        var is_callee_contextless = false;
        if (callee_node.tag == .hir_global_ref) {
            direct_def = DefId.fromInt(callee_node.data.lhs);
            direct_sym = SymbolIndex.fromInt(callee_node.data.rhs);
            is_callee_contextless = self.isCalleeContextless(direct_def, direct_sym);
        }

        const call_site_idx: u32 = @intCast(self.body.calls.items.len);
        const is_c_variadic = if (sig_view) |sv| (sv.is_c_abi and sv.is_variadic) else false;
        const fixed_arity: u16 = if (sig_view) |sv|
            @intCast(@min(sv.paramCount(), std.math.maxInt(u16)))
        else
            @intCast(@min(arg_words.items.len, std.math.maxInt(u16)));
        try self.body.calls.append(self.body.allocator, .{
            .callee_val = callee_val,
            .direct_def_id = direct_def,
            .direct_symbol = direct_sym,
            .args_start = args_start,
            .args_len = @intCast(arg_words.items.len),
            .modes_start = modes_start,
            .call_borrows_start = call_borrows_start,
            .call_borrows_len = @intCast(call_borrows.items.len),
            .type_args_start = type_args_start,
            .type_args_len = type_args_len,
            .ret_ty = call_node.type_id,
            .is_callee_contextless = is_callee_contextless,
            .is_c_variadic = is_c_variadic,
            .is_unsafe_call = call_node.flags.is_unsafe,
            .fixed_arity = fixed_arity,
            .origin_token = tok,
        });

        // [4] Enforce Call Continuation Split-Edge Invariant:
        //     `normal_bb` has `pred_len == 1`, `paramLen() == 1` (`%ret_val`), `normal_edge.args_len == 0`:
        const normal_bb = try self.ssa.createBlock(false, false);
        const ret_val = try self.ssa.addExplicitBlockParam(normal_bb, call_node.type_id, tok, true);
        const normal_edge = try self.ssa.addOutgoingEdge(
            self.cur_bb,
            normal_bb,
            &.{},
            std.math.maxInt(u16),
        );
        self.ssa.setTerminator(self.cur_bb, .{
            .kind = .call,
            .edge_len = 1,
            .cond_or_val = call_site_idx,
            .edge_start = normal_edge.asInt(),
        });
        try self.ssa.sealBlock(normal_bb);

        self.cur_bb = normal_bb;

        // [5] Close call-scoped Ghost tokens in reverse LIFO order & mark `set` places initialized:
        var bor_idx = call_borrows.items.len;
        while (bor_idx > 0) {
            bor_idx -= 1;
            try self.emitGhostEnd(MirValueId.fromInt(call_borrows.items[bor_idx]), tok);
        }
        const unwrapped_call_ret = self.pool.unwrapUnderlyingType(call_node.type_id);
        const is_fallible_result_call = !unwrapped_call_ret.isError() and
            self.pool.getNode(unwrapped_call_ret).tag == .result_ty;
        for (set_places.items) |set_place| {
            const place_rec = self.body.places.items[set_place.asInt()];
            if (place_rec.proj_len == 0) {
                if (self.is_for_sast and is_fallible_result_call) {
                    try self.registerStorageLocalInCurrentScope(LocalId.fromInt(place_rec.base), tok);
                } else {
                    try self.markStorageInit(LocalId.fromInt(place_rec.base), tok);
                }
            }
        }
        if (!self.hasTypeRegions(call_node.type_id)) {
            try self.popAndCloseBorrowsTo(call_expr_borrow_floor, tok);
        }

        if (call_node.type_id == .never_ty) {
            self.ssa.setTerminator(self.cur_bb, .{ .kind = .unreachable_term });
        }
        return ret_val;
    }

    /// Checks whether a direct callee `(def_id, sym_idx)` is `contextless` / `@noalloc`.
    fn isCalleeContextless(
        self: *const MirLowerer,
        def_id: DefId,
        sym_idx: SymbolIndex,
    ) bool {
        for (self.hir_store.functions.items) |fn_meta| {
            if ((!sym_idx.isNone() and fn_meta.symbol_index == sym_idx) or
                (!def_id.isNone() and fn_meta.def_id == def_id))
            {
                return fn_meta.is_contextless or fn_meta.is_derived;
            }
        }
        if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) {
            const sym = self.sym_table.getSymbol(sym_idx).*;
            if (sym.flags.is_builtin or sym.flags.is_comptime) return true;
        }
        return false;
    }

    /// Lowers `hir_intrinsic_call` (`@compile_assert`, `@compile_error`, `@embed_bytes`, wire/narrow intrinsics, etc.).
    fn lowerIntrinsicNode(self: *MirLowerer, intr_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(intr_hir);
        const tok = node.origin_token;

        const extra_base = node.data.rhs;
        const type_len = if (extra_base < self.hir_store.extra_data.items.len)
            self.hir_store.extra_data.items[extra_base]
        else
            0;
        const val_len = if (extra_base + 1 < self.hir_store.extra_data.items.len)
            self.hir_store.extra_data.items[extra_base + 1]
        else
            0;
        const val_start = extra_base + 2 + type_len;

        const is_internal_intr = (node.data.lhs & hir.HIR_INTERNAL_INTRINSIC_FLAG) != 0;
        const is_async_future_make = is_internal_intr and
            @as(hir.HirInternalIntrinsic, @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))))) == .async_future_make;

        var lowered_vals: std.ArrayListUnmanaged(u32) = .empty;
        defer lowered_vals.deinit(self.allocator);
        if (val_start + val_len <= self.hir_store.extra_data.items.len) {
            for (self.hir_store.extra_data.items[val_start .. val_start + val_len]) |raw_arg| {
                const arg_hir = HirIndex.fromInt(raw_arg);
                if (is_async_future_make and !arg_hir.isNone() and
                    self.hir_store.getNode(arg_hir).tag == .hir_project_arg)
                {
                    const proj_node = self.hir_store.getNode(arg_hir);
                    const mode: ParamMode = @fromBackingInt(@intCast(@as(u2, @truncate(proj_node.data.lhs))));
                    if (mode == .inout_mode or mode == .set_mode) {
                        const inner_hir = HirIndex.fromInt(proj_node.data.rhs);
                        const arg_place = try self.lowerMutPlace(inner_hir);
                        const ghost_op: MirOp = if (mode == .inout_mode) .ghost_access_inout else .ghost_access_set;
                        const borrow_tok = try self.emitGhostOpen(ghost_op, arg_place, .addr_borrow, tok);
                        try self.active_expr_borrows.append(self.allocator, borrow_tok);
                        const mut_ref_ty = try self.pool.internRef(self.hir_store.getNode(inner_hir).type_id, true);
                        const addr_val = try self.ssa.emitInst(self.cur_bb, .{
                            .op = .place_addr,
                            .flags = .{ .is_synthetic = true },
                            .type_id = mut_ref_ty,
                            .operands = .{ .lhs = arg_place.asInt(), .rhs = 0 },
                        }, tok);
                        if (mode == .set_mode) {
                            const place_rec = self.body.places.items[arg_place.asInt()];
                            if (place_rec.proj_len == 0) {
                                try self.markStorageInit(LocalId.fromInt(place_rec.base), tok);
                            }
                        }
                        try lowered_vals.append(self.allocator, addr_val.asInt());
                        continue;
                    }
                }
                const arg_val = try self.lowerRValue(arg_hir);
                try lowered_vals.append(self.allocator, arg_val.asInt());
            }
        }

        if (is_internal_intr) {
            const internal_kind: hir.HirInternalIntrinsic = @fromBackingInt(
                @intCast(@as(u8, @truncate(node.data.lhs))),
            );
            const args_start: u32 = @intCast(self.body.extra_args.items.len);
            try self.body.extra_args.appendSlice(self.body.allocator, lowered_vals.items);
            return switch (internal_kind) {
                .narrow_check => self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .has_trap_risk = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.narrow_check),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok),
                .try_narrow => self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.try_narrow),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok),
                .async_future_make => self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .is_synthetic = true, .is_unsafe = node.flags.is_unsafe },
                    .aux_u16 = @backingInt(MirIntrinsicKind.async_future_make),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok),
                .async_task_group_enter => self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.async_task_group_enter),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok),
                .async_spawn => self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.async_spawn),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok),
                .async_join => self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.async_join),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok),
                .async_cancel => self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.async_cancel),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok),
                .async_task_group_exit => self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.async_task_group_exit),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok),
                .async_yield => self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.async_yield),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok),
                .async_block_on => self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.async_block_on),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok),
                .int_min, .int_max, .int_bits => blk_int_meta: {
                    const type_arg_raw = if (type_len >= 1 and extra_base + 2 < self.hir_store.extra_data.items.len)
                        self.hir_store.extra_data.items[extra_base + 2]
                    else
                        node.type_id.asInt();
                    const mir_kind: MirIntrinsicKind = switch (internal_kind) {
                        .int_min => .int_min,
                        .int_max => .int_max,
                        .int_bits => .int_bits,
                        else => unreachable,
                    };
                    break :blk_int_meta self.ssa.emitInst(self.cur_bb, .{
                        .op = .intrinsic_op,
                        .flags = .{ .is_synthetic = true },
                        .aux_u16 = @backingInt(mir_kind),
                        .type_id = node.type_id,
                        .operands = .{ .lhs = type_arg_raw, .rhs = 0 },
                    }, tok);
                },
                .scalar_clz,
                .scalar_ctz,
                .scalar_popcnt,
                .scalar_bswap,
                .scalar_rotl,
                .scalar_rotr,
                .ptr_is_null,
                .ptr_offset,
                .slice_split_at,
                .slice_reverse,
                .soa_vec_new,
                .soa_vec_with_cap,
                .soa_vec_len,
                .soa_vec_cap,
                .soa_vec_push,
                .soa_vec_pop,
                .soa_vec_clear,
                .soa_vec_reserve,
                .soa_vec_as_slice,
                .soa_vec_col_slice,
                => blk_std01_int: {
                    const mir_kind: MirIntrinsicKind = switch (internal_kind) {
                        .scalar_clz => .scalar_clz,
                        .scalar_ctz => .scalar_ctz,
                        .scalar_popcnt => .scalar_popcnt,
                        .scalar_bswap => .scalar_bswap,
                        .scalar_rotl => .scalar_rotl,
                        .scalar_rotr => .scalar_rotr,
                        .ptr_is_null => .ptr_is_null,
                        .ptr_offset => .ptr_offset,
                        .slice_split_at => .slice_split_at,
                        .slice_reverse => .slice_reverse,
                        .soa_vec_new => .soa_vec_new,
                        .soa_vec_with_cap => .soa_vec_with_cap,
                        .soa_vec_len => .soa_vec_len,
                        .soa_vec_cap => .soa_vec_cap,
                        .soa_vec_push => .soa_vec_push,
                        .soa_vec_pop => .soa_vec_pop,
                        .soa_vec_clear => .soa_vec_clear,
                        .soa_vec_reserve => .soa_vec_reserve,
                        .soa_vec_as_slice => .soa_vec_as_slice,
                        .soa_vec_col_slice => .soa_vec_col_slice,
                        else => unreachable,
                    };
                    break :blk_std01_int self.ssa.emitInst(self.cur_bb, .{
                        .op = .intrinsic_op,
                        .flags = .{
                            .has_side_effects = mir_kind.isSideEffectingRoot(),
                            .has_trap_risk = internal_kind == .slice_split_at,
                            .is_synthetic = true,
                            .is_unsafe = node.flags.is_unsafe,
                        },
                        .aux_u16 = @backingInt(mir_kind),
                        .type_id = node.type_id,
                        .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                    }, tok);
                },
            };
        }

        const intr_kind: type_system.IntrinsicKind = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))));
        switch (intr_kind) {
            .c_import => return self.emitUnitVal(tok),
            .implements => {
                const t0_raw = if (type_len >= 1 and extra_base + 2 < self.hir_store.extra_data.items.len)
                    self.hir_store.extra_data.items[extra_base + 2]
                else
                    TypeId.unit_ty.asInt();
                const t1_raw = if (type_len >= 2 and extra_base + 3 < self.hir_store.extra_data.items.len)
                    self.hir_store.extra_data.items[extra_base + 3]
                else
                    TypeId.unit_ty.asInt();
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .aux_u16 = @backingInt(MirIntrinsicKind.implements),
                    .type_id = .bool_ty,
                    .operands = .{ .lhs = t0_raw, .rhs = t1_raw },
                }, tok);
            },
            .compile_error => {
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, lowered_vals.items);
                _ = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .has_trap_risk = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.compile_error),
                    .type_id = .never_ty,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok);
                try self.emitBorrowEndsAboveDepth(0, tok);
                self.ssa.setTerminator(self.cur_bb, .{
                    .kind = .trap,
                    .aux_u8 = @backingInt(MirTrapReason.assertion_failed),
                });
                return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
            },
            .compile_assert => {
                if (lowered_vals.items.len >= 1) {
                    const cond_val = MirValueId.fromInt(lowered_vals.items[0]);
                    const pass_bb = try self.ssa.createBlock(false, false);
                    const fail_bb = try self.ssa.createBlock(false, true);
                    try self.emitCondBr(cond_val, pass_bb, fail_bb);
                    try self.ssa.sealBlock(pass_bb);
                    try self.ssa.sealBlock(fail_bb);

                    self.cur_bb = fail_bb;
                    const args_start: u32 = @intCast(self.body.extra_args.items.len);
                    try self.body.extra_args.appendSlice(self.body.allocator, lowered_vals.items);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .intrinsic_op,
                        .flags = .{ .has_side_effects = true, .has_trap_risk = true },
                        .aux_u16 = @backingInt(MirIntrinsicKind.compile_assert),
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                    }, tok);
                    self.ssa.setTerminator(self.cur_bb, .{
                        .kind = .trap,
                        .aux_u8 = @backingInt(MirTrapReason.assertion_failed),
                    });

                    self.cur_bb = pass_bb;
                }
                return self.emitUnitVal(tok);
            },
            .embed_bytes => {
                const origin_fid = self.hir_store.embed_origin_files.get(intr_hir.asInt()) orelse
                    self.hir_store.file_id;
                const fid_const_idx = try self.body.appendConst(.{ .int_val = @as(i128, origin_fid.asInt()) });
                const fid_val = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .flags = .{ .is_synthetic = true },
                    .type_id = .u32_ty,
                    .operands = .{ .lhs = fid_const_idx, .rhs = 0 },
                }, tok);
                try lowered_vals.append(self.allocator, fid_val.asInt());
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, lowered_vals.items);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .aux_u16 = @backingInt(MirIntrinsicKind.embed_bytes),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok);
            },
            .size_of, .align_of, .type_name => {
                const type_arg_raw = if (type_len >= 1 and extra_base + 2 < self.hir_store.extra_data.items.len)
                    self.hir_store.extra_data.items[extra_base + 2]
                else
                    TypeId.unit_ty.asInt();
                const mir_kind: MirIntrinsicKind = switch (intr_kind) {
                    .size_of => .size_of,
                    .align_of => .align_of,
                    .type_name => .type_name,
                    else => unreachable,
                };
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .aux_u16 = @backingInt(mir_kind),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = type_arg_raw, .rhs = 0 },
                }, tok);
            },
            .as_bytes, .bit_cast, .from_bytes, .view_bytes => {
                const mir_kind: MirIntrinsicKind = switch (intr_kind) {
                    .as_bytes => .as_bytes,
                    .bit_cast => .bit_cast,
                    .from_bytes => .from_bytes,
                    .view_bytes => .view_bytes,
                    else => unreachable,
                };
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, lowered_vals.items);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_trap_risk = true, .is_unsafe = node.flags.is_unsafe },
                    .aux_u16 = @backingInt(mir_kind),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok);
            },
            .drop_trace => {
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, lowered_vals.items);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_unsafe = node.flags.is_unsafe },
                    .aux_u16 = @backingInt(MirIntrinsicKind.drop_trace),
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok);
            },
            .panic, .trap, .sys_exit => {
                const mir_kind: MirIntrinsicKind = switch (intr_kind) {
                    .panic => .panic,
                    .trap => .trap,
                    .sys_exit => .sys_exit,
                    else => unreachable,
                };
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, lowered_vals.items);
                _ = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{
                        .has_side_effects = true,
                        .has_trap_risk = intr_kind != .sys_exit,
                        .is_unsafe = node.flags.is_unsafe,
                    },
                    .aux_u16 = @backingInt(mir_kind),
                    .type_id = .never_ty,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok);
                try self.emitBorrowEndsAboveDepth(0, tok);
                if (intr_kind == .sys_exit) {
                    self.ssa.setTerminator(self.cur_bb, .{ .kind = .unreachable_term });
                } else {
                    self.ssa.setTerminator(self.cur_bb, .{
                        .kind = .trap,
                        .aux_u8 = @backingInt(MirTrapReason.assertion_failed),
                    });
                }
                return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
            },
            .atomic_load,
            .atomic_store,
            .atomic_rmw_add,
            .atomic_rmw_sub,
            .atomic_rmw_xchg,
            .atomic_cmpxchg,
            .atomic_fence,
            .poll_reload,
            .sys_write,
            => {
                const mir_kind: MirIntrinsicKind = switch (intr_kind) {
                    .atomic_load => .atomic_load,
                    .atomic_store => .atomic_store,
                    .atomic_rmw_add => .atomic_rmw_add,
                    .atomic_rmw_sub => .atomic_rmw_sub,
                    .atomic_rmw_xchg => .atomic_rmw_xchg,
                    .atomic_cmpxchg => .atomic_cmpxchg,
                    .atomic_fence => .atomic_fence,
                    .poll_reload => .poll_reload,
                    .sys_write => .sys_write,
                    else => unreachable,
                };
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, lowered_vals.items);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_unsafe = node.flags.is_unsafe },
                    .aux_u16 = @backingInt(mir_kind),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok);
            },
            .simd_splat,
            .simd_add,
            .simd_sub,
            .simd_mul,
            .simd_reduce_add,
            .simd_load_unaligned,
            .simd_and,
            .simd_or,
            .simd_xor,
            .simd_eq,
            .simd_gt_s8,
            .simd_lt_s8,
            .simd_swizzle,
            .simd_shl_u8,
            .simd_shr_u8,
            .simd_bitmask,
            .sqrt,
            .from_le_bytes,
            .from_be_bytes,
            .to_le_bytes,
            .to_be_bytes,
            .slice_from_raw_parts,
            .slice_from_raw_parts_mut,
            .str_from_utf8_unchecked,
            .tls_scratch_ptr,
            .tls_alloc_state,
            .ctx_next_rng_seed,
            .fmt_write,
            .memcpy,
            .memmove,
            .memset,
            .ptr_copy,
            .ptr_copy_nonoverlapping,
            .ptr_read,
            .ptr_write,
            .drop_in_place,
            .forget,
            .sys_mmap,
            .sys_munmap,
            .wasm_memory_grow,
            => {
                const mir_kind: MirIntrinsicKind = switch (intr_kind) {
                    .simd_splat => .simd_splat,
                    .simd_add => .simd_add,
                    .simd_sub => .simd_sub,
                    .simd_mul => .simd_mul,
                    .simd_reduce_add => .simd_reduce_add,
                    .simd_load_unaligned => .simd_load_unaligned,
                    .simd_and => .simd_and,
                    .simd_or => .simd_or,
                    .simd_xor => .simd_xor,
                    .simd_eq => .simd_eq,
                    .simd_gt_s8 => .simd_gt_s8,
                    .simd_lt_s8 => .simd_lt_s8,
                    .simd_swizzle => .simd_swizzle,
                    .simd_shl_u8 => .simd_shl_u8,
                    .simd_shr_u8 => .simd_shr_u8,
                    .simd_bitmask => .simd_bitmask,
                    .sqrt => .sqrt,
                    .from_le_bytes => .from_le_bytes,
                    .from_be_bytes => .from_be_bytes,
                    .to_le_bytes => .to_le_bytes,
                    .to_be_bytes => .to_be_bytes,
                    .slice_from_raw_parts, .slice_from_raw_parts_mut => .slice_from_raw_parts,
                    .str_from_utf8_unchecked => .str_from_utf8_unchecked,
                    .tls_scratch_ptr => .tls_scratch_ptr,
                    .tls_alloc_state => .tls_alloc_state,
                    .ctx_next_rng_seed => .ctx_next_rng_seed,
                    .fmt_write => .fmt_write,
                    .memcpy => .memcpy,
                    .memmove => .memmove,
                    .memset => .memset,
                    .ptr_copy => .ptr_copy,
                    .ptr_copy_nonoverlapping => .ptr_copy_nonoverlapping,
                    .ptr_read => .ptr_read,
                    .ptr_write => .ptr_write,
                    .drop_in_place => .ptr_drop_in_place,
                    .forget => .forget,
                    .sys_mmap => .sys_mmap,
                    .sys_munmap => .sys_munmap,
                    .wasm_memory_grow => .wasm_memory_grow,
                    else => unreachable,
                };
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, lowered_vals.items);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{
                        .has_side_effects = mir_kind.isSideEffectingRoot(),
                        .is_unsafe = node.flags.is_unsafe,
                    },
                    .aux_u16 = @backingInt(mir_kind),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok);
            },
            else => {
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, lowered_vals.items);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .aux_u16 = @backingInt(MirIntrinsicKind.derive_debug_fmt),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = @intCast(lowered_vals.items.len) },
                }, tok);
            },
        }
    }

    /// Lowers `hir_construct` into `MirOp.aggregate_make` (or `const_scalar` for `bitfield_zero`).
    fn lowerConstructNode(self: *MirLowerer, construct_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(construct_hir);
        const tok = node.origin_token;
        const ckind: hir.HirConstructKind = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))));
        const tag_ordinal: u32 = node.data.lhs >> 8;

        switch (ckind) {
            .bitfield_zero => {
                const unwrapped_bf = self.pool.unwrapUnderlyingType(node.type_id);
                const bf_node = self.pool.getNode(unwrapped_bf);
                if (bf_node.tag == .bit_field_ty) {
                    const backing_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(bf_node.lhs));
                    const backing_node = self.pool.getNode(backing_ty);
                    if (backing_node.tag == .array_ty) {
                        const zero_u8_const = try self.body.appendConst(.{ .int_val = 0 });
                        const zero_u8_val = try self.ssa.emitInst(self.cur_bb, .{
                            .op = .const_scalar,
                            .type_id = .u8_ty,
                            .operands = .{ .lhs = zero_u8_const, .rhs = 0 },
                        }, tok);
                        const arr_len: u32 = backing_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                        return self.ssa.emitInst(self.cur_bb, .{
                            .op = .aggregate_make,
                            .aux_u16 = @backingInt(AggregateKind.array_repeat),
                            .type_id = node.type_id,
                            .operands = .{ .lhs = zero_u8_val.asInt(), .rhs = arr_len },
                        }, tok);
                    }
                }
                const c_idx = try self.body.appendConst(.{ .int_val = 0 });
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .type_id = node.type_id,
                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                }, tok);
            },
            .array_repeat => {
                const repeat_count = self.hir_store.extra_data.items[node.data.rhs];
                const elem_hir = HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs + 1]);
                const elem_val = try self.lowerRValue(elem_hir);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .aggregate_make,
                    .aux_u16 = @backingInt(AggregateKind.array_repeat),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = elem_val.asInt(), .rhs = repeat_count },
                }, tok);
            },
            .struct_init, .tuple_init, .array_elements, .str_interp => {
                const raw_elems = self.hir_store.getLenPrefixedExtra(node.data.rhs);
                var elem_vals = try self.allocator.alloc(u32, raw_elems.len);
                defer self.allocator.free(elem_vals);
                for (raw_elems, 0..) |raw_elem, i| {
                    elem_vals[i] = (try self.lowerRValue(HirIndex.fromInt(raw_elem))).asInt();
                }
                const extra_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, elem_vals);
                const agg_kind: AggregateKind = switch (ckind) {
                    .struct_init => .struct_agg,
                    .tuple_init => .tuple_agg,
                    .array_elements => .array_elems,
                    .str_interp => .str_concat,
                    else => unreachable,
                };
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .aggregate_make,
                    .aux_u16 = @backingInt(agg_kind),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = extra_start, .rhs = @intCast(raw_elems.len) },
                }, tok);
            },
            .enum_variant, .optional_none, .optional_some, .result_ok, .result_err => {
                const resolved_tag: u32 = switch (ckind) {
                    .optional_none, .result_ok => 0,
                    .optional_some, .result_err => 1,
                    else => tag_ordinal,
                };
                const raw_elems = self.hir_store.getLenPrefixedExtra(node.data.rhs);
                var elem_vals = try self.allocator.alloc(u32, raw_elems.len);
                defer self.allocator.free(elem_vals);
                for (raw_elems, 0..) |raw_elem, i| {
                    elem_vals[i] = (try self.lowerRValue(HirIndex.fromInt(raw_elem))).asInt();
                }
                const extra_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, elem_vals);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .aggregate_make,
                    .aux_u16 = @backingInt(AggregateKind.tagged_variant),
                    .type_id = node.type_id,
                    .operands = .{
                        .lhs = extra_start,
                        .rhs = (resolved_tag << 16) | (@as(u32, @intCast(raw_elems.len)) & 0xFFFF),
                    },
                }, tok);
            },
            .fmt_args => {
                if (node.data.rhs + 2 > self.hir_store.extra_data.items.len) {
                    return self.ssa.emitDefaultScalarInBlock(self.cur_bb, node.type_id);
                }
                const piece_len = self.hir_store.extra_data.items[node.data.rhs];
                const hole_len = self.hir_store.extra_data.items[node.data.rhs + 1];
                const pieces_start = node.data.rhs + 2;
                const holes_start = pieces_start + piece_len;
                if (holes_start + hole_len * 3 > self.hir_store.extra_data.items.len) {
                    return self.ssa.emitDefaultScalarInBlock(self.cur_bb, node.type_id);
                }
                var fmt_words: std.ArrayListUnmanaged(u32) = .empty;
                defer fmt_words.deinit(self.allocator);

                const plen_c = try self.body.appendConst(.{ .int_val = @as(i128, piece_len) });
                const plen_val = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .flags = .{ .is_synthetic = true },
                    .type_id = .usize_ty,
                    .operands = .{ .lhs = plen_c, .rhs = 0 },
                }, tok);
                try fmt_words.append(self.allocator, plen_val.asInt());

                for (self.hir_store.extra_data.items[pieces_start .. pieces_start + piece_len]) |raw_piece| {
                    const piece_val = try self.lowerRValue(HirIndex.fromInt(raw_piece));
                    try fmt_words.append(self.allocator, piece_val.asInt());
                }

                for (0..hole_len) |hole_i| {
                    const base_off = holes_start + hole_i * 3;
                    const hole_hir = HirIndex.fromInt(self.hir_store.extra_data.items[base_off]);
                    const spec_lo_raw = self.hir_store.extra_data.items[base_off + 1];
                    const spec_hi_raw = self.hir_store.extra_data.items[base_off + 2];

                    const hole_ty = self.hir_store.getNode(hole_hir).type_id;
                    const hole_ref_ty = try self.pool.internRef(hole_ty, false);
                    const hole_place = try self.lowerPlace(hole_hir);
                    const borrow_tok = try self.emitGhostOpen(
                        .ghost_access_let,
                        hole_place,
                        .addr_borrow,
                        tok,
                    );
                    try self.active_expr_borrows.append(self.allocator, borrow_tok);
                    const hole_ref_val = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_addr,
                        .flags = .{ .is_synthetic = true },
                        .type_id = hole_ref_ty,
                        .operands = .{ .lhs = hole_place.asInt(), .rhs = 0 },
                    }, tok);
                    const lo_c = try self.body.appendConst(.{ .int_val = @as(i128, spec_lo_raw) });
                    const lo_val = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .const_scalar,
                        .flags = .{ .is_synthetic = true },
                        .type_id = .u32_ty,
                        .operands = .{ .lhs = lo_c, .rhs = 0 },
                    }, tok);
                    const hi_c = try self.body.appendConst(.{ .int_val = @as(i128, spec_hi_raw) });
                    const hi_val = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .const_scalar,
                        .flags = .{ .is_synthetic = true },
                        .type_id = .u32_ty,
                        .operands = .{ .lhs = hi_c, .rhs = 0 },
                    }, tok);
                    try fmt_words.appendSlice(
                        self.allocator,
                        &[3]u32{ hole_ref_val.asInt(), lo_val.asInt(), hi_val.asInt() },
                    );
                }
                if (hole_len > 0) {
                    const args_anchor_lid = try self.allocTempLocal(.u8_ty, tok, true, false);
                    try self.markStorageInit(args_anchor_lid, tok);
                    const args_anchor_place = try self.makePlace(args_anchor_lid, &.{});
                    const anchor_borrow_tok = try self.emitGhostOpen(
                        .ghost_access_let,
                        args_anchor_place,
                        .addr_borrow,
                        tok,
                    );
                    try self.active_expr_borrows.append(self.allocator, anchor_borrow_tok);
                    const u8_ref_ty = try self.pool.internRef(.u8_ty, false);
                    const anchor_ref_val = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_addr,
                        .flags = .{ .is_synthetic = true },
                        .type_id = u8_ref_ty,
                        .operands = .{ .lhs = args_anchor_place.asInt(), .rhs = 0 },
                    }, tok);
                    try fmt_words.append(self.allocator, anchor_ref_val.asInt());
                }
                const extra_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(self.body.allocator, fmt_words.items);
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .aggregate_make,
                    .flags = .{ .is_synthetic = true },
                    .aux_u16 = @backingInt(AggregateKind.fmt_args_make),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = extra_start, .rhs = @intCast(fmt_words.items.len) },
                }, tok);
            },
            .fmt_value => {
                if (node.data.rhs + 3 > self.hir_store.extra_data.items.len) {
                    return self.ssa.emitDefaultScalarInBlock(self.cur_bb, node.type_id);
                }
                const val_hir = HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs]);
                const spec_lo_raw = self.hir_store.extra_data.items[node.data.rhs + 1];
                const spec_hi_raw = self.hir_store.extra_data.items[node.data.rhs + 2];
                const val_ssa = try self.lowerBorrowedValue(val_hir);
                const lo_c = try self.body.appendConst(.{ .int_val = @as(i128, spec_lo_raw) });
                const lo_val = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .flags = .{ .is_synthetic = true },
                    .type_id = .u32_ty,
                    .operands = .{ .lhs = lo_c, .rhs = 0 },
                }, tok);
                const hi_c = try self.body.appendConst(.{ .int_val = @as(i128, spec_hi_raw) });
                const hi_val = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .flags = .{ .is_synthetic = true },
                    .type_id = .u32_ty,
                    .operands = .{ .lhs = hi_c, .rhs = 0 },
                }, tok);
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(
                    self.body.allocator,
                    &[3]u32{ val_ssa.asInt(), lo_val.asInt(), hi_val.asInt() },
                );
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.fmt_value),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = 3 },
                }, tok);
            },
        }
    }

    /// Returns `true` if `closure_hir` is `@local` or captures regional borrows (`V6`).
    fn isClosureMarkedLocal(self: *const MirLowerer, closure_hir: HirIndex) bool {
        const node = self.hir_store.getNode(closure_hir);
        if (node.tag != .hir_closure or node.data.lhs >= self.hir_store.functions.items.len) return false;
        const fn_meta = self.hir_store.functions.items[node.data.lhs];
        if (fn_meta.is_local_closure) return true;
        for (0..fn_meta.capture_len) |cap_i| {
            const outer_slot = self.hir_store.extra_data.items[fn_meta.capture_extra_start + cap_i * 2];
            if (outer_slot < self.hir_store.locals.items.len) {
                const cap_ty = self.hir_store.locals.items[outer_slot].type_id;
                if (self.isPtrOrRefType(cap_ty) or self.hasTypeRegions(cap_ty)) return true;
            }
            const outer_lid = self.mapHirLocal(outer_slot);
            if (!outer_lid.isNone() and self.body.locals.items[outer_lid.asInt()].flags().is_local_closure) {
                return true;
            }
        }
        return false;
    }

    /// Lowers `hir_closure` into `MirOp.aggregate_make(.closure_make)` packaging captured outer locals.
    fn lowerClosureNode(self: *MirLowerer, closure_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(closure_hir);
        const tok = node.origin_token;
        const fn_meta_idx = node.data.lhs;
        const is_local = self.isClosureMarkedLocal(closure_hir);
        var cap_vals: std.ArrayListUnmanaged(u32) = .empty;
        defer cap_vals.deinit(self.allocator);

        var fn_def_raw: u32 = fn_meta_idx;
        if (fn_meta_idx < self.hir_store.functions.items.len) {
            const fn_meta = self.hir_store.functions.items[fn_meta_idx];
            if (!fn_meta.def_id.isNone()) fn_def_raw = fn_meta.def_id.asInt();
            try cap_vals.append(self.allocator, fn_meta.capture_len);
            for (0..fn_meta.capture_len) |cap_i| {
                const outer_hir_local = self.hir_store.extra_data.items[fn_meta.capture_extra_start + cap_i * 2];
                const lid = self.mapHirLocal(outer_hir_local);
                if (!lid.isNone()) {
                    if (self.body.locals.items[lid.asInt()].flags().is_address_taken) {
                        const place = try self.makePlace(lid, &.{});
                        const val = try self.loadPlaceValue(
                            place,
                            self.body.locals.items[lid.asInt()].type_id,
                            tok,
                            fn_meta.is_move_closure,
                        );
                        try cap_vals.append(self.allocator, val.asInt());
                    } else {
                        const val = try self.ssa.readVariable(lid.asInt(), self.cur_bb);
                        try cap_vals.append(self.allocator, val.asInt());
                    }
                } else {
                    try cap_vals.append(self.allocator, (try self.emitUnitVal(tok)).asInt());
                }
            }
        } else {
            try cap_vals.append(self.allocator, 0);
        }

        const extra_start: u32 = @intCast(self.body.extra_args.items.len);
        try self.body.extra_args.appendSlice(self.body.allocator, cap_vals.items);
        return self.ssa.emitInst(self.cur_bb, .{
            .op = .aggregate_make,
            .flags = .{ .is_local_closure = is_local },
            .aux_u16 = @backingInt(AggregateKind.closure_make),
            .type_id = node.type_id,
            .operands = .{ .lhs = fn_def_raw, .rhs = extra_start },
        }, tok);
    }

    /// Lowers `hir_block` managing lexical scope depth, mid-expression borrows, and LIFO scope cleanups.
    fn lowerBlockNode(self: *MirLowerer, block_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(block_hir);
        const tok = node.origin_token;
        const stmts = self.hir_store.getLenPrefixedExtra(node.data.lhs);
        const tail_hir = HirIndex.fromInt(node.data.rhs);
        const is_preserving_walrus_borrows = node.flags.is_synthetic and self.isKeepingStmtBorrows(node);

        self.scope_depth += 1;
        const entered_depth = self.scope_depth;
        const saved_real_depth = self.enclosing_real_block_depth;
        const saved_cond_depth = self.active_cond_scope_depth;
        if (!node.flags.is_synthetic) {
            self.enclosing_real_block_depth = entered_depth;
            self.active_cond_scope_depth = 0;
        }
        defer {
            self.enclosing_real_block_depth = saved_real_depth;
            self.active_cond_scope_depth = saved_cond_depth;
        }
        const block_borrow_base = self.active_expr_borrows.items.len;
        const pa_meta = self.hir_store.parallel_assign_blocks.get(block_hir.asInt());
        var pa_targets: std.ArrayListUnmanaged(PlaceId) = .empty;
        defer pa_targets.deinit(self.allocator);

        for (stmts, 0..) |raw_stmt, stmt_idx| {
            if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) break;
            const stmt_borrow_base = self.active_expr_borrows.items.len;
            const stmt_hir = HirIndex.fromInt(raw_stmt);
            const stmt_node = self.hir_store.getNode(stmt_hir);
            self.last_assigned_place = .none;
            _ = try self.lowerRValue(stmt_hir);
            if (pa_meta) |span| {
                if (stmt_idx >= span.first_assign_idx and
                    stmt_idx < @as(usize, span.first_assign_idx) + span.assign_count and
                    !self.last_assigned_place.isNone())
                {
                    try pa_targets.append(self.allocator, self.last_assigned_place);
                }
            }
            // Statement-scoped temporaries close at `;`; region-carrying `let` bindings live to block exit:
            if (!self.isKeepingStmtBorrows(stmt_node) and
                !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb))
            {
                try self.popAndCloseBorrowsTo(stmt_borrow_base, stmt_node.origin_token);
            }
        }
        if (pa_targets.items.len >= 2 and !self.cur_bb.isNone()) {
            const p_start: u32 = @intCast(self.body.parallel_assign_places.items.len);
            try self.body.parallel_assign_places.appendSlice(self.body.allocator, pa_targets.items);
            try self.body.parallel_assign_groups.append(self.body.allocator, .{
                .block_id = self.cur_bb,
                .places_start = p_start,
                .places_len = @intCast(pa_targets.items.len),
                .origin_token = tok,
            });
        }

        var result_val: MirValueId = .none;
        if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
            result_val = if (!tail_hir.isNone())
                try self.lowerRValue(tail_hir)
            else
                try self.emitUnitVal(tok);
        }

        const is_live = !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb);
        if (!is_preserving_walrus_borrows) {
            if (is_live) {
                try self.popAndCloseBorrowsTo(block_borrow_base, tok);
            } else {
                self.active_expr_borrows.items.len = block_borrow_base;
            }
        }
        try self.exitLexicalScopeCleanups(entered_depth, is_live, tok);
        self.scope_depth -= 1;

        if (result_val.isNone()) {
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }
        return result_val;
    }

    /// Returns `true` if `pat_idx` matches every inhabitant of its pattern type unconditionally.
    fn isIrrefutableCondPat(self: *const MirLowerer, pat_idx: u32, depth: u8) bool {
        if (depth >= 32) return false;
        if (pat_idx == NONE_U32) return true;
        if (pat_idx >= self.hir_store.patterns.items.len) return false;
        const pat = self.hir_store.patterns.items[pat_idx];
        return switch (pat.kind) {
            .wildcard, .bind => true,
            .at_pat => |ap| self.isIrrefutableCondPat(ap.sub_pat, depth + 1),
            .or_pat => |op| self.isIrrefutableCondPat(op.lhs_pat, depth + 1) or
                self.isIrrefutableCondPat(op.rhs_pat, depth + 1),
            .tuple => |tup| blk_tup: {
                if (tup.sub_len != self.countProductFields(pat.type_id)) break :blk_tup false;
                if (tup.sub_start + tup.sub_len > self.hir_store.extra_data.items.len) break :blk_tup false;
                for (self.hir_store.extra_data.items[tup.sub_start .. tup.sub_start + tup.sub_len]) |sub_raw| {
                    if (!self.isIrrefutableCondPat(sub_raw, depth + 1)) break :blk_tup false;
                }
                break :blk_tup true;
            },
            .struct_pat => |sp| blk_struct: {
                for (0..sp.field_len) |field_i| {
                    const pair_base = sp.field_start + @as(u32, @intCast(field_i * 2));
                    if (pair_base + 1 >= self.hir_store.extra_data.items.len) break :blk_struct false;
                    if (!self.isIrrefutableCondPat(self.hir_store.extra_data.items[pair_base + 1], depth + 1)) {
                        break :blk_struct false;
                    }
                }
                break :blk_struct true;
            },
            .variant => |vp| blk_var: {
                if (self.countSumVariants(pat.type_id) != 1) break :blk_var false;
                if (vp.sub_start + vp.sub_len > self.hir_store.extra_data.items.len) break :blk_var false;
                for (self.hir_store.extra_data.items[vp.sub_start .. vp.sub_start + vp.sub_len]) |sub_raw| {
                    if (!self.isIrrefutableCondPat(sub_raw, depth + 1)) break :blk_var false;
                }
                break :blk_var true;
            },
            else => false,
        };
    }

    /// Accumulates variant `tag_ordinal` bits (`< 64`) of a sum type irrefutably matched by `pat_idx`.
    fn collectIrrefutableVariantMask(
        self: *const MirLowerer,
        pat_idx: u32,
        covered_mask: *u64,
        has_overflow_tag: *bool,
        depth: u8,
    ) void {
        if (depth >= 32 or pat_idx >= self.hir_store.patterns.items.len) return;
        const pat = self.hir_store.patterns.items[pat_idx];
        switch (pat.kind) {
            .wildcard, .bind => covered_mask.* = std.math.maxInt(u64),
            .at_pat => |ap| self.collectIrrefutableVariantMask(ap.sub_pat, covered_mask, has_overflow_tag, depth + 1),
            .or_pat => |op| {
                self.collectIrrefutableVariantMask(op.lhs_pat, covered_mask, has_overflow_tag, depth + 1);
                self.collectIrrefutableVariantMask(op.rhs_pat, covered_mask, has_overflow_tag, depth + 1);
            },
            .variant => |vp| {
                if (vp.sub_start + vp.sub_len > self.hir_store.extra_data.items.len) return;
                for (self.hir_store.extra_data.items[vp.sub_start .. vp.sub_start + vp.sub_len]) |sub_raw| {
                    if (!self.isIrrefutableCondPat(sub_raw, depth + 1)) return;
                }
                if (vp.tag_ordinal < 64) {
                    covered_mask.* |= (@as(u64, 1) << @intCast(vp.tag_ordinal));
                } else {
                    has_overflow_tag.* = true;
                }
            },
            else => {},
        }
    }

    /// Moves non-`Copy` `.auto_drop_tier` fields of an uncovered variant `ad_place` into temp locals and drops them in LIFO order.
    fn emitUncoveredAutoDropPayloadDeinit(
        self: *MirLowerer,
        ad_place: PlaceId,
        ad_ty: TypeId,
        depth: u32,
        tok: TokenIndex,
    ) anyerror!void {
        if (depth > 16 or ad_ty.isError() or ad_ty == .unit_ty) return;
        if (type_system.classifyOwnershipTier(self.pool, self.sym_table, ad_ty) != .auto_drop_tier) return;

        const unwrapped_ty = self.pool.unwrapUnderlyingType(ad_ty);
        if (self.pool.getTag(unwrapped_ty) == .tuple_ty) {
            const elems = self.pool.getTupleElements(unwrapped_ty);
            var field_lids: std.ArrayListUnmanaged(LocalId) = .empty;
            defer field_lids.deinit(self.allocator);

            for (elems, 0..) |raw_elem_ty, elem_i| {
                const elem_ty = TypeId.fromInt(raw_elem_ty);
                if (elem_ty.isError() or elem_ty == .unit_ty) continue;
                if (type_system.classifyOwnershipTier(self.pool, self.sym_table, elem_ty) != .auto_drop_tier) continue;
                const elem_proj = [1]MirProjection{.{ .kind = .field, .payload = @intCast(elem_i) }};
                if (!self.isValidPlaceExtension(ad_place, &elem_proj)) continue;
                const elem_place = try self.extendPlace(ad_place, &elem_proj);
                if (self.pool.getTag(self.pool.unwrapUnderlyingType(elem_ty)) == .tuple_ty) {
                    try self.emitUncoveredAutoDropPayloadDeinit(elem_place, elem_ty, depth + 1, tok);
                } else {
                    const elem_val = try self.loadPlaceValue(elem_place, elem_ty, tok, false);
                    const elem_lid = try self.allocTempLocal(elem_ty, tok, true, false);
                    const elem_dst = try self.makePlace(elem_lid, &.{});
                    try self.markStorageInitAtDepth(elem_lid, self.active_cond_scope_depth, tok);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_store,
                        .flags = .{ .has_side_effects = true, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = elem_dst.asInt(), .rhs = elem_val.asInt() },
                    }, tok);
                    if (self.storage_locals.items.len > 0) {
                        _ = self.storage_locals.pop();
                    }
                    try field_lids.append(self.allocator, elem_lid);
                }
            }

            var rev_idx = field_lids.items.len;
            while (rev_idx > 0) {
                rev_idx -= 1;
                _ = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .ghost_storage_deinit,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = field_lids.items[rev_idx].asInt(), .rhs = 0 },
                }, tok);
            }
            return;
        }

        const ad_val = try self.loadPlaceValue(ad_place, ad_ty, tok, false);
        const ad_lid = try self.allocTempLocal(ad_ty, tok, true, false);
        const ad_dst_place = try self.makePlace(ad_lid, &.{});
        try self.markStorageInitAtDepth(ad_lid, self.active_cond_scope_depth, tok);
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .place_store,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = ad_dst_place.asInt(), .rhs = ad_val.asInt() },
        }, tok);
        if (self.storage_locals.items.len > 0) {
            _ = self.storage_locals.pop();
        }
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .ghost_storage_deinit,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = ad_lid.asInt(), .rhs = 0 },
        }, tok);
    }

    /// Returns `true` when `scrut_place` can be discharged at Checkpoint B1 without invalidating downstream uses.
    fn isDischargeableCondScrutineeAtB1(
        self: *const MirLowerer,
        scrut_hir: HirIndex,
        scrut_node: hir.HirNode,
        scrut_place: PlaceId,
        pat_idx: u32,
    ) bool {
        if (scrut_node.flags.category != .place_imm and scrut_node.flags.category != .place_mut) {
            return true;
        }
        if (self.isPlaceBehindSharedRef(scrut_place)) return false;
        if (!self.isCompleteLinearUnpackPat(pat_idx, 0)) return false;
        if (scrut_node.tag != .hir_var_ref) return false;
        if (self.body.getPlaceProjections(scrut_place).len != 0) return false;
        if (self.loop_depth != 0) return false;

        const target_hir_local = scrut_node.data.lhs;
        const start_idx: usize = @as(usize, scrut_hir.asInt()) + 1;
        const end_idx: usize = self.hir_store.nodes.len;
        if (start_idx >= end_idx) return true;
        const tags = self.hir_store.nodes.items(.tag)[start_idx..end_idx];
        const datas = self.hir_store.nodes.items(.data)[start_idx..end_idx];
        for (tags, datas) |tag, data| {
            if (tag == .hir_var_ref and data.lhs == target_hir_local) return false;
        }
        return true;
    }

    /// Discharges `scrut_place` at Checkpoint B1 when `pat_idx` irrefutably covers every `@linear` variant.
    fn dischargeLinearSumComplementAtB1(
        self: *MirLowerer,
        scrut_place: PlaceId,
        scrut_ty: TypeId,
        pat_idx: u32,
        tok: TokenIndex,
    ) !void {
        if (scrut_ty.isError() or
            type_system.classifyOwnershipTier(self.pool, self.sym_table, scrut_ty) != .linear_tier)
        {
            return;
        }
        const unwrapped = self.pool.unwrapUnderlyingType(scrut_ty);
        if (unwrapped.isError()) return;
        const total_vars = self.countSumVariants(unwrapped) orelse return;
        if (total_vars == 0 or total_vars > 64) return;

        var covered_mask: u64 = 0;
        var has_overflow_tag = false;
        self.collectIrrefutableVariantMask(pat_idx, &covered_mask, &has_overflow_tag, 0);
        if (has_overflow_tag) return;

        var uncovered_tags: [64]u32 = undefined;
        var uncovered_tys: [64]TypeId = undefined;
        var uncovered_count: usize = 0;
        for (0..total_vars) |var_i| {
            if (((covered_mask >> @intCast(var_i)) & 1) != 0) continue;
            const var_ord: u32 = @intCast(var_i);
            const payload_ty = self.resolveVariantPayloadType(unwrapped, var_ord);
            if (payload_ty.isError() or payload_ty == .unit_ty) continue;
            const var_tier = type_system.classifyOwnershipTier(self.pool, self.sym_table, payload_ty);
            if (var_tier == .linear_tier) return;
            if (var_tier == .auto_drop_tier) {
                uncovered_tags[uncovered_count] = var_ord;
                uncovered_tys[uncovered_count] = payload_ty;
                uncovered_count += 1;
            }
        }

        if (uncovered_count > 0) {
            const discr_open = try self.emitGhostOpen(.ghost_access_let, scrut_place, .scoped_projection, tok);
            const discr_val = try self.ssa.emitInst(self.cur_bb, .{
                .op = .place_discriminant,
                .type_id = .u32_ty,
                .operands = .{ .lhs = scrut_place.asInt(), .rhs = 0 },
            }, tok);
            try self.emitGhostEnd(discr_open, tok);

            var case_bbs: [64]MirBlockId = undefined;
            for (0..uncovered_count) |case_i| {
                case_bbs[case_i] = try self.ssa.createBlock(false, false);
            }
            const done_bb = try self.ssa.createBlock(false, false);

            const first_edge_idx: u32 = @intCast(self.body.extra_edges.items.len);
            for (0..uncovered_count) |case_i| {
                const sw_val_idx: u16 = @intCast(self.body.switch_values.items.len);
                try self.body.switch_values.append(self.body.allocator, @as(i128, uncovered_tags[case_i]));
                _ = try self.ssa.addOutgoingEdge(self.cur_bb, case_bbs[case_i], &.{}, sw_val_idx);
            }
            _ = try self.ssa.addOutgoingEdge(self.cur_bb, done_bb, &.{}, std.math.maxInt(u16));
            self.ssa.setTerminator(self.cur_bb, .{
                .kind = .switch_int,
                .edge_len = @intCast(uncovered_count + 1),
                .cond_or_val = discr_val.asInt(),
                .edge_start = first_edge_idx,
            });

            for (0..uncovered_count) |case_i| {
                try self.ssa.sealBlock(case_bbs[case_i]);
                self.cur_bb = case_bbs[case_i];
                const dc_proj = [2]MirProjection{
                    .{ .kind = .downcast, .payload = uncovered_tags[case_i] },
                    .{ .kind = .field, .payload = 0 },
                };
                if (self.isValidPlaceExtension(scrut_place, &dc_proj)) {
                    const ad_src_place = try self.extendPlace(scrut_place, &dc_proj);
                    try self.emitUncoveredAutoDropPayloadDeinit(ad_src_place, uncovered_tys[case_i], 0, tok);
                }
                try self.emitBr(done_bb, &.{});
            }

            try self.ssa.sealBlock(done_bb);
            self.cur_bb = done_bb;
        }

        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .ghost_storage_move,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = scrut_place.asInt(), .rhs = 0 },
        }, tok);
    }

    /// Lowers conjunctive `ConditionScope` clauses (`bool_pred` & `is_match`) with Two-Checkpoint pre-`else` cleanup (`SE-01`/`SE-02`).
    fn lowerCondClauseList(
        self: *MirLowerer,
        cursor_io: *u32,
        clause_count: u32,
        outer_storage_floor: usize,
        outer_borrow_floor: usize,
        false_target_bb: MirBlockId,
        tok: TokenIndex,
    ) anyerror!bool {
        var clause_i: u32 = 0;
        while (clause_i < clause_count and cursor_io.* < self.hir_store.extra_data.items.len) : (clause_i += 1) {
            const kind_raw = self.hir_store.extra_data.items[cursor_io.*];
            cursor_io.* += 1;

            if (kind_raw == @backingInt(hir.HirCondClauseKind.is_match)) {
                if (cursor_io.* + 2 > self.hir_store.extra_data.items.len) return false;
                const scrut_hir = HirIndex.fromInt(self.hir_store.extra_data.items[cursor_io.*]);
                const pat_idx = self.hir_store.extra_data.items[cursor_io.* + 1];
                cursor_io.* += 2;

                if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return false;

                const scrut_borrow_base = self.active_expr_borrows.items.len;
                const scrut_node = self.hir_store.getNode(scrut_hir);
                const scrut_place = blk_scrut: {
                    if (scrut_node.flags.category == .place_imm or scrut_node.flags.category == .place_mut) {
                        break :blk_scrut try self.lowerPlace(scrut_hir);
                    }
                    const scrut_val = try self.lowerRValue(scrut_hir);
                    if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                        return false;
                    }
                    const scrut_lid = try self.allocTempLocal(scrut_node.type_id, tok, true, false);
                    const tmp_place = try self.makePlace(scrut_lid, &.{});
                    try self.markStorageInitAtDepth(scrut_lid, self.active_cond_scope_depth, tok);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_store,
                        .flags = .{ .has_side_effects = true, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = tmp_place.asInt(), .rhs = scrut_val.asInt() },
                    }, tok);
                    break :blk_scrut tmp_place;
                };
                if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return false;
                if (scrut_node.flags.category == .rvalue and !self.hasTypeRegions(scrut_node.type_id)) {
                    try self.popAndCloseBorrowsTo(scrut_borrow_base, tok);
                }

                // Checkpoint B1: capture storage ceiling BEFORE pattern bindings are initialized:
                const b1_storage_ceil = self.storage_locals.items.len;
                const b1_borrow_ceil = self.active_expr_borrows.items.len;

                var matrix_arena = std.heap.ArenaAllocator.init(self.allocator);
                defer matrix_arena.deinit();
                const m_alloc = matrix_arena.allocator();

                var synthetic_arms: [2]HirMatchArm = .{
                    .{
                        .pat_idx = pat_idx,
                        .guard_hir = .none,
                        .body_hir = .none,
                        .origin_token = tok,
                    },
                    .{
                        .pat_idx = NONE_U32,
                        .guard_hir = .none,
                        .body_hir = .none,
                        .origin_token = tok,
                    },
                };
                var arm_blocks: [2]MirBlockId = .{
                    try self.ssa.createBlock(false, false),
                    try self.ssa.createBlock(false, false),
                };
                var arm_reached: [2]bool = .{ false, false };
                var arm_ref_specs: [2]std.ArrayListUnmanaged(ArmRefSpec) = .{ .empty, .empty };

                var initial_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
                try self.appendExpandedOrRows(m_alloc, pat_idx, 0, &initial_rows);
                const wild_pats = try m_alloc.alloc(u32, 1);
                wild_pats[0] = NONE_U32;
                try initial_rows.append(m_alloc, .{
                    .pats = wild_pats,
                    .bindings = &.{},
                    .arm_idx = 1,
                });

                const init_cols = try m_alloc.alloc(PlaceId, 1);
                init_cols[0] = scrut_place;
                const init_tys = try m_alloc.alloc(TypeId, 1);
                init_tys[0] = scrut_node.type_id;

                const match_ctx = MatchCompileCtx{
                    .m_alloc = m_alloc,
                    .arms = &synthetic_arms,
                    .arm_blocks = &arm_blocks,
                    .arm_reached = &arm_reached,
                    .arm_ref_specs = &arm_ref_specs,
                    .scrut_place = scrut_place,
                    .scrut_ty = scrut_node.type_id,
                };
                self.decision_node_count = 0;
                try self.compileDecisionMatrix(&match_ctx, init_cols, init_tys, initial_rows.items, tok);

                try self.ssa.sealBlock(arm_blocks[0]);
                try self.ssa.sealBlock(arm_blocks[1]);

                // False edge at Checkpoint B1 (discriminant/structure mismatch – pattern bindings NOT yet live):
                if (arm_reached[1] and
                    self.ssa.blocks_scratch.items[arm_blocks[1].asInt()].preds.items.len > 0)
                {
                    self.cur_bb = arm_blocks[1];
                    const saved_borrows_len = self.active_expr_borrows.items.len;
                    self.active_expr_borrows.items.len = b1_borrow_ceil;
                    try self.emitBorrowEndsAboveDepth(outer_borrow_floor, tok);
                    self.active_expr_borrows.items.len = saved_borrows_len;
                    if (self.isDischargeableCondScrutineeAtB1(scrut_hir, scrut_node, scrut_place, pat_idx)) {
                        try self.dischargeLinearSumComplementAtB1(scrut_place, scrut_node.type_id, pat_idx, tok);
                    }
                    try self.emitStorageDeinitsInRange(outer_storage_floor, b1_storage_ceil, tok);
                    try self.emitBr(false_target_bb, &.{});
                } else {
                    self.ssa.setTerminator(arm_blocks[1], .{ .kind = .unreachable_term });
                }

                // True edge entering Checkpoint B2 (`arm_blocks[0]`):
                if (!arm_reached[0] or
                    self.ssa.blocks_scratch.items[arm_blocks[0].asInt()].preds.items.len == 0)
                {
                    self.ssa.setTerminator(arm_blocks[0], .{ .kind = .unreachable_term });
                    return false;
                }
                self.cur_bb = arm_blocks[0];
                for (arm_ref_specs[0].items) |spec| {
                    const ref_tok = try self.emitGhostOpen(
                        if (spec.is_mut) .ghost_access_inout else .ghost_access_let,
                        spec.place_id,
                        .addr_borrow,
                        tok,
                    );
                    try self.active_expr_borrows.append(self.allocator, ref_tok);
                }
            } else {
                if (cursor_io.* >= self.hir_store.extra_data.items.len) return false;
                const pred_hir = HirIndex.fromInt(self.hir_store.extra_data.items[cursor_io.*]);
                cursor_io.* += 1;

                if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return false;
                const pred_borrow_floor = self.active_expr_borrows.items.len;
                const pred_node = self.hir_store.getNode(pred_hir);
                const pred_val = try self.lowerRValue(pred_hir);
                if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return false;
                if (!self.isKeepingStmtBorrows(pred_node)) {
                    try self.popAndCloseBorrowsTo(pred_borrow_floor, tok);
                }

                const pred_hit_bb = try self.ssa.createBlock(false, false);
                const pred_miss_bb = try self.ssa.createBlock(false, false);
                try self.emitCondBr(pred_val, pred_hit_bb, pred_miss_bb);
                try self.ssa.sealBlock(pred_hit_bb);
                try self.ssa.sealBlock(pred_miss_bb);

                self.cur_bb = pred_miss_bb;
                try self.emitBorrowEndsAboveDepth(outer_borrow_floor, tok);
                try self.emitStorageDeinitsInRange(outer_storage_floor, self.storage_locals.items.len, tok);
                try self.emitBr(false_target_bb, &.{});

                self.cur_bb = pred_hit_bb;
            }
        }
        return !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb);
    }

    /// Lowers `hir_cond_if` (`SE-01` / `SE-02`) with Two-Checkpoint pre-`else` `ConditionScope` drop cascade.
    fn lowerCondIfNode(self: *MirLowerer, cond_if_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(cond_if_hir);
        const tok = node.origin_token;
        if (node.data.lhs >= self.hir_store.extra_data.items.len) {
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }

        const has_val = node.type_id != .unit_ty and node.type_id != .never_ty;
        const res_var = if (has_val)
            try self.allocTempLocal(node.type_id, tok, false, false)
        else
            LocalId.none;

        const outer_storage_floor = self.storage_locals.items.len;
        const outer_borrow_floor = self.active_expr_borrows.items.len;
        const outer_scope_depth = self.scope_depth;
        self.scope_depth += 1;
        const cond_scope_depth = self.scope_depth;
        const saved_cond_depth = self.active_cond_scope_depth;
        const saved_real_depth = self.enclosing_real_block_depth;
        self.active_cond_scope_depth = cond_scope_depth;
        self.enclosing_real_block_depth = cond_scope_depth;

        const else_entry_bb = try self.ssa.createBlock(false, false);
        const join_bb = try self.ssa.createBlock(false, false);

        var cursor = node.data.lhs;
        const clause_count = self.hir_store.extra_data.items[cursor];
        cursor += 1;

        const has_reached_then = try self.lowerCondClauseList(
            &cursor,
            clause_count,
            outer_storage_floor,
            outer_borrow_floor,
            else_entry_bb,
            tok,
        );
        self.active_cond_scope_depth = saved_cond_depth;
        self.enclosing_real_block_depth = saved_real_depth;

        const then_hir = if (cursor < self.hir_store.extra_data.items.len)
            HirIndex.fromInt(self.hir_store.extra_data.items[cursor])
        else
            HirIndex.none;
        const else_hir = if (cursor + 1 < self.hir_store.extra_data.items.len)
            HirIndex.fromInt(self.hir_store.extra_data.items[cursor + 1])
        else
            HirIndex.none;

        // Seal `else_entry_bb` now that all clause false-exit edges have been wired:
        try self.ssa.sealBlock(else_entry_bb);

        var has_reachable_arm = false;
        if (has_reached_then) {
            const then_borrow_base = self.active_expr_borrows.items.len;
            const then_val = try self.lowerRValue(then_hir);
            const is_then_live = !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb);
            if (is_then_live) {
                try self.popAndCloseBorrowsTo(then_borrow_base, tok);
                if (has_val) try self.ssa.writeVariable(res_var.asInt(), self.cur_bb, then_val);
                try self.popAndCloseBorrowsTo(outer_borrow_floor, tok);
                try self.exitLexicalScopeCleanups(cond_scope_depth, true, tok);
                try self.emitBr(join_bb, &.{});
                has_reachable_arm = true;
            } else {
                self.active_expr_borrows.items.len = outer_borrow_floor;
                try self.exitLexicalScopeCleanups(cond_scope_depth, false, tok);
            }
        } else {
            self.active_expr_borrows.items.len = outer_borrow_floor;
            try self.exitLexicalScopeCleanups(cond_scope_depth, false, tok);
        }

        // Shrink `ConditionScope` back to `outer_storage_floor` BEFORE lowering `else_hir`:
        self.storage_locals.items.len = outer_storage_floor;
        self.active_expr_borrows.items.len = outer_borrow_floor;
        self.scope_depth = outer_scope_depth;

        if (self.ssa.blocks_scratch.items[else_entry_bb.asInt()].preds.items.len > 0) {
            self.cur_bb = else_entry_bb;
            const else_borrow_base = self.active_expr_borrows.items.len;
            const else_val = if (!else_hir.isNone())
                try self.lowerRValue(else_hir)
            else
                try self.emitUnitVal(tok);
            if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                try self.popAndCloseBorrowsTo(else_borrow_base, tok);
                if (has_val) try self.ssa.writeVariable(res_var.asInt(), self.cur_bb, else_val);
                try self.emitBr(join_bb, &.{});
                has_reachable_arm = true;
            } else {
                self.active_expr_borrows.items.len = else_borrow_base;
            }
        } else {
            self.ssa.setTerminator(else_entry_bb, .{ .kind = .unreachable_term });
        }

        try self.ssa.sealBlock(join_bb);
        if (!has_reachable_arm) {
            self.cur_bb = join_bb;
            self.ssa.setTerminator(join_bb, .{ .kind = .unreachable_term });
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }
        self.cur_bb = join_bb;
        if (has_val) return self.ssa.readVariable(res_var.asInt(), join_bb);
        return self.emitUnitVal(tok);
    }

    /// Lowers `hir_cond_while` (`SE-01` / `SE-02` / `SE-06`) with per-iteration `ConditionScope` cleanup.
    fn lowerCondWhileNode(self: *MirLowerer, cond_while_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(cond_while_hir);
        const tok = node.origin_token;
        const loop_id = node.data.rhs;
        if (node.data.lhs >= self.hir_store.extra_data.items.len) {
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }

        const header_bb = try self.ssa.createBlock(false, false);
        const exit_bb = try self.ssa.createBlock(false, false);
        try self.emitBr(header_bb, &.{});

        const outer_storage_floor = self.storage_locals.items.len;
        const outer_borrow_floor = self.active_expr_borrows.items.len;
        const outer_scope_depth = self.scope_depth;

        self.loop_depth += 1;
        try self.loop_stack.append(self.allocator, .{
            .loop_id = loop_id,
            .header_bb = header_bb,
            .exit_bb = exit_bb,
            .break_var_id = NONE_U32,
            .outer_scope_depth = outer_scope_depth,
            .loop_depth = self.loop_depth,
            .outer_borrow_depth = outer_borrow_floor,
        });

        self.cur_bb = header_bb;
        self.scope_depth += 1;
        const cond_scope_depth = self.scope_depth;
        const saved_cond_depth = self.active_cond_scope_depth;
        const saved_real_depth = self.enclosing_real_block_depth;
        self.active_cond_scope_depth = cond_scope_depth;
        self.enclosing_real_block_depth = cond_scope_depth;

        var cursor = node.data.lhs;
        const clause_count = self.hir_store.extra_data.items[cursor];
        cursor += 1;

        const has_reached_body = try self.lowerCondClauseList(
            &cursor,
            clause_count,
            outer_storage_floor,
            outer_borrow_floor,
            exit_bb,
            tok,
        );
        self.active_cond_scope_depth = saved_cond_depth;
        self.enclosing_real_block_depth = saved_real_depth;

        const body_hir = if (cursor < self.hir_store.extra_data.items.len)
            HirIndex.fromInt(self.hir_store.extra_data.items[cursor])
        else
            HirIndex.none;
        const res_opt_local = if (cursor + 1 < self.hir_store.extra_data.items.len)
            self.hir_store.extra_data.items[cursor + 1]
        else
            NONE_U32;

        var latch_bb = header_bb;
        if (has_reached_body) {
            const body_borrow_base = self.active_expr_borrows.items.len;
            _ = try self.lowerRValue(body_hir);
            const is_body_live = !self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb);
            if (is_body_live) {
                latch_bb = self.cur_bb;
                try self.popAndCloseBorrowsTo(body_borrow_base, tok);
                try self.popAndCloseBorrowsTo(outer_borrow_floor, tok);
                try self.exitLexicalScopeCleanups(cond_scope_depth, true, tok);
                try self.emitBr(header_bb, &.{});
            } else {
                self.active_expr_borrows.items.len = outer_borrow_floor;
                try self.exitLexicalScopeCleanups(cond_scope_depth, false, tok);
                const preds = self.ssa.blocks_scratch.items[header_bb.asInt()].preds.items;
                if (preds.len > 1) {
                    const last_edge_id = preds[preds.len - 1];
                    latch_bb = self.body.extra_edges.items[last_edge_id.asInt()].src_bb;
                }
            }
        } else {
            self.active_expr_borrows.items.len = outer_borrow_floor;
            try self.exitLexicalScopeCleanups(cond_scope_depth, false, tok);
        }

        self.storage_locals.items.len = outer_storage_floor;
        self.active_expr_borrows.items.len = outer_borrow_floor;
        self.scope_depth = outer_scope_depth;

        if (self.hir_store.loop_contracts.get(loop_id)) |contract_meta| {
            try self.body.loop_contracts.append(self.body.allocator, .{
                .header_bb = header_bb,
                .latch_bb = latch_bb,
                .meta = contract_meta,
            });
        }

        _ = self.loop_stack.pop();
        self.loop_depth -= 1;

        try self.ssa.sealBlock(header_bb);
        try self.ssa.sealBlock(exit_bb);

        self.cur_bb = exit_bb;
        if (self.ssa.blocks_scratch.items[exit_bb.asInt()].preds.items.len == 0) {
            self.ssa.setTerminator(exit_bb, .{ .kind = .unreachable_term });
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }
        if (res_opt_local != NONE_U32) {
            const opt_lid = self.mapHirLocal(res_opt_local);
            if (!opt_lid.isNone()) {
                if (self.body.locals.items[opt_lid.asInt()].flags().is_address_taken) {
                    const opt_place = try self.makePlace(opt_lid, &.{});
                    return self.loadPlaceValue(opt_place, node.type_id, tok, true);
                }
                return self.ssa.readVariable(opt_lid.asInt(), exit_bb);
            }
        }
        return self.emitUnitVal(tok);
    }

    /// Lowers `hir_orelse` (`opt orelse fallback`, `SE-03`): evaluates `opt` once, lazily runs `fallback` on `.None` without `errdefer`.
    fn lowerOrelseNode(self: *MirLowerer, orelse_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(orelse_hir);
        const tok = node.origin_token;
        const opt_hir = HirIndex.fromInt(node.data.lhs);
        const fallback_hir = HirIndex.fromInt(node.data.rhs);

        const opt_borrow_base = self.active_expr_borrows.items.len;
        const opt_val = try self.lowerRValue(opt_hir);
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
            self.active_expr_borrows.items.len = opt_borrow_base;
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }
        if (!self.hasTypeRegions(node.type_id)) {
            try self.popAndCloseBorrowsTo(opt_borrow_base, tok);
        }

        const discr_val = try self.ssa.emitInst(self.cur_bb, .{
            .op = .unary_op,
            .flags = .{ .is_synthetic = true },
            .aux_u16 = @backingInt(UnaryOpKind.ssa_discriminant),
            .type_id = .u32_ty,
            .operands = .{ .lhs = opt_val.asInt(), .rhs = 0 },
        }, tok);
        const some_tag_const = try self.body.appendConst(.{ .int_val = 1 });
        const some_tag_val = try self.ssa.emitInst(self.cur_bb, .{
            .op = .const_scalar,
            .flags = .{ .is_synthetic = true },
            .type_id = .u32_ty,
            .operands = .{ .lhs = some_tag_const, .rhs = 0 },
        }, tok);
        const is_some = try self.ssa.emitInst(self.cur_bb, .{
            .op = .bin_op,
            .flags = .{ .is_synthetic = true },
            .aux_u16 = @backingInt(BinOpKind.eq),
            .type_id = .bool_ty,
            .operands = .{ .lhs = discr_val.asInt(), .rhs = some_tag_val.asInt() },
        }, tok);

        const has_val = node.type_id != .unit_ty and node.type_id != .never_ty;
        const res_var = if (has_val)
            try self.allocTempLocal(node.type_id, tok, false, false)
        else
            LocalId.none;

        const some_bb = try self.ssa.createBlock(false, false);
        const none_bb = try self.ssa.createBlock(false, false);
        const join_bb = try self.ssa.createBlock(false, false);
        try self.emitCondBr(is_some, some_bb, none_bb);
        try self.ssa.sealBlock(some_bb);
        try self.ssa.sealBlock(none_bb);

        // `.Some(v)` fast path:
        self.cur_bb = some_bb;
        if (has_val) {
            const payload_val = try self.ssa.emitInst(self.cur_bb, .{
                .op = .unary_op,
                .flags = .{ .is_synthetic = true },
                .aux_u16 = @backingInt(UnaryOpKind.ssa_variant_payload),
                .type_id = node.type_id,
                .operands = .{ .lhs = opt_val.asInt(), .rhs = 1 },
            }, tok);
            try self.ssa.writeVariable(res_var.asInt(), self.cur_bb, payload_val);
        }
        try self.emitBr(join_bb, &.{});
        var has_reaches_join = true;

        // `.None` lazy fallback path (does NOT trigger `errdefer` unless `fallback_hir` explicitly `return Err`s):
        self.cur_bb = none_bb;
        const fb_borrow_base = self.active_expr_borrows.items.len;
        const fb_val = try self.lowerRValue(fallback_hir);
        if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
            if (!self.hasTypeRegions(node.type_id)) {
                try self.popAndCloseBorrowsTo(fb_borrow_base, tok);
            }
            if (has_val) try self.ssa.writeVariable(res_var.asInt(), self.cur_bb, fb_val);
            try self.emitBr(join_bb, &.{});
        } else {
            self.active_expr_borrows.items.len = fb_borrow_base;
        }

        try self.ssa.sealBlock(join_bb);
        _ = &has_reaches_join;
        self.cur_bb = join_bb;
        if (has_val) return self.ssa.readVariable(res_var.asInt(), join_bb);
        return self.emitUnitVal(tok);
    }

    /// Lowers `hir_ctx_get`, `hir_ctx_set`, `hir_ctx_region_push`, and `hir_ctx_region_pop` (`SE-08`).
    fn lowerContextIntrinsicNode(self: *MirLowerer, ctx_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(ctx_hir);
        const tok = node.origin_token;
        const slot_ord = node.data.lhs;
        const slot_const_idx = try self.body.appendConst(.{ .int_val = @as(i128, slot_ord) });
        const slot_val = try self.ssa.emitInst(self.cur_bb, .{
            .op = .const_scalar,
            .flags = .{ .is_synthetic = true },
            .type_id = .u32_ty,
            .operands = .{ .lhs = slot_const_idx, .rhs = 0 },
        }, tok);

        switch (node.tag) {
            .hir_ctx_get => {
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.append(self.body.allocator, slot_val.asInt());
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.ctx_get),
                    .type_id = node.type_id,
                    .operands = .{ .lhs = args_start, .rhs = 1 },
                }, tok);
            },
            .hir_ctx_set => {
                const rhs_val = try self.lowerBorrowedValue(HirIndex.fromInt(node.data.rhs));
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(
                    self.body.allocator,
                    &[2]u32{ slot_val.asInt(), rhs_val.asInt() },
                );
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.ctx_set),
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = args_start, .rhs = 2 },
                }, tok);
            },
            .hir_ctx_region_push => {
                const region_val = try self.lowerBorrowedValue(HirIndex.fromInt(node.data.rhs));
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.appendSlice(
                    self.body.allocator,
                    &[2]u32{ slot_val.asInt(), region_val.asInt() },
                );
                self.body.has_ghost_instructions = true;
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.ghost_ctx_region_push),
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = args_start, .rhs = 2 },
                }, tok);
            },
            .hir_ctx_region_pop => {
                const args_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.append(self.body.allocator, slot_val.asInt());
                self.body.has_ghost_instructions = true;
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.ghost_ctx_region_pop),
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = args_start, .rhs = 1 },
                }, tok);
            },
            else => return self.emitUnitVal(tok),
        }
    }

    /// Emits sequence length extraction (`const_scalar` for concrete `[T; N]`, `.slice_len` load otherwise).
    fn emitPlaceSequenceLength(
        self: *MirLowerer,
        peeled_place: PlaceId,
        unwrapped_base: TypeId,
        tok: TokenIndex,
    ) !MirValueId {
        if (!unwrapped_base.isError()) {
            const base_node = self.pool.getNode(unwrapped_base);
            const is_fixed = base_node.tag == .array_ty or base_node.tag == .soa_array_ty;
            if (is_fixed and (base_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) == 0) {
                const c_idx = try self.body.appendConst(.{ .int_val = @as(i128, base_node.rhs) });
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .flags = .{ .is_synthetic = true },
                    .type_id = .usize_ty,
                    .operands = .{ .lhs = c_idx, .rhs = 0 },
                }, tok);
            }
            if (base_node.tag == .soa_vec_ty) {
                const ref_ty = try self.pool.internRef(unwrapped_base, false);
                const vec_addr = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .place_addr,
                    .flags = .{ .is_synthetic = true },
                    .type_id = ref_ty,
                    .operands = .{ .lhs = peeled_place.asInt(), .rhs = 0 },
                }, tok);
                const a_start: u32 = @intCast(self.body.extra_args.items.len);
                try self.body.extra_args.append(self.body.allocator, vec_addr.asInt());
                return self.ssa.emitInst(self.cur_bb, .{
                    .op = .intrinsic_op,
                    .flags = .{ .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.soa_vec_len),
                    .type_id = .usize_ty,
                    .operands = .{ .lhs = a_start, .rhs = 1 },
                }, tok);
            }
        }
        const len_proj = [1]MirProjection{.{ .kind = .slice_len, .payload = 0 }};
        if (self.isValidPlaceExtension(peeled_place, &len_proj)) {
            const len_place = try self.extendPlace(peeled_place, &len_proj);
            return self.loadPlaceValue(len_place, .usize_ty, tok, false);
        }
        const zero_idx = try self.body.appendConst(.{ .int_val = 0 });
        return self.ssa.emitInst(self.cur_bb, .{
            .op = .const_scalar,
            .flags = .{ .is_synthetic = true },
            .type_id = .usize_ty,
            .operands = .{ .lhs = zero_idx, .rhs = 0 },
        }, tok);
    }

    /// Emits `MirIntrinsicKind.subslice_make` over `peeled_place` (opening a Ghost borrow when `is_opening_borrow`).
    fn emitSubsliceFromPlace(
        self: *MirLowerer,
        peeled_place: PlaceId,
        unwrapped_base: TypeId,
        res_ty: TypeId,
        lo_val: MirValueId,
        hi_val: MirValueId,
        is_opening_borrow: bool,
        tok: TokenIndex,
    ) !MirValueId {
        const res_unwrapped = self.pool.unwrapUnderlyingType(res_ty);
        const is_mut = !res_unwrapped.isError() and self.pool.getNode(res_unwrapped).tag == .mut_ref_ty;
        if (is_opening_borrow) {
            const borrow_tok = try self.emitGhostOpen(
                if (is_mut) .ghost_access_inout else .ghost_access_let,
                peeled_place,
                .addr_borrow,
                tok,
            );
            try self.active_expr_borrows.append(self.allocator, borrow_tok);
        }

        const base_tag: type_system.TypeTag = if (unwrapped_base.isError()) .primitive else self.pool.getNode(unwrapped_base).tag;
        const base_val: MirValueId = if (unwrapped_base == .str_ty or
            base_tag == .slice_ty or base_tag == .soa_slice_ty or
            unionSliceElemType(self.pool, unwrapped_base) != null)
            try self.loadPlaceValue(peeled_place, unwrapped_base, tok, false)
        else blk_addr: {
            const ref_arr_ty = try self.pool.internRef(unwrapped_base, is_mut);
            break :blk_addr try self.ssa.emitInst(self.cur_bb, .{
                .op = .place_addr,
                .flags = .{ .is_synthetic = true },
                .type_id = ref_arr_ty,
                .operands = .{ .lhs = peeled_place.asInt(), .rhs = @intFromBool(is_mut) },
            }, tok);
        };

        const args_start: u32 = @intCast(self.body.extra_args.items.len);
        try self.body.extra_args.appendSlice(
            self.body.allocator,
            &[3]u32{ base_val.asInt(), lo_val.asInt(), hi_val.asInt() },
        );
        return self.ssa.emitInst(self.cur_bb, .{
            .op = .intrinsic_op,
            .flags = .{ .is_synthetic = true },
            .aux_u16 = @backingInt(MirIntrinsicKind.subslice_make),
            .type_id = res_ty,
            .operands = .{ .lhs = args_start, .rhs = 3 },
        }, tok);
    }

    /// Lowers `hir_slice_range` (`base[start..end]` / `base[start..=end]`, `SE-04` / `SE-05`).
    fn lowerSliceRangeNode(self: *MirLowerer, range_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(range_hir);
        const tok = node.origin_token;
        const base_hir = HirIndex.fromInt(node.data.lhs);
        if (node.data.rhs + 3 > self.hir_store.extra_data.items.len) {
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }
        const start_hir = HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs]);
        const end_hir = HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs + 1]);
        const is_inclusive = self.hir_store.extra_data.items[node.data.rhs + 2] != 0;

        const base_node = self.hir_store.getNode(base_hir);
        const res_unwrapped = self.pool.unwrapUnderlyingType(node.type_id);
        const is_mut = !res_unwrapped.isError() and self.pool.getNode(res_unwrapped).tag == .mut_ref_ty;
        const raw_base_place = if (is_mut and base_node.flags.category == .place_mut)
            try self.lowerMutPlace(base_hir)
        else
            try self.lowerPlace(base_hir);
        const peeled = try self.peelAutoDerefPlace(raw_base_place, base_node.type_id);
        const unwrapped_base = self.pool.unwrapUnderlyingType(peeled.pointee_ty);

        const len_val = try self.emitPlaceSequenceLength(peeled.place_id, unwrapped_base, tok);

        const lo_val: MirValueId = if (!start_hir.isNone())
            try self.lowerRValue(start_hir)
        else blk_zero: {
            const zero_c = try self.body.appendConst(.{ .int_val = 0 });
            break :blk_zero try self.ssa.emitInst(self.cur_bb, .{
                .op = .const_scalar,
                .flags = .{ .is_synthetic = true },
                .type_id = .usize_ty,
                .operands = .{ .lhs = zero_c, .rhs = 0 },
            }, tok);
        };

        const hi_val: MirValueId = if (!end_hir.isNone()) blk_hi: {
            const raw_end = try self.lowerRValue(end_hir);
            if (!is_inclusive) break :blk_hi raw_end;
            const one_c = try self.body.appendConst(.{ .int_val = 1 });
            const one_val = try self.ssa.emitInst(self.cur_bb, .{
                .op = .const_scalar,
                .flags = .{ .is_synthetic = true },
                .type_id = .usize_ty,
                .operands = .{ .lhs = one_c, .rhs = 0 },
            }, tok);
            break :blk_hi try self.ssa.emitInst(self.cur_bb, .{
                .op = .bin_op,
                .flags = .{ .has_trap_risk = true, .is_synthetic = true },
                .aux_u16 = @backingInt(BinOpKind.uadd_checked),
                .type_id = .usize_ty,
                .operands = .{ .lhs = raw_end.asInt(), .rhs = one_val.asInt() },
            }, tok);
        } else len_val;

        const chk_start: u32 = @intCast(self.body.extra_args.items.len);
        try self.body.extra_args.appendSlice(
            self.body.allocator,
            &[3]u32{ lo_val.asInt(), hi_val.asInt(), len_val.asInt() },
        );
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .intrinsic_op,
            .flags = .{ .has_side_effects = true, .has_trap_risk = true, .is_synthetic = true },
            .aux_u16 = @backingInt(MirIntrinsicKind.slice_range_check),
            .type_id = .unit_ty,
            .operands = .{ .lhs = chk_start, .rhs = 3 },
        }, tok);

        return self.emitSubsliceFromPlace(
            peeled.place_id,
            unwrapped_base,
            node.type_id,
            lo_val,
            hi_val,
            true,
            tok,
        );
    }

    /// Lowers `hir_if` into `cond_br` + `then_bb` + `else_bb` + Braun SSA `join_bb`.
    fn lowerIfNode(self: *MirLowerer, if_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(if_hir);
        const tok = node.origin_token;
        const cond_hir = HirIndex.fromInt(node.data.lhs);
        const then_hir = HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs]);
        const else_hir = HirIndex.fromInt(self.hir_store.extra_data.items[node.data.rhs + 1]);

        const outer_scope_depth = self.scope_depth;
        const cond_scope_depth = outer_scope_depth + 1;
        const cond_storage_base = self.storage_locals.items.len;
        const cond_borrow_base = self.active_expr_borrows.items.len;

        self.scope_depth = cond_scope_depth;
        const cond_val = try self.lowerRValue(cond_hir);
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
            self.scope_depth = outer_scope_depth;
            self.storage_locals.items.len = cond_storage_base;
            self.active_expr_borrows.items.len = cond_borrow_base;
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }
        try self.popAndCloseBorrowsTo(cond_borrow_base, tok);

        const cond_temps = try self.allocator.dupe(
            ActiveStorageLocal,
            self.storage_locals.items[cond_storage_base..],
        );
        defer self.allocator.free(cond_temps);
        if (cond_temps.len == 0) {
            self.scope_depth = outer_scope_depth;
        }

        const has_val = node.type_id != .unit_ty and node.type_id != .never_ty;
        const res_var = if (has_val)
            try self.allocTempLocal(node.type_id, tok, false, false)
        else
            LocalId.none;

        const then_bb = try self.ssa.createBlock(false, false);
        const else_bb = try self.ssa.createBlock(false, false);
        const join_bb = try self.ssa.createBlock(false, false);
        try self.emitCondBr(cond_val, then_bb, else_bb);
        try self.ssa.sealBlock(then_bb);
        try self.ssa.sealBlock(else_bb);

        var has_reachable_arm = false;

        // `then` branch:
        self.cur_bb = then_bb;
        const then_borrow_base = self.active_expr_borrows.items.len;
        const then_val = try self.lowerRValue(then_hir);
        if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
            try self.popAndCloseBorrowsTo(then_borrow_base, tok);
            if (has_val) try self.ssa.writeVariable(res_var.asInt(), self.cur_bb, then_val);
            if (cond_temps.len > 0) {
                try self.exitLexicalScopeCleanups(cond_scope_depth, true, tok);
            }
            try self.emitBr(join_bb, &.{});
            has_reachable_arm = true;
        } else {
            self.active_expr_borrows.items.len = then_borrow_base;
            if (cond_temps.len > 0) {
                try self.exitLexicalScopeCleanups(cond_scope_depth, false, tok);
            }
        }
        self.storage_locals.items.len = cond_storage_base;
        self.scope_depth = outer_scope_depth;

        // `else` branch:
        self.cur_bb = else_bb;
        if (cond_temps.len > 0) {
            var rev_idx = cond_temps.len;
            while (rev_idx > 0) {
                rev_idx -= 1;
                _ = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .ghost_storage_deinit,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = cond_temps[rev_idx].local_id.asInt(), .rhs = 0 },
                }, tok);
            }
        }
        const else_borrow_base = self.active_expr_borrows.items.len;
        const else_val = if (!else_hir.isNone())
            try self.lowerRValue(else_hir)
        else
            try self.emitUnitVal(tok);
        if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
            try self.popAndCloseBorrowsTo(else_borrow_base, tok);
            if (has_val) try self.ssa.writeVariable(res_var.asInt(), self.cur_bb, else_val);
            try self.emitBr(join_bb, &.{});
            has_reachable_arm = true;
        } else {
            self.active_expr_borrows.items.len = else_borrow_base;
        }

        try self.ssa.sealBlock(join_bb);
        if (!has_reachable_arm) {
            self.cur_bb = join_bb;
            self.ssa.setTerminator(join_bb, .{ .kind = .unreachable_term });
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }

        self.cur_bb = join_bb;
        if (has_val) {
            return self.ssa.readVariable(res_var.asInt(), join_bb);
        }
        return self.emitUnitVal(tok);
    }

    /// Lowers `hir_loop` using an unsealed Braun loop header `header_bb` sealed after body back-edges.
    fn lowerLoopNode(self: *MirLowerer, loop_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(loop_hir);
        const tok = node.origin_token;
        const body_hir = HirIndex.fromInt(node.data.lhs);
        const loop_id = node.data.rhs;

        const has_val = node.type_id != .unit_ty and node.type_id != .never_ty;
        const break_var = if (has_val)
            try self.allocTempLocal(node.type_id, tok, false, false)
        else
            LocalId.none;

        const header_bb = try self.ssa.createBlock(false, false);
        const exit_bb = try self.ssa.createBlock(false, false);
        try self.emitBr(header_bb, &.{});

        self.loop_depth += 1;
        try self.loop_stack.append(self.allocator, .{
            .loop_id = loop_id,
            .header_bb = header_bb,
            .exit_bb = exit_bb,
            .break_var_id = if (has_val) break_var.asInt() else NONE_U32,
            .outer_scope_depth = self.scope_depth,
            .loop_depth = self.loop_depth,
            .outer_borrow_depth = self.active_expr_borrows.items.len,
        });

        self.cur_bb = header_bb;
        const iter_borrow_base = self.active_expr_borrows.items.len;
        _ = try self.lowerRValue(body_hir);
        var latch_bb = header_bb;
        if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
            latch_bb = self.cur_bb;
            try self.popAndCloseBorrowsTo(iter_borrow_base, tok);
            try self.emitBr(header_bb, &.{});
        } else {
            self.active_expr_borrows.items.len = iter_borrow_base;
            const preds = self.ssa.blocks_scratch.items[header_bb.asInt()].preds.items;
            if (preds.len > 1) {
                const last_edge_id = preds[preds.len - 1];
                latch_bb = self.body.extra_edges.items[last_edge_id.asInt()].src_bb;
            }
        }

        if (self.hir_store.loop_contracts.get(loop_id)) |contract_meta| {
            try self.body.loop_contracts.append(self.body.allocator, .{
                .header_bb = header_bb,
                .latch_bb = latch_bb,
                .meta = contract_meta,
            });
        }

        _ = self.loop_stack.pop();
        self.loop_depth -= 1;

        // All back-edges and `continue` edges into `header_bb` are now wired; seal `header_bb` & `exit_bb`:
        try self.ssa.sealBlock(header_bb);
        try self.ssa.sealBlock(exit_bb);

        self.cur_bb = exit_bb;
        if (self.ssa.blocks_scratch.items[exit_bb.asInt()].preds.items.len == 0) {
            self.ssa.setTerminator(exit_bb, .{ .kind = .unreachable_term });
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }
        if (has_val) {
            return self.ssa.readVariable(break_var.asInt(), exit_bb);
        }
        return self.emitUnitVal(tok);
    }

    /// Looks up the active `LoopTargets` matching `target_loop_id` (or innermost loop when `0`/`NONE_U32`).
    fn findLoopTargets(self: *const MirLowerer, target_loop_id: u32) ?LoopTargets {
        if (self.loop_stack.items.len == 0) return null;
        var idx = self.loop_stack.items.len;
        while (idx > 0) {
            idx -= 1;
            if (self.loop_stack.items[idx].loop_id == target_loop_id) {
                return self.loop_stack.items[idx];
            }
        }
        return self.loop_stack.items[self.loop_stack.items.len - 1];
    }

    /// Lowers `hir_break`: evaluates optional break value, closes loop borrows & `defer`s, jumps to `exit_bb`.
    fn lowerBreakNode(self: *MirLowerer, break_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(break_hir);
        const tok = node.origin_token;
        const target_loop_id = node.data.lhs;
        const val_hir = HirIndex.fromInt(node.data.rhs);

        const break_val = if (!val_hir.isNone())
            try self.lowerRValue(val_hir)
        else
            MirValueId.none;

        if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
            if (self.findLoopTargets(target_loop_id)) |targets| {
                if (targets.break_var_id != NONE_U32 and !break_val.isNone()) {
                    try self.ssa.writeVariable(targets.break_var_id, self.cur_bb, break_val);
                }
                try self.emitBorrowEndsAboveDepth(targets.outer_borrow_depth, tok);
                try self.emitInlineNormalCleanupsAbove(targets.outer_scope_depth, tok);
                try self.emitBr(targets.exit_bb, &.{});
            }
        }
        return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
    }

    /// Looks up the active `FsmMatchTargets` matching `target_fsm_id` (`SE-23`).
    fn findFsmTargets(self: *const MirLowerer, target_fsm_id: u32) ?FsmMatchTargets {
        if (self.fsm_stack.items.len == 0) return null;
        var idx = self.fsm_stack.items.len;
        while (idx > 0) {
            idx -= 1;
            if (self.fsm_stack.items[idx].fsm_id == target_fsm_id) {
                return self.fsm_stack.items[idx];
            }
        }
        return self.fsm_stack.items[self.fsm_stack.items.len - 1];
    }

    /// Lowers `hir_continue`: closes loop-body borrows & `defer`s, jumps to unsealed `header_bb` or FSM `dispatch_bb`.
    fn lowerContinueNode(self: *MirLowerer, cont_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(cont_hir);
        const tok = node.origin_token;
        const target_loop_id = node.data.lhs;

        if ((target_loop_id & hir.LABELED_MATCH_CONTINUE_FLAG) != 0) {
            const target_fsm_id = target_loop_id & ~hir.LABELED_MATCH_CONTINUE_FLAG;
            const val_hir = HirIndex.fromInt(node.data.rhs);
            const next_val = if (!val_hir.isNone())
                try self.lowerRValue(val_hir)
            else
                try self.emitUnitVal(tok);
            if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                if (self.findFsmTargets(target_fsm_id)) |fsm_targets| {
                    try self.emitBorrowEndsAboveDepth(fsm_targets.outer_borrow_depth, tok);
                    try self.emitInlineNormalCleanupsAbove(fsm_targets.outer_scope_depth, tok);
                    const set_tok = try self.emitGhostOpen(
                        .ghost_access_set,
                        fsm_targets.scrut_place,
                        .scoped_projection,
                        tok,
                    );
                    try self.emitZeroPadIfRequired(fsm_targets.scrut_place, fsm_targets.scrut_ty, tok);
                    _ = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .place_store,
                        .flags = .{ .has_side_effects = true, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .operands = .{
                            .lhs = fsm_targets.scrut_place.asInt(),
                            .rhs = next_val.asInt(),
                        },
                    }, tok);
                    try self.emitGhostEnd(set_tok, tok);
                    try self.emitBr(fsm_targets.dispatch_bb, &.{});
                }
            }
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }

        if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
            if (self.findLoopTargets(target_loop_id)) |targets| {
                try self.emitBorrowEndsAboveDepth(targets.outer_borrow_depth, tok);
                try self.emitInlineNormalCleanupsAbove(targets.outer_scope_depth, tok);
                try self.emitBr(targets.header_bb, &.{});
            }
        }
        return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
    }

    // --------- Explicit Signed / Unsigned / Float Opcodes ---------

    /// Unwraps `distinct`, `.bit_field_ty`, and backed `.enum_ty` to their underlying scalar carrier `TypeId`.
    fn unwrapScalarCarrierType(self: *const MirLowerer, ty: TypeId) TypeId {
        var cur = self.pool.unwrapUnderlyingType(ty);
        if (cur.isError()) return cur;
        const node = self.pool.getNode(cur);
        if (node.tag == .bit_field_ty) {
            cur = self.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
        } else if (node.tag == .enum_ty) {
            if (self.pool.getEnumBackingIntType(cur)) |backing_int| {
                cur = self.pool.unwrapUnderlyingType(backing_int);
            }
        }
        return cur;
    }

    /// Unwraps `distinct`, `ref_ty`, `mut_ref_ty`, and `raw_ptr_ty` wrappers to the underlying value type.
    fn unwrapAllRefsType(self: *const MirLowerer, initial_ty: TypeId) TypeId {
        var cur = self.pool.unwrapUnderlyingType(initial_ty);
        var depth: usize = 0;
        while (!cur.isError() and depth < 16) : (depth += 1) {
            const node = self.pool.getNode(cur);
            if (node.tag == .ref_ty or node.tag == .mut_ref_ty or node.tag == .raw_ptr_ty) {
                cur = self.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            } else {
                break;
            }
        }
        return cur;
    }

    /// Returns `true` if `ty` unwraps to `f32` or `f64`.
    fn isFloatType(self: *const MirLowerer, ty: TypeId) bool {
        const unwrapped = self.pool.unwrapUnderlyingType(ty);
        return unwrapped == .f32_ty or unwrapped == .f64_ty or unwrapped == .untyped_float_ty;
    }

    /// Returns `true` if `ty` unwraps to a signed two's-complement integer (`i8 .. i128`, `isize`).
    fn isSignedIntType(self: *const MirLowerer, ty: TypeId) bool {
        const unwrapped = self.unwrapScalarCarrierType(ty);
        return switch (unwrapped) {
            .i8_ty, .i16_ty, .i32_ty, .i64_ty, .i128_ty, .isize_ty, .untyped_int_ty => true,
            else => false,
        };
    }

    /// Returns the scalar bit width of `ty` under `self.body.target_layout`.
    fn scalarBitWidth(self: *const MirLowerer, ty: TypeId) u32 {
        const unwrapped = self.unwrapScalarCarrierType(ty);
        const ptr_bits = @as(u32, self.body.target_layout.ptr_byte_size) * 8;
        return switch (unwrapped) {
            .bool_ty, .i8_ty, .u8_ty => 8,
            .i16_ty, .u16_ty => 16,
            .i32_ty, .u32_ty, .f32_ty, .char_ty, .untyped_int_ty => 32,
            .i64_ty, .u64_ty, .f64_ty, .untyped_float_ty => 64,
            .i128_ty, .u128_ty => 128,
            .isize_ty, .usize_ty => ptr_bits,
            else => ptr_bits,
        };
    }

    /// Maps `(HirBinaryOp, operand_ty)` to an explicit signed/unsigned/float `BinOpKind`.
    fn selectMirBinOp(
        self: *const MirLowerer,
        hir_op: hir.HirBinaryOp,
        operand_ty: TypeId,
    ) BinOpKind {
        const is_float = self.isFloatType(operand_ty);
        const is_signed = self.isSignedIntType(operand_ty);
        return switch (hir_op) {
            .add => if (is_float) .fadd else if (is_signed) .sadd_checked else .uadd_checked,
            .sub => if (is_float) .fsub else if (is_signed) .ssub_checked else .usub_checked,
            .mul => if (is_float) .fmul else if (is_signed) .smul_checked else .umul_checked,
            .div => if (is_float) .fdiv else if (is_signed) .sdiv_checked else .udiv_checked,
            .rem => if (is_float) .frem else if (is_signed) .srem_checked else .urem_checked,
            .wrap_add => .add_wrap,
            .wrap_sub => .sub_wrap,
            .wrap_mul => .mul_wrap,
            .sat_add => if (is_signed) .sadd_sat else .uadd_sat,
            .sat_sub => if (is_signed) .ssub_sat else .usub_sat,
            .sat_mul => if (is_signed) .smul_sat else .umul_sat,
            .bit_and => .bit_and,
            .bit_or => .bit_or,
            .bit_xor => .bit_xor,
            .shl => .shl_checked,
            .shr => if (is_signed) .ashr_checked else .lshr_checked,
            .eq => .eq,
            .ne => .ne,
            .lt => if (is_float) .flt else if (is_signed) .slt else .ult,
            .le => if (is_float) .fle else if (is_signed) .sle else .ule,
            .gt => if (is_float) .fgt else if (is_signed) .sgt else .ugt,
            .ge => if (is_float) .fge else if (is_signed) .sge else .uge,
            .logical_and => .bit_and,
            .logical_or => .bit_or,
        };
    }

    /// Maps `(HirCastKind, src_ty, dst_ty)` to an explicit `UnaryOpKind` (`null` for identity `copy_val`).
    fn selectMirCastOp(
        self: *const MirLowerer,
        cast_kind: hir.HirCastKind,
        src_ty: TypeId,
        dst_ty: TypeId,
    ) ?UnaryOpKind {
        return switch (cast_kind) {
            .distinct_unwrap, .distinct_wrap, .ref_coerce => null,
            .noop => blk_noop: {
                const unwrapped_src = self.pool.unwrapUnderlyingType(src_ty);
                const unwrapped_dst = self.pool.unwrapUnderlyingType(dst_ty);
                if (unwrapped_src != unwrapped_dst and
                    (unwrapped_src == .str_ty or unionSliceElemType(self.pool, unwrapped_src) != null))
                {
                    break :blk_noop .bitcast_op;
                }
                break :blk_noop null;
            },
            .ptr_cast, .array_to_slice => .ptr_cast,
            .int_to_int => blk: {
                const unwrapped_src = self.pool.unwrapUnderlyingType(src_ty);
                const carrier_dst = self.unwrapScalarCarrierType(dst_ty);
                const is_dst_int = switch (carrier_dst) {
                    .i8_ty,
                    .u8_ty,
                    .i16_ty,
                    .u16_ty,
                    .i32_ty,
                    .u32_ty,
                    .i64_ty,
                    .u64_ty,
                    .i128_ty,
                    .u128_ty,
                    .isize_ty,
                    .usize_ty,
                    .untyped_int_ty,
                    => true,
                    else => false,
                };
                if (unwrapped_src == .bool_ty and is_dst_int) {
                    break :blk .int_zext;
                }
                const src_bits = self.scalarBitWidth(src_ty);
                const dst_bits = self.scalarBitWidth(dst_ty);
                if (dst_bits < src_bits) break :blk .int_trunc;
                if (dst_bits > src_bits) {
                    break :blk if (self.isSignedIntType(src_ty)) .int_sext else .int_zext;
                }
                break :blk if (src_ty == dst_ty) null else .bitcast_op;
            },
            .int_to_float => if (self.isSignedIntType(src_ty)) .int_to_float_signed else .int_to_float_unsigned,
            .float_to_int => if (self.isSignedIntType(dst_ty)) .float_to_int_signed else .float_to_int_unsigned,
            .float_to_float => blk: {
                const src_bits = self.scalarBitWidth(src_ty);
                const dst_bits = self.scalarBitWidth(dst_ty);
                if (dst_bits > src_bits) break :blk .float_promote;
                if (dst_bits < src_bits) break :blk .float_demote;
                break :blk if (src_ty == dst_ty) null else .float_promote;
            },
        };
    }

    // ---------- Maranget + Jacobs Decision-Tree Lowering ----------

    /// Pending variable capture accumulated while specializing a `MatrixRow`.
    const PatBinding = struct {
        /// Target `HirStore` local slot ID.
        hir_local_id: u32,
        /// Scrutinee sub-place holding the matched value.
        place_id: PlaceId,
        /// Concrete `TypeId` of the bound sub-pattern.
        val_ty: TypeId,
        /// `true` if captured by reference (`ref x` / `ref mut x`).
        is_ref: bool,
        /// `true` if captured as mutable reference or mutable slot.
        is_mut: bool,
        /// `true` if captured via `..rest` slice/array pattern subslice (`[prefix.., ..rest, ..suffix]`).
        is_subslice: bool = false,
        /// Constant leading element offset (`sp.prefix_len`) when `is_subslice` is `true`.
        subslice_lo: u32 = 0,
        /// Constant trailing element count (`sp.suffix_len`) subtracted from `len` when `is_subslice` is `true`.
        subslice_hi_from_end: u32 = 0,
    };

    /// Single row inside the Maranget pattern matrix (`DR-13` §4.1).
    const MatrixRow = struct {
        /// Per-column `HirPat` index (`NONE_U32` denotes an irrefutable wildcard `_`).
        pats: []u32,
        /// Deferred bindings accumulated from stripped `.bind` patterns along this row.
        bindings: []PatBinding,
        /// Target arm index (`0 .. arms.len - 1`) sharing `arm_blocks[arm_idx]`.
        arm_idx: u32,
    };

    /// Arm-scoped `ref` / `ref mut` borrow specification opened on entry to `arm_blocks[arm_idx]`.
    const ArmRefSpec = struct {
        /// Bound `HirStore` local ID so duplicate rows from `or_pat` merge cleanly.
        hir_local_id: u32,
        /// Borrowed scrutinee (or sub-place) `PlaceId` for `V4` tracking.
        place_id: PlaceId,
        /// `true` for `ref mut` (`ghost_access_inout`), `false` for `ref` (`ghost_access_let`).
        is_mut: bool,
    };

    /// Shared per-`match` compilation state threaded through Maranget matrix specialization.
    const MatchCompileCtx = struct {
        /// Arena allocator scoped to this `lowerMatchExpr` invocation.
        m_alloc: std.mem.Allocator,
        /// Lowered `HirMatchArm` slice.
        arms: []const HirMatchArm,
        /// Pre-allocated target basic block per arm.
        arm_blocks: []const MirBlockId,
        /// Tracks whether at least one decision-tree leaf branched to `arm_blocks[arm_i]`.
        arm_reached: []bool,
        /// Accumulated `ref` / `ref mut` borrows to open at the start of `arm_blocks[arm_i]`.
        arm_ref_specs: []std.ArrayListUnmanaged(ArmRefSpec),
        /// Root scrutinee `PlaceId` used when an `or_pat` binds the same `ref` local to distinct sub-places.
        scrut_place: PlaceId,
        /// Static `TypeId` of `scrut_place`.
        scrut_ty: TypeId,
        /// Optional per-arm pattern-bound storage locals for labeled `fsm: match` (`SE-23`).
        arm_storage_locals: ?[]std.ArrayListUnmanaged(LocalId) = null,
    };

    /// Disjoint elementary integer/char interval `[low ..= high]` (`DR-13` §4.1.5).
    const DisjointInterval = struct {
        /// Inclusive lower bound.
        low: i128,
        /// Inclusive upper bound.
        high: i128,
    };

    /// Compares two pattern range bounds under `u128` (when `is_u128`) or signed `i128` order.
    fn isIntBoundLess(is_u128: bool, lhs_bound: i128, rhs_bound: i128) bool {
        if (is_u128) {
            return @as(u128, @bitCast(lhs_bound)) < @as(u128, @bitCast(rhs_bound));
        }
        return lhs_bound < rhs_bound;
    }

    /// Compares `lhs_bound <= rhs_bound` under `u128` (when `is_u128`) or signed `i128` order.
    fn isIntBoundLessOrEq(is_u128: bool, lhs_bound: i128, rhs_bound: i128) bool {
        return lhs_bound == rhs_bound or isIntBoundLess(is_u128, lhs_bound, rhs_bound);
    }

    /// Records arm-scoped `ref` / `ref mut` `PatBinding`s for `arm_idx`, merging distinct `or_pat` sub-places.
    fn recordArmRefBindings(
        self: *MirLowerer,
        ctx: *const MatchCompileCtx,
        arm_idx: u32,
        bindings: []const PatBinding,
    ) !void {
        for (bindings) |binding| {
            const is_subslice_ref = blk_sub: {
                if (!binding.is_subslice) break :blk_sub false;
                const lid = self.mapHirLocal(binding.hir_local_id);
                if (lid.isNone()) break :blk_sub false;
                const rest_ty = self.pool.unwrapUnderlyingType(self.body.locals.items[lid.asInt()].type_id);
                if (rest_ty.isError()) break :blk_sub false;
                const rest_tag = self.pool.getNode(rest_ty).tag;
                break :blk_sub rest_tag == .ref_ty or rest_tag == .mut_ref_ty;
            };
            if (!binding.is_ref and !is_subslice_ref) continue;

            // Strip `.index` projections so `arm_blocks[arm_idx]` never references block-local index SSA values:
            var borrow_place = binding.place_id;
            if (borrow_place.asInt() < self.body.places.items.len) {
                const projs = self.body.getPlaceProjections(borrow_place);
                for (projs, 0..) |proj, step_i| {
                    if (proj.kind == .index) {
                        const base_lid = LocalId.fromInt(self.body.places.items[borrow_place.asInt()].base);
                        borrow_place = try self.makePlace(base_lid, projs[0..step_i]);
                        break;
                    }
                }
            }

            var has_merged = false;
            for (ctx.arm_ref_specs[arm_idx].items) |*existing| {
                if (existing.hir_local_id == binding.hir_local_id) {
                    if (existing.place_id != borrow_place) {
                        existing.place_id = ctx.scrut_place;
                    }
                    existing.is_mut = existing.is_mut or binding.is_mut;
                    has_merged = true;
                    break;
                }
            }
            if (!has_merged) {
                try ctx.arm_ref_specs[arm_idx].append(ctx.m_alloc, .{
                    .hir_local_id = binding.hir_local_id,
                    .place_id = borrow_place,
                    .is_mut = binding.is_mut,
                });
            }
        }
    }

    /// Lowers `hir_match` via Maranget + Jacobs pattern-matrix compilation (`DR-13` §4.1).
    fn lowerMatchExpr(self: *MirLowerer, match_hir: HirIndex) anyerror!MirValueId {
        const node = self.hir_store.getNode(match_hir);
        const tok = node.origin_token;
        const scrut_hir = HirIndex.fromInt(node.data.lhs);
        const arm_start = self.hir_store.extra_data.items[node.data.rhs];
        const arm_len = self.hir_store.extra_data.items[node.data.rhs + 1];
        const arms = self.hir_store.match_arms.items[arm_start .. arm_start + arm_len];
        const is_destructuring_let = self.isDestructuringLetMatch(node);
        const fsm_meta_opt = self.hir_store.labeled_matches.get(match_hir.asInt());

        // [1] Materialize scrutinee into an addressable `PlaceId` so sub-places can project & downcast:
        const scrut_borrow_base = self.active_expr_borrows.items.len;
        const scrut_node = self.hir_store.getNode(scrut_hir);
        const scrut_place = blk: {
            if (fsm_meta_opt == null and
                (scrut_node.flags.category == .place_imm or scrut_node.flags.category == .place_mut))
            {
                break :blk try self.lowerPlace(scrut_hir);
            }
            const scrut_val = try self.lowerRValue(scrut_hir);
            if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                self.active_expr_borrows.items.len = scrut_borrow_base;
                return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
            }
            const scrut_lid = try self.allocTempLocal(scrut_node.type_id, tok, true, false);
            const tmp_place = try self.makePlace(scrut_lid, &.{});
            try self.markStorageInit(scrut_lid, tok);
            _ = try self.ssa.emitInst(self.cur_bb, .{
                .op = .place_store,
                .flags = .{ .has_side_effects = true, .is_synthetic = true },
                .type_id = .unit_ty,
                .operands = .{ .lhs = tmp_place.asInt(), .rhs = scrut_val.asInt() },
            }, tok);
            break :blk tmp_place;
        };
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
            self.active_expr_borrows.items.len = scrut_borrow_base;
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }
        const is_closing_scrut_early = (fsm_meta_opt != null or scrut_node.flags.category == .rvalue) and
            !self.hasTypeRegions(scrut_node.type_id);
        if (is_closing_scrut_early) {
            try self.popAndCloseBorrowsTo(scrut_borrow_base, tok);
        }

        if (arms.len == 0) {
            self.ssa.setTerminator(self.cur_bb, .{ .kind = .unreachable_term });
            self.active_expr_borrows.items.len = scrut_borrow_base;
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }

        // Use a dedicated arena for temporary Maranget matrix slices freed on exit:
        var matrix_arena = std.heap.ArenaAllocator.init(self.allocator);
        defer matrix_arena.deinit();
        const m_alloc = matrix_arena.allocator();

        // [2] Pre-create one shared `^arm_i` block per `HirMatchArm` (`or_pat`s share `^arm_i`!):
        const arm_blocks = try m_alloc.alloc(MirBlockId, arms.len);
        const arm_reached = try m_alloc.alloc(bool, arms.len);
        const arm_ref_specs = try m_alloc.alloc(std.ArrayListUnmanaged(ArmRefSpec), arms.len);
        @memset(arm_reached, false);
        for (0..arms.len) |arm_i| {
            arm_blocks[arm_i] = try self.ssa.createBlock(false, false);
            arm_ref_specs[arm_i] = .empty;
        }

        const outer_scope_depth = self.scope_depth;
        const saved_real_block_depth = self.enclosing_real_block_depth;
        var fsm_dispatch_bb: MirBlockId = .none;
        var arm_storage_locals: ?[]std.ArrayListUnmanaged(LocalId) = null;
        defer if (arm_storage_locals) |asl| {
            for (asl) |*list| list.deinit(self.allocator);
        };

        if (fsm_meta_opt) |fsm_meta| {
            const match_arm_depth = outer_scope_depth + 1;
            self.scope_depth = match_arm_depth;
            self.enclosing_real_block_depth = match_arm_depth;
            const asl = try m_alloc.alloc(std.ArrayListUnmanaged(LocalId), arms.len);
            for (0..arms.len) |arm_i| asl[arm_i] = .empty;
            arm_storage_locals = asl;

            fsm_dispatch_bb = try self.ssa.createBlock(false, false);
            try self.emitBr(fsm_dispatch_bb, &.{});
            self.cur_bb = fsm_dispatch_bb;
            try self.fsm_stack.append(self.allocator, .{
                .fsm_id = fsm_meta.fsm_id & ~hir.LABELED_MATCH_CONTINUE_FLAG,
                .dispatch_bb = fsm_dispatch_bb,
                .scrut_place = scrut_place,
                .scrut_ty = scrut_node.type_id,
                .outer_scope_depth = outer_scope_depth,
                .outer_borrow_depth = self.active_expr_borrows.items.len,
            });
        }

        // [3] Build initial 1-column matrix expanding top-level `or_pat` alternatives in order:
        var initial_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
        for (arms, 0..) |arm, arm_i| {
            try self.appendExpandedOrRows(
                m_alloc,
                arm.pat_idx,
                @intCast(arm_i),
                &initial_rows,
            );
        }

        const init_cols = try m_alloc.alloc(PlaceId, 1);
        init_cols[0] = scrut_place;
        const init_tys = try m_alloc.alloc(TypeId, 1);
        init_tys[0] = scrut_node.type_id;

        const match_ctx = MatchCompileCtx{
            .m_alloc = m_alloc,
            .arms = arms,
            .arm_blocks = arm_blocks,
            .arm_reached = arm_reached,
            .arm_ref_specs = arm_ref_specs,
            .scrut_place = scrut_place,
            .scrut_ty = scrut_node.type_id,
            .arm_storage_locals = arm_storage_locals,
        };

        self.decision_node_count = 0;
        try self.compileDecisionMatrix(
            &match_ctx,
            init_cols,
            init_tys,
            initial_rows.items,
            tok,
        );

        // [4] Seal all `^arm_i` blocks, lower reachable arm bodies, and join at `join_bb`:
        const has_val = node.type_id != .unit_ty and node.type_id != .never_ty;
        const res_var = if (has_val)
            try self.allocTempLocal(node.type_id, tok, false, false)
        else
            LocalId.none;
        const join_bb = try self.ssa.createBlock(false, false);
        var has_any_reaches_join = false;
        var has_any_arm_ref = false;
        var has_any_mut_arm_ref = false;
        var destructuring_kept_borrows: std.ArrayListUnmanaged(MirValueId) = .empty;

        for (arms, 0..) |arm, arm_i| {
            try self.ssa.sealBlock(arm_blocks[arm_i]);
            if (!arm_reached[arm_i] or
                self.ssa.blocks_scratch.items[arm_blocks[arm_i].asInt()].preds.items.len == 0)
            {
                self.ssa.setTerminator(arm_blocks[arm_i], .{ .kind = .unreachable_term });
                continue;
            }
            self.cur_bb = arm_blocks[arm_i];
            if (arm_storage_locals) |asl| {
                const match_arm_depth = outer_scope_depth + 1;
                for (asl[arm_i].items) |bound_lid| {
                    try self.storage_locals.append(self.allocator, .{
                        .local_id = bound_lid,
                        .scope_depth = match_arm_depth,
                        .loop_depth = self.loop_depth,
                        .origin_token = arm.origin_token,
                    });
                }
            }
            const arm_borrow_base = self.active_expr_borrows.items.len;
            for (arm_ref_specs[arm_i].items) |spec| {
                has_any_arm_ref = true;
                if (spec.is_mut) has_any_mut_arm_ref = true;
                const ref_tok = try self.emitGhostOpen(
                    if (spec.is_mut) .ghost_access_inout else .ghost_access_let,
                    spec.place_id,
                    .addr_borrow,
                    arm.origin_token,
                );
                try self.active_expr_borrows.append(self.allocator, ref_tok);
            }
            const arm_val = try self.lowerRValue(arm.body_hir);
            if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                if (is_destructuring_let and arm_i == 0) {
                    try destructuring_kept_borrows.appendSlice(
                        m_alloc,
                        self.active_expr_borrows.items[arm_borrow_base..],
                    );
                    self.active_expr_borrows.items.len = arm_borrow_base;
                    if (arm_storage_locals != null) {
                        try self.exitLexicalScopeCleanups(outer_scope_depth + 1, true, arm.origin_token);
                    }
                    if (has_val) try self.ssa.writeVariable(res_var.asInt(), self.cur_bb, arm_val);
                    try self.emitBr(join_bb, &.{});
                    has_any_reaches_join = true;
                } else if (is_destructuring_let and arm_i > 0) {
                    try self.popAndCloseBorrowsTo(arm_borrow_base, arm.origin_token);
                    if (arm_storage_locals != null) {
                        try self.exitLexicalScopeCleanups(outer_scope_depth + 1, false, arm.origin_token);
                    }
                    self.ssa.setTerminator(self.cur_bb, .{ .kind = .unreachable_term });
                } else {
                    try self.popAndCloseBorrowsTo(arm_borrow_base, arm.origin_token);
                    if (arm_storage_locals != null) {
                        try self.exitLexicalScopeCleanups(outer_scope_depth + 1, true, arm.origin_token);
                    }
                    if (has_val) try self.ssa.writeVariable(res_var.asInt(), self.cur_bb, arm_val);
                    try self.emitBr(join_bb, &.{});
                    has_any_reaches_join = true;
                }
            } else {
                self.active_expr_borrows.items.len = arm_borrow_base;
                if (arm_storage_locals != null) {
                    try self.exitLexicalScopeCleanups(outer_scope_depth + 1, false, arm.origin_token);
                }
            }
        }

        if (fsm_meta_opt != null) {
            _ = self.fsm_stack.pop();
            self.enclosing_real_block_depth = saved_real_block_depth;
            self.scope_depth = outer_scope_depth;
            try self.ssa.sealBlock(fsm_dispatch_bb);
        }

        try self.ssa.sealBlock(join_bb);
        self.cur_bb = join_bb;
        if (!has_any_reaches_join) {
            self.ssa.setTerminator(join_bb, .{ .kind = .unreachable_term });
            self.active_expr_borrows.items.len = scrut_borrow_base;
            return self.ssa.emitDefaultScalarInBlock(.fromInt(0), node.type_id);
        }

        if (is_destructuring_let) {
            try self.active_expr_borrows.appendSlice(self.allocator, destructuring_kept_borrows.items);
        } else if (!self.hasTypeRegions(node.type_id)) {
            if (!is_closing_scrut_early) {
                try self.popAndCloseBorrowsTo(scrut_borrow_base, tok);
            }
        } else if (has_any_arm_ref) {
            const join_ref_tok = try self.emitGhostOpen(
                if (has_any_mut_arm_ref) .ghost_access_inout else .ghost_access_let,
                scrut_place,
                .addr_borrow,
                tok,
            );
            try self.active_expr_borrows.append(self.allocator, join_ref_tok);
        }

        if (has_val) {
            return self.ssa.readVariable(res_var.asInt(), join_bb);
        }
        return self.emitUnitVal(tok);
    }

    /// Recursively flattens top-level `or_pat` trees into separate `MatrixRow`s sharing `arm_idx`.
    fn appendExpandedOrRows(
        self: *const MirLowerer,
        m_alloc: std.mem.Allocator,
        pat_idx: u32,
        arm_idx: u32,
        out_rows: *std.ArrayListUnmanaged(MatrixRow),
    ) !void {
        if (pat_idx != NONE_U32 and pat_idx < self.hir_store.patterns.items.len) {
            const pat = self.hir_store.patterns.items[pat_idx];
            if (pat.kind == .or_pat) {
                try self.appendExpandedOrRows(m_alloc, pat.kind.or_pat.lhs_pat, arm_idx, out_rows);
                try self.appendExpandedOrRows(m_alloc, pat.kind.or_pat.rhs_pat, arm_idx, out_rows);
                return;
            }
        }
        const row_pats = try m_alloc.alloc(u32, 1);
        row_pats[0] = pat_idx;
        try out_rows.append(m_alloc, .{
            .pats = row_pats,
            .bindings = &.{},
            .arm_idx = arm_idx,
        });
    }

    /// Returns `true` if sub-pattern `sub_idx` safely binds or unpacks any `@linear` value without `_` drops.
    fn isNonWildcardLinearSubPat(self: *const MirLowerer, sub_idx: u32, depth: u8) bool {
        if (depth >= 32 or sub_idx == NONE_U32 or sub_idx >= self.hir_store.patterns.items.len) return false;
        const sub_pat = self.hir_store.patterns.items[sub_idx];
        if (sub_pat.type_id.isError() or
            type_system.classifyOwnershipTier(self.pool, self.sym_table, sub_pat.type_id) != .linear_tier)
        {
            return true;
        }
        return switch (sub_pat.kind) {
            .bind => |bind_pat| !bind_pat.is_ref,
            .at_pat => |ap| !ap.is_ref and self.isNonWildcardLinearSubPat(ap.sub_pat, depth + 1),
            .struct_pat, .tuple, .variant, .or_pat, .slice_pat => self.isCompleteLinearUnpackPat(sub_idx, depth + 1),
            else => false,
        };
    }

    /// Returns `true` if `pat_idx` structurally unpacks a `@linear` aggregate/sum by value without dropping `@linear` fields.
    fn isCompleteLinearUnpackPat(self: *const MirLowerer, pat_idx: u32, depth: u8) bool {
        if (depth >= 32 or pat_idx == NONE_U32 or pat_idx >= self.hir_store.patterns.items.len) return false;
        const pat = self.hir_store.patterns.items[pat_idx];
        switch (pat.kind) {
            .at_pat => |ap| {
                return !ap.is_ref and self.isCompleteLinearUnpackPat(ap.sub_pat, depth + 1);
            },
            .slice_pat => |sp| {
                if (sp.has_rest) return false;
                const unwrapped = self.pool.unwrapUnderlyingType(pat.type_id);
                if (unwrapped.isError()) return false;
                const ty_node = self.pool.getNode(unwrapped);
                if (ty_node.tag != .array_ty and ty_node.tag != .soa_array_ty) return false;
                if ((ty_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) != 0) return false;
                const sub_total = @as(u32, sp.prefix_len) + @as(u32, sp.suffix_len);
                if (sub_total != ty_node.rhs) return false;
                if (sp.prefix_start + sub_total > self.hir_store.extra_data.items.len) return false;
                for (self.hir_store.extra_data.items[sp.prefix_start .. sp.prefix_start + sub_total]) |sub_raw| {
                    if (!self.isNonWildcardLinearSubPat(sub_raw, depth + 1)) return false;
                }
                return true;
            },
            .struct_pat => |sp| {
                const unwrapped = self.pool.unwrapUnderlyingType(pat.type_id);
                if (unwrapped.isError()) return false;
                const ty_node = self.pool.getNode(unwrapped);
                if (ty_node.tag != .struct_ty and ty_node.tag != .union_ty) return false;
                const sym = self.sym_table.getSymbol(SymbolIndex.fromInt(ty_node.rhs)).*;
                if (sym.target_scope.isNone()) return true;

                var field_ord: u32 = 0;
                for (self.sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                    const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                    if (mem_sym.kind != .field_sym) continue;
                    defer field_ord += 1;
                    if (!mem_sym.type_id.isError() and
                        type_system.classifyOwnershipTier(self.pool, self.sym_table, mem_sym.type_id) == .linear_tier)
                    {
                        var matched_sub: ?u32 = null;
                        for (0..sp.field_len) |field_i| {
                            const pair_base = sp.field_start + @as(u32, @intCast(field_i * 2));
                            if (self.hir_store.extra_data.items[pair_base] == field_ord) {
                                matched_sub = self.hir_store.extra_data.items[pair_base + 1];
                                break;
                            }
                        }
                        const sub_pat_idx = matched_sub orelse return false;
                        if (!self.isNonWildcardLinearSubPat(sub_pat_idx, depth + 1)) return false;
                    }
                }
                return true;
            },
            .tuple => |tup| {
                if (tup.sub_len != self.countProductFields(pat.type_id)) return false;
                for (self.hir_store.extra_data.items[tup.sub_start .. tup.sub_start + tup.sub_len]) |sub_raw| {
                    if (!self.isNonWildcardLinearSubPat(sub_raw, depth + 1)) return false;
                }
                return true;
            },
            .variant => |vp| {
                for (self.hir_store.extra_data.items[vp.sub_start .. vp.sub_start + vp.sub_len]) |sub_raw| {
                    if (!self.isNonWildcardLinearSubPat(sub_raw, depth + 1)) return false;
                }
                return true;
            },
            .or_pat => |op| {
                return self.isCompleteLinearUnpackPat(op.lhs_pat, depth + 1) and
                    self.isCompleteLinearUnpackPat(op.rhs_pat, depth + 1);
            },
            else => return false,
        }
    }

    /// Emits `ghost_storage_move(scrut_place)` when `pat_idx` unpacks a `@linear` scrutinee completely by value.
    fn emitLinearUnpackMoveIfApplicable(
        self: *MirLowerer,
        scrut_place: PlaceId,
        scrut_ty: TypeId,
        pat_idx: u32,
        bindings: []const PatBinding,
        tok: TokenIndex,
    ) !void {
        if (scrut_place.asInt() >= self.body.places.items.len) return;
        if (self.isPlaceBehindSharedRef(scrut_place)) return;
        for (bindings) |binding| {
            if (binding.is_ref) return;
        }
        if (scrut_ty.isError() or
            type_system.classifyOwnershipTier(self.pool, self.sym_table, scrut_ty) != .linear_tier)
        {
            return;
        }
        if (!self.isCompleteLinearUnpackPat(pat_idx, 0)) return;

        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .ghost_storage_move,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = scrut_place.asInt(), .rhs = 0 },
        }, tok);
    }

    /// Recursively compiles `(col_places, col_types, raw_rows)` into a CFG decision tree (`DR-13` §4.1).
    fn compileDecisionMatrix(
        self: *MirLowerer,
        ctx: *const MatchCompileCtx,
        in_places: []const PlaceId,
        in_types: []const TypeId,
        in_rows: []const MatrixRow,
        tok: TokenIndex,
    ) anyerror!void {
        if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) return;

        self.decision_node_count += 1;
        if (self.decision_node_count > MAX_DECISION_NODES) {
            try self.ssa.reportResourceOverflow(
                "match decision tree exceeded `MAX_DECISION_NODES` (16,384)",
            );
            self.ssa.setTerminator(self.cur_bb, .{ .kind = .unreachable_term });
            return;
        }

        // [1] Empty matrix -> exhausted / unreachable leaf:
        if (in_rows.len == 0) {
            self.ssa.setTerminator(self.cur_bb, .{ .kind = .unreachable_term });
            return;
        }

        // [2] Normalize nested `or_pat`, `.bind`, `.wildcard`, `.tuple`, and `.struct_pat` columns:
        var col_places = in_places;
        var col_types = in_types;
        const rows = try self.normalizeDecisionMatrix(
            ctx.m_alloc,
            &col_places,
            &col_types,
            in_rows,
            tok,
        );

        if (rows.len == 0) {
            self.ssa.setTerminator(self.cur_bb, .{ .kind = .unreachable_term });
            return;
        }

        // [3] Check if top row `rows[0]` is all wildcards (`NONE_U32`):
        var is_top_all_wild = true;
        for (rows[0].pats) |pat_idx| {
            if (pat_idx != NONE_U32) {
                is_top_all_wild = false;
                break;
            }
        }
        if (is_top_all_wild) {
            const matched_row = rows[0];
            const arm = ctx.arms[matched_row.arm_idx];
            if (arm.guard_hir.isNone()) {
                self.active_fsm_arm_storage = if (ctx.arm_storage_locals) |asl| &asl[matched_row.arm_idx] else null;
                defer self.active_fsm_arm_storage = null;
                try self.emitPatternBindings(matched_row.bindings, true, false, arm.origin_token);
                try self.emitPartialVariantWildcardMoves(
                    col_places,
                    col_types,
                    matched_row.bindings,
                    arm.origin_token,
                );
                try self.emitLinearUnpackMoveIfApplicable(
                    ctx.scrut_place,
                    ctx.scrut_ty,
                    arm.pat_idx,
                    matched_row.bindings,
                    arm.origin_token,
                );
                try self.recordArmRefBindings(ctx, matched_row.arm_idx, matched_row.bindings);
                ctx.arm_reached[matched_row.arm_idx] = true;
                try self.emitBr(ctx.arm_blocks[matched_row.arm_idx], &.{});
                return;
            }

            // Guarded arm (`DR-13` §4.1.6): push `.match_guard` shared borrows onto
            // `active_expr_borrows` and bind with `is_in_guard = true` so `inout` opens only on hit:
            const guard_borrow_base = self.active_expr_borrows.items.len;
            for (matched_row.bindings) |binding| {
                const g_tok = try self.emitGhostOpen(
                    .ghost_access_let,
                    binding.place_id,
                    .match_guard,
                    arm.origin_token,
                );
                try self.active_expr_borrows.append(self.allocator, g_tok);
            }
            try self.emitPatternBindings(matched_row.bindings, false, true, arm.origin_token);

            const guard_val = try self.lowerRValue(arm.guard_hir);
            if (self.cur_bb.isNone() or self.ssa.isBlockTerminated(self.cur_bb)) {
                self.active_expr_borrows.items.len = guard_borrow_base;
                return;
            }
            try self.popAndCloseBorrowsTo(guard_borrow_base, arm.origin_token);

            const hit_bb = try self.ssa.createBlock(false, false);
            const miss_bb = try self.ssa.createBlock(false, false);
            try self.emitCondBr(guard_val, hit_bb, miss_bb);
            try self.ssa.sealBlock(hit_bb);
            try self.ssa.sealBlock(miss_bb);

            self.cur_bb = hit_bb;
            {
                self.active_fsm_arm_storage = if (ctx.arm_storage_locals) |asl| &asl[matched_row.arm_idx] else null;
                defer self.active_fsm_arm_storage = null;
                try self.emitPatternBindings(matched_row.bindings, true, false, arm.origin_token);
                try self.emitPartialVariantWildcardMoves(
                    col_places,
                    col_types,
                    matched_row.bindings,
                    arm.origin_token,
                );
                try self.emitLinearUnpackMoveIfApplicable(
                    ctx.scrut_place,
                    ctx.scrut_ty,
                    arm.pat_idx,
                    matched_row.bindings,
                    arm.origin_token,
                );
            }
            try self.recordArmRefBindings(ctx, matched_row.arm_idx, matched_row.bindings);
            ctx.arm_reached[matched_row.arm_idx] = true;
            try self.emitBr(ctx.arm_blocks[matched_row.arm_idx], &.{});

            self.cur_bb = miss_bb;
            return self.compileDecisionMatrix(
                ctx,
                col_places,
                col_types,
                rows[1..],
                tok,
            );
        }

        // [4] Select pivot column `pivot_col` using Jacobs' clause-frequency heuristic (`DR-13` §4.1.3):
        const pivot_col = self.selectJacobsPivotColumn(rows, col_places.len);
        const raw_pivot_place = col_places[pivot_col];
        const raw_pivot_ty = col_types[pivot_col];
        const peeled_pivot = try self.peelAutoDerefPlace(raw_pivot_place, raw_pivot_ty);
        const pivot_place = peeled_pivot.place_id;
        const pivot_ty = peeled_pivot.pointee_ty;

        // Dispatch specialization by first concrete pattern kind in `pivot_col`:
        const first_pat = self.hir_store.patterns.items[rows[0].pats[pivot_col]];
        switch (first_pat.kind) {
            .variant => try self.specializeVariantColumn(
                ctx,
                col_places,
                col_types,
                rows,
                pivot_col,
                pivot_place,
                pivot_ty,
                tok,
            ),
            .lit_bool => try self.specializeBoolColumn(
                ctx,
                col_places,
                col_types,
                rows,
                pivot_col,
                pivot_place,
                tok,
            ),
            .lit_int_range => try self.specializeIntRangeColumn(
                ctx,
                col_places,
                col_types,
                rows,
                pivot_col,
                pivot_place,
                pivot_ty,
                tok,
            ),
            .lit_float, .lit_str => try self.specializeScalarEqColumn(
                ctx,
                col_places,
                col_types,
                rows,
                pivot_col,
                pivot_place,
                pivot_ty,
                tok,
            ),
            .slice_pat => try self.specializeSliceColumn(
                ctx,
                col_places,
                col_types,
                rows,
                pivot_col,
                pivot_place,
                pivot_ty,
                tok,
            ),
            else => {
                self.ssa.setTerminator(self.cur_bb, .{ .kind = .unreachable_term });
            },
        }
    }

    /// Expands nested `or_pat`s, strips `.wildcard`/`.bind`s, and flattens product (`tuple`/`struct_pat`) columns.
    fn normalizeDecisionMatrix(
        self: *MirLowerer,
        m_alloc: std.mem.Allocator,
        col_places_io: *[]const PlaceId,
        col_types_io: *[]const TypeId,
        in_rows: []const MatrixRow,
        tok: TokenIndex,
    ) ![]MatrixRow {
        var cur_places = col_places_io.*;
        var cur_types = col_types_io.*;
        var cur_rows = try m_alloc.dupe(MatrixRow, in_rows);

        var has_changed = true;
        var guard_iters: usize = 0;
        while (has_changed and guard_iters < 64) : (guard_iters += 1) {
            has_changed = false;

            // (a) Expand any row containing an `or_pat` in any column:
            var expanded_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
            var has_expanded_or = false;
            for (cur_rows) |row| {
                var or_col: ?usize = null;
                for (row.pats, 0..) |pat_idx, col_i| {
                    if (pat_idx != NONE_U32 and pat_idx < self.hir_store.patterns.items.len and
                        self.hir_store.patterns.items[pat_idx].kind == .or_pat)
                    {
                        or_col = col_i;
                        break;
                    }
                }
                if (or_col) |split_col| {
                    has_expanded_or = true;
                    const or_data = self.hir_store.patterns.items[row.pats[split_col]].kind.or_pat;
                    const lhs_pats = try m_alloc.dupe(u32, row.pats);
                    lhs_pats[split_col] = or_data.lhs_pat;
                    const rhs_pats = try m_alloc.dupe(u32, row.pats);
                    rhs_pats[split_col] = or_data.rhs_pat;
                    try expanded_rows.append(m_alloc, .{
                        .pats = lhs_pats,
                        .bindings = row.bindings,
                        .arm_idx = row.arm_idx,
                    });
                    try expanded_rows.append(m_alloc, .{
                        .pats = rhs_pats,
                        .bindings = row.bindings,
                        .arm_idx = row.arm_idx,
                    });
                } else {
                    try expanded_rows.append(m_alloc, row);
                }
            }
            if (has_expanded_or) {
                cur_rows = expanded_rows.items;
                has_changed = true;
                continue;
            }

            // (b) Strip `.wildcard` and `.bind` patterns into `row.bindings` + `NONE_U32`:
            for (cur_rows) |*row| {
                for (row.pats, 0..) |*pat_slot, col_i| {
                    const pat_idx = pat_slot.*;
                    if (pat_idx == NONE_U32 or pat_idx >= self.hir_store.patterns.items.len) continue;
                    const pat = self.hir_store.patterns.items[pat_idx];
                    switch (pat.kind) {
                        .wildcard => {
                            pat_slot.* = NONE_U32;
                            has_changed = true;
                        },
                        .bind => |bind_pat| {
                            const new_binds = try m_alloc.alloc(PatBinding, row.bindings.len + 1);
                            @memcpy(new_binds[0..row.bindings.len], row.bindings);
                            new_binds[row.bindings.len] = .{
                                .hir_local_id = bind_pat.local_id,
                                .place_id = cur_places[col_i],
                                .val_ty = cur_types[col_i],
                                .is_ref = bind_pat.is_ref,
                                .is_mut = bind_pat.is_mut,
                            };
                            row.bindings = new_binds;
                            pat_slot.* = NONE_U32;
                            has_changed = true;
                        },
                        .at_pat => |ap| {
                            const new_binds = try m_alloc.alloc(PatBinding, row.bindings.len + 1);
                            @memcpy(new_binds[0..row.bindings.len], row.bindings);
                            new_binds[row.bindings.len] = .{
                                .hir_local_id = ap.local_id,
                                .place_id = cur_places[col_i],
                                .val_ty = cur_types[col_i],
                                .is_ref = ap.is_ref,
                                .is_mut = ap.is_mut,
                            };
                            row.bindings = new_binds;
                            pat_slot.* = ap.sub_pat;
                            has_changed = true;
                        },
                        else => {},
                    }
                }
            }
            if (has_changed) continue;

            // (c) Product flattening: flatten any column containing `.tuple` or `.struct_pat`:
            var prod_col: ?usize = null;
            for (0..cur_places.len) |col_i| {
                for (cur_rows) |row| {
                    const pat_idx = row.pats[col_i];
                    if (pat_idx == NONE_U32 or pat_idx >= self.hir_store.patterns.items.len) continue;
                    const pk = self.hir_store.patterns.items[pat_idx].kind;
                    if (pk == .tuple or pk == .struct_pat) {
                        prod_col = col_i;
                        break;
                    }
                }
                if (prod_col != null) break;
            }

            if (prod_col) |flat_col| {
                const peeled = try self.peelAutoDerefPlace(cur_places[flat_col], cur_types[flat_col]);
                const agg_ty = peeled.pointee_ty;
                const field_count = self.countProductFields(agg_ty);

                const next_col_len = cur_places.len - 1 + field_count;
                const next_places = try m_alloc.alloc(PlaceId, next_col_len);
                const next_types = try m_alloc.alloc(TypeId, next_col_len);

                @memcpy(next_places[0..flat_col], cur_places[0..flat_col]);
                @memcpy(next_types[0..flat_col], cur_types[0..flat_col]);
                for (0..field_count) |f_ord| {
                    const field_ty = self.resolveAggregateMemberType(agg_ty, @intCast(f_ord));
                    const field_proj = [1]MirProjection{.{ .kind = .field, .payload = @intCast(f_ord) }};
                    next_places[flat_col + f_ord] = if (self.isValidPlaceExtension(peeled.place_id, &field_proj))
                        try self.extendPlace(peeled.place_id, &field_proj)
                    else
                        try self.allocErrorFallbackPlace(field_ty, tok);
                    next_types[flat_col + f_ord] = field_ty;
                }
                @memcpy(next_places[flat_col + field_count ..], cur_places[flat_col + 1 ..]);
                @memcpy(next_types[flat_col + field_count ..], cur_types[flat_col + 1 ..]);

                for (cur_rows) |*row| {
                    const next_pats = try m_alloc.alloc(u32, next_col_len);
                    @memcpy(next_pats[0..flat_col], row.pats[0..flat_col]);
                    @memset(next_pats[flat_col .. flat_col + field_count], NONE_U32);
                    @memcpy(next_pats[flat_col + field_count ..], row.pats[flat_col + 1 ..]);

                    const cell_pat_idx = row.pats[flat_col];
                    if (cell_pat_idx != NONE_U32 and cell_pat_idx < self.hir_store.patterns.items.len) {
                        switch (self.hir_store.patterns.items[cell_pat_idx].kind) {
                            .tuple => |tup| {
                                const copy_n = @min(tup.sub_len, field_count);
                                for (0..copy_n) |sub_i| {
                                    next_pats[flat_col + sub_i] =
                                        self.hir_store.extra_data.items[tup.sub_start + sub_i];
                                }
                            },
                            .struct_pat => |sp| {
                                for (0..sp.field_len) |f_i| {
                                    const pair_base = sp.field_start + @as(u32, @intCast(f_i * 2));
                                    const ord = self.hir_store.extra_data.items[pair_base];
                                    const sub_pat = self.hir_store.extra_data.items[pair_base + 1];
                                    if (ord < field_count) {
                                        next_pats[flat_col + ord] = sub_pat;
                                    }
                                }
                            },
                            else => {},
                        }
                    }
                    row.pats = next_pats;
                }

                cur_places = next_places;
                cur_types = next_types;
                has_changed = true;
            }
        }

        col_places_io.* = cur_places;
        col_types_io.* = cur_types;
        return cur_rows;
    }

    /// Counts canonical fields/elements in a tuple or nominal struct `agg_ty`.
    fn countProductFields(self: *const MirLowerer, agg_ty: TypeId) usize {
        if (agg_ty.isError()) return 0;
        const unwrapped = self.pool.unwrapUnderlyingType(agg_ty);
        if (unwrapped == .source_loc_ty) return 4;
        if (unwrapped == .fmt_spec_ty) return 3;
        const node = self.pool.getNode(unwrapped);
        switch (node.tag) {
            .tuple_ty => return self.pool.getTupleElements(unwrapped).len,
            .struct_ty, .union_ty => {
                const sym = self.sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                if (sym.target_scope.isNone()) return 0;
                var count: usize = 0;
                for (self.sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                    if (self.sym_table.getSymbol(mem_idx).kind == .field_sym) count += 1;
                }
                return count;
            },
            else => return 0,
        }
    }

    /// Counts total variants in an `Option`, `Result`, or nominal `enum` (`null` if open/non-sum).
    fn countSumVariants(self: *const MirLowerer, sum_ty: TypeId) ?usize {
        if (sum_ty.isError()) return null;
        const unwrapped = self.pool.unwrapUnderlyingType(sum_ty);
        const node = self.pool.getNode(unwrapped);
        return switch (node.tag) {
            .optional_ty, .result_ty => 2,
            .enum_ty => blk: {
                const sym = self.sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                if (sym.target_scope.isNone()) break :blk 0;
                var count: usize = 0;
                for (self.sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                    if (self.sym_table.getSymbol(mem_idx).kind == .enum_variant_sym) count += 1;
                }
                break :blk count;
            },
            else => null,
        };
    }

    /// Selects the highest-scoring active column in `rows[0]` via Jacobs' clause-frequency heuristic.
    fn selectJacobsPivotColumn(
        self: *const MirLowerer,
        rows: []const MatrixRow,
        col_count: usize,
    ) usize {
        var best_col: usize = 0;
        var best_score: usize = 0;
        var has_found_any = false;

        for (0..col_count) |col_i| {
            if (rows[0].pats[col_i] == NONE_U32) continue;
            var active_clauses: usize = 0;
            for (rows) |row| {
                if (row.pats[col_i] != NONE_U32) active_clauses += 1;
            }
            if (!has_found_any or active_clauses > best_score) {
                has_found_any = true;
                best_col = col_i;
                best_score = active_clauses;
            }
        }
        _ = self;
        return best_col;
    }

    /// Materializes deferred `PatBinding`s into SSA variables or address-taken local slots.
    fn emitPatternBindings(
        self: *MirLowerer,
        bindings: []const PatBinding,
        is_move_allowed: bool,
        is_in_guard: bool,
        tok: TokenIndex,
    ) !void {
        for (bindings) |binding| {
            const lid = self.mapHirLocal(binding.hir_local_id);
            if (lid.isNone()) continue;
            const decl_depth = self.resolveLocalDeclScopeDepth(binding.hir_local_id);
            if (lid.asInt() < self.body.local_scope_depths.items.len) {
                self.body.local_scope_depths.items[lid.asInt()] =
                    @intCast(@min(@max(decl_depth, 1), std.math.maxInt(u16)));
            }
            const local_decl = self.body.locals.items[lid.asInt()];

            const bound_val = if (binding.is_subslice) blk_subslice: {
                const peeled = try self.peelAutoDerefPlace(binding.place_id, binding.val_ty);
                const unwrapped_seq = self.pool.unwrapUnderlyingType(peeled.pointee_ty);
                const len_val = try self.emitPlaceSequenceLength(peeled.place_id, unwrapped_seq, tok);
                const lo_c = try self.body.appendConst(.{ .int_val = @as(i128, binding.subslice_lo) });
                const lo_val = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .flags = .{ .is_synthetic = true },
                    .type_id = .usize_ty,
                    .operands = .{ .lhs = lo_c, .rhs = 0 },
                }, tok);
                const hi_val: MirValueId = if (binding.subslice_hi_from_end == 0)
                    len_val
                else blk_hi: {
                    const tail_c = try self.body.appendConst(.{ .int_val = @as(i128, binding.subslice_hi_from_end) });
                    const tail_val = try self.ssa.emitInst(self.cur_bb, .{
                        .op = .const_scalar,
                        .flags = .{ .is_synthetic = true },
                        .type_id = .usize_ty,
                        .operands = .{ .lhs = tail_c, .rhs = 0 },
                    }, tok);
                    break :blk_hi try self.ssa.emitInst(self.cur_bb, .{
                        .op = .bin_op,
                        .flags = .{ .is_synthetic = true },
                        .aux_u16 = @backingInt(BinOpKind.sub_wrap),
                        .type_id = .usize_ty,
                        .operands = .{ .lhs = len_val.asInt(), .rhs = tail_val.asInt() },
                    }, tok);
                };
                break :blk_subslice try self.emitSubsliceFromPlace(
                    peeled.place_id,
                    unwrapped_seq,
                    local_decl.type_id,
                    lo_val,
                    hi_val,
                    false,
                    tok,
                );
            } else if (binding.is_ref)
                try self.ssa.emitInst(self.cur_bb, .{
                    .op = .place_addr,
                    .type_id = local_decl.type_id,
                    .operands = .{
                        .lhs = binding.place_id.asInt(),
                        .rhs = @intFromBool(binding.is_mut and !is_in_guard),
                    },
                }, tok)
            else
                try self.loadPlaceValue(binding.place_id, binding.val_ty, tok, is_move_allowed);

            if (local_decl.flags().is_address_taken) {
                const dst_place = try self.makePlace(lid, &.{});
                try self.markStorageInitAtDepth(lid, decl_depth, tok);
                try self.emitZeroPadIfRequired(dst_place, local_decl.type_id, tok);
                _ = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .place_store,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = dst_place.asInt(), .rhs = bound_val.asInt() },
                }, tok);
            } else {
                try self.ssa.writeVariable(lid.asInt(), self.cur_bb, bound_val);
            }
        }
    }

    /// Returns `true` when `binding` moves a non-`Copy` sub-place out by value (invalidating whole-enum drop).
    fn isByValueMoveBinding(self: *const MirLowerer, binding: PatBinding) bool {
        if (binding.is_ref or binding.is_subslice or binding.val_ty.isError()) return false;
        if (self.pool.getFlags(binding.val_ty).is_copy) return false;
        return !self.isPlaceBehindSharedRef(binding.place_id);
    }

    /// Returns `true` if `place_a` and `place_b` alias or one is a projection prefix of the other.
    fn hasOverlappingPlaces(self: *const MirLowerer, place_a: PlaceId, place_b: PlaceId) bool {
        if (place_a == place_b) return true;
        const raw_a = self.body.places.items[place_a.asInt()];
        const raw_b = self.body.places.items[place_b.asInt()];
        if (raw_a.base != raw_b.base) return false;
        const projs_a = self.body.getPlaceProjections(place_a);
        const projs_b = self.body.getPlaceProjections(place_b);
        const common_len = @min(projs_a.len, projs_b.len);
        for (0..common_len) |proj_i| {
            if (projs_a[proj_i].kind != projs_b[proj_i].kind or
                projs_a[proj_i].payload != projs_b[proj_i].payload)
            {
                return false;
            }
        }
        return true;
    }

    /// Returns `true` if `col_place` projects out of the same `.downcast` variant prefix as `moved_place`.
    fn hasSharedMovedDowncastPrefix(self: *const MirLowerer, col_place: PlaceId, moved_place: PlaceId) bool {
        const raw_col = self.body.places.items[col_place.asInt()];
        const raw_mov = self.body.places.items[moved_place.asInt()];
        if (raw_col.base != raw_mov.base) return false;
        const col_projs = self.body.getPlaceProjections(col_place);
        const mov_projs = self.body.getPlaceProjections(moved_place);
        const common_len = @min(col_projs.len, mov_projs.len);
        var has_shared_downcast = false;
        for (0..common_len) |proj_i| {
            if (col_projs[proj_i].kind != mov_projs[proj_i].kind or
                col_projs[proj_i].payload != mov_projs[proj_i].payload)
            {
                break;
            }
            if (col_projs[proj_i].kind == .downcast) {
                has_shared_downcast = true;
            }
        }
        return has_shared_downcast;
    }

    /// Moves a `_`-matched `.auto_drop_tier` variant sub-place into temporary storage at `target_depth`.
    fn materializeWildcardMoveIntoScope(
        self: *MirLowerer,
        col_place: PlaceId,
        col_ty: TypeId,
        target_depth: u32,
        depth: u32,
        tok: TokenIndex,
    ) anyerror!void {
        if (depth > 16 or col_ty.isError() or col_ty == .unit_ty) return;
        if (type_system.classifyOwnershipTier(self.pool, self.sym_table, col_ty) != .auto_drop_tier) return;

        const unwrapped_ty = self.pool.unwrapUnderlyingType(col_ty);
        if (self.pool.getTag(unwrapped_ty) == .tuple_ty) {
            for (self.pool.getTupleElements(unwrapped_ty), 0..) |raw_elem_ty, elem_i| {
                const elem_ty = TypeId.fromInt(raw_elem_ty);
                const elem_proj = [1]MirProjection{.{ .kind = .field, .payload = @intCast(elem_i) }};
                if (!self.isValidPlaceExtension(col_place, &elem_proj)) continue;
                const elem_place = try self.extendPlace(col_place, &elem_proj);
                try self.materializeWildcardMoveIntoScope(elem_place, elem_ty, target_depth, depth + 1, tok);
            }
            return;
        }

        const wild_val = try self.loadPlaceValue(col_place, col_ty, tok, true);
        const wild_lid = try self.allocTempLocal(col_ty, tok, true, false);
        const wild_dst = try self.makePlace(wild_lid, &.{});
        try self.markStorageInitAtDepth(wild_lid, target_depth, tok);
        try self.emitZeroPadIfRequired(wild_dst, col_ty, tok);
        _ = try self.ssa.emitInst(self.cur_bb, .{
            .op = .place_store,
            .flags = .{ .has_side_effects = true, .is_synthetic = true },
            .type_id = .unit_ty,
            .operands = .{ .lhs = wild_dst.asInt(), .rhs = wild_val.asInt() },
        }, tok);
    }

    /// Materializes synthetic moves for `_`-matched `AutoDrop` siblings in partially-moved enum variants.
    fn emitPartialVariantWildcardMoves(
        self: *MirLowerer,
        col_places: []const PlaceId,
        col_types: []const TypeId,
        bindings: []const PatBinding,
        tok: TokenIndex,
    ) anyerror!void {
        if (col_places.len == 0 or bindings.len == 0) return;

        var has_downcast_move = false;
        for (bindings) |binding| {
            if (!self.isByValueMoveBinding(binding)) continue;
            for (self.body.getPlaceProjections(binding.place_id)) |proj| {
                if (proj.kind == .downcast) {
                    has_downcast_move = true;
                    break;
                }
            }
            if (has_downcast_move) break;
        }
        if (!has_downcast_move) return;

        const target_depth = if (self.active_cond_scope_depth != 0)
            self.active_cond_scope_depth
        else
            self.scope_depth;

        var moved_places: std.ArrayListUnmanaged(PlaceId) = .empty;
        defer moved_places.deinit(self.allocator);

        for (col_places, 0..) |col_place, col_i| {
            const col_ty = col_types[col_i];
            if (col_ty.isError() or col_ty == .unit_ty) continue;
            if (type_system.classifyOwnershipTier(self.pool, self.sym_table, col_ty) != .auto_drop_tier) continue;
            if (self.isPlaceBehindSharedRef(col_place)) continue;

            var is_sibling_of_move = false;
            for (bindings) |binding| {
                if (self.isByValueMoveBinding(binding) and
                    self.hasSharedMovedDowncastPrefix(col_place, binding.place_id))
                {
                    is_sibling_of_move = true;
                    break;
                }
            }
            if (!is_sibling_of_move) continue;

            var has_overlap = false;
            for (bindings) |binding| {
                if (self.hasOverlappingPlaces(col_place, binding.place_id)) {
                    has_overlap = true;
                    break;
                }
            }
            if (has_overlap) continue;
            for (moved_places.items) |prev_place| {
                if (self.hasOverlappingPlaces(col_place, prev_place)) {
                    has_overlap = true;
                    break;
                }
            }
            if (has_overlap) continue;

            try moved_places.append(self.allocator, col_place);
            try self.materializeWildcardMoveIntoScope(col_place, col_ty, target_depth, 0, tok);
        }
    }

    /// Returns a new slice removing element `drop_col` and inserting `insert_slice` in its place.
    fn spliceColumnSlice(
        comptime Elem: type,
        m_alloc: std.mem.Allocator,
        orig: []const Elem,
        drop_col: usize,
        insert_slice: []const Elem,
    ) ![]Elem {
        const out = try m_alloc.alloc(Elem, orig.len - 1 + insert_slice.len);
        @memcpy(out[0..drop_col], orig[0..drop_col]);
        @memcpy(out[drop_col .. drop_col + insert_slice.len], insert_slice);
        @memcpy(out[drop_col + insert_slice.len ..], orig[drop_col + 1 ..]);
        return out;
    }

    /// Specializes a sum-type column (`enum`, `Option`, `Result`) via `place_discriminant` + `switch_int`.
    fn specializeVariantColumn(
        self: *MirLowerer,
        ctx: *const MatchCompileCtx,
        col_places: []const PlaceId,
        col_types: []const TypeId,
        rows: []const MatrixRow,
        pivot_col: usize,
        pivot_place: PlaceId,
        pivot_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!void {
        const m_alloc = ctx.m_alloc;
        // Collect distinct `tag_ordinal`s and payload arities appearing in `pivot_col`:
        var tag_list: std.ArrayListUnmanaged(u32) = .empty;
        var arity_list: std.ArrayListUnmanaged(u32) = .empty;
        var payload_ty_list: std.ArrayListUnmanaged(TypeId) = .empty;

        for (rows) |row| {
            const pat_idx = row.pats[pivot_col];
            if (pat_idx == NONE_U32) continue;
            const pat = self.hir_store.patterns.items[pat_idx];
            if (pat.kind != .variant) continue;
            const vp = pat.kind.variant;
            var has_tag = false;
            for (tag_list.items) |existing_tag| {
                if (existing_tag == vp.tag_ordinal) {
                    has_tag = true;
                    break;
                }
            }
            if (!has_tag) {
                try tag_list.append(m_alloc, vp.tag_ordinal);
                try arity_list.append(m_alloc, vp.sub_len);
                try payload_ty_list.append(m_alloc, vp.payload_ty);
            }
        }

        const discr_open = try self.emitGhostOpen(.ghost_access_let, pivot_place, .scoped_projection, tok);
        const discr_val = try self.ssa.emitInst(self.cur_bb, .{
            .op = .place_discriminant,
            .type_id = .u32_ty,
            .operands = .{ .lhs = pivot_place.asInt(), .rhs = 0 },
        }, tok);
        try self.emitGhostEnd(discr_open, tok);

        const case_bbs = try m_alloc.alloc(MirBlockId, tag_list.items.len);
        for (0..tag_list.items.len) |case_i| {
            case_bbs[case_i] = try self.ssa.createBlock(false, false);
        }
        const default_bb = try self.ssa.createBlock(false, false);

        const first_edge_idx: u32 = @intCast(self.body.extra_edges.items.len);
        for (tag_list.items, 0..) |tag_ord, case_i| {
            const sw_val_idx: u16 = @intCast(self.body.switch_values.items.len);
            try self.body.switch_values.append(self.body.allocator, @as(i128, tag_ord));
            _ = try self.ssa.addOutgoingEdge(self.cur_bb, case_bbs[case_i], &.{}, sw_val_idx);
        }
        _ = try self.ssa.addOutgoingEdge(self.cur_bb, default_bb, &.{}, std.math.maxInt(u16));
        self.ssa.setTerminator(self.cur_bb, .{
            .kind = .switch_int,
            .edge_len = @intCast(tag_list.items.len + 1),
            .cond_or_val = discr_val.asInt(),
            .edge_start = first_edge_idx,
        });

        // Compile each variant's specialized child matrix:
        for (tag_list.items, 0..) |tag_ord, case_i| {
            try self.ssa.sealBlock(case_bbs[case_i]);
            self.cur_bb = case_bbs[case_i];

            const arity: usize = arity_list.items[case_i];
            const raw_payload_ty = payload_ty_list.items[case_i];
            const downcast_proj = [1]MirProjection{.{ .kind = .downcast, .payload = tag_ord }};
            const is_downcast_valid = self.isValidPlaceExtension(pivot_place, &downcast_proj);
            const downcast_place = if (is_downcast_valid)
                try self.extendPlace(pivot_place, &downcast_proj)
            else
                try self.allocErrorFallbackPlace(.err_ty, tok);

            const sub_places = try m_alloc.alloc(PlaceId, arity);
            const sub_types = try m_alloc.alloc(TypeId, arity);
            if (arity == 1) {
                sub_types[0] = if (!raw_payload_ty.isError() and raw_payload_ty != .unit_ty)
                    raw_payload_ty
                else
                    self.resolveVariantPayloadType(pivot_ty, tag_ord);
                const field0_proj = [1]MirProjection{.{ .kind = .field, .payload = 0 }};
                sub_places[0] = if (is_downcast_valid and self.isValidPlaceExtension(downcast_place, &field0_proj))
                    try self.extendPlace(downcast_place, &field0_proj)
                else
                    try self.allocErrorFallbackPlace(sub_types[0], tok);
            } else if (arity > 1) {
                const tup_ty = if (!raw_payload_ty.isError() and raw_payload_ty != .unit_ty)
                    raw_payload_ty
                else
                    self.resolveVariantPayloadType(pivot_ty, tag_ord);
                const field0_proj = [1]MirProjection{.{ .kind = .field, .payload = 0 }};
                const payload_place = if (is_downcast_valid and self.isValidPlaceExtension(downcast_place, &field0_proj))
                    try self.extendPlace(downcast_place, &field0_proj)
                else
                    try self.allocErrorFallbackPlace(tup_ty, tok);
                for (0..arity) |elem_k| {
                    sub_types[elem_k] = self.resolveAggregateMemberType(tup_ty, @intCast(elem_k));
                    const elem_proj = [1]MirProjection{.{ .kind = .field, .payload = @intCast(elem_k) }};
                    sub_places[elem_k] = if (self.isValidPlaceExtension(payload_place, &elem_proj))
                        try self.extendPlace(payload_place, &elem_proj)
                    else
                        try self.allocErrorFallbackPlace(sub_types[elem_k], tok);
                }
            }

            const next_places = try spliceColumnSlice(PlaceId, m_alloc, col_places, pivot_col, sub_places);
            const next_types = try spliceColumnSlice(TypeId, m_alloc, col_types, pivot_col, sub_types);

            var spec_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
            const wild_subs = try m_alloc.alloc(u32, arity);
            @memset(wild_subs, NONE_U32);

            for (rows) |row| {
                const pat_idx = row.pats[pivot_col];
                if (pat_idx == NONE_U32) {
                    const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, wild_subs);
                    try spec_rows.append(m_alloc, .{
                        .pats = next_pats,
                        .bindings = row.bindings,
                        .arm_idx = row.arm_idx,
                    });
                } else {
                    const pat = self.hir_store.patterns.items[pat_idx];
                    if (pat.kind == .variant and pat.kind.variant.tag_ordinal == tag_ord) {
                        const vp = pat.kind.variant;
                        const child_slice = if (vp.sub_len == arity)
                            self.hir_store.extra_data.items[vp.sub_start .. vp.sub_start + vp.sub_len]
                        else
                            wild_subs;
                        const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, child_slice);
                        try spec_rows.append(m_alloc, .{
                            .pats = next_pats,
                            .bindings = row.bindings,
                            .arm_idx = row.arm_idx,
                        });
                    }
                }
            }

            try self.compileDecisionMatrix(
                ctx,
                next_places,
                next_types,
                spec_rows.items,
                tok,
            );
        }

        // Compile default matrix `D(M)` (unreachable when all variants of `pivot_ty` were covered!):
        try self.ssa.sealBlock(default_bb);
        self.cur_bb = default_bb;
        if (self.countSumVariants(pivot_ty)) |total_vars| {
            if (tag_list.items.len >= total_vars) {
                self.ssa.setTerminator(default_bb, .{ .kind = .unreachable_term });
                return;
            }
        }

        const def_places = try spliceColumnSlice(PlaceId, m_alloc, col_places, pivot_col, &.{});
        const def_types = try spliceColumnSlice(TypeId, m_alloc, col_types, pivot_col, &.{});
        var def_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
        for (rows) |row| {
            if (row.pats[pivot_col] == NONE_U32) {
                const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, &.{});
                try def_rows.append(m_alloc, .{
                    .pats = next_pats,
                    .bindings = row.bindings,
                    .arm_idx = row.arm_idx,
                });
            }
        }
        try self.compileDecisionMatrix(
            ctx,
            def_places,
            def_types,
            def_rows.items,
            tok,
        );
    }

    /// Specializes a `bool` column via `cond_br` (`true` vs `false`).
    fn specializeBoolColumn(
        self: *MirLowerer,
        ctx: *const MatchCompileCtx,
        col_places: []const PlaceId,
        col_types: []const TypeId,
        rows: []const MatrixRow,
        pivot_col: usize,
        pivot_place: PlaceId,
        tok: TokenIndex,
    ) anyerror!void {
        const m_alloc = ctx.m_alloc;
        const cond_val = try self.loadPlaceValue(pivot_place, .bool_ty, tok, false);
        const true_bb = try self.ssa.createBlock(false, false);
        const false_bb = try self.ssa.createBlock(false, false);
        try self.emitCondBr(cond_val, true_bb, false_bb);
        try self.ssa.sealBlock(true_bb);
        try self.ssa.sealBlock(false_bb);

        const next_places = try spliceColumnSlice(PlaceId, m_alloc, col_places, pivot_col, &.{});
        const next_types = try spliceColumnSlice(TypeId, m_alloc, col_types, pivot_col, &.{});

        for ([2]bool{ true, false }, [2]MirBlockId{ true_bb, false_bb }) |target_bool, branch_bb| {
            self.cur_bb = branch_bb;
            var spec_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
            for (rows) |row| {
                const pat_idx = row.pats[pivot_col];
                const is_match = if (pat_idx == NONE_U32)
                    true
                else blk: {
                    const pat = self.hir_store.patterns.items[pat_idx];
                    break :blk pat.kind == .lit_bool and pat.kind.lit_bool == target_bool;
                };
                if (is_match) {
                    const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, &.{});
                    try spec_rows.append(m_alloc, .{
                        .pats = next_pats,
                        .bindings = row.bindings,
                        .arm_idx = row.arm_idx,
                    });
                }
            }
            try self.compileDecisionMatrix(
                ctx,
                next_places,
                next_types,
                spec_rows.items,
                tok,
            );
        }
    }

    /// Specializes integer/`char` singleton & range columns using `switch_int` or disjoint elementary intervals (`DR-13` §4.1.5).
    fn specializeIntRangeColumn(
        self: *MirLowerer,
        ctx: *const MatchCompileCtx,
        col_places: []const PlaceId,
        col_types: []const TypeId,
        rows: []const MatrixRow,
        pivot_col: usize,
        pivot_place: PlaceId,
        pivot_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!void {
        const m_alloc = ctx.m_alloc;
        const unwrapped_pivot_ty = self.pool.unwrapUnderlyingType(pivot_ty);
        const is_u128 = unwrapped_pivot_ty == .u128_ty;
        const domain_max: i128 = if (is_u128)
            @bitCast(@as(u128, std.math.maxInt(u128)))
        else
            std.math.maxInt(i128);

        const scrut_val = try self.loadPlaceValue(pivot_place, pivot_ty, tok, false);
        const next_places = try spliceColumnSlice(PlaceId, m_alloc, col_places, pivot_col, &.{});
        const next_types = try spliceColumnSlice(TypeId, m_alloc, col_types, pivot_col, &.{});

        // Check whether all ranges in `pivot_col` are small discrete sets (`<= 16` total scalar cases):
        var discrete_vals: std.ArrayListUnmanaged(i128) = .empty;
        var has_discrete_switch = true;
        for (rows) |row| {
            const pat_idx = row.pats[pivot_col];
            if (pat_idx == NONE_U32) continue;
            const pat = self.hir_store.patterns.items[pat_idx];
            if (pat.kind != .lit_int_range) continue;
            const rng = pat.kind.lit_int_range;
            if (isIntBoundLess(is_u128, rng.max_val, rng.min_val)) continue;
            const span_u128: u128 = @bitCast(rng.max_val -% rng.min_val);
            if (span_u128 > 8 or discrete_vals.items.len > 16) {
                has_discrete_switch = false;
                break;
            }
            var cur_val = rng.min_val;
            while (true) : (cur_val +%= 1) {
                var has_existing = false;
                for (discrete_vals.items) |existing_v| {
                    if (existing_v == cur_val) {
                        has_existing = true;
                        break;
                    }
                }
                if (!has_existing) try discrete_vals.append(m_alloc, cur_val);
                if (cur_val == rng.max_val) break;
            }
        }

        if (has_discrete_switch and discrete_vals.items.len > 0 and discrete_vals.items.len <= 24) {
            const case_bbs = try m_alloc.alloc(MirBlockId, discrete_vals.items.len);
            for (0..discrete_vals.items.len) |case_i| {
                case_bbs[case_i] = try self.ssa.createBlock(false, false);
            }
            const default_bb = try self.ssa.createBlock(false, false);
            const edge_start: u32 = @intCast(self.body.extra_edges.items.len);

            for (discrete_vals.items, 0..) |cval, case_i| {
                const sw_idx: u16 = @intCast(self.body.switch_values.items.len);
                try self.body.switch_values.append(self.body.allocator, cval);
                _ = try self.ssa.addOutgoingEdge(self.cur_bb, case_bbs[case_i], &.{}, sw_idx);
            }
            _ = try self.ssa.addOutgoingEdge(self.cur_bb, default_bb, &.{}, std.math.maxInt(u16));
            self.ssa.setTerminator(self.cur_bb, .{
                .kind = .switch_int,
                .edge_len = @intCast(discrete_vals.items.len + 1),
                .cond_or_val = scrut_val.asInt(),
                .edge_start = edge_start,
            });

            for (discrete_vals.items, 0..) |cval, case_i| {
                try self.ssa.sealBlock(case_bbs[case_i]);
                self.cur_bb = case_bbs[case_i];
                var spec_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
                for (rows) |row| {
                    const pat_idx = row.pats[pivot_col];
                    const is_match = if (pat_idx == NONE_U32)
                        true
                    else blk: {
                        const pat = self.hir_store.patterns.items[pat_idx];
                        if (pat.kind != .lit_int_range) break :blk false;
                        const rng = pat.kind.lit_int_range;
                        break :blk !isIntBoundLess(is_u128, rng.max_val, rng.min_val) and
                            isIntBoundLessOrEq(is_u128, rng.min_val, cval) and
                            isIntBoundLessOrEq(is_u128, cval, rng.max_val);
                    };
                    if (is_match) {
                        const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, &.{});
                        try spec_rows.append(m_alloc, .{
                            .pats = next_pats,
                            .bindings = row.bindings,
                            .arm_idx = row.arm_idx,
                        });
                    }
                }
                try self.compileDecisionMatrix(
                    ctx,
                    next_places,
                    next_types,
                    spec_rows.items,
                    tok,
                );
            }

            try self.ssa.sealBlock(default_bb);
            self.cur_bb = default_bb;
            var def_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
            for (rows) |row| {
                if (row.pats[pivot_col] == NONE_U32) {
                    const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, &.{});
                    try def_rows.append(m_alloc, .{
                        .pats = next_pats,
                        .bindings = row.bindings,
                        .arm_idx = row.arm_idx,
                    });
                }
            }
            return self.compileDecisionMatrix(
                ctx,
                next_places,
                next_types,
                def_rows.items,
                tok,
            );
        }

        // Disjoint Elementary Interval Decomposition (`DR-13` §4.1.5) for wide/overlapping ranges:
        var endpoints: std.ArrayListUnmanaged(i128) = .empty;
        for (rows) |row| {
            const pat_idx = row.pats[pivot_col];
            if (pat_idx == NONE_U32) continue;
            const pat = self.hir_store.patterns.items[pat_idx];
            if (pat.kind != .lit_int_range) continue;
            const rng = pat.kind.lit_int_range;
            if (isIntBoundLess(is_u128, rng.max_val, rng.min_val)) continue;
            try endpoints.append(m_alloc, rng.min_val);
            if (isIntBoundLess(is_u128, rng.max_val, domain_max)) {
                try endpoints.append(m_alloc, rng.max_val +% 1);
            }
        }
        const SortCtx = struct {
            is_unsigned_128: bool,
            pub fn isLessThan(sort_ctx: @This(), lhs_pt: i128, rhs_pt: i128) bool {
                return isIntBoundLess(sort_ctx.is_unsigned_128, lhs_pt, rhs_pt);
            }
        };
        std.mem.sort(i128, endpoints.items, SortCtx{ .is_unsigned_128 = is_u128 }, SortCtx.isLessThan);
        var uniq_len: usize = 0;
        for (endpoints.items) |pt| {
            if (uniq_len == 0 or endpoints.items[uniq_len - 1] != pt) {
                endpoints.items[uniq_len] = pt;
                uniq_len += 1;
            }
        }
        const pts = endpoints.items[0..uniq_len];

        var intervals: std.ArrayListUnmanaged(DisjointInterval) = .empty;
        for (0..pts.len) |pt_i| {
            const lo = pts[pt_i];
            const hi = if (pt_i + 1 < pts.len) pts[pt_i + 1] -% 1 else domain_max;
            var is_covered = false;
            for (rows) |row| {
                const pat_idx = row.pats[pivot_col];
                if (pat_idx == NONE_U32) continue;
                const pat = self.hir_store.patterns.items[pat_idx];
                if (pat.kind == .lit_int_range) {
                    const rng = pat.kind.lit_int_range;
                    if (!isIntBoundLess(is_u128, rng.max_val, rng.min_val) and
                        isIntBoundLessOrEq(is_u128, rng.min_val, lo) and
                        isIntBoundLessOrEq(is_u128, hi, rng.max_val))
                    {
                        is_covered = true;
                        break;
                    }
                }
            }
            if (is_covered) {
                try intervals.append(m_alloc, .{ .low = lo, .high = hi });
            }
        }

        const is_signed = self.isSignedIntType(pivot_ty);
        const ge_op: BinOpKind = if (is_signed) .sge else .uge;
        const le_op: BinOpKind = if (is_signed) .sle else .ule;

        for (intervals.items) |iv| {
            const lo_c = try self.body.appendConst(if (unwrapped_pivot_ty == .char_ty)
                .{ .char_val = @intCast(@max(iv.low, 0)) }
            else
                .{ .int_val = iv.low });
            const lo_val = try self.ssa.emitInst(self.cur_bb, .{
                .op = .const_scalar,
                .flags = .{ .is_synthetic = true },
                .type_id = pivot_ty,
                .operands = .{ .lhs = lo_c, .rhs = 0 },
            }, tok);
            const ge_cond = try self.ssa.emitInst(self.cur_bb, .{
                .op = .bin_op,
                .flags = .{ .is_synthetic = true },
                .aux_u16 = @backingInt(ge_op),
                .type_id = .bool_ty,
                .operands = .{ .lhs = scrut_val.asInt(), .rhs = lo_val.asInt() },
            }, tok);

            const hi_c = try self.body.appendConst(if (unwrapped_pivot_ty == .char_ty)
                .{ .char_val = @intCast(@min(@max(iv.high, 0), 0x10FFFF)) }
            else
                .{ .int_val = iv.high });
            const hi_val = try self.ssa.emitInst(self.cur_bb, .{
                .op = .const_scalar,
                .flags = .{ .is_synthetic = true },
                .type_id = pivot_ty,
                .operands = .{ .lhs = hi_c, .rhs = 0 },
            }, tok);
            const le_cond = try self.ssa.emitInst(self.cur_bb, .{
                .op = .bin_op,
                .flags = .{ .is_synthetic = true },
                .aux_u16 = @backingInt(le_op),
                .type_id = .bool_ty,
                .operands = .{ .lhs = scrut_val.asInt(), .rhs = hi_val.asInt() },
            }, tok);
            const in_iv = try self.ssa.emitInst(self.cur_bb, .{
                .op = .bin_op,
                .flags = .{ .is_synthetic = true },
                .aux_u16 = @backingInt(BinOpKind.bit_and),
                .type_id = .bool_ty,
                .operands = .{ .lhs = ge_cond.asInt(), .rhs = le_cond.asInt() },
            }, tok);

            const hit_bb = try self.ssa.createBlock(false, false);
            const next_bb = try self.ssa.createBlock(false, false);
            try self.emitCondBr(in_iv, hit_bb, next_bb);
            try self.ssa.sealBlock(hit_bb);
            try self.ssa.sealBlock(next_bb);

            self.cur_bb = hit_bb;
            var spec_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
            for (rows) |row| {
                const pat_idx = row.pats[pivot_col];
                const is_match = if (pat_idx == NONE_U32)
                    true
                else blk: {
                    const pat = self.hir_store.patterns.items[pat_idx];
                    if (pat.kind != .lit_int_range) break :blk false;
                    const rng = pat.kind.lit_int_range;
                    break :blk !isIntBoundLess(is_u128, rng.max_val, rng.min_val) and
                        isIntBoundLessOrEq(is_u128, rng.min_val, iv.low) and
                        isIntBoundLessOrEq(is_u128, iv.high, rng.max_val);
                };
                if (is_match) {
                    const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, &.{});
                    try spec_rows.append(m_alloc, .{
                        .pats = next_pats,
                        .bindings = row.bindings,
                        .arm_idx = row.arm_idx,
                    });
                }
            }
            try self.compileDecisionMatrix(
                ctx,
                next_places,
                next_types,
                spec_rows.items,
                tok,
            );
            self.cur_bb = next_bb;
        }

        // Default fallback after all disjoint intervals:
        var def_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
        for (rows) |row| {
            if (row.pats[pivot_col] == NONE_U32) {
                const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, &.{});
                try def_rows.append(m_alloc, .{
                    .pats = next_pats,
                    .bindings = row.bindings,
                    .arm_idx = row.arm_idx,
                });
            }
        }
        try self.compileDecisionMatrix(
            ctx,
            next_places,
            next_types,
            def_rows.items,
            tok,
        );
    }

    /// Specializes `f32`/`f64` or `str` equality literal patterns via `BinOpKind.eq` + `cond_br`.
    fn specializeScalarEqColumn(
        self: *MirLowerer,
        ctx: *const MatchCompileCtx,
        col_places: []const PlaceId,
        col_types: []const TypeId,
        rows: []const MatrixRow,
        pivot_col: usize,
        pivot_place: PlaceId,
        pivot_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!void {
        const m_alloc = ctx.m_alloc;
        const target_pat = self.hir_store.patterns.items[rows[0].pats[pivot_col]];
        const scrut_val = try self.loadPlaceValue(pivot_place, pivot_ty, tok, false);
        const lit_const: MirConst = switch (target_pat.kind) {
            .lit_float => |fv| .{ .float_val = fv },
            .lit_str => |sv| .{ .str_val = sv },
            else => .unit_val,
        };
        const c_idx = try self.body.appendConst(lit_const);
        const lit_val = try self.ssa.emitInst(self.cur_bb, .{
            .op = .const_scalar,
            .flags = .{ .is_synthetic = true },
            .type_id = pivot_ty,
            .operands = .{ .lhs = c_idx, .rhs = 0 },
        }, tok);
        const eq_cond = try self.ssa.emitInst(self.cur_bb, .{
            .op = .bin_op,
            .flags = .{ .is_synthetic = true },
            .aux_u16 = @backingInt(BinOpKind.eq),
            .type_id = .bool_ty,
            .operands = .{ .lhs = scrut_val.asInt(), .rhs = lit_val.asInt() },
        }, tok);

        const hit_bb = try self.ssa.createBlock(false, false);
        const miss_bb = try self.ssa.createBlock(false, false);
        try self.emitCondBr(eq_cond, hit_bb, miss_bb);
        try self.ssa.sealBlock(hit_bb);
        try self.ssa.sealBlock(miss_bb);

        const next_places = try spliceColumnSlice(PlaceId, m_alloc, col_places, pivot_col, &.{});
        const next_types = try spliceColumnSlice(TypeId, m_alloc, col_types, pivot_col, &.{});

        self.cur_bb = hit_bb;
        var hit_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
        for (rows) |row| {
            const pat_idx = row.pats[pivot_col];
            const is_same = if (pat_idx == NONE_U32)
                true
            else blk: {
                const cand = self.hir_store.patterns.items[pat_idx];
                break :blk switch (target_pat.kind) {
                    .lit_float => |fv| cand.kind == .lit_float and cand.kind.lit_float == fv,
                    .lit_str => |sv| cand.kind == .lit_str and cand.kind.lit_str == sv,
                    else => false,
                };
            };
            if (is_same) {
                const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, &.{});
                try hit_rows.append(m_alloc, .{
                    .pats = next_pats,
                    .bindings = row.bindings,
                    .arm_idx = row.arm_idx,
                });
            }
        }
        try self.compileDecisionMatrix(
            ctx,
            next_places,
            next_types,
            hit_rows.items,
            tok,
        );

        self.cur_bb = miss_bb;
        var miss_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
        for (rows) |row| {
            const pat_idx = row.pats[pivot_col];
            if (pat_idx == NONE_U32) {
                try miss_rows.append(m_alloc, row);
            } else {
                const cand = self.hir_store.patterns.items[pat_idx];
                const is_same = switch (target_pat.kind) {
                    .lit_float => |fv| cand.kind == .lit_float and cand.kind.lit_float == fv,
                    .lit_str => |sv| cand.kind == .lit_str and cand.kind.lit_str == sv,
                    else => false,
                };
                if (!is_same) try miss_rows.append(m_alloc, row);
            }
        }
        try self.compileDecisionMatrix(
            ctx,
            col_places,
            col_types,
            miss_rows.items,
            tok,
        );
    }

    /// Specializes fixed-array and slice patterns (`[p0, ..rest, s0]`) via `switch_int` on sequence length.
    fn specializeSliceColumn(
        self: *MirLowerer,
        ctx: *const MatchCompileCtx,
        col_places: []const PlaceId,
        col_types: []const TypeId,
        rows: []const MatrixRow,
        pivot_col: usize,
        pivot_place: PlaceId,
        pivot_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!void {
        const m_alloc = ctx.m_alloc;
        const unwrapped_seq = self.pool.unwrapUnderlyingType(pivot_ty);
        const elem_ty: TypeId = if (unwrapped_seq.isError())
            .err_ty
        else if (unwrapped_seq == .str_ty)
            .u8_ty
        else
            self.pool.unwrapUnderlyingType(TypeId.fromInt(self.pool.getNode(unwrapped_seq).lhs));

        var max_exact_len: u32 = 0;
        var has_exact = false;
        var max_rest_prefix: u32 = 0;
        var max_rest_suffix: u32 = 0;

        for (rows) |row| {
            const pat_idx = row.pats[pivot_col];
            if (pat_idx == NONE_U32 or pat_idx >= self.hir_store.patterns.items.len) continue;
            const pat = self.hir_store.patterns.items[pat_idx];
            if (pat.kind != .slice_pat) continue;
            const sp = pat.kind.slice_pat;
            const min_len = @as(u32, sp.prefix_len) + @as(u32, sp.suffix_len);
            if (sp.has_rest) {
                if (sp.prefix_len > max_rest_prefix) max_rest_prefix = sp.prefix_len;
                if (sp.suffix_len > max_rest_suffix) max_rest_suffix = sp.suffix_len;
            } else {
                has_exact = true;
                if (min_len > max_exact_len) max_exact_len = min_len;
            }
        }

        const rest_floor: usize = @as(usize, max_rest_prefix) + @as(usize, max_rest_suffix);
        const exact_ceil: usize = if (has_exact) @as(usize, max_exact_len) + 1 else 0;
        const threshold: usize = @min(@max(rest_floor, exact_ceil), 1024);

        const len_val = try self.emitPlaceSequenceLength(pivot_place, unwrapped_seq, tok);

        const case_bbs = try m_alloc.alloc(MirBlockId, threshold);
        for (0..threshold) |len_k| {
            case_bbs[len_k] = try self.ssa.createBlock(false, false);
        }
        const default_bb = try self.ssa.createBlock(false, false);

        const first_edge_idx: u32 = @intCast(self.body.extra_edges.items.len);
        for (0..threshold) |len_k| {
            const sw_val_idx: u16 = @intCast(self.body.switch_values.items.len);
            try self.body.switch_values.append(self.body.allocator, @as(i128, len_k));
            _ = try self.ssa.addOutgoingEdge(self.cur_bb, case_bbs[len_k], &.{}, sw_val_idx);
        }
        _ = try self.ssa.addOutgoingEdge(self.cur_bb, default_bb, &.{}, std.math.maxInt(u16));
        self.ssa.setTerminator(self.cur_bb, .{
            .kind = .switch_int,
            .edge_len = @intCast(threshold + 1),
            .cond_or_val = len_val.asInt(),
            .edge_start = first_edge_idx,
        });

        // [1] Concrete length arms `len == concrete_len` (`0 .. threshold - 1`):
        for (0..threshold) |concrete_len| {
            try self.ssa.sealBlock(case_bbs[concrete_len]);
            self.cur_bb = case_bbs[concrete_len];

            const sub_places = try m_alloc.alloc(PlaceId, concrete_len);
            const sub_types = try m_alloc.alloc(TypeId, concrete_len);
            for (0..concrete_len) |elem_i| {
                const idx_c = try self.body.appendConst(.{ .int_val = @as(i128, elem_i) });
                const idx_val = try self.ssa.emitInst(self.cur_bb, .{
                    .op = .const_scalar,
                    .flags = .{ .is_synthetic = true },
                    .type_id = .usize_ty,
                    .operands = .{ .lhs = idx_c, .rhs = 0 },
                }, tok);
                const idx_proj = [1]MirProjection{.{ .kind = .index, .payload = idx_val.asInt() }};
                sub_places[elem_i] = if (self.isValidPlaceExtension(pivot_place, &idx_proj))
                    try self.extendPlace(pivot_place, &idx_proj)
                else
                    try self.allocErrorFallbackPlace(elem_ty, tok);
                sub_types[elem_i] = elem_ty;
            }

            const next_places = try spliceColumnSlice(PlaceId, m_alloc, col_places, pivot_col, sub_places);
            const next_types = try spliceColumnSlice(TypeId, m_alloc, col_types, pivot_col, sub_types);

            var child_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
            const wild_fill = try m_alloc.alloc(u32, concrete_len);
            @memset(wild_fill, NONE_U32);

            for (rows) |row| {
                const pat_idx = row.pats[pivot_col];
                if (pat_idx == NONE_U32) {
                    const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, wild_fill);
                    try child_rows.append(m_alloc, .{
                        .pats = next_pats,
                        .bindings = row.bindings,
                        .arm_idx = row.arm_idx,
                    });
                    continue;
                }
                if (pat_idx >= self.hir_store.patterns.items.len) continue;
                const pat = self.hir_store.patterns.items[pat_idx];
                if (pat.kind != .slice_pat) continue;
                const sp = pat.kind.slice_pat;
                const req_len: usize = @as(usize, sp.prefix_len) + @as(usize, sp.suffix_len);
                const is_len_match = if (sp.has_rest) concrete_len >= req_len else concrete_len == req_len;
                if (!is_len_match) continue;

                const sub_pats = try m_alloc.alloc(u32, concrete_len);
                @memset(sub_pats, NONE_U32);
                if (sp.prefix_start + req_len <= self.hir_store.extra_data.items.len) {
                    for (0..sp.prefix_len) |pre_i| {
                        sub_pats[pre_i] = self.hir_store.extra_data.items[sp.prefix_start + pre_i];
                    }
                    const suf_base_col = concrete_len - sp.suffix_len;
                    const suf_extra_start = sp.prefix_start + sp.prefix_len;
                    for (0..sp.suffix_len) |suf_i| {
                        sub_pats[suf_base_col + suf_i] =
                            self.hir_store.extra_data.items[suf_extra_start + suf_i];
                    }
                }

                var next_bindings = row.bindings;
                if (sp.has_rest and sp.rest_local_id != NONE_U32) {
                    const ext_binds = try m_alloc.alloc(PatBinding, row.bindings.len + 1);
                    @memcpy(ext_binds[0..row.bindings.len], row.bindings);
                    ext_binds[row.bindings.len] = .{
                        .hir_local_id = sp.rest_local_id,
                        .place_id = pivot_place,
                        .val_ty = pivot_ty,
                        .is_ref = false,
                        .is_mut = sp.is_rest_mut,
                        .is_subslice = true,
                        .subslice_lo = sp.prefix_len,
                        .subslice_hi_from_end = sp.suffix_len,
                    };
                    next_bindings = ext_binds;
                }

                const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, sub_pats);
                try child_rows.append(m_alloc, .{
                    .pats = next_pats,
                    .bindings = next_bindings,
                    .arm_idx = row.arm_idx,
                });
            }

            try self.compileDecisionMatrix(ctx, next_places, next_types, child_rows.items, tok);
        }

        // [2] Open length arm `len >= threshold` (`default_bb`):
        try self.ssa.sealBlock(default_bb);
        self.cur_bb = default_bb;

        const pre_cols: usize = max_rest_prefix;
        const suf_cols: usize = max_rest_suffix;
        const open_arity = pre_cols + suf_cols;
        const open_places = try m_alloc.alloc(PlaceId, open_arity);
        const open_types = try m_alloc.alloc(TypeId, open_arity);

        for (0..pre_cols) |pre_i| {
            const idx_c = try self.body.appendConst(.{ .int_val = @as(i128, pre_i) });
            const idx_val = try self.ssa.emitInst(self.cur_bb, .{
                .op = .const_scalar,
                .flags = .{ .is_synthetic = true },
                .type_id = .usize_ty,
                .operands = .{ .lhs = idx_c, .rhs = 0 },
            }, tok);
            const idx_proj = [1]MirProjection{.{ .kind = .index, .payload = idx_val.asInt() }};
            open_places[pre_i] = if (self.isValidPlaceExtension(pivot_place, &idx_proj))
                try self.extendPlace(pivot_place, &idx_proj)
            else
                try self.allocErrorFallbackPlace(elem_ty, tok);
            open_types[pre_i] = elem_ty;
        }
        for (0..suf_cols) |suf_col_i| {
            const dist_from_end = suf_cols - suf_col_i;
            const dist_c = try self.body.appendConst(.{ .int_val = @as(i128, dist_from_end) });
            const dist_val = try self.ssa.emitInst(self.cur_bb, .{
                .op = .const_scalar,
                .flags = .{ .is_synthetic = true },
                .type_id = .usize_ty,
                .operands = .{ .lhs = dist_c, .rhs = 0 },
            }, tok);
            const idx_val = try self.ssa.emitInst(self.cur_bb, .{
                .op = .bin_op,
                .flags = .{ .is_synthetic = true },
                .aux_u16 = @backingInt(BinOpKind.sub_wrap),
                .type_id = .usize_ty,
                .operands = .{ .lhs = len_val.asInt(), .rhs = dist_val.asInt() },
            }, tok);
            const idx_proj = [1]MirProjection{.{ .kind = .index, .payload = idx_val.asInt() }};
            open_places[pre_cols + suf_col_i] = if (self.isValidPlaceExtension(pivot_place, &idx_proj))
                try self.extendPlace(pivot_place, &idx_proj)
            else
                try self.allocErrorFallbackPlace(elem_ty, tok);
            open_types[pre_cols + suf_col_i] = elem_ty;
        }

        const def_places = try spliceColumnSlice(PlaceId, m_alloc, col_places, pivot_col, open_places);
        const def_types = try spliceColumnSlice(TypeId, m_alloc, col_types, pivot_col, open_types);

        var def_rows: std.ArrayListUnmanaged(MatrixRow) = .empty;
        const def_wild = try m_alloc.alloc(u32, open_arity);
        @memset(def_wild, NONE_U32);

        for (rows) |row| {
            const pat_idx = row.pats[pivot_col];
            if (pat_idx == NONE_U32) {
                const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, def_wild);
                try def_rows.append(m_alloc, .{
                    .pats = next_pats,
                    .bindings = row.bindings,
                    .arm_idx = row.arm_idx,
                });
                continue;
            }
            if (pat_idx >= self.hir_store.patterns.items.len) continue;
            const pat = self.hir_store.patterns.items[pat_idx];
            if (pat.kind != .slice_pat) continue;
            const sp = pat.kind.slice_pat;
            if (!sp.has_rest) continue;

            const sub_pats = try m_alloc.alloc(u32, open_arity);
            @memset(sub_pats, NONE_U32);
            const req_len: usize = @as(usize, sp.prefix_len) + @as(usize, sp.suffix_len);
            if (sp.prefix_start + req_len <= self.hir_store.extra_data.items.len) {
                for (0..sp.prefix_len) |pre_i| {
                    sub_pats[pre_i] = self.hir_store.extra_data.items[sp.prefix_start + pre_i];
                }
                const suf_col_base = pre_cols + (suf_cols - sp.suffix_len);
                const suf_extra_start = sp.prefix_start + sp.prefix_len;
                for (0..sp.suffix_len) |suf_i| {
                    sub_pats[suf_col_base + suf_i] =
                        self.hir_store.extra_data.items[suf_extra_start + suf_i];
                }
            }

            var next_bindings = row.bindings;
            if (sp.rest_local_id != NONE_U32) {
                const ext_binds = try m_alloc.alloc(PatBinding, row.bindings.len + 1);
                @memcpy(ext_binds[0..row.bindings.len], row.bindings);
                ext_binds[row.bindings.len] = .{
                    .hir_local_id = sp.rest_local_id,
                    .place_id = pivot_place,
                    .val_ty = pivot_ty,
                    .is_ref = false,
                    .is_mut = sp.is_rest_mut,
                    .is_subslice = true,
                    .subslice_lo = sp.prefix_len,
                    .subslice_hi_from_end = sp.suffix_len,
                };
                next_bindings = ext_binds;
            }

            const next_pats = try spliceColumnSlice(u32, m_alloc, row.pats, pivot_col, sub_pats);
            try def_rows.append(m_alloc, .{
                .pats = next_pats,
                .bindings = next_bindings,
                .arm_idx = row.arm_idx,
            });
        }

        try self.compileDecisionMatrix(ctx, def_places, def_types, def_rows.items, tok);
    }

    // ------------- Top-Level Function Lowering Driver -------------

    /// Appends `hir_slot` (or a fallback placeholder) to `self.body.locals`, optionally recording `hir_local_remap`.
    fn appendHirSlotAsMirLocal(
        self: *MirLowerer,
        hir_slot: u32,
        is_ret: bool,
        is_arg: bool,
        fallback_ty: TypeId,
        is_recording_remap: bool,
    ) !void {
        const mir_slot: u32 = @intCast(self.body.locals.items.len);
        if (hir_slot < self.hir_store.locals.items.len) {
            const h_loc = self.hir_store.locals.items[hir_slot];
            const mir_ty: TypeId = if (!is_ret and h_loc.mode == .set_mode and self.pool.isOutRef(h_loc.type_id))
                self.pool.unwrapUnderlyingType(TypeId.fromInt(self.pool.getNode(self.pool.unwrapUnderlyingType(h_loc.type_id)).lhs))
            else
                h_loc.type_id;
            try self.body.locals.append(
                self.body.allocator,
                LocalDecl.init(
                    h_loc.name,
                    mir_ty,
                    .none,
                    0,
                    if (is_ret) .set_mode else h_loc.mode,
                    .{
                        .is_mut = is_ret or h_loc.is_mut or h_loc.mode == .inout_mode or h_loc.mode == .set_mode,
                        .is_arg = is_arg,
                        .is_synthetic_temp = h_loc.is_temp,
                        .is_address_taken = is_ret or (is_arg and (h_loc.mode == .inout_mode or h_loc.mode == .set_mode)),
                        .is_return_slot = is_ret,
                    },
                ),
            );
            try self.body.local_scope_depths.append(
                self.body.allocator,
                if (is_ret or is_arg) 0 else 1,
            );
            try self.local_var_types.append(self.allocator, mir_ty);
        } else {
            try self.body.locals.append(
                self.body.allocator,
                LocalDecl.init(.empty, fallback_ty, .none, 0, if (is_ret) .set_mode else .let_mode, .{
                    .is_mut = is_ret,
                    .is_arg = is_arg,
                    .is_synthetic_temp = true,
                    .is_address_taken = is_ret,
                    .is_return_slot = is_ret,
                }),
            );
            try self.body.local_scope_depths.append(
                self.body.allocator,
                if (is_ret or is_arg) 0 else 1,
            );
            try self.local_var_types.append(self.allocator, fallback_ty);
        }
        if (is_recording_remap) {
            try self.hir_local_remap.put(self.allocator, hir_slot, LocalId.fromInt(mir_slot));
        }
    }

    /// Lowers a single `HirFnMeta` into `self.body` and finalizes SSA via `self.ssa.finish()`.
    fn lowerFunction(self: *MirLowerer, fn_meta: HirFnMeta) !void {
        const is_sast_sub = self.is_for_sast and fn_meta.is_subscript;
        const is_sast_probe = is_sast_sub or fn_meta.is_sast_default_probe;
        const eff_ret_ty: TypeId = if (is_sast_sub) .unit_ty else fn_meta.ret_ty;
        self.is_sast_subscript_body = is_sast_sub;
        self.is_sast_subscript_inout = is_sast_sub and fn_meta.is_subscript_inout_arm;
        self.body.def_id = if (is_sast_probe) .NONE else fn_meta.def_id;
        self.body.symbol_index = if (is_sast_probe) .none else fn_meta.symbol_index;
        self.body.name = if (is_sast_probe) .empty else fn_meta.name;
        self.body.sast_owner_def_id = fn_meta.def_id;
        self.body.sast_owner_symbol = fn_meta.symbol_index;
        self.body.ret_ty = eff_ret_ty;
        self.body.param_count = fn_meta.capture_len + fn_meta.param_len;
        self.body.target_layout = self.hir_store.target_layout;
        self.body.is_async = fn_meta.is_async;
        self.body.is_contextless = fn_meta.is_contextless and !fn_meta.is_async;
        self.body.is_sast_default_probe = fn_meta.is_sast_default_probe;
        self.body.is_sast_subscript_probe = is_sast_sub;
        if (fn_meta.is_subscript) {
            for (self.hir_store.functions.items, 0..) |cand_meta, cand_idx| {
                if (cand_meta.body_hir == fn_meta.body_hir and
                    cand_meta.is_subscript_inout_arm == fn_meta.is_subscript_inout_arm)
                {
                    self.subscript_splice_stack[0] = .{ .store = self.hir_store, .fn_meta_idx = cand_idx };
                    self.subscript_splice_depth = 1;
                    break;
                }
            }
        }

        self.base_hir_local = fn_meta.return_local_id;
        self.root_local_len = if (fn_meta.total_local_len > 0)
            fn_meta.total_local_len
        else
            1 + fn_meta.capture_len + fn_meta.param_len;

        // [1] Populate `locals` (`_0` return slot + formal captures + formal parameters + body locals) & `PlaceId(0)`:
        try self.body.locals.ensureTotalCapacity(self.body.allocator, self.root_local_len);
        try self.body.local_scope_depths.ensureTotalCapacity(self.body.allocator, self.root_local_len);
        try self.local_var_types.ensureTotalCapacity(self.allocator, self.root_local_len);

        if (fn_meta.capture_len > 0) {
            try self.appendHirSlotAsMirLocal(self.base_hir_local, true, false, eff_ret_ty, true);
            for (0..fn_meta.capture_len) |cap_i| {
                const inner_hir_slot = self.hir_store.extra_data.items[fn_meta.capture_extra_start + cap_i * 2 + 1];
                try self.appendHirSlotAsMirLocal(inner_hir_slot, false, true, .unit_ty, true);
            }
            for (0..fn_meta.param_len) |param_i| {
                const param_hir_slot = fn_meta.param_local_start + @as(u32, @intCast(param_i));
                try self.appendHirSlotAsMirLocal(param_hir_slot, false, true, .unit_ty, true);
            }
            for (1..self.root_local_len) |offset| {
                const hir_slot = self.base_hir_local + @as(u32, @intCast(offset));
                if (self.hir_local_remap.contains(hir_slot)) continue;
                try self.appendHirSlotAsMirLocal(hir_slot, false, false, .unit_ty, true);
            }
        } else {
            for (0..self.root_local_len) |offset| {
                const hir_slot = self.base_hir_local + @as(u32, @intCast(offset));
                const is_ret = offset == 0;
                const is_arg = offset >= 1 and offset <= fn_meta.param_len;
                try self.appendHirSlotAsMirLocal(
                    hir_slot,
                    is_ret,
                    is_arg,
                    if (is_ret) eff_ret_ty else TypeId.unit_ty,
                    false,
                );
            }
        }
        self.ssa.var_types = self.local_var_types.items;

        // Reserve `PlaceId.return_place` (`0`):
        try self.body.places.append(self.body.allocator, .{
            .base = LocalId.return_slot.asInt(),
            .proj_start = 0,
            .proj_len = 0,
        });

        // [2] Scan body for address-taken locals (`&x`, `&mut x`, `inout`, `set`, projections):
        self.scanAddressTakenLocals(fn_meta.body_hir);

        // [3] Create sealed entry block `^bb0` and initialize non-`set` formal parameters:
        const entry_bb = try self.ssa.createBlock(true, false);
        self.cur_bb = entry_bb;

        for (1..self.body.locals.items.len) |slot_i| {
            const lid = LocalId.fromInt(@intCast(slot_i));
            const decl = self.body.locals.items[slot_i];
            if (!decl.flags().is_arg) continue;
            if (decl.mode() != .set_mode) {
                _ = try self.ssa.emitInst(entry_bb, .{
                    .op = .ghost_storage_init,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = lid.asInt(), .rhs = 0 },
                }, .none);
                if (!decl.flags().is_address_taken) {
                    const param_place = try self.makePlace(lid, &.{});
                    const arg_val = try self.loadPlaceValue(param_place, decl.type_id, .none, false);
                    try self.ssa.writeVariable(lid.asInt(), entry_bb, arg_val);
                }
            }
        }

        // [4] Lower `fn_meta.body_hir` and finalize any open fallthrough path:
        if (!fn_meta.body_hir.isNone()) {
            const tail_val = try self.lowerRValue(fn_meta.body_hir);
            if (!self.cur_bb.isNone() and !self.ssa.isBlockTerminated(self.cur_bb)) {
                if (eff_ret_ty == .never_ty) {
                    self.ssa.setTerminator(self.cur_bb, .{ .kind = .unreachable_term });
                } else {
                    try self.popAndCloseBorrowsTo(0, .none);
                    try self.emitInlineNormalCleanupsAbove(0, .none);
                    const final_ret = if (eff_ret_ty == .unit_ty)
                        try self.emitUnitVal(.none)
                    else
                        tail_val;
                    try self.emitFinalReturnTerminator(final_ret, .none);
                }
            }
        } else {
            try self.emitFinalReturnTerminator(
                try self.ssa.emitDefaultScalarInBlock(entry_bb, eff_ret_ty),
                .none,
            );
        }

        // [5] Seal, prune unreachable blocks, collapse trivial phis, and pack `MirBody`:
        try self.ssa.finish();
    }
};

// --------- Dominator Tree & `MirVerifier` Invariants ----------

/// Formal verification error codes returned by `verifyMirBody` (`DR-13` §4.4).
pub const MirVerifyError = error{
    OutOfMemory,
    V1DuplicateSsaDefinition,
    V1DominanceViolation,
    V2InvalidTerminatorOrEdge,
    V2PredEdgeBijectionMismatch,
    V2EdgeArgCountMismatch,
    V2CallContinuationSplitViolation,
    V3InvalidPlaceProjection,
    V4PostStripGhostPresent,
    V4UnbalancedGhostStack,
    V4GhostExclusivityConflict,
    V5ReadUninitializedOrMoved,
    V5IncompleteExitInitialization,
    V6ContextlessCallViolation,
    V6LocalClosureEscape,
};

/// Cooper-Harvey-Kennedy immediate-dominator tree over a `MirBody` CFG.
pub const DominatorTree = struct {
    /// Backing allocator owning `rpo_blocks`, `rpo_index`, and `idom`.
    allocator: std.mem.Allocator,
    /// Reachable `MirBlockId` raw indices in Reverse Post-Order (`rpo_blocks[0] == 0`).
    rpo_blocks: []u32,
    /// Map `block_idx -> RPO position` (`NONE_U32` if unreachable from `^bb0`).
    rpo_index: []u32,
    /// Immediate dominator per block (`idom[0] = 0`, `NONE_U32` if unreachable).
    idom: []u32,

    /// Releases arrays owned by `self`.
    pub fn deinit(self: *DominatorTree) void {
        self.allocator.free(self.rpo_blocks);
        self.allocator.free(self.rpo_index);
        self.allocator.free(self.idom);
        self.* = undefined;
    }

    /// Returns `true` if `block_id` is reachable from entry block `^bb0`.
    pub inline fn isReachable(self: *const DominatorTree, block_id: MirBlockId) bool {
        const idx = block_id.asInt();
        return idx < self.rpo_index.len and self.rpo_index[idx] != NONE_U32;
    }

    /// Returns `true` if `dom_bb` dominates `target_bb` (reflexive: `isDominatorOf(b, b) == true`).
    pub fn isDominatorOf(self: *const DominatorTree, dom_bb: MirBlockId, target_bb: MirBlockId) bool {
        if (!self.isReachable(dom_bb) or !self.isReachable(target_bb)) return false;
        const dom_idx = dom_bb.asInt();
        var cur = target_bb.asInt();
        var guard_steps: usize = 0;
        while (cur != dom_idx and guard_steps <= self.rpo_blocks.len) : (guard_steps += 1) {
            const next_idom = self.idom[cur];
            if (next_idom == cur or next_idom == NONE_U32) return false;
            cur = next_idom;
        }
        return cur == dom_idx;
    }
};

/// Computes the Cooper-Harvey-Kennedy dominator tree rooted at `^bb0` (`DR-13` §4.4).
pub fn computeDominators(allocator: std.mem.Allocator, body: *const MirBody) !DominatorTree {
    const block_count = body.blocks.items.len;
    const rpo_index = try allocator.alloc(u32, block_count);
    errdefer allocator.free(rpo_index);
    @memset(rpo_index, NONE_U32);

    const idom = try allocator.alloc(u32, block_count);
    errdefer allocator.free(idom);
    @memset(idom, NONE_U32);

    if (block_count == 0) {
        const empty_rpo = try allocator.alloc(u32, 0);
        return .{
            .allocator = allocator,
            .rpo_blocks = empty_rpo,
            .rpo_index = rpo_index,
            .idom = idom,
        };
    }

    // [1] Iterative post-order DFS from `^bb0`:
    const DfsFrame = struct { bb: u32, next_edge: u16 };
    const stack = try allocator.alloc(DfsFrame, block_count);
    defer allocator.free(stack);
    const visited = try allocator.alloc(bool, block_count);
    defer allocator.free(visited);
    @memset(visited, false);

    var post_order = try allocator.alloc(u32, block_count);
    defer allocator.free(post_order);
    var post_len: usize = 0;

    visited[0] = true;
    stack[0] = .{ .bb = 0, .next_edge = 0 };
    var sp: usize = 1;

    while (sp > 0) {
        const top = &stack[sp - 1];
        const term = body.blocks.items[top.bb].terminator;
        if (top.next_edge < term.edge_len and
            term.edge_start + top.next_edge < body.extra_edges.items.len)
        {
            const edge = body.extra_edges.items[term.edge_start + top.next_edge];
            top.next_edge += 1;
            const dst = edge.target_bb.asInt();
            if (dst < block_count and !visited[dst]) {
                visited[dst] = true;
                stack[sp] = .{ .bb = dst, .next_edge = 0 };
                sp += 1;
            }
        } else {
            post_order[post_len] = top.bb;
            post_len += 1;
            sp -= 1;
        }
    }

    // Reverse post-order into `rpo_blocks`:
    const rpo_blocks = try allocator.alloc(u32, post_len);
    errdefer allocator.free(rpo_blocks);
    for (0..post_len) |i| {
        const bb_idx = post_order[post_len - 1 - i];
        rpo_blocks[i] = bb_idx;
        rpo_index[bb_idx] = @intCast(i);
    }

    // [2] Iterative Cooper-Harvey-Kennedy `idom` intersection:
    idom[0] = 0;
    var has_changed = true;
    while (has_changed) {
        has_changed = false;
        for (rpo_blocks[1..]) |bb_idx| {
            var new_idom: u32 = NONE_U32;
            const preds = body.getPredEdges(MirBlockId.fromInt(bb_idx));
            for (preds) |pred_eid| {
                if (pred_eid.asInt() >= body.extra_edges.items.len) continue;
                const pred_bb = body.extra_edges.items[pred_eid.asInt()].src_bb.asInt();
                if (pred_bb >= block_count or idom[pred_bb] == NONE_U32) continue;
                if (new_idom == NONE_U32) {
                    new_idom = pred_bb;
                } else {
                    new_idom = intersectDominators(pred_bb, new_idom, idom, rpo_index);
                }
            }
            if (new_idom != NONE_U32 and idom[bb_idx] != new_idom) {
                idom[bb_idx] = new_idom;
                has_changed = true;
            }
        }
    }

    return .{
        .allocator = allocator,
        .rpo_blocks = rpo_blocks,
        .rpo_index = rpo_index,
        .idom = idom,
    };
}

/// Finger-intersects two dominator chains in `rpo_index` order.
fn intersectDominators(
    left_bb: u32,
    right_bb: u32,
    idom: []const u32,
    rpo_index: []const u32,
) u32 {
    var finger1 = left_bb;
    var finger2 = right_bb;
    while (finger1 != finger2) {
        while (rpo_index[finger1] > rpo_index[finger2]) {
            finger1 = idom[finger1];
        }
        while (rpo_index[finger2] > rpo_index[finger1]) {
            finger2 = idom[finger2];
        }
    }
    return finger1;
}

/// Active Ghost access entry tracked by `MirVerifier` Invariant `V4`.
const GhostStackItem = struct {
    /// SSA `MirValueId` of the opening `ghost_access_*` instruction.
    token_val: MirValueId,
    /// Borrowed `PlaceId`.
    place_id: PlaceId,
    /// Opening opcode (`ghost_access_let`, `ghost_access_inout`, or `ghost_access_set`).
    op: MirOp,
};

/// Returns `true` if `place_a` and `place_b` alias/overlap in memory (`DR-02` Law of Exclusivity).
fn hasOverlappingPlaces(body: *const MirBody, place_a: PlaceId, place_b: PlaceId) bool {
    if (place_a == place_b) return true;
    const pa = body.places.items[place_a.asInt()];
    const pb = body.places.items[place_b.asInt()];
    if (pa.base != pb.base) return false;

    const projs_a = body.getPlaceProjections(place_a);
    const projs_b = body.getPlaceProjections(place_b);
    const shared_len = @min(projs_a.len, projs_b.len);
    for (0..shared_len) |step_i| {
        const sa = projs_a[step_i];
        const sb = projs_b[step_i];
        if (sa.kind == .field and sb.kind == .field and sa.payload != sb.payload) {
            return false;
        }
        if (sa.kind == .soa_elem and sb.kind == .soa_elem and sa.payload != sb.payload) {
            return false;
        }
        if (sa.kind == .downcast and sb.kind == .downcast and sa.payload != sb.payload) {
            return false;
        }
    }
    return true;
}

/// Emits a diagnostic on `sink` (if non-null) when a formal `MirVerifier` invariant fails.
fn emitVerifierDiagnostic(
    sink: ?*DiagnosticSink,
    file_id: FileId,
    code: DiagnosticCode,
    message: []const u8,
) !void {
    const out_sink = sink orelse return;
    const span = Span.init(file_id, 0, 0);
    const labels = [1]LabeledSpan{.{
        .span = span,
        .label = message,
        .style = .primary,
    }};
    try out_sink.emit(.{
        .code = code,
        .severity = .err,
        .primary_span = span,
        .message = message,
        .labels = &labels,
    });
}

/// Verifies formal `MirBody` invariants `V1`–`V6` (`DR-13` §4.4).
pub fn verifyMirBody(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    diagnostic_sink: ?*DiagnosticSink,
) MirVerifyError!void {
    if (body.blocks.items.len == 0) return error.V2InvalidTerminatorOrEdge;

    var dom = try computeDominators(allocator, body);
    defer dom.deinit();

    // [1] Verify `V2` CFG, `EdgeId` bijection, and Call Continuation Split-Edge:
    const entry_bb = body.blocks.items[0];
    if (entry_bb.pred_len != 0 or entry_bb.paramLen() != 0) {
        return error.V2InvalidTerminatorOrEdge;
    }

    const edge_count = body.extra_edges.items.len;
    const edge_seen_from_term = try allocator.alloc(bool, edge_count);
    defer allocator.free(edge_seen_from_term);
    @memset(edge_seen_from_term, false);

    for (dom.rpo_blocks) |bb_idx| {
        const bb = body.blocks.items[bb_idx];
        const term = bb.terminator;
        if (@as(usize, term.edge_start) + term.edge_len > edge_count) {
            return error.V2InvalidTerminatorOrEdge;
        }
        const is_arity_valid = switch (term.kind) {
            .unreachable_term, .ret, .trap => term.edge_len == 0,
            .br, .call => term.edge_len == 1,
            .cond_br, .coro_suspend => term.edge_len == 2,
            .switch_int => term.edge_len >= 1,
        };
        if (!is_arity_valid) return error.V2InvalidTerminatorOrEdge;

        for (0..term.edge_len) |off| {
            const eid = term.edge_start + @as(u32, @intCast(off));
            if (edge_seen_from_term[eid]) return error.V2PredEdgeBijectionMismatch;
            edge_seen_from_term[eid] = true;

            const edge = body.extra_edges.items[eid];
            if (edge.src_bb.asInt() != bb_idx or edge.target_bb.asInt() >= body.blocks.items.len) {
                return error.V2InvalidTerminatorOrEdge;
            }
            if (@as(usize, edge.args_start) + edge.args_len > body.extra_args.items.len) {
                return error.V2InvalidTerminatorOrEdge;
            }

            const dst_bb = body.blocks.items[edge.target_bb.asInt()];
            if (term.kind == .call) {
                if (term.cond_or_val >= body.calls.items.len) return error.V2InvalidTerminatorOrEdge;
                // Call Continuation Split-Edge Invariant:
                if (dst_bb.pred_len != 1 or dst_bb.paramLen() != 1 or edge.args_len != 0) {
                    return error.V2CallContinuationSplitViolation;
                }
            } else if (term.kind == .coro_suspend) {
                if (off == 0) {
                    // `resume_bb` receives `%ready_val` via Split-Edge (`pred_len == 1, paramLen() == 1, args_len == 0`):
                    if (dst_bb.pred_len != 1 or dst_bb.paramLen() != 1 or edge.args_len != 0) {
                        return error.V2CallContinuationSplitViolation;
                    }
                } else {
                    // `cancel_bb` takes 0 arguments and has `suspend_bb` as sole predecessor:
                    if (dst_bb.pred_len != 1 or dst_bb.paramLen() != 0 or edge.args_len != 0) {
                        return error.V2EdgeArgCountMismatch;
                    }
                }
            } else {
                if (edge.args_len != dst_bb.paramLen()) {
                    return error.V2EdgeArgCountMismatch;
                }
            }

            // Confirm `eid` is listed in `dst_bb`'s `pred_edges`:
            var is_in_preds = false;
            for (body.getPredEdges(edge.target_bb)) |pred_eid| {
                if (pred_eid.asInt() == eid) {
                    is_in_preds = true;
                    break;
                }
            }
            if (!is_in_preds) return error.V2PredEdgeBijectionMismatch;
        }
    }

    // Confirm every `pred_edge` on every reachable block originates from a reachable terminator edge:
    for (dom.rpo_blocks) |bb_idx| {
        const preds = body.getPredEdges(MirBlockId.fromInt(bb_idx));
        for (preds, 0..) |pred_eid, p_i| {
            if (pred_eid.asInt() >= edge_count or !edge_seen_from_term[pred_eid.asInt()]) {
                return error.V2PredEdgeBijectionMismatch;
            }
            const edge = body.extra_edges.items[pred_eid.asInt()];
            if (edge.target_bb.asInt() != bb_idx) return error.V2PredEdgeBijectionMismatch;
            for (preds[0..p_i]) |earlier| {
                if (earlier == pred_eid) return error.V2PredEdgeBijectionMismatch;
            }
        }
    }

    // [2] Verify `V1` SSA single-definition and strict dominance:
    const inst_total = body.insts.len;
    const def_block = try allocator.alloc(u32, inst_total);
    defer allocator.free(def_block);
    @memset(def_block, NONE_U32);

    const def_rank = try allocator.alloc(u32, inst_total);
    defer allocator.free(def_rank);
    @memset(def_rank, 0);

    for (dom.rpo_blocks) |bb_idx| {
        const bb_id = MirBlockId.fromInt(bb_idx);
        for (body.getBlockParams(bb_id)) |param_val| {
            const raw = param_val.asInt();
            if (raw >= inst_total) return error.V1DominanceViolation;
            if (body.getInst(param_val).op != .block_param) return error.V1DuplicateSsaDefinition;
            if (def_block[raw] != NONE_U32) return error.V1DuplicateSsaDefinition;
            def_block[raw] = bb_idx;
            def_rank[raw] = 0;
        }
        for (body.getBlockInsts(bb_id), 0..) |inst_val, pos| {
            const raw = inst_val.asInt();
            if (raw >= inst_total) return error.V1DominanceViolation;
            if (body.getInst(inst_val).op == .block_param) return error.V1DuplicateSsaDefinition;
            if (def_block[raw] != NONE_U32) return error.V1DuplicateSsaDefinition;
            def_block[raw] = bb_idx;
            def_rank[raw] = @intCast(pos + 1);
        }
    }

    // Helper checking dominance of `raw_val` used at `(use_bb, use_rank)`:
    const DomCheckCtx = struct {
        dom_tree: *const DominatorTree,
        def_blocks: []const u32,
        def_ranks: []const u32,
        total: usize,

        fn checkVal(
            ctx: @This(),
            raw_val: u32,
            use_bb: MirBlockId,
            use_rank: u32,
        ) MirVerifyError!void {
            if (raw_val == NONE_U32 or raw_val >= ctx.total) return error.V1DominanceViolation;
            const d_bb = ctx.def_blocks[raw_val];
            if (d_bb == NONE_U32) return error.V1DominanceViolation;
            if (d_bb == use_bb.asInt()) {
                if (ctx.def_ranks[raw_val] >= use_rank) return error.V1DominanceViolation;
            } else if (!ctx.dom_tree.isDominatorOf(MirBlockId.fromInt(d_bb), use_bb)) {
                return error.V1DominanceViolation;
            }
        }

        fn checkPlaceIndices(
            ctx: @This(),
            mir_body: *const MirBody,
            raw_place: u32,
            use_bb: MirBlockId,
            use_rank: u32,
        ) MirVerifyError!void {
            if (raw_place >= mir_body.places.items.len) return error.V3InvalidPlaceProjection;
            for (mir_body.getPlaceProjections(PlaceId.fromInt(raw_place))) |proj| {
                if (proj.kind == .index) {
                    try ctx.checkVal(proj.payload, use_bb, use_rank);
                }
            }
        }
    };
    const v1_ctx = DomCheckCtx{
        .dom_tree = &dom,
        .def_blocks = def_block,
        .def_ranks = def_rank,
        .total = inst_total,
    };

    // [3] Verify `V3` `MirPlace` projection type well-formedness:
    for (0..body.places.items.len) |place_i| {
        try verifySinglePlaceType(body, PlaceId.fromInt(@intCast(place_i)), pool, sym_table);
    }

    // Verify all instruction, projection, terminator, call, and edge SSA uses (`V1`):
    for (dom.rpo_blocks) |bb_idx| {
        const bb_id = MirBlockId.fromInt(bb_idx);
        for (body.getBlockInsts(bb_id), 0..) |inst_val, pos| {
            const rank: u32 = @intCast(pos + 1);
            const inst = body.getInst(inst_val);
            switch (inst.op) {
                .block_param, .const_scalar, .fn_addr => {},
                .ghost_storage_init, .ghost_storage_deinit => {
                    if (inst.operands.lhs >= body.locals.items.len) return error.V3InvalidPlaceProjection;
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
                    try v1_ctx.checkPlaceIndices(body, inst.operands.lhs, bb_id, rank);
                },
                .place_store => {
                    try v1_ctx.checkPlaceIndices(body, inst.operands.lhs, bb_id, rank);
                    try v1_ctx.checkVal(inst.operands.rhs, bb_id, rank);
                },
                .ghost_access_end,
                .copy_val,
                .unary_op,
                .aggregate_extract,
                .bitfield_extract,
                => {
                    try v1_ctx.checkVal(inst.operands.lhs, bb_id, rank);
                },
                .bin_op => {
                    try v1_ctx.checkVal(inst.operands.lhs, bb_id, rank);
                    try v1_ctx.checkVal(inst.operands.rhs, bb_id, rank);
                },
                .aggregate_insert => {
                    try v1_ctx.checkVal(inst.operands.lhs, bb_id, rank);
                    if (inst.operands.rhs + 2 > body.extra_args.items.len) return error.V1DominanceViolation;
                    try v1_ctx.checkVal(body.extra_args.items[inst.operands.rhs + 1], bb_id, rank);
                },
                .bitfield_insert => {
                    if (inst.operands.lhs + 2 > body.extra_args.items.len) return error.V1DominanceViolation;
                    try v1_ctx.checkVal(body.extra_args.items[inst.operands.lhs], bb_id, rank);
                    try v1_ctx.checkVal(body.extra_args.items[inst.operands.lhs + 1], bb_id, rank);
                },
                .aggregate_make => {
                    const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                    switch (agg_kind) {
                        .array_repeat => try v1_ctx.checkVal(inst.operands.lhs, bb_id, rank),
                        .tagged_variant => {
                            const elem_len = inst.operands.rhs & 0xFFFF;
                            for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + elem_len]) |v_id| {
                                try v1_ctx.checkVal(v_id, bb_id, rank);
                            }
                        },
                        .closure_make => {
                            const cap_len = body.extra_args.items[inst.operands.rhs];
                            const cap_start = inst.operands.rhs + 1;
                            for (body.extra_args.items[cap_start .. cap_start + cap_len]) |v_id| {
                                try v1_ctx.checkVal(v_id, bb_id, rank);
                            }
                        },
                        .tuple_agg, .struct_agg, .array_elems, .str_concat, .fmt_args_make => {
                            for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |v_id| {
                                try v1_ctx.checkVal(v_id, bb_id, rank);
                            }
                        },
                    }
                },
                .intrinsic_op => {
                    const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                    if (ikind.hasPlaceInLhs()) {
                        try v1_ctx.checkPlaceIndices(body, inst.operands.lhs, bb_id, rank);
                        if (ikind.hasSsaFlagInRhs() and inst.operands.rhs != NONE_U32) {
                            try v1_ctx.checkVal(inst.operands.rhs, bb_id, rank);
                        }
                    } else if (ikind.hasExtraArgs() and inst.operands.rhs > 0) {
                        if (inst.operands.lhs + inst.operands.rhs > body.extra_args.items.len) {
                            return error.V1DominanceViolation;
                        }
                        for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |v_id| {
                            try v1_ctx.checkVal(v_id, bb_id, rank);
                        }
                    }
                },
            }
        }

        const term_rank: u32 = std.math.maxInt(u32);
        const term = body.blocks.items[bb_idx].terminator;
        switch (term.kind) {
            .ret => {
                if (term.cond_or_val != NONE_U32) {
                    try v1_ctx.checkVal(term.cond_or_val, bb_id, term_rank);
                }
            },
            .cond_br, .switch_int, .coro_suspend => {
                try v1_ctx.checkVal(term.cond_or_val, bb_id, term_rank);
            },
            .call => {
                const call_site = body.calls.items[term.cond_or_val];
                try v1_ctx.checkVal(call_site.callee_val.asInt(), bb_id, term_rank);
                for (0..call_site.args_len) |arg_i| {
                    const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                    const word = body.extra_args.items[call_site.args_start + arg_i];
                    if (mode == .let_mode or mode == .sink_mode) {
                        try v1_ctx.checkVal(word, bb_id, term_rank);
                    } else {
                        try v1_ctx.checkPlaceIndices(body, word, bb_id, term_rank);
                    }
                }
                for (0..call_site.call_borrows_len) |bor_i| {
                    const tok_raw = body.extra_args.items[call_site.call_borrows_start + bor_i];
                    try v1_ctx.checkVal(tok_raw, bb_id, term_rank);
                }
            },
            else => {},
        }

        for (body.getOutgoingEdges(bb_id)) |edge| {
            for (body.extra_args.items[edge.args_start .. edge.args_start + edge.args_len]) |arg_raw| {
                try v1_ctx.checkVal(arg_raw, bb_id, term_rank);
            }
        }
    }

    // [4] Verify `V4` Ghost bracket stack discipline and Law of Exclusivity:
    if (body.is_ghost_stripped) {
        for (dom.rpo_blocks) |bb_idx| {
            for (body.getBlockInsts(MirBlockId.fromInt(bb_idx))) |inst_val| {
                const inst = body.getInst(inst_val);
                if (inst.op.isGhost() or
                    (inst.op == .intrinsic_op and
                        @as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)).isGhostIntrinsic()))
                {
                    return error.V4PostStripGhostPresent;
                }
            }
        }
    } else if (body.has_ghost_instructions) {
        try verifyV4GhostBrackets(allocator, body, &dom, diagnostic_sink);
    }

    // [5] Verify `V5` definite initialization and `inout`/`set` exit completeness:
    if (!body.is_ghost_stripped) {
        try verifyV5DefiniteInit(allocator, body, pool, &dom, diagnostic_sink);
    }

    // [6] Verify `V6` `contextless` call discipline and `@local` closure non-escape:
    try verifyV6ContextAndClosureEscape(allocator, body, &dom, diagnostic_sink);
}

/// Returns `true` if `projs` starting from `base_local_idx` satisfies `V3` projection type consistency.
fn isValidProjectionChain(
    body: *const MirBody,
    base_local_idx: u32,
    projs: []const MirProjection,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
) bool {
    if (base_local_idx >= body.locals.items.len) return false;
    var cur_ty = pool.unwrapUnderlyingType(body.locals.items[base_local_idx].type_id);
    var active_downcast: ?u32 = null;
    var active_soa_field_ty: ?TypeId = null;

    for (projs) |proj| {
        if (active_soa_field_ty) |soa_field_ty| {
            active_soa_field_ty = null;
            if (proj.kind == .index) {
                cur_ty = soa_field_ty;
                continue;
            } else if (proj.kind == .slice_len) {
                cur_ty = .usize_ty;
                continue;
            }
            return false;
        }
        if (cur_ty.isError()) return true;
        const node = pool.getNode(cur_ty);
        switch (proj.kind) {
            .deref => {
                if (active_downcast != null) return false;
                if (node.tag != .ref_ty and node.tag != .mut_ref_ty and node.tag != .raw_ptr_ty) {
                    return false;
                }
                cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            },
            .downcast => {
                if (active_downcast != null) return false;
                switch (node.tag) {
                    .optional_ty, .result_ty => {
                        if (proj.payload >= 2) return false;
                    },
                    .enum_ty => {
                        const sym = sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                        var v_count: u32 = 0;
                        if (!sym.target_scope.isNone()) {
                            for (sym_table.getScopeMembers(sym.target_scope)) |m_idx| {
                                if (sym_table.getSymbol(m_idx).kind == .enum_variant_sym) v_count += 1;
                            }
                        }
                        if (proj.payload >= v_count) return false;
                    },
                    else => return false,
                }
                active_downcast = proj.payload;
            },
            .field => {
                if (active_downcast) |tag_ord| {
                    active_downcast = null;
                    cur_ty = resolveVerifierVariantPayload(pool, sym_table, cur_ty, tag_ord) orelse
                        return false;
                    if (proj.payload > 0) {
                        cur_ty = resolveVerifierFieldType(pool, sym_table, cur_ty, proj.payload) orelse
                            return false;
                    }
                } else {
                    cur_ty = resolveVerifierFieldType(pool, sym_table, cur_ty, proj.payload) orelse
                        return false;
                }
            },
            .index => {
                if (active_downcast != null) return false;
                if (cur_ty == .str_ty) {
                    cur_ty = .u8_ty;
                    continue;
                }
                if (unionSliceElemType(pool, cur_ty)) |elem_ty| {
                    cur_ty = elem_ty;
                    continue;
                }
                if (node.tag != .array_ty and node.tag != .slice_ty and
                    node.tag != .soa_array_ty and node.tag != .soa_slice_ty and
                    node.tag != .soa_vec_ty and node.tag != .raw_ptr_ty)
                {
                    return false;
                }
                cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            },
            .soa_elem => {
                if (active_downcast != null) return false;
                if (node.tag != .soa_array_ty and node.tag != .soa_slice_ty and node.tag != .soa_vec_ty) {
                    return false;
                }
                const elem_struct_ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                active_soa_field_ty = resolveVerifierFieldType(pool, sym_table, elem_struct_ty, proj.payload) orelse
                    return false;
            },
            .slice_len => {
                if (active_downcast != null) return false;
                if (cur_ty != .str_ty and node.tag != .slice_ty and node.tag != .soa_slice_ty and
                    node.tag != .soa_vec_ty and node.tag != .array_ty and node.tag != .soa_array_ty and
                    unionSliceElemType(pool, cur_ty) == null)
                {
                    return false;
                }
                cur_ty = .usize_ty;
            },
        }
    }
    return true;
}

/// Verifies `V3` projection type consistency along `place_id`.
fn verifySinglePlaceType(
    body: *const MirBody,
    place_id: PlaceId,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
) MirVerifyError!void {
    const place = body.places.items[place_id.asInt()];
    if (place.base >= body.locals.items.len) return error.V3InvalidPlaceProjection;
    if (@as(usize, place.proj_start) + place.proj_len > body.projections.items.len) {
        return error.V3InvalidPlaceProjection;
    }
    if (!isValidProjectionChain(body, place.base, body.getPlaceProjections(place_id), pool, sym_table)) {
        return error.V3InvalidPlaceProjection;
    }
}

/// Resolves field/tuple element `ordinal` on `agg_ty` without mutating `pool`.
fn resolveVerifierFieldType(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    agg_ty: TypeId,
    ordinal: u32,
) ?TypeId {
    const unwrapped = pool.unwrapUnderlyingType(agg_ty);
    if (unwrapped.isError()) return unwrapped;
    if (unwrapped == .source_loc_ty) {
        return switch (ordinal) {
            0, 1 => .str_ty,
            2, 3 => .u32_ty,
            else => null,
        };
    }
    if (unwrapped == .fmt_spec_ty) {
        return switch (ordinal) {
            0 => .u32_ty,
            1, 2 => .u16_ty,
            else => null,
        };
    }
    const node = pool.getNode(unwrapped);
    switch (node.tag) {
        .tuple_ty => {
            const elems = pool.getTupleElements(unwrapped);
            if (ordinal >= elems.len) return null;
            return pool.unwrapUnderlyingType(TypeId.fromInt(elems[ordinal]));
        },
        .struct_ty, .union_ty => {
            const sym = sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
            if (sym.target_scope.isNone()) return null;
            const subst = type_system.NominalTypeSubst.init(pool, sym_table, unwrapped);
            var cur_ord: u32 = 0;
            for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                const mem_sym = sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .field_sym) continue;
                if (cur_ord == ordinal) {
                    return pool.unwrapUnderlyingType(subst.resolve(mem_sym.type_id));
                }
                cur_ord += 1;
            }
            return null;
        },
        else => return null,
    }
}

/// Resolves sum-type payload `TypeId` at `tag_ord` without mutating `pool`.
fn resolveVerifierVariantPayload(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    sum_ty: TypeId,
    tag_ord: u32,
) ?TypeId {
    const unwrapped = pool.unwrapUnderlyingType(sum_ty);
    const node = pool.getNode(unwrapped);
    return switch (node.tag) {
        .optional_ty => if (tag_ord == 1)
            pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs))
        else if (tag_ord == 0)
            .unit_ty
        else
            null,
        .result_ty => if (tag_ord == 0)
            pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs))
        else if (tag_ord == 1)
            pool.unwrapUnderlyingType(TypeId.fromInt(node.rhs))
        else
            null,
        .enum_ty => blk: {
            const sym = sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
            if (sym.target_scope.isNone()) break :blk null;
            const subst = type_system.NominalTypeSubst.init(pool, sym_table, unwrapped);
            var cur_ord: u32 = 0;
            for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                const mem_sym = sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .enum_variant_sym) continue;
                if (cur_ord == tag_ord) {
                    break :blk pool.unwrapUnderlyingType(subst.resolve(mem_sym.type_id));
                }
                cur_ord += 1;
            }
            break :blk null;
        },
        else => null,
    };
}

/// Verifies `V4` pre-strip Ghost bracket stack balance and Law of Exclusivity (`E0301`).
fn verifyV4GhostBrackets(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    dom: *const DominatorTree,
    diagnostic_sink: ?*DiagnosticSink,
) MirVerifyError!void {
    const block_count = body.blocks.items.len;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const a_alloc = arena.allocator();

    const in_stacks = try a_alloc.alloc(?[]GhostStackItem, block_count);
    @memset(in_stacks, null);
    in_stacks[0] = &.{};

    var worklist: std.ArrayListUnmanaged(u32) = .empty;
    try worklist.append(a_alloc, 0);
    var head: usize = 0;

    while (head < worklist.items.len) : (head += 1) {
        const bb_idx = worklist.items[head];
        const bb_id = MirBlockId.fromInt(bb_idx);
        const start_stack = in_stacks[bb_idx] orelse continue;

        var cur_stack: std.ArrayListUnmanaged(GhostStackItem) = .empty;
        try cur_stack.appendSlice(a_alloc, start_stack);

        for (body.getBlockInsts(bb_id)) |inst_val| {
            const inst = body.getInst(inst_val);
            if (inst.op.isGhostAccessOpen()) {
                const new_place = PlaceId.fromInt(inst.operands.lhs);
                for (cur_stack.items) |active| {
                    if (hasOverlappingPlaces(body, active.place_id, new_place) and
                        (active.op != .ghost_access_let or inst.op != .ghost_access_let))
                    {
                        try emitVerifierDiagnostic(
                            diagnostic_sink,
                            body.file_id,
                            .e0301_use_after_free,
                            "overlapping exclusive (`inout`/`set`) and active Ghost borrow (`V4`)",
                        );
                        return error.V4GhostExclusivityConflict;
                    }
                }
                try cur_stack.append(a_alloc, .{
                    .token_val = inst_val,
                    .place_id = new_place,
                    .op = inst.op,
                });
            } else if (inst.op == .ghost_access_end) {
                const closed_tok = MirValueId.fromInt(inst.operands.lhs);
                if (cur_stack.items.len == 0 or
                    cur_stack.items[cur_stack.items.len - 1].token_val != closed_tok)
                {
                    return error.V4UnbalancedGhostStack;
                }
                _ = cur_stack.pop();
            }
        }

        const term = body.blocks.items[bb_idx].terminator;
        if (term.kind == .ret and cur_stack.items.len != 0) {
            return error.V4UnbalancedGhostStack;
        }

        const out_slice = try a_alloc.dupe(GhostStackItem, cur_stack.items);
        for (body.getOutgoingEdges(bb_id)) |edge| {
            const dst = edge.target_bb.asInt();
            if (!dom.isReachable(edge.target_bb)) continue;
            if (in_stacks[dst]) |existing| {
                if (existing.len != out_slice.len) return error.V4UnbalancedGhostStack;
                for (existing, out_slice) |ea, eb| {
                    if (ea.token_val != eb.token_val or ea.place_id != eb.place_id or ea.op != eb.op) {
                        return error.V4UnbalancedGhostStack;
                    }
                }
            } else {
                in_stacks[dst] = out_slice;
                try worklist.append(a_alloc, dst);
            }
        }
    }
}

/// Returns `true` if `place_a` and `place_b` denote the exact same base local and projection chain.
fn isSamePlacePath(body: *const MirBody, place_a: PlaceId, place_b: PlaceId) bool {
    if (place_a == place_b) return true;
    const rec_a = body.places.items[place_a.asInt()];
    const rec_b = body.places.items[place_b.asInt()];
    if (rec_a.base != rec_b.base or rec_a.proj_len != rec_b.proj_len) return false;
    const projs_a = body.getPlaceProjections(place_a);
    const projs_b = body.getPlaceProjections(place_b);
    for (projs_a, projs_b) |step_a, step_b| {
        if (step_a.kind != step_b.kind or step_a.payload != step_b.payload) return false;
    }
    return true;
}

/// Returns `true` if `prefix_id` is an equal or shallower projection prefix of `target_id`.
fn isPlacePrefixOrEqual(body: *const MirBody, prefix_id: PlaceId, target_id: PlaceId) bool {
    if (prefix_id == target_id) return true;
    const rec_pre = body.places.items[prefix_id.asInt()];
    const rec_tgt = body.places.items[target_id.asInt()];
    if (rec_pre.base != rec_tgt.base or rec_pre.proj_len > rec_tgt.proj_len) return false;
    const projs_pre = body.getPlaceProjections(prefix_id);
    const projs_tgt = body.getPlaceProjections(target_id);
    for (0..projs_pre.len) |step_i| {
        if (projs_pre[step_i].kind != projs_tgt[step_i].kind or
            projs_pre[step_i].payload != projs_tgt[step_i].payload)
        {
            return false;
        }
    }
    return true;
}

/// Returns `true` if `prefix_id` is a strict ancestor prefix (`proj_len < target_id.proj_len`) of `target_id`.
fn isPlaceStrictPrefix(body: *const MirBody, prefix_id: PlaceId, target_id: PlaceId) bool {
    const rec_pre = body.places.items[prefix_id.asInt()];
    const rec_tgt = body.places.items[target_id.asInt()];
    return rec_pre.proj_len < rec_tgt.proj_len and isPlacePrefixOrEqual(body, prefix_id, target_id);
}

/// Returns `true` if `raw_val` originates from an explicit `.Err(…)` variant construction (`tag == 1`).
fn isKnownErrVariantSsaVal(body: *const MirBody, raw_val: u32) bool {
    var cur = raw_val;
    var steps: usize = 0;
    while (cur < body.insts.len and steps < 8) : (steps += 1) {
        const inst = body.getInst(MirValueId.fromInt(cur));
        if (inst.op == .copy_val) {
            cur = inst.operands.lhs;
            continue;
        }
        if (inst.op == .aggregate_make) {
            const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            if (agg_kind == .tagged_variant) {
                return (inst.operands.rhs >> 16) == 1;
            }
        }
        break;
    }
    return false;
}

/// Verifies `V5` definite initialization, partial sub-place moves, and `inout`/`set` exit completeness (`E0302`).
fn verifyV5DefiniteInit(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    pool: *const InternPool,
    dom: *const DominatorTree,
    diagnostic_sink: ?*DiagnosticSink,
) MirVerifyError!void {
    const local_count = body.locals.items.len;
    if (local_count == 0) return;
    const block_count = body.blocks.items.len;

    // Collect distinct sub-places (`proj_len > 0`) moved via `ghost_storage_move`:
    var moved_subplaces: std.ArrayListUnmanaged(PlaceId) = .empty;
    defer moved_subplaces.deinit(allocator);
    for (dom.rpo_blocks) |bb_idx| {
        for (body.getBlockInsts(MirBlockId.fromInt(bb_idx))) |inst_val| {
            const inst = body.getInst(inst_val);
            if (inst.op != .ghost_storage_move or inst.operands.lhs >= body.places.items.len) continue;
            const pl_id = PlaceId.fromInt(inst.operands.lhs);
            if (body.places.items[pl_id.asInt()].proj_len == 0) continue;
            var has_existing = false;
            for (moved_subplaces.items) |existing_pl| {
                if (isSamePlacePath(body, existing_pl, pl_id)) {
                    has_existing = true;
                    break;
                }
            }
            if (!has_existing) try moved_subplaces.append(allocator, pl_id);
        }
    }

    const sub_count = moved_subplaces.items.len;
    const state_width = local_count + sub_count;

    const in_states = try allocator.alloc(bool, block_count * state_width);
    defer allocator.free(in_states);
    const out_states = try allocator.alloc(bool, block_count * state_width);
    defer allocator.free(out_states);

    // Entry root locals start `false` (uninitialized); sub-places start `true` (unmoved); non-entry blocks start `true`:
    @memset(in_states, true);
    @memset(out_states, true);
    @memset(in_states[0..local_count], false);

    const scratch = try allocator.alloc(bool, state_width);
    defer allocator.free(scratch);

    // [1] Compute greatest fixed point over reachable blocks in RPO:
    var has_changed = true;
    while (has_changed) {
        has_changed = false;
        for (dom.rpo_blocks) |bb_idx| {
            const base_off = @as(usize, bb_idx) * state_width;
            if (bb_idx != 0) {
                @memset(scratch, true);
                for (body.getPredEdges(MirBlockId.fromInt(bb_idx))) |pred_eid| {
                    const src_bb = body.extra_edges.items[pred_eid.asInt()].src_bb;
                    if (!dom.isReachable(src_bb)) continue;
                    const src_off = @as(usize, src_bb.asInt()) * state_width;
                    for (0..state_width) |slot_i| {
                        scratch[slot_i] = scratch[slot_i] and out_states[src_off + slot_i];
                    }
                }
                if (!std.mem.eql(bool, in_states[base_off .. base_off + state_width], scratch)) {
                    @memcpy(in_states[base_off .. base_off + state_width], scratch);
                    has_changed = true;
                }
            }

            @memcpy(scratch, in_states[base_off .. base_off + state_width]);
            applyInitTransfer(body, moved_subplaces.items, local_count, MirBlockId.fromInt(bb_idx), scratch);
            if (!std.mem.eql(bool, out_states[base_off .. base_off + state_width], scratch)) {
                @memcpy(out_states[base_off .. base_off + state_width], scratch);
                has_changed = true;
            }
        }
    }

    // [2] Replay converged entry states and verify every read, deref deinit, and `.ret` exit:
    for (dom.rpo_blocks) |bb_idx| {
        const base_off = @as(usize, bb_idx) * state_width;
        @memcpy(scratch, in_states[base_off .. base_off + state_width]);
        const bb_id = MirBlockId.fromInt(bb_idx);

        for (body.getBlockInsts(bb_id)) |inst_val| {
            const inst = body.getInst(inst_val);
            switch (inst.op) {
                .ghost_storage_init => {
                    const lid = inst.operands.lhs;
                    scratch[lid] = true;
                    for (moved_subplaces.items, 0..) |sub_pl, sub_i| {
                        if (body.places.items[sub_pl.asInt()].base == lid) {
                            scratch[local_count + sub_i] = true;
                        }
                    }
                },
                .ghost_storage_deinit => {
                    const lid = inst.operands.lhs;
                    for (moved_subplaces.items, 0..) |sub_pl, sub_i| {
                        if (body.places.items[sub_pl.asInt()].base == lid and !scratch[local_count + sub_i]) {
                            const projs = body.getPlaceProjections(sub_pl);
                            if (projs.len > 0 and projs[0].kind == .deref) {
                                try emitVerifierDiagnostic(
                                    diagnostic_sink,
                                    body.file_id,
                                    .e0302_use_after_move,
                                    "cannot leave dereferenced `&mut` target uninitialized after move (`V5`)",
                                );
                                return error.V5IncompleteExitInitialization;
                            }
                        }
                    }
                    scratch[lid] = false;
                    for (moved_subplaces.items, 0..) |sub_pl, sub_i| {
                        if (body.places.items[sub_pl.asInt()].base == lid) {
                            scratch[local_count + sub_i] = true;
                        }
                    }
                },
                .ghost_storage_move => {
                    const pl_id = PlaceId.fromInt(inst.operands.lhs);
                    const pl_rec = body.places.items[pl_id.asInt()];
                    if (pl_rec.proj_len == 0) {
                        scratch[pl_rec.base] = false;
                    } else {
                        for (moved_subplaces.items, 0..) |sub_pl, sub_i| {
                            if (hasOverlappingPlaces(body, pl_id, sub_pl)) {
                                scratch[local_count + sub_i] = false;
                            }
                        }
                    }
                },
                .place_store => {
                    const pl_id = PlaceId.fromInt(inst.operands.lhs);
                    const pl_rec = body.places.items[pl_id.asInt()];
                    if (pl_rec.proj_len == 0) {
                        if (scratch[pl_rec.base]) {
                            for (moved_subplaces.items, 0..) |sub_pl, sub_i| {
                                if (body.places.items[sub_pl.asInt()].base == pl_rec.base and
                                    !scratch[local_count + sub_i])
                                {
                                    const projs = body.getPlaceProjections(sub_pl);
                                    if (projs.len > 0 and projs[0].kind == .deref) {
                                        try emitVerifierDiagnostic(
                                            diagnostic_sink,
                                            body.file_id,
                                            .e0302_use_after_move,
                                            "cannot overwrite `&mut` binding while pointee is moved-from (`V5`)",
                                        );
                                        return error.V5IncompleteExitInitialization;
                                    }
                                }
                            }
                        }
                        scratch[pl_rec.base] = true;
                        for (moved_subplaces.items, 0..) |sub_pl, sub_i| {
                            if (body.places.items[sub_pl.asInt()].base == pl_rec.base) {
                                scratch[local_count + sub_i] = true;
                            }
                        }
                    } else {
                        if (!scratch[pl_rec.base]) {
                            try emitVerifierDiagnostic(
                                diagnostic_sink,
                                body.file_id,
                                .e0302_use_after_move,
                                "projection write through uninitialized or moved local (`V5`)",
                            );
                            return error.V5ReadUninitializedOrMoved;
                        }
                        for (moved_subplaces.items, 0..) |sub_pl, sub_i| {
                            if (!scratch[local_count + sub_i] and isPlaceStrictPrefix(body, sub_pl, pl_id)) {
                                try emitVerifierDiagnostic(
                                    diagnostic_sink,
                                    body.file_id,
                                    .e0302_use_after_move,
                                    "projection write into moved sub-place (`V5`)",
                                );
                                return error.V5ReadUninitializedOrMoved;
                            }
                        }
                        for (moved_subplaces.items, 0..) |sub_pl, sub_i| {
                            if (isPlacePrefixOrEqual(body, pl_id, sub_pl)) {
                                scratch[local_count + sub_i] = true;
                            }
                        }
                    }
                },
                .ghost_access_let,
                .ghost_access_inout,
                .place_load,
                .place_discriminant,
                => {
                    const pl_id = PlaceId.fromInt(inst.operands.lhs);
                    const pl_rec = body.places.items[pl_id.asInt()];
                    if (!scratch[pl_rec.base]) {
                        try emitVerifierDiagnostic(
                            diagnostic_sink,
                            body.file_id,
                            .e0302_use_after_move,
                            "read of uninitialized or moved local (`V5`)",
                        );
                        return error.V5ReadUninitializedOrMoved;
                    }
                    for (moved_subplaces.items, 0..) |sub_pl, sub_i| {
                        if (!scratch[local_count + sub_i] and hasOverlappingPlaces(body, pl_id, sub_pl)) {
                            try emitVerifierDiagnostic(
                                diagnostic_sink,
                                body.file_id,
                                .e0302_use_after_move,
                                "read of partially moved place (`V5`)",
                            );
                            return error.V5ReadUninitializedOrMoved;
                        }
                    }
                },
                else => {},
            }
        }

        const term = body.blocks.items[bb_idx].terminator;
        if (term.kind == .ret) {
            if (!scratch[0]) {
                try emitVerifierDiagnostic(
                    diagnostic_sink,
                    body.file_id,
                    .e0302_use_after_move,
                    "return slot `_0` is not definitely initialized at `.ret` (`V5`)",
                );
                return error.V5IncompleteExitInitialization;
            }
            const ret_unwrapped = pool.unwrapUnderlyingType(body.ret_ty);
            const is_result_ret = !ret_unwrapped.isError() and pool.getNode(ret_unwrapped).tag == .result_ty;
            const is_known_err_ret = is_result_ret and
                (body.blocks.items[bb_idx].isCleanupPad() or isKnownErrVariantSsaVal(body, term.cond_or_val));
            for (0..body.param_count) |param_i| {
                const slot_i = 1 + param_i;
                if (slot_i < local_count) {
                    const mode = body.locals.items[slot_i].mode();
                    if ((mode == .inout_mode or (mode == .set_mode and !is_known_err_ret)) and !scratch[slot_i]) {
                        try emitVerifierDiagnostic(
                            diagnostic_sink,
                            body.file_id,
                            .e0302_use_after_move,
                            "`&mut` or `&out` parameter is not definitely initialized on return (`V5`)",
                        );
                        return error.V5IncompleteExitInitialization;
                    }
                }
            }
            for (moved_subplaces.items, 0..) |sub_pl, sub_i| {
                if (scratch[local_count + sub_i]) continue;
                const sub_rec = body.places.items[sub_pl.asInt()];
                const projs = body.getPlaceProjections(sub_pl);
                const has_deref_root = projs.len > 0 and projs[0].kind == .deref;
                const is_borrowed_param_place = sub_rec.base >= 1 and sub_rec.base <= body.param_count and
                    (body.locals.items[sub_rec.base].mode() == .inout_mode or
                        body.locals.items[sub_rec.base].mode() == .set_mode);
                if (has_deref_root or is_borrowed_param_place) {
                    try emitVerifierDiagnostic(
                        diagnostic_sink,
                        body.file_id,
                        .e0302_use_after_move,
                        "borrowed `inout`/`&mut` place left partially moved on return (`V5`)",
                    );
                    return error.V5IncompleteExitInitialization;
                }
            }
        }
    }
}

/// Applies initialization and partial-move state transitions across instructions in `bb_id`.
fn applyInitTransfer(
    body: *const MirBody,
    moved_subplaces: []const PlaceId,
    local_count: usize,
    bb_id: MirBlockId,
    state: []bool,
) void {
    for (body.getBlockInsts(bb_id)) |inst_val| {
        const inst = body.getInst(inst_val);
        switch (inst.op) {
            .ghost_storage_init => {
                const lid = inst.operands.lhs;
                state[lid] = true;
                for (moved_subplaces, 0..) |sub_pl, sub_i| {
                    if (body.places.items[sub_pl.asInt()].base == lid) {
                        state[local_count + sub_i] = true;
                    }
                }
            },
            .ghost_storage_deinit => {
                const lid = inst.operands.lhs;
                state[lid] = false;
                for (moved_subplaces, 0..) |sub_pl, sub_i| {
                    if (body.places.items[sub_pl.asInt()].base == lid) {
                        state[local_count + sub_i] = true;
                    }
                }
            },
            .ghost_storage_move => {
                const pl_id = PlaceId.fromInt(inst.operands.lhs);
                const pl_rec = body.places.items[pl_id.asInt()];
                if (pl_rec.proj_len == 0) {
                    state[pl_rec.base] = false;
                } else {
                    for (moved_subplaces, 0..) |sub_pl, sub_i| {
                        if (hasOverlappingPlaces(body, pl_id, sub_pl)) {
                            state[local_count + sub_i] = false;
                        }
                    }
                }
            },
            .place_store => {
                const pl_id = PlaceId.fromInt(inst.operands.lhs);
                const pl_rec = body.places.items[pl_id.asInt()];
                if (pl_rec.proj_len == 0) {
                    state[pl_rec.base] = true;
                    for (moved_subplaces, 0..) |sub_pl, sub_i| {
                        if (body.places.items[sub_pl.asInt()].base == pl_rec.base) {
                            state[local_count + sub_i] = true;
                        }
                    }
                } else {
                    for (moved_subplaces, 0..) |sub_pl, sub_i| {
                        if (isPlacePrefixOrEqual(body, pl_id, sub_pl)) {
                            state[local_count + sub_i] = true;
                        }
                    }
                }
            },
            else => {},
        }
    }
}

/// Verifies `V6` `contextless` call discipline and `@local` closure non-escape (`E0306`).
fn verifyV6ContextAndClosureEscape(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    dom: *const DominatorTree,
    diagnostic_sink: ?*DiagnosticSink,
) MirVerifyError!void {
    // [1] `contextless` call & context-intrinsic check:
    if (body.is_contextless) {
        for (dom.rpo_blocks) |bb_idx| {
            for (body.getBlockInsts(MirBlockId.fromInt(bb_idx))) |inst_val| {
                const inst = body.getInst(inst_val);
                if (inst.op == .intrinsic_op and
                    @as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)).isContextIntrinsic())
                {
                    return error.V6ContextlessCallViolation;
                }
            }
            const term = body.blocks.items[bb_idx].terminator;
            if (term.kind == .coro_suspend) {
                return error.V6ContextlessCallViolation;
            }
            if (term.kind == .call) {
                const cs = body.calls.items[term.cond_or_val];
                if (!cs.is_callee_contextless) {
                    return error.V6ContextlessCallViolation;
                }
            }
        }
    }

    // [2] `@local` closure taint propagation & non-escape check (`E0306`):
    var has_any_local_closure = false;
    for (body.locals.items) |loc| {
        if (loc.flags().is_local_closure) {
            has_any_local_closure = true;
            break;
        }
    }
    if (!has_any_local_closure) {
        outer: for (dom.rpo_blocks) |bb_idx| {
            for (body.getBlockInsts(MirBlockId.fromInt(bb_idx))) |inst_val| {
                if (body.getInst(inst_val).flags.is_local_closure) {
                    has_any_local_closure = true;
                    break :outer;
                }
            }
        }
    }
    if (!has_any_local_closure) return;

    const tainted_local = try allocator.alloc(bool, body.locals.items.len);
    defer allocator.free(tainted_local);
    for (body.locals.items, 0..) |loc, i| {
        tainted_local[i] = loc.flags().is_local_closure;
    }

    const tainted_val = try allocator.alloc(bool, body.insts.len);
    defer allocator.free(tainted_val);
    @memset(tainted_val, false);
    for (dom.rpo_blocks) |bb_idx| {
        for (body.getBlockInsts(MirBlockId.fromInt(bb_idx))) |inst_val| {
            if (body.getInst(inst_val).flags.is_local_closure) {
                tainted_val[inst_val.asInt()] = true;
            }
        }
    }

    var has_changed = true;
    while (has_changed) {
        has_changed = false;
        for (dom.rpo_blocks) |bb_idx| {
            const bb_id = MirBlockId.fromInt(bb_idx);
            for (body.getBlockInsts(bb_id)) |inst_val| {
                const raw_v = inst_val.asInt();
                const inst = body.getInst(inst_val);
                var is_now_tainted = tainted_val[raw_v];
                switch (inst.op) {
                    .place_load, .place_addr => {
                        const base = body.places.items[inst.operands.lhs].base;
                        if (tainted_local[base]) is_now_tainted = true;
                    },
                    .copy_val, .unary_op, .aggregate_extract => {
                        if (inst.operands.lhs < tainted_val.len and tainted_val[inst.operands.lhs]) {
                            is_now_tainted = true;
                        }
                    },
                    .aggregate_insert => {
                        if (inst.operands.lhs < tainted_val.len and tainted_val[inst.operands.lhs]) {
                            is_now_tainted = true;
                        }
                        if (inst.operands.rhs + 2 <= body.extra_args.items.len) {
                            const ins_val = body.extra_args.items[inst.operands.rhs + 1];
                            if (ins_val < tainted_val.len and tainted_val[ins_val]) is_now_tainted = true;
                        }
                    },
                    .aggregate_make => {
                        const ak: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                        switch (ak) {
                            .array_repeat => {
                                if (inst.operands.lhs < tainted_val.len and tainted_val[inst.operands.lhs]) {
                                    is_now_tainted = true;
                                }
                            },
                            .tuple_agg, .struct_agg, .array_elems, .str_concat, .fmt_args_make => {
                                for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |elem_v| {
                                    if (elem_v < tainted_val.len and tainted_val[elem_v]) is_now_tainted = true;
                                }
                            },
                            .tagged_variant => {
                                const elen = inst.operands.rhs & 0xFFFF;
                                for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + elen]) |elem_v| {
                                    if (elem_v < tainted_val.len and tainted_val[elem_v]) is_now_tainted = true;
                                }
                            },
                            .closure_make => {
                                const cap_len = body.extra_args.items[inst.operands.rhs];
                                const cap_start = inst.operands.rhs + 1;
                                for (body.extra_args.items[cap_start .. cap_start + cap_len]) |cap_v| {
                                    if (cap_v < tainted_val.len and tainted_val[cap_v]) is_now_tainted = true;
                                }
                            },
                        }
                    },
                    .place_store => {
                        const pl = body.places.items[inst.operands.lhs];
                        if (inst.operands.rhs < tainted_val.len and tainted_val[inst.operands.rhs]) {
                            if (!tainted_local[pl.base]) {
                                tainted_local[pl.base] = true;
                                has_changed = true;
                            }
                        }
                    },
                    else => {},
                }
                if (is_now_tainted and !tainted_val[raw_v]) {
                    tainted_val[raw_v] = true;
                    has_changed = true;
                }
            }

            for (body.getOutgoingEdges(bb_id)) |edge| {
                const dst_params = body.getBlockParams(edge.target_bb);
                const call_off: usize = if (body.blocks.items[bb_idx].terminator.kind == .call) 1 else 0;
                for (0..edge.args_len) |arg_i| {
                    const arg_v = body.extra_args.items[edge.args_start + arg_i];
                    if (arg_v < tainted_val.len and tainted_val[arg_v] and
                        call_off + arg_i < dst_params.len)
                    {
                        const param_raw = dst_params[call_off + arg_i].asInt();
                        if (!tainted_val[param_raw]) {
                            tainted_val[param_raw] = true;
                            has_changed = true;
                        }
                    }
                }
            }
        }
    }

    // Check for illegal escapes (`_0` return, `inout`/`set` parameter, `.deref` store, or `sink` call argument):
    if (tainted_local[0]) {
        try emitVerifierDiagnostic(
            diagnostic_sink,
            body.file_id,
            .e0306_region_escape_violation,
            "`@local` stack-pinned closure cannot escape via return slot `_0` (`V6`)",
        );
        return error.V6LocalClosureEscape;
    }
    for (0..body.param_count) |param_i| {
        const slot_i = 1 + param_i;
        if (slot_i < tainted_local.len and tainted_local[slot_i]) {
            const p_mode = body.locals.items[slot_i].mode();
            if (p_mode == .inout_mode or p_mode == .set_mode) {
                try emitVerifierDiagnostic(
                    diagnostic_sink,
                    body.file_id,
                    .e0306_region_escape_violation,
                    "`@local` stack-pinned closure cannot escape via `inout` or `set` parameter (`V6`)",
                );
                return error.V6LocalClosureEscape;
            }
        }
    }

    for (dom.rpo_blocks) |bb_idx| {
        const bb_id = MirBlockId.fromInt(bb_idx);
        for (body.getBlockInsts(bb_id)) |inst_val| {
            const inst = body.getInst(inst_val);
            if (inst.op == .place_store and
                inst.operands.rhs < tainted_val.len and
                tainted_val[inst.operands.rhs])
            {
                const pl_id = PlaceId.fromInt(inst.operands.lhs);
                const pl = body.places.items[pl_id.asInt()];
                if (pl.base == 0) {
                    try emitVerifierDiagnostic(
                        diagnostic_sink,
                        body.file_id,
                        .e0306_region_escape_violation,
                        "`@local` stack-pinned closure cannot be returned (`V6`)",
                    );
                    return error.V6LocalClosureEscape;
                }
                if (pl.base >= 1 and pl.base <= body.param_count) {
                    const p_mode = body.locals.items[pl.base].mode();
                    if (p_mode == .inout_mode or p_mode == .set_mode) {
                        try emitVerifierDiagnostic(
                            diagnostic_sink,
                            body.file_id,
                            .e0306_region_escape_violation,
                            "`@local` stack-pinned closure cannot escape via `inout` or `set` parameter (`V6`)",
                        );
                        return error.V6LocalClosureEscape;
                    }
                }
                for (body.getPlaceProjections(pl_id)) |proj| {
                    if (proj.kind == .deref) {
                        try emitVerifierDiagnostic(
                            diagnostic_sink,
                            body.file_id,
                            .e0306_region_escape_violation,
                            "`@local` stack-pinned closure cannot be stored through pointer/reference (`V6`)",
                        );
                        return error.V6LocalClosureEscape;
                    }
                }
            }
        }

        const term = body.blocks.items[bb_idx].terminator;
        if (term.kind == .ret and term.cond_or_val < tainted_val.len and tainted_val[term.cond_or_val]) {
            try emitVerifierDiagnostic(
                diagnostic_sink,
                body.file_id,
                .e0306_region_escape_violation,
                "`@local` stack-pinned closure cannot be returned (`V6`)",
            );
            return error.V6LocalClosureEscape;
        }
        if (term.kind == .call) {
            const cs = body.calls.items[term.cond_or_val];
            for (0..cs.args_len) |arg_i| {
                const mode = body.call_arg_modes.items[cs.modes_start + arg_i];
                const arg_v = body.extra_args.items[cs.args_start + arg_i];
                if (mode == .sink_mode and arg_v < tainted_val.len and tainted_val[arg_v]) {
                    try emitVerifierDiagnostic(
                        diagnostic_sink,
                        body.file_id,
                        .e0306_region_escape_violation,
                        "`@local` stack-pinned closure cannot escape into `sink` parameter (`V6`)",
                    );
                    return error.V6LocalClosureEscape;
                }
                if ((mode == .inout_mode or mode == .set_mode) and arg_v < body.places.items.len) {
                    const arg_base = body.places.items[arg_v].base;
                    if (arg_base < tainted_local.len and tainted_local[arg_base]) {
                        try emitVerifierDiagnostic(
                            diagnostic_sink,
                            body.file_id,
                            .e0306_region_escape_violation,
                            "`@local` stack-pinned closure cannot escape via `inout` or `set` call argument (`V6`)",
                        );
                        return error.V6LocalClosureEscape;
                    }
                }
            }
        }
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Collection of verified `MirBody` records lowered from a `HirStore`.
pub const MirModuleBundle = struct {
    /// Backing allocator.
    allocator: std.mem.Allocator,
    /// Lowered, SSA-promoted, and `V1`–`V6` verified function/closure/method bodies.
    bodies: std.ArrayListUnmanaged(MirBody) = .empty,

    /// Releases all `MirBody`s owned by `self`.
    pub fn deinit(self: *MirModuleBundle) void {
        for (self.bodies.items) |*b_item| {
            b_item.deinit();
        }
        self.bodies.deinit(self.allocator);
        self.* = undefined;
    }

    /// Finds a lowered `MirBody` by UTF-8 function name (`null` if absent).
    pub fn findBodyByName(
        self: *const MirModuleBundle,
        interner: *const StringInterner,
        target_name: []const u8,
    ) ?*const MirBody {
        for (self.bodies.items) |*b_item| {
            if (b_item.name != .empty and
                std.mem.eql(u8, interner.get(b_item.name), target_name))
            {
                return b_item;
            }
        }
        return null;
    }
};

/// Standalone end-to-end `Source -> HIR -> MIR` bundle for unit and golden snapshot tests.
pub const MirSourceBundle = struct {
    /// Underlying frontend + `HirStore` bundle.
    hir_bundle: hir.HirSourceBundle,
    /// Lowered & verified `MirModuleBundle`.
    mir_bundle: MirModuleBundle,

    /// Releases all `MIR`, `HIR`, and frontend arenas owned by `self`.
    pub fn deinit(self: *MirSourceBundle) void {
        self.mir_bundle.deinit();
        self.hir_bundle.deinit();
        self.* = undefined;
    }
};

/// Lowers a single `HirFnMeta` into a Block-Argument SSA `MirBody` with cross-store `subscript` splicing
/// and verifies `V1`–`V6`.
pub fn lowerHirFnToMirWithSubscripts(
    allocator: std.mem.Allocator,
    hir_store: *const HirStore,
    extra_subscript_stores: []const *const HirStore,
    fn_meta: HirFnMeta,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
) !MirBody {
    var body = MirBody.init(allocator, hir_store.file_id, fn_meta.def_id);
    errdefer body.deinit();

    var lowerer = MirLowerer{
        .allocator = allocator,
        .hir_store = hir_store,
        .extra_hir_stores = extra_subscript_stores,
        .pool = pool,
        .sym_table = sym_table,
        .interner = interner,
        .body = &body,
        .ssa = MirSsaBuilder.init(allocator, &body, &.{}, diagnostic_sink),
        .diagnostic_sink = diagnostic_sink,
    };
    defer lowerer.deinit();

    try lowerer.lowerFunction(fn_meta);

    if (!body.has_overflowed_limits) {
        try verifyMirBody(allocator, &body, pool, sym_table, diagnostic_sink);
    }
    return body;
}

/// Lowers a single `HirFnMeta` into a Block-Argument SSA `MirBody` and verifies `V1`–`V6`.
pub fn lowerHirFnToMir(
    allocator: std.mem.Allocator,
    hir_store: *const HirStore,
    fn_meta: HirFnMeta,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
) !MirBody {
    return lowerHirFnToMirWithSubscripts(
        allocator,
        hir_store,
        &.{},
        fn_meta,
        pool,
        sym_table,
        interner,
        diagnostic_sink,
    );
}

/// Lowers all non-`subscript` bodies in `hir_store` into `MirBody`s with cross-store `subscript` splicing
/// and verifies `V1`–`V6` on every emitted body.
pub fn lowerHirToMirWithSubscripts(
    allocator: std.mem.Allocator,
    hir_store: *const HirStore,
    extra_subscript_stores: []const *const HirStore,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
) !MirModuleBundle {
    var bundle = MirModuleBundle{ .allocator = allocator };
    errdefer bundle.deinit();

    for (hir_store.functions.items) |fn_meta| {
        // Skip `extern` prototypes (`body_hir == .none`), `subscript` templates, and SAST default probes:
        if (fn_meta.body_hir.isNone() or fn_meta.is_subscript or fn_meta.is_sast_default_probe) continue;
        var lowered_body = try lowerHirFnToMirWithSubscripts(
            allocator,
            hir_store,
            extra_subscript_stores,
            fn_meta,
            pool,
            sym_table,
            interner,
            diagnostic_sink,
        );
        errdefer lowered_body.deinit();
        try bundle.bodies.append(allocator, lowered_body);
    }
    return bundle;
}

/// Lowers all non-`subscript` function, method, derived, and closure bodies in `hir_store` into `MirBody`s
/// and automatically runs `verifyMirBody` (`V1`–`V6`) on every emitted body!
pub fn lowerHirToMir(
    allocator: std.mem.Allocator,
    hir_store: *const HirStore,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
) !MirModuleBundle {
    return lowerHirToMirWithSubscripts(allocator, hir_store, &.{}, pool, sym_table, interner, diagnostic_sink);
}

/// Lowers a single `HirFnMeta` into `MirBody` with cross-store `subscript` splicing without pre-SAST `V4`–`V6` gating.
pub fn lowerHirFnToMirForSastWithSubscripts(
    allocator: std.mem.Allocator,
    hir_store: *const HirStore,
    extra_subscript_stores: []const *const HirStore,
    fn_meta: HirFnMeta,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
) !MirBody {
    var body = MirBody.init(allocator, hir_store.file_id, fn_meta.def_id);
    errdefer body.deinit();

    var lowerer = MirLowerer{
        .allocator = allocator,
        .hir_store = hir_store,
        .extra_hir_stores = extra_subscript_stores,
        .pool = pool,
        .sym_table = sym_table,
        .interner = interner,
        .body = &body,
        .ssa = MirSsaBuilder.init(allocator, &body, &.{}, diagnostic_sink),
        .diagnostic_sink = diagnostic_sink,
        .is_for_sast = true,
    };
    defer lowerer.deinit();

    try lowerer.lowerFunction(fn_meta);
    return body;
}

/// Lowers a single `HirFnMeta` into `MirBody` without pre-SAST `V4`/`V5`/`V6` gating so `mir_sast` can analyze it.
pub fn lowerHirFnToMirForSast(
    allocator: std.mem.Allocator,
    hir_store: *const HirStore,
    fn_meta: HirFnMeta,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
) !MirBody {
    return lowerHirFnToMirForSastWithSubscripts(
        allocator,
        hir_store,
        &.{},
        fn_meta,
        pool,
        sym_table,
        interner,
        diagnostic_sink,
    );
}

/// Lowers all non-`subscript` bodies in `hir_store` into `MirModuleBundle` for Phase 6 `mir_sast` with cross-store subscripts.
pub fn lowerHirToMirForSastWithSubscripts(
    allocator: std.mem.Allocator,
    hir_store: *const HirStore,
    extra_subscript_stores: []const *const HirStore,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
) !MirModuleBundle {
    var bundle = MirModuleBundle{ .allocator = allocator };
    errdefer bundle.deinit();

    for (hir_store.functions.items) |fn_meta| {
        if (fn_meta.body_hir.isNone() or fn_meta.is_splice_helper_only) continue;
        var lowered_body = try lowerHirFnToMirForSastWithSubscripts(
            allocator,
            hir_store,
            extra_subscript_stores,
            fn_meta,
            pool,
            sym_table,
            interner,
            diagnostic_sink,
        );
        errdefer lowered_body.deinit();
        try bundle.bodies.append(allocator, lowered_body);
    }
    return bundle;
}

/// Lowers all non-`subscript` bodies in `hir_store` into `MirModuleBundle` for Phase 6 `mir_sast` analysis.
pub fn lowerHirToMirForSast(
    allocator: std.mem.Allocator,
    hir_store: *const HirStore,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
) !MirModuleBundle {
    return lowerHirToMirForSastWithSubscripts(allocator, hir_store, &.{}, pool, sym_table, interner, diagnostic_sink);
}

/// Parses, resolves, type-checks, lowers to `HIR`, lowers to `MIR`, and verifies `V1`–`V6` in one call.
pub fn lowerSourceToMir(
    allocator: std.mem.Allocator,
    file_id: FileId,
    source: []const u8,
    target_layout: TargetLayout,
    eval_hook: hir.ComptimeEvalHook,
) !MirSourceBundle {
    var is_moved_to_bundle = false;
    var interner = try StringInterner.init(allocator);
    errdefer if (!is_moved_to_bundle) interner.deinit();
    var diagnostics = DiagnosticSink.init(allocator);
    errdefer if (!is_moved_to_bundle) diagnostics.deinit();
    var tokens = TokenBuffer.init(allocator);
    errdefer if (!is_moved_to_bundle) tokens.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    errdefer if (!is_moved_to_bundle) cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    errdefer if (!is_moved_to_bundle) ast_arena.deinit();

    _ = try parser.parseSource(
        source,
        file_id,
        &tokens,
        &cst_arena,
        &ast_arena,
        &diagnostics,
        &interner,
    );

    var sym_table = try SymbolTable.init(allocator, &interner);
    errdefer if (!is_moved_to_bundle) sym_table.deinit();
    _ = try symbol_resolver.collectFileModuleItems(
        &sym_table,
        &interner,
        file_id,
        source,
        &tokens,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    try symbol_resolver.resolveFileUseImports(
        &sym_table,
        &interner,
        file_id,
        source,
        &tokens,
        &cst_arena,
        &diagnostics,
    );

    var pool = try InternPool.init(allocator);
    errdefer if (!is_moved_to_bundle) pool.deinit();

    var checker = try type_system.TypeChecker.init(
        allocator,
        &interner,
        &pool,
        &sym_table,
        file_id,
        source,
        &tokens,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    defer checker.deinit();
    checker.target_layout = target_layout;
    try checker.resolveModuleSignatures();
    try checker.checkFileBodies();

    var side_tables = try checker.extractFileSemanticSideTables(allocator);
    errdefer if (!is_moved_to_bundle) side_tables.deinit();

    var hir_store = try hir.lowerFileToHir(
        allocator,
        file_id,
        source,
        &tokens,
        &cst_arena,
        &ast_arena,
        &interner,
        &pool,
        &sym_table,
        &side_tables,
        &diagnostics,
        target_layout,
        eval_hook,
    );
    errdefer if (!is_moved_to_bundle) hir_store.deinit();

    var hir_bundle = hir.HirSourceBundle{
        .allocator = allocator,
        .interner = interner,
        .tokens = tokens,
        .cst_arena = cst_arena,
        .ast_arena = ast_arena,
        .sym_table = sym_table,
        .pool = pool,
        .side_tables = side_tables,
        .hir_store = hir_store,
        .diagnostics = diagnostics,
    };
    is_moved_to_bundle = true;
    errdefer hir_bundle.deinit();

    const mir_bundle = try lowerHirToMir(
        allocator,
        &hir_bundle.hir_store,
        &hir_bundle.pool,
        &hir_bundle.sym_table,
        &hir_bundle.interner,
        &hir_bundle.diagnostics,
    );
    return .{
        .hir_bundle = hir_bundle,
        .mir_bundle = mir_bundle,
    };
}

/// Returns `true` when `raw_ty` unwraps to a nominal `@zero_pad` `struct`, `union`, or `enum` (`DR-20` `D-01`).
pub fn isZeroPadNominalType(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_ty: TypeId,
) bool {
    if (raw_ty.isError()) return false;
    const unwrapped = pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped.isError()) return false;
    const ty_node = pool.getNode(unwrapped);
    if (ty_node.tag != .struct_ty and ty_node.tag != .union_ty and ty_node.tag != .enum_ty) {
        return false;
    }
    const sym_idx = SymbolIndex.fromInt(ty_node.rhs);
    if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return false;
    return sym_table.getSymbol(sym_idx).contract_flags.is_zero_pad;
}

/// Renders a `MirBody` into a deterministic monochrome human-readable dump for golden snapshots.
pub fn renderMir(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    interner: *const StringInterner,
) ![]u8 {
    var out: std.ArrayListUnmanaged(u8) = .empty;
    errdefer out.deinit(allocator);
    var num_buf: [96]u8 = undefined;

    // Header:
    try out.appendSlice(allocator, "mir fn @");
    if (body.name != .empty) {
        try out.appendSlice(allocator, interner.get(body.name));
    } else {
        try out.appendSlice(allocator, "<anon>");
    }
    try out.appendSlice(
        allocator,
        std.fmt.bufPrint(&num_buf, "(params: {d})", .{body.param_count}) catch "",
    );
    if (body.is_async) try out.appendSlice(allocator, " [async]");
    if (body.is_contextless) try out.appendSlice(allocator, " [contextless]");
    if (body.is_ghost_stripped) try out.appendSlice(allocator, " [ghost_stripped]");
    try out.appendSlice(allocator, " {\n");

    // Locals:
    for (body.locals.items, 0..) |loc, li| {
        try out.appendSlice(
            allocator,
            std.fmt.bufPrint(&num_buf, "  local _{d} [{s}]", .{ li, @tagName(loc.mode()) }) catch "",
        );
        if (loc.name != .empty) {
            try out.appendSlice(allocator, " (");
            try out.appendSlice(allocator, interner.get(loc.name));
            try out.append(allocator, ')');
        }
        if (loc.flags().is_address_taken) try out.appendSlice(allocator, " [addr]");
        if (loc.flags().is_local_closure) try out.appendSlice(allocator, " [@local]");
        try out.append(allocator, '\n');
    }

    // Blocks:
    for (body.blocks.items, 0..) |bb, bb_i| {
        const bb_id = MirBlockId.fromInt(@intCast(bb_i));
        try out.appendSlice(
            allocator,
            std.fmt.bufPrint(&num_buf, "  ^bb{d}(", .{bb_i}) catch "",
        );
        for (body.getBlockParams(bb_id), 0..) |p_val, p_i| {
            if (p_i > 0) try out.appendSlice(allocator, ", ");
            try out.appendSlice(
                allocator,
                std.fmt.bufPrint(&num_buf, "%{d}", .{p_val.asInt()}) catch "",
            );
        }
        try out.appendSlice(
            allocator,
            std.fmt.bufPrint(&num_buf, ") [preds: {d}]", .{bb.pred_len}) catch "",
        );
        if (bb.isCleanupPad()) try out.appendSlice(allocator, " [cleanup_pad]");
        try out.appendSlice(allocator, ":\n");

        for (body.getBlockInsts(bb_id)) |inst_val| {
            const inst = body.getInst(inst_val);
            try out.appendSlice(
                allocator,
                std.fmt.bufPrint(
                    &num_buf,
                    "    %{d} = {s}",
                    .{ inst_val.asInt(), @tagName(inst.op) },
                ) catch "",
            );
            switch (inst.op) {
                .bin_op => {
                    const bk: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                    try out.appendSlice(
                        allocator,
                        std.fmt.bufPrint(
                            &num_buf,
                            ".{s} %{d}, %{d}",
                            .{ @tagName(bk), inst.operands.lhs, inst.operands.rhs },
                        ) catch "",
                    );
                },
                .unary_op => {
                    const uk: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                    try out.appendSlice(
                        allocator,
                        std.fmt.bufPrint(&num_buf, ".{s} %{d}", .{ @tagName(uk), inst.operands.lhs }) catch "",
                    );
                },
                .place_load,
                .place_discriminant,
                .place_addr,
                .soa_column_slice,
                .ghost_access_let,
                .ghost_access_inout,
                .ghost_access_set,
                .ghost_storage_move,
                => {
                    try appendRenderedPlace(allocator, body, PlaceId.fromInt(inst.operands.lhs), &out);
                },
                .place_store => {
                    try appendRenderedPlace(allocator, body, PlaceId.fromInt(inst.operands.lhs), &out);
                    try out.appendSlice(
                        allocator,
                        std.fmt.bufPrint(&num_buf, " <- %{d}", .{inst.operands.rhs}) catch "",
                    );
                },
                .ghost_access_end, .copy_val => {
                    try out.appendSlice(
                        allocator,
                        std.fmt.bufPrint(&num_buf, " %{d}", .{inst.operands.lhs}) catch "",
                    );
                },
                .ghost_storage_init, .ghost_storage_deinit => {
                    try out.appendSlice(
                        allocator,
                        std.fmt.bufPrint(&num_buf, " _{d}", .{inst.operands.lhs}) catch "",
                    );
                },
                .intrinsic_op => {
                    const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                    try out.append(allocator, '.');
                    try out.appendSlice(allocator, @tagName(ikind));
                    if (ikind.hasPlaceInLhs()) {
                        try appendRenderedPlace(allocator, body, PlaceId.fromInt(inst.operands.lhs), &out);
                        if (ikind.hasSsaFlagInRhs() and inst.operands.rhs != NONE_U32) {
                            try out.appendSlice(
                                allocator,
                                std.fmt.bufPrint(&num_buf, ", %{d}", .{inst.operands.rhs}) catch "",
                            );
                        } else if (ikind == .ghost_storage_free and inst.operands.rhs != NONE_U32) {
                            try out.appendSlice(
                                allocator,
                                std.fmt.bufPrint(&num_buf, ", reg={d}", .{inst.operands.rhs}) catch "",
                            );
                        }
                    } else if (ikind.hasTypeIdInLhs()) {
                        try out.appendSlice(
                            allocator,
                            std.fmt.bufPrint(&num_buf, " [ty={d}]", .{inst.operands.lhs}) catch "",
                        );
                    } else if (ikind.hasExtraArgs() and inst.operands.rhs > 0 and
                        inst.operands.lhs + inst.operands.rhs <= body.extra_args.items.len)
                    {
                        try out.appendSlice(allocator, " (");
                        for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs], 0..) |arg_v, arg_i| {
                            if (arg_i > 0) try out.appendSlice(allocator, ", ");
                            try out.appendSlice(
                                allocator,
                                std.fmt.bufPrint(&num_buf, "%{d}", .{arg_v}) catch "",
                            );
                        }
                        try out.append(allocator, ')');
                    }
                },
                else => {
                    try out.appendSlice(
                        allocator,
                        std.fmt.bufPrint(
                            &num_buf,
                            " ({d}, {d})",
                            .{ inst.operands.lhs, inst.operands.rhs },
                        ) catch "",
                    );
                },
            }
            if (inst.flags.is_dollar_sub) {
                try out.appendSlice(allocator, " [dollar_sub]");
            }
            if (inst.flags.is_abort_on_panic) {
                try out.appendSlice(allocator, " [abort_on_panic]");
            }
            try out.append(allocator, '\n');
        }

        // Terminator + per-edge arguments:
        const term = bb.terminator;
        try out.appendSlice(allocator, "    term ");
        try out.appendSlice(allocator, @tagName(term.kind));
        if (term.cond_or_val != NONE_U32) {
            try out.appendSlice(
                allocator,
                std.fmt.bufPrint(&num_buf, " [val=%{d}]", .{term.cond_or_val}) catch "",
            );
        }
        const is_abort_term = (term.kind == .call and term.cond_or_val < body.calls.items.len and
            body.calls.items[term.cond_or_val].is_abort_on_panic) or
            (term.kind == .trap and (term.aux_u8 & TRAP_ABORT_ON_PANIC_FLAG) != 0);
        if (is_abort_term) {
            try out.appendSlice(allocator, " [abort_on_panic]");
        }
        for (body.getOutgoingEdges(bb_id)) |edge| {
            try out.appendSlice(
                allocator,
                std.fmt.bufPrint(&num_buf, " -> ^bb{d}(", .{edge.target_bb.asInt()}) catch "",
            );
            for (body.extra_args.items[edge.args_start .. edge.args_start + edge.args_len], 0..) |arg_v, a_i| {
                if (a_i > 0) try out.appendSlice(allocator, ", ");
                try out.appendSlice(
                    allocator,
                    std.fmt.bufPrint(&num_buf, "%{d}", .{arg_v}) catch "",
                );
            }
            try out.append(allocator, ')');
        }
        try out.append(allocator, '\n');
    }

    try out.appendSlice(allocator, "}\n");
    return out.toOwnedSlice(allocator);
}

/// Formats ` place_id` (` _base.proj…`) into `out`.
fn appendRenderedPlace(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    place_id: PlaceId,
    out: *std.ArrayListUnmanaged(u8),
) !void {
    if (place_id.asInt() >= body.places.items.len) return;
    var num_buf: [48]u8 = undefined;
    const place = body.places.items[place_id.asInt()];
    try out.appendSlice(
        allocator,
        std.fmt.bufPrint(&num_buf, " _{d}", .{place.base}) catch "",
    );
    for (body.getPlaceProjections(place_id)) |proj| {
        switch (proj.kind) {
            .deref => try out.appendSlice(allocator, ".*"),
            .field => try out.appendSlice(
                allocator,
                std.fmt.bufPrint(&num_buf, ".f{d}", .{proj.payload}) catch "",
            ),
            .index => try out.appendSlice(
                allocator,
                std.fmt.bufPrint(&num_buf, "[%{d}]", .{proj.payload}) catch "",
            ),
            .downcast => try out.appendSlice(
                allocator,
                std.fmt.bufPrint(&num_buf, "@v{d}", .{proj.payload}) catch "",
            ),
            .soa_elem => try out.appendSlice(
                allocator,
                std.fmt.bufPrint(&num_buf, ".soa_col{d}", .{proj.payload}) catch "",
            ),
            .slice_len => try out.appendSlice(allocator, ".len"),
        }
    }
}

/// Returns `true` if `stem` matches a reserved Windows DOS device name (`CON`, `PRN`, `AUX`, `NUL`,
/// `COM1`–`COM9`, `LPT1`–`LPT9`, case-insensitive, `DR-20` `Fix-17` Gate D).
fn isReservedWindowsEmbedStem(stem: []const u8) bool {
    if (stem.len == 3) {
        return std.ascii.eqlIgnoreCase(stem, "CON") or
            std.ascii.eqlIgnoreCase(stem, "PRN") or
            std.ascii.eqlIgnoreCase(stem, "AUX") or
            std.ascii.eqlIgnoreCase(stem, "NUL");
    }
    if (stem.len == 4 and stem[3] >= '1' and stem[3] <= '9') {
        return std.ascii.eqlIgnoreCase(stem[0..3], "COM") or
            std.ascii.eqlIgnoreCase(stem[0..3], "LPT");
    }
    return false;
}

/// Validates a relative `@embed_bytes(path)` string, rejecting empty paths, absolute paths, Windows
/// drive prefixes, NUL bytes, `.` or `..` segments, empty segments, and reserved Windows device stems (`E0326`).
pub fn isValidSandboxedEmbedPath(rel_path: []const u8) bool {
    if (rel_path.len == 0) return false;
    if (rel_path[0] == '/' or rel_path[0] == '\\') return false;
    if (std.fs.path.isAbsolute(rel_path)) return false;
    for (rel_path) |byte_val| {
        if (byte_val == 0 or byte_val == ':') return false;
    }

    var start_pos: usize = 0;
    var idx: usize = 0;
    while (idx <= rel_path.len) : (idx += 1) {
        const is_sep = idx == rel_path.len or rel_path[idx] == '/' or rel_path[idx] == '\\';
        if (is_sep) {
            const segment = rel_path[start_pos..idx];
            if (segment.len == 0) return false;
            if (std.mem.eql(u8, segment, ".") or std.mem.eql(u8, segment, "..")) return false;
            const trimmed_seg = std.mem.trimEnd(u8, segment, " .");
            if (trimmed_seg.len == 0) return false;
            const dot_pos = std.mem.indexOfScalar(u8, trimmed_seg, '.') orelse trimmed_seg.len;
            const stem = std.mem.trimEnd(u8, trimmed_seg[0..dot_pos], " ");
            if (isReservedWindowsEmbedStem(stem)) return false;
            start_pos = idx + 1;
        }
    }
    return true;
}

/// Returns `true` if canonical file path `canon_target` is strictly nested inside canonical directory
/// `canon_root` on a path-component boundary.
pub fn isCanonicalPathWithinRoot(canon_root: []const u8, canon_target: []const u8) bool {
    if (canon_root.len == 0 or canon_target.len == 0) return false;
    const root_trimmed = std.mem.trimEnd(u8, canon_root, "/\\");
    if (canon_target.len <= root_trimmed.len) return false;

    for (0..root_trimmed.len) |idx| {
        const root_byte = root_trimmed[idx];
        const target_byte = canon_target[idx];
        const is_root_sep = root_byte == '/' or root_byte == '\\';
        const is_target_sep = target_byte == '/' or target_byte == '\\';
        if (is_root_sep and is_target_sep) continue;
        if (builtin.os.tag == .windows) {
            if (std.ascii.toLower(root_byte) != std.ascii.toLower(target_byte)) return false;
        } else {
            if (root_byte != target_byte) return false;
        }
    }

    const boundary_byte = canon_target[root_trimmed.len];
    return boundary_byte == '/' or boundary_byte == '\\';
}

/// Returns `true` if the suffix of `canon_target` beneath `canon_root` matches `rel_path` segment-for-segment
/// without traversing any intermediate symlink or NTFS junction/reparse point (`DR-20` `Fix-17` Gate D).
pub fn isDirectCanonicalSubpath(canon_root: []const u8, canon_target: []const u8, rel_path: []const u8) bool {
    if (!isCanonicalPathWithinRoot(canon_root, canon_target)) return false;
    const root_trimmed = std.mem.trimEnd(u8, canon_root, "/\\");
    const target_rel = canon_target[root_trimmed.len + 1 ..];
    if (target_rel.len != rel_path.len) return false;
    for (0..rel_path.len) |i| {
        const lhs_byte = target_rel[i];
        const rhs_byte = rel_path[i];
        const is_lhs_sep = lhs_byte == '/' or lhs_byte == '\\';
        const is_rhs_sep = rhs_byte == '/' or rhs_byte == '\\';
        if (is_lhs_sep and is_rhs_sep) continue;
        if (builtin.os.tag == .windows) {
            if (std.ascii.toLower(lhs_byte) != std.ascii.toLower(rhs_byte)) return false;
        } else {
            if (lhs_byte != rhs_byte) return false;
        }
    }
    return true;
}

/// Emits a diagnostic at `tok` in `body.file_id` when `diagnostic_sink` is present.
fn emitEmbedDiagnostic(
    diagnostic_sink: ?*DiagnosticSink,
    file_id: FileId,
    tokens: ?*const TokenBuffer,
    tok: TokenIndex,
    code: DiagnosticCode,
    message: []const u8,
    label_msg: []const u8,
) !void {
    const sink = diagnostic_sink orelse return;
    const span = if (tokens) |tbuf|
        (if (!tok.isNone() and tok.asInt() < tbuf.countTokens())
            tbuf.getTokenSpan(file_id, tok)
        else
            Span.init(file_id, 0, 0))
    else
        Span.init(file_id, 0, 0);
    try sink.emit(.{
        .code = code,
        .severity = .err,
        .primary_span = span,
        .message = message,
        .labels = &[_]LabeledSpan{.{
            .span = span,
            .label = label_msg,
            .style = .primary,
        }},
    });
}

/// Resolves the active `EmbedPackageJail` for lexical `origin_file_id` (fail-closed to `.cxtree_only` for `PackageId >= 2`).
pub fn resolveActiveEmbedJail(
    origin_file_id: FileId,
    sym_table: ?*const SymbolTable,
    package_jails: ?*const std.AutoHashMapUnmanaged(PackageId, EmbedPackageJail),
    workspace_root: ?[]const u8,
) EmbedPackageJail {
    const owner_pkg_id: PackageId = if (sym_table != null and !origin_file_id.isNone())
        sym_table.?.getFilePackageId(origin_file_id)
    else
        .root;
    if (package_jails) |jails| {
        if (jails.get(owner_pkg_id)) |configured_jail| return configured_jail;
    }
    if (owner_pkg_id.asInt() >= 2) {
        return .{ .cxtree_only = .{ .pkg_id = owner_pkg_id } };
    }
    if (package_jails != null) {
        if (workspace_root) |ws_root| {
            return .{ .host_dir_jailed = ws_root };
        }
    }
    return .unrestricted_legacy;
}

/// Reads `<root_path>/<rel_path>` via segment-by-segment `openDir(.follow_symlinks = false)` and
/// `openFile(.follow_symlinks = false, .resolve_beneath = true, .allow_directory = false)` with zero TOCTOU.
pub fn readSandboxedHostEmbedFile(
    allocator: std.mem.Allocator,
    io_handle: std.Io,
    root_path: []const u8,
    rel_path: []const u8,
    max_bytes: u64,
) std.mem.Allocator.Error!HostEmbedReadResult {
    const canon_root = std.Io.Dir.cwd().realPathFileAlloc(io_handle, root_path, allocator) catch {
        return .{ .io_error = .{
            .is_not_found = false,
            .message = "`@embed_bytes` workspace root could not be canonicalized",
            .label = "invalid workspace sandbox root",
        } };
    };
    defer allocator.free(canon_root);

    var cur_dir = std.Io.Dir.cwd().openDir(io_handle, canon_root, .{
        .follow_symlinks = false,
    }) catch |dir_err| switch (dir_err) {
        error.SymLinkLoop, error.NotDir => {
            return .{ .sandbox_escape = .{
                .message = "`@embed_bytes` package root cannot be a symlink or non-directory",
                .label = "`@embed_bytes` sandbox violation here",
            } };
        },
        else => {
            return .{ .io_error = .{
                .is_not_found = false,
                .message = "`@embed_bytes` package root directory could not be opened",
                .label = "unreadable package sandbox root",
            } };
        },
    };
    defer cur_dir.close(io_handle);

    // Walk intermediate path components one segment at a time with `.follow_symlinks = false`:
    var seg_start: usize = 0;
    var scan_i: usize = 0;
    var leaf_segment: []const u8 = rel_path;
    while (scan_i <= rel_path.len) : (scan_i += 1) {
        const is_end = scan_i == rel_path.len;
        if (!is_end and rel_path[scan_i] != '/' and rel_path[scan_i] != '\\') continue;
        const seg = rel_path[seg_start..scan_i];
        if (is_end) {
            leaf_segment = seg;
            break;
        }
        const next_dir = cur_dir.openDir(io_handle, seg, .{
            .follow_symlinks = false,
        }) catch |step_err| switch (step_err) {
            error.SymLinkLoop, error.NotDir, error.AccessDenied => {
                return .{ .sandbox_escape = .{
                    .message = "`@embed_bytes` intermediate path segment cannot traverse a symlink or non-directory",
                    .label = "`@embed_bytes` symlink or sandbox escape blocked here",
                } };
            },
            error.FileNotFound => {
                return .{ .io_error = .{
                    .is_not_found = true,
                    .message = "`@embed_bytes` target directory does not exist inside package sandbox",
                    .label = "missing `@embed_bytes` directory",
                } };
            },
            else => {
                return .{ .io_error = .{
                    .is_not_found = false,
                    .message = "`@embed_bytes` intermediate directory could not be opened inside package sandbox",
                    .label = "unreadable `@embed_bytes` directory",
                } };
            },
        };
        cur_dir.close(io_handle);
        cur_dir = next_dir;
        seg_start = scan_i + 1;
    }

    const opened_file = cur_dir.openFile(io_handle, leaf_segment, .{
        .mode = .read_only,
        .allow_directory = false,
        .follow_symlinks = false,
        .resolve_beneath = true,
    }) catch |open_err| switch (open_err) {
        error.SymLinkLoop, error.IsDir, error.NotDir, error.AccessDenied => {
            return .{ .sandbox_escape = .{
                .message = "`@embed_bytes` target cannot be a symlink, reparse point, or directory",
                .label = "`@embed_bytes` symlink or non-regular target blocked here",
            } };
        },
        error.FileNotFound => {
            return .{ .io_error = .{
                .is_not_found = true,
                .message = "`@embed_bytes` target file could not be opened inside workspace sandbox",
                .label = "unreadable `@embed_bytes` file",
            } };
        },
        else => {
            return .{ .io_error = .{
                .is_not_found = false,
                .message = "`@embed_bytes` target file could not be opened inside workspace sandbox",
                .label = "unreadable `@embed_bytes` file",
            } };
        },
    };
    defer opened_file.close(io_handle);

    const file_stat = opened_file.stat(io_handle) catch {
        return .{ .io_error = .{
            .is_not_found = false,
            .message = "`@embed_bytes` target file metadata could not be queried",
            .label = "unreadable `@embed_bytes` file",
        } };
    };
    if (file_stat.kind != .file) {
        return .{ .sandbox_escape = .{
            .message = "`@embed_bytes` target must be a regular file inside the package sandbox",
            .label = "non-regular `@embed_bytes` target blocked here",
        } };
    }
    if (file_stat.size > max_bytes) {
        return .{ .sandbox_escape = .{
            .message = "`@embed_bytes` target file exceeds `MAX_EMBED_BYTES` package sandbox cap",
            .label = "oversized `@embed_bytes` file",
        } };
    }

    const full_path = try std.fs.path.join(allocator, &.{ canon_root, rel_path });
    defer allocator.free(full_path);
    const canon_target = std.Io.Dir.cwd().realPathFileAlloc(io_handle, full_path, allocator) catch {
        return .{ .sandbox_escape = .{
            .message = "`@embed_bytes` target path could not be canonicalized inside package sandbox",
            .label = "`@embed_bytes` sandbox violation here",
        } };
    };
    defer allocator.free(canon_target);

    if (!isDirectCanonicalSubpath(canon_root, canon_target, rel_path)) {
        return .{ .sandbox_escape = .{
            .message = "`@embed_bytes` target resolved outside package sandbox or traversed a symlink/junction",
            .label = "sandbox escape blocked here",
        } };
    }

    const expected_size: usize = @intCast(file_stat.size);
    const file_bytes = try allocator.alloc(u8, expected_size);
    errdefer allocator.free(file_bytes);
    const actual_read = opened_file.readPositionalAll(io_handle, file_bytes, 0) catch {
        allocator.free(file_bytes);
        return .{ .io_error = .{
            .is_not_found = false,
            .message = "`@embed_bytes` target file could not be read from verified descriptor",
            .label = "unreadable `@embed_bytes` file",
        } };
    };
    if (actual_read != expected_size) {
        allocator.free(file_bytes);
        return .{ .io_error = .{
            .is_not_found = false,
            .message = "`@embed_bytes` target file changed size concurrently during read",
            .label = "truncated `@embed_bytes` file",
        } };
    }
    return .{ .ok = file_bytes };
}

/// Resolves a `.cxtree_only` asset strictly through `vfs_map` without touching host filesystem syscalls.
pub fn lookupSandboxedCxTreeEmbedAsset(
    allocator: std.mem.Allocator,
    vfs_map: *const vfs_sourcemap.VfsSourceMap,
    origin_file_id: FileId,
    explicit_prefix: []const u8,
    rel_path: []const u8,
) !?[]const u8 {
    var derived_prefix: []const u8 = std.mem.trimEnd(u8, explicit_prefix, "/\\");
    if (derived_prefix.len == 0 and !origin_file_id.isNone()) {
        const origin_vpath = vfs_map.getFilePath(origin_file_id);
        if (std.mem.startsWith(u8, origin_vpath, "/cx/")) {
            if (std.mem.indexOfScalarPos(u8, origin_vpath, 4, '/')) |slash_pos| {
                derived_prefix = origin_vpath[0..slash_pos];
            }
        }
    }
    if (derived_prefix.len == 0) return null;

    var joined_vpath = try allocator.alloc(u8, derived_prefix.len + 1 + rel_path.len);
    defer allocator.free(joined_vpath);
    @memcpy(joined_vpath[0..derived_prefix.len], derived_prefix);
    joined_vpath[derived_prefix.len] = '/';
    for (rel_path, 0..) |ch_byte, i| {
        joined_vpath[derived_prefix.len + 1 + i] = if (ch_byte == '\\') '/' else ch_byte;
    }
    if (try vfs_map.lookupCxTreeAsset(joined_vpath)) |asset_slice| {
        return asset_slice;
    }
    return null;
}

/// Resolves reachable constant-path `@embed_bytes` calls in `body` into `blob_store` and rewrites them in-place
/// to `MirOp.const_scalar` (`MirConst.raw_blob`), keeping `MirLowerer` pure/I/O-free.
pub fn materializeBodyEmbedBytes(
    body: *MirBody,
    interner: *const StringInterner,
    tokens: ?*const TokenBuffer,
    blob_store: *MirBlobStore,
    options: EmbedMaterializeOptions,
    diagnostic_sink: ?*DiagnosticSink,
) !bool {
    if (body.blocks.items.len == 0) return true;
    const allocator = blob_store.allocator;

    // [1] Compute block reachability from `^bb0` so unreachable dead branches are skipped:
    var is_reachable = try allocator.alloc(bool, body.blocks.items.len);
    defer allocator.free(is_reachable);
    @memset(is_reachable, false);
    var worklist: std.ArrayListUnmanaged(u32) = .empty;
    defer worklist.deinit(allocator);
    is_reachable[0] = true;
    try worklist.append(allocator, 0);
    while (worklist.items.len > 0) {
        const cur_idx = worklist.pop().?;
        for (body.getOutgoingEdges(MirBlockId.fromInt(cur_idx))) |edge| {
            const tgt = edge.target_bb.asInt();
            if (tgt < is_reachable.len and !is_reachable[tgt]) {
                is_reachable[tgt] = true;
                try worklist.append(allocator, tgt);
            }
        }
    }

    // [2] Materialize constant-path `.embed_bytes` in reachable blocks:
    var is_all_ok = true;
    for (0..body.blocks.items.len) |bb_idx| {
        if (!is_reachable[bb_idx]) continue;
        for (body.getBlockInsts(MirBlockId.fromInt(@intCast(bb_idx)))) |inst_val| {
            const inst = body.getInst(inst_val);
            if (inst.op != .intrinsic_op) continue;
            if (@as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)) != .embed_bytes) continue;
            if (inst.operands.rhs == 0 or inst.operands.lhs + inst.operands.rhs > body.extra_args.items.len) {
                continue;
            }
            var cur_val = body.extra_args.items[inst.operands.lhs];
            var hop_budget: u32 = 32;
            while (hop_budget > 0 and cur_val < body.insts.len) : (hop_budget -= 1) {
                const def_inst = body.insts.get(cur_val);
                if (def_inst.op == .copy_val) {
                    cur_val = def_inst.operands.lhs;
                } else {
                    break;
                }
            }
            if (cur_val >= body.insts.len) continue;
            const path_inst = body.insts.get(cur_val);
            if (path_inst.op != .const_scalar or path_inst.operands.lhs >= body.consts.items.len) continue;
            const path_const = body.consts.items[path_inst.operands.lhs];
            if (path_const != .str_val) continue;

            // Resolve lexical `origin_file_id` strictly from `args[1]`, NEVER `body.file_id` when present:
            const origin_file_id: FileId = if (inst.operands.rhs >= 2) blk_origin: {
                var fid_val = body.extra_args.items[inst.operands.lhs + 1];
                var fid_hops: u32 = 32;
                while (fid_hops > 0 and fid_val < body.insts.len) : (fid_hops -= 1) {
                    const def_fid = body.insts.get(fid_val);
                    if (def_fid.op == .copy_val) {
                        fid_val = def_fid.operands.lhs;
                    } else {
                        break;
                    }
                }
                if (fid_val < body.insts.len) {
                    const fid_inst = body.insts.get(fid_val);
                    if (fid_inst.op == .const_scalar and fid_inst.operands.lhs < body.consts.items.len) {
                        const fid_const = body.consts.items[fid_inst.operands.lhs];
                        if (fid_const == .int_val and
                            fid_const.int_val >= 0 and
                            fid_const.int_val <= std.math.maxInt(u32))
                        {
                            break :blk_origin FileId.fromInt(@intCast(fid_const.int_val));
                        }
                    }
                }
                break :blk_origin body.file_id;
            } else body.file_id;

            const rel_path = interner.get(path_const.str_val);
            const tok = if (inst_val.asInt() < body.origin_tokens.items.len)
                body.origin_tokens.items[inst_val.asInt()]
            else
                TokenIndex.none;

            if (!isValidSandboxedEmbedPath(rel_path)) {
                try emitEmbedDiagnostic(
                    diagnostic_sink,
                    body.file_id,
                    tokens,
                    tok,
                    .e0326_embed_path_escape,
                    "`@embed_bytes` path must be a relative package path without `.`, `..`, drive prefixes, or device names",
                    "`@embed_bytes` path escapes package sandbox here",
                );
                is_all_ok = false;
                continue;
            }

            var loaded_bytes: ?[]const u8 = null;
            var owned_disk_buf: ?[]u8 = null;
            defer if (owned_disk_buf) |buf| allocator.free(buf);

            const active_jail = resolveActiveEmbedJail(
                origin_file_id,
                options.sym_table,
                options.package_jails,
                options.workspace_root,
            );
            switch (active_jail) {
                .cxtree_only => |cx_jail| {
                    if (options.vfs_source_map) |vfs_map| {
                        const cx_bytes_opt = lookupSandboxedCxTreeEmbedAsset(
                            allocator,
                            vfs_map,
                            origin_file_id,
                            cx_jail.virtual_root_prefix,
                            rel_path,
                        ) catch |cx_err| {
                            const err_code: DiagnosticCode = if (cx_err == error.CacheIntegrityMismatch)
                                .e0015_cache_integrity_mismatch
                            else
                                .e0004_source_file_io_error;
                            try emitEmbedDiagnostic(
                                diagnostic_sink,
                                body.file_id,
                                tokens,
                                tok,
                                err_code,
                                "`@embed_bytes` external package asset failed content-addressable cache verification",
                                "corrupt or unreadable `.cxtree` asset",
                            );
                            is_all_ok = false;
                            continue;
                        };
                        if (cx_bytes_opt) |cx_bytes| {
                            if (cx_bytes.len > options.max_blob_bytes) {
                                try emitEmbedDiagnostic(
                                    diagnostic_sink,
                                    body.file_id,
                                    tokens,
                                    tok,
                                    .e0326_embed_path_escape,
                                    "`@embed_bytes` target file exceeds `MAX_EMBED_BYTES` package sandbox cap",
                                    "oversized `@embed_bytes` file",
                                );
                                is_all_ok = false;
                                continue;
                            }
                            loaded_bytes = cx_bytes;
                        }
                    }
                    if (loaded_bytes == null) {
                        try emitEmbedDiagnostic(
                            diagnostic_sink,
                            body.file_id,
                            tokens,
                            tok,
                            .e0004_source_file_io_error,
                            "`@embed_bytes` target file does not exist inside external package archive",
                            "missing package `@embed_bytes` asset",
                        );
                        is_all_ok = false;
                        continue;
                    }
                },
                .host_dir_jailed => |jail_root| {
                    if (options.io) |io_handle| {
                        switch (try readSandboxedHostEmbedFile(
                            allocator,
                            io_handle,
                            jail_root,
                            rel_path,
                            options.max_blob_bytes,
                        )) {
                            .ok => |file_bytes| {
                                owned_disk_buf = file_bytes;
                                loaded_bytes = file_bytes;
                            },
                            .sandbox_escape => |esc| {
                                try emitEmbedDiagnostic(
                                    diagnostic_sink,
                                    body.file_id,
                                    tokens,
                                    tok,
                                    .e0326_embed_path_escape,
                                    esc.message,
                                    esc.label,
                                );
                                is_all_ok = false;
                                continue;
                            },
                            .io_error => |io_err| {
                                try emitEmbedDiagnostic(
                                    diagnostic_sink,
                                    body.file_id,
                                    tokens,
                                    tok,
                                    .e0004_source_file_io_error,
                                    io_err.message,
                                    io_err.label,
                                );
                                is_all_ok = false;
                                continue;
                            },
                        }
                    }
                },
                .unrestricted_legacy => {
                    if (options.virtual_files) |vfs_map| {
                        if (vfs_map.get(rel_path)) |vfs_bytes| {
                            if (vfs_bytes.len > options.max_blob_bytes) {
                                try emitEmbedDiagnostic(
                                    diagnostic_sink,
                                    body.file_id,
                                    tokens,
                                    tok,
                                    .e0326_embed_path_escape,
                                    "`@embed_bytes` target file exceeds `MAX_EMBED_BYTES` package sandbox cap",
                                    "oversized `@embed_bytes` file",
                                );
                                is_all_ok = false;
                                continue;
                            }
                            loaded_bytes = vfs_bytes;
                        }
                    }
                    if (loaded_bytes == null) {
                        if (options.workspace_root) |ws_root| {
                            if (options.io) |io_handle| {
                                switch (try readSandboxedHostEmbedFile(
                                    allocator,
                                    io_handle,
                                    ws_root,
                                    rel_path,
                                    options.max_blob_bytes,
                                )) {
                                    .ok => |file_bytes| {
                                        owned_disk_buf = file_bytes;
                                        loaded_bytes = file_bytes;
                                    },
                                    .sandbox_escape => |esc| {
                                        try emitEmbedDiagnostic(
                                            diagnostic_sink,
                                            body.file_id,
                                            tokens,
                                            tok,
                                            .e0326_embed_path_escape,
                                            esc.message,
                                            esc.label,
                                        );
                                        is_all_ok = false;
                                        continue;
                                    },
                                    .io_error => |io_err| {
                                        try emitEmbedDiagnostic(
                                            diagnostic_sink,
                                            body.file_id,
                                            tokens,
                                            tok,
                                            .e0503_forbidden_comptime_operation,
                                            io_err.message,
                                            io_err.label,
                                        );
                                        is_all_ok = false;
                                        continue;
                                    },
                                }
                            }
                        }
                    }
                },
            }

            const raw_bytes = loaded_bytes orelse {
                try emitEmbedDiagnostic(
                    diagnostic_sink,
                    body.file_id,
                    tokens,
                    tok,
                    .e0503_forbidden_comptime_operation,
                    "`@embed_bytes` requires an active workspace root or virtual file mapping",
                    "unavailable `@embed_bytes` file",
                );
                is_all_ok = false;
                continue;
            };

            if (options.compiler_db) |db| {
                _ = try db.recordEmbedSandboxDependency();
                _ = try db.recordEmbeddedFileRead(rel_path, raw_bytes);
            }

            const blob_id = try blob_store.internBlob(rel_path, raw_bytes);
            const const_idx = try body.appendConst(.{
                .raw_blob = .{
                    .blob_id = blob_id,
                    .align_log2 = 0,
                    .byte_len = raw_bytes.len,
                },
            });
            body.insts.set(inst_val.asInt(), .{
                .op = .const_scalar,
                .flags = .{},
                .aux_u16 = 0,
                .type_id = inst.type_id,
                .operands = .{ .lhs = const_idx, .rhs = 0 },
            });
        }
    }
    return is_all_ok;
}

/// Materializes reachable `@embed_bytes` constants across all `bodies` in a module prior to codegen.
pub fn materializeModuleEmbedBytes(
    bodies: []MirBody,
    interner: *const StringInterner,
    tokens: ?*const TokenBuffer,
    blob_store: *MirBlobStore,
    options: EmbedMaterializeOptions,
    diagnostic_sink: ?*DiagnosticSink,
) !bool {
    var is_all_ok = true;
    for (bodies) |*body| {
        if (!(try materializeBodyEmbedBytes(body, interner, tokens, blob_store, options, diagnostic_sink))) {
            is_all_ok = false;
        }
    }
    return is_all_ok;
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_mir_layout_invariants_and_value_zero_validity" {
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(LocalFlags));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(LocalDecl));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(MirPlace));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(MirProjection));
    try std.testing.expectEqual(
        @as(usize, 16),
        @sizeOf(MirOp) + @sizeOf(InstFlags) + @sizeOf(u16) +
            @sizeOf(TypeId) + @sizeOf(MirInst.Operands),
    );
    try std.testing.expectEqual(@as(usize, 12), @sizeOf(MirTerminator));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(MirBasicBlock));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(MirOutgoingEdge));

    // `MirValueId.fromInt(0)` is a valid SSA instruction ID, never `.none`:
    const first_ssa = MirValueId.fromInt(0);
    try std.testing.expect(!first_ssa.isNone());
    try std.testing.expect(MirValueId.none.isNone());
}

test "test_mir_braun_ssa_loop_carried_phi_and_signed_unsigned_float_ops" {
    const alloc = std.testing.allocator;
    const source =
        \\pub fn sum_loop(limit: u32) -> u32 {
        \\    var total: u32 = 0;
        \\    var cur: u32 = 0;
        \\    while cur < limit {
        \\        total = total + cur;
        \\        cur = cur + 1;
        \\    }
        \\    return total;
        \\}
        \\pub fn signed_and_float(lhs_i: i32, rhs_i: i32, lhs_f: f64, rhs_f: f64) -> f64 {
        \\    let diff_i: i32 = lhs_i - rhs_i;
        \\    return (diff_i as f64) + (lhs_f * rhs_f);
        \\}
    ;

    var bundle = try lowerSourceToMir(alloc, FileId.fromInt(1), source, TargetLayout.NATIVE_64, .{});
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    const sum_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "sum_loop").?;
    try std.testing.expect(sum_body.has_ghost_instructions);
    try std.testing.expect(!sum_body.is_ghost_stripped);

    // Loop header block should carry promoted `total` and `cur` as `block_param`s (`>= 2` params):
    var has_loop_header_params = false;
    var has_uadd_checked = false;
    var has_ult = false;
    for (sum_body.blocks.items, 0..) |bb, bb_i| {
        if (bb.paramLen() >= 2) has_loop_header_params = true;
        for (sum_body.getBlockInsts(MirBlockId.fromInt(@intCast(bb_i)))) |inst_val| {
            const inst = sum_body.getInst(inst_val);
            if (inst.op == .bin_op) {
                const bk: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                if (bk == .uadd_checked) has_uadd_checked = true;
                if (bk == .ult) has_ult = true;
            }
        }
    }
    try std.testing.expect(has_loop_header_params);
    try std.testing.expect(has_uadd_checked);
    try std.testing.expect(has_ult);

    const sf_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "signed_and_float").?;
    var has_ssub = false;
    var has_itof_signed = false;
    var has_fmul = false;
    var has_fadd = false;
    for (0..sf_body.blocks.items.len) |bb_i| {
        for (sf_body.getBlockInsts(MirBlockId.fromInt(@intCast(bb_i)))) |inst_val| {
            const inst = sf_body.getInst(inst_val);
            if (inst.op == .bin_op) {
                const bk: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                if (bk == .ssub_checked) has_ssub = true;
                if (bk == .fmul) has_fmul = true;
                if (bk == .fadd) has_fadd = true;
            } else if (inst.op == .unary_op) {
                const uk: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                if (uk == .int_to_float_signed) has_itof_signed = true;
            }
        }
    }
    try std.testing.expect(has_ssub and has_itof_signed and has_fmul and has_fadd);
}

test "test_mir_braun_ssa_duplicate_target_cond_br_and_proj_index_rewrite_and_reseed" {
    const alloc = std.testing.allocator;
    var interner = try StringInterner.init(alloc);
    defer interner.deinit();
    var pool = try InternPool.init(alloc);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(alloc, &interner);
    defer sym_table.deinit();

    var body = MirBody.init(alloc, FileId.fromInt(1), .NONE);
    defer body.deinit();
    body.ret_ty = .i32_ty;

    // `_0` return slot + `_1` `[i32; 4]` array slot:
    const arr_ty = try pool.internArray(.i32_ty, 4, false);
    try body.locals.append(alloc, LocalDecl.init(.empty, .i32_ty, .none, 0, .set_mode, .{
        .is_mut = true,
        .is_address_taken = true,
        .is_return_slot = true,
    }));
    try body.locals.append(alloc, LocalDecl.init(.empty, arr_ty, .none, 0, .let_mode, .{
        .is_mut = true,
        .is_address_taken = true,
    }));
    try body.places.append(alloc, .{ .base = 0, .proj_start = 0, .proj_len = 0 });
    try body.places.append(alloc, .{ .base = 1, .proj_start = 0, .proj_len = 0 });

    const var_types = [2]TypeId{ .i32_ty, .usize_ty };
    var ssa = MirSsaBuilder.init(alloc, &body, &var_types, null);
    defer ssa.deinit();

    const bb0 = try ssa.createBlock(true, false);
    const bb_join = try ssa.createBlock(false, false);

    // Initialize `_1` array in `bb0`:
    _ = try ssa.emitInst(bb0, .{
        .op = .ghost_storage_init,
        .type_id = .unit_ty,
        .operands = .{ .lhs = 1, .rhs = 0 },
    }, .none);
    const c_true = try body.appendConst(.{ .bool_val = true });
    const cond_val = try ssa.emitInst(bb0, .{
        .op = .const_scalar,
        .type_id = .bool_ty,
        .operands = .{ .lhs = c_true, .rhs = 0 },
    }, .none);
    const c_10 = try body.appendConst(.{ .int_val = 10 });
    const v_10 = try ssa.emitInst(bb0, .{
        .op = .const_scalar,
        .type_id = .i32_ty,
        .operands = .{ .lhs = c_10, .rhs = 0 },
    }, .none);
    const c_20 = try body.appendConst(.{ .int_val = 20 });
    const v_20 = try ssa.emitInst(bb0, .{
        .op = .const_scalar,
        .type_id = .i32_ty,
        .operands = .{ .lhs = c_20, .rhs = 0 },
    }, .none);
    const c_idx0 = try body.appendConst(.{ .int_val = 0 });
    const v_idx0 = try ssa.emitInst(bb0, .{
        .op = .const_scalar,
        .type_id = .usize_ty,
        .operands = .{ .lhs = c_idx0, .rhs = 0 },
    }, .none);
    try ssa.writeVariable(1, bb0, v_idx0);

    // Explicit pinned block param on `bb_join` with duplicate target `cond_br %cond, ^bb_join(10), ^bb_join(20)`:
    const explicit_join_p = try ssa.addExplicitBlockParam(bb_join, .i32_ty, .none, false);
    const e_then = try ssa.addOutgoingEdge(bb0, bb_join, &[1]MirValueId{v_10}, std.math.maxInt(u16));
    _ = try ssa.addOutgoingEdge(bb0, bb_join, &[1]MirValueId{v_20}, std.math.maxInt(u16));
    ssa.setTerminator(bb0, .{
        .kind = .cond_br,
        .edge_len = 2,
        .cond_or_val = cond_val.asInt(),
        .edge_start = e_then.asInt(),
    });

    // Read `var 1` BEFORE sealing `bb_join` so it creates a trivial phi used inside `ProjKind.index`:
    const unsealed_idx_phi = try ssa.readVariable(1, bb_join);
    try body.projections.append(alloc, .{ .kind = .index, .payload = unsealed_idx_phi.asInt() });
    const elem_place_id = PlaceId.fromInt(@intCast(body.places.items.len));
    try body.places.append(alloc, .{ .base = 1, .proj_start = 0, .proj_len = 1 });

    const g_open = try ssa.emitInst(bb_join, .{
        .op = .ghost_access_inout,
        .type_id = .unit_ty,
        .operands = .{ .lhs = elem_place_id.asInt(), .rhs = 0 },
    }, .none);
    _ = try ssa.emitInst(bb_join, .{
        .op = .place_store,
        .type_id = .unit_ty,
        .operands = .{ .lhs = elem_place_id.asInt(), .rhs = explicit_join_p.asInt() },
    }, .none);
    _ = try ssa.emitInst(bb_join, .{
        .op = .ghost_access_end,
        .type_id = .unit_ty,
        .operands = .{ .lhs = g_open.asInt(), .rhs = 0 },
    }, .none);
    _ = try ssa.emitInst(bb_join, .{
        .op = .ghost_storage_init,
        .type_id = .unit_ty,
        .operands = .{ .lhs = 0, .rhs = 0 },
    }, .none);
    _ = try ssa.emitInst(bb_join, .{
        .op = .place_store,
        .type_id = .unit_ty,
        .operands = .{ .lhs = 0, .rhs = explicit_join_p.asInt() },
    }, .none);
    ssa.setTerminator(bb_join, .{ .kind = .ret, .cond_or_val = explicit_join_p.asInt() });

    try ssa.sealBlock(bb_join);
    try ssa.finish();

    // Trivial phi in `projections[0].payload` MUST have been rewritten to `v_idx0`:
    try std.testing.expectEqual(v_idx0.asInt(), body.projections.items[0].payload);
    // Duplicate-target `cond_br` edges MUST preserve distinct arguments `v_10` and `v_20`:
    const out_edges = body.getOutgoingEdges(bb0);
    try std.testing.expectEqual(@as(usize, 2), out_edges.len);
    try std.testing.expectEqual(v_10.asInt(), body.extra_args.items[out_edges[0].args_start]);
    try std.testing.expectEqual(v_20.asInt(), body.extra_args.items[out_edges[1].args_start]);

    try verifyMirBody(alloc, &body, &pool, &sym_table, null);

    // Test `initFromExistingBody` pre-seeding existing `MirBody` without losing edge args:
    const sroa_types = [1]TypeId{.i32_ty};
    var reseeded = try MirSsaBuilder.initFromExistingBody(alloc, &body, &sroa_types, null);
    defer reseeded.deinit();
    try reseeded.writeVariable(0, bb0, v_10);
    const read_after = try reseeded.readVariable(0, bb_join);
    try std.testing.expectEqual(v_10, read_after);
    try reseeded.finish();
    try verifyMirBody(alloc, &body, &pool, &sym_table, null);
}

test "test_mir_call_continuation_split_edge_and_hylo_inout_set_modes" {
    const alloc = std.testing.allocator;
    const source =
        \\pub fn fill_and_bump(acc: &mut i32, out_slot: &out i32) -> i32 {
        \\    acc.* = acc.* + 10;
        \\    out_slot.* = acc.* * 2;
        \\    return acc.*;
        \\}
        \\pub fn caller() -> i32 {
        \\    var count: i32 = 5;
        \\    var result_slot: i32;
        \\    let snap: i32 = fill_and_bump(&mut count, &out result_slot);
        \\    return snap + result_slot;
        \\}
    ;

    var bundle = try lowerSourceToMir(alloc, FileId.fromInt(2), source, TargetLayout.NATIVE_64, .{});
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    const caller_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "caller").?;
    var has_seen_call = false;
    for (caller_body.blocks.items, 0..) |bb, bb_i| {
        if (bb.terminator.kind == .call) {
            has_seen_call = true;
            const edges = caller_body.getOutgoingEdges(MirBlockId.fromInt(@intCast(bb_i)));
            try std.testing.expectEqual(@as(usize, 1), edges.len);
            try std.testing.expectEqual(@as(u16, 0), edges[0].args_len);
            const normal_bb = caller_body.blocks.items[edges[0].target_bb.asInt()];
            try std.testing.expectEqual(@as(u16, 1), normal_bb.pred_len);
            try std.testing.expectEqual(@as(u14, 1), normal_bb.paramLen());
        }
    }
    try std.testing.expect(has_seen_call);
}

test "test_mir_subscript_yield_splice_zero_yield_and_soa_bitfield_parity" {
    const alloc = std.testing.allocator;
    const source =
        \\pub struct Vec2 {
        \\    pub x: f32,
        \\    pub y: f32,
        \\}
        \\pub bit_field Flags : u8 {
        \\    pub active: bool | 1,
        \\    pub level: u8 | 3,
        \\    pub reserved: u8 | 4,
        \\}
        \\pub struct SlotArr {
        \\    pub arr: [i32; 4],
        \\}
        \\impl SlotArr {
        \\    pub subscript(idx: usize) -> i32 {
        \\        let { yield self.arr[idx]; }
        \\        inout { yield &mut self.arr[idx]; }
        \\    }
        \\}
        \\pub fn mutate_via_subscript() -> i32 {
        \\    var nums = SlotArr { arr: [1, 2, 3, 4] };
        \\    nums[2] = 99;
        \\    return nums[2];
        \\}
        \\pub fn soa_and_bits(pts: &#soa [Vec2], idx: usize, reg: &mut Flags) -> f32 {
        \\    reg.active = true;
        \\    reg.level = 5;
        \\    let first: f32 = pts[idx].x;
        \\    let second: f32 = pts.x[idx];
        \\    if reg.active {
        \\        return first + second;
        \\    }
        \\    return 0.0;
        \\}
    ;

    var bundle = try lowerSourceToMir(alloc, FileId.fromInt(3), source, TargetLayout.NATIVE_64, .{});
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    // `subscript` template is spliced inline and NOT emitted as a standalone `yield`-bearing `MirBody`:
    try std.testing.expect(bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "subscript") == null);
    const sub_caller = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "mutate_via_subscript",
    ).?;
    try std.testing.expectEqual(@as(usize, 0), sub_caller.calls.items.len);

    const soa_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "soa_and_bits").?;
    var has_bf_insert = false;
    var has_bf_extract = false;
    var soa_elem_count: usize = 0;
    for (soa_body.projections.items) |proj| {
        if (proj.kind == .soa_elem) soa_elem_count += 1;
    }
    for (0..soa_body.blocks.items.len) |bb_i| {
        for (soa_body.getBlockInsts(MirBlockId.fromInt(@intCast(bb_i)))) |inst_val| {
            const op = soa_body.getInst(inst_val).op;
            if (op == .bitfield_insert) has_bf_insert = true;
            if (op == .bitfield_extract) has_bf_extract = true;
        }
    }
    try std.testing.expect(soa_elem_count >= 2);
    try std.testing.expect(has_bf_insert and has_bf_extract);
}

test "test_mir_maranget_jacobs_or_pat_shared_arm_range_intervals_and_guard_fallthrough" {
    const alloc = std.testing.allocator;
    const source =
        \\pub fn classify_code(code: i32) -> i32 {
        \\    return match code {
        \\        1 | 2 | 3 => 10,
        \\        10..=200 => 20,
        \\        val if val > 500 => val,
        \\        _ => 0,
        \\    };
        \\}
    ;

    var bundle = try lowerSourceToMir(alloc, FileId.fromInt(4), source, TargetLayout.NATIVE_64, .{});
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    const match_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "classify_code").?;
    // Confirm `1 | 2 | 3` shares a single `^arm_0` block (`pred_len == 3`):
    var has_shared_or_arm = false;
    for (match_body.blocks.items) |bb| {
        if (bb.pred_len == 3) {
            has_shared_or_arm = true;
            break;
        }
    }
    try std.testing.expect(has_shared_or_arm);
}

test "test_mir_shared_cold_lifo_defer_errdefer_pads_and_render_mir" {
    const alloc = std.testing.allocator;
    const source =
        \\pub fn step_one(flag: bool) -> i32!i32 {
        \\    if flag { return .Ok(10); }
        \\    return .Err(1);
        \\}
        \\pub fn run_txn(a_ok: bool, b_ok: bool, dyn_res: i32!i32) -> i32!i32 {
        \\    var trace: i32 = 0;
        \\    defer { trace = trace + 1; }
        \\    errdefer |err_code| { trace = trace + err_code; }
        \\    let v1: i32 = step_one(a_ok)?;
        \\    let v2: i32 = step_one(b_ok)?;
        \\    if v1 == v2 {
        \\        return dyn_res;
        \\    }
        \\    return .Ok(v1 + v2);
        \\}
    ;

    var bundle = try lowerSourceToMir(alloc, FileId.fromInt(5), source, TargetLayout.NATIVE_64, .{});
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    const txn_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "run_txn").?;
    // Confirm shared cold cleanup pad exists (`isCleanupPad()`) and is shared across `>= 2` error sites:
    var shared_pad_count: usize = 0;
    for (txn_body.blocks.items) |bb| {
        if (bb.isCleanupPad() and bb.pred_len >= 2) {
            shared_pad_count += 1;
        }
    }
    try std.testing.expect(shared_pad_count >= 1);

    const rendered = try renderMir(alloc, txn_body, &bundle.hir_bundle.interner);
    defer alloc.free(rendered);
    try std.testing.expect(std.mem.indexOf(u8, rendered, "mir fn @run_txn") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered, "[cleanup_pad]") != null);
}

test "test_mir_verifier_rejects_v1_through_v6_violations" {
    const alloc = std.testing.allocator;
    var interner = try StringInterner.init(alloc);
    defer interner.deinit();
    var pool = try InternPool.init(alloc);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(alloc, &interner);
    defer sym_table.deinit();

    // Build a minimal valid baseline `MirBody` (`^bb0`: init `_0`, store `0`, `ret`):
    var base_body = MirBody.init(alloc, FileId.fromInt(9), .NONE);
    defer base_body.deinit();
    base_body.ret_ty = .i32_ty;
    try base_body.locals.append(alloc, LocalDecl.init(.empty, .i32_ty, .none, 0, .set_mode, .{
        .is_mut = true,
        .is_address_taken = true,
        .is_return_slot = true,
    }));
    try base_body.places.append(alloc, .{ .base = 0, .proj_start = 0, .proj_len = 0 });

    var ssa = MirSsaBuilder.init(alloc, &base_body, &.{}, null);
    defer ssa.deinit();
    const bb0 = try ssa.createBlock(true, false);
    const init_0 = try ssa.emitInst(bb0, .{
        .op = .ghost_storage_init,
        .type_id = .unit_ty,
        .operands = .{ .lhs = 0, .rhs = 0 },
    }, .none);
    const c_zero = try base_body.appendConst(.{ .int_val = 0 });
    const v_zero = try ssa.emitInst(bb0, .{
        .op = .const_scalar,
        .type_id = .i32_ty,
        .operands = .{ .lhs = c_zero, .rhs = 0 },
    }, .none);
    _ = try ssa.emitInst(bb0, .{
        .op = .place_store,
        .type_id = .unit_ty,
        .operands = .{ .lhs = 0, .rhs = v_zero.asInt() },
    }, .none);
    ssa.setTerminator(bb0, .{ .kind = .ret, .cond_or_val = v_zero.asInt() });
    try ssa.finish();
    try verifyMirBody(alloc, &base_body, &pool, &sym_table, null);

    // [V1] Duplicate SSA definition:
    {
        var bad_v1 = try base_body.clone(alloc);
        defer bad_v1.deinit();
        try bad_v1.block_insts.append(alloc, v_zero);
        bad_v1.blocks.items[0].inst_len += 1;
        try std.testing.expectError(
            error.V1DuplicateSsaDefinition,
            verifyMirBody(alloc, &bad_v1, &pool, &sym_table, null),
        );
    }

    // [V2] Call Continuation Split-Edge violation (`normal_edge.args_len != 0`):
    {
        var bad_v2 = try base_body.clone(alloc);
        defer bad_v2.deinit();
        var bb1 = MirBasicBlock{};
        bb1.setParamLen(1);
        bb1.pred_len = 1;
        bb1.terminator = .{ .kind = .ret, .cond_or_val = v_zero.asInt() };
        try bad_v2.blocks.append(alloc, bb1);
        try bad_v2.calls.append(alloc, .{ .callee_val = v_zero, .ret_ty = .i32_ty });
        try bad_v2.extra_args.append(alloc, v_zero.asInt());
        try bad_v2.extra_edges.append(alloc, .{
            .src_bb = MirBlockId.fromInt(0),
            .target_bb = MirBlockId.fromInt(1),
            .args_start = 0,
            .args_len = 1, // Illegal on `.call` normal edge.
        });
        try bad_v2.pred_edges.append(alloc, EdgeId.fromInt(0));
        bad_v2.blocks.items[1].pred_start = 0;
        bad_v2.blocks.items[0].terminator = .{
            .kind = .call,
            .edge_len = 1,
            .cond_or_val = 0,
            .edge_start = 0,
        };
        try std.testing.expectError(
            error.V2CallContinuationSplitViolation,
            verifyMirBody(alloc, &bad_v2, &pool, &sym_table, null),
        );
    }

    // [V3] Invalid projection (`.deref` on non-pointer `i32` local):
    {
        var bad_v3 = try base_body.clone(alloc);
        defer bad_v3.deinit();
        try bad_v3.projections.append(alloc, .{ .kind = .deref, .payload = 0 });
        try bad_v3.places.append(alloc, .{ .base = 0, .proj_start = 0, .proj_len = 1 });
        try std.testing.expectError(
            error.V3InvalidPlaceProjection,
            verifyMirBody(alloc, &bad_v3, &pool, &sym_table, null),
        );
    }

    // [V4a] Post-strip residual ghost instruction check:
    {
        var bad_v4_post = try base_body.clone(alloc);
        defer bad_v4_post.deinit();
        bad_v4_post.is_ghost_stripped = true;
        try std.testing.expectError(
            error.V4PostStripGhostPresent,
            verifyMirBody(alloc, &bad_v4_post, &pool, &sym_table, null),
        );
    }

    // [V4b] Pre-strip Law of Exclusivity violation (`ghost_access_let` + overlapping `ghost_access_inout`):
    {
        var bad_v4_excl = try base_body.clone(alloc);
        defer bad_v4_excl.deinit();
        const g1 = try bad_v4_excl.appendInst(.{
            .op = .ghost_access_let,
            .type_id = .unit_ty,
            .operands = .{ .lhs = 0, .rhs = 0 },
        }, .none);
        const g2 = try bad_v4_excl.appendInst(.{
            .op = .ghost_access_inout,
            .type_id = .unit_ty,
            .operands = .{ .lhs = 0, .rhs = 0 },
        }, .none);
        try bad_v4_excl.block_insts.append(alloc, g1);
        try bad_v4_excl.block_insts.append(alloc, g2);
        bad_v4_excl.blocks.items[0].inst_len += 2;
        try std.testing.expectError(
            error.V4GhostExclusivityConflict,
            verifyMirBody(alloc, &bad_v4_excl, &pool, &sym_table, null),
        );
    }

    // [V5] Exit without initializing `_0` (convert `init_0` + `place_store` into no-ops):
    {
        var bad_v5 = try base_body.clone(alloc);
        defer bad_v5.deinit();
        bad_v5.insts.items(.op)[init_0.asInt()] = .const_scalar;
        bad_v5.insts.items(.operands)[init_0.asInt()] = .{ .lhs = c_zero, .rhs = 0 };
        bad_v5.block_insts.items.len = 2;
        bad_v5.blocks.items[0].inst_len = 2;
        try std.testing.expectError(
            error.V5IncompleteExitInitialization,
            verifyMirBody(alloc, &bad_v5, &pool, &sym_table, null),
        );
    }

    // [V6] `@local` stack-pinned closure escaping via return slot `_0`:
    {
        var bad_v6 = try base_body.clone(alloc);
        defer bad_v6.deinit();
        try bad_v6.locals.append(alloc, LocalDecl.init(.empty, .i32_ty, .none, 0, .let_mode, .{
            .is_address_taken = true,
            .is_local_closure = true,
        }));
        const closure_place = PlaceId.fromInt(@intCast(bad_v6.places.items.len));
        try bad_v6.places.append(alloc, .{ .base = 1, .proj_start = 0, .proj_len = 0 });
        const init_cl = try bad_v6.appendInst(.{
            .op = .ghost_storage_init,
            .type_id = .unit_ty,
            .operands = .{ .lhs = 1, .rhs = 0 },
        }, .none);
        const load_cl = try bad_v6.appendInst(.{
            .op = .place_load,
            .type_id = .i32_ty,
            .operands = .{ .lhs = closure_place.asInt(), .rhs = 0 },
        }, .none);
        const store_ret = try bad_v6.appendInst(.{
            .op = .place_store,
            .type_id = .unit_ty,
            .operands = .{ .lhs = 0, .rhs = load_cl.asInt() },
        }, .none);
        try bad_v6.block_insts.appendSlice(alloc, &[3]MirValueId{ init_cl, load_cl, store_ret });
        bad_v6.blocks.items[0].inst_len += 3;
        bad_v6.blocks.items[0].terminator.cond_or_val = load_cl.asInt();
        try std.testing.expectError(
            error.V6LocalClosureEscape,
            verifyMirBody(alloc, &bad_v6, &pool, &sym_table, null),
        );
    }

    // [V5b] Read after `ghost_storage_move` (`E0302`):
    {
        var bad_move = try base_body.clone(alloc);
        defer bad_move.deinit();
        try bad_move.locals.append(alloc, LocalDecl.init(.empty, .i32_ty, .none, 0, .let_mode, .{
            .is_address_taken = true,
        }));
        const slot1_place = PlaceId.fromInt(@intCast(bad_move.places.items.len));
        try bad_move.places.append(alloc, .{ .base = 1, .proj_start = 0, .proj_len = 0 });
        const init_1 = try bad_move.appendInst(.{
            .op = .ghost_storage_init,
            .type_id = .unit_ty,
            .operands = .{ .lhs = 1, .rhs = 0 },
        }, .none);
        const move_1 = try bad_move.appendInst(.{
            .op = .ghost_storage_move,
            .type_id = .unit_ty,
            .operands = .{ .lhs = slot1_place.asInt(), .rhs = 0 },
        }, .none);
        const dead_read = try bad_move.appendInst(.{
            .op = .place_load,
            .type_id = .i32_ty,
            .operands = .{ .lhs = slot1_place.asInt(), .rhs = 0 },
        }, .none);
        try bad_move.block_insts.appendSlice(alloc, &[3]MirValueId{ init_1, move_1, dead_read });
        bad_move.blocks.items[0].inst_len += 3;
        try std.testing.expectError(
            error.V5ReadUninitializedOrMoved,
            verifyMirBody(alloc, &bad_move, &pool, &sym_table, null),
        );
    }
}

test "test_mir_derive_bodies_attribute_schema_and_inclusive_u8_range_end_to_end" {
    const alloc = std.testing.allocator;
    const source =
        \\@attribute_schema(targets: [.StructField])
        \\pub struct Column {
        \\    pub width: i32 = 8,
        \\}
        \\@derive(Equatable, Hash, Clone, Debug)
        \\pub struct Point {
        \\    @Column(width: 32)
        \\    pub x: i32,
        \\    pub y: i32,
        \\}
        \\pub fn read_first_col() -> Column? {
        \\    return comptime @field_attr_lookup[Column](@type_info[Point]().id, 0);
        \\}
        \\pub fn count_full_u8_inclusive() -> u32 {
        \\    var total: u32 = 0;
        \\    let low: u8 = 0;
        \\    let high: u8 = 255;
        \\    for idx in low..=high {
        \\        if idx == 128 { continue; }
        \\        total = total + 1;
        \\    }
        \\    return total;
        \\}
    ;

    var bundle = try lowerSourceToMir(alloc, FileId.fromInt(10), source, TargetLayout.NATIVE_64, .{});
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());
    // 5 `@derive` bodies (`eq`, `hash`, `clone`, `debug`, `fmt_debug`) + 2 user functions = 7 verified `MirBody`s:
    try std.testing.expectEqual(@as(usize, 7), bundle.mir_bundle.bodies.items.len);
}

test "test_redteam_3a_mir_mut_ref_linearity_two_phase_borrows_and_match_ref_guards" {
    const alloc = std.testing.allocator;

    // [1] Linear `&mut i32` double-move caught by `V5`, and `&r1.*` + `r1.* = 20` caught by `V4`:
    const double_move_mut_ref_src =
        \\pub fn use_two(first_ref: &mut i32, second_ref: &mut i32) -> i32 {
        \\    return first_ref.* + second_ref.*;
        \\}
        \\pub fn bad_alias(var val: i32) -> i32 {
        \\    let r1: &mut i32 = &mut val;
        \\    let r2: &mut i32 = r1;
        \\    return use_two(r1, r2);
        \\}
    ;
    try std.testing.expectError(
        error.V5ReadUninitializedOrMoved,
        lowerSourceToMir(alloc, FileId.fromInt(30), double_move_mut_ref_src, TargetLayout.NATIVE_64, .{}),
    );

    const reborrow_conflict_src =
        \\pub fn bad_reborrow(r1: &mut i32) -> i32 {
        \\    let shared_view: &i32 = &r1.*;
        \\    r1.* = 20;
        \\    return shared_view.*;
        \\}
    ;
    try std.testing.expectError(
        error.V4GhostExclusivityConflict,
        lowerSourceToMir(alloc, FileId.fromInt(31), reborrow_conflict_src, TargetLayout.NATIVE_64, .{}),
    );

    // [2] `buf.push(buf.len())` and `let count = buf.len(); buf.push(count);` pass `V4` cleanly:
    const vec_push_len_src =
        \\pub struct MiniBuf {
        \\    pub count: usize,
        \\}
        \\impl MiniBuf {
        \\    pub fn len(&self) -> usize {
        \\        return self.count;
        \\}
        \\    pub fn push(&mut self, item: usize) {
        \\        self.count = self.count + item;
        \\    }
        \\}
        \\pub fn push_both(var buf: MiniBuf) -> usize {
        \\    buf.push(buf.len());
        \\    let saved_len: usize = buf.len();
        \\    buf.push(saved_len);
        \\    return buf.len();
        \\}
    ;
    var vec_bundle = try lowerSourceToMir(alloc, FileId.fromInt(32), vec_push_len_src, TargetLayout.NATIVE_64, .{});
    defer vec_bundle.deinit();
    try std.testing.expect(!vec_bundle.hir_bundle.diagnostics.hasErrors());

    // [3] `ref` / `ref mut` match arms, `or_pat` `(1, ref x) | (ref x, 1)`, `let … else` `ref`, and `?` in guard:
    const match_ref_ok_src =
        \\pub fn check_guard(val: i32) -> bool!i32 {
        \\    if val < 0 { return .Err(val); }
        \\    return .Ok(val > 5);
        \\}
        \\pub fn match_refs(var opt_val: i32?, pair_in: (i32, i32)) -> i32!i32 {
        \\    let or_sum: i32 = match pair_in {
        \\        (1, &bound_x) | (&bound_x, 1) => bound_x.*,
        \\        _ => 0,
        \\    };
        \\    let guarded: i32 = match opt_val {
        \\        .Some(&mut slot) if check_guard(slot.*)? => {
        \\            slot.* = slot.* + 10;
        \\            slot.*
        \\        },
        \\        _ => 0,
        \\    };
        \\    let .Some(&kept_ref) = opt_val else {
        \\        return .Ok(or_sum + guarded);
        \\    };
        \\    return .Ok(kept_ref.* + or_sum + guarded);
        \\}
    ;
    var match_bundle = try lowerSourceToMir(alloc, FileId.fromInt(33), match_ref_ok_src, TargetLayout.NATIVE_64, .{});
    defer match_bundle.deinit();
    try std.testing.expect(!match_bundle.hir_bundle.diagnostics.hasErrors());

    // Mutating `opt_val` while `let .Some(&kept_ref) = opt_val else { … };` is still live must fail `V4`:
    const bad_let_else_ref_src =
        \\pub fn mutate_under_let_else_ref(var opt_val: i32?) -> i32 {
        \\    let .Some(&kept_ref) = opt_val else {
        \\        return 0;
        \\    };
        \\    opt_val = .None;
        \\    return kept_ref.*;
        \\}
    ;
    try std.testing.expectError(
        error.V4GhostExclusivityConflict,
        lowerSourceToMir(alloc, FileId.fromInt(34), bad_let_else_ref_src, TargetLayout.NATIVE_64, .{}),
    );
}

test "test_redteam_3a_mir_definite_init_partial_moves_local_closure_escape_and_cleanup_pads" {
    const alloc = std.testing.allocator;

    // [1] Uninitialized `var` across conditional branch caught by `V5`:
    const uninit_var_src =
        \\pub fn maybe_uninit(cond: bool) -> i32 {
        \\    var num: i32;
        \\    if cond {
        \\        num = 1;
        \\    }
        \\    return num;
        \\}
    ;
    try std.testing.expectError(
        error.V5ReadUninitializedOrMoved,
        lowerSourceToMir(alloc, FileId.fromInt(35), uninit_var_src, TargetLayout.NATIVE_64, .{}),
    );

    // [2] Partial double-move of non-`Copy` field caught by `V5`, while sibling move + re-init passes:
    const partial_double_move_src =
        \\pub struct Resource {
        \\    pub lock_ref: &mut i32,
        \\}
        \\pub struct ResPair {
        \\    pub first: Resource,
        \\    pub second: Resource,
        \\}
        \\pub fn bad_partial_move(pair_val: ResPair) -> i32 {
        \\    let moved_a: Resource = pair_val.first;
        \\    let moved_b: Resource = pair_val.first;
        \\    return moved_a.lock_ref.* + moved_b.lock_ref.*;
        \\}
    ;
    try std.testing.expectError(
        error.V5ReadUninitializedOrMoved,
        lowerSourceToMir(alloc, FileId.fromInt(36), partial_double_move_src, TargetLayout.NATIVE_64, .{}),
    );

    const partial_reinit_ok_src =
        \\pub struct Resource {
        \\    pub lock_ref: &mut i32,
        \\}
        \\pub struct ResPair {
        \\    pub first: Resource,
        \\    pub second: Resource,
        \\}
        \\pub fn valid_partial_reinit(var pair_val: own ResPair, fresh_a: &mut i32, fresh_b: &mut i32) {
        \\    let moved_first: Resource = pair_val.first;
        \\    let moved_second: Resource = pair_val.second;
        \\    fresh_a.* = moved_first.lock_ref.* + 1;
        \\    fresh_b.* = moved_second.lock_ref.* + 2;
        \\    pair_val.first = Resource { lock_ref: fresh_a };
        \\    pair_val.second = Resource { lock_ref: fresh_b };
        \\}
    ;
    var reinit_bundle = try lowerSourceToMir(alloc, FileId.fromInt(37), partial_reinit_ok_src, TargetLayout.NATIVE_64, .{});
    defer reinit_bundle.deinit();
    try std.testing.expect(!reinit_bundle.hir_bundle.diagnostics.hasErrors());

    // [3] Moving out of `&mut` parameter without re-initializing before return caught by `V5`:
    const inout_steal_src =
        \\pub struct Resource {
        \\    pub lock_ref: &mut i32,
        \\}
        \\pub fn steal_inout(slot: &mut Resource) -> Resource {
        \\    let stolen: Resource = slot.*;
        \\    return stolen;
        \\}
    ;
    try std.testing.expectError(
        error.V5IncompleteExitInitialization,
        lowerSourceToMir(alloc, FileId.fromInt(38), inout_steal_src, TargetLayout.NATIVE_64, .{}),
    );

    // [4] Captureless closure passes `own` cleanly, while Tier-1 borrow closure, field-stored `@local`, and `&mut` escape fail `V6`:
    const pure_closure_ok_src =
        \\pub fn consume_sink[F](cb: own F) -> i32 {
        \\    _ = cb;
        \\    return 7;
        \\}
        \\pub fn pass_pure() -> i32 {
        \\    return consume_sink(own (|| 42));
        \\}
    ;
    var pure_cl_bundle = try lowerSourceToMir(alloc, FileId.fromInt(39), pure_closure_ok_src, TargetLayout.NATIVE_64, .{});
    defer pure_cl_bundle.deinit();
    try std.testing.expect(!pure_cl_bundle.hir_bundle.diagnostics.hasErrors());

    const anon_local_escape_src =
        \\pub fn consume_sink[F](cb: own F) -> i32 {
        \\    _ = cb;
        \\    return 0;
        \\}
        \\pub fn escape_anon(borrowed: &i32) -> i32 {
        \\    return consume_sink(own (|| borrowed.*));
        \\}
    ;
    try std.testing.expectError(
        error.V6LocalClosureEscape,
        lowerSourceToMir(alloc, FileId.fromInt(40), anon_local_escape_src, TargetLayout.NATIVE_64, .{}),
    );

    const field_local_escape_src =
        \\pub struct Holder[F] {
        \\    pub cb: F,
        \\}
        \\pub fn consume_sink[T](item: own T) -> i32 {
        \\    _ = item;
        \\    return 0;
        \\}
        \\pub fn escape_via_field(borrowed: &i32) -> i32 {
        \\    let pinned_cb = || borrowed.*;
        \\    var box_val = Holder { cb: pinned_cb };
        \\    box_val.cb = pinned_cb;
        \\    return consume_sink(own box_val);
        \\}
    ;
    try std.testing.expectError(
        error.V6LocalClosureEscape,
        lowerSourceToMir(alloc, FileId.fromInt(41), field_local_escape_src, TargetLayout.NATIVE_64, .{}),
    );

    const inout_local_escape_src =
        \\pub fn leak_into_inout[F](out_cb: &mut F, borrowed: &i32) {
        \\    let pinned_cb = || borrowed.*;
        \\    out_cb.* = pinned_cb;
        \\}
    ;
    try std.testing.expectError(
        error.V6LocalClosureEscape,
        lowerSourceToMir(alloc, FileId.fromInt(42), inout_local_escape_src, TargetLayout.NATIVE_64, .{}),
    );

    // [5] Per-scope `errdefer` storage deinits, `i128`/`u128` ranges,
    // `subscript` post-yield ordering, and `distinct Result` `?` + `errdefer`:
    const combined_mir_src =
        \\pub struct GuardedRes {
        \\    pub tag: i32,
        \\}
        \\type TxnResult = distinct (i32!i32);
        \\pub fn fallible_step(ok_flag: bool) -> i32!i32 {
        \\    if ok_flag { return .Ok(5); }
        \\    return .Err(1);
        \\}
        \\pub struct TrackedArr {
        \\    pub arr: [i32; 2],
        \\}
        \\impl TrackedArr {
        \\    pub subscript(post_log: &mut i32, idx: usize) -> i32 {
        \\        let {
        \\            post_log.* = 10;
        \\            yield self.arr[idx];
        \\            post_log.* = post_log.* + self.arr[idx];
        \\        }
        \\        inout {
        \\            post_log.* = 10;
        \\            yield &mut self.arr[idx];
        \\            post_log.* = post_log.* + self.arr[idx];
        \\        }
        \\    }
        \\}
        \\pub fn run_scoped_errdefer(flag_a: bool, flag_b: bool) -> TxnResult {
        \\    var err_count: i32 = 0;
        \\    errdefer { err_count = err_count + 1; }
        \\    {
        \\        let inner_owned = GuardedRes { tag: 1 };
        \\        _ = fallible_step(flag_a)?;
        \\        _ = inner_owned.tag;
        \\    }
        \\    let outer_owned = GuardedRes { tag: 2 };
        \\    let v_b: i32 = fallible_step(flag_b)?;
        \\    return (.Ok(v_b + outer_owned.tag + err_count)) as TxnResult;
        \\}
        \\pub fn wide_ranges(s_val: i128, u_val: u128) -> i32 {
        \\    let s_cls: i32 = match s_val {
        \\        -170141183460469231731687303715884105728..=0 => 1,
        \\        1..=170141183460469231731687303715884105727 => 2,
        \\    };
        \\    let u_cls: i32 = match u_val {
        \\        0..=170141183460469231731687303715884105727 => 10,
        \\        170141183460469231731687303715884105728..=340282366920938463463374607431768211455 => 20,
        \\    };
        \\    return s_cls + u_cls;
        \\}
        \\pub fn use_tracked_subscript() -> i32 {
        \\    var data = TrackedArr { arr: [3, 4] };
        \\    var log_val: i32 = 0;
        \\    data[&mut log_val, 0] = 50;
        \\    var read_back: i32 = 0;
        \\    {
        \\        let elem_ref: &i32 = &data[&mut log_val, 0];
        \\        read_back = elem_ref.*;
        \\    }
        \\    return read_back + log_val;
        \\}
        \\pub fn unit_block_default() {
        \\    let unit_v: () = {};
        \\    return unit_v;
        \\}
    ;
    var comb_bundle = try lowerSourceToMir(alloc, FileId.fromInt(43), combined_mir_src, TargetLayout.NATIVE_64, .{});
    defer comb_bundle.deinit();
    try std.testing.expect(!comb_bundle.hir_bundle.diagnostics.hasErrors());

    // Verify every live `MirValueId` referenced by any reachable terminator or edge belongs to a basic block:
    for (comb_bundle.mir_bundle.bodies.items) |*mir_body| {
        const is_block_owned = try alloc.alloc(bool, mir_body.insts.len);
        defer alloc.free(is_block_owned);
        @memset(is_block_owned, false);
        for (mir_body.block_params.items) |param_v| is_block_owned[param_v.asInt()] = true;
        for (mir_body.block_insts.items) |inst_v| is_block_owned[inst_v.asInt()] = true;
        for (mir_body.blocks.items) |bb_rec| {
            const term = bb_rec.terminator;
            if (term.kind == .unreachable_term) continue;
            if ((term.kind == .ret or term.kind == .cond_br or term.kind == .switch_int) and
                term.cond_or_val != NONE_U32)
            {
                try std.testing.expect(is_block_owned[term.cond_or_val]);
            }
            for (mir_body.extra_edges.items[term.edge_start .. term.edge_start + term.edge_len]) |edge| {
                for (mir_body.extra_args.items[edge.args_start .. edge.args_start + edge.args_len]) |raw_arg| {
                    try std.testing.expect(is_block_owned[raw_arg]);
                }
            }
        }
    }
}

test "test_phase6_mir_intrinsics_vacated_windows_and_subscript_defer" {
    const alloc = std.testing.allocator;
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(MirInst));
    try std.testing.expect(MirIntrinsicKind.zero_pad.hasPlaceInLhs());
    try std.testing.expect(MirIntrinsicKind.drop_in_place.hasPlaceInLhs());
    try std.testing.expect(MirIntrinsicKind.drop_if_live.hasPlaceInLhs());
    try std.testing.expect(MirIntrinsicKind.ghost_storage_free.hasPlaceInLhs());
    try std.testing.expect(!MirIntrinsicKind.bounds_check.hasPlaceInLhs());
    try std.testing.expect(MirIntrinsicKind.drop_if_live.hasSsaFlagInRhs());
    try std.testing.expect(!MirIntrinsicKind.drop_in_place.hasSsaFlagInRhs());
    try std.testing.expect(MirIntrinsicKind.ghost_storage_free.isGhostIntrinsic());
    try std.testing.expect(!MirIntrinsicKind.drop_in_place.isGhostIntrinsic());

    // [1] Lower `.narrow`, `.try_narrow`, `@zero_pad`, wire intrinsics, `@drop_trace`, `bounds_check`, and `Fix-06B` `subscript`:
    const phase6_src =
        \\@zero_pad
        \\@repr(C)
        \\pub struct WireHdr {
        \\    pub tag: u8,
        \\    pub code: u32,
        \\}
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct NonCopyBox {
        \\    pub data: Vec[u32],
        \\}
        \\pub struct BoxArr {
        \\    pub items: [NonCopyBox; 2],
        \\}
        \\impl BoxArr {
        \\    pub subscript(log_slot: &mut i32, idx: usize) -> NonCopyBox {
        \\        let {
        \\            defer { log_slot.* = log_slot.* + 100; }
        \\            yield self.items[idx];
        \\            log_slot.* = log_slot.* + 1;
        \\        }
        \\        inout {
        \\            defer { log_slot.* = log_slot.* + 100; }
        \\            yield &mut self.items[idx];
        \\            log_slot.* = log_slot.* + 1;
        \\        }
        \\    }
        \\}
        \\pub fn inspect_phase6_lowering(raw_num: i32, boxes: &mut BoxArr) -> u32 {
        \\    let narrowed_u8: u8 = raw_num.narrow[u8]();
        \\    let maybe_u8: u8? = raw_num.try_narrow[u8]();
        \\    let hdr = WireHdr { tag: narrowed_u8, code: 7 };
        \\    let hdr_bytes: &[u8] = hdr.as_bytes();
        \\    let casted_u64: u64 = @bit_cast[u64](hdr);
        \\    let decoded_hdr: WireHdr? = @from_bytes[WireHdr](hdr_bytes);
        \\    let viewed_hdr: (&WireHdr)? = @view_bytes[WireHdr](hdr_bytes);
        \\    @drop_trace(42);
        \\    var trace_log: i32 = 0;
        \\    {
        \\        _ = &boxes.*[&mut trace_log, 0];
        \\    }
        \\    boxes.*[&mut trace_log, 1] = NonCopyBox { data: Vec { len: 2 } };
        \\    _ = maybe_u8;
        \\    _ = casted_u64;
        \\    _ = decoded_hdr;
        \\    _ = viewed_hdr;
        \\    return hdr_bytes[0] as u32;
        \\}
    ;
    var bundle = try lowerSourceToMir(alloc, FileId.fromInt(90), phase6_src, TargetLayout.NATIVE_64, .{});
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    const fn_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "inspect_phase6_lowering").?;
    try std.testing.expect(fn_body.vacated_windows.items.len >= 1);

    var cloned_body = try fn_body.clone(alloc);
    defer cloned_body.deinit();
    try std.testing.expectEqual(fn_body.vacated_windows.items.len, cloned_body.vacated_windows.items.len);

    const rendered = try renderMir(alloc, fn_body, &bundle.hir_bundle.interner);
    defer alloc.free(rendered);
    try std.testing.expect(std.mem.indexOf(u8, rendered, "narrow_check") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered, "try_narrow") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered, "zero_pad") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered, "bounds_check") != null);
}

test "test_phase76_stage4_mir_cross_store_subscript_and_nested_fsm_continue" {
    const alloc = std.testing.allocator;
    const mir_vm = @import("mir_vm.zig");

    // [1] Cross-store `subscript` splicing (`lowerHirToMirWithSubscripts` & `ForSastWithSubscripts`):
    {
        const sub_src =
            \\pub struct CounterPair {
            \\    pub slots: [i64; 2],
            \\}
            \\impl CounterPair {
            \\    pub subscript(post_hits: &mut i64, idx: usize) -> i64 {
            \\        let {
            \\            yield self.slots[idx];
            \\            post_hits.* = post_hits.* + 10;
            \\        }
            \\        inout {
            \\            yield &mut self.slots[idx];
            \\            post_hits.* = post_hits.* + 100;
            \\        }
            \\    }
            \\}
            \\pub fn run_cross_subscript() -> i64 {
            \\    var pair = CounterPair { slots: [5, 9] };
            \\    var hits: i64 = 0;
            \\    pair[&mut hits, 1] = 40;
            \\    let read_val: i64 = pair[&mut hits, 1];
            \\    return read_val + hits + pair.slots[0];
            \\}
        ;
        var full_hir = try hir.lowerSourceToHir(alloc, sub_src, TargetLayout.NATIVE_64);
        defer full_hir.deinit();
        try std.testing.expect(!full_hir.diagnostics.hasErrors());

        // Partition `full_hir.hir_store` into a caller-only `HirStore` (zero subscript `HirFnMeta`s) + external store:
        var caller_only_store = HirStore.init(alloc, full_hir.hir_store.file_id);
        defer caller_only_store.deinit();
        caller_only_store.target_layout = full_hir.hir_store.target_layout;
        for (0..full_hir.hir_store.nodes.len) |node_i| {
            _ = try caller_only_store.appendNode(full_hir.hir_store.nodes.get(node_i), .none);
        }
        try caller_only_store.extra_data.appendSlice(alloc, full_hir.hir_store.extra_data.items);
        try caller_only_store.const_pool.appendSlice(alloc, full_hir.hir_store.const_pool.items);
        try caller_only_store.locals.appendSlice(alloc, full_hir.hir_store.locals.items);
        try caller_only_store.patterns.appendSlice(alloc, full_hir.hir_store.patterns.items);
        try caller_only_store.match_arms.appendSlice(alloc, full_hir.hir_store.match_arms.items);
        for (full_hir.hir_store.functions.items) |fn_meta| {
            if (!fn_meta.is_subscript) {
                try caller_only_store.functions.append(alloc, fn_meta);
            }
        }
        try std.testing.expectEqual(@as(usize, 1), caller_only_store.functions.items.len);

        const ext_stores = [1]*const HirStore{&full_hir.hir_store};
        var mir_sink = DiagnosticSink.init(alloc);
        defer mir_sink.deinit();
        var spliced_mod = try lowerHirToMirWithSubscripts(
            alloc,
            &caller_only_store,
            &ext_stores,
            &full_hir.pool,
            &full_hir.sym_table,
            &full_hir.interner,
            &mir_sink,
        );
        defer spliced_mod.deinit();
        try std.testing.expect(!mir_sink.hasErrors());

        var sast_mod = try lowerHirToMirForSastWithSubscripts(
            alloc,
            &caller_only_store,
            &ext_stores,
            &full_hir.pool,
            &full_hir.sym_table,
            &full_hir.interner,
            &mir_sink,
        );
        defer sast_mod.deinit();
        try std.testing.expect(!mir_sink.hasErrors());

        var rodata_pool = mir_vm.RodataPool.init(alloc);
        defer rodata_pool.deinit();
        var vm = try mir_vm.MirVm.init(
            alloc,
            &full_hir.interner,
            &full_hir.pool,
            &full_hir.sym_table,
            &rodata_pool,
            null,
            null,
            .{},
        );
        defer vm.deinit();
        const run_body = spliced_mod.findBodyByName(&full_hir.interner, "run_cross_subscript").?;
        _ = try vm.registerBody(run_body, .none);
        const vm_out = try vm.evalBody(run_body, &.{});
        // `read_val (40) + hits (100 + 10) + pair.slots[0] (5) == 155`:
        try std.testing.expectEqual(@as(i64, 155), vm_out.slot.scalar_i64);
    }

    // [2] Nested `outer: match` `continue :outer` and Phase-0 `cur_ptr.*` freeze:
    {
        const fsm_src =
            \\pub enum OuterState {
            \\    Start,
            \\    Finish(i64),
            \\}
            \\pub enum InnerState {
            \\    First,
            \\    Second,
            \\}
            \\pub fn rebind_raw_i64(ptr_slot: &mut *mut i64, next_ptr: *mut i64) -> i64 {
            \\    ptr_slot.* = next_ptr;
            \\    return 99;
            \\}
            \\pub fn nested_fsm_and_raw_rebind() -> i64 {
            \\    var fsm_res: i64 = 0;
            \\    outer: match OuterState.Start {
            \\        .Start => {
            \\            inner: match InnerState.First {
            \\                .First => continue :inner .Second,
            \\                .Second => continue :outer .Finish(77),
            \\            }
            \\        },
            \\        .Finish(done_v) => {
            \\            fsm_res = done_v;
            \\        },
            \\    }
            \\    var slot_x: i64 = 10;
            \\    var slot_y: i64 = 20;
            \\    var tag_out: i64 = 0;
            \\    var cur_ptr: *mut i64 = &raw mut slot_x;
            \\    unsafe {
            \\        (cur_ptr.*, tag_out) = (rebind_raw_i64(&mut cur_ptr, &raw mut slot_y), 5_i64);
            \\    }
            \\    return fsm_res * 10000 + slot_x * 100 + slot_y + tag_out;
            \\}
        ;
        var fsm_bundle = try lowerSourceToMir(alloc, FileId.fromInt(91), fsm_src, TargetLayout.NATIVE_64, .{});
        defer fsm_bundle.deinit();
        try std.testing.expect(!fsm_bundle.hir_bundle.diagnostics.hasErrors());

        const fsm_body = fsm_bundle.mir_bundle.findBodyByName(
            &fsm_bundle.hir_bundle.interner,
            "nested_fsm_and_raw_rebind",
        ).?;
        for (fsm_body.locals.items) |loc_decl| {
            try std.testing.expect(!loc_decl.flags().is_local_closure);
        }

        var rodata_pool = mir_vm.RodataPool.init(alloc);
        defer rodata_pool.deinit();
        var vm = try mir_vm.MirVm.init(
            alloc,
            &fsm_bundle.hir_bundle.interner,
            &fsm_bundle.hir_bundle.pool,
            &fsm_bundle.hir_bundle.sym_table,
            &rodata_pool,
            null,
            null,
            .{},
        );
        defer vm.deinit();
        for (fsm_bundle.mir_bundle.bodies.items) |*body_ptr| {
            _ = try vm.registerBody(body_ptr, .none);
        }
        const eval_res = try vm.evalBody(fsm_body, &.{});
        // `fsm_res == 77` (`continue :outer .Finish(77)` targets `outer`!), `slot_x == 99`, `slot_y == 20`, `tag_out == 5`:
        try std.testing.expectEqual(@as(i64, 779925), eval_res.slot.scalar_i64);
    }
}

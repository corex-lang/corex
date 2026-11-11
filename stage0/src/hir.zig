//! High-Level Intermediate Representation (`HIR`) Arena & Desugaring Engine
//!
//! Implements Phase 5 (`PLAN.md` §2.1, `DR-02`, `DR-05`, and `DR-13` Deliverable 2) Structure-of-Arrays
//! `HirNode` / `HirStore` lowering from typed `AST` + `BodySemanticSideTables`:
//! - Zero-padding 18-byte SoA `HirNode` layout (`20` bytes AoS) with bounded `MAX_HIR_NODES` and depth caps,
//! - Canonical desugaring of `|>`, postfix `?`, `catch`, `let … else`, `if let`, `while let`, and `is` patterns,
//! - Continue-safe and `u8`-overflow-safe `for` / `while` loop canonicalization, `#soa` projections, and `bit_field` RMW,
//! - Two-phase `@derive(Eq, Hash, Debug, Clone)` body synthesis, `comptime if`/`match`/`for` unrolling, and `renderHir`.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const diagnostic = @import("diag/diagnostic.zig");
const parser = @import("parser.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const query_db = @import("query_db.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const NodeIndex = mem_foundation.NodeIndex;
const ExtraIndex = mem_foundation.ExtraIndex;
/// Re-exported canonical 32-bit `HirIndex` handle.
pub const HirIndex = mem_foundation.HirIndex;
const ScopeId = mem_foundation.ScopeId;
const TypeId = mem_foundation.TypeId;
const DefId = query_db.DefId;
const TokenKind = syntax_arenas.TokenKind;
const CstNodeKind = syntax_arenas.CstNodeKind;
const AstTag = syntax_arenas.AstTag;
const TokenBuffer = syntax_arenas.TokenBuffer;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstArena = syntax_arenas.AstArena;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const LabeledSpan = diagnostic.LabeledSpan;
const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolKind = symbol_resolver.SymbolKind;
const SymbolTable = symbol_resolver.SymbolTable;
const NamespaceMask = symbol_resolver.NamespaceMask;
const InternPool = type_system.InternPool;
const ParamMode = type_system.ParamMode;
const IntrinsicKind = type_system.IntrinsicKind;
const TargetLayout = type_system.TargetLayout;
const BodySemanticSideTables = type_system.BodySemanticSideTables;
const AttrArgValue = type_system.AttrArgValue;

// ---------------------------------------- TYPES ----------------------------------------

// ------------------- HIR Tags & Node Layout -------------------

/// Discriminant for every canonical High-Level IR (`HIR`) node (`DR-13` §2.1).
pub const HirTag = enum(u8) {
    // Declarations (`0..6`):
    /// Translation-unit or inline module root (`lhs = extra_start, rhs = item_len`).
    hir_module = 0,
    /// Function or method declaration (`lhs = fn_meta_index, rhs = body_hir`).
    hir_fn_decl = 1,
    /// Function parameter declaration (`lhs = local_id, rhs = param_mode`).
    hir_param_decl = 2,
    /// Nominal `struct`, `union`, or `bit_field` item (`lhs = def_id, rhs = symbol_index`).
    hir_struct_decl = 3,
    /// Nominal `enum` item (`lhs = def_id, rhs = symbol_index`).
    hir_enum_decl = 4,
    /// Module or block `const` item (`lhs = def_or_sym_id, rhs = init_hir`).
    hir_const_decl = 5,
    /// Local `let` / `var` binding (`lhs = local_id, rhs = init_hir_or_none`).
    hir_local_decl = 6,

    // Leaf & Place Projections (`7..14`):
    /// Interned compile-time constant literal or folded aggregate (`lhs = const_pool_idx, rhs = 0`).
    hir_const_val = 7,
    /// Reference to a function parameter or local slot (`lhs = local_id, rhs = 0`).
    hir_var_ref = 8,
    /// Reference to a global function or constant (`lhs = def_id, rhs = symbol_index`).
    hir_global_ref = 9,
    /// Struct, tuple, or slice `.len` field projection (`lhs = base_hir, rhs = field_ordinal`).
    hir_field_proj = 10,
    /// Array or slice element projection (`lhs = base_hir, rhs = index_hir`).
    hir_index_proj = 11,
    /// `#soa` column element pointer projection (`lhs = base_hir, rhs = extra{field_ordinal, index_hir}`).
    hir_soa_field_ptr = 12,
    /// `bit_field` LSB shift-and-mask read (`lhs = base_hir, rhs = @bitCast(BitSpec)`).
    hir_bitfield_read = 13,
    /// `bit_field` read-modify-write assignment (`lhs = dest_place_hir, rhs = extra{BitSpec, val_hir}`).
    hir_bitfield_rmw = 14,

    // Expressions & Calls (`15..24`):
    /// Prefix unary operation (`lhs = HirUnaryOp, rhs = operand_hir`).
    hir_unary_op = 15,
    /// Explicit `as` or implicit representation coercion (`lhs = src_hir, rhs = HirCastKind`).
    hir_cast = 16,
    /// Infix binary operation (`lhs = extra{lhs_hir, rhs_hir}, rhs = HirBinaryOp`).
    hir_binary_op = 17,
    /// Place assignment (`lhs = dest_place_hir, rhs = rvalue_hir`).
    hir_assign = 18,
    /// Hylo parameter-mode projection wrapper (`lhs = ParamMode, rhs = arg_hir`).
    hir_project_arg = 19,
    /// Direct or indirect function/method call (`lhs = callee_hir, rhs = extra{arg_len, args…}`).
    hir_call = 20,
    /// Compiler `@intrinsic` invocation (`lhs = IntrinsicKind, rhs = extra{type_arg_len, val_arg_len, …}`).
    hir_intrinsic_call = 21,
    /// `subscript` projection call (`lhs = callee_hir, rhs = extra{arg_len, args…}`).
    hir_subscript_call = 22,
    /// Struct, tuple, array, or enum/Option/Result constructor (`lhs = HirConstructKind | (tag << 8), rhs = extra_idx`).
    hir_construct = 23,
    /// Closure expression (`lhs = fn_meta_index, rhs = body_hir`).
    hir_closure = 24,

    // Control Flow, Scopes & Recovery (`25..33`):
    /// Lexical statement block with optional tail expression (`lhs = extra{stmt_len, stmts…}, rhs = tail_hir_or_none`).
    hir_block = 25,
    /// Conditional branch (`lhs = cond_hir, rhs = extra{then_hir, else_hir_or_none}`).
    hir_if = 26,
    /// Canonical pattern match (`lhs = scrutinee_hir, rhs = extra{arm_start, arm_len}`).
    hir_match = 27,
    /// Canonical infinite loop (`lhs = body_hir, rhs = loop_id`).
    hir_loop = 28,
    /// Loop exit jump (`lhs = target_loop_id, rhs = val_hir_or_none`).
    hir_break = 29,
    /// Loop header jump (`lhs = target_loop_id, rhs = 0`).
    hir_continue = 30,
    /// Function exit (`lhs = val_hir_or_none, rhs = ReturnErrorKind`).
    hir_return = 31,
    /// Scope-bound `defer` or `errdefer` registration (`lhs = is_errdefer | (err_local_plus1 << 1), rhs = cleanup_hir`).
    hir_defer = 32,
    /// `subscript` projection `yield` (`lhs = yielded_place_hir, rhs = 0`).
    hir_yield = 33,
    /// Error-recovery poison node preserving downstream IR invariants (`lhs = 0, rhs = 0`).
    hir_error_hole = 34,
};

/// Value category attached to every `HirNode` (`DR-13` §2.1).
pub const ValueCategory = enum(u2) {
    /// Pure temporary value (`0`).
    rvalue = 0,
    /// Immutable addressable memory location (`let` local, immutable parameter, or shared projection).
    place_imm = 1,
    /// Mutable addressable memory location (`var` local, `inout`/`set` parameter, or `&mut` dereference).
    place_mut = 2,
    /// Diverging control-flow expression (`never`).
    diverging = 3,
};

/// Packed 1-byte metadata flags stored per `HirNode` (`DR-13` §2.1).
pub const HirFlags = packed struct(u8) {
    /// Value/place classification of this node.
    category: ValueCategory = .rvalue,
    /// `true` if synthesized during `AST -> HIR` desugaring or `@derive` expansion.
    is_synthetic: bool = false,
    /// `true` if produced by compile-time constant folding or `comptime` unrolling.
    is_comptime_folded: bool = false,
    /// `true` if enclosed inside an `unsafe` block.
    is_unsafe: bool = false,
    /// `true` if tainted by an upstream syntax or type error.
    has_error: bool = false,
    /// Reserved zero padding bits.
    _reserved: u2 = 0,
};

/// Zero-padding 18-byte Structure-of-Arrays `HIR` node (`20` bytes AoS, `[MAJOR-05]`).
pub const HirNode = struct {
    /// Node discriminant (`1` byte).
    tag: HirTag,
    /// Packed category and origin flags (`1` byte).
    flags: HirFlags = .{},
    /// Concrete `InternPool` `TypeId` (`4` bytes; never `.untyped_int_ty` or `.untyped_float_ty`).
    type_id: TypeId,
    /// Anchor `TokenIndex` in the owning `FileId` (`4` bytes).
    origin_token: TokenIndex,
    /// Tag-specific dual 32-bit payload (`8` bytes).
    data: Data = .{},

    /// Contiguous 8-byte operand payload for `HirNode`.
    pub const Data = extern struct {
        /// Primary 32-bit payload word.
        lhs: u32 = 0,
        /// Secondary 32-bit payload word.
        rhs: u32 = 0,
    };
};

// ------------------ Operators, Casts & Specs ------------------

/// Packed 32-bit bit-slice specification for LSB-first `bit_field` extraction and RMW (`DR-13` §2.2).
pub const BitSpec = packed struct(u32) {
    /// Zero-based bit offset from the least-significant bit of the backing integer (`0..127`).
    bit_offset: u8 = 0,
    /// Width of the bit-field member in bits (`1..128`).
    bit_width: u8 = 0,
    /// Width of the enclosing `bit_field` backing integer in bits (`8, 16, 32, 64, 128`).
    backing_bits: u8 = 0,
    /// `true` if the extracted field type requires arithmetic sign-extension.
    is_signed: bool = false,
    /// Reserved zero padding bits.
    _pad: u7 = 0,

    /// Represents `self` as a raw 32-bit unsigned integer.
    pub inline fn asU32(self: BitSpec) u32 {
        return @bitCast(self);
    }

    /// Decodes a `BitSpec` from a raw 32-bit unsigned integer.
    pub inline fn fromU32(raw_bits: u32) BitSpec {
        return @bitCast(raw_bits);
    }
};

/// Classification of `hir_return` for `defer` vs. `errdefer` cleanup routing (`[CRITICAL-08]`).
pub const ReturnErrorKind = enum(u8) {
    /// Infallible return or statically known `.Ok(v)` / `.Some(v)` return (`defer` only).
    normal = 0,
    /// Statically known `.Err(e)` / `.None` or `?`-desugared early return (`errdefer` + `defer`).
    explicit_err = 1,
    /// Dynamic `Result[T, E]` or `T?` value requiring a runtime discriminant check on exit.
    dynamic_fallible = 2,
};

/// Canonical unary operators in `HIR`.
pub const HirUnaryOp = enum(u8) {
    /// Two's-complement or IEEE-754 negation (`-x`).
    neg = 0,
    /// Boolean logical negation (`not b` / `!b` on `bool`).
    logical_not = 1,
    /// Bitwise complement (`!x` on integers).
    bit_not = 2,
    /// Shared address-of borrow (`&place`).
    addr_of = 3,
    /// Exclusive mutable address-of borrow (`&mut place`).
    addr_of_mut = 4,
    /// Pointer or reference dereference (`*ptr`).
    deref = 5,
};

/// Canonical binary operators in `HIR` (short-circuiting `and`/`or` remain explicit until `MIR` CFG lowering).
pub const HirBinaryOp = enum(u8) {
    /// Checked addition (`+`).
    add = 0,
    /// Checked subtraction (`-`).
    sub = 1,
    /// Checked multiplication (`*`).
    mul = 2,
    /// Checked division (`/`).
    div = 3,
    /// Checked remainder (`%`).
    rem = 4,
    /// Modular wrapping addition (`+%`).
    wrap_add = 5,
    /// Modular wrapping subtraction (`-%`).
    wrap_sub = 6,
    /// Modular wrapping multiplication (`*%`).
    wrap_mul = 7,
    /// Saturating addition (`+|`).
    sat_add = 8,
    /// Saturating subtraction (`-|`).
    sat_sub = 9,
    /// Saturating multiplication (`*|`).
    sat_mul = 10,
    /// Bitwise AND (`&`).
    bit_and = 11,
    /// Bitwise inclusive OR (`|`).
    bit_or = 12,
    /// Bitwise exclusive OR (`^`).
    bit_xor = 13,
    /// Bitwise shift left (`<<`).
    shl = 14,
    /// Bitwise shift right (`>>`).
    shr = 15,
    /// Equality comparison (`==`).
    eq = 16,
    /// Inequality comparison (`!=`).
    ne = 17,
    /// Less-than comparison (`<`).
    lt = 18,
    /// Less-than-or-equal comparison (`<=`).
    le = 19,
    /// Greater-than comparison (`>`).
    gt = 20,
    /// Greater-than-or-equal comparison (`>=`).
    ge = 21,
    /// Short-circuiting logical conjunction (`and` / `&&`).
    logical_and = 22,
    /// Short-circuiting logical disjunction (`or` / `||`).
    logical_or = 23,
};

/// Canonical type conversion kinds for `hir_cast`.
pub const HirCastKind = enum(u8) {
    /// Integer width or signedness cast (`i32 as i64`, `u32 as u8`).
    int_to_int = 0,
    /// Integer to IEEE-754 float conversion (`i32 as f64`).
    int_to_float = 1,
    /// IEEE-754 float to integer truncation (`f64 as i32`).
    float_to_int = 2,
    /// Float precision widening or narrowing (`f32 as f64`).
    float_to_float = 3,
    /// Reference-to-raw-pointer or raw-pointer cast (`&x as *T`).
    ptr_cast = 4,
    /// Unwrapping a `distinct` newtype to its underlying representation.
    distinct_unwrap = 5,
    /// Wrapping an underlying value into a `distinct` newtype.
    distinct_wrap = 6,
    /// Mutability relaxation coercion (`&mut T -> &T`).
    ref_coerce = 7,
    /// Fixed-size array or `&[T; N]` to fat slice `[T]` coercion.
    array_to_slice = 8,
    /// Identity or range-refinement widening (`T is low..=high -> T`).
    noop = 9,
};

/// Aggregate construction flavor encoded in the low byte of `hir_construct.lhs`.
pub const HirConstructKind = enum(u8) {
    /// Nominal `struct` or `union` field initialization (`extra = {elem_len, field_0_hir, …}` in canonical field order).
    struct_init = 0,
    /// Tuple construction (`extra = {elem_len, elem_0_hir, …}`).
    tuple_init = 1,
    /// Explicit array element list (`extra = {elem_len, elem_0_hir, …}`).
    array_elements = 2,
    /// Repeated array literal `[val; count]` (`extra = {count, val_hir}`).
    array_repeat = 3,
    /// Nominal `enum` variant (`lhs >> 8 = tag_ordinal`, `extra = {payload_len, payload_hirs…}`).
    enum_variant = 4,
    /// `Option[T]::None` (`tag = 0`, no payload).
    optional_none = 5,
    /// `Option[T]::Some(val)` (`tag = 1`, `extra = {1, val_hir}`).
    optional_some = 6,
    /// `Result[T, E]::Ok(val)` (`tag = 0`, `extra = {1, val_hir}`).
    result_ok = 7,
    /// `Result[T, E]::Err(err)` (`tag = 1`, `extra = {1, err_hir}`).
    result_err = 8,
    /// Zero-initialized backing integer for `bit_field` default construction.
    bitfield_zero = 9,
    /// Runtime string interpolation sequence (`extra = {part_len, part_0_hir, …}`).
    str_interp = 10,
};

// ---------------- Locals, Constants & Patterns ----------------

/// Metadata for a function parameter, user local binding, or desugaring temporary in `HirStore.locals`.
pub const HirLocalDecl = struct {
    /// Interned identifier (`SymbolId.empty` for anonymous temporaries).
    name: SymbolId = .empty,
    /// Resolved concrete `TypeId` of this slot.
    type_id: TypeId,
    /// Source span of the binding site.
    decl_span: Span,
    /// Parameter passing convention (`.let_mode` for standard locals).
    mode: ParamMode = .let_mode,
    /// `true` if declared with `var` or `mut`.
    is_mut: bool = false,
    /// `true` if this slot is a formal function/closure parameter.
    is_param: bool = false,
    /// `true` if synthesized by `HirLowerer` desugaring.
    is_temp: bool = false,
    /// `true` if bound inside a `comptime` context.
    is_comptime: bool = false,
    /// Originating `SymbolIndex` in `SymbolTable` (`.none` for synthetic temporaries).
    symbol_index: SymbolIndex = .none,
};

/// Metadata header for a lowered function, method, derived trait method, or closure in `HirStore.functions`.
pub const HirFnMeta = struct {
    /// Owning `DefId` (`.NONE` for closures and inline derived methods without dedicated top-level `DefId`).
    def_id: DefId = .NONE,
    /// Resolved `SymbolIndex` in `SymbolTable`.
    symbol_index: SymbolIndex = .none,
    /// Interned function or method name.
    name: SymbolId = .empty,
    /// Function signature `TypeId` (`.fn_ty` or `.closure_ty`).
    fn_ty: TypeId,
    /// Resolved return `TypeId` (or yielded element `TypeId` for `subscript`).
    ret_ty: TypeId,
    /// Starting index in `HirStore.locals` for this function's return slot (`param_local_start` = return slot, `+1..` = params).
    return_local_id: u32,
    /// Starting index in `HirStore.locals` of formal parameters (`return_local_id + 1`).
    param_local_start: u32,
    /// Number of formal parameters.
    param_len: u32,
    /// Total number of locals (`1 + param_len + body_locals`) owned by this function in `HirStore.locals`.
    total_local_len: u32 = 0,
    /// Root `hir_block` node of the lowered body (`.none` for `extern` prototypes).
    body_hir: HirIndex = .none,
    /// `true` if declared with `subscript` (`yield` projection).
    is_subscript: bool = false,
    /// `true` if annotated or inferred as `contextless` / `@noalloc`.
    is_contextless: bool = false,
    /// `true` if declared `comptime fn`.
    is_comptime: bool = false,
    /// `true` if synthesized for `@derive(Eq, Hash, Debug, Clone)`.
    is_derived: bool = false,
    /// `true` if this closure carries an explicit `@local` attribute (`CRIT-05`).
    is_local_closure: bool = false,
    /// Capture local pairs `(outer_local_id, inner_local_id)` range in `HirStore.extra_data` for closures.
    capture_extra_start: u32 = 0,
    /// Number of captured bindings for closures (`0` for non-capturing functions).
    capture_len: u32 = 0,
};

/// Compile-time constant value interned in `HirStore.const_pool` (`hir_const_val`) and returned by `ComptimeEvalHook`.
pub const ComptimeValue = union(enum) {
    /// Unit value `()`.
    unit_val,
    /// Boolean constant (`true` or `false`).
    bool_val: bool,
    /// Signed/unsigned 128-bit integer constant.
    int_val: i128,
    /// IEEE-754 64-bit floating-point constant.
    float_val: f64,
    /// Unicode scalar value (`char`).
    char_val: u21,
    /// Interned UTF-8 string slice (`str`).
    str_val: SymbolId,
    /// Interned embedded byte buffer (`&[u8]`).
    bytes_val: SymbolId,
    /// Tuple, struct, or fixed-array constant (`elem_start..elem_start + elem_len` in `HirStore.const_elements`).
    aggregate: struct {
        /// Concrete `TypeId` of the aggregate.
        type_id: TypeId,
        /// Starting index into `HirStore.const_elements`.
        elem_start: u32,
        /// Number of element constants.
        elem_len: u32,
    },
    /// Enum, `Option[T]`, or `Result[T, E]` constant (`payload_const_idx = maxInt(u32)` if unit payload).
    variant: struct {
        /// Concrete `TypeId` of the sum type.
        type_id: TypeId,
        /// Zero-based variant discriminant ordinal.
        tag_ordinal: u32,
        /// Index in `HirStore.const_pool` of payload, or `std.math.maxInt(u32)` if payload-free.
        payload_const_idx: u32,
    },
    /// Compile-time reflection `TypeInfo` mirror for `@type_info[T]()`.
    type_info_mirror: struct {
        /// Reflected target `TypeId`.
        reflected_ty: TypeId,
        /// Byte size under `TargetLayout`.
        size_bytes: u64,
        /// Byte alignment under `TargetLayout`.
        align_bytes: u32,
        /// Interned type name string.
        type_name_id: SymbolId,
        /// Owning nominal `DefId` (`MetaId`).
        owner_def_id: DefId,
    },
    /// Compile-time reflection `FieldInfo` mirror yielded when iterating `@type_info[T]().fields`.
    field_info_mirror: struct {
        /// Enclosing nominal `TypeId`.
        owner_ty: TypeId,
        /// Enclosing nominal `DefId`.
        owner_def_id: DefId,
        /// Zero-based field declaration ordinal.
        field_ordinal: u32,
        /// Interned field name.
        field_name: SymbolId,
        /// Concrete field `TypeId`.
        field_ty: TypeId,
        /// Byte offset of this field in AoS layout.
        byte_offset: u64,
    },
    /// Compile-time reflection `VariantInfo` mirror yielded when iterating `@type_info[T]().variants`.
    variant_info_mirror: struct {
        /// Enclosing `enum` `TypeId`.
        owner_ty: TypeId,
        /// Enclosing `enum` `DefId`.
        owner_def_id: DefId,
        /// Zero-based variant discriminant ordinal.
        variant_ordinal: u32,
        /// Interned variant name.
        variant_name: SymbolId,
        /// Variant payload `TypeId` (`.unit_ty` if unit variant).
        payload_ty: TypeId,
    },
};

/// Canonical lowered pattern representation stored in `HirStore.patterns` (`DR-13` §3.4).
pub const HirPat = struct {
    /// Matched scrutinee `TypeId`.
    type_id: TypeId,
    /// Anchor token for diagnostics and span lookup.
    origin_token: TokenIndex,
    /// Structural pattern payload.
    kind: Kind,

    /// Tagged union of canonical `HIR` pattern constructors.
    pub const Kind = union(enum) {
        /// Irrefutable wildcard `_`.
        wildcard,
        /// Local variable capture (`x`, `mut x`, `ref x`).
        bind: struct {
            /// Target `LocalId` in `HirStore.locals`.
            local_id: u32,
            /// `true` if mutable binding.
            is_mut: bool,
            /// `true` if borrowed by reference (`ref` / `&`).
            is_ref: bool,
        },
        /// Boolean constant pattern (`false` or `true`).
        lit_bool: bool,
        /// Inclusive integer or `char` range `[min_val ..= max_val]` (`min_val == max_val` for singletons).
        lit_int_range: struct {
            /// Inclusive lower bound.
            min_val: i128,
            /// Inclusive upper bound.
            max_val: i128,
        },
        /// Floating-point literal pattern.
        lit_float: f64,
        /// UTF-8 string literal equality pattern.
        lit_str: SymbolId,
        /// Tuple destructuring (`extra_data[sub_start .. sub_start + sub_len]` holds child `HirPat` indices).
        tuple: struct {
            /// Start offset in `HirStore.extra_data`.
            sub_start: u32,
            /// Number of tuple element sub-patterns.
            sub_len: u32,
        },
        /// Struct field destructuring (`extra_data` stores `field_len` pairs `(field_ordinal, sub_pat_idx)`).
        struct_pat: struct {
            /// Start offset in `HirStore.extra_data`.
            field_start: u32,
            /// Number of destructured struct fields.
            field_len: u32,
        },
        /// `enum`, `Option[T]`, or `Result[T, E]` variant pattern.
        variant: struct {
            /// Zero-based discriminant ordinal (`None=0, Some=1`; `Ok=0, Err=1`; or `enum` ordinal).
            tag_ordinal: u32,
            /// Variant payload `TypeId` (`.unit_ty` if unit variant).
            payload_ty: TypeId,
            /// Start offset of payload sub-patterns in `HirStore.extra_data`.
            sub_start: u32,
            /// Number of payload sub-patterns (`0`, `1`, or tuple arity).
            sub_len: u32,
        },
        /// Disjunctive `P1 | P2` pattern sharing the same arm continuation.
        or_pat: struct {
            /// Left alternative `HirPat` index.
            lhs_pat: u32,
            /// Right alternative `HirPat` index.
            rhs_pat: u32,
        },
    };
};

/// Single canonical `match` arm pairing a `HirPat`, optional boolean guard, and arm body (`DR-13` §3.4).
pub const HirMatchArm = struct {
    /// Root `HirPat` index in `HirStore.patterns`.
    pat_idx: u32,
    /// Optional guard expression (`HirIndex.none` when unguarded).
    guard_hir: HirIndex = .none,
    /// Arm body expression `HirIndex`.
    body_hir: HirIndex,
    /// Anchor token of the arm.
    origin_token: TokenIndex,
};

// ------------------ Comptime Evaluation Hook ------------------

/// Pluggable callback interface allowing Wave 2C's `MirVm` and `CompilerDb` to evaluate Tier-2 `comptime`
/// function calls and cross-file `const` items during `AST -> HIR` unrolling without circular `@import`s.
pub const ComptimeEvalHook = struct {
    /// Optional strongly typed `CompilerDb` pointer for cross-module `DefId` queries (`null` in standalone mode).
    compiler_db: ?*query_db.CompilerDb = null,
    /// Optional caller-assigned session identifier (`0` if unused).
    session_id: u32 = 0,
    /// Optional hook invoked to evaluate arbitrary `HIR` subtrees (e.g., `comptime fn` calls via `MirVm`).
    eval_hir_fn: ?*const fn (
        compiler_db: ?*query_db.CompilerDb,
        session_id: u32,
        store: *const HirStore,
        hir_id: HirIndex,
        expected_ty: TypeId,
        sink: ?*DiagnosticSink,
    ) anyerror!?ComptimeValue = null,
    /// Optional hook invoked to resolve external `DefId` constants.
    eval_const_def_fn: ?*const fn (
        compiler_db: ?*query_db.CompilerDb,
        session_id: u32,
        def_id: DefId,
        expected_ty: TypeId,
        sink: ?*DiagnosticSink,
    ) anyerror!?ComptimeValue = null,
};

// -------------------- SoA HIR Arena Store ---------------------

/// Per-module or per-`DefId` Structure-of-Arrays `HIR` arena (`DR-13` §2.1).
pub const HirStore = struct {
    /// Backing allocator for growable SoA columns and side tables.
    allocator: std.mem.Allocator,
    /// Owning source `FileId`.
    file_id: FileId,
    /// Target ABI layout used for `@size_of` / `@align_of` / `@type_info` folding.
    target_layout: TargetLayout = TargetLayout.NATIVE_64,
    /// Primary 18-byte-per-node SoA column store.
    nodes: std.MultiArrayList(HirNode) = .empty,
    /// Parallel `NodeIndex` origin side array for exact multi-token `getSpan` reconstruction.
    origin_ast: std.ArrayListUnmanaged(NodeIndex) = .empty,
    /// Flat 32-bit index buffer for variable-length child lists, call args, and construct payloads.
    extra_data: std.ArrayListUnmanaged(u32) = .empty,
    /// Lowered pattern arena indexed by `u32`.
    patterns: std.ArrayListUnmanaged(HirPat) = .empty,
    /// Lowered `match` arm table indexed by `hir_match`.
    match_arms: std.ArrayListUnmanaged(HirMatchArm) = .empty,
    /// Local variable and parameter declaration table indexed by `LocalId` (`u32`).
    locals: std.ArrayListUnmanaged(HirLocalDecl) = .empty,
    /// Lowered function, derived method, and closure headers.
    functions: std.ArrayListUnmanaged(HirFnMeta) = .empty,
    /// Interned compile-time constant pool indexed by `hir_const_val.lhs`.
    const_pool: std.ArrayListUnmanaged(ComptimeValue) = .empty,
    /// Flat constant-pool child indices for aggregate `ComptimeValue`s.
    const_elements: std.ArrayListUnmanaged(u32) = .empty,
    /// Root `hir_module` or single-item `HirIndex` (`.none` when empty).
    root_hir: HirIndex = .none,
    /// `true` if `MAX_HIR_NODES` or `MAX_HIR_LOWER_DEPTH` was exceeded (`E0508`).
    has_overflowed_limits: bool = false,

    /// Initializes an empty `HirStore` bound to `allocator` and `file_id`.
    pub fn init(allocator: std.mem.Allocator, file_id: FileId) HirStore {
        return .{
            .allocator = allocator,
            .file_id = file_id,
        };
    }

    /// Releases all SoA columns and auxiliary tables owned by `self`.
    pub fn deinit(self: *HirStore) void {
        self.nodes.deinit(self.allocator);
        self.origin_ast.deinit(self.allocator);
        self.extra_data.deinit(self.allocator);
        self.patterns.deinit(self.allocator);
        self.match_arms.deinit(self.allocator);
        self.locals.deinit(self.allocator);
        self.functions.deinit(self.allocator);
        self.const_pool.deinit(self.allocator);
        self.const_elements.deinit(self.allocator);
        self.* = undefined;
    }

    /// Returns the total number of `HirNode` records stored in `self`.
    pub inline fn countNodes(self: *const HirStore) usize {
        return self.nodes.len;
    }

    /// Fetches a `HirNode` by `hir_id` in $O(1)$ time.
    pub inline fn getNode(self: *const HirStore, hir_id: HirIndex) HirNode {
        return self.nodes.get(hir_id.asInt());
    }

    /// Appends a `HirNode` and its `ast_origin`, enforcing `MAX_HIR_NODES`.
    pub fn appendNode(self: *HirStore, node: HirNode, ast_origin: NodeIndex) !HirIndex {
        if (self.nodes.len >= MAX_HIR_NODES) {
            self.has_overflowed_limits = true;
            return error.HirLimitExceeded;
        }
        const idx: u32 = @intCast(self.nodes.len);
        try self.nodes.append(self.allocator, node);
        try self.origin_ast.append(self.allocator, ast_origin);
        return HirIndex.fromInt(idx);
    }

    /// Appends a slice of `u32` words to `self.extra_data` and returns the starting offset.
    pub fn appendExtraSlice(self: *HirStore, values: []const u32) !u32 {
        const start_idx: u32 = @intCast(self.extra_data.items.len);
        try self.extra_data.appendSlice(self.allocator, values);
        return start_idx;
    }

    /// Appends a length-prefixed slice (`[len, values…]`) to `self.extra_data` and returns the offset of `len`.
    pub fn appendLenPrefixedExtra(self: *HirStore, values: []const u32) !u32 {
        const start_idx: u32 = @intCast(self.extra_data.items.len);
        try self.extra_data.ensureUnusedCapacity(self.allocator, values.len + 1);
        self.extra_data.appendAssumeCapacity(@intCast(values.len));
        self.extra_data.appendSliceAssumeCapacity(values);
        return start_idx;
    }

    /// Reads a length-prefixed slice previously written via `appendLenPrefixedExtra`.
    pub fn getLenPrefixedExtra(self: *const HirStore, start_offset: u32) []const u32 {
        if (start_offset >= self.extra_data.items.len) return &.{};
        const slice_len: usize = self.extra_data.items[start_offset];
        const body_start: usize = @as(usize, start_offset) + 1;
        const body_end: usize = @min(body_start + slice_len, self.extra_data.items.len);
        return self.extra_data.items[body_start..body_end];
    }

    /// Appends a `ComptimeValue` to `self.const_pool` and returns its `u32` pool index.
    pub fn appendConst(self: *HirStore, val: ComptimeValue) !u32 {
        const idx: u32 = @intCast(self.const_pool.items.len);
        try self.const_pool.append(self.allocator, val);
        return idx;
    }

    /// Appends a `HirPat` to `self.patterns` and returns its `u32` pattern index.
    pub fn appendPat(self: *HirStore, pat: HirPat) !u32 {
        const idx: u32 = @intCast(self.patterns.items.len);
        try self.patterns.append(self.allocator, pat);
        return idx;
    }

    /// Appends a `HirLocalDecl` to `self.locals` and returns its `u32` local slot ID.
    pub fn appendLocal(self: *HirStore, decl: HirLocalDecl) !u32 {
        const idx: u32 = @intCast(self.locals.items.len);
        try self.locals.append(self.allocator, decl);
        return idx;
    }

    /// Resolves the exact multi-token `Span` of `hir_id` via `origin_ast` (CST subtree) or `origin_token`.
    pub fn getSpan(
        self: *const HirStore,
        hir_id: HirIndex,
        ast_arena: *const AstArena,
        cst_arena: *const LosslessCstArena,
        tokens: *const TokenBuffer,
    ) Span {
        if (hir_id.isNone() or hir_id.asInt() >= self.nodes.len) {
            return Span.init(self.file_id, 0, 0);
        }
        const ast_id = self.origin_ast.items[hir_id.asInt()];
        if (!ast_id.isNone() and ast_id.asInt() < ast_arena.countNodes()) {
            const cst_id = ast_arena.getCstOrigin(ast_id);
            if (!cst_id.isNone() and cst_id.asInt() < cst_arena.countNodes()) {
                const start_idx: usize = cst_id.asInt();
                const cst_rec = cst_arena.getNode(cst_id);
                const end_idx: usize = @min(
                    start_idx + @max(@as(usize, cst_rec.subtree_size), 1),
                    cst_arena.countNodes(),
                );
                var first_tok: TokenIndex = .none;
                var last_tok: TokenIndex = .none;
                var cur = start_idx;
                while (cur < end_idx) : (cur += 1) {
                    const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                    if (sub.subtree_size <= 1 and !sub.flags.is_missing_or_injected and
                        !sub.token.isNone() and sub.token.asInt() < tokens.countTokens())
                    {
                        if (first_tok.isNone()) first_tok = sub.token;
                        last_tok = sub.token;
                    }
                }
                if (!first_tok.isNone() and !last_tok.isNone()) {
                    const start_span = tokens.getTokenSpan(self.file_id, first_tok);
                    const end_span = tokens.getTokenSpan(self.file_id, last_tok);
                    return Span.merge(start_span, end_span);
                }
            }
            const main_tok = ast_arena.getNode(ast_id).main_token;
            if (!main_tok.isNone() and main_tok.asInt() < tokens.countTokens()) {
                return tokens.getTokenSpan(self.file_id, main_tok);
            }
        }
        const tok_idx = self.nodes.items(.origin_token)[hir_id.asInt()];
        if (!tok_idx.isNone() and tok_idx.asInt() < tokens.countTokens()) {
            return tokens.getTokenSpan(self.file_id, tok_idx);
        }
        return Span.init(self.file_id, 0, 0);
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Hard upper bound on `HirNode` count per `HirStore` (`4,194,304` nodes -> `E0508`).
pub const MAX_HIR_NODES: u32 = 4_194_304;

/// Hard upper bound on recursive `AST -> HIR` lowering depth (`512` frames -> `E0508`).
pub const MAX_HIR_LOWER_DEPTH: u32 = 512;

/// Maximum unrolled iteration count for `comptime for` loops (`4,096` iterations -> `E0501`).
pub const MAX_UNROLL: u32 = 4096;

/// Distinguished field ordinal representing `.len` on slices, `#soa` slices, and `str`.
pub const FIELD_ORDINAL_LEN: u32 = 0xFFFF_FFFE;

/// Sentinel value indicating no `HirIndex` or optional child (`0xFFFF_FFFF`).
const NONE_U32: u32 = std.math.maxInt(u32);

/// FNV-1a 64-bit offset basis used by synthesized `@derive(Hash)` implementations.
const FNV1A_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;

/// FNV-1a 64-bit prime multiplier used by synthesized `@derive(Hash)` implementations.
const FNV1A_PRIME: u64 = 0x0000_0100_0000_01b3;

comptime {
    std.debug.assert(@sizeOf(HirFlags) == 1);
    std.debug.assert(
        @sizeOf(HirTag) + @sizeOf(HirFlags) + @sizeOf(TypeId) + @sizeOf(TokenIndex) + @sizeOf(HirNode.Data) == 18,
    );
    std.debug.assert(@sizeOf(HirNode) == 20);
    std.debug.assert(@sizeOf(BitSpec) == 4);
}

// -------------------------------------- INTERNALS --------------------------------------

// ----------------- AST-to-HIR Lowering Engine -----------------

/// Undo-log entry restoring an outer lexical `SymbolId -> LocalId` mapping on scope exit.
const ShadowLocalRestore = struct {
    /// Interned variable name that was bound or shadowed.
    name_id: u32,
    /// Previous `LocalId` mapped to `name_id` (`null` if unbound in outer scopes).
    prev_local_id: ?u32,
};

/// Undo-log entry restoring an outer `comptime` constant binding on scope or unroll exit.
const ShadowComptimeRestore = struct {
    /// Interned constant or induction variable name.
    name_id: u32,
    /// Previous `ComptimeValue` mapped to `name_id` (`null` if previously unbound).
    prev_val: ?ComptimeValue,
};

/// Unrolled loop control-flow state for `break` / `continue` inside `comptime for` (`CRIT-10`).
const ComptimeLoopState = enum(u8) {
    /// Normal sequential statement execution.
    normal,
    /// `continue` executed in the current unrolled iteration; skip remaining statements of iteration.
    continued,
    /// `break` executed in the current unrolled iteration; terminate unrolling loop.
    broken,
};

/// Virtual zero-temporary `soa_zip(s0, s1, …)` binding descriptor (`DR-13` §2.2 Rule 5).
const VirtualZipBinding = struct {
    /// Lowered sequence local IDs (`_seq_0 .. _seq_{count-1}`).
    seq_locals: []const u32 = &.{},
    /// Concrete sequence `TypeId`s.
    seq_types: []const TypeId = &.{},
    /// Optional named argument labels (`soa_zip(pos: xs, vel: ys)`).
    seq_labels: []const SymbolId = &.{},
    /// Loop index local ID (`_cur_idx`) holding the current element offset.
    idx_local: u32 = 0,
};

/// Undo-log entry restoring an outer virtual `soa_zip` binding on loop exit.
const ShadowZipRestore = struct {
    /// Interned loop variable name.
    name_id: u32,
    /// Previous `VirtualZipBinding` (`null` if none).
    prev_zip: ?VirtualZipBinding,
};

/// Stateful `AST -> HIR` desugaring, `@derive` synthesis, and `comptime` unrolling engine.
const HirLowerer = struct {
    /// Backing allocator for temporary scratch containers.
    allocator: std.mem.Allocator,
    /// Destination `HirStore` receiving lowered nodes, patterns, constants, and locals.
    store: *HirStore,
    /// Shared string interner.
    interner: *StringInterner,
    /// Canonical `InternPool` (`TypeArena`).
    pool: *InternPool,
    /// Resolved module and lexical `SymbolTable`.
    sym_table: *const SymbolTable,
    /// UTF-8 source buffer of `store.file_id`.
    source: []const u8,
    /// Lexical token buffer of `store.file_id`.
    tokens: *const TokenBuffer,
    /// Lossless CST arena of `store.file_id`.
    cst_arena: *const LosslessCstArena,
    /// Parsed AST arena of `store.file_id`.
    ast_arena: *const AstArena,
    /// Optional per-body or per-file semantic side tables from `TypeChecker`.
    side_tables: ?*const BodySemanticSideTables,
    /// Optional diagnostic sink for `E0501` / `E0508` / `E0510` lowering errors.
    diagnostic_sink: ?*DiagnosticSink,
    /// Pluggable Tier-2 `comptime` evaluation hook.
    eval_hook: ComptimeEvalHook,
    /// Precomputed $O(1)$ upper bounds for `ast_arena.extra_data` slices.
    node_extra_end: []u32,
    /// Precomputed $O(1)$ `CstNodeIndex -> NodeIndex` reverse lookup map.
    cst_to_ast: []NodeIndex,

    /// Current AST/HIR recursion depth (`<= MAX_HIR_LOWER_DEPTH`).
    recursion_depth: u32 = 0,
    /// Active lexical `ScopeId` for fallback symbol lookups.
    current_scope: ScopeId = .none,
    /// Enclosing function or closure return `TypeId`.
    current_fn_ret_ty: TypeId = .unit_ty,
    /// Enclosing `hir_loop` identifier (`null` outside loops).
    current_loop_id: ?u32 = null,
    /// Monotonic counter assigning unique `loop_id` handles within a function.
    next_loop_id: u32 = 0,
    /// `true` while lowering inside an `unsafe { … }` block.
    is_in_unsafe: bool = false,
    /// `true` if `E0508` has already been emitted for this `HirStore` (prevents diagnostic floods).
    has_emitted_limit_diag: bool = false,
    /// Active function boundary local floor for closure capture detection (`0` at module level).
    closure_outer_local_ceil: u32 = 0,
    /// Collected `(outer_local_id, inner_local_id)` pairs for the currently lowering closure.
    active_closure_captures: std.ArrayListUnmanaged(u32) = .empty,

    /// $O(1)$ map from `SymbolIndex` to `LocalId` in `store.locals`.
    symbol_to_local: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// $O(1)$ map from interned `SymbolId` to active innermost `LocalId`.
    active_name_to_local: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// Scoped undo log for `active_name_to_local`.
    local_shadow_log: std.ArrayListUnmanaged(ShadowLocalRestore) = .empty,
    /// $O(1)$ map from interned `SymbolId` to active `ComptimeValue` (`comptime for` / local `const`).
    active_comptime_vals: std.AutoHashMapUnmanaged(u32, ComptimeValue) = .empty,
    /// Scoped undo log for `active_comptime_vals`.
    comptime_shadow_log: std.ArrayListUnmanaged(ShadowComptimeRestore) = .empty,
    /// $O(1)$ map from interned `SymbolId` to active `VirtualZipBinding` (`soa_zip`).
    active_zip_bindings: std.AutoHashMapUnmanaged(u32, VirtualZipBinding) = .empty,
    /// Scoped undo log for `active_zip_bindings`.
    zip_shadow_log: std.ArrayListUnmanaged(ShadowZipRestore) = .empty,
    /// Active `SymbolIndex` recursion stack preventing infinite cycles when folding module `const` items (`E0509`).
    const_eval_stack: [64]SymbolIndex = @splat(.none),
    /// Current depth of `const_eval_stack`.
    const_eval_depth: usize = 0,
    /// Arena owning dynamic slices inside `VirtualZipBinding` descriptors.
    zip_arena: std.heap.ArenaAllocator,
    /// Floor index in `local_shadow_log` marking bindings introduced by the currently lowering pattern (`CRIT-09`).
    current_pat_shadow_floor: usize = 0,
    /// `true` when unrolling the body of a `comptime for` loop (`CRIT-10`).
    is_in_comptime_for: bool = false,
    /// Nesting depth of runtime conditional branches inside an active `comptime for` body (`CRIT-10`).
    comptime_runtime_cond_depth: u32 = 0,
    /// Pending `break` / `continue` control-flow state for the active `comptime for` iteration (`CRIT-10`).
    comptime_loop_state: ComptimeLoopState = .normal,
    /// Override outer token stamped onto sub-parsed `{expr}` string interpolation HIR nodes (`MAJ-08`).
    interp_override_token: TokenIndex = .none,
    /// Override outer span used while lowering sub-parsed `{expr}` string interpolation HIR nodes (`MAJ-08`).
    interp_override_span: ?Span = null,

    /// Initializes a `HirLowerer` with precomputed $O(1)$ AST/CST auxiliary index maps.
    fn init(
        allocator: std.mem.Allocator,
        store: *HirStore,
        interner: *StringInterner,
        pool: *InternPool,
        sym_table: *const SymbolTable,
        source: []const u8,
        tokens: *const TokenBuffer,
        cst_arena: *const LosslessCstArena,
        ast_arena: *const AstArena,
        side_tables: ?*const BodySemanticSideTables,
        diagnostic_sink: ?*DiagnosticSink,
        eval_hook: ComptimeEvalHook,
    ) !HirLowerer {
        const extra_ends = try syntax_arenas.computeAstNodeExtraEnds(allocator, ast_arena);
        errdefer if (extra_ends.len > 0) allocator.free(extra_ends);
        const cst_map = try syntax_arenas.computeCstToAstMap(allocator, cst_arena.countNodes(), ast_arena);
        return .{
            .allocator = allocator,
            .store = store,
            .interner = interner,
            .pool = pool,
            .sym_table = sym_table,
            .source = source,
            .tokens = tokens,
            .cst_arena = cst_arena,
            .ast_arena = ast_arena,
            .side_tables = side_tables,
            .diagnostic_sink = diagnostic_sink,
            .eval_hook = eval_hook,
            .node_extra_end = extra_ends,
            .cst_to_ast = cst_map,
            .zip_arena = std.heap.ArenaAllocator.init(allocator),
        };
    }

    /// Releases temporary lookup maps and precomputed AST/CST index slices owned by `self`.
    fn deinit(self: *HirLowerer) void {
        if (self.node_extra_end.len > 0) self.allocator.free(self.node_extra_end);
        if (self.cst_to_ast.len > 0) self.allocator.free(self.cst_to_ast);
        self.zip_arena.deinit();
        self.active_closure_captures.deinit(self.allocator);
        self.symbol_to_local.deinit(self.allocator);
        self.active_name_to_local.deinit(self.allocator);
        self.local_shadow_log.deinit(self.allocator);
        self.active_comptime_vals.deinit(self.allocator);
        self.comptime_shadow_log.deinit(self.allocator);
        self.active_zip_bindings.deinit(self.allocator);
        self.zip_shadow_log.deinit(self.allocator);
        self.* = undefined;
    }

    /// Binds `name_id` to `local_id` in `active_name_to_local`, recording the previous binding in `local_shadow_log`.
    fn pushLexicalLocal(self: *HirLowerer, name_id: SymbolId, local_id: u32) !void {
        if (name_id == .empty) return;
        const prev = self.active_name_to_local.get(name_id.asInt());
        try self.local_shadow_log.append(self.allocator, .{
            .name_id = name_id.asInt(),
            .prev_local_id = prev,
        });
        try self.active_name_to_local.put(self.allocator, name_id.asInt(), local_id);
    }

    /// Rewinds `active_name_to_local` back to `checkpoint` in LIFO order.
    fn popLexicalLocalsTo(self: *HirLowerer, checkpoint: usize) void {
        while (self.local_shadow_log.items.len > checkpoint) {
            const entry = self.local_shadow_log.pop().?;
            if (entry.prev_local_id) |prev_id| {
                self.active_name_to_local.putAssumeCapacity(entry.name_id, prev_id);
            } else {
                _ = self.active_name_to_local.remove(entry.name_id);
            }
        }
    }

    /// Binds `name_id` to `val` in `active_comptime_vals`, recording the previous binding in `comptime_shadow_log`.
    fn pushComptimeBinding(self: *HirLowerer, name_id: SymbolId, val: ComptimeValue) !void {
        if (name_id == .empty) return;
        const prev = self.active_comptime_vals.get(name_id.asInt());
        try self.comptime_shadow_log.append(self.allocator, .{
            .name_id = name_id.asInt(),
            .prev_val = prev,
        });
        try self.active_comptime_vals.put(self.allocator, name_id.asInt(), val);
    }

    /// Rewinds `active_comptime_vals` back to `checkpoint` in LIFO order.
    fn popComptimeBindingsTo(self: *HirLowerer, checkpoint: usize) void {
        while (self.comptime_shadow_log.items.len > checkpoint) {
            const entry = self.comptime_shadow_log.pop().?;
            if (entry.prev_val) |prev_val| {
                self.active_comptime_vals.putAssumeCapacity(entry.name_id, prev_val);
            } else {
                _ = self.active_comptime_vals.remove(entry.name_id);
            }
        }
    }

    /// Binds `name_id` to `zip_info` in `active_zip_bindings` with scoped undo logging.
    fn pushZipBinding(self: *HirLowerer, name_id: SymbolId, zip_info: VirtualZipBinding) !void {
        if (name_id == .empty) return;
        const prev = self.active_zip_bindings.get(name_id.asInt());
        try self.zip_shadow_log.append(self.allocator, .{
            .name_id = name_id.asInt(),
            .prev_zip = prev,
        });
        try self.active_zip_bindings.put(self.allocator, name_id.asInt(), zip_info);
    }

    /// Rewinds `active_zip_bindings` back to `checkpoint`.
    fn popZipBindingsTo(self: *HirLowerer, checkpoint: usize) void {
        while (self.zip_shadow_log.items.len > checkpoint) {
            const entry = self.zip_shadow_log.pop().?;
            if (entry.prev_zip) |prev_val| {
                self.active_zip_bindings.putAssumeCapacity(entry.name_id, prev_val);
            } else {
                _ = self.active_zip_bindings.remove(entry.name_id);
            }
        }
    }

    /// Returns the `extra_data` slice owned by `node_id` in $O(1)$ time.
    fn getAstExtraSlice(self: *const HirLowerer, node_id: NodeIndex, is_rhs: bool) []const u32 {
        if (node_id.isNone() or node_id.asInt() >= self.ast_arena.countNodes()) return &.{};
        const ast_node = self.ast_arena.getNode(node_id);
        const operand = if (is_rhs) ast_node.rhs else ast_node.lhs;
        if (operand.tag != .extra) return &.{};
        const start_idx: usize = operand.payload;
        const end_idx: usize = @min(
            @as(usize, self.node_extra_end[node_id.asInt()]),
            self.ast_arena.extra_data.items.len,
        );
        if (start_idx >= end_idx) return &.{};
        return self.ast_arena.extra_data.items[start_idx..end_idx];
    }

    /// Finds the first `NodeIndex` anchored inside CST range `[cst_start .. cst_end)`.
    fn findFirstAstInCstRange(self: *const HirLowerer, cst_start: usize, cst_end: usize) NodeIndex {
        const clamped_end = @min(cst_end, self.cst_to_ast.len);
        var cur = cst_start;
        while (cur < clamped_end) : (cur += 1) {
            const mapped = self.cst_to_ast[cur];
            if (!mapped.isNone()) return mapped;
        }
        return .none;
    }

    /// Materializes `.untyped_int_ty` to `.i32_ty` and `.untyped_float_ty` to `.f64_ty` so `HIR` is 100% concrete.
    inline fn concreteType(self: *const HirLowerer, raw_ty: TypeId) TypeId {
        _ = self;
        if (raw_ty == .untyped_int_ty) return .i32_ty;
        if (raw_ty == .untyped_float_ty) return .f64_ty;
        return raw_ty;
    }

    /// Unwraps `.ref_ty` / `.mut_ref_ty` auto-dereference layers up to 16 levels deep.
    fn unwrapRefType(self: *const HirLowerer, raw_ty: TypeId) TypeId {
        var cur = raw_ty;
        var i: u32 = 0;
        while (i < 16) : (i += 1) {
            const ty_node = self.pool.getNode(cur);
            if (ty_node.tag == .ref_ty or ty_node.tag == .mut_ref_ty) {
                cur = TypeId.fromInt(ty_node.lhs);
            } else {
                break;
            }
        }
        return cur;
    }

    /// Queries `side_tables` for the resolved `TypeId` of `node_id`, falling back to lexical/literal types.
    fn nodeType(self: *const HirLowerer, node_id: NodeIndex) TypeId {
        if (node_id.isNone() or node_id.asInt() >= self.ast_arena.countNodes()) return .err_ty;
        if (self.side_tables) |tables| {
            const recorded = tables.getNodeType(node_id);
            if (!recorded.isError()) return self.concreteType(recorded);
        }
        const ast_node = self.ast_arena.getNode(node_id);
        return switch (ast_node.tag) {
            .bool_lit => .bool_ty,
            .char_lit => .char_ty,
            .string_lit => .str_ty,
            .int_lit => .i32_ty,
            .float_lit => .f64_ty,
            .ident_expr, .self_val => blk: {
                const lexeme = if (ast_node.tag == .self_val)
                    "self"
                else
                    symbol_resolver.extractTokenSlice(self.source, self.tokens, ast_node.main_token);
                if (self.interner.lookup(lexeme)) |name_id| {
                    if (self.active_name_to_local.get(name_id.asInt())) |local_id| {
                        break :blk self.store.locals.items[local_id].type_id;
                    }
                    if (self.active_comptime_vals.get(name_id.asInt())) |ct_val| {
                        break :blk self.inferComptimeValType(ct_val);
                    }
                    switch (self.sym_table.lookupLexical(self.current_scope, name_id, NamespaceMask.ALL)) {
                        .found => |sym_idx| break :blk self.concreteType(self.sym_table.getSymbol(sym_idx).type_id),
                        else => {},
                    }
                }
                break :blk .err_ty;
            },
            .field_access => blk: {
                if (ast_node.lhs.tag == .node and ast_node.rhs.tag == .token) {
                    const recv_ty = self.unwrapRefType(self.nodeType(NodeIndex.fromInt(ast_node.lhs.payload)));
                    const f_name = symbol_resolver.extractTokenSlice(
                        self.source,
                        self.tokens,
                        TokenIndex.fromInt(ast_node.rhs.payload),
                    );
                    if (self.findStructFieldInfo(recv_ty, f_name)) |f_info| {
                        break :blk self.concreteType(f_info.field_ty);
                    }
                }
                break :blk .err_ty;
            },
            else => .err_ty,
        };
    }

    /// Queries `side_tables` for the resolved `SymbolIndex` of `node_id`, or returns `.none`.
    fn nodeSymbol(self: *const HirLowerer, node_id: NodeIndex) SymbolIndex {
        if (node_id.isNone()) return .none;
        if (self.side_tables) |tables| {
            return tables.getNodeSymbol(node_id);
        }
        return .none;
    }

    /// Computes a `Span` for `node_id` using `ast_arena` and `tokens`.
    fn astSpan(self: *const HirLowerer, node_id: NodeIndex) Span {
        if (self.interp_override_span) |ov_span| return ov_span;
        if (!node_id.isNone() and node_id.asInt() < self.ast_arena.countNodes()) {
            const main_tok = self.ast_arena.getNode(node_id).main_token;
            if (!main_tok.isNone() and main_tok.asInt() < self.tokens.countTokens()) {
                return self.tokens.getTokenSpan(self.store.file_id, main_tok);
            }
        }
        return Span.init(self.store.file_id, 0, 0);
    }

    /// Emits a single-label diagnostic to `self.diagnostic_sink` when present.
    fn emitDiagnostic(
        self: *HirLowerer,
        code: DiagnosticCode,
        span: Span,
        message: []const u8,
        label: []const u8,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const labels = [1]LabeledSpan{.{
            .span = span,
            .label = label,
            .style = .primary,
        }};
        try sink.emit(.{
            .code = code,
            .severity = code.defaultSeverity(),
            .primary_span = span,
            .message = message,
            .labels = &labels,
        });
    }

    /// Appends a `HirNode` to `self.store`, catching `HirLimitExceeded` and emitting `E0508` + poison recovery.
    fn emitNode(self: *HirLowerer, node: HirNode, ast_origin: NodeIndex) !HirIndex {
        var effective_node = node;
        var effective_origin = ast_origin;
        if (!self.interp_override_token.isNone()) {
            effective_node.origin_token = self.interp_override_token;
            effective_origin = .none;
        }
        return self.store.appendNode(effective_node, effective_origin) catch |err| switch (err) {
            error.HirLimitExceeded => {
                if (!self.has_emitted_limit_diag) {
                    self.has_emitted_limit_diag = true;
                    const err_span = if (self.interp_override_span) |ov_span|
                        ov_span
                    else if (!effective_origin.isNone())
                        self.astSpan(effective_origin)
                    else if (!effective_node.origin_token.isNone() and
                        effective_node.origin_token.asInt() < self.tokens.countTokens())
                        self.tokens.getTokenSpan(self.store.file_id, effective_node.origin_token)
                    else
                        Span.init(self.store.file_id, 0, 0);
                    try self.emitDiagnostic(
                        .e0508_comptime_resource_limit_exceeded,
                        err_span,
                        "HIR node count exceeded `MAX_HIR_NODES` (4,194,304)",
                        "resource cap `MAX_HIR_NODES` reached here",
                    );
                }
                if (self.store.nodes.len > 0) {
                    return HirIndex.fromInt(@intCast(self.store.nodes.len - 1));
                }
                return .none;
            },
            else => return err,
        };
    }

    /// Emits a synthetic `hir_error_hole` recovery node at `origin_tok`.
    fn emitErrorHole(self: *HirLowerer, origin_tok: TokenIndex, ast_origin: NodeIndex, ty: TypeId) !HirIndex {
        return self.emitNode(.{
            .tag = .hir_error_hole,
            .flags = .{ .category = .rvalue, .has_error = true, .is_synthetic = true },
            .type_id = if (ty.isError()) .unit_ty else self.concreteType(ty),
            .origin_token = origin_tok,
        }, ast_origin);
    }

    /// Emits a synthetic `()` unit constant node.
    fn emitUnitConst(self: *HirLowerer, origin_tok: TokenIndex, ast_origin: NodeIndex) !HirIndex {
        const const_idx = try self.store.appendConst(.unit_val);
        return self.emitNode(.{
            .tag = .hir_const_val,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = origin_tok,
            .data = .{ .lhs = const_idx, .rhs = 0 },
        }, ast_origin);
    }

    /// Emits a `hir_const_val` node wrapping `val` with concrete `ty`.
    fn emitConstVal(
        self: *HirLowerer,
        val: ComptimeValue,
        ty: TypeId,
        origin_tok: TokenIndex,
        ast_origin: NodeIndex,
        is_folded: bool,
    ) !HirIndex {
        const const_idx = try self.store.appendConst(val);
        return self.emitNode(.{
            .tag = .hir_const_val,
            .flags = .{
                .category = .rvalue,
                .is_synthetic = is_folded,
                .is_comptime_folded = is_folded,
            },
            .type_id = self.concreteType(ty),
            .origin_token = origin_tok,
            .data = .{ .lhs = const_idx, .rhs = 0 },
        }, ast_origin);
    }

    /// Allocates a synthetic temporary local in `store.locals` and returns its `u32` slot ID.
    fn allocTempLocal(self: *HirLowerer, ty: TypeId, origin_tok: TokenIndex, is_mut: bool) !u32 {
        const span = if (self.interp_override_span) |ov_span|
            ov_span
        else if (!origin_tok.isNone() and origin_tok.asInt() < self.tokens.countTokens())
            self.tokens.getTokenSpan(self.store.file_id, origin_tok)
        else
            Span.init(self.store.file_id, 0, 0);
        return self.store.appendLocal(.{
            .name = .empty,
            .type_id = self.concreteType(ty),
            .decl_span = span,
            .mode = .let_mode,
            .is_mut = is_mut,
            .is_param = false,
            .is_temp = true,
        });
    }

    /// Emits a `hir_var_ref` referencing `local_id`.
    fn emitVarRef(self: *HirLowerer, local_id: u32, origin_tok: TokenIndex, ast_origin: NodeIndex) !HirIndex {
        var resolved_local = local_id;
        if (self.closure_outer_local_ceil > 0 and local_id < self.closure_outer_local_ceil) {
            resolved_local = try self.captureOuterLocalInClosure(local_id);
        }
        const decl = self.store.locals.items[resolved_local];
        const cat: ValueCategory = if (decl.is_mut or decl.mode == .inout_mode or decl.mode == .set_mode)
            .place_mut
        else
            .place_imm;
        return self.emitNode(.{
            .tag = .hir_var_ref,
            .flags = .{ .category = cat, .is_synthetic = decl.is_temp },
            .type_id = decl.type_id,
            .origin_token = origin_tok,
            .data = .{ .lhs = resolved_local, .rhs = 0 },
        }, ast_origin);
    }

    /// Records or reuses an inner capture slot when a closure references an outer function's `local_id`.
    fn captureOuterLocalInClosure(self: *HirLowerer, outer_local_id: u32) !u32 {
        var i: usize = 0;
        while (i + 1 < self.active_closure_captures.items.len) : (i += 2) {
            if (self.active_closure_captures.items[i] == outer_local_id) {
                return self.active_closure_captures.items[i + 1];
            }
        }
        const outer_decl = self.store.locals.items[outer_local_id];
        const inner_local = try self.store.appendLocal(.{
            .name = outer_decl.name,
            .type_id = outer_decl.type_id,
            .decl_span = outer_decl.decl_span,
            .mode = .let_mode,
            .is_mut = outer_decl.is_mut,
            .is_param = true,
            .is_temp = false,
        });
        try self.active_closure_captures.append(self.allocator, outer_local_id);
        try self.active_closure_captures.append(self.allocator, inner_local);
        return inner_local;
    }

    // -------------- Module & Top-Level Item Lowering --------------

    /// Lowers all top-level and inline-module declarations in `self.ast_arena` into `hir_module`.
    fn lowerModule(self: *HirLowerer) !HirIndex {
        const mod_scope = self.sym_table.file_module_scopes.get(self.store.file_id.asInt()) orelse
            self.sym_table.prelude_scope;
        self.current_scope = mod_scope;

        var lowered_items: std.ArrayListUnmanaged(u32) = .empty;
        defer lowered_items.deinit(self.allocator);

        if (self.ast_arena.countNodes() > 0) {
            const root_node = self.ast_arena.getNode(.root);
            if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
                const root_slice = self.ast_arena.getExtraSlice(
                    ExtraIndex.fromInt(root_node.lhs.payload),
                    root_node.rhs.payload,
                );
                try self.lowerItemSlice(mod_scope, root_slice, &lowered_items);
            }
        }

        const extra_start = try self.store.appendExtraSlice(lowered_items.items);
        const mod_hir = try self.emitNode(.{
            .tag = .hir_module,
            .flags = .{ .category = .rvalue },
            .type_id = .unit_ty,
            .origin_token = TokenIndex.fromInt(0),
            .data = .{
                .lhs = extra_start,
                .rhs = @intCast(lowered_items.items.len),
            },
        }, .root);
        self.store.root_hir = mod_hir;
        return mod_hir;
    }

    /// Lowers a single `DefId` item (and any `@derive` methods if `DefId` is a nominal type) in isolation.
    fn lowerSingleDef(self: *HirLowerer, def_id: DefId) !HirIndex {
        if (def_id.isNone()) return .none;
        const mod_scope = self.sym_table.file_module_scopes.get(self.store.file_id.asInt()) orelse
            self.sym_table.prelude_scope;
        self.current_scope = mod_scope;

        if (self.sym_table.def_to_symbol.get(def_id.asInt())) |sym_idx| {
            const sym = self.sym_table.getSymbol(sym_idx).*;
            self.current_scope = sym.scope_id;
            const lowered = try self.lowerSymbolItem(sym_idx);
            if ((sym.kind == .struct_sym or sym.kind == .enum_sym or
                sym.kind == .union_sym or sym.kind == .bit_field_sym) and
                !sym.target_scope.isNone() and sym.derive_mask.hasAny())
            {
                for (self.sym_table.getScopeMembers(sym.target_scope)) |member_idx| {
                    const member_sym = self.sym_table.getSymbol(member_idx).*;
                    if (member_sym.kind == .fn_sym and member_sym.flags.is_prototype_only and
                        !member_sym.flags.is_imported)
                    {
                        _ = try self.synthesizeDerivedMethodHir(sym_idx, member_idx);
                    }
                }
            }
            self.store.root_hir = lowered;
            return lowered;
        }

        if (self.ast_arena.countNodes() > 0) {
            const root_node = self.ast_arena.getNode(.root);
            if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
                const item_slice = self.ast_arena.getExtraSlice(
                    ExtraIndex.fromInt(root_node.lhs.payload),
                    root_node.rhs.payload,
                );
                var ordinal: u12 = 0;
                for (item_slice) |raw_idx| {
                    const item_id = NodeIndex.fromInt(raw_idx);
                    if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
                    if (self.ast_arena.getNode(item_id).tag == .item_hole) continue;
                    if (ordinal == def_id.itemIndex()) {
                        const item_tag = self.ast_arena.getNode(item_id).tag;
                        if (item_tag == .impl_decl) {
                            const impl_members = symbol_resolver.extractImplMemberItems(self.ast_arena, item_id);
                            var lowered_members: std.ArrayListUnmanaged(u32) = .empty;
                            defer lowered_members.deinit(self.allocator);

                            var mem_cursor: usize = 0;
                            var sym_raw: u32 = 0;
                            while (sym_raw < self.sym_table.symbols.items.len) : (sym_raw += 1) {
                                const cand_sym_idx = SymbolIndex.fromInt(sym_raw);
                                const cand_sym = self.sym_table.getSymbol(cand_sym_idx).*;
                                if (cand_sym.owner_def_id != def_id) continue;
                                if (cand_sym.kind != .fn_sym and cand_sym.kind != .const_sym) continue;

                                var matched_ast_override: ?NodeIndex = null;
                                while (mem_cursor < impl_members.len) {
                                    const mem_ast_idx = NodeIndex.fromInt(impl_members[mem_cursor]);
                                    mem_cursor += 1;
                                    if (mem_ast_idx.asInt() >= self.ast_arena.countNodes()) continue;
                                    const mem_ast = self.ast_arena.getNode(mem_ast_idx);
                                    const is_kind_match = (cand_sym.kind == .fn_sym and mem_ast.tag == .fn_decl) or
                                        (cand_sym.kind == .const_sym and mem_ast.tag == .const_decl);
                                    if (!is_kind_match) continue;
                                    matched_ast_override = mem_ast_idx;
                                    break;
                                }

                                self.current_scope = cand_sym.scope_id;
                                const m_hir = try self.lowerSymbolItemWithAstOverride(
                                    cand_sym_idx,
                                    matched_ast_override,
                                );
                                if (!m_hir.isNone()) {
                                    try lowered_members.append(self.allocator, m_hir.asInt());
                                }
                            }

                            const extra_start = try self.store.appendExtraSlice(lowered_members.items);
                            const impl_mod_hir = try self.emitNode(.{
                                .tag = .hir_module,
                                .flags = .{ .category = .rvalue },
                                .type_id = .unit_ty,
                                .origin_token = self.ast_arena.getNode(item_id).main_token,
                                .data = .{
                                    .lhs = extra_start,
                                    .rhs = @intCast(lowered_members.items.len),
                                },
                            }, item_id);
                            self.store.root_hir = impl_mod_hir;
                            return impl_mod_hir;
                        }

                        const lowered = try self.lowerBlockExpr(item_id, .unit_ty, false);
                        self.store.root_hir = lowered;
                        return lowered;
                    }
                    if (ordinal < std.math.maxInt(u12)) ordinal += 1;
                }
            }
        }
        return .none;
    }

    /// Lowers a slice of AST module items inside `scope_id`, appending resulting `HirIndex` handles to `out_items`.
    fn lowerItemSlice(
        self: *HirLowerer,
        scope_id: ScopeId,
        item_slice: []const u32,
        out_items: *std.ArrayListUnmanaged(u32),
    ) anyerror!void {
        const saved_scope = self.current_scope;
        self.current_scope = scope_id;
        defer self.current_scope = saved_scope;

        // [1] Lower symbol-backed items registered in `scope_id`:
        for (self.sym_table.getScopeMembers(scope_id)) |sym_idx| {
            const sym = self.sym_table.getSymbol(sym_idx).*;
            if (sym.flags.is_builtin or sym.flags.is_imported) continue;
            if (!sym.decl_span.file_id.isNone() and sym.decl_span.file_id != self.store.file_id) continue;

            switch (sym.kind) {
                .fn_sym, .const_sym => {
                    const item_hir = try self.lowerSymbolItem(sym_idx);
                    if (!item_hir.isNone()) try out_items.append(self.allocator, item_hir.asInt());
                },
                .struct_sym, .union_sym, .bit_field_sym, .enum_sym => {
                    const decl_hir = try self.lowerSymbolItem(sym_idx);
                    if (!decl_hir.isNone()) try out_items.append(self.allocator, decl_hir.asInt());
                    if (!sym.target_scope.isNone()) {
                        for (self.sym_table.getScopeMembers(sym.target_scope)) |member_idx| {
                            const member_sym = self.sym_table.getSymbol(member_idx).*;
                            if (member_sym.kind == .fn_sym and !member_sym.flags.is_imported) {
                                const method_hir = if (member_sym.flags.is_prototype_only and sym.derive_mask.hasAny())
                                    try self.synthesizeDerivedMethodHir(sym_idx, member_idx)
                                else
                                    try self.lowerSymbolItem(member_idx);
                                if (!method_hir.isNone()) try out_items.append(self.allocator, method_hir.asInt());
                            }
                        }
                    }
                },
                .module_sym => {
                    if (!sym.target_scope.isNone() and !sym.ast_node.isNone()) {
                        const sub_slice = self.getAstExtraSlice(sym.ast_node, true);
                        try self.lowerItemSlice(sym.target_scope, sub_slice, out_items);
                    }
                },
                else => {},
            }
        }

        // [2] Lower top-level `comptime { … }` blocks in `item_slice`:
        for (item_slice) |raw_item_id| {
            const item_id = NodeIndex.fromInt(raw_item_id);
            if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
            if (self.ast_arena.getNode(item_id).tag == .block) {
                const blk_hir = try self.lowerBlockExpr(item_id, .unit_ty, false);
                if (!blk_hir.isNone()) try out_items.append(self.allocator, blk_hir.asInt());
            }
        }
    }

    /// Lowers a single `SymbolIndex` (`fn_sym`, `const_sym`, `struct_sym`, or `enum_sym`) into `HIR`.
    fn lowerSymbolItem(self: *HirLowerer, sym_idx: SymbolIndex) anyerror!HirIndex {
        return self.lowerSymbolItemWithAstOverride(sym_idx, null);
    }

    /// Lowers `sym_idx` into `HIR`, optionally overriding `sym.ast_node` with `ast_override`.
    fn lowerSymbolItemWithAstOverride(
        self: *HirLowerer,
        sym_idx: SymbolIndex,
        ast_override: ?NodeIndex,
    ) anyerror!HirIndex {
        const sym = self.sym_table.getSymbol(sym_idx).*;
        const eff_ast = ast_override orelse sym.ast_node;
        switch (sym.kind) {
            .struct_sym, .union_sym, .bit_field_sym => {
                const tok = if (!eff_ast.isNone())
                    self.ast_arena.getNode(eff_ast).main_token
                else
                    TokenIndex.fromInt(0);
                return self.emitNode(.{
                    .tag = .hir_struct_decl,
                    .flags = .{ .category = .rvalue },
                    .type_id = sym.type_id,
                    .origin_token = tok,
                    .data = .{ .lhs = sym.def_id.asInt(), .rhs = sym_idx.asInt() },
                }, eff_ast);
            },
            .enum_sym => {
                const tok = if (!eff_ast.isNone())
                    self.ast_arena.getNode(eff_ast).main_token
                else
                    TokenIndex.fromInt(0);
                return self.emitNode(.{
                    .tag = .hir_enum_decl,
                    .flags = .{ .category = .rvalue },
                    .type_id = sym.type_id,
                    .origin_token = tok,
                    .data = .{ .lhs = sym.def_id.asInt(), .rhs = sym_idx.asInt() },
                }, eff_ast);
            },
            .const_sym => {
                if (eff_ast.isNone()) return .none;
                const const_ast = self.ast_arena.getNode(eff_ast);
                const init_hir = if (const_ast.rhs.tag == .node) blk: {
                    const init_ast_id = NodeIndex.fromInt(const_ast.rhs.payload);
                    if (try self.tryEvalAstComptime(init_ast_id, sym.type_id)) |folded_val| {
                        break :blk try self.emitConstVal(
                            folded_val,
                            sym.type_id,
                            const_ast.main_token,
                            init_ast_id,
                            true,
                        );
                    }
                    break :blk try self.lowerExpr(init_ast_id, sym.type_id);
                } else .none;
                return self.emitNode(.{
                    .tag = .hir_const_decl,
                    .flags = .{ .category = .rvalue },
                    .type_id = self.concreteType(sym.type_id),
                    .origin_token = const_ast.main_token,
                    .data = .{
                        .lhs = if (!sym.def_id.isNone()) sym.def_id.asInt() else sym_idx.asInt(),
                        .rhs = init_hir.asInt(),
                    },
                }, eff_ast);
            },
            .fn_sym => return self.lowerFnDeclSymbolWithAstOverride(sym_idx, ast_override),
            else => return .none,
        }
    }

    /// Lowers a function or `subscript` declaration (`fn_sym_idx`) and populates `HirStore.functions`.
    fn lowerFnDeclSymbolWithAstOverride(
        self: *HirLowerer,
        fn_sym_idx: SymbolIndex,
        ast_override: ?NodeIndex,
    ) anyerror!HirIndex {
        const fn_sym = self.sym_table.getSymbol(fn_sym_idx).*;
        const eff_ast = ast_override orelse fn_sym.ast_node;
        if (fn_sym.flags.is_prototype_only and !eff_ast.isNone()) {
            const proto_ast = self.ast_arena.getNode(eff_ast);
            if (proto_ast.rhs.tag != .node) return .none;
        }
        if (eff_ast.isNone()) return .none;

        const fn_ast = self.ast_arena.getNode(eff_ast);
        const sig_view = self.pool.getFnSignatureView(fn_sym.type_id) orelse return .none;

        const is_subscript = !fn_ast.main_token.isNone() and
            fn_ast.main_token.asInt() < self.tokens.countTokens() and
            std.mem.eql(
                u8,
                symbol_resolver.extractTokenSlice(self.source, self.tokens, fn_ast.main_token),
                "subscript",
            );
        const is_contextless = self.hasContextlessAttr(fn_sym_idx);

        const saved_scope = self.current_scope;
        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_loop_id = self.current_loop_id;
        const saved_closure_ceil = self.closure_outer_local_ceil;
        const local_checkpoint = self.local_shadow_log.items.len;
        const ct_checkpoint = self.comptime_shadow_log.items.len;
        defer {
            self.popComptimeBindingsTo(ct_checkpoint);
            self.popLexicalLocalsTo(local_checkpoint);
            self.current_scope = saved_scope;
            self.current_fn_ret_ty = saved_ret_ty;
            self.current_loop_id = saved_loop_id;
            self.closure_outer_local_ceil = saved_closure_ceil;
        }

        self.current_scope = if (!fn_sym.target_scope.isNone()) fn_sym.target_scope else fn_sym.scope_id;
        self.current_fn_ret_ty = sig_view.ret_ty;
        self.current_loop_id = null;
        self.closure_outer_local_ceil = 0;

        // [1] Reserve local slot `0` (relative to function start) for `_return_slot`:
        const return_local_id = try self.store.appendLocal(.{
            .name = .empty,
            .type_id = self.concreteType(sig_view.ret_ty),
            .decl_span = fn_sym.decl_span,
            .mode = .set_mode,
            .is_mut = true,
            .is_param = false,
            .is_temp = true,
        });
        const param_local_start: u32 = @intCast(self.store.locals.items.len);

        // [2] Register formal parameter slots in declaration order (`0 .. sig_view.paramCount()`):
        const param_syms = try self.allocator.alloc(SymbolIndex, sig_view.paramCount());
        defer if (param_syms.len > 0) self.allocator.free(param_syms);
        @memset(param_syms, .none);
        if (!fn_sym.target_scope.isNone()) {
            for (self.sym_table.getScopeMembers(fn_sym.target_scope)) |mem_idx| {
                const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind == .param_sym and mem_sym.member_ordinal < param_syms.len) {
                    param_syms[mem_sym.member_ordinal] = mem_idx;
                }
            }
        }

        var param_idx: usize = 0;
        while (param_idx < sig_view.paramCount()) : (param_idx += 1) {
            const p_ty = self.concreteType(sig_view.getParamType(param_idx));
            const p_mode = sig_view.getParamMode(param_idx);
            const p_sym_idx = if (param_idx < param_syms.len) param_syms[param_idx] else SymbolIndex.none;
            const p_name = if (!p_sym_idx.isNone()) self.sym_table.getSymbol(p_sym_idx).name else SymbolId.empty;
            const p_span = if (!p_sym_idx.isNone())
                self.sym_table.getSymbol(p_sym_idx).decl_span
            else
                fn_sym.decl_span;
            const p_is_mut = (!p_sym_idx.isNone() and self.sym_table.getSymbol(p_sym_idx).flags.is_mut) or
                p_mode == .inout_mode or p_mode == .set_mode;

            const slot_id = try self.store.appendLocal(.{
                .name = p_name,
                .type_id = p_ty,
                .decl_span = p_span,
                .mode = p_mode,
                .is_mut = p_is_mut,
                .is_param = true,
                .is_temp = false,
                .is_comptime = !p_sym_idx.isNone() and self.sym_table.getSymbol(p_sym_idx).flags.is_comptime,
                .symbol_index = p_sym_idx,
            });
            if (!p_sym_idx.isNone()) {
                try self.symbol_to_local.put(self.allocator, p_sym_idx.asInt(), slot_id);
            }
            try self.pushLexicalLocal(p_name, slot_id);
            _ = try self.emitNode(.{
                .tag = .hir_param_decl,
                .flags = .{ .category = if (p_is_mut) .place_mut else .place_imm },
                .type_id = p_ty,
                .origin_token = fn_ast.main_token,
                .data = .{ .lhs = slot_id, .rhs = @backingInt(p_mode) },
            }, .none);
        }

        const fn_meta_idx: u32 = @intCast(self.store.functions.items.len);
        try self.store.functions.append(self.allocator, .{
            .def_id = fn_sym.def_id,
            .symbol_index = fn_sym_idx,
            .name = fn_sym.name,
            .fn_ty = fn_sym.type_id,
            .ret_ty = self.concreteType(sig_view.ret_ty),
            .return_local_id = return_local_id,
            .param_local_start = param_local_start,
            .param_len = @intCast(sig_view.paramCount()),
            .is_subscript = is_subscript,
            .is_contextless = is_contextless,
            .is_comptime = fn_sym.flags.is_comptime,
            .is_derived = false,
        });

        // [3] Lower function body block if present:
        var body_hir: HirIndex = .none;
        if (fn_ast.rhs.tag == .node) {
            const body_ast_id = NodeIndex.fromInt(fn_ast.rhs.payload);
            body_hir = try self.lowerBlockExpr(body_ast_id, sig_view.ret_ty, !is_subscript);
        }

        const total_locals: u32 = @intCast(self.store.locals.items.len - return_local_id);
        self.store.functions.items[fn_meta_idx].body_hir = body_hir;
        self.store.functions.items[fn_meta_idx].total_local_len = total_locals;

        return self.emitNode(.{
            .tag = .hir_fn_decl,
            .flags = .{ .category = .rvalue },
            .type_id = fn_sym.type_id,
            .origin_token = fn_ast.main_token,
            .data = .{ .lhs = fn_meta_idx, .rhs = body_hir.asInt() },
        }, eff_ast);
    }

    /// Returns `true` if `cst_id` carries a direct leading `@<target_attr>` attribute.
    fn hasAttrNamedInCst(self: *const HirLowerer, cst_id: CstNodeIndex, target_attr: []const u8) bool {
        if (cst_id.isNone() or cst_id.asInt() >= self.cst_arena.countNodes()) return false;
        const start_idx: usize = cst_id.asInt();
        const rec = self.cst_arena.getNode(cst_id);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var cur = start_idx + 1;
        while (cur < end_idx) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.kind == .fn_introducer or sub.kind == .block) break;
            if (sub.kind == .attribute) {
                const attr_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                var leaf_cur = cur + 1;
                while (leaf_cur < attr_end) : (leaf_cur += 1) {
                    const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(leaf_cur)));
                    if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                        leaf.token.asInt() < self.tokens.countTokens())
                    {
                        const tk = self.tokens.getToken(leaf.token).kind;
                        if (tk == .at) continue;
                        if (symbol_resolver.isIdentifierToken(tk)) {
                            const lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, leaf.token);
                            if (std.mem.eql(u8, lex, target_attr)) return true;
                        }
                        break;
                    }
                }
                cur = attr_end;
                continue;
            }
            if (sub.subtree_size > 1) {
                cur += sub.subtree_size;
                continue;
            }
            if (!sub.token.isNone() and sub.token.asInt() < self.tokens.countTokens()) {
                const tk = self.tokens.getToken(sub.token).kind;
                if (tk == .pipe or tk == .pipepipe or tk == .eq or tk == .colon) break;
            }
            cur += 1;
        }
        return false;
    }

    /// Checks whether `fn_sym_idx` carries a `@noalloc` or `@contextless` attribute in CST.
    fn hasContextlessAttr(self: *const HirLowerer, fn_sym_idx: SymbolIndex) bool {
        const sym = self.sym_table.getSymbol(fn_sym_idx).*;
        return self.hasAttrNamedInCst(sym.cst_node, "noalloc") or
            self.hasAttrNamedInCst(sym.cst_node, "contextless");
    }

    // --------- Phase 3 Two-Phase `@derive` Body Synthesis ---------

    /// Synthesizes the structural `HIR` body for `@derive(Eq, Hash, Debug, Clone)` (`DR-05` Deliverable 1 §2.2).
    fn synthesizeDerivedMethodHir(
        self: *HirLowerer,
        nominal_sym_idx: SymbolIndex,
        method_sym_idx: SymbolIndex,
    ) !HirIndex {
        const nom_sym = self.sym_table.getSymbol(nominal_sym_idx).*;
        const method_sym = self.sym_table.getSymbol(method_sym_idx).*;
        const sig_view = self.pool.getFnSignatureView(method_sym.type_id) orelse return .none;
        const tok = if (!nom_sym.ast_node.isNone())
            self.ast_arena.getNode(nom_sym.ast_node).main_token
        else
            TokenIndex.fromInt(0);

        const local_checkpoint = self.local_shadow_log.items.len;
        defer self.popLexicalLocalsTo(local_checkpoint);

        const return_local_id = try self.store.appendLocal(.{
            .name = .empty,
            .type_id = self.concreteType(sig_view.ret_ty),
            .decl_span = nom_sym.decl_span,
            .mode = .set_mode,
            .is_mut = true,
            .is_param = false,
            .is_temp = true,
        });
        const param_local_start: u32 = @intCast(self.store.locals.items.len);

        const self_name = try self.interner.intern("self");
        const self_local = try self.store.appendLocal(.{
            .name = self_name,
            .type_id = sig_view.getParamType(0),
            .decl_span = nom_sym.decl_span,
            .mode = .let_mode,
            .is_mut = false,
            .is_param = true,
            .is_temp = false,
        });
        var other_local: u32 = NONE_U32;
        if (sig_view.paramCount() >= 2) {
            const other_name = try self.interner.intern("other");
            other_local = try self.store.appendLocal(.{
                .name = other_name,
                .type_id = sig_view.getParamType(1),
                .decl_span = nom_sym.decl_span,
                .mode = .let_mode,
                .is_mut = false,
                .is_param = true,
                .is_temp = false,
            });
        }

        const fn_meta_idx: u32 = @intCast(self.store.functions.items.len);
        try self.store.functions.append(self.allocator, .{
            .def_id = method_sym.def_id,
            .symbol_index = method_sym_idx,
            .name = method_sym.name,
            .fn_ty = method_sym.type_id,
            .ret_ty = self.concreteType(sig_view.ret_ty),
            .return_local_id = return_local_id,
            .param_local_start = param_local_start,
            .param_len = @intCast(sig_view.paramCount()),
            .is_subscript = false,
            .is_contextless = true,
            .is_comptime = false,
            .is_derived = true,
        });

        const m_name = method_sym.name_text;
        const body_hir = if (std.mem.eql(u8, m_name, "eq"))
            try self.synthDeriveEqBody(nom_sym, self_local, other_local, tok)
        else if (std.mem.eql(u8, m_name, "hash"))
            try self.synthDeriveHashBody(nom_sym, self_local, tok)
        else if (std.mem.eql(u8, m_name, "clone"))
            try self.synthDeriveCloneBody(nom_sym, self_local, tok)
        else
            try self.synthDeriveDebugBody(nom_sym, tok);

        self.store.functions.items[fn_meta_idx].body_hir = body_hir;
        self.store.functions.items[fn_meta_idx].total_local_len =
            @intCast(self.store.locals.items.len - return_local_id);

        return self.emitNode(.{
            .tag = .hir_fn_decl,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = method_sym.type_id,
            .origin_token = tok,
            .data = .{ .lhs = fn_meta_idx, .rhs = body_hir.asInt() },
        }, nom_sym.ast_node);
    }

    /// Synthesizes `fn eq(&self, other: &Self) -> bool` over struct fields or enum discriminants.
    fn synthDeriveEqBody(
        self: *HirLowerer,
        nom_sym: symbol_resolver.SymbolRecord,
        self_local: u32,
        other_local: u32,
        tok: TokenIndex,
    ) !HirIndex {
        var combined_cond: ?HirIndex = null;
        if (nom_sym.kind == .struct_sym and !nom_sym.target_scope.isNone()) {
            var field_ord: u32 = 0;
            for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .field_sym) continue;
                const self_ref = try self.emitVarRef(self_local, tok, .none);
                const self_deref = try self.emitSyntheticDeref(self_ref, nom_sym.type_id, tok);
                const lhs_proj = try self.emitNode(.{
                    .tag = .hir_field_proj,
                    .flags = .{ .category = .place_imm, .is_synthetic = true },
                    .type_id = mem_sym.type_id,
                    .origin_token = tok,
                    .data = .{ .lhs = self_deref.asInt(), .rhs = field_ord },
                }, .none);

                const other_ref = try self.emitVarRef(other_local, tok, .none);
                const other_deref = try self.emitSyntheticDeref(other_ref, nom_sym.type_id, tok);
                const rhs_proj = try self.emitNode(.{
                    .tag = .hir_field_proj,
                    .flags = .{ .category = .place_imm, .is_synthetic = true },
                    .type_id = mem_sym.type_id,
                    .origin_token = tok,
                    .data = .{ .lhs = other_deref.asInt(), .rhs = field_ord },
                }, .none);

                const field_eq = try self.emitDerivedMemberEq(lhs_proj, rhs_proj, mem_sym.type_id, tok);
                combined_cond = if (combined_cond) |prev_cond|
                    try self.emitSyntheticBinOp(.logical_and, prev_cond, field_eq, .bool_ty, tok)
                else
                    field_eq;
                field_ord += 1;
            }
        } else if (nom_sym.kind == .enum_sym and !nom_sym.target_scope.isNone()) {
            // Synthesize exhaustive nested `match *self` / `match *other` borrowing payloads in place:
            const self_deref = try self.emitSyntheticDeref(
                try self.emitVarRef(self_local, tok, .none),
                nom_sym.type_id,
                tok,
            );
            var outer_arms: std.ArrayListUnmanaged(HirMatchArm) = .empty;
            defer outer_arms.deinit(self.allocator);
            var var_ord: u32 = 0;
            for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .enum_variant_sym) continue;

                const is_copy_pay = self.pool.getFlags(mem_sym.type_id).is_copy;
                var lhs_sub_start: u32 = 0;
                var rhs_sub_start: u32 = 0;
                var sub_len: u32 = 0;
                var eq_body: HirIndex = .none;

                if (mem_sym.type_id == .unit_ty) {
                    eq_body = try self.emitConstVal(.{ .bool_val = true }, .bool_ty, tok, .none, true);
                } else {
                    const bind_slot_ty = if (is_copy_pay)
                        mem_sym.type_id
                    else
                        try self.pool.internRef(mem_sym.type_id, false);
                    const lhs_cap = try self.allocTempLocal(bind_slot_ty, tok, false);
                    const rhs_cap = try self.allocTempLocal(bind_slot_ty, tok, false);
                    const lhs_bind_pat = try self.store.appendPat(.{
                        .type_id = mem_sym.type_id,
                        .origin_token = tok,
                        .kind = .{ .bind = .{ .local_id = lhs_cap, .is_mut = false, .is_ref = !is_copy_pay } },
                    });
                    const rhs_bind_pat = try self.store.appendPat(.{
                        .type_id = mem_sym.type_id,
                        .origin_token = tok,
                        .kind = .{ .bind = .{ .local_id = rhs_cap, .is_mut = false, .is_ref = !is_copy_pay } },
                    });
                    lhs_sub_start = try self.store.appendExtraSlice(&[1]u32{lhs_bind_pat});
                    rhs_sub_start = try self.store.appendExtraSlice(&[1]u32{rhs_bind_pat});
                    sub_len = 1;
                    const lhs_val = if (is_copy_pay)
                        try self.emitVarRef(lhs_cap, tok, .none)
                    else
                        try self.emitSyntheticDeref(try self.emitVarRef(lhs_cap, tok, .none), mem_sym.type_id, tok);
                    const rhs_val = if (is_copy_pay)
                        try self.emitVarRef(rhs_cap, tok, .none)
                    else
                        try self.emitSyntheticDeref(try self.emitVarRef(rhs_cap, tok, .none), mem_sym.type_id, tok);
                    eq_body = try self.emitDerivedMemberEq(lhs_val, rhs_val, mem_sym.type_id, tok);
                }

                const lhs_var_pat = try self.store.appendPat(.{
                    .type_id = nom_sym.type_id,
                    .origin_token = tok,
                    .kind = .{
                        .variant = .{
                            .tag_ordinal = var_ord,
                            .payload_ty = mem_sym.type_id,
                            .sub_start = lhs_sub_start,
                            .sub_len = sub_len,
                        },
                    },
                });
                const rhs_var_pat = try self.store.appendPat(.{
                    .type_id = nom_sym.type_id,
                    .origin_token = tok,
                    .kind = .{
                        .variant = .{
                            .tag_ordinal = var_ord,
                            .payload_ty = mem_sym.type_id,
                            .sub_start = rhs_sub_start,
                            .sub_len = sub_len,
                        },
                    },
                });
                const rhs_wild_pat = try self.store.appendPat(.{
                    .type_id = nom_sym.type_id,
                    .origin_token = tok,
                    .kind = .wildcard,
                });
                const other_deref = try self.emitSyntheticDeref(
                    try self.emitVarRef(other_local, tok, .none),
                    nom_sym.type_id,
                    tok,
                );
                const inner_arm_start: u32 = @intCast(self.store.match_arms.items.len);
                try self.store.match_arms.append(self.allocator, .{
                    .pat_idx = rhs_var_pat,
                    .guard_hir = .none,
                    .body_hir = eq_body,
                    .origin_token = tok,
                });
                try self.store.match_arms.append(self.allocator, .{
                    .pat_idx = rhs_wild_pat,
                    .guard_hir = .none,
                    .body_hir = try self.emitConstVal(.{ .bool_val = false }, .bool_ty, tok, .none, true),
                    .origin_token = tok,
                });
                const inner_extra = try self.store.appendExtraSlice(&[2]u32{ inner_arm_start, 2 });
                const inner_match = try self.emitNode(.{
                    .tag = .hir_match,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .bool_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = other_deref.asInt(), .rhs = inner_extra },
                }, .none);
                try outer_arms.append(self.allocator, .{
                    .pat_idx = lhs_var_pat,
                    .guard_hir = .none,
                    .body_hir = inner_match,
                    .origin_token = tok,
                });
                var_ord += 1;
            }
            if (outer_arms.items.len > 0) {
                const arm_start: u32 = @intCast(self.store.match_arms.items.len);
                try self.store.match_arms.appendSlice(self.allocator, outer_arms.items);
                const match_extra = try self.store.appendExtraSlice(&[2]u32{
                    arm_start,
                    @intCast(outer_arms.items.len),
                });
                combined_cond = try self.emitNode(.{
                    .tag = .hir_match,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .bool_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = self_deref.asInt(), .rhs = match_extra },
                }, .none);
            }
        }

        const result_expr = combined_cond orelse
            try self.emitConstVal(.{ .bool_val = true }, .bool_ty, tok, .none, true);
        return self.wrapSyntheticReturnBlock(result_expr, .bool_ty, tok);
    }

    /// Emits equality between `lhs_hir` and `rhs_hir` for `@derive(Eq)` (primitive `==`, tuple, or nominal `.eq`).
    fn emitDerivedMemberEq(
        self: *HirLowerer,
        lhs_hir: HirIndex,
        rhs_hir: HirIndex,
        member_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!HirIndex {
        const base_ty = self.pool.unwrapUnderlyingType(member_ty);
        if (base_ty.isPrimitive()) {
            return self.emitSyntheticBinOp(.eq, lhs_hir, rhs_hir, .bool_ty, tok);
        }
        if (try self.lookupMethodOnType(member_ty, "eq")) |eq_sym_idx| {
            const ref_ty = try self.pool.internRef(member_ty, false);
            const lhs_addr = try self.emitSyntheticAddrOf(lhs_hir, ref_ty, false, tok);
            const rhs_addr = try self.emitSyntheticAddrOf(rhs_hir, ref_ty, false, tok);
            return self.emitDirectSymbolCall(eq_sym_idx, &[2]HirIndex{ lhs_addr, rhs_addr }, .bool_ty, tok);
        }
        const ty_node = self.pool.getNode(base_ty);
        if (ty_node.tag == .tuple_ty) {
            const elems = self.pool.getTupleElements(base_ty);
            var combined: ?HirIndex = null;
            for (elems, 0..) |raw_elem, elem_i| {
                const elem_ty = TypeId.fromInt(raw_elem);
                const lhs_elem = try self.emitNode(.{
                    .tag = .hir_field_proj,
                    .flags = .{ .category = .place_imm, .is_synthetic = true },
                    .type_id = self.concreteType(elem_ty),
                    .origin_token = tok,
                    .data = .{ .lhs = lhs_hir.asInt(), .rhs = @intCast(elem_i) },
                }, .none);
                const rhs_elem = try self.emitNode(.{
                    .tag = .hir_field_proj,
                    .flags = .{ .category = .place_imm, .is_synthetic = true },
                    .type_id = self.concreteType(elem_ty),
                    .origin_token = tok,
                    .data = .{ .lhs = rhs_hir.asInt(), .rhs = @intCast(elem_i) },
                }, .none);
                const sub_eq = try self.emitDerivedMemberEq(lhs_elem, rhs_elem, elem_ty, tok);
                combined = if (combined) |prev|
                    try self.emitSyntheticBinOp(.logical_and, prev, sub_eq, .bool_ty, tok)
                else
                    sub_eq;
            }
            return combined orelse self.emitConstVal(.{ .bool_val = true }, .bool_ty, tok, .none, true);
        }
        return self.emitSyntheticBinOp(.eq, lhs_hir, rhs_hir, .bool_ty, tok);
    }

    /// Appends one FNV-1a 64-bit mixing step `state = (state ^ val_u64) *% FNV1A_PRIME` to `out_stmts`.
    fn emitFnv1aMixStmt(
        self: *HirLowerer,
        state_local: u32,
        val_u64: HirIndex,
        tok: TokenIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
    ) !void {
        const xored = try self.emitSyntheticBinOp(
            .bit_xor,
            try self.emitVarRef(state_local, tok, .none),
            val_u64,
            .u64_ty,
            tok,
        );
        const prime_hir = try self.emitConstVal(
            .{ .int_val = @as(i128, FNV1A_PRIME) },
            .u64_ty,
            tok,
            .none,
            true,
        );
        const mixed = try self.emitSyntheticBinOp(.wrap_mul, xored, prime_hir, .u64_ty, tok);
        const assign_hir = try self.emitNode(.{
            .tag = .hir_assign,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{
                .lhs = (try self.emitVarRef(state_local, tok, .none)).asInt(),
                .rhs = mixed.asInt(),
            },
        }, .none);
        try out_stmts.append(self.allocator, assign_hir.asInt());
    }

    /// Computes a `u64` hash contribution for `val_hir` (`val_ty`) in `@derive(Hash)` (`MAJ-07`).
    fn emitDerivedValueHash(
        self: *HirLowerer,
        val_hir: HirIndex,
        val_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!HirIndex {
        if (try self.lookupMethodOnType(val_ty, "hash")) |h_sym| {
            const ref_ty = try self.pool.internRef(val_ty, false);
            const addr = try self.emitSyntheticAddrOf(val_hir, ref_ty, false, tok);
            return self.emitDirectSymbolCall(h_sym, &[1]HirIndex{addr}, .u64_ty, tok);
        }

        const base_ty = self.pool.unwrapUnderlyingType(val_ty);
        var unwrapped_val = val_hir;
        if (base_ty != val_ty) {
            unwrapped_val = try self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = base_ty,
                .origin_token = tok,
                .data = .{ .lhs = val_hir.asInt(), .rhs = @backingInt(HirCastKind.distinct_unwrap) },
            }, .none);
        }

        switch (base_ty) {
            .unit_ty => return self.emitConstVal(.{ .int_val = 0 }, .u64_ty, tok, .none, true),
            .u64_ty => return unwrapped_val,
            .f32_ty => {
                const bits_u32 = try self.emitNode(.{
                    .tag = .hir_cast,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .u32_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = unwrapped_val.asInt(), .rhs = @backingInt(HirCastKind.int_to_int) },
                }, .none);
                return self.emitNode(.{
                    .tag = .hir_cast,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .u64_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = bits_u32.asInt(), .rhs = @backingInt(HirCastKind.int_to_int) },
                }, .none);
            },
            .f64_ty => {
                return self.emitNode(.{
                    .tag = .hir_cast,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .u64_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = unwrapped_val.asInt(), .rhs = @backingInt(HirCastKind.int_to_int) },
                }, .none);
            },
            .str_ty => {
                const len_hir = try self.emitSequenceLen(unwrapped_val, .str_ty, tok);
                return self.emitNode(.{
                    .tag = .hir_cast,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .u64_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = len_hir.asInt(), .rhs = @backingInt(HirCastKind.int_to_int) },
                }, .none);
            },
            else => {
                if (base_ty == .bool_ty or base_ty == .char_ty or base_ty.isIntegerPrimitive()) {
                    return self.emitNode(.{
                        .tag = .hir_cast,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = .u64_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = unwrapped_val.asInt(), .rhs = @backingInt(HirCastKind.int_to_int) },
                    }, .none);
                }
            },
        }

        const ty_node = self.pool.getNode(base_ty);
        switch (ty_node.tag) {
            .tuple_ty => {
                const elems = self.pool.getTupleElements(base_ty);
                var sub_stmts: std.ArrayListUnmanaged(u32) = .empty;
                defer sub_stmts.deinit(self.allocator);
                const sub_state = try self.allocTempLocal(.u64_ty, tok, true);
                const init_h = try self.emitConstVal(.{ .int_val = @as(i128, FNV1A_OFFSET_BASIS) }, .u64_ty, tok, .none, true);
                try sub_stmts.append(self.allocator, (try self.emitLocalDeclNode(sub_state, init_h, tok)).asInt());
                for (elems, 0..) |raw_elem, elem_i| {
                    const elem_ty = TypeId.fromInt(raw_elem);
                    const proj = try self.emitNode(.{
                        .tag = .hir_field_proj,
                        .flags = .{ .category = .place_imm, .is_synthetic = true },
                        .type_id = self.concreteType(elem_ty),
                        .origin_token = tok,
                        .data = .{ .lhs = unwrapped_val.asInt(), .rhs = @intCast(elem_i) },
                    }, .none);
                    const elem_hash = try self.emitDerivedValueHash(proj, elem_ty, tok);
                    try self.emitFnv1aMixStmt(sub_state, elem_hash, tok, &sub_stmts);
                }
                const tail = try self.emitVarRef(sub_state, tok, .none);
                return self.emitSyntheticBlock(sub_stmts.items, tail, .u64_ty, tok);
            },
            .array_ty => {
                const elem_ty = TypeId.fromInt(ty_node.lhs);
                const arr_len = ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                var sub_stmts: std.ArrayListUnmanaged(u32) = .empty;
                defer sub_stmts.deinit(self.allocator);
                const sub_state = try self.allocTempLocal(.u64_ty, tok, true);
                const init_h = try self.emitConstVal(.{ .int_val = @as(i128, FNV1A_OFFSET_BASIS) }, .u64_ty, tok, .none, true);
                try sub_stmts.append(self.allocator, (try self.emitLocalDeclNode(sub_state, init_h, tok)).asInt());
                if (arr_len <= 64) {
                    for (0..arr_len) |elem_i| {
                        const idx_c = try self.emitConstVal(.{ .int_val = @intCast(elem_i) }, .usize_ty, tok, .none, true);
                        const proj = try self.emitNode(.{
                            .tag = .hir_index_proj,
                            .flags = .{ .category = .place_imm, .is_synthetic = true },
                            .type_id = self.concreteType(elem_ty),
                            .origin_token = tok,
                            .data = .{ .lhs = unwrapped_val.asInt(), .rhs = idx_c.asInt() },
                        }, .none);
                        const elem_hash = try self.emitDerivedValueHash(proj, elem_ty, tok);
                        try self.emitFnv1aMixStmt(sub_state, elem_hash, tok, &sub_stmts);
                    }
                }
                const tail = try self.emitVarRef(sub_state, tok, .none);
                return self.emitSyntheticBlock(sub_stmts.items, tail, .u64_ty, tok);
            },
            .optional_ty => {
                const inner_ty = self.concreteType(TypeId.fromInt(ty_node.lhs));
                const is_copy_inner = self.pool.getFlags(inner_ty).is_copy;
                const bind_slot_ty = if (is_copy_inner)
                    inner_ty
                else
                    try self.pool.internRef(inner_ty, false);
                const cap_local = try self.allocTempLocal(bind_slot_ty, tok, false);
                const cap_bind = try self.store.appendPat(.{
                    .type_id = inner_ty,
                    .origin_token = tok,
                    .kind = .{ .bind = .{ .local_id = cap_local, .is_mut = false, .is_ref = !is_copy_inner } },
                });
                const some_sub = try self.store.appendExtraSlice(&[1]u32{cap_bind});
                const some_pat = try self.store.appendPat(.{
                    .type_id = base_ty,
                    .origin_token = tok,
                    .kind = .{ .variant = .{ .tag_ordinal = 1, .payload_ty = inner_ty, .sub_start = some_sub, .sub_len = 1 } },
                });
                const none_pat = try self.store.appendPat(.{
                    .type_id = base_ty,
                    .origin_token = tok,
                    .kind = .{ .variant = .{ .tag_ordinal = 0, .payload_ty = .unit_ty, .sub_start = 0, .sub_len = 0 } },
                });
                const pay_expr = if (is_copy_inner)
                    try self.emitVarRef(cap_local, tok, .none)
                else
                    try self.emitSyntheticDeref(try self.emitVarRef(cap_local, tok, .none), inner_ty, tok);
                const inner_hash = try self.emitDerivedValueHash(pay_expr, inner_ty, tok);
                const one_u64 = try self.emitConstVal(.{ .int_val = 1 }, .u64_ty, tok, .none, true);
                const some_hash = try self.emitSyntheticBinOp(.wrap_add, inner_hash, one_u64, .u64_ty, tok);
                const none_hash = try self.emitConstVal(.{ .int_val = 0 }, .u64_ty, tok, .none, true);
                const arm_start: u32 = @intCast(self.store.match_arms.items.len);
                try self.store.match_arms.append(self.allocator, .{
                    .pat_idx = some_pat,
                    .guard_hir = .none,
                    .body_hir = some_hash,
                    .origin_token = tok,
                });
                try self.store.match_arms.append(self.allocator, .{
                    .pat_idx = none_pat,
                    .guard_hir = .none,
                    .body_hir = none_hash,
                    .origin_token = tok,
                });
                const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, 2 });
                return self.emitNode(.{
                    .tag = .hir_match,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .u64_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = unwrapped_val.asInt(), .rhs = match_extra },
                }, .none);
            },
            else => return self.emitConstVal(.{ .int_val = 0 }, .u64_ty, tok, .none, true),
        }
    }

    /// Synthesizes `fn hash(&self) -> u64` using FNV-1a 64-bit mixing across all fields/discriminants.
    fn synthDeriveHashBody(
        self: *HirLowerer,
        nom_sym: symbol_resolver.SymbolRecord,
        self_local: u32,
        tok: TokenIndex,
    ) !HirIndex {
        var stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer stmts.deinit(self.allocator);

        const state_local = try self.allocTempLocal(.u64_ty, tok, true);
        const init_basis = try self.emitConstVal(
            .{ .int_val = @as(i128, FNV1A_OFFSET_BASIS) },
            .u64_ty,
            tok,
            .none,
            true,
        );
        const decl_node = try self.emitNode(.{
            .tag = .hir_local_decl,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = state_local, .rhs = init_basis.asInt() },
        }, .none);
        try stmts.append(self.allocator, decl_node.asInt());

        if (nom_sym.kind == .struct_sym and !nom_sym.target_scope.isNone()) {
            var field_ord: u32 = 0;
            for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .field_sym) continue;
                const self_deref = try self.emitSyntheticDeref(
                    try self.emitVarRef(self_local, tok, .none),
                    nom_sym.type_id,
                    tok,
                );
                const field_proj = try self.emitNode(.{
                    .tag = .hir_field_proj,
                    .flags = .{ .category = .place_imm, .is_synthetic = true },
                    .type_id = mem_sym.type_id,
                    .origin_token = tok,
                    .data = .{ .lhs = self_deref.asInt(), .rhs = field_ord },
                }, .none);
                const member_hash = try self.emitDerivedValueHash(field_proj, mem_sym.type_id, tok);
                try self.emitFnv1aMixStmt(state_local, member_hash, tok, &stmts);
                field_ord += 1;
            }
        } else if (nom_sym.kind == .enum_sym and !nom_sym.target_scope.isNone()) {
            const self_deref = try self.emitSyntheticDeref(
                try self.emitVarRef(self_local, tok, .none),
                nom_sym.type_id,
                tok,
            );
            var temp_arms: std.ArrayListUnmanaged(HirMatchArm) = .empty;
            defer temp_arms.deinit(self.allocator);
            var var_ord: u32 = 0;
            for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .enum_variant_sym) continue;

                var arm_stmts: std.ArrayListUnmanaged(u32) = .empty;
                defer arm_stmts.deinit(self.allocator);
                const tag_const = try self.emitConstVal(.{ .int_val = @as(i128, var_ord) }, .u64_ty, tok, .none, true);
                try self.emitFnv1aMixStmt(state_local, tag_const, tok, &arm_stmts);

                var sub_start: u32 = 0;
                var sub_len: u32 = 0;
                if (mem_sym.type_id != .unit_ty) {
                    const is_copy_pay = self.pool.getFlags(mem_sym.type_id).is_copy;
                    const bind_slot_ty = if (is_copy_pay)
                        mem_sym.type_id
                    else
                        try self.pool.internRef(mem_sym.type_id, false);
                    const cap_local = try self.allocTempLocal(bind_slot_ty, tok, false);
                    const bind_pat = try self.store.appendPat(.{
                        .type_id = mem_sym.type_id,
                        .origin_token = tok,
                        .kind = .{ .bind = .{ .local_id = cap_local, .is_mut = false, .is_ref = !is_copy_pay } },
                    });
                    sub_start = try self.store.appendExtraSlice(&[1]u32{bind_pat});
                    sub_len = 1;
                    const pay_expr = if (is_copy_pay)
                        try self.emitVarRef(cap_local, tok, .none)
                    else
                        try self.emitSyntheticDeref(try self.emitVarRef(cap_local, tok, .none), mem_sym.type_id, tok);
                    const payload_hash = try self.emitDerivedValueHash(pay_expr, mem_sym.type_id, tok);
                    try self.emitFnv1aMixStmt(state_local, payload_hash, tok, &arm_stmts);
                }

                const var_pat = try self.store.appendPat(.{
                    .type_id = nom_sym.type_id,
                    .origin_token = tok,
                    .kind = .{
                        .variant = .{
                            .tag_ordinal = var_ord,
                            .payload_ty = mem_sym.type_id,
                            .sub_start = sub_start,
                            .sub_len = sub_len,
                        },
                    },
                });
                const arm_body = try self.emitSyntheticBlock(arm_stmts.items, .none, .unit_ty, tok);
                try temp_arms.append(self.allocator, .{
                    .pat_idx = var_pat,
                    .guard_hir = .none,
                    .body_hir = arm_body,
                    .origin_token = tok,
                });
                var_ord += 1;
            }
            if (temp_arms.items.len > 0) {
                const arm_start: u32 = @intCast(self.store.match_arms.items.len);
                try self.store.match_arms.appendSlice(self.allocator, temp_arms.items);
                const match_extra = try self.store.appendExtraSlice(&[2]u32{
                    arm_start,
                    @intCast(temp_arms.items.len),
                });
                const match_hir = try self.emitNode(.{
                    .tag = .hir_match,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = self_deref.asInt(), .rhs = match_extra },
                }, .none);
                try stmts.append(self.allocator, match_hir.asInt());
            }
        }

        const ret_hir = try self.emitNode(.{
            .tag = .hir_return,
            .flags = .{ .category = .diverging, .is_synthetic = true },
            .type_id = .never_ty,
            .origin_token = tok,
            .data = .{
                .lhs = (try self.emitVarRef(state_local, tok, .none)).asInt(),
                .rhs = @backingInt(ReturnErrorKind.normal),
            },
        }, .none);
        try stmts.append(self.allocator, ret_hir.asInt());

        const extra_idx = try self.store.appendLenPrefixedExtra(stmts.items);
        return self.emitNode(.{
            .tag = .hir_block,
            .flags = .{ .category = .diverging, .is_synthetic = true },
            .type_id = .u64_ty,
            .origin_token = tok,
            .data = .{ .lhs = extra_idx, .rhs = NONE_U32 },
        }, .none);
    }

    /// Clones a single member `place_hir` (`member_ty`) for `@derive(Clone)` (`MAJ-07`).
    fn emitDerivedMemberClone(
        self: *HirLowerer,
        place_hir: HirIndex,
        member_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!HirIndex {
        if (self.pool.getFlags(member_ty).is_copy) return place_hir;
        if (try self.lookupMethodOnType(member_ty, "clone")) |c_sym| {
            const ref_ty = try self.pool.internRef(member_ty, false);
            const addr = try self.emitSyntheticAddrOf(place_hir, ref_ty, false, tok);
            return self.emitDirectSymbolCall(c_sym, &[1]HirIndex{addr}, member_ty, tok);
        }
        const base_ty = self.pool.unwrapUnderlyingType(member_ty);
        if (self.pool.getTag(base_ty) == .tuple_ty) {
            const elems = self.pool.getTupleElements(base_ty);
            var cloned_elems: std.ArrayListUnmanaged(u32) = .empty;
            defer cloned_elems.deinit(self.allocator);
            for (elems, 0..) |raw_elem, elem_i| {
                const elem_ty = TypeId.fromInt(raw_elem);
                const proj = try self.emitNode(.{
                    .tag = .hir_field_proj,
                    .flags = .{ .category = .place_imm, .is_synthetic = true },
                    .type_id = self.concreteType(elem_ty),
                    .origin_token = tok,
                    .data = .{ .lhs = place_hir.asInt(), .rhs = @intCast(elem_i) },
                }, .none);
                const sub_clone = try self.emitDerivedMemberClone(proj, elem_ty, tok);
                try cloned_elems.append(self.allocator, sub_clone.asInt());
            }
            const extra_idx = try self.store.appendLenPrefixedExtra(cloned_elems.items);
            return self.emitNode(.{
                .tag = .hir_construct,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = base_ty,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(HirConstructKind.tuple_init), .rhs = extra_idx },
            }, .none);
        }
        return place_hir;
    }

    /// Synthesizes `fn clone(&self) -> Self` copying or `.clone()`-ing all struct fields / enum variants.
    fn synthDeriveCloneBody(
        self: *HirLowerer,
        nom_sym: symbol_resolver.SymbolRecord,
        self_local: u32,
        tok: TokenIndex,
    ) !HirIndex {
        if (nom_sym.kind == .struct_sym and !nom_sym.target_scope.isNone()) {
            var field_hirs: std.ArrayListUnmanaged(u32) = .empty;
            defer field_hirs.deinit(self.allocator);
            var field_ord: u32 = 0;
            for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .field_sym) continue;
                const self_deref = try self.emitSyntheticDeref(
                    try self.emitVarRef(self_local, tok, .none),
                    nom_sym.type_id,
                    tok,
                );
                const proj = try self.emitNode(.{
                    .tag = .hir_field_proj,
                    .flags = .{ .category = .place_imm, .is_synthetic = true },
                    .type_id = mem_sym.type_id,
                    .origin_token = tok,
                    .data = .{ .lhs = self_deref.asInt(), .rhs = field_ord },
                }, .none);
                const cloned_field = try self.emitDerivedMemberClone(proj, mem_sym.type_id, tok);
                try field_hirs.append(self.allocator, cloned_field.asInt());
                field_ord += 1;
            }
            const extra_idx = try self.store.appendLenPrefixedExtra(field_hirs.items);
            const constructed = try self.emitNode(.{
                .tag = .hir_construct,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = nom_sym.type_id,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(HirConstructKind.struct_init), .rhs = extra_idx },
            }, .none);
            return self.wrapSyntheticReturnBlock(constructed, nom_sym.type_id, tok);
        }

        if (nom_sym.kind == .enum_sym and !nom_sym.target_scope.isNone() and
            !self.pool.getFlags(nom_sym.type_id).is_copy)
        {
            const self_deref = try self.emitSyntheticDeref(
                try self.emitVarRef(self_local, tok, .none),
                nom_sym.type_id,
                tok,
            );
            var temp_arms: std.ArrayListUnmanaged(HirMatchArm) = .empty;
            defer temp_arms.deinit(self.allocator);
            var var_ord: u32 = 0;
            for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .enum_variant_sym) continue;

                var sub_start: u32 = 0;
                var sub_len: u32 = 0;
                var construct_extra: u32 = 0;
                if (mem_sym.type_id == .unit_ty) {
                    construct_extra = try self.store.appendLenPrefixedExtra(&.{});
                } else {
                    const ref_pay_ty = try self.pool.internRef(mem_sym.type_id, false);
                    const cap_local = try self.store.appendLocal(.{
                        .name = .empty,
                        .type_id = ref_pay_ty,
                        .decl_span = nom_sym.decl_span,
                        .mode = .let_mode,
                        .is_mut = false,
                        .is_param = false,
                        .is_temp = true,
                    });
                    const bind_pat = try self.store.appendPat(.{
                        .type_id = mem_sym.type_id,
                        .origin_token = tok,
                        .kind = .{ .bind = .{ .local_id = cap_local, .is_mut = false, .is_ref = true } },
                    });
                    sub_start = try self.store.appendExtraSlice(&[1]u32{bind_pat});
                    sub_len = 1;
                    const deref_pay = try self.emitSyntheticDeref(
                        try self.emitVarRef(cap_local, tok, .none),
                        mem_sym.type_id,
                        tok,
                    );
                    const cloned_pay = try self.emitDerivedMemberClone(deref_pay, mem_sym.type_id, tok);
                    construct_extra = try self.store.appendLenPrefixedExtra(&[1]u32{cloned_pay.asInt()});
                }

                const var_pat = try self.store.appendPat(.{
                    .type_id = nom_sym.type_id,
                    .origin_token = tok,
                    .kind = .{
                        .variant = .{
                            .tag_ordinal = var_ord,
                            .payload_ty = mem_sym.type_id,
                            .sub_start = sub_start,
                            .sub_len = sub_len,
                        },
                    },
                });
                const var_val = try self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = nom_sym.type_id,
                    .origin_token = tok,
                    .data = .{
                        .lhs = @as(u32, @backingInt(HirConstructKind.enum_variant)) | (var_ord << 8),
                        .rhs = construct_extra,
                    },
                }, .none);
                try temp_arms.append(self.allocator, .{
                    .pat_idx = var_pat,
                    .guard_hir = .none,
                    .body_hir = var_val,
                    .origin_token = tok,
                });
                var_ord += 1;
            }
            if (temp_arms.items.len > 0) {
                const arm_start: u32 = @intCast(self.store.match_arms.items.len);
                try self.store.match_arms.appendSlice(self.allocator, temp_arms.items);
                const match_extra = try self.store.appendExtraSlice(&[2]u32{
                    arm_start,
                    @intCast(temp_arms.items.len),
                });
                const match_hir = try self.emitNode(.{
                    .tag = .hir_match,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = nom_sym.type_id,
                    .origin_token = tok,
                    .data = .{ .lhs = self_deref.asInt(), .rhs = match_extra },
                }, .none);
                return self.wrapSyntheticReturnBlock(match_hir, nom_sym.type_id, tok);
            }
        }

        const deref_val = try self.emitSyntheticDeref(
            try self.emitVarRef(self_local, tok, .none),
            nom_sym.type_id,
            tok,
        );
        return self.wrapSyntheticReturnBlock(deref_val, nom_sym.type_id, tok);
    }

    /// Synthesizes `fn debug(&self) -> str` returning the nominal debug header string.
    fn synthDeriveDebugBody(
        self: *HirLowerer,
        nom_sym: symbol_resolver.SymbolRecord,
        tok: TokenIndex,
    ) !HirIndex {
        const label_id = try self.interner.intern(nom_sym.name_text);
        const str_hir = try self.emitConstVal(.{ .str_val = label_id }, .str_ty, tok, .none, true);
        return self.wrapSyntheticReturnBlock(str_hir, .str_ty, tok);
    }

    /// Wraps `ret_expr` in `hir_block { hir_return(ret_expr, .normal) }`.
    fn wrapSyntheticReturnBlock(
        self: *HirLowerer,
        ret_expr: HirIndex,
        ret_ty: TypeId,
        tok: TokenIndex,
    ) !HirIndex {
        const ret_node = try self.emitNode(.{
            .tag = .hir_return,
            .flags = .{ .category = .diverging, .is_synthetic = true },
            .type_id = .never_ty,
            .origin_token = tok,
            .data = .{ .lhs = ret_expr.asInt(), .rhs = @backingInt(ReturnErrorKind.normal) },
        }, .none);
        const stmts = [1]u32{ret_node.asInt()};
        const extra_idx = try self.store.appendLenPrefixedExtra(&stmts);
        return self.emitNode(.{
            .tag = .hir_block,
            .flags = .{ .category = .diverging, .is_synthetic = true },
            .type_id = ret_ty,
            .origin_token = tok,
            .data = .{ .lhs = extra_idx, .rhs = NONE_U32 },
        }, .none);
    }

    /// Looks up a method by `method_name` inside `owner_ty`'s nominal `target_scope`.
    fn lookupMethodOnType(self: *HirLowerer, owner_ty: TypeId, method_name: []const u8) !?SymbolIndex {
        const ty_node = self.pool.getNode(self.unwrapRefType(owner_ty));
        if (ty_node.tag != .struct_ty and ty_node.tag != .enum_ty and ty_node.tag != .union_ty) return null;
        const nom_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(ty_node.rhs)).*;
        if (nom_sym.target_scope.isNone()) return null;
        const m_id = try self.interner.intern(method_name);
        const found = self.sym_table.lookupInScopeDirect(nom_sym.target_scope, m_id, NamespaceMask.VALUE_ONLY);
        return if (found.isNone()) null else found;
    }

    /// Emits a synthetic dereference `*ptr_hir`.
    fn emitSyntheticDeref(
        self: *HirLowerer,
        ptr_hir: HirIndex,
        pointee_ty: TypeId,
        tok: TokenIndex,
    ) !HirIndex {
        return self.emitNode(.{
            .tag = .hir_unary_op,
            .flags = .{ .category = .place_imm, .is_synthetic = true },
            .type_id = self.concreteType(pointee_ty),
            .origin_token = tok,
            .data = .{ .lhs = @backingInt(HirUnaryOp.deref), .rhs = ptr_hir.asInt() },
        }, .none);
    }

    /// Emits a synthetic `&place` or `&mut place` node.
    fn emitSyntheticAddrOf(
        self: *HirLowerer,
        place_hir: HirIndex,
        ref_ty: TypeId,
        is_mut: bool,
        tok: TokenIndex,
    ) !HirIndex {
        return self.emitNode(.{
            .tag = .hir_unary_op,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = ref_ty,
            .origin_token = tok,
            .data = .{
                .lhs = @backingInt(if (is_mut) HirUnaryOp.addr_of_mut else HirUnaryOp.addr_of),
                .rhs = place_hir.asInt(),
            },
        }, .none);
    }

    /// Emits a synthetic `hir_binary_op` node.
    fn emitSyntheticBinOp(
        self: *HirLowerer,
        bin_op: HirBinaryOp,
        lhs_hir: HirIndex,
        rhs_hir: HirIndex,
        res_ty: TypeId,
        tok: TokenIndex,
    ) !HirIndex {
        const pair = [2]u32{ lhs_hir.asInt(), rhs_hir.asInt() };
        const extra_idx = try self.store.appendExtraSlice(&pair);
        return self.emitNode(.{
            .tag = .hir_binary_op,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = self.concreteType(res_ty),
            .origin_token = tok,
            .data = .{ .lhs = extra_idx, .rhs = @backingInt(bin_op) },
        }, .none);
    }

    /// Emits a synthetic `hir_call` to `callee_sym_idx`, adjusting and projecting `args` per formal signature (`CRIT-13`).
    fn emitDirectSymbolCall(
        self: *HirLowerer,
        callee_sym_idx: SymbolIndex,
        args: []const HirIndex,
        ret_ty: TypeId,
        tok: TokenIndex,
    ) !HirIndex {
        const callee_sym = self.sym_table.getSymbol(callee_sym_idx).*;
        const callee_hir = try self.emitNode(.{
            .tag = .hir_global_ref,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = callee_sym.type_id,
            .origin_token = tok,
            .data = .{ .lhs = callee_sym.def_id.asInt(), .rhs = callee_sym_idx.asInt() },
        }, .none);

        const sig_view = self.pool.getFnSignatureView(callee_sym.type_id);
        var wrapped_args: std.ArrayListUnmanaged(u32) = .empty;
        defer wrapped_args.deinit(self.allocator);
        try wrapped_args.ensureTotalCapacity(self.allocator, args.len);

        for (args, 0..) |arg_hir, i| {
            const p_ty = if (sig_view) |sv|
                (if (i < sv.paramCount()) self.concreteType(sv.getParamType(i)) else self.store.getNode(arg_hir).type_id)
            else
                self.store.getNode(arg_hir).type_id;
            const p_mode = if (sig_view) |sv|
                (if (i < sv.paramCount()) sv.getParamMode(i) else ParamMode.let_mode)
            else
                ParamMode.let_mode;
            const adjusted = try self.adjustReceiverForParam(arg_hir, p_ty, tok);
            const proj = try self.wrapArgProjection(adjusted, p_mode, tok);
            wrapped_args.appendAssumeCapacity(proj.asInt());
        }
        const extra_idx = try self.store.appendLenPrefixedExtra(wrapped_args.items);
        return self.emitNode(.{
            .tag = .hir_call,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = self.concreteType(ret_ty),
            .origin_token = tok,
            .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
        }, .none);
    }

    // -------------- Block, Loop & Statement Lowering --------------

    /// Enters a recursive lowering frame, returning `false` and emitting `E0508` if `MAX_HIR_LOWER_DEPTH` is hit.
    fn enterDepth(self: *HirLowerer, ast_origin: NodeIndex) !bool {
        if (self.recursion_depth >= MAX_HIR_LOWER_DEPTH) {
            self.store.has_overflowed_limits = true;
            if (!self.has_emitted_limit_diag) {
                self.has_emitted_limit_diag = true;
                try self.emitDiagnostic(
                    .e0508_comptime_resource_limit_exceeded,
                    self.astSpan(ast_origin),
                    "HIR lowering exceeded `MAX_HIR_LOWER_DEPTH` (512)",
                    "maximum AST-to-HIR recursion depth reached here",
                );
            }
            return false;
        }
        self.recursion_depth += 1;
        return true;
    }

    /// Exits a recursive lowering frame previously opened by `enterDepth`.
    inline fn leaveDepth(self: *HirLowerer) void {
        self.recursion_depth -= 1;
    }

    /// Lowers a lexical `.block` expression, optionally synthesizing a trailing `hir_return` for function bodies.
    fn lowerBlockExpr(
        self: *HirLowerer,
        block_id: NodeIndex,
        expected_ty: TypeId,
        is_auto_return_fn_body: bool,
    ) anyerror!HirIndex {
        if (block_id.isNone() or block_id.asInt() >= self.ast_arena.countNodes()) {
            return self.emitUnitConst(TokenIndex.fromInt(0), .none);
        }
        const block_node = self.ast_arena.getNode(block_id);
        if (!try self.enterDepth(block_id)) {
            return self.emitErrorHole(block_node.main_token, block_id, expected_ty);
        }
        defer self.leaveDepth();

        const saved_unsafe = self.is_in_unsafe;
        if (self.hasKeywordInCst(self.ast_arena.getCstOrigin(block_id), .kw_unsafe)) {
            self.is_in_unsafe = true;
        }
        const local_checkpoint = self.local_shadow_log.items.len;
        const ct_checkpoint = self.comptime_shadow_log.items.len;
        const zip_checkpoint = self.zip_shadow_log.items.len;
        defer {
            self.popZipBindingsTo(zip_checkpoint);
            self.popComptimeBindingsTo(ct_checkpoint);
            self.popLexicalLocalsTo(local_checkpoint);
            self.is_in_unsafe = saved_unsafe;
        }

        var stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer stmts.deinit(self.allocator);

        var has_diverged = false;
        for (self.getAstExtraSlice(block_id, false)) |raw_stmt_id| {
            try self.lowerStmt(NodeIndex.fromInt(raw_stmt_id), &stmts, &has_diverged);
            if (self.comptime_loop_state != .normal) break;
        }

        var tail_hir: HirIndex = .none;
        if (block_node.rhs.tag == .node and self.comptime_loop_state == .normal) {
            const tail_ast_id = NodeIndex.fromInt(block_node.rhs.payload);
            tail_hir = try self.lowerExpr(tail_ast_id, expected_ty);
            if (!tail_hir.isNone() and self.store.getNode(tail_hir).type_id == .never_ty) {
                try stmts.append(self.allocator, tail_hir.asInt());
                tail_hir = .none;
                has_diverged = true;
            }
        }

        if (is_auto_return_fn_body) {
            if (!tail_hir.isNone()) {
                const err_kind = self.classifyReturnExpr(tail_hir, expected_ty);
                const ret_node = try self.emitNode(.{
                    .tag = .hir_return,
                    .flags = .{ .category = .diverging, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                    .type_id = .never_ty,
                    .origin_token = block_node.main_token,
                    .data = .{ .lhs = tail_hir.asInt(), .rhs = @backingInt(err_kind) },
                }, block_id);
                try stmts.append(self.allocator, ret_node.asInt());
                tail_hir = .none;
                has_diverged = true;
            } else if (!has_diverged and self.concreteType(expected_ty) == .unit_ty) {
                const unit_val = try self.emitUnitConst(block_node.main_token, .none);
                const ret_node = try self.emitNode(.{
                    .tag = .hir_return,
                    .flags = .{ .category = .diverging, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                    .type_id = .never_ty,
                    .origin_token = block_node.main_token,
                    .data = .{ .lhs = unit_val.asInt(), .rhs = @backingInt(ReturnErrorKind.normal) },
                }, block_id);
                try stmts.append(self.allocator, ret_node.asInt());
                has_diverged = true;
            }
        }

        const extra_idx = try self.store.appendLenPrefixedExtra(stmts.items);
        const block_ty: TypeId = if (!tail_hir.isNone())
            self.store.getNode(tail_hir).type_id
        else if (has_diverged)
            .never_ty
        else
            .unit_ty;

        return self.emitNode(.{
            .tag = .hir_block,
            .flags = .{
                .category = if (has_diverged and tail_hir.isNone()) .diverging else .rvalue,
                .is_unsafe = self.is_in_unsafe,
            },
            .type_id = self.concreteType(block_ty),
            .origin_token = block_node.main_token,
            .data = .{ .lhs = extra_idx, .rhs = tail_hir.asInt() },
        }, block_id);
    }

    /// Classifies `val_hir` for `defer` vs. `errdefer` cleanup routing (`[CRITICAL-08]`).
    fn classifyReturnExpr(self: *const HirLowerer, val_hir: HirIndex, fn_ret_ty: TypeId) ReturnErrorKind {
        if (val_hir.isNone()) return .normal;
        const ret_ty_node = self.pool.getNode(self.pool.unwrapUnderlyingType(fn_ret_ty));
        if (ret_ty_node.tag != .result_ty and ret_ty_node.tag != .optional_ty) return .normal;

        const val_node = self.store.getNode(val_hir);
        if (val_node.tag == .hir_construct) {
            const construct_kind: HirConstructKind = @fromBackingInt(@intCast(@as(u8, @truncate(val_node.data.lhs))));
            return switch (construct_kind) {
                .result_ok, .optional_some => .normal,
                .result_err, .optional_none => .explicit_err,
                else => .dynamic_fallible,
            };
        }
        if (val_node.tag == .hir_const_val and val_node.data.lhs < self.store.const_pool.items.len) {
            const const_val = self.store.const_pool.items[val_node.data.lhs];
            if (const_val == .variant) {
                if (ret_ty_node.tag == .result_ty) {
                    return if (const_val.variant.tag_ordinal == 0) .normal else .explicit_err;
                }
                return if (const_val.variant.tag_ordinal == 1) .normal else .explicit_err;
            }
        }
        return .dynamic_fallible;
    }

    /// Lowers a single statement inside a lexical block, appending 0, 1, or more `HirIndex` items to `out_stmts`.
    fn lowerStmt(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
        has_diverged: *bool,
    ) anyerror!void {
        if (stmt_id.isNone() or stmt_id.asInt() >= self.ast_arena.countNodes()) return;
        const stmt_node = self.ast_arena.getNode(stmt_id);
        if (!try self.enterDepth(stmt_id)) {
            const hole = try self.emitErrorHole(stmt_node.main_token, stmt_id, .unit_ty);
            try out_stmts.append(self.allocator, hole.asInt());
            return;
        }
        defer self.leaveDepth();

        switch (stmt_node.tag) {
            .stmt_hole, .expr_hole, .item_hole => {
                const hole = try self.emitErrorHole(stmt_node.main_token, stmt_id, .unit_ty);
                try out_stmts.append(self.allocator, hole.asInt());
            },
            .fn_decl,
            .struct_decl,
            .enum_decl,
            .union_decl,
            .type_alias_decl,
            .trait_decl,
            .impl_decl,
            .use_decl,
            => {},
            .local_var_decl => try self.lowerLocalVarDecl(stmt_id, out_stmts),
            .const_decl => try self.lowerLocalConstDecl(stmt_id, out_stmts),
            .defer_stmt => {
                const def_hir = try self.lowerDeferStmt(stmt_id);
                if (!def_hir.isNone()) try out_stmts.append(self.allocator, def_hir.asInt());
            },
            .return_stmt => {
                const val_hir = if (stmt_node.lhs.tag == .node)
                    try self.lowerExpr(NodeIndex.fromInt(stmt_node.lhs.payload), self.current_fn_ret_ty)
                else
                    try self.emitUnitConst(stmt_node.main_token, .none);
                const err_kind = self.classifyReturnExpr(val_hir, self.current_fn_ret_ty);
                const ret_hir = try self.emitNode(.{
                    .tag = .hir_return,
                    .flags = .{ .category = .diverging, .is_unsafe = self.is_in_unsafe },
                    .type_id = .never_ty,
                    .origin_token = stmt_node.main_token,
                    .data = .{ .lhs = val_hir.asInt(), .rhs = @backingInt(err_kind) },
                }, stmt_id);
                try out_stmts.append(self.allocator, ret_hir.asInt());
                has_diverged.* = true;
            },
            .break_stmt => {
                if (self.is_in_comptime_for) {
                    if (self.comptime_runtime_cond_depth > 0) {
                        try self.emitDiagnostic(
                            .e0503_forbidden_comptime_operation,
                            self.astSpan(stmt_id),
                            "`break` targeting a `comptime for` loop cannot depend on a runtime condition",
                            "use `comptime if` or a runtime `for` loop instead",
                        );
                    } else {
                        self.comptime_loop_state = .broken;
                    }
                    has_diverged.* = true;
                    return;
                }
                const val_hir = if (stmt_node.lhs.tag == .node)
                    try self.lowerExpr(NodeIndex.fromInt(stmt_node.lhs.payload), .err_ty)
                else
                    HirIndex.none;
                const loop_id = self.current_loop_id orelse 0;
                const brk_hir = try self.emitNode(.{
                    .tag = .hir_break,
                    .flags = .{ .category = .diverging, .is_unsafe = self.is_in_unsafe },
                    .type_id = .never_ty,
                    .origin_token = stmt_node.main_token,
                    .data = .{ .lhs = loop_id, .rhs = val_hir.asInt() },
                }, stmt_id);
                try out_stmts.append(self.allocator, brk_hir.asInt());
                has_diverged.* = true;
            },
            .continue_stmt => {
                if (self.is_in_comptime_for) {
                    if (self.comptime_runtime_cond_depth > 0) {
                        try self.emitDiagnostic(
                            .e0503_forbidden_comptime_operation,
                            self.astSpan(stmt_id),
                            "`continue` targeting a `comptime for` loop cannot depend on a runtime condition",
                            "use `comptime if` or a runtime `for` loop instead",
                        );
                    } else {
                        self.comptime_loop_state = .continued;
                    }
                    has_diverged.* = true;
                    return;
                }
                const loop_id = self.current_loop_id orelse 0;
                const cont_hir = try self.emitNode(.{
                    .tag = .hir_continue,
                    .flags = .{ .category = .diverging, .is_unsafe = self.is_in_unsafe },
                    .type_id = .never_ty,
                    .origin_token = stmt_node.main_token,
                    .data = .{ .lhs = loop_id, .rhs = 0 },
                }, stmt_id);
                try out_stmts.append(self.allocator, cont_hir.asInt());
                has_diverged.* = true;
            },
            .for_stmt => try self.lowerForStmt(stmt_id, out_stmts),
            .while_stmt => {
                const while_hir = try self.lowerWhileStmt(stmt_id);
                if (!while_hir.isNone()) try out_stmts.append(self.allocator, while_hir.asInt());
            },
            .assign_stmt => {
                const assign_hir = try self.lowerAssignStmt(stmt_id);
                if (!assign_hir.isNone()) try out_stmts.append(self.allocator, assign_hir.asInt());
            },
            else => {
                const expr_hir = try self.lowerExpr(stmt_id, .unit_ty);
                if (!expr_hir.isNone()) {
                    try out_stmts.append(self.allocator, expr_hir.asInt());
                    if (self.store.getNode(expr_hir).type_id == .never_ty) {
                        has_diverged.* = true;
                    }
                }
            },
        }
    }

    /// Lowers `let` / `var` local declarations, including irrefutable destructuring and `let Pat = init else { … }`.
    fn lowerLocalVarDecl(
        self: *HirLowerer,
        decl_id: NodeIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
    ) anyerror!void {
        const decl_node = self.ast_arena.getNode(decl_id);
        const decl_cst = self.ast_arena.getCstOrigin(decl_id);
        const pat_id = if (decl_node.lhs.tag == .node) NodeIndex.fromInt(decl_node.lhs.payload) else .none;
        const is_var = !decl_node.main_token.isNone() and
            self.tokens.getToken(decl_node.main_token).kind == .kw_var;
        const is_mut = is_var or self.hasKeywordInCst(decl_cst, .kw_mut);

        var init_expr_ast: NodeIndex = .none;
        var else_block_ast: NodeIndex = .none;
        if (!decl_cst.isNone() and decl_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = decl_cst.asInt();
            const rec = self.cst_arena.getNode(decl_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var pat_end_pos: usize = start_idx + 1;
            if (!pat_id.isNone()) {
                const pat_cst = self.ast_arena.getCstOrigin(pat_id);
                if (!pat_cst.isNone() and pat_cst.asInt() < self.cst_arena.countNodes()) {
                    const pat_rec = self.cst_arena.getNode(pat_cst);
                    pat_end_pos = @min(
                        @as(usize, pat_cst.asInt()) + @max(@as(usize, pat_rec.subtree_size), 1),
                        end_idx,
                    );
                }
            }
            var has_seen_eq = false;
            var cur = pat_end_pos;
            while (cur < end_idx) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.kind == .let_else_branch) {
                    const branch_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                    else_block_ast = self.findFirstAstInCstRange(cur + 1, branch_end);
                    cur = branch_end;
                    continue;
                }
                if (sub.subtree_size <= 1 and !sub.flags.is_bracketed and
                    !sub.flags.is_missing_or_injected and !sub.token.isNone() and
                    sub.token.asInt() < self.tokens.countTokens())
                {
                    if (self.tokens.getToken(sub.token).kind == .eq) has_seen_eq = true;
                }
                cur += 1;
            }
            if (has_seen_eq and decl_node.rhs.tag == .node) {
                init_expr_ast = NodeIndex.fromInt(decl_node.rhs.payload);
            }
        } else if (decl_node.rhs.tag == .node) {
            const rhs_id = NodeIndex.fromInt(decl_node.rhs.payload);
            if (!isTypeAstTag(self.ast_arena.getNode(rhs_id).tag)) {
                init_expr_ast = rhs_id;
            }
        }

        const pat_ty = self.nodeType(pat_id);
        const init_ty = if (!init_expr_ast.isNone()) self.nodeType(init_expr_ast) else .err_ty;
        const resolved_ty = if (!pat_ty.isError())
            pat_ty
        else if (!init_ty.isError())
            init_ty
        else
            .unit_ty;

        // [1] Simple `let x = init;` or uninitialized `var x: T;`:
        if (else_block_ast.isNone() and !pat_id.isNone() and
            self.ast_arena.getNode(pat_id).tag == .bind_pat)
        {
            const pat_cst = self.ast_arena.getCstOrigin(pat_id);
            const is_ref_pat = self.hasKeywordInCst(pat_cst, .kw_ref) or self.hasKeywordInCst(pat_cst, .amp);
            const is_ref_mut = self.hasKeywordInCst(pat_cst, .kw_mut);

            var init_hir: HirIndex = .none;
            var actual_ty: TypeId = resolved_ty;
            if (!init_expr_ast.isNone()) {
                if (is_ref_pat) {
                    const pointee_expect = if (self.pool.getTag(resolved_ty) == .ref_ty or
                        self.pool.getTag(resolved_ty) == .mut_ref_ty)
                        TypeId.fromInt(self.pool.getNode(resolved_ty).lhs)
                    else
                        resolved_ty;
                    const raw_init = try self.lowerExpr(init_expr_ast, pointee_expect);
                    const raw_ty = self.store.getNode(raw_init).type_id;
                    actual_ty = if (self.pool.getTag(resolved_ty) == .ref_ty or
                        self.pool.getTag(resolved_ty) == .mut_ref_ty)
                        resolved_ty
                    else
                        try self.pool.internRef(raw_ty, is_ref_mut);
                    init_hir = try self.emitSyntheticAddrOf(
                        raw_init,
                        actual_ty,
                        self.pool.getTag(actual_ty) == .mut_ref_ty,
                        decl_node.main_token,
                    );
                } else {
                    init_hir = try self.lowerExpr(init_expr_ast, resolved_ty);
                    if (resolved_ty.isError() or resolved_ty == .unit_ty) {
                        actual_ty = self.store.getNode(init_hir).type_id;
                    }
                    if (!init_hir.isNone() and self.store.getNode(init_hir).tag == .hir_closure and
                        self.hasAttrNamedInCst(decl_cst, "local"))
                    {
                        const fn_meta_idx = self.store.getNode(init_hir).data.lhs;
                        if (fn_meta_idx < self.store.functions.items.len) {
                            self.store.functions.items[fn_meta_idx].is_local_closure = true;
                        }
                    }
                }
            }
            const slot_id = try self.bindSimplePatternLocal(pat_id, actual_ty, is_mut);
            const local_hir = try self.emitNode(.{
                .tag = .hir_local_decl,
                .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
                .type_id = .unit_ty,
                .origin_token = decl_node.main_token,
                .data = .{ .lhs = slot_id, .rhs = init_hir.asInt() },
            }, decl_id);
            try out_stmts.append(self.allocator, local_hir.asInt());
            return;
        }

        // [2] Wildcard `let _ = init;`:
        if (else_block_ast.isNone() and !pat_id.isNone() and
            self.ast_arena.getNode(pat_id).tag == .wildcard_pat)
        {
            if (!init_expr_ast.isNone()) {
                const discarded_hir = try self.lowerExpr(init_expr_ast, resolved_ty);
                const tmp_slot = try self.allocTempLocal(
                    self.store.getNode(discarded_hir).type_id,
                    decl_node.main_token,
                    false,
                );
                const local_hir = try self.emitNode(.{
                    .tag = .hir_local_decl,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .origin_token = decl_node.main_token,
                    .data = .{ .lhs = tmp_slot, .rhs = discarded_hir.asInt() },
                }, decl_id);
                try out_stmts.append(self.allocator, local_hir.asInt());
            }
            return;
        }

        // [3] Guard `let Pat = init else { diverge }` (`DR-13` §2.2 Rule 4) or tuple/struct destructuring:
        const scrutinee_hir = if (!init_expr_ast.isNone())
            try self.lowerExpr(init_expr_ast, resolved_ty)
        else
            try self.emitUnitConst(decl_node.main_token, .none);
        const scrut_ty = self.store.getNode(scrutinee_hir).type_id;

        // Evaluate `else` block BEFORE binding `pat_id` so pattern captures are not visible in `else`:
        var else_hir: HirIndex = .none;
        if (!else_block_ast.isNone()) {
            else_hir = try self.lowerBlockExpr(else_block_ast, .never_ty, false);
        }

        if (!scrutinee_hir.isNone() and self.store.getNode(scrutinee_hir).tag == .hir_closure and
            self.hasAttrNamedInCst(decl_cst, "local"))
        {
            const fn_meta_idx = self.store.getNode(scrutinee_hir).data.lhs;
            if (fn_meta_idx < self.store.functions.items.len) {
                self.store.functions.items[fn_meta_idx].is_local_closure = true;
            }
        }

        const lowered_pat_idx = try self.lowerTopPattern(pat_id, scrut_ty, is_mut);
        const arm_start: u32 = @intCast(self.store.match_arms.items.len);
        try self.store.match_arms.append(self.allocator, .{
            .pat_idx = lowered_pat_idx,
            .guard_hir = .none,
            .body_hir = try self.emitUnitConst(decl_node.main_token, .none),
            .origin_token = decl_node.main_token,
        });
        var arm_count: u32 = 1;
        if (!else_hir.isNone()) {
            const wild_pat = try self.store.appendPat(.{
                .type_id = scrut_ty,
                .origin_token = decl_node.main_token,
                .kind = .wildcard,
            });
            try self.store.match_arms.append(self.allocator, .{
                .pat_idx = wild_pat,
                .guard_hir = .none,
                .body_hir = else_hir,
                .origin_token = decl_node.main_token,
            });
            arm_count = 2;
        }
        const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, arm_count });
        const match_hir = try self.emitNode(.{
            .tag = .hir_match,
            .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
            .type_id = .unit_ty,
            .origin_token = decl_node.main_token,
            .data = .{ .lhs = scrutinee_hir.asInt(), .rhs = match_extra },
        }, decl_id);
        try out_stmts.append(self.allocator, match_hir.asInt());
    }

    /// Allocates and registers a local slot for a `.bind_pat` node.
    fn bindSimplePatternLocal(
        self: *HirLowerer,
        pat_id: NodeIndex,
        slot_ty: TypeId,
        is_decl_mut: bool,
    ) !u32 {
        const pat_node = self.ast_arena.getNode(pat_id);
        const pat_cst = self.ast_arena.getCstOrigin(pat_id);
        const is_ref_pat = self.hasKeywordInCst(pat_cst, .kw_ref) or self.hasKeywordInCst(pat_cst, .amp);
        const is_mut = is_decl_mut or (!is_ref_pat and self.hasKeywordInCst(pat_cst, .kw_mut));
        const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, pat_node.main_token);
        const name_id = if (lexeme.len > 0 and !std.mem.eql(u8, lexeme, "_"))
            try self.interner.intern(lexeme)
        else
            SymbolId.empty;
        const sym_idx = self.nodeSymbol(pat_id);
        const concrete_ty = self.concreteType(if (!sym_idx.isNone())
            self.sym_table.getSymbol(sym_idx).type_id
        else
            slot_ty);
        const slot_id = try self.store.appendLocal(.{
            .name = name_id,
            .type_id = concrete_ty,
            .decl_span = self.astSpan(pat_id),
            .mode = .let_mode,
            .is_mut = is_mut,
            .is_param = false,
            .is_temp = false,
            .symbol_index = sym_idx,
        });
        if (!sym_idx.isNone()) {
            try self.symbol_to_local.put(self.allocator, sym_idx.asInt(), slot_id);
        }
        try self.pushLexicalLocal(name_id, slot_id);
        return slot_id;
    }

    /// Lowers a block-scoped `const NAME = expr;` statement and binds `NAME` in `active_comptime_vals`.
    fn lowerLocalConstDecl(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
    ) !void {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const name_tok = symbol_resolver.findItemNameToken(
            self.tokens,
            self.cst_arena,
            self.ast_arena.getCstOrigin(stmt_id),
            stmt_node.main_token,
        );
        const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, name_tok);
        const name_id = if (lexeme.len > 0) try self.interner.intern(lexeme) else SymbolId.empty;

        var init_hir: HirIndex = .none;
        var resolved_ty: TypeId = .i32_ty;
        if (stmt_node.rhs.tag == .node) {
            const init_id = NodeIndex.fromInt(stmt_node.rhs.payload);
            const cand_ty = self.nodeType(init_id);
            if (!cand_ty.isError()) resolved_ty = cand_ty;
            if (try self.tryEvalAstComptime(init_id, resolved_ty)) |folded_val| {
                try self.pushComptimeBinding(name_id, folded_val);
                init_hir = try self.emitConstVal(folded_val, resolved_ty, stmt_node.main_token, init_id, true);
            } else {
                init_hir = try self.lowerExpr(init_id, resolved_ty);
            }
        }
        const const_node = try self.emitNode(.{
            .tag = .hir_const_decl,
            .flags = .{ .category = .rvalue },
            .type_id = self.concreteType(resolved_ty),
            .origin_token = stmt_node.main_token,
            .data = .{ .lhs = name_id.asInt(), .rhs = init_hir.asInt() },
        }, stmt_id);
        try out_stmts.append(self.allocator, const_node.asInt());
    }

    /// Lowers `defer` and `errdefer |err|` statements into `hir_defer`.
    fn lowerDeferStmt(self: *HirLowerer, stmt_id: NodeIndex) !HirIndex {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const is_errdefer = !stmt_node.main_token.isNone() and
            self.tokens.getToken(stmt_node.main_token).kind == .kw_errdefer;

        const local_checkpoint = self.local_shadow_log.items.len;
        defer self.popLexicalLocalsTo(local_checkpoint);

        var err_local_plus1: u32 = 0;
        if (is_errdefer and stmt_node.lhs.tag == .token) {
            const cap_tok = TokenIndex.fromInt(stmt_node.lhs.payload);
            const cap_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, cap_tok);
            const ret_node = self.pool.getNode(self.pool.unwrapUnderlyingType(self.current_fn_ret_ty));
            const err_ty: TypeId = if (ret_node.tag == .result_ty)
                TypeId.fromInt(ret_node.rhs)
            else
                .unit_ty;
            const cap_sym_id = if (cap_name.len > 0 and !std.mem.eql(u8, cap_name, "_"))
                try self.interner.intern(cap_name)
            else
                SymbolId.empty;
            const err_slot = try self.store.appendLocal(.{
                .name = cap_sym_id,
                .type_id = self.concreteType(err_ty),
                .decl_span = self.tokens.getTokenSpan(self.store.file_id, cap_tok),
                .mode = .let_mode,
                .is_mut = false,
                .is_param = false,
                .is_temp = cap_sym_id == .empty,
            });
            try self.pushLexicalLocal(cap_sym_id, err_slot);
            err_local_plus1 = err_slot + 1;
        }

        const cleanup_hir = if (stmt_node.rhs.tag == .node) blk: {
            const body_id = NodeIndex.fromInt(stmt_node.rhs.payload);
            if (self.ast_arena.getNode(body_id).tag == .block) {
                break :blk try self.lowerBlockExpr(body_id, .unit_ty, false);
            }
            break :blk try self.lowerExpr(body_id, .unit_ty);
        } else try self.emitUnitConst(stmt_node.main_token, .none);

        const encoded_lhs: u32 = @as(u32, @intFromBool(is_errdefer)) | (err_local_plus1 << 1);
        return self.emitNode(.{
            .tag = .hir_defer,
            .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
            .type_id = .unit_ty,
            .origin_token = stmt_node.main_token,
            .data = .{ .lhs = encoded_lhs, .rhs = cleanup_hir.asInt() },
        }, stmt_id);
    }

    /// Dispatches `comptime for` unrolling (`MAX_UNROLL = 4096`) vs. runtime `for` canonicalization.
    fn lowerForStmt(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
    ) anyerror!void {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const pair = self.getAstExtraSlice(stmt_id, false);
        const pat_id = if (pair.len >= 1) NodeIndex.fromInt(pair[0]) else .none;
        const iter_id = if (pair.len >= 2) NodeIndex.fromInt(pair[1]) else .none;
        const body_id = if (stmt_node.rhs.tag == .node) NodeIndex.fromInt(stmt_node.rhs.payload) else .none;

        const is_comptime_for = !stmt_node.main_token.isNone() and
            self.tokens.getToken(stmt_node.main_token).kind == .kw_comptime;
        if (is_comptime_for) {
            try self.lowerComptimeForStmt(stmt_id, pat_id, iter_id, body_id, out_stmts);
            return;
        }
        const loop_hir = try self.lowerRuntimeForStmt(stmt_id, pat_id, iter_id, body_id);
        if (!loop_hir.isNone()) try out_stmts.append(self.allocator, loop_hir.asInt());
    }

    /// Statically unrolls `comptime for pat in iter_expr { body }` up to `MAX_UNROLL = 4096` (`E0501`).
    fn lowerComptimeForStmt(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        pat_id: NodeIndex,
        iter_id: NodeIndex,
        body_id: NodeIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
    ) anyerror!void {
        var elements: std.ArrayListUnmanaged(ComptimeValue) = .empty;
        defer elements.deinit(self.allocator);

        const has_exceeded = try self.collectComptimeForSequence(iter_id, &elements);
        if (has_exceeded or elements.items.len > MAX_UNROLL) {
            try self.emitDiagnostic(
                .e0501_comptime_step_limit_exceeded,
                self.astSpan(stmt_id),
                "`comptime for` loop exceeded `MAX_UNROLL` (4,096 iterations)",
                "reduce `comptime for` iteration count to at most 4,096",
            );
            return;
        }

        const saved_in_ct_for = self.is_in_comptime_for;
        const saved_rt_cond_depth = self.comptime_runtime_cond_depth;
        const saved_ct_state = self.comptime_loop_state;
        self.is_in_comptime_for = true;
        self.comptime_runtime_cond_depth = 0;
        self.comptime_loop_state = .normal;
        defer {
            self.is_in_comptime_for = saved_in_ct_for;
            self.comptime_runtime_cond_depth = saved_rt_cond_depth;
            self.comptime_loop_state = saved_ct_state;
        }

        const pat_name_id = self.extractBindPatNameId(pat_id);
        for (elements.items) |elem_val| {
            const ct_checkpoint = self.comptime_shadow_log.items.len;
            defer self.popComptimeBindingsTo(ct_checkpoint);
            try self.pushComptimeBinding(pat_name_id, elem_val);

            const unrolled_blk = try self.lowerBlockExpr(body_id, .unit_ty, false);
            if (!unrolled_blk.isNone()) {
                try out_stmts.append(self.allocator, unrolled_blk.asInt());
            }
            if (self.comptime_loop_state == .continued) {
                self.comptime_loop_state = .normal;
                continue;
            }
            if (self.comptime_loop_state == .broken) {
                self.comptime_loop_state = .normal;
                break;
            }
        }
    }

    /// Collects compile-time elements for `comptime for` (`a..b`, `a..=b`, array/tuple literals, `.fields`, `.variants`).
    /// Returns `true` if the sequence exceeds `MAX_UNROLL` (`4,096`).
    fn collectComptimeForSequence(
        self: *HirLowerer,
        iter_id: NodeIndex,
        out_elems: *std.ArrayListUnmanaged(ComptimeValue),
    ) !bool {
        if (iter_id.isNone() or iter_id.asInt() >= self.ast_arena.countNodes()) return false;
        const iter_node = self.ast_arena.getNode(iter_id);

        // [1] Compile-time integer range `start..end` or `start..=end`:
        if (iter_node.tag == .binary_expr and !iter_node.main_token.isNone()) {
            const op_kind = self.tokens.getToken(iter_node.main_token).kind;
            if ((op_kind == .dotdot or op_kind == .dotdoteq) and
                iter_node.lhs.tag == .node and iter_node.rhs.tag == .node)
            {
                const lhs_ast_id = NodeIndex.fromInt(iter_node.lhs.payload);
                const rhs_ast_id = NodeIndex.fromInt(iter_node.rhs.payload);
                const start_val = (try self.tryEvalAstComptime(lhs_ast_id, .i64_ty)) orelse return false;
                const end_val = (try self.tryEvalAstComptime(rhs_ast_id, .i64_ty)) orelse return false;
                if (start_val != .int_val or end_val != .int_val) return false;
                const is_inclusive = op_kind == .dotdoteq;
                const lhs_ty = self.pool.unwrapUnderlyingType(self.nodeType(lhs_ast_id));
                const rhs_ty = self.pool.unwrapUnderlyingType(self.nodeType(rhs_ast_id));
                const is_u128 = lhs_ty == .u128_ty or rhs_ty == .u128_ty;

                var diff: u128 = 0;
                if (is_u128) {
                    const start_u: u128 = @bitCast(start_val.int_val);
                    const end_u: u128 = @bitCast(end_val.int_val);
                    if ((!is_inclusive and start_u >= end_u) or (is_inclusive and start_u > end_u)) {
                        return false;
                    }
                    diff = end_u - start_u;
                } else {
                    if ((!is_inclusive and start_val.int_val >= end_val.int_val) or
                        (is_inclusive and start_val.int_val > end_val.int_val))
                    {
                        return false;
                    }
                    diff = @bitCast(end_val.int_val -% start_val.int_val);
                }
                if (diff > MAX_UNROLL or (is_inclusive and diff >= MAX_UNROLL)) return true;
                const total_iters: usize = @intCast(if (is_inclusive) diff + 1 else diff);

                var cur = start_val.int_val;
                var count: usize = 0;
                while (count < total_iters) : (count += 1) {
                    try out_elems.append(self.allocator, .{ .int_val = cur });
                    if (count + 1 < total_iters) cur = cur +% 1;
                }
                return false;
            }
        }

        // [2] Reflection `@type_info[T]().fields` or `@type_info[T]().variants`:
        if (iter_node.tag == .field_access and iter_node.lhs.tag == .node and iter_node.rhs.tag == .token) {
            const base_id = NodeIndex.fromInt(iter_node.lhs.payload);
            const member_tok = TokenIndex.fromInt(iter_node.rhs.payload);
            const member_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, member_tok);
            if (try self.tryEvalAstComptime(base_id, .err_ty)) |base_val| {
                if (base_val == .type_info_mirror) {
                    const target_ty = self.unwrapRefType(base_val.type_info_mirror.reflected_ty);
                    const ty_rec = self.pool.getNode(target_ty);
                    if (std.mem.eql(u8, member_name, "fields") and
                        (ty_rec.tag == .struct_ty or ty_rec.tag == .union_ty or ty_rec.tag == .bit_field_ty))
                    {
                        const nom_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(ty_rec.rhs)).*;
                        if (!nom_sym.target_scope.isNone()) {
                            var ord: u32 = 0;
                            for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |m_idx| {
                                const m_sym = self.sym_table.getSymbol(m_idx).*;
                                if (m_sym.kind != .field_sym) continue;
                                if (out_elems.items.len >= MAX_UNROLL) return true;
                                const field_offset = if (ty_rec.tag == .struct_ty)
                                    type_system.computeStructFieldOffset(
                                        self.pool,
                                        self.sym_table,
                                        target_ty,
                                        ord,
                                        self.store.target_layout,
                                    ) orelse 0
                                else
                                    0;
                                try out_elems.append(self.allocator, .{
                                    .field_info_mirror = .{
                                        .owner_ty = target_ty,
                                        .owner_def_id = nom_sym.def_id,
                                        .field_ordinal = ord,
                                        .field_name = m_sym.name,
                                        .field_ty = m_sym.type_id,
                                        .byte_offset = field_offset,
                                    },
                                });
                                ord += 1;
                            }
                        }
                        return false;
                    }
                    if (std.mem.eql(u8, member_name, "variants") and ty_rec.tag == .enum_ty) {
                        const nom_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(ty_rec.rhs)).*;
                        if (!nom_sym.target_scope.isNone()) {
                            var ord: u32 = 0;
                            for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |m_idx| {
                                const m_sym = self.sym_table.getSymbol(m_idx).*;
                                if (m_sym.kind != .enum_variant_sym) continue;
                                if (out_elems.items.len >= MAX_UNROLL) return true;
                                try out_elems.append(self.allocator, .{
                                    .variant_info_mirror = .{
                                        .owner_ty = target_ty,
                                        .owner_def_id = nom_sym.def_id,
                                        .variant_ordinal = ord,
                                        .variant_name = m_sym.name,
                                        .payload_ty = m_sym.type_id,
                                    },
                                });
                                ord += 1;
                            }
                        }
                        return false;
                    }
                }
            }
        }

        // [3] Explicit array or tuple literal `[e0, e1, …]`:
        if (iter_node.tag == .array_lit or iter_node.tag == .tuple_lit) {
            const item_nodes = self.getAstExtraSlice(iter_id, false);
            if (iter_node.tag == .array_lit and item_nodes.len == 2 and
                type_system.hasShallowSemicolonInArrayCst(
                    self.cst_arena,
                    self.tokens,
                    self.ast_arena.getCstOrigin(iter_id),
                ))
            {
                const count_val = (try self.tryEvalAstComptime(NodeIndex.fromInt(item_nodes[1]), .usize_ty)) orelse
                    return false;
                if (count_val != .int_val or count_val.int_val < 0) return false;
                if (count_val.int_val > MAX_UNROLL) return true;
                const elem_val = (try self.tryEvalAstComptime(NodeIndex.fromInt(item_nodes[0]), .err_ty)) orelse
                    return false;
                var idx: usize = 0;
                while (idx < @as(usize, @intCast(count_val.int_val))) : (idx += 1) {
                    try out_elems.append(self.allocator, elem_val);
                }
                return false;
            }
            if (item_nodes.len > MAX_UNROLL) return true;
            for (item_nodes) |raw_elem| {
                if (try self.tryEvalAstComptime(NodeIndex.fromInt(raw_elem), .err_ty)) |folded| {
                    try out_elems.append(self.allocator, folded);
                }
            }
            return false;
        }

        // [4] Evaluated `aggregate` constant (`const ITEMS = [1, 2, 3]`):
        if (try self.tryEvalAstComptime(iter_id, .err_ty)) |seq_val| {
            if (seq_val == .aggregate) {
                if (seq_val.aggregate.elem_len > MAX_UNROLL) return true;
                const start = seq_val.aggregate.elem_start;
                const end = start + seq_val.aggregate.elem_len;
                for (self.store.const_elements.items[start..end]) |const_idx| {
                    try out_elems.append(self.allocator, self.store.const_pool.items[const_idx]);
                }
            }
        }
        return false;
    }

    /// Lowers runtime `for pat in iter_expr { body }` into canonical `continue`-safe & `u8`-overflow-safe `hir_loop`.
    fn lowerRuntimeForStmt(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        pat_id: NodeIndex,
        iter_id: NodeIndex,
        body_id: NodeIndex,
    ) anyerror!HirIndex {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const tok = stmt_node.main_token;
        if (iter_id.isNone() or iter_id.asInt() >= self.ast_arena.countNodes()) {
            return self.emitUnitConst(tok, stmt_id);
        }
        const iter_node = self.ast_arena.getNode(iter_id);

        const loop_id = self.next_loop_id;
        self.next_loop_id += 1;
        const saved_loop_id = self.current_loop_id;
        const saved_in_ct_for = self.is_in_comptime_for;
        self.current_loop_id = loop_id;
        self.is_in_comptime_for = false;
        const local_checkpoint = self.local_shadow_log.items.len;
        const zip_checkpoint = self.zip_shadow_log.items.len;
        defer {
            self.popZipBindingsTo(zip_checkpoint);
            self.popLexicalLocalsTo(local_checkpoint);
            self.is_in_comptime_for = saved_in_ct_for;
            self.current_loop_id = saved_loop_id;
        }

        var outer_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer outer_stmts.deinit(self.allocator);

        // [1] Exclusive `start..end` and inclusive `start..=end` (`0u8..=255u8` overflow-safe, `DR-13` §2.2 Rule 5):
        if (iter_node.tag == .binary_expr and !iter_node.main_token.isNone()) {
            const op_kind = self.tokens.getToken(iter_node.main_token).kind;
            if ((op_kind == .dotdot or op_kind == .dotdoteq) and
                iter_node.lhs.tag == .node and iter_node.rhs.tag == .node)
            {
                const is_inclusive = op_kind == .dotdoteq;
                const elem_ty = self.concreteType(blk: {
                    const p_ty = self.unwrapRefType(self.nodeType(pat_id));
                    if (!p_ty.isError()) break :blk p_ty;
                    const i_ty = self.nodeType(iter_id);
                    if (!i_ty.isError()) break :blk i_ty;
                    break :blk .i32_ty;
                });
                const start_hir = try self.lowerExpr(NodeIndex.fromInt(iter_node.lhs.payload), elem_ty);
                const end_hir = try self.lowerExpr(NodeIndex.fromInt(iter_node.rhs.payload), elem_ty);

                const cur_local = try self.allocTempLocal(elem_ty, tok, true);
                const end_local = try self.allocTempLocal(elem_ty, tok, false);
                try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(cur_local, start_hir, tok)).asInt());
                try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(end_local, end_hir, tok)).asInt());

                var loop_stmts: std.ArrayListUnmanaged(u32) = .empty;
                defer loop_stmts.deinit(self.allocator);

                if (!is_inclusive) {
                    // `if !(_cur < _end) { break; }`:
                    const lt_cond = try self.emitSyntheticBinOp(
                        .lt,
                        try self.emitVarRef(cur_local, tok, .none),
                        try self.emitVarRef(end_local, tok, .none),
                        .bool_ty,
                        tok,
                    );
                    const exit_guard = try self.emitLoopBreakIfFalse(lt_cond, loop_id, tok);
                    try loop_stmts.append(self.allocator, exit_guard.asInt());

                    // Capture immutable per-iteration `elem = _cur` BEFORE advancing `_cur = _cur +% 1` (`MAJ-04`):
                    const iter_elem_local = try self.allocTempLocal(elem_ty, tok, false);
                    const iter_elem_decl = try self.emitLocalDeclNode(
                        iter_elem_local,
                        try self.emitVarRef(cur_local, tok, .none),
                        tok,
                    );
                    try loop_stmts.append(self.allocator, iter_elem_decl.asInt());
                    const elem_val = try self.emitVarRef(iter_elem_local, tok, .none);
                    try self.emitPatternBindStmts(pat_id, elem_val, elem_ty, tok, &loop_stmts);

                    const one_const = try self.emitConstVal(.{ .int_val = 1 }, elem_ty, tok, .none, true);
                    const next_val = try self.emitSyntheticBinOp(
                        .wrap_add,
                        try self.emitVarRef(cur_local, tok, .none),
                        one_const,
                        elem_ty,
                        tok,
                    );
                    const adv_assign = try self.emitSyntheticAssign(
                        try self.emitVarRef(cur_local, tok, .none),
                        next_val,
                        tok,
                    );
                    try loop_stmts.append(self.allocator, adv_assign.asInt());
                } else {
                    // `var _is_done: bool = _cur > _end;` prevents `255u8 + 1` wraparound:
                    const init_done = try self.emitSyntheticBinOp(
                        .gt,
                        try self.emitVarRef(cur_local, tok, .none),
                        try self.emitVarRef(end_local, tok, .none),
                        .bool_ty,
                        tok,
                    );
                    const done_local = try self.allocTempLocal(.bool_ty, tok, true);
                    try outer_stmts.append(
                        self.allocator,
                        (try self.emitLocalDeclNode(done_local, init_done, tok)).asInt(),
                    );

                    // `if _is_done { break; }`:
                    const done_break = try self.emitLoopBreakIfTrue(
                        try self.emitVarRef(done_local, tok, .none),
                        loop_id,
                        tok,
                    );
                    try loop_stmts.append(self.allocator, done_break.asInt());

                    // Capture immutable per-iteration `elem = _cur` BEFORE `_is_done / _cur +% 1` step (`MAJ-04`):
                    const iter_elem_local = try self.allocTempLocal(elem_ty, tok, false);
                    const iter_elem_decl = try self.emitLocalDeclNode(
                        iter_elem_local,
                        try self.emitVarRef(cur_local, tok, .none),
                        tok,
                    );
                    try loop_stmts.append(self.allocator, iter_elem_decl.asInt());
                    const elem_val = try self.emitVarRef(iter_elem_local, tok, .none);
                    try self.emitPatternBindStmts(pat_id, elem_val, elem_ty, tok, &loop_stmts);

                    // `if _cur == _end { _is_done = true; } else { _cur = _cur +% 1; }`:
                    const at_end_cond = try self.emitSyntheticBinOp(
                        .eq,
                        try self.emitVarRef(cur_local, tok, .none),
                        try self.emitVarRef(end_local, tok, .none),
                        .bool_ty,
                        tok,
                    );
                    const set_done = try self.emitSyntheticAssign(
                        try self.emitVarRef(done_local, tok, .none),
                        try self.emitConstVal(.{ .bool_val = true }, .bool_ty, tok, .none, true),
                        tok,
                    );
                    const then_blk = try self.wrapSingleStmtBlock(set_done, tok);

                    const one_const = try self.emitConstVal(.{ .int_val = 1 }, elem_ty, tok, .none, true);
                    const next_val = try self.emitSyntheticBinOp(
                        .wrap_add,
                        try self.emitVarRef(cur_local, tok, .none),
                        one_const,
                        elem_ty,
                        tok,
                    );
                    const inc_cur = try self.emitSyntheticAssign(
                        try self.emitVarRef(cur_local, tok, .none),
                        next_val,
                        tok,
                    );
                    const else_blk = try self.wrapSingleStmtBlock(inc_cur, tok);

                    const step_if_extra = try self.store.appendExtraSlice(&[2]u32{
                        then_blk.asInt(),
                        else_blk.asInt(),
                    });
                    const step_if = try self.emitNode(.{
                        .tag = .hir_if,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = at_end_cond.asInt(), .rhs = step_if_extra },
                    }, .none);
                    try loop_stmts.append(self.allocator, step_if.asInt());
                }

                const user_body = try self.lowerBlockExpr(body_id, .unit_ty, false);
                try loop_stmts.append(self.allocator, user_body.asInt());

                const loop_blk = try self.emitSyntheticBlock(loop_stmts.items, .none, .unit_ty, tok);
                const loop_node = try self.emitNode(.{
                    .tag = .hir_loop,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = loop_blk.asInt(), .rhs = loop_id },
                }, stmt_id);
                try outer_stmts.append(self.allocator, loop_node.asInt());
                return self.emitSyntheticBlock(outer_stmts.items, .none, .unit_ty, tok);
            }
        }

        // [2] Zero-temporary `soa_zip(s0, s1, …)` (`DR-13` §2.2 Rule 5):
        if (iter_node.tag == .call_expr and iter_node.lhs.tag == .node) {
            const callee_id = NodeIndex.fromInt(iter_node.lhs.payload);
            const callee_node = self.ast_arena.getNode(callee_id);
            if (callee_node.tag == .ident_expr) {
                const callee_name = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.tokens,
                    callee_node.main_token,
                );
                if (std.mem.eql(u8, callee_name, "soa_zip")) {
                    return self.lowerSoaZipLoop(stmt_id, pat_id, iter_id, body_id, loop_id, &outer_stmts);
                }
            }
        }

        // [3] Standard slice, fixed array, or `#soa` sequence iteration:
        const seq_hir = try self.lowerExpr(iter_id, .err_ty);
        const seq_ty = self.store.getNode(seq_hir).type_id;
        const unwrapped_seq_ty = self.unwrapRefType(seq_ty);
        const seq_ty_node = self.pool.getNode(unwrapped_seq_ty);
        const elem_ty: TypeId = switch (seq_ty_node.tag) {
            .slice_ty, .soa_slice_ty, .array_ty, .soa_array_ty => TypeId.fromInt(seq_ty_node.lhs),
            else => .unit_ty,
        };

        const seq_local = try self.allocTempLocal(seq_ty, tok, false);
        try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(seq_local, seq_hir, tok)).asInt());

        const len_hir = try self.emitSequenceLen(try self.emitVarRef(seq_local, tok, .none), seq_ty, tok);
        const len_local = try self.allocTempLocal(.usize_ty, tok, false);
        try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(len_local, len_hir, tok)).asInt());

        const idx_local = try self.allocTempLocal(.usize_ty, tok, true);
        const zero_usize = try self.emitConstVal(.{ .int_val = 0 }, .usize_ty, tok, .none, true);
        try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_local, zero_usize, tok)).asInt());

        var loop_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer loop_stmts.deinit(self.allocator);

        const lt_cond = try self.emitSyntheticBinOp(
            .lt,
            try self.emitVarRef(idx_local, tok, .none),
            try self.emitVarRef(len_local, tok, .none),
            .bool_ty,
            tok,
        );
        try loop_stmts.append(self.allocator, (try self.emitLoopBreakIfFalse(lt_cond, loop_id, tok)).asInt());

        const cur_idx_local = try self.allocTempLocal(.usize_ty, tok, false);
        try loop_stmts.append(
            self.allocator,
            (try self.emitLocalDeclNode(cur_idx_local, try self.emitVarRef(idx_local, tok, .none), tok)).asInt(),
        );

        const one_usize = try self.emitConstVal(.{ .int_val = 1 }, .usize_ty, tok, .none, true);
        const inc_idx = try self.emitSyntheticBinOp(
            .wrap_add,
            try self.emitVarRef(idx_local, tok, .none),
            one_usize,
            .usize_ty,
            tok,
        );
        try loop_stmts.append(
            self.allocator,
            (try self.emitSyntheticAssign(try self.emitVarRef(idx_local, tok, .none), inc_idx, tok)).asInt(),
        );

        const seq_base = if (seq_ty != unwrapped_seq_ty)
            try self.emitSyntheticDeref(try self.emitVarRef(seq_local, tok, .none), unwrapped_seq_ty, tok)
        else
            try self.emitVarRef(seq_local, tok, .none);
        const is_elem_mut = self.pool.getTag(seq_ty) == .mut_ref_ty or
            ((seq_ty_node.tag == .slice_ty or seq_ty_node.tag == .soa_slice_ty) and seq_ty_node.rhs != 0) or
            self.store.getNode(seq_hir).flags.category == .place_mut;
        const elem_proj = try self.emitNode(.{
            .tag = .hir_index_proj,
            .flags = .{ .category = if (is_elem_mut) .place_mut else .place_imm, .is_synthetic = true },
            .type_id = self.concreteType(elem_ty),
            .origin_token = tok,
            .data = .{
                .lhs = seq_base.asInt(),
                .rhs = (try self.emitVarRef(cur_idx_local, tok, .none)).asInt(),
            },
        }, .none);
        try self.emitPatternBindStmts(pat_id, elem_proj, elem_ty, tok, &loop_stmts);

        const user_body = try self.lowerBlockExpr(body_id, .unit_ty, false);
        try loop_stmts.append(self.allocator, user_body.asInt());

        const loop_blk = try self.emitSyntheticBlock(loop_stmts.items, .none, .unit_ty, tok);
        const loop_node = try self.emitNode(.{
            .tag = .hir_loop,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = loop_blk.asInt(), .rhs = loop_id },
        }, stmt_id);
        try outer_stmts.append(self.allocator, loop_node.asInt());
        return self.emitSyntheticBlock(outer_stmts.items, .none, .unit_ty, tok);
    }

    /// Lowers `for pat in soa_zip(s0, s1, …) { body }` without allocating an intermediate AoS tuple on stack.
    fn lowerSoaZipLoop(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        pat_id: NodeIndex,
        iter_id: NodeIndex,
        body_id: NodeIndex,
        loop_id: u32,
        outer_stmts: *std.ArrayListUnmanaged(u32),
    ) !HirIndex {
        const tok = self.ast_arena.getNode(stmt_id).main_token;
        const raw_args = self.getAstExtraSlice(iter_id, true);
        const arg_labels = try self.allocator.alloc(SymbolId, raw_args.len);
        defer if (arg_labels.len > 0) self.allocator.free(arg_labels);
        @memset(arg_labels, .empty);
        try self.extractCallArgLabels(iter_id, arg_labels);

        var seq_locals_list: std.ArrayListUnmanaged(u32) = .empty;
        defer seq_locals_list.deinit(self.allocator);
        var seq_types_list: std.ArrayListUnmanaged(TypeId) = .empty;
        defer seq_types_list.deinit(self.allocator);
        var seq_labels_list: std.ArrayListUnmanaged(SymbolId) = .empty;
        defer seq_labels_list.deinit(self.allocator);

        for (raw_args, 0..) |raw_arg, raw_i| {
            var arg_id = NodeIndex.fromInt(raw_arg);
            if (arg_id.asInt() >= self.ast_arena.countNodes()) continue;
            const arg_ast = self.ast_arena.getNode(arg_id);
            if (isTypeAstTag(arg_ast.tag)) continue;

            var item_label: SymbolId = if (raw_i < arg_labels.len) arg_labels[raw_i] else .empty;
            if (arg_ast.tag == .binary_expr and !arg_ast.main_token.isNone() and
                self.tokens.getToken(arg_ast.main_token).kind == .eq and
                arg_ast.lhs.tag == .node and arg_ast.rhs.tag == .node)
            {
                const lhs_ast = self.ast_arena.getNode(NodeIndex.fromInt(arg_ast.lhs.payload));
                if (lhs_ast.tag == .ident_expr and !lhs_ast.main_token.isNone()) {
                    const lbl_text = symbol_resolver.extractTokenSlice(self.source, self.tokens, lhs_ast.main_token);
                    item_label = try self.interner.intern(lbl_text);
                    arg_id = NodeIndex.fromInt(arg_ast.rhs.payload);
                }
            }

            const seq_hir = try self.lowerExpr(arg_id, .err_ty);
            const seq_ty = self.store.getNode(seq_hir).type_id;
            const is_seq_mut = self.store.getNode(seq_hir).flags.category == .place_mut;
            const seq_slot = try self.allocTempLocal(seq_ty, tok, is_seq_mut);
            try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(seq_slot, seq_hir, tok)).asInt());
            try seq_locals_list.append(self.allocator, seq_slot);
            try seq_types_list.append(self.allocator, seq_ty);
            try seq_labels_list.append(self.allocator, item_label);
        }

        if (seq_locals_list.items.len == 0) return self.emitUnitConst(tok, stmt_id);

        const arena_alloc = self.zip_arena.allocator();
        var zip_info: VirtualZipBinding = .{
            .seq_locals = try arena_alloc.dupe(u32, seq_locals_list.items),
            .seq_types = try arena_alloc.dupe(TypeId, seq_types_list.items),
            .seq_labels = try arena_alloc.dupe(SymbolId, seq_labels_list.items),
        };

        const first_len = try self.emitSequenceLen(
            try self.emitVarRef(zip_info.seq_locals[0], tok, .none),
            zip_info.seq_types[0],
            tok,
        );
        const len_local = try self.allocTempLocal(.usize_ty, tok, false);
        try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(len_local, first_len, tok)).asInt());

        const idx_local = try self.allocTempLocal(.usize_ty, tok, true);
        const zero_usize = try self.emitConstVal(.{ .int_val = 0 }, .usize_ty, tok, .none, true);
        try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_local, zero_usize, tok)).asInt());

        var loop_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer loop_stmts.deinit(self.allocator);

        const lt_cond = try self.emitSyntheticBinOp(
            .lt,
            try self.emitVarRef(idx_local, tok, .none),
            try self.emitVarRef(len_local, tok, .none),
            .bool_ty,
            tok,
        );
        try loop_stmts.append(self.allocator, (try self.emitLoopBreakIfFalse(lt_cond, loop_id, tok)).asInt());

        const cur_idx_local = try self.allocTempLocal(.usize_ty, tok, false);
        try loop_stmts.append(
            self.allocator,
            (try self.emitLocalDeclNode(cur_idx_local, try self.emitVarRef(idx_local, tok, .none), tok)).asInt(),
        );
        zip_info.idx_local = cur_idx_local;

        const one_usize = try self.emitConstVal(.{ .int_val = 1 }, .usize_ty, tok, .none, true);
        const inc_idx = try self.emitSyntheticBinOp(
            .wrap_add,
            try self.emitVarRef(idx_local, tok, .none),
            one_usize,
            .usize_ty,
            tok,
        );
        try loop_stmts.append(
            self.allocator,
            (try self.emitSyntheticAssign(try self.emitVarRef(idx_local, tok, .none), inc_idx, tok)).asInt(),
        );

        if (!pat_id.isNone()) {
            const pat_tag = self.ast_arena.getNode(pat_id).tag;
            if (pat_tag == .bind_pat) {
                try self.pushZipBinding(self.extractBindPatNameId(pat_id), zip_info);
            } else if (pat_tag == .tuple_pat) {
                const sub_pats = self.getAstExtraSlice(pat_id, false);
                const count = @min(sub_pats.len, zip_info.seq_locals.len);
                for (sub_pats[0..count], 0..) |raw_sub, i| {
                    const seq_ty = zip_info.seq_types[i];
                    const unwrapped = self.unwrapRefType(seq_ty);
                    const seq_ty_node = self.pool.getNode(unwrapped);
                    const elem_ty = TypeId.fromInt(seq_ty_node.lhs);
                    const is_elem_mut = self.pool.getTag(seq_ty) == .mut_ref_ty or
                        ((seq_ty_node.tag == .slice_ty or seq_ty_node.tag == .soa_slice_ty) and seq_ty_node.rhs != 0) or
                        self.store.locals.items[zip_info.seq_locals[i]].is_mut;
                    const seq_base = if (seq_ty != unwrapped)
                        try self.emitSyntheticDeref(
                            try self.emitVarRef(zip_info.seq_locals[i], tok, .none),
                            unwrapped,
                            tok,
                        )
                    else
                        try self.emitVarRef(zip_info.seq_locals[i], tok, .none);
                    const elem_proj = try self.emitNode(.{
                        .tag = .hir_index_proj,
                        .flags = .{ .category = if (is_elem_mut) .place_mut else .place_imm, .is_synthetic = true },
                        .type_id = self.concreteType(elem_ty),
                        .origin_token = tok,
                        .data = .{
                            .lhs = seq_base.asInt(),
                            .rhs = (try self.emitVarRef(cur_idx_local, tok, .none)).asInt(),
                        },
                    }, .none);
                    try self.emitPatternBindStmts(NodeIndex.fromInt(raw_sub), elem_proj, elem_ty, tok, &loop_stmts);
                }
            }
        }

        const user_body = try self.lowerBlockExpr(body_id, .unit_ty, false);
        try loop_stmts.append(self.allocator, user_body.asInt());
        const loop_blk = try self.emitSyntheticBlock(loop_stmts.items, .none, .unit_ty, tok);
        const loop_node = try self.emitNode(.{
            .tag = .hir_loop,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = loop_blk.asInt(), .rhs = loop_id },
        }, stmt_id);
        try outer_stmts.append(self.allocator, loop_node.asInt());
        return self.emitSyntheticBlock(outer_stmts.items, .none, .unit_ty, tok);
    }

    /// Lowers `while cond { body }` and `while let pat = expr { body }` into canonical `hir_loop`.
    fn lowerWhileStmt(self: *HirLowerer, stmt_id: NodeIndex) anyerror!HirIndex {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const tok = stmt_node.main_token;
        const cond_id = if (stmt_node.lhs.tag == .node) NodeIndex.fromInt(stmt_node.lhs.payload) else .none;
        const body_id = if (stmt_node.rhs.tag == .node) NodeIndex.fromInt(stmt_node.rhs.payload) else .none;

        const loop_id = self.next_loop_id;
        self.next_loop_id += 1;
        const saved_loop_id = self.current_loop_id;
        const saved_in_ct_for = self.is_in_comptime_for;
        self.current_loop_id = loop_id;
        self.is_in_comptime_for = false;
        const local_checkpoint = self.local_shadow_log.items.len;
        defer {
            self.popLexicalLocalsTo(local_checkpoint);
            self.is_in_comptime_for = saved_in_ct_for;
            self.current_loop_id = saved_loop_id;
        }

        const brk_node = try self.emitNode(.{
            .tag = .hir_break,
            .flags = .{ .category = .diverging, .is_synthetic = true },
            .type_id = .never_ty,
            .origin_token = tok,
            .data = .{ .lhs = loop_id, .rhs = NONE_U32 },
        }, .none);
        const brk_blk = try self.wrapSingleStmtBlock(brk_node, tok);

        const step_hir = try self.lowerConditionBranch(
            cond_id,
            self.ast_arena.getCstOrigin(stmt_id),
            body_id,
            .none,
            brk_blk,
            .unit_ty,
            tok,
            stmt_id,
        );
        const loop_blk = try self.wrapSingleStmtBlock(step_hir, tok);
        return self.emitNode(.{
            .tag = .hir_loop,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = loop_blk.asInt(), .rhs = loop_id },
        }, stmt_id);
    }

    /// Lowers `lhs = rhs;` and compound assignments (`+=`, `-=`, etc.), synthesizing `hir_bitfield_rmw` on `bit_field`s.
    fn lowerAssignStmt(self: *HirLowerer, stmt_id: NodeIndex) anyerror!HirIndex {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const tok = stmt_node.main_token;
        const lhs_id = if (stmt_node.lhs.tag == .node) NodeIndex.fromInt(stmt_node.lhs.payload) else .none;
        const rhs_id = if (stmt_node.rhs.tag == .node) NodeIndex.fromInt(stmt_node.rhs.payload) else .none;

        const op_kind = if (!tok.isNone() and tok.asInt() < self.tokens.countTokens())
            self.tokens.getToken(tok).kind
        else
            TokenKind.eq;

        // [1] Direct `=` assignment:
        if (op_kind == .eq) {
            const lhs_hir = try self.lowerExpr(lhs_id, .err_ty);
            const lhs_node = self.store.getNode(lhs_hir);
            const rhs_hir = try self.lowerExpr(rhs_id, lhs_node.type_id);
            if (lhs_node.tag == .hir_bitfield_read) {
                const rmw_extra = try self.store.appendExtraSlice(&[2]u32{ lhs_node.data.rhs, rhs_hir.asInt() });
                self.store.nodes.set(lhs_hir.asInt(), .{
                    .tag = .hir_bitfield_rmw,
                    .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                    .type_id = .unit_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = lhs_node.data.lhs, .rhs = rmw_extra },
                });
                self.store.origin_ast.items[lhs_hir.asInt()] = stmt_id;
                return lhs_hir;
            }
            return self.emitNode(.{
                .tag = .hir_assign,
                .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
                .type_id = .unit_ty,
                .origin_token = tok,
                .data = .{ .lhs = lhs_hir.asInt(), .rhs = rhs_hir.asInt() },
            }, stmt_id);
        }

        // [2] Compound assignment (`+=`, `-=`, etc.): evaluate `rhs` BEFORE `&mut lhs` (`DR-02` §2.2 & `MAJ-02`):
        const bin_op: HirBinaryOp = switch (op_kind) {
            .plus_eq => .add,
            .minus_eq => .sub,
            .star_eq => .mul,
            .slash_eq => .div,
            .percent_eq => .rem,
            .amp_eq => .bit_and,
            .pipe_eq => .bit_or,
            .caret_eq => .bit_xor,
            .shl_eq => .shl,
            .shr_eq => .shr,
            else => .add,
        };

        const expected_rhs_ty = self.nodeType(lhs_id);
        const raw_rhs_hir = try self.lowerExpr(rhs_id, expected_rhs_ty);
        const rhs_local = try self.allocTempLocal(self.store.getNode(raw_rhs_hir).type_id, tok, false);
        const decl_rhs = try self.emitLocalDeclNode(rhs_local, raw_rhs_hir, tok);

        const lhs_hir = try self.lowerExpr(lhs_id, .err_ty);
        const lhs_node = self.store.getNode(lhs_hir);
        const rhs_ref = try self.applyImplicitCoercionIfNeeded(
            try self.emitVarRef(rhs_local, tok, .none),
            lhs_node.type_id,
            tok,
        );

        if (lhs_node.tag == .hir_bitfield_read) {
            const base_hir = HirIndex.fromInt(lhs_node.data.lhs);
            const base_node = self.store.getNode(base_hir);
            if (base_node.tag == .hir_var_ref) {
                const updated_val = try self.emitSyntheticBinOp(bin_op, lhs_hir, rhs_ref, lhs_node.type_id, tok);
                const rmw_extra = try self.store.appendExtraSlice(&[2]u32{
                    lhs_node.data.rhs,
                    updated_val.asInt(),
                });
                const rmw_hir = try self.emitNode(.{
                    .tag = .hir_bitfield_rmw,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = base_hir.asInt(), .rhs = rmw_extra },
                }, stmt_id);
                return self.emitSyntheticBlock(&[2]u32{ decl_rhs.asInt(), rmw_hir.asInt() }, .none, .unit_ty, tok);
            }
            const ptr_ty = try self.pool.internRef(base_node.type_id, true);
            const addr_hir = try self.emitSyntheticAddrOf(base_hir, ptr_ty, true, tok);
            const ptr_local = try self.allocTempLocal(ptr_ty, tok, false);
            const decl_ptr = try self.emitLocalDeclNode(ptr_local, addr_hir, tok);
            const deref_read_base = try self.emitSyntheticDeref(
                try self.emitVarRef(ptr_local, tok, .none),
                base_node.type_id,
                tok,
            );
            const bf_read = try self.emitNode(.{
                .tag = .hir_bitfield_read,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = lhs_node.type_id,
                .origin_token = tok,
                .data = .{ .lhs = deref_read_base.asInt(), .rhs = lhs_node.data.rhs },
            }, .none);
            const updated_val = try self.emitSyntheticBinOp(bin_op, bf_read, rhs_ref, lhs_node.type_id, tok);
            const deref_write_base = try self.emitNode(.{
                .tag = .hir_unary_op,
                .flags = .{ .category = .place_mut, .is_synthetic = true },
                .type_id = base_node.type_id,
                .origin_token = tok,
                .data = .{
                    .lhs = @backingInt(HirUnaryOp.deref),
                    .rhs = (try self.emitVarRef(ptr_local, tok, .none)).asInt(),
                },
            }, .none);
            const rmw_extra = try self.store.appendExtraSlice(&[2]u32{ lhs_node.data.rhs, updated_val.asInt() });
            const rmw_hir = try self.emitNode(.{
                .tag = .hir_bitfield_rmw,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = .unit_ty,
                .origin_token = tok,
                .data = .{ .lhs = deref_write_base.asInt(), .rhs = rmw_extra },
            }, stmt_id);
            return self.emitSyntheticBlock(
                &[3]u32{ decl_rhs.asInt(), decl_ptr.asInt(), rmw_hir.asInt() },
                .none,
                .unit_ty,
                tok,
            );
        }

        if (lhs_node.tag == .hir_var_ref) {
            const read_ref = try self.emitVarRef(lhs_node.data.lhs, tok, .none);
            const updated_val = try self.emitSyntheticBinOp(bin_op, read_ref, rhs_ref, lhs_node.type_id, tok);
            const assign_hir = try self.emitSyntheticAssign(lhs_hir, updated_val, tok);
            return self.emitSyntheticBlock(&[2]u32{ decl_rhs.asInt(), assign_hir.asInt() }, .none, .unit_ty, tok);
        }

        const ptr_ty = try self.pool.internRef(lhs_node.type_id, true);
        const addr_hir = try self.emitSyntheticAddrOf(lhs_hir, ptr_ty, true, tok);
        const ptr_local = try self.allocTempLocal(ptr_ty, tok, false);
        const decl_ptr = try self.emitLocalDeclNode(ptr_local, addr_hir, tok);
        const deref_read = try self.emitSyntheticDeref(
            try self.emitVarRef(ptr_local, tok, .none),
            lhs_node.type_id,
            tok,
        );
        const updated_val = try self.emitSyntheticBinOp(bin_op, deref_read, rhs_ref, lhs_node.type_id, tok);
        const deref_write = try self.emitNode(.{
            .tag = .hir_unary_op,
            .flags = .{ .category = .place_mut, .is_synthetic = true },
            .type_id = lhs_node.type_id,
            .origin_token = tok,
            .data = .{
                .lhs = @backingInt(HirUnaryOp.deref),
                .rhs = (try self.emitVarRef(ptr_local, tok, .none)).asInt(),
            },
        }, .none);
        const assign_hir = try self.emitSyntheticAssign(deref_write, updated_val, tok);
        return self.emitSyntheticBlock(
            &[3]u32{ decl_rhs.asInt(), decl_ptr.asInt(), assign_hir.asInt() },
            .none,
            .unit_ty,
            tok,
        );
    }

    /// Emits a synthetic `hir_local_decl` node initializing `local_id` with `init_hir`.
    fn emitLocalDeclNode(
        self: *HirLowerer,
        local_id: u32,
        init_hir: HirIndex,
        tok: TokenIndex,
    ) !HirIndex {
        return self.emitNode(.{
            .tag = .hir_local_decl,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = local_id, .rhs = init_hir.asInt() },
        }, .none);
    }

    /// Emits a synthetic `hir_assign` node.
    fn emitSyntheticAssign(
        self: *HirLowerer,
        dest_hir: HirIndex,
        val_hir: HirIndex,
        tok: TokenIndex,
    ) !HirIndex {
        return self.emitNode(.{
            .tag = .hir_assign,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = dest_hir.asInt(), .rhs = val_hir.asInt() },
        }, .none);
    }

    /// Emits a synthetic `hir_block` over `stmt_ids` and `tail_hir`.
    fn emitSyntheticBlock(
        self: *HirLowerer,
        stmt_ids: []const u32,
        tail_hir: HirIndex,
        block_ty: TypeId,
        tok: TokenIndex,
    ) !HirIndex {
        const extra_idx = try self.store.appendLenPrefixedExtra(stmt_ids);
        return self.emitNode(.{
            .tag = .hir_block,
            .flags = .{
                .category = if (block_ty == .never_ty) .diverging else .rvalue,
                .is_synthetic = true,
            },
            .type_id = self.concreteType(block_ty),
            .origin_token = tok,
            .data = .{ .lhs = extra_idx, .rhs = tail_hir.asInt() },
        }, .none);
    }

    /// Wraps a single statement `HirIndex` in a synthetic `hir_block`.
    fn wrapSingleStmtBlock(self: *HirLowerer, stmt_hir: HirIndex, tok: TokenIndex) !HirIndex {
        const stmt_ty = self.store.getNode(stmt_hir).type_id;
        return self.emitSyntheticBlock(
            &[1]u32{stmt_hir.asInt()},
            .none,
            if (stmt_ty == .never_ty) .never_ty else .unit_ty,
            tok,
        );
    }

    /// Emits `if cond { break; }` for loop exit guards.
    fn emitLoopBreakIfTrue(
        self: *HirLowerer,
        cond_hir: HirIndex,
        loop_id: u32,
        tok: TokenIndex,
    ) !HirIndex {
        const brk_node = try self.emitNode(.{
            .tag = .hir_break,
            .flags = .{ .category = .diverging, .is_synthetic = true },
            .type_id = .never_ty,
            .origin_token = tok,
            .data = .{ .lhs = loop_id, .rhs = NONE_U32 },
        }, .none);
        const then_blk = try self.wrapSingleStmtBlock(brk_node, tok);
        const extra_idx = try self.store.appendExtraSlice(&[2]u32{ then_blk.asInt(), NONE_U32 });
        return self.emitNode(.{
            .tag = .hir_if,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = cond_hir.asInt(), .rhs = extra_idx },
        }, .none);
    }

    /// Emits `if !cond { break; }` for loop continuation guards.
    fn emitLoopBreakIfFalse(
        self: *HirLowerer,
        cond_hir: HirIndex,
        loop_id: u32,
        tok: TokenIndex,
    ) !HirIndex {
        const not_cond = try self.emitNode(.{
            .tag = .hir_unary_op,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .bool_ty,
            .origin_token = tok,
            .data = .{ .lhs = @backingInt(HirUnaryOp.logical_not), .rhs = cond_hir.asInt() },
        }, .none);
        return self.emitLoopBreakIfTrue(not_cond, loop_id, tok);
    }

    /// Emits `.len` (`usize`) for an array, `#soa` array, slice, `#soa` slice, or `str`.
    fn emitSequenceLen(
        self: *HirLowerer,
        seq_hir: HirIndex,
        seq_ty: TypeId,
        tok: TokenIndex,
    ) !HirIndex {
        const unwrapped = self.unwrapRefType(seq_ty);
        const ty_node = self.pool.getNode(unwrapped);
        if (ty_node.tag == .array_ty or ty_node.tag == .soa_array_ty) {
            if ((ty_node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) != 0) {
                const const_sym = SymbolId.fromInt(ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG);
                switch (self.sym_table.lookupLexical(self.current_scope, const_sym, NamespaceMask.ALL)) {
                    .found => |found_idx| {
                        const sym = self.sym_table.getSymbol(found_idx).*;
                        return self.emitNode(.{
                            .tag = .hir_global_ref,
                            .flags = .{ .category = .rvalue, .is_synthetic = true },
                            .type_id = .usize_ty,
                            .origin_token = tok,
                            .data = .{ .lhs = sym.def_id.asInt(), .rhs = found_idx.asInt() },
                        }, .none);
                    },
                    else => {},
                }
            }
            const fixed_len = ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
            return self.emitConstVal(.{ .int_val = @as(i128, fixed_len) }, .usize_ty, tok, .none, true);
        }
        const base_hir = if (seq_ty != unwrapped)
            try self.emitSyntheticDeref(seq_hir, unwrapped, tok)
        else
            seq_hir;
        return self.emitNode(.{
            .tag = .hir_field_proj,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .usize_ty,
            .origin_token = tok,
            .data = .{ .lhs = base_hir.asInt(), .rhs = FIELD_ORDINAL_LEN },
        }, .none);
    }

    /// Emits local declaration or pattern-destructuring statements binding `pat_id` to `val_hir`.
    fn emitPatternBindStmts(
        self: *HirLowerer,
        pat_id: NodeIndex,
        val_hir: HirIndex,
        elem_ty: TypeId,
        tok: TokenIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
    ) !void {
        if (pat_id.isNone() or pat_id.asInt() >= self.ast_arena.countNodes()) return;
        const pat_tag = self.ast_arena.getNode(pat_id).tag;
        if (pat_tag == .wildcard_pat) return;
        if (pat_tag == .bind_pat) {
            const pat_cst = self.ast_arena.getCstOrigin(pat_id);
            const is_ref_pat = self.hasKeywordInCst(pat_cst, .kw_ref) or self.hasKeywordInCst(pat_cst, .amp);
            const is_ref_mut = self.hasKeywordInCst(pat_cst, .kw_mut);
            if (is_ref_pat) {
                const ref_ty = try self.pool.internRef(self.concreteType(elem_ty), is_ref_mut);
                const slot_id = try self.bindSimplePatternLocal(pat_id, ref_ty, false);
                const addr_hir = try self.emitSyntheticAddrOf(val_hir, ref_ty, is_ref_mut, tok);
                const decl_hir = try self.emitLocalDeclNode(slot_id, addr_hir, tok);
                try out_stmts.append(self.allocator, decl_hir.asInt());
                return;
            }
            const slot_id = try self.bindSimplePatternLocal(pat_id, elem_ty, false);
            const decl_hir = try self.emitLocalDeclNode(slot_id, val_hir, tok);
            try out_stmts.append(self.allocator, decl_hir.asInt());
            return;
        }
        const lowered_pat = try self.lowerTopPattern(pat_id, elem_ty, false);
        const arm_start: u32 = @intCast(self.store.match_arms.items.len);
        try self.store.match_arms.append(self.allocator, .{
            .pat_idx = lowered_pat,
            .guard_hir = .none,
            .body_hir = try self.emitUnitConst(tok, .none),
            .origin_token = tok,
        });
        const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, 1 });
        const match_hir = try self.emitNode(.{
            .tag = .hir_match,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = val_hir.asInt(), .rhs = match_extra },
        }, pat_id);
        try out_stmts.append(self.allocator, match_hir.asInt());
    }

    // -------------- Expression & Projection Lowering --------------

    /// Lowers an AST expression node (`expr_id`) into canonical concrete `HIR`.
    fn lowerExpr(self: *HirLowerer, expr_id: NodeIndex, expected_ty: TypeId) anyerror!HirIndex {
        if (expr_id.isNone() or expr_id.asInt() >= self.ast_arena.countNodes()) {
            return self.emitUnitConst(TokenIndex.fromInt(0), .none);
        }
        const ast_node = self.ast_arena.getNode(expr_id);
        if (!try self.enterDepth(expr_id)) {
            return self.emitErrorHole(ast_node.main_token, expr_id, expected_ty);
        }
        defer self.leaveDepth();

        const recorded_ty = self.nodeType(expr_id);
        const target_ty = if (!recorded_ty.isError())
            recorded_ty
        else if (!expected_ty.isError())
            self.concreteType(expected_ty)
        else
            .err_ty;

        const raw_hir: HirIndex = switch (ast_node.tag) {
            .expr_hole, .type_hole, .item_hole, .stmt_hole, .pattern_hole, .incomplete_member_access => {
                return self.emitErrorHole(ast_node.main_token, expr_id, target_ty);
            },
            .bool_lit => blk: {
                const is_true = !ast_node.main_token.isNone() and
                    self.tokens.getToken(ast_node.main_token).kind == .kw_true;
                break :blk try self.emitConstVal(
                    .{ .bool_val = is_true },
                    .bool_ty,
                    ast_node.main_token,
                    expr_id,
                    false,
                );
            },
            .int_lit => blk: {
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, ast_node.main_token);
                const parsed_int = extractIntValue(lexeme) orelse 0;
                const int_ty = if (!target_ty.isError()) target_ty else .i32_ty;
                break :blk try self.emitConstVal(
                    .{ .int_val = parsed_int },
                    int_ty,
                    ast_node.main_token,
                    expr_id,
                    false,
                );
            },
            .float_lit => blk: {
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, ast_node.main_token);
                const parsed_flt = extractFloatValue(lexeme) orelse 0.0;
                const flt_ty = if (!target_ty.isError() and target_ty.isFloatPrimitive()) target_ty else .f64_ty;
                break :blk try self.emitConstVal(
                    .{ .float_val = parsed_flt },
                    flt_ty,
                    ast_node.main_token,
                    expr_id,
                    false,
                );
            },
            .char_lit => blk: {
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, ast_node.main_token);
                const codepoint = extractCharValue(lexeme);
                break :blk try self.emitConstVal(
                    .{ .char_val = codepoint },
                    .char_ty,
                    ast_node.main_token,
                    expr_id,
                    false,
                );
            },
            .string_lit => try self.lowerStringLitOrInterp(expr_id),
            .self_val, .ident_expr, .path_expr => try self.lowerIdentOrPathExpr(expr_id, target_ty),
            .contextual_variant => try self.lowerContextualVariant(expr_id, target_ty),
            .tuple_lit => try self.lowerTupleLit(expr_id, target_ty),
            .array_lit => try self.lowerArrayLit(expr_id, target_ty),
            .struct_lit => try self.lowerStructLit(expr_id, target_ty),
            .unary_expr => try self.lowerUnaryExpr(expr_id, target_ty),
            .cast_expr => try self.lowerCastExpr(expr_id, target_ty),
            .pipe_expr => try self.lowerPipeExpr(expr_id, target_ty),
            .try_expr => try self.lowerTryExpr(expr_id, target_ty),
            .binary_expr => try self.lowerBinaryOrCatchExpr(expr_id, target_ty),
            .field_access => try self.lowerFieldAccess(expr_id, target_ty),
            .index_expr => try self.lowerIndexExpr(expr_id, target_ty),
            .call_expr, .generic_call, .incomplete_call => try self.lowerCallExpr(expr_id, target_ty),
            .method_call => try self.lowerMethodCallExpr(expr_id, target_ty),
            .block => try self.lowerBlockExpr(expr_id, target_ty, false),
            .if_expr => try self.lowerIfExpr(expr_id, target_ty, false),
            .match_expr => try self.lowerMatchExpr(expr_id, target_ty, false),
            .loop_expr => try self.lowerLoopExpr(expr_id, target_ty),
            .closure_expr => try self.lowerClosureExpr(expr_id, target_ty),
            .await_expr => if (ast_node.lhs.tag == .node)
                try self.lowerExpr(NodeIndex.fromInt(ast_node.lhs.payload), target_ty)
            else
                try self.emitErrorHole(ast_node.main_token, expr_id, target_ty),
            else => try self.emitErrorHole(ast_node.main_token, expr_id, target_ty),
        };

        return self.applyImplicitCoercionIfNeeded(raw_hir, expected_ty, ast_node.main_token);
    }

    /// Inserts an explicit `hir_cast` node when `expected_ty` requires mutability relaxation or borrowed slice coercion.
    fn applyImplicitCoercionIfNeeded(
        self: *HirLowerer,
        hir_id: HirIndex,
        expected_ty: TypeId,
        tok: TokenIndex,
    ) !HirIndex {
        if (hir_id.isNone() or expected_ty.isError()) return hir_id;
        const concrete_exp = self.concreteType(expected_ty);
        const actual_ty = self.store.getNode(hir_id).type_id;
        if (actual_ty == concrete_exp or actual_ty == .never_ty or actual_ty.isError()) return hir_id;

        const act_node = self.pool.getNode(actual_ty);
        const exp_node = self.pool.getNode(concrete_exp);

        if (act_node.tag == .mut_ref_ty and exp_node.tag == .ref_ty and act_node.lhs == exp_node.lhs) {
            return self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = concrete_exp,
                .origin_token = tok,
                .data = .{ .lhs = hir_id.asInt(), .rhs = @backingInt(HirCastKind.ref_coerce) },
            }, .none);
        }
        if (act_node.tag == .ref_ty or act_node.tag == .mut_ref_ty) {
            const inner_tag = self.pool.getTag(TypeId.fromInt(act_node.lhs));
            const is_arr_inner = inner_tag == .array_ty or inner_tag == .soa_array_ty;
            const is_slice_exp = exp_node.tag == .slice_ty or exp_node.tag == .soa_slice_ty or
                ((exp_node.tag == .ref_ty or exp_node.tag == .mut_ref_ty) and
                    (self.pool.getTag(TypeId.fromInt(exp_node.lhs)) == .slice_ty or
                        self.pool.getTag(TypeId.fromInt(exp_node.lhs)) == .soa_slice_ty));
            if (is_arr_inner and is_slice_exp) {
                return self.emitNode(.{
                    .tag = .hir_cast,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = concrete_exp,
                    .origin_token = tok,
                    .data = .{ .lhs = hir_id.asInt(), .rhs = @backingInt(HirCastKind.array_to_slice) },
                }, .none);
            }
        }
        if (self.pool.unwrapRefinementBase(actual_ty) == self.pool.unwrapRefinementBase(concrete_exp)) {
            return self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = concrete_exp,
                .origin_token = tok,
                .data = .{ .lhs = hir_id.asInt(), .rhs = @backingInt(HirCastKind.noop) },
            }, .none);
        }
        return hir_id;
    }

    /// Lowers `.string_lit` and raw `r"…"` literals, expanding `"{expr}"` interpolations (`DR-13` §2.2 Rule 5).
    fn lowerStringLitOrInterp(self: *HirLowerer, expr_id: NodeIndex) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const raw_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, ast_node.main_token);

        // Check raw string literal `r"…"` (`MAJ-08`) with verbatim UTF-8 bytes and zero escape processing:
        if (type_system.extractRawStringContent(raw_lex)) |raw_body| {
            const raw_id = try self.interner.intern(raw_body);
            return self.emitConstVal(.{ .str_val = raw_id }, .str_ty, ast_node.main_token, expr_id, false);
        }

        const body_slice = extractQuotedBody(raw_lex);
        if (type_system.scanNextInterpolationSegment(body_slice, 0) == null) {
            const decoded = try type_system.decodeStandardStringSegment(self.allocator, body_slice);
            defer self.allocator.free(decoded);
            const str_id = try self.interner.intern(decoded);
            return self.emitConstVal(.{ .str_val = str_id }, .str_ty, ast_node.main_token, expr_id, false);
        }

        var part_hirs: std.ArrayListUnmanaged(u32) = .empty;
        defer part_hirs.deinit(self.allocator);

        var scan_pos: usize = 0;
        while (type_system.scanNextInterpolationSegment(body_slice, scan_pos)) |seg| {
            if (seg.open_brace > scan_pos) {
                const decoded_lit = try type_system.decodeStandardStringSegment(
                    self.allocator,
                    body_slice[scan_pos..seg.open_brace],
                );
                defer self.allocator.free(decoded_lit);
                if (decoded_lit.len > 0) {
                    const seg_id = try self.interner.intern(decoded_lit);
                    const seg_hir = try self.emitConstVal(
                        .{ .str_val = seg_id },
                        .str_ty,
                        ast_node.main_token,
                        .none,
                        true,
                    );
                    try part_hirs.append(self.allocator, seg_hir.asInt());
                }
            }
            const interp_text = std.mem.trim(u8, body_slice[seg.expr_start..seg.expr_end], " \t\r\n");
            const interp_hir = try self.lowerInterpolatedSegment(interp_text, ast_node.main_token);
            try part_hirs.append(self.allocator, interp_hir.asInt());
            scan_pos = seg.after_close;
        }
        if (scan_pos < body_slice.len) {
            const decoded_tail = try type_system.decodeStandardStringSegment(self.allocator, body_slice[scan_pos..]);
            defer self.allocator.free(decoded_tail);
            if (decoded_tail.len > 0) {
                const tail_id = try self.interner.intern(decoded_tail);
                const tail_hir = try self.emitConstVal(
                    .{ .str_val = tail_id },
                    .str_ty,
                    ast_node.main_token,
                    .none,
                    true,
                );
                try part_hirs.append(self.allocator, tail_hir.asInt());
            }
        }

        const extra_idx = try self.store.appendLenPrefixedExtra(part_hirs.items);
        return self.emitNode(.{
            .tag = .hir_construct,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .str_ty,
            .origin_token = ast_node.main_token,
            .data = .{ .lhs = @backingInt(HirConstructKind.str_interp), .rhs = extra_idx },
        }, expr_id);
    }

    /// Lowers a `{expr}` segment inside an interpolated string literal (`MAJ-08`).
    fn lowerInterpolatedSegment(self: *HirLowerer, segment_src: []const u8, tok: TokenIndex) !HirIndex {
        if (segment_src.len == 0) {
            const empty_id = try self.interner.intern("");
            return self.emitConstVal(.{ .str_val = empty_id }, .str_ty, tok, .none, true);
        }
        if (isPlainMemberChain(segment_src)) {
            var dot_iter = std.mem.splitScalar(u8, segment_src, '.');
            const root_name = std.mem.trim(u8, dot_iter.first(), " \t");
            const root_sym_id = try self.interner.intern(root_name);

            var cur_hir: HirIndex = .none;
            if (self.active_comptime_vals.get(root_sym_id.asInt())) |ct_val| {
                cur_hir = try self.emitConstVal(ct_val, self.inferComptimeValType(ct_val), tok, .none, true);
            } else if (self.active_name_to_local.get(root_sym_id.asInt())) |local_id| {
                cur_hir = try self.emitVarRef(local_id, tok, .none);
            } else {
                switch (self.sym_table.lookupLexical(self.current_scope, root_sym_id, NamespaceMask.ALL)) {
                    .found => |sym_idx| {
                        const sym = self.sym_table.getSymbol(sym_idx).*;
                        cur_hir = try self.emitNode(.{
                            .tag = .hir_global_ref,
                            .flags = .{ .category = .rvalue, .is_synthetic = true },
                            .type_id = self.concreteType(sym.type_id),
                            .origin_token = tok,
                            .data = .{ .lhs = sym.def_id.asInt(), .rhs = sym_idx.asInt() },
                        }, .none);
                    },
                    else => cur_hir = .none,
                }
            }
            if (!cur_hir.isNone()) {
                while (dot_iter.next()) |field_part| {
                    const trimmed_field = std.mem.trim(u8, field_part, " \t");
                    if (trimmed_field.len == 0) break;
                    cur_hir = try self.projectNamedMember(cur_hir, trimmed_field, tok, .none);
                }
                return cur_hir;
            }
        }

        // Sub-parse general `{expr}` (`{a + b}`, `{foo(x)}`, `{arr[0]}`) in the active lexical environment:
        var wrapper_buf: std.ArrayListUnmanaged(u8) = .empty;
        defer wrapper_buf.deinit(self.allocator);
        try wrapper_buf.appendSlice(self.allocator, "fn __cx_interp__() {\n");
        try wrapper_buf.appendSlice(self.allocator, segment_src);
        try wrapper_buf.appendSlice(self.allocator, "\n}\n");

        var sub_tokens = TokenBuffer.init(self.allocator);
        defer sub_tokens.deinit();
        var sub_cst = LosslessCstArena.init(self.allocator);
        defer sub_cst.deinit();
        var sub_ast = AstArena.init(self.allocator);
        defer sub_ast.deinit();
        var sub_diags = DiagnosticSink.init(self.allocator);
        defer sub_diags.deinit();

        _ = parser.parseSource(
            wrapper_buf.items,
            self.store.file_id,
            &sub_tokens,
            &sub_cst,
            &sub_ast,
            &sub_diags,
            self.interner,
        ) catch return self.emitErrorHole(tok, .none, .str_ty);
        if (sub_diags.hasErrors() or sub_ast.countNodes() <= 1) {
            return self.emitErrorHole(tok, .none, .str_ty);
        }

        const sub_extra_ends = try syntax_arenas.computeAstNodeExtraEnds(self.allocator, &sub_ast);
        defer if (sub_extra_ends.len > 0) self.allocator.free(sub_extra_ends);
        const sub_cst_map = try syntax_arenas.computeCstToAstMap(
            self.allocator,
            sub_cst.countNodes(),
            &sub_ast,
        );
        defer if (sub_cst_map.len > 0) self.allocator.free(sub_cst_map);

        const outer_span = if (!tok.isNone() and tok.asInt() < self.tokens.countTokens())
            self.tokens.getTokenSpan(self.store.file_id, tok)
        else
            Span.init(self.store.file_id, 0, 0);

        const saved_source = self.source;
        const saved_tokens = self.tokens;
        const saved_cst = self.cst_arena;
        const saved_ast = self.ast_arena;
        const saved_tables = self.side_tables;
        const saved_extra_ends = self.node_extra_end;
        const saved_cst_map = self.cst_to_ast;
        const saved_ov_tok = self.interp_override_token;
        const saved_ov_span = self.interp_override_span;

        self.source = wrapper_buf.items;
        self.tokens = &sub_tokens;
        self.cst_arena = &sub_cst;
        self.ast_arena = &sub_ast;
        self.side_tables = null;
        self.node_extra_end = sub_extra_ends;
        self.cst_to_ast = sub_cst_map;
        self.interp_override_token = tok;
        self.interp_override_span = outer_span;
        defer {
            self.source = saved_source;
            self.tokens = saved_tokens;
            self.cst_arena = saved_cst;
            self.ast_arena = saved_ast;
            self.side_tables = saved_tables;
            self.node_extra_end = saved_extra_ends;
            self.cst_to_ast = saved_cst_map;
            self.interp_override_token = saved_ov_tok;
            self.interp_override_span = saved_ov_span;
        }

        const root_node = sub_ast.getNode(.root);
        if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
            const root_items = sub_ast.getExtraSlice(
                ExtraIndex.fromInt(root_node.lhs.payload),
                root_node.rhs.payload,
            );
            const fn_node = sub_ast.getNode(NodeIndex.fromInt(root_items[0]));
            if (fn_node.rhs.tag == .node) {
                const block_id = NodeIndex.fromInt(fn_node.rhs.payload);
                const block_node = sub_ast.getNode(block_id);
                if (block_node.rhs.tag == .node) {
                    return self.lowerExpr(NodeIndex.fromInt(block_node.rhs.payload), .err_ty);
                }
                const stmts = self.getAstExtraSlice(block_id, false);
                if (stmts.len == 1) {
                    return self.lowerExpr(NodeIndex.fromInt(stmts[0]), .err_ty);
                }
            }
        }
        return self.emitErrorHole(tok, .none, .str_ty);
    }

    /// Lowers `.self_val`, `.ident_expr`, and `.path_expr` into `hir_const_val`, `hir_var_ref`, `hir_construct`, or `hir_global_ref`.
    fn lowerIdentOrPathExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;

        if (ast_node.tag == .ident_expr or ast_node.tag == .self_val) {
            const lexeme = if (ast_node.tag == .self_val)
                "self"
            else
                symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
            const name_id = if (lexeme.len > 0) try self.interner.intern(lexeme) else SymbolId.empty;

            // [1] Active `comptime for` or block `const` value:
            if (self.active_comptime_vals.get(name_id.asInt())) |ct_val| {
                const resolved_ty = if (!target_ty.isError()) target_ty else self.inferComptimeValType(ct_val);
                return self.emitConstVal(ct_val, resolved_ty, tok, expr_id, true);
            }

            // [2] Active lexical local or parameter slot:
            if (self.active_name_to_local.get(name_id.asInt())) |local_id| {
                return self.emitVarRef(local_id, tok, expr_id);
            }
        }

        var sym_idx = self.nodeSymbol(expr_id);
        if (sym_idx.isNone() and (ast_node.tag == .ident_expr or ast_node.tag == .self_val)) {
            const lexeme = if (ast_node.tag == .self_val)
                "self"
            else
                symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
            if (lexeme.len > 0) {
                const name_id = try self.interner.intern(lexeme);
                switch (self.sym_table.lookupLexical(self.current_scope, name_id, NamespaceMask.ALL)) {
                    .found => |found_idx| sym_idx = found_idx,
                    else => {},
                }
            }
        }

        if (!sym_idx.isNone()) {
            if (self.symbol_to_local.get(sym_idx.asInt())) |mapped_local| {
                return self.emitVarRef(mapped_local, tok, expr_id);
            }
            const sym = self.sym_table.getSymbol(sym_idx).*;
            if (sym.kind == .const_sym) {
                if (try self.evalConstSymbol(sym_idx)) |folded_const| {
                    const const_ty = if (!target_ty.isError()) target_ty else sym.type_id;
                    return self.emitConstVal(folded_const, const_ty, tok, expr_id, true);
                }
            }
            if (sym.kind == .enum_variant_sym and sym.type_id == .unit_ty) {
                const extra_idx = try self.store.appendLenPrefixedExtra(&.{});
                const encoded_lhs: u32 = @as(u32, @backingInt(HirConstructKind.enum_variant)) |
                    (@as(u32, sym.member_ordinal) << 8);
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue },
                    .type_id = if (!target_ty.isError()) target_ty else sym.type_id,
                    .origin_token = tok,
                    .data = .{ .lhs = encoded_lhs, .rhs = extra_idx },
                }, expr_id);
            }
            return self.emitNode(.{
                .tag = .hir_global_ref,
                .flags = .{ .category = .rvalue },
                .type_id = if (!target_ty.isError()) target_ty else self.concreteType(sym.type_id),
                .origin_token = tok,
                .data = .{ .lhs = sym.def_id.asInt(), .rhs = sym_idx.asInt() },
            }, expr_id);
        }

        return self.emitErrorHole(tok, expr_id, target_ty);
    }

    /// Lowers `.None`, `.Some(x)`, `.Ok(x)`, `.Err(e)`, and `.Variant(args)` into `hir_construct`.
    fn lowerContextualVariant(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const expr_node = self.ast_arena.getNode(expr_id);
        const var_tok = if (expr_node.lhs.tag == .token)
            TokenIndex.fromInt(expr_node.lhs.payload)
        else
            expr_node.main_token;
        const var_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, var_tok);
        const arg_nodes = self.getAstExtraSlice(expr_id, true);
        const ty_node = self.pool.getNode(target_ty);

        switch (ty_node.tag) {
            .optional_ty => {
                if (std.mem.eql(u8, var_name, "None")) {
                    const extra_idx = try self.store.appendLenPrefixedExtra(&.{});
                    return self.emitNode(.{
                        .tag = .hir_construct,
                        .flags = .{ .category = .rvalue },
                        .type_id = target_ty,
                        .origin_token = expr_node.main_token,
                        .data = .{ .lhs = @backingInt(HirConstructKind.optional_none), .rhs = extra_idx },
                    }, expr_id);
                }
                const payload_ty = TypeId.fromInt(ty_node.lhs);
                const payload_hir = if (arg_nodes.len >= 1)
                    try self.lowerExpr(NodeIndex.fromInt(arg_nodes[0]), payload_ty)
                else
                    try self.emitUnitConst(expr_node.main_token, .none);
                const extra_idx = try self.store.appendLenPrefixedExtra(&[1]u32{payload_hir.asInt()});
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue },
                    .type_id = target_ty,
                    .origin_token = expr_node.main_token,
                    .data = .{
                        .lhs = @as(u32, @backingInt(HirConstructKind.optional_some)) | (1 << 8),
                        .rhs = extra_idx,
                    },
                }, expr_id);
            },
            .result_ty => {
                const is_ok = std.mem.eql(u8, var_name, "Ok");
                const payload_ty = TypeId.fromInt(if (is_ok) ty_node.lhs else ty_node.rhs);
                const payload_hir = if (arg_nodes.len >= 1)
                    try self.lowerExpr(NodeIndex.fromInt(arg_nodes[0]), payload_ty)
                else
                    try self.emitUnitConst(expr_node.main_token, .none);
                const extra_idx = try self.store.appendLenPrefixedExtra(&[1]u32{payload_hir.asInt()});
                const kind: HirConstructKind = if (is_ok) .result_ok else .result_err;
                const tag_shift: u32 = if (is_ok) 0 else (1 << 8);
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue },
                    .type_id = target_ty,
                    .origin_token = expr_node.main_token,
                    .data = .{ .lhs = @as(u32, @backingInt(kind)) | tag_shift, .rhs = extra_idx },
                }, expr_id);
            },
            .enum_ty => {
                var var_ordinal: u32 = 0;
                var var_payload_ty: TypeId = .unit_ty;
                const sym_idx = self.nodeSymbol(expr_id);
                if (!sym_idx.isNone()) {
                    const v_sym = self.sym_table.getSymbol(sym_idx).*;
                    var_ordinal = v_sym.member_ordinal;
                    var_payload_ty = v_sym.type_id;
                } else {
                    const enum_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(ty_node.rhs)).*;
                    if (!enum_sym.target_scope.isNone()) {
                        if (self.interner.lookup(var_name)) |v_name_id| {
                            const found = self.sym_table.lookupInScopeDirect(
                                enum_sym.target_scope,
                                v_name_id,
                                NamespaceMask.VALUE_ONLY,
                            );
                            if (!found.isNone()) {
                                const v_sym = self.sym_table.getSymbol(found).*;
                                var_ordinal = v_sym.member_ordinal;
                                var_payload_ty = v_sym.type_id;
                            }
                        }
                    }
                }
                var lowered_args: std.ArrayListUnmanaged(u32) = .empty;
                defer lowered_args.deinit(self.allocator);
                if (arg_nodes.len == 1) {
                    try lowered_args.append(
                        self.allocator,
                        (try self.lowerExpr(NodeIndex.fromInt(arg_nodes[0]), var_payload_ty)).asInt(),
                    );
                } else if (arg_nodes.len > 1) {
                    const tup_elems = self.pool.getTupleElements(var_payload_ty);
                    for (arg_nodes, 0..) |raw_arg, i| {
                        const sub_ty = if (i < tup_elems.len) TypeId.fromInt(tup_elems[i]) else .err_ty;
                        try lowered_args.append(
                            self.allocator,
                            (try self.lowerExpr(NodeIndex.fromInt(raw_arg), sub_ty)).asInt(),
                        );
                    }
                }
                const extra_idx = try self.store.appendLenPrefixedExtra(lowered_args.items);
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue },
                    .type_id = target_ty,
                    .origin_token = expr_node.main_token,
                    .data = .{
                        .lhs = @as(u32, @backingInt(HirConstructKind.enum_variant)) | (var_ordinal << 8),
                        .rhs = extra_idx,
                    },
                }, expr_id);
            },
            else => return self.emitErrorHole(expr_node.main_token, expr_id, target_ty),
        }
    }

    /// Lowers `()` or `(a, b, …)` into `hir_const_val` or `hir_construct(.tuple_init)`.
    fn lowerTupleLit(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const elem_nodes = self.getAstExtraSlice(expr_id, false);
        if (elem_nodes.len == 0) {
            return self.emitUnitConst(ast_node.main_token, expr_id);
        }
        const tup_types = if (self.pool.getTag(target_ty) == .tuple_ty)
            self.pool.getTupleElements(target_ty)
        else
            &.{};
        var lowered_elems: std.ArrayListUnmanaged(u32) = .empty;
        defer lowered_elems.deinit(self.allocator);
        for (elem_nodes, 0..) |raw_elem, i| {
            const elem_ty = if (i < tup_types.len) TypeId.fromInt(tup_types[i]) else .err_ty;
            const elem_hir = try self.lowerExpr(NodeIndex.fromInt(raw_elem), elem_ty);
            try lowered_elems.append(self.allocator, elem_hir.asInt());
        }
        const extra_idx = try self.store.appendLenPrefixedExtra(lowered_elems.items);
        return self.emitNode(.{
            .tag = .hir_construct,
            .flags = .{ .category = .rvalue },
            .type_id = self.concreteType(target_ty),
            .origin_token = ast_node.main_token,
            .data = .{ .lhs = @backingInt(HirConstructKind.tuple_init), .rhs = extra_idx },
        }, expr_id);
    }

    /// Lowers `[a, b, c]` and `[val; N]` into `hir_construct(.array_elements / .array_repeat)`.
    fn lowerArrayLit(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const elem_nodes = self.getAstExtraSlice(expr_id, false);
        const ty_node = self.pool.getNode(target_ty);
        const elem_ty = if (ty_node.tag == .array_ty or ty_node.tag == .slice_ty or
            ty_node.tag == .soa_array_ty or ty_node.tag == .soa_slice_ty)
            TypeId.fromInt(ty_node.lhs)
        else
            .err_ty;

        if (elem_nodes.len == 2 and type_system.hasShallowSemicolonInArrayCst(
            self.cst_arena,
            self.tokens,
            self.ast_arena.getCstOrigin(expr_id),
        )) {
            const val_hir = try self.lowerExpr(NodeIndex.fromInt(elem_nodes[0]), elem_ty);
            const repeat_count: u32 = if (ty_node.tag == .array_ty or ty_node.tag == .soa_array_ty)
                (ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG)
            else if (try self.tryEvalAstComptime(NodeIndex.fromInt(elem_nodes[1]), .usize_ty)) |cnt_val|
                (if (cnt_val == .int_val and cnt_val.int_val >= 0) @intCast(cnt_val.int_val) else 0)
            else
                0;
            const extra_idx = try self.store.appendExtraSlice(&[2]u32{ repeat_count, val_hir.asInt() });
            return self.emitNode(.{
                .tag = .hir_construct,
                .flags = .{ .category = .rvalue },
                .type_id = self.concreteType(target_ty),
                .origin_token = ast_node.main_token,
                .data = .{ .lhs = @backingInt(HirConstructKind.array_repeat), .rhs = extra_idx },
            }, expr_id);
        }

        var lowered_elems: std.ArrayListUnmanaged(u32) = .empty;
        defer lowered_elems.deinit(self.allocator);
        for (elem_nodes) |raw_elem| {
            const elem_hir = try self.lowerExpr(NodeIndex.fromInt(raw_elem), elem_ty);
            try lowered_elems.append(self.allocator, elem_hir.asInt());
        }
        const extra_idx = try self.store.appendLenPrefixedExtra(lowered_elems.items);
        return self.emitNode(.{
            .tag = .hir_construct,
            .flags = .{ .category = .rvalue },
            .type_id = self.concreteType(target_ty),
            .origin_token = ast_node.main_token,
            .data = .{ .lhs = @backingInt(HirConstructKind.array_elements), .rhs = extra_idx },
        }, expr_id);
    }

    /// Lowers `struct`, `union`, and `bit_field` literals preserving source evaluation order and canonical layout.
    fn lowerStructLit(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const field_exprs = self.getAstExtraSlice(expr_id, true);
        const struct_node = self.pool.getNode(target_ty);
        if (struct_node.tag != .struct_ty and struct_node.tag != .union_ty and
            struct_node.tag != .bit_field_ty)
        {
            return self.emitErrorHole(tok, expr_id, target_ty);
        }

        const struct_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(struct_node.rhs)).*;
        if (struct_sym.target_scope.isNone()) {
            return self.emitErrorHole(tok, expr_id, target_ty);
        }

        // Collect canonical struct / `bit_field` member declarations dynamically (`CRIT-11`):
        var canonical_tys: std.ArrayListUnmanaged(TypeId) = .empty;
        defer canonical_tys.deinit(self.allocator);
        var canonical_names: std.ArrayListUnmanaged(SymbolId) = .empty;
        defer canonical_names.deinit(self.allocator);
        var canonical_texts: std.ArrayListUnmanaged([]const u8) = .empty;
        defer canonical_texts.deinit(self.allocator);
        for (self.sym_table.getScopeMembers(struct_sym.target_scope)) |mem_idx| {
            const mem_sym = self.sym_table.getSymbol(mem_idx).*;
            if (mem_sym.kind != .field_sym) continue;
            try canonical_tys.append(self.allocator, mem_sym.type_id);
            try canonical_names.append(self.allocator, mem_sym.name);
            try canonical_texts.append(self.allocator, mem_sym.name_text);
        }
        const total_fields = canonical_tys.items.len;

        // Extract field names (and optional trailing `..spread`) from CST `.field_init` subtrees:
        var init_names: std.ArrayListUnmanaged(TokenIndex) = .empty;
        defer init_names.deinit(self.allocator);
        var has_spread = false;
        const lit_cst = self.ast_arena.getCstOrigin(expr_id);
        if (!lit_cst.isNone() and lit_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = lit_cst.asInt();
            const rec = self.cst_arena.getNode(lit_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var cur = start_idx + 1;
            while (cur < end_idx) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.kind == .field_init) {
                    const f_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                    var f_cur = cur + 1;
                    while (f_cur < f_end) : (f_cur += 1) {
                        const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(f_cur)));
                        if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                            leaf.token.asInt() < self.tokens.countTokens())
                        {
                            const leaf_kind = self.tokens.getToken(leaf.token).kind;
                            if (leaf_kind == .dotdot) {
                                has_spread = true;
                                break;
                            }
                            if (symbol_resolver.isIdentifierToken(leaf_kind)) {
                                try init_names.append(self.allocator, leaf.token);
                                break;
                            }
                        }
                    }
                    cur = f_end;
                    continue;
                }
                cur += 1;
            }
        }

        var stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer stmts.deinit(self.allocator);
        var field_slots = try self.allocator.alloc(HirIndex, total_fields);
        defer self.allocator.free(field_slots);
        @memset(field_slots, .none);
        var is_out_of_order = false;
        var prev_ord: usize = 0;

        const named_expr_len = if (has_spread and field_exprs.len > 0) field_exprs.len - 1 else field_exprs.len;
        for (field_exprs[0..named_expr_len], 0..) |raw_val_expr, i| {
            var target_ord: usize = @min(i, if (total_fields > 0) total_fields - 1 else 0);
            if (i < init_names.items.len and !init_names.items[i].isNone()) {
                const f_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, init_names.items[i]);
                if (self.interner.lookup(f_lex)) |f_sym_id| {
                    for (canonical_names.items, 0..) |canon_id, ord_idx| {
                        if (canon_id == f_sym_id) {
                            target_ord = ord_idx;
                            break;
                        }
                    }
                }
            }
            if (i > 0 and target_ord < prev_ord) is_out_of_order = true;
            prev_ord = target_ord;

            const f_ty = if (target_ord < total_fields) canonical_tys.items[target_ord] else .err_ty;
            const val_hir = try self.lowerExpr(NodeIndex.fromInt(raw_val_expr), f_ty);
            const tmp_local = try self.allocTempLocal(self.store.getNode(val_hir).type_id, tok, false);
            try stmts.append(self.allocator, (try self.emitLocalDeclNode(tmp_local, val_hir, tok)).asInt());
            if (target_ord < total_fields) {
                field_slots[target_ord] = try self.emitVarRef(tmp_local, tok, .none);
            }
        }

        if (struct_node.tag == .bit_field_ty) {
            if (!has_spread and stmts.items.len == 0) {
                return self.emitDefaultInitValue(target_ty, tok);
            }
            const base_bf_hir = if (has_spread and field_exprs.len > 0)
                try self.lowerExpr(NodeIndex.fromInt(field_exprs[field_exprs.len - 1]), target_ty)
            else
                try self.emitDefaultInitValue(target_ty, tok);
            const bf_acc_local = try self.allocTempLocal(target_ty, tok, true);
            try stmts.append(self.allocator, (try self.emitLocalDeclNode(bf_acc_local, base_bf_hir, tok)).asInt());
            for (0..total_fields) |ord_idx| {
                if (field_slots[ord_idx].isNone()) continue;
                if (self.computeBitFieldSpec(target_ty, canonical_texts.items[ord_idx])) |bf_info| {
                    const coerced_val = try self.applyImplicitCoercionIfNeeded(
                        field_slots[ord_idx],
                        bf_info.field_ty,
                        tok,
                    );
                    const rmw_extra = try self.store.appendExtraSlice(&[2]u32{
                        @bitCast(bf_info.spec),
                        coerced_val.asInt(),
                    });
                    const bf_ref = try self.emitVarRef(bf_acc_local, tok, .none);
                    const rmw_hir = try self.emitNode(.{
                        .tag = .hir_bitfield_rmw,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = bf_ref.asInt(), .rhs = rmw_extra },
                    }, .none);
                    try stmts.append(self.allocator, rmw_hir.asInt());
                }
            }
            return self.emitSyntheticBlock(
                stmts.items,
                try self.emitVarRef(bf_acc_local, tok, expr_id),
                target_ty,
                tok,
            );
        }

        if (has_spread and field_exprs.len > 0) {
            const spread_hir = try self.lowerExpr(NodeIndex.fromInt(field_exprs[field_exprs.len - 1]), target_ty);
            const spread_local = try self.allocTempLocal(target_ty, tok, false);
            try stmts.append(self.allocator, (try self.emitLocalDeclNode(spread_local, spread_hir, tok)).asInt());
            for (0..total_fields) |ord_idx| {
                if (field_slots[ord_idx].isNone()) {
                    field_slots[ord_idx] = try self.emitNode(.{
                        .tag = .hir_field_proj,
                        .flags = .{ .category = .place_imm, .is_synthetic = true },
                        .type_id = self.concreteType(canonical_tys.items[ord_idx]),
                        .origin_token = tok,
                        .data = .{
                            .lhs = (try self.emitVarRef(spread_local, tok, .none)).asInt(),
                            .rhs = @intCast(ord_idx),
                        },
                    }, .none);
                }
            }
        }

        var final_fields = try self.allocator.alloc(u32, total_fields);
        defer self.allocator.free(final_fields);
        for (0..total_fields) |ord_idx| {
            const f_hir = if (!field_slots[ord_idx].isNone())
                field_slots[ord_idx]
            else
                try self.emitDefaultInitValue(canonical_tys.items[ord_idx], tok);
            final_fields[ord_idx] = f_hir.asInt();
        }
        const extra_idx = try self.store.appendLenPrefixedExtra(final_fields);
        const construct_hir = try self.emitNode(.{
            .tag = .hir_construct,
            .flags = .{ .category = .rvalue },
            .type_id = target_ty,
            .origin_token = tok,
            .data = .{ .lhs = @backingInt(HirConstructKind.struct_init), .rhs = extra_idx },
        }, expr_id);

        if (is_out_of_order or has_spread or stmts.items.len > 0) {
            return self.emitSyntheticBlock(stmts.items, construct_hir, target_ty, tok);
        }
        return construct_hir;
    }

    /// Lowers prefix unary operations (`comptime`, `yield`, `-`, `not`, `!`, `&`, `&mut`, `*`).
    fn lowerUnaryExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node) return self.emitErrorHole(tok, expr_id, target_ty);
        const inner_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const op_kind = self.tokens.getToken(tok).kind;

        // [1] `comptime` prefix (`comptime if`, `comptime match`, `comptime { … }`, `comptime expr`):
        if (op_kind == .kw_comptime) {
            const inner_tag = self.ast_arena.getNode(inner_id).tag;
            if (inner_tag == .if_expr) return self.lowerIfExpr(inner_id, target_ty, true);
            if (inner_tag == .match_expr) return self.lowerMatchExpr(inner_id, target_ty, true);
            if (try self.tryEvalAstComptime(inner_id, target_ty)) |folded_val| {
                const res_ty = if (!target_ty.isError()) target_ty else self.inferComptimeValType(folded_val);
                return self.emitConstVal(folded_val, res_ty, tok, expr_id, true);
            }
            const lowered_inner = try self.lowerExpr(inner_id, target_ty);
            if (self.eval_hook.eval_hir_fn) |eval_fn| {
                if (try eval_fn(
                    self.eval_hook.compiler_db,
                    self.eval_hook.session_id,
                    self.store,
                    lowered_inner,
                    target_ty,
                    self.diagnostic_sink,
                )) |vm_val| {
                    const res_ty = if (!target_ty.isError()) target_ty else self.store.getNode(lowered_inner).type_id;
                    return self.emitConstVal(vm_val, res_ty, tok, expr_id, true);
                }
            }
            return lowered_inner;
        }

        // [2] `yield place_expr` inside `subscript` (`DR-02` §2.2):
        if (op_kind == .ident and
            std.mem.eql(u8, symbol_resolver.extractTokenSlice(self.source, self.tokens, tok), "yield"))
        {
            const yielded_hir = try self.lowerExpr(inner_id, self.current_fn_ret_ty);
            return self.emitNode(.{
                .tag = .hir_yield,
                .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
                .type_id = self.store.getNode(yielded_hir).type_id,
                .origin_token = tok,
                .data = .{ .lhs = yielded_hir.asInt(), .rhs = 0 },
            }, expr_id);
        }

        // [3] Fold negated integer literal (`-128i8`, `-170141183460469231731687303715884105728i128`) directly:
        if (op_kind == .minus and self.ast_arena.getNode(inner_id).tag == .int_lit) {
            const inner_tok = self.ast_arena.getNode(inner_id).main_token;
            const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, inner_tok);
            const neg_val = extractNegatedIntValue(lexeme) orelse 0;
            const int_ty = if (!target_ty.isError()) target_ty else .i32_ty;
            return self.emitConstVal(.{ .int_val = neg_val }, int_ty, tok, expr_id, false);
        }

        const inner_hir = try self.lowerExpr(inner_id, .err_ty);
        const inner_node = self.store.getNode(inner_hir);

        switch (op_kind) {
            .minus => return self.emitNode(.{
                .tag = .hir_unary_op,
                .flags = .{ .category = .rvalue },
                .type_id = if (!target_ty.isError()) target_ty else inner_node.type_id,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(HirUnaryOp.neg), .rhs = inner_hir.asInt() },
            }, expr_id),
            .kw_not => return self.emitNode(.{
                .tag = .hir_unary_op,
                .flags = .{ .category = .rvalue },
                .type_id = .bool_ty,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(HirUnaryOp.logical_not), .rhs = inner_hir.asInt() },
            }, expr_id),
            .bang => {
                const un_op: HirUnaryOp = if (inner_node.type_id == .bool_ty) .logical_not else .bit_not;
                return self.emitNode(.{
                    .tag = .hir_unary_op,
                    .flags = .{ .category = .rvalue },
                    .type_id = if (!target_ty.isError()) target_ty else inner_node.type_id,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(un_op), .rhs = inner_hir.asInt() },
                }, expr_id);
            },
            .amp, .kw_ref => {
                const is_mut = self.hasKeywordInCst(self.ast_arena.getCstOrigin(expr_id), .kw_mut) or
                    (self.pool.getTag(target_ty) == .mut_ref_ty);
                const ref_ty = if (!target_ty.isError())
                    target_ty
                else
                    try self.pool.internRef(inner_node.type_id, is_mut);
                return self.emitNode(.{
                    .tag = .hir_unary_op,
                    .flags = .{ .category = .rvalue },
                    .type_id = ref_ty,
                    .origin_token = tok,
                    .data = .{
                        .lhs = @backingInt(if (is_mut) HirUnaryOp.addr_of_mut else HirUnaryOp.addr_of),
                        .rhs = inner_hir.asInt(),
                    },
                }, expr_id);
            },
            .star => {
                const ptr_ty_node = self.pool.getNode(inner_node.type_id);
                const is_mut_deref = ptr_ty_node.tag == .mut_ref_ty or
                    (ptr_ty_node.tag == .raw_ptr_ty and ptr_ty_node.rhs != 0);
                const pointee_ty = if (!target_ty.isError())
                    target_ty
                else switch (ptr_ty_node.tag) {
                    .ref_ty, .mut_ref_ty, .raw_ptr_ty => TypeId.fromInt(ptr_ty_node.lhs),
                    else => .unit_ty,
                };
                return self.emitNode(.{
                    .tag = .hir_unary_op,
                    .flags = .{
                        .category = if (is_mut_deref) .place_mut else .place_imm,
                        .is_unsafe = self.is_in_unsafe or ptr_ty_node.tag == .raw_ptr_ty,
                    },
                    .type_id = self.concreteType(pointee_ty),
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirUnaryOp.deref), .rhs = inner_hir.asInt() },
                }, expr_id);
            },
            else => return inner_hir,
        }
    }

    /// Lowers `src as TargetType` into `hir_cast` with exact `HirCastKind`.
    fn lowerCastExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.lhs.tag != .node) {
            return self.emitErrorHole(ast_node.main_token, expr_id, target_ty);
        }
        const lhs_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const resolved_dst_ty = self.concreteType(if (!target_ty.isError()) target_ty else self.nodeType(expr_id));
        const lhs_hint_ty = if (!resolved_dst_ty.isError() and
            self.ast_arena.getNode(lhs_id).tag == .contextual_variant)
            self.pool.unwrapUnderlyingType(resolved_dst_ty)
        else
            TypeId.err_ty;
        const src_hir = try self.lowerExpr(lhs_id, lhs_hint_ty);

        const src_ty = self.store.getNode(src_hir).type_id;
        const dst_ty = if (!resolved_dst_ty.isError()) resolved_dst_ty else src_ty;
        const src_tag = self.pool.getTag(src_ty);
        const dst_tag = self.pool.getTag(dst_ty);

        const cast_kind: HirCastKind = if (src_tag == .distinct_ty and dst_tag != .distinct_ty)
            .distinct_unwrap
        else if (src_tag != .distinct_ty and dst_tag == .distinct_ty)
            .distinct_wrap
        else if ((src_ty.isIntegerPrimitive() or src_ty == .bool_ty or src_ty == .char_ty) and
            (dst_ty.isIntegerPrimitive() or dst_ty == .char_ty))
            .int_to_int
        else if (src_ty.isIntegerPrimitive() and dst_ty.isFloatPrimitive())
            .int_to_float
        else if (src_ty.isFloatPrimitive() and dst_ty.isIntegerPrimitive())
            .float_to_int
        else if (src_ty.isFloatPrimitive() and dst_ty.isFloatPrimitive())
            .float_to_float
        else if (src_tag == .raw_ptr_ty or dst_tag == .raw_ptr_ty or src_tag == .ref_ty or src_tag == .mut_ref_ty)
            .ptr_cast
        else
            .noop;

        return self.emitNode(.{
            .tag = .hir_cast,
            .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
            .type_id = dst_ty,
            .origin_token = ast_node.main_token,
            .data = .{ .lhs = src_hir.asInt(), .rhs = @backingInt(cast_kind) },
        }, expr_id);
    }

    /// Desugars `lhs |> f(a_1, …, a_k)` and `lhs |> recv.m(a_1, …, a_k)` (`DR-13` §2.2 Rule 1 & `MAJ-06`).
    fn lowerPipeExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .node) {
            return self.emitErrorHole(tok, expr_id, target_ty);
        }
        const lhs_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const rhs_id = NodeIndex.fromInt(ast_node.rhs.payload);
        const rhs_node = self.ast_arena.getNode(rhs_id);

        // [1] Method pipeline `lhs |> recv.method(a_1, …, a_k)` -> `method(recv, lhs, a_1, …, a_k)` (`MAJ-06`):
        if (rhs_node.tag == .method_call and rhs_node.lhs.tag == .node) {
            const recv_id = NodeIndex.fromInt(rhs_node.lhs.payload);
            const raw_items = self.getAstExtraSlice(rhs_id, true);
            if (raw_items.len == 0) return self.emitErrorHole(tok, expr_id, target_ty);
            const member_tok = TokenIndex.fromInt(raw_items[0]);
            const member_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, member_tok);

            var method_sym_idx = self.nodeSymbol(rhs_id);
            if (method_sym_idx.isNone()) {
                const recv_ty = self.unwrapRefType(self.nodeType(recv_id));
                if (try self.lookupMethodOnType(recv_ty, member_name)) |found_m| {
                    method_sym_idx = found_m;
                }
            }
            if (method_sym_idx.isNone()) return self.emitErrorHole(tok, expr_id, target_ty);

            const method_sym = self.sym_table.getSymbol(method_sym_idx).*;
            const sig_view = self.pool.getFnSignatureView(method_sym.type_id);

            var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
            defer seq_stmts.deinit(self.allocator);

            const lhs_param_ty = if (sig_view) |sv|
                (if (sv.paramCount() > 1) sv.getParamType(1) else .err_ty)
            else
                .err_ty;
            const lhs_mode: ParamMode = if (sig_view) |sv|
                (if (sv.paramCount() > 1) sv.getParamMode(1) else .let_mode)
            else
                .let_mode;

            var piped_hir = try self.lowerExpr(lhs_id, lhs_param_ty);
            if (!lhs_param_ty.isError()) {
                piped_hir = try self.adjustReceiverForParam(piped_hir, lhs_param_ty, tok);
            }
            if (lhs_mode != .inout_mode and lhs_mode != .set_mode) {
                const lhs_tmp = try self.allocTempLocal(self.store.getNode(piped_hir).type_id, tok, false);
                try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(lhs_tmp, piped_hir, tok)).asInt());
                piped_hir = try self.emitVarRef(lhs_tmp, tok, .none);
            }

            var extra_arg_hirs: std.ArrayListUnmanaged(HirIndex) = .empty;
            defer extra_arg_hirs.deinit(self.allocator);
            var extra_arg_modes: std.ArrayListUnmanaged(ParamMode) = .empty;
            defer extra_arg_modes.deinit(self.allocator);

            var param_ord: usize = 2;
            for (raw_items[1..]) |raw_item| {
                const item_id = NodeIndex.fromInt(raw_item);
                if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
                if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) continue;

                const p_ty = if (sig_view) |sv|
                    (if (param_ord < sv.paramCount()) sv.getParamType(param_ord) else .err_ty)
                else
                    .err_ty;
                const p_mode: ParamMode = if (sig_view) |sv|
                    (if (param_ord < sv.paramCount()) sv.getParamMode(param_ord) else .let_mode)
                else
                    .let_mode;
                var arg_hir = try self.lowerExpr(item_id, p_ty);
                if (!p_ty.isError()) {
                    arg_hir = try self.adjustReceiverForParam(arg_hir, p_ty, tok);
                }
                if (p_mode != .inout_mode and p_mode != .set_mode) {
                    const tmp_slot = try self.allocTempLocal(self.store.getNode(arg_hir).type_id, tok, false);
                    try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(tmp_slot, arg_hir, tok)).asInt());
                    arg_hir = try self.emitVarRef(tmp_slot, tok, .none);
                }
                try extra_arg_hirs.append(self.allocator, arg_hir);
                try extra_arg_modes.append(self.allocator, p_mode);
                param_ord += 1;
            }

            const raw_recv_hir = try self.lowerExpr(recv_id, .err_ty);
            const self_param_ty = if (sig_view) |sv|
                (if (sv.paramCount() > 0) sv.getParamType(0) else self.store.getNode(raw_recv_hir).type_id)
            else
                self.store.getNode(raw_recv_hir).type_id;
            const self_mode: ParamMode = if (sig_view) |sv|
                (if (sv.paramCount() > 0) sv.getParamMode(0) else .let_mode)
            else
                .let_mode;
            const adjusted_recv = try self.adjustReceiverForParam(raw_recv_hir, self_param_ty, tok);

            var wrapped_args: std.ArrayListUnmanaged(u32) = .empty;
            defer wrapped_args.deinit(self.allocator);
            try wrapped_args.append(
                self.allocator,
                (try self.wrapArgProjection(adjusted_recv, self_mode, tok)).asInt(),
            );
            try wrapped_args.append(
                self.allocator,
                (try self.wrapArgProjection(piped_hir, lhs_mode, tok)).asInt(),
            );
            for (extra_arg_hirs.items, 0..) |arg_hir, i| {
                try wrapped_args.append(
                    self.allocator,
                    (try self.wrapArgProjection(arg_hir, extra_arg_modes.items[i], tok)).asInt(),
                );
            }

            const callee_hir = try self.emitNode(.{
                .tag = .hir_global_ref,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = method_sym.type_id,
                .origin_token = tok,
                .data = .{ .lhs = method_sym.def_id.asInt(), .rhs = method_sym_idx.asInt() },
            }, .none);
            const ret_ty = if (!target_ty.isError())
                target_ty
            else if (sig_view) |sv|
                self.concreteType(sv.ret_ty)
            else
                .unit_ty;
            const extra_idx = try self.store.appendLenPrefixedExtra(wrapped_args.items);
            const call_hir = try self.emitNode(.{
                .tag = if (self.isCalleeSubscript(callee_hir)) .hir_subscript_call else .hir_call,
                .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                .type_id = ret_ty,
                .origin_token = tok,
                .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
            }, expr_id);
            if (seq_stmts.items.len > 0) {
                return self.emitSyntheticBlock(seq_stmts.items, call_hir, ret_ty, tok);
            }
            return call_hir;
        }

        // [2] Function / indirect pipeline `lhs |> f(a_1, …, a_k)` or `lhs |> f`:
        var callee_ast_id: NodeIndex = rhs_id;
        var raw_call_items: []const u32 = &.{};
        if (rhs_node.tag == .call_expr or rhs_node.tag == .generic_call or rhs_node.tag == .incomplete_call) {
            if (rhs_node.lhs.tag == .node) callee_ast_id = NodeIndex.fromInt(rhs_node.lhs.payload);
            raw_call_items = self.getAstExtraSlice(rhs_id, true);
        }

        const rhs_sym_idx = self.nodeSymbol(rhs_id);
        const resolved_sym_idx = if (!rhs_sym_idx.isNone()) rhs_sym_idx else self.nodeSymbol(callee_ast_id);
        const is_direct_sym = !resolved_sym_idx.isNone() and
            self.sym_table.getSymbol(resolved_sym_idx).kind == .fn_sym;
        const pre_callee_ty = if (is_direct_sym)
            self.sym_table.getSymbol(resolved_sym_idx).type_id
        else
            self.nodeType(callee_ast_id);
        var sig_view = self.pool.getFnSignatureView(pre_callee_ty);

        var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer seq_stmts.deinit(self.allocator);

        const first_ty: TypeId = if (sig_view) |sv|
            (if (sv.paramCount() > 0) sv.getParamType(0) else .err_ty)
        else
            .err_ty;
        const first_mode_pre: ParamMode = if (sig_view) |sv|
            (if (sv.paramCount() > 0) sv.getParamMode(0) else .let_mode)
        else
            .let_mode;

        var lhs_hir = try self.lowerExpr(lhs_id, first_ty);
        if (!is_direct_sym and first_mode_pre != .inout_mode and first_mode_pre != .set_mode) {
            const lhs_tmp = try self.allocTempLocal(self.store.getNode(lhs_hir).type_id, tok, false);
            try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(lhs_tmp, lhs_hir, tok)).asInt());
            lhs_hir = try self.emitVarRef(lhs_tmp, tok, .none);
        }

        var lowered_call_args: std.ArrayListUnmanaged(HirIndex) = .empty;
        defer lowered_call_args.deinit(self.allocator);
        var arg_ordinal: usize = 1;
        for (raw_call_items) |raw_item| {
            const item_id = NodeIndex.fromInt(raw_item);
            if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
            if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) continue;

            const param_ty: TypeId = if (sig_view) |sv|
                (if (arg_ordinal < sv.paramCount()) sv.getParamType(arg_ordinal) else .err_ty)
            else
                .err_ty;
            const param_mode_pre: ParamMode = if (sig_view) |sv|
                (if (arg_ordinal < sv.paramCount()) sv.getParamMode(arg_ordinal) else .let_mode)
            else
                .let_mode;
            var arg_hir = try self.lowerExpr(item_id, param_ty);
            if (!is_direct_sym and param_mode_pre != .inout_mode and param_mode_pre != .set_mode) {
                const tmp_slot = try self.allocTempLocal(self.store.getNode(arg_hir).type_id, tok, false);
                try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(tmp_slot, arg_hir, tok)).asInt());
                arg_hir = try self.emitVarRef(tmp_slot, tok, .none);
            }
            try lowered_call_args.append(self.allocator, arg_hir);
            arg_ordinal += 1;
        }

        const callee_hir = if (is_direct_sym) blk: {
            const fn_sym = self.sym_table.getSymbol(resolved_sym_idx).*;
            break :blk try self.emitNode(.{
                .tag = .hir_global_ref,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = fn_sym.type_id,
                .origin_token = tok,
                .data = .{ .lhs = fn_sym.def_id.asInt(), .rhs = resolved_sym_idx.asInt() },
            }, callee_ast_id);
        } else try self.lowerExpr(callee_ast_id, .err_ty);

        if (sig_view == null) {
            sig_view = self.pool.getFnSignatureView(self.store.getNode(callee_hir).type_id);
        }

        var wrapped_args: std.ArrayListUnmanaged(u32) = .empty;
        defer wrapped_args.deinit(self.allocator);

        const first_mode: ParamMode = if (sig_view) |sv|
            (if (sv.paramCount() > 0) sv.getParamMode(0) else .let_mode)
        else
            .let_mode;
        if (sig_view) |sv| {
            if (sv.paramCount() > 0) {
                lhs_hir = try self.adjustReceiverForParam(lhs_hir, sv.getParamType(0), tok);
            }
        }
        try wrapped_args.append(self.allocator, (try self.wrapArgProjection(lhs_hir, first_mode, tok)).asInt());

        for (lowered_call_args.items, 0..) |raw_arg_hir, i| {
            const p_idx = i + 1;
            var adj_arg = raw_arg_hir;
            const p_mode: ParamMode = if (sig_view) |sv|
                (if (p_idx < sv.paramCount()) sv.getParamMode(p_idx) else .let_mode)
            else
                .let_mode;
            if (sig_view) |sv| {
                if (p_idx < sv.paramCount()) {
                    adj_arg = try self.adjustReceiverForParam(adj_arg, sv.getParamType(p_idx), tok);
                }
            }
            try wrapped_args.append(self.allocator, (try self.wrapArgProjection(adj_arg, p_mode, tok)).asInt());
        }

        const ret_ty = if (!target_ty.isError())
            target_ty
        else if (sig_view) |sv|
            self.concreteType(sv.ret_ty)
        else
            .unit_ty;

        const extra_idx = try self.store.appendLenPrefixedExtra(wrapped_args.items);
        const call_hir = try self.emitNode(.{
            .tag = if (self.isCalleeSubscript(callee_hir)) .hir_subscript_call else .hir_call,
            .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
            .type_id = ret_ty,
            .origin_token = tok,
            .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
        }, expr_id);
        if (seq_stmts.items.len > 0) {
            return self.emitSyntheticBlock(seq_stmts.items, call_hir, ret_ty, tok);
        }
        return call_hir;
    }

    /// Desugars postfix `expr?` on `Result[T, E]` and `T?` (`Option[T]`) with `@from` conversion (`DR-13` §2.2 Rule 2).
    fn lowerTryExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node) return self.emitErrorHole(tok, expr_id, target_ty);

        var inner_hir = try self.lowerExpr(NodeIndex.fromInt(ast_node.lhs.payload), .err_ty);
        const raw_inner_ty = self.store.getNode(inner_hir).type_id;
        const inner_ty = self.pool.unwrapUnderlyingType(raw_inner_ty);
        if (inner_ty != raw_inner_ty) {
            inner_hir = try self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = inner_ty,
                .origin_token = tok,
                .data = .{ .lhs = inner_hir.asInt(), .rhs = @backingInt(HirCastKind.distinct_unwrap) },
            }, .none);
        }
        const inner_ty_node = self.pool.getNode(inner_ty);
        const concrete_fn_ret = self.concreteType(self.current_fn_ret_ty);
        const unwrapped_fn_ret = self.pool.unwrapUnderlyingType(concrete_fn_ret);

        if (inner_ty_node.tag == .optional_ty) {
            const payload_ty = self.concreteType(TypeId.fromInt(inner_ty_node.lhs));
            const val_local = try self.allocTempLocal(payload_ty, tok, false);
            const val_bind = try self.store.appendPat(.{
                .type_id = payload_ty,
                .origin_token = tok,
                .kind = .{ .bind = .{ .local_id = val_local, .is_mut = false, .is_ref = false } },
            });
            const some_sub = try self.store.appendExtraSlice(&[1]u32{val_bind});
            const some_pat = try self.store.appendPat(.{
                .type_id = inner_ty,
                .origin_token = tok,
                .kind = .{
                    .variant = .{
                        .tag_ordinal = 1,
                        .payload_ty = payload_ty,
                        .sub_start = some_sub,
                        .sub_len = 1,
                    },
                },
            });
            const none_pat = try self.store.appendPat(.{
                .type_id = inner_ty,
                .origin_token = tok,
                .kind = .{
                    .variant = .{
                        .tag_ordinal = 0,
                        .payload_ty = .unit_ty,
                        .sub_start = 0,
                        .sub_len = 0,
                    },
                },
            });

            const ret_none_extra = try self.store.appendLenPrefixedExtra(&.{});
            var ret_none_val = try self.emitNode(.{
                .tag = .hir_construct,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = unwrapped_fn_ret,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(HirConstructKind.optional_none), .rhs = ret_none_extra },
            }, .none);
            if (unwrapped_fn_ret != concrete_fn_ret) {
                ret_none_val = try self.emitNode(.{
                    .tag = .hir_cast,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = concrete_fn_ret,
                    .origin_token = tok,
                    .data = .{ .lhs = ret_none_val.asInt(), .rhs = @backingInt(HirCastKind.distinct_wrap) },
                }, .none);
            }
            const ret_stmt = try self.emitNode(.{
                .tag = .hir_return,
                .flags = .{ .category = .diverging, .is_synthetic = true },
                .type_id = .never_ty,
                .origin_token = tok,
                .data = .{ .lhs = ret_none_val.asInt(), .rhs = @backingInt(ReturnErrorKind.explicit_err) },
            }, expr_id);

            const arm_start: u32 = @intCast(self.store.match_arms.items.len);
            try self.store.match_arms.append(self.allocator, .{
                .pat_idx = some_pat,
                .guard_hir = .none,
                .body_hir = try self.emitVarRef(val_local, tok, .none),
                .origin_token = tok,
            });
            try self.store.match_arms.append(self.allocator, .{
                .pat_idx = none_pat,
                .guard_hir = .none,
                .body_hir = ret_stmt,
                .origin_token = tok,
            });
            const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, 2 });
            return self.emitNode(.{
                .tag = .hir_match,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = payload_ty,
                .origin_token = tok,
                .data = .{ .lhs = inner_hir.asInt(), .rhs = match_extra },
            }, expr_id);
        }

        if (inner_ty_node.tag == .result_ty) {
            const ok_ty = self.concreteType(TypeId.fromInt(inner_ty_node.lhs));
            const err_ty = self.concreteType(TypeId.fromInt(inner_ty_node.rhs));

            const ok_local = try self.allocTempLocal(ok_ty, tok, false);
            const ok_bind = try self.store.appendPat(.{
                .type_id = ok_ty,
                .origin_token = tok,
                .kind = .{ .bind = .{ .local_id = ok_local, .is_mut = false, .is_ref = false } },
            });
            const ok_sub = try self.store.appendExtraSlice(&[1]u32{ok_bind});
            const ok_pat = try self.store.appendPat(.{
                .type_id = inner_ty,
                .origin_token = tok,
                .kind = .{ .variant = .{ .tag_ordinal = 0, .payload_ty = ok_ty, .sub_start = ok_sub, .sub_len = 1 } },
            });

            const err_local = try self.allocTempLocal(err_ty, tok, false);
            const err_bind = try self.store.appendPat(.{
                .type_id = err_ty,
                .origin_token = tok,
                .kind = .{ .bind = .{ .local_id = err_local, .is_mut = false, .is_ref = false } },
            });
            const err_sub = try self.store.appendExtraSlice(&[1]u32{err_bind});
            const err_pat = try self.store.appendPat(.{
                .type_id = inner_ty,
                .origin_token = tok,
                .kind = .{
                    .variant = .{ .tag_ordinal = 1, .payload_ty = err_ty, .sub_start = err_sub, .sub_len = 1 },
                },
            });

            var converted_err = try self.emitVarRef(err_local, tok, .none);
            const fn_ret_node = self.pool.getNode(unwrapped_fn_ret);
            const outer_err_ty = if (fn_ret_node.tag == .result_ty)
                self.concreteType(TypeId.fromInt(fn_ret_node.rhs))
            else
                err_ty;

            var has_converted_err = false;
            if (self.side_tables) |tables| {
                if (tables.getTryConversion(expr_id)) |conv_def_id| {
                    if (!conv_def_id.isNone()) {
                        if (self.sym_table.def_to_symbol.get(conv_def_id.asInt())) |conv_sym_idx| {
                            converted_err = try self.emitDirectSymbolCall(
                                conv_sym_idx,
                                &[1]HirIndex{converted_err},
                                outer_err_ty,
                                tok,
                            );
                            has_converted_err = true;
                        }
                    }
                }
            }
            if (!has_converted_err and err_ty != outer_err_ty) {
                const unwrapped_outer_err = self.pool.unwrapUnderlyingType(outer_err_ty);
                const outer_err_node = self.pool.getNode(unwrapped_outer_err);
                if (outer_err_node.tag == .enum_ty) {
                    const enum_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(outer_err_node.rhs)).*;
                    if (!enum_sym.target_scope.isNone()) {
                        for (self.sym_table.getScopeMembers(enum_sym.target_scope)) |member_idx| {
                            const member_sym = self.sym_table.getSymbol(member_idx).*;
                            if (member_sym.kind != .enum_variant_sym or !member_sym.flags.is_from_error) continue;
                            const var_pay_ty = self.concreteType(member_sym.type_id);
                            const expected_src_ty = if (self.pool.getTag(var_pay_ty) == .tuple_ty) blk: {
                                const tup_elems = self.pool.getTupleElements(var_pay_ty);
                                break :blk if (tup_elems.len == 1)
                                    self.concreteType(TypeId.fromInt(tup_elems[0]))
                                else
                                    var_pay_ty;
                            } else var_pay_ty;
                            if (expected_src_ty == err_ty) {
                                const wrap_extra = try self.store.appendLenPrefixedExtra(
                                    &[1]u32{converted_err.asInt()},
                                );
                                converted_err = try self.emitNode(.{
                                    .tag = .hir_construct,
                                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                                    .type_id = unwrapped_outer_err,
                                    .origin_token = tok,
                                    .data = .{
                                        .lhs = @as(u32, @backingInt(HirConstructKind.enum_variant)) |
                                            (@as(u32, member_sym.member_ordinal) << 8),
                                        .rhs = wrap_extra,
                                    },
                                }, .none);
                                if (unwrapped_outer_err != outer_err_ty) {
                                    converted_err = try self.emitNode(.{
                                        .tag = .hir_cast,
                                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                                        .type_id = outer_err_ty,
                                        .origin_token = tok,
                                        .data = .{
                                            .lhs = converted_err.asInt(),
                                            .rhs = @backingInt(HirCastKind.distinct_wrap),
                                        },
                                    }, .none);
                                }
                                break;
                            }
                        }
                    }
                }
            }

            const err_extra = try self.store.appendLenPrefixedExtra(&[1]u32{converted_err.asInt()});
            var ret_err_val = try self.emitNode(.{
                .tag = .hir_construct,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = unwrapped_fn_ret,
                .origin_token = tok,
                .data = .{
                    .lhs = @as(u32, @backingInt(HirConstructKind.result_err)) | (1 << 8),
                    .rhs = err_extra,
                },
            }, .none);
            if (unwrapped_fn_ret != concrete_fn_ret) {
                ret_err_val = try self.emitNode(.{
                    .tag = .hir_cast,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = concrete_fn_ret,
                    .origin_token = tok,
                    .data = .{ .lhs = ret_err_val.asInt(), .rhs = @backingInt(HirCastKind.distinct_wrap) },
                }, .none);
            }
            const ret_stmt = try self.emitNode(.{
                .tag = .hir_return,
                .flags = .{ .category = .diverging, .is_synthetic = true },
                .type_id = .never_ty,
                .origin_token = tok,
                .data = .{ .lhs = ret_err_val.asInt(), .rhs = @backingInt(ReturnErrorKind.explicit_err) },
            }, expr_id);

            const arm_start: u32 = @intCast(self.store.match_arms.items.len);
            try self.store.match_arms.append(self.allocator, .{
                .pat_idx = ok_pat,
                .guard_hir = .none,
                .body_hir = try self.emitVarRef(ok_local, tok, .none),
                .origin_token = tok,
            });
            try self.store.match_arms.append(self.allocator, .{
                .pat_idx = err_pat,
                .guard_hir = .none,
                .body_hir = ret_stmt,
                .origin_token = tok,
            });
            const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, 2 });
            return self.emitNode(.{
                .tag = .hir_match,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = ok_ty,
                .origin_token = tok,
                .data = .{ .lhs = inner_hir.asInt(), .rhs = match_extra },
            }, expr_id);
        }

        return self.emitErrorHole(tok, expr_id, target_ty);
    }

    /// Lowers infix binary operators, `expr catch |err| fallback`, and `expr is Pattern`.
    fn lowerBinaryOrCatchExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const op_kind = self.tokens.getToken(tok).kind;

        if (op_kind == .kw_catch) {
            return self.lowerCatchExpr(expr_id, target_ty);
        }
        if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .node) {
            return self.emitErrorHole(tok, expr_id, target_ty);
        }
        const lhs_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const rhs_id = NodeIndex.fromInt(ast_node.rhs.payload);

        // [1] Standalone `expr is Pattern -> bool` (`DR-13` §2.2 Rule 4):
        if (op_kind == .kw_is) {
            const scrutinee_hir = try self.lowerExpr(lhs_id, .err_ty);
            const scrut_ty = self.store.getNode(scrutinee_hir).type_id;
            const local_checkpoint = self.local_shadow_log.items.len;
            defer self.popLexicalLocalsTo(local_checkpoint);

            const pat_idx = try self.lowerTopPattern(rhs_id, scrut_ty, false);
            const wild_pat = try self.store.appendPat(.{
                .type_id = scrut_ty,
                .origin_token = tok,
                .kind = .wildcard,
            });
            const arm_start: u32 = @intCast(self.store.match_arms.items.len);
            try self.store.match_arms.append(self.allocator, .{
                .pat_idx = pat_idx,
                .guard_hir = .none,
                .body_hir = try self.emitConstVal(.{ .bool_val = true }, .bool_ty, tok, .none, true),
                .origin_token = tok,
            });
            try self.store.match_arms.append(self.allocator, .{
                .pat_idx = wild_pat,
                .guard_hir = .none,
                .body_hir = try self.emitConstVal(.{ .bool_val = false }, .bool_ty, tok, .none, true),
                .origin_token = tok,
            });
            const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, 2 });
            return self.emitNode(.{
                .tag = .hir_match,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = .bool_ty,
                .origin_token = tok,
                .data = .{ .lhs = scrutinee_hir.asInt(), .rhs = match_extra },
            }, expr_id);
        }

        // [2] Resolved operator trait call (`side_tables` or nominal `Eq::eq` for `==` / `!=`, `CRIT-13`):
        const op_sym_idx = self.nodeSymbol(expr_id);
        if (!op_sym_idx.isNone() and self.sym_table.getSymbol(op_sym_idx).kind == .fn_sym) {
            const lhs_hir = try self.lowerExpr(lhs_id, .err_ty);
            const rhs_hir = try self.lowerExpr(rhs_id, .err_ty);
            const op_call = try self.emitDirectSymbolCall(
                op_sym_idx,
                &[2]HirIndex{ lhs_hir, rhs_hir },
                if (!target_ty.isError()) target_ty else self.store.getNode(lhs_hir).type_id,
                tok,
            );
            if (op_kind == .bang_eq and std.mem.eql(u8, self.sym_table.getSymbol(op_sym_idx).name_text, "eq")) {
                return self.emitNode(.{
                    .tag = .hir_unary_op,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .bool_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirUnaryOp.logical_not), .rhs = op_call.asInt() },
                }, expr_id);
            }
            return op_call;
        }

        const lhs_hir = try self.lowerExpr(lhs_id, .err_ty);
        const lhs_ty = self.store.getNode(lhs_hir).type_id;
        const rhs_expected = if (op_kind == .ampamp or op_kind == .kw_and or
            op_kind == .pipepipe or op_kind == .kw_or)
            .bool_ty
        else
            lhs_ty;
        const rhs_hir = try self.lowerExpr(rhs_id, rhs_expected);

        if (op_kind == .eqeq or op_kind == .bang_eq) {
            const unref_lhs = self.unwrapRefType(lhs_ty);
            const lhs_tag = self.pool.getTag(unref_lhs);
            if (lhs_tag == .struct_ty or lhs_tag == .enum_ty or lhs_tag == .union_ty or
                lhs_tag == .bit_field_ty or lhs_tag == .distinct_ty)
            {
                if (try self.lookupMethodOnType(unref_lhs, "eq")) |eq_sym_idx| {
                    const eq_call = try self.emitDirectSymbolCall(
                        eq_sym_idx,
                        &[2]HirIndex{ lhs_hir, rhs_hir },
                        .bool_ty,
                        tok,
                    );
                    if (op_kind == .bang_eq) {
                        return self.emitNode(.{
                            .tag = .hir_unary_op,
                            .flags = .{ .category = .rvalue, .is_synthetic = true },
                            .type_id = .bool_ty,
                            .origin_token = tok,
                            .data = .{ .lhs = @backingInt(HirUnaryOp.logical_not), .rhs = eq_call.asInt() },
                        }, expr_id);
                    }
                    return eq_call;
                }
            }
        }

        const bin_op: HirBinaryOp = switch (op_kind) {
            .plus => .add,
            .minus => .sub,
            .star => .mul,
            .slash => .div,
            .percent => .rem,
            .plus_percent => .wrap_add,
            .minus_percent => .wrap_sub,
            .star_percent => .wrap_mul,
            .plus_pipe => .sat_add,
            .minus_pipe => .sat_sub,
            .star_pipe => .sat_mul,
            .amp => .bit_and,
            .pipe => .bit_or,
            .caret => .bit_xor,
            .shl => .shl,
            .shr => .shr,
            .eqeq => .eq,
            .bang_eq => .ne,
            .lt => .lt,
            .le => .le,
            .gt => .gt,
            .ge => .ge,
            .ampamp, .kw_and => .logical_and,
            .pipepipe, .kw_or => .logical_or,
            else => .add,
        };

        const res_ty = switch (bin_op) {
            .eq, .ne, .lt, .le, .gt, .ge, .logical_and, .logical_or => .bool_ty,
            else => if (!target_ty.isError()) target_ty else lhs_ty,
        };
        const pair = [2]u32{ lhs_hir.asInt(), rhs_hir.asInt() };
        const extra_idx = try self.store.appendExtraSlice(&pair);
        return self.emitNode(.{
            .tag = .hir_binary_op,
            .flags = .{ .category = .rvalue },
            .type_id = self.concreteType(res_ty),
            .origin_token = tok,
            .data = .{ .lhs = extra_idx, .rhs = @backingInt(bin_op) },
        }, expr_id);
    }

    /// Desugars `lhs catch [|err|] fallback` into `hir_match` (`DR-13` §2.2 Rule 3).
    fn lowerCatchExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const lhs_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;
        const rhs_id = if (ast_node.rhs.tag == .node) NodeIndex.fromInt(ast_node.rhs.payload) else .none;

        var lhs_hir = try self.lowerExpr(lhs_id, .err_ty);
        const raw_lhs_ty = self.store.getNode(lhs_hir).type_id;
        const lhs_ty = self.pool.unwrapUnderlyingType(raw_lhs_ty);
        if (lhs_ty != raw_lhs_ty) {
            lhs_hir = try self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = lhs_ty,
                .origin_token = tok,
                .data = .{ .lhs = lhs_hir.asInt(), .rhs = @backingInt(HirCastKind.distinct_unwrap) },
            }, .none);
        }
        const lhs_ty_node = self.pool.getNode(lhs_ty);
        const is_optional = lhs_ty_node.tag == .optional_ty;
        const ok_ty = self.concreteType(TypeId.fromInt(lhs_ty_node.lhs));
        const err_payload_ty = if (lhs_ty_node.tag == .result_ty)
            self.concreteType(TypeId.fromInt(lhs_ty_node.rhs))
        else
            .unit_ty;

        const ok_local = try self.allocTempLocal(ok_ty, tok, false);
        const ok_bind = try self.store.appendPat(.{
            .type_id = ok_ty,
            .origin_token = tok,
            .kind = .{ .bind = .{ .local_id = ok_local, .is_mut = false, .is_ref = false } },
        });
        const ok_sub = try self.store.appendExtraSlice(&[1]u32{ok_bind});
        const ok_pat = try self.store.appendPat(.{
            .type_id = lhs_ty,
            .origin_token = tok,
            .kind = .{
                .variant = .{
                    .tag_ordinal = if (is_optional) 1 else 0,
                    .payload_ty = ok_ty,
                    .sub_start = ok_sub,
                    .sub_len = 1,
                },
            },
        });

        const local_checkpoint = self.local_shadow_log.items.len;
        defer self.popLexicalLocalsTo(local_checkpoint);

        const cap_tok = self.extractCatchCaptureToken(expr_id, tok);
        var err_pat: u32 = 0;
        if (is_optional) {
            err_pat = try self.store.appendPat(.{
                .type_id = lhs_ty,
                .origin_token = tok,
                .kind = .{ .variant = .{ .tag_ordinal = 0, .payload_ty = .unit_ty, .sub_start = 0, .sub_len = 0 } },
            });
        } else {
            const cap_name = if (!cap_tok.isNone())
                symbol_resolver.extractTokenSlice(self.source, self.tokens, cap_tok)
            else
                "";
            const cap_sym_id = if (cap_name.len > 0 and !std.mem.eql(u8, cap_name, "_"))
                try self.interner.intern(cap_name)
            else
                SymbolId.empty;
            const err_slot = try self.store.appendLocal(.{
                .name = cap_sym_id,
                .type_id = err_payload_ty,
                .decl_span = if (!cap_tok.isNone())
                    self.tokens.getTokenSpan(self.store.file_id, cap_tok)
                else
                    self.astSpan(expr_id),
                .mode = .let_mode,
                .is_mut = false,
                .is_param = false,
                .is_temp = cap_sym_id == .empty,
            });
            try self.pushLexicalLocal(cap_sym_id, err_slot);
            const err_bind = try self.store.appendPat(.{
                .type_id = err_payload_ty,
                .origin_token = tok,
                .kind = .{ .bind = .{ .local_id = err_slot, .is_mut = false, .is_ref = false } },
            });
            const err_sub = try self.store.appendExtraSlice(&[1]u32{err_bind});
            err_pat = try self.store.appendPat(.{
                .type_id = lhs_ty,
                .origin_token = tok,
                .kind = .{
                    .variant = .{
                        .tag_ordinal = 1,
                        .payload_ty = err_payload_ty,
                        .sub_start = err_sub,
                        .sub_len = 1,
                    },
                },
            });
        }

        const resolved_res_ty = if (!target_ty.isError()) target_ty else ok_ty;
        const fallback_hir = try self.lowerExpr(rhs_id, resolved_res_ty);

        const arm_start: u32 = @intCast(self.store.match_arms.items.len);
        try self.store.match_arms.append(self.allocator, .{
            .pat_idx = ok_pat,
            .guard_hir = .none,
            .body_hir = try self.emitVarRef(ok_local, tok, .none),
            .origin_token = tok,
        });
        try self.store.match_arms.append(self.allocator, .{
            .pat_idx = err_pat,
            .guard_hir = .none,
            .body_hir = fallback_hir,
            .origin_token = tok,
        });
        const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, 2 });
        return self.emitNode(.{
            .tag = .hir_match,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = resolved_res_ty,
            .origin_token = tok,
            .data = .{ .lhs = lhs_hir.asInt(), .rhs = match_extra },
        }, expr_id);
    }

    /// Lowers `.field_access` (`s.field`, `tup.0`, `.len`, `#soa` `items[i].x`, and `bit_field` `bf.member`).
    fn lowerFieldAccess(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .token) {
            return self.emitErrorHole(tok, expr_id, target_ty);
        }
        const recv_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const member_tok = TokenIndex.fromInt(ast_node.rhs.payload);
        const member_lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, member_tok);

        // [1] Fold compile-time `TypeInfo` / `FieldInfo` / `VariantInfo` member access directly:
        if (try self.tryEvalAstComptime(expr_id, target_ty)) |folded_meta| {
            const res_ty = if (!target_ty.isError()) target_ty else self.inferComptimeValType(folded_meta);
            return self.emitConstVal(folded_meta, res_ty, tok, expr_id, true);
        }

        const recv_ast = self.ast_arena.getNode(recv_id);

        // [2] Virtual zero-temporary `soa_zip` projection (`v.0` or `v.pos`, `DR-13` §2.2 Rule 5):
        if (recv_ast.tag == .ident_expr) {
            const recv_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, recv_ast.main_token);
            if (self.interner.lookup(recv_lex)) |recv_sym_id| {
                if (self.active_zip_bindings.get(recv_sym_id.asInt())) |zip_info| {
                    var matched_col: ?usize = null;
                    if (self.tokens.getToken(member_tok).kind == .int_lit) {
                        if (extractIntValue(member_lexeme)) |col_idx| {
                            if (col_idx >= 0 and col_idx < zip_info.seq_locals.len) {
                                matched_col = @intCast(col_idx);
                            }
                        }
                    } else if (self.interner.lookup(member_lexeme)) |label_id| {
                        for (zip_info.seq_labels, 0..) |seq_lbl, col_i| {
                            if (seq_lbl == label_id) {
                                matched_col = col_i;
                                break;
                            }
                        }
                    }
                    if (matched_col) |col_ord| {
                        const seq_slot = zip_info.seq_locals[col_ord];
                        const seq_ty = zip_info.seq_types[col_ord];
                        const unwrapped_seq = self.unwrapRefType(seq_ty);
                        const seq_ty_node = self.pool.getNode(unwrapped_seq);
                        const elem_ty = TypeId.fromInt(seq_ty_node.lhs);
                        const is_mut_seq = self.pool.getTag(seq_ty) == .mut_ref_ty or
                            ((seq_ty_node.tag == .slice_ty or seq_ty_node.tag == .soa_slice_ty) and
                                seq_ty_node.rhs != 0) or
                            self.store.locals.items[seq_slot].is_mut;
                        const seq_base = if (seq_ty != unwrapped_seq)
                            try self.emitSyntheticDeref(
                                try self.emitVarRef(seq_slot, tok, .none),
                                unwrapped_seq,
                                tok,
                            )
                        else
                            try self.emitVarRef(seq_slot, tok, .none);
                        return self.emitNode(.{
                            .tag = .hir_index_proj,
                            .flags = .{
                                .category = if (is_mut_seq) .place_mut else .place_imm,
                                .is_synthetic = true,
                            },
                            .type_id = self.concreteType(elem_ty),
                            .origin_token = tok,
                            .data = .{
                                .lhs = seq_base.asInt(),
                                .rhs = (try self.emitVarRef(zip_info.idx_local, tok, .none)).asInt(),
                            },
                        }, expr_id);
                    }
                }
            }
        }

        // [3] Intercept `#soa` AoS-style element projection `items[i].field -> hir_soa_field_ptr` (`DR-13` §2.2 Rule 6):
        if (recv_ast.tag == .index_expr and recv_ast.lhs.tag == .node and recv_ast.rhs.tag == .node) {
            const soa_base_ast = NodeIndex.fromInt(recv_ast.lhs.payload);
            const idx_ast = NodeIndex.fromInt(recv_ast.rhs.payload);
            const raw_soa_ty = self.nodeType(soa_base_ast);
            const unwrapped_soa_ty = self.unwrapRefType(raw_soa_ty);
            const soa_tag = self.pool.getTag(unwrapped_soa_ty);
            if (soa_tag == .soa_slice_ty or soa_tag == .soa_array_ty) {
                return self.emitSoaElementFieldPtr(
                    soa_base_ast,
                    idx_ast,
                    unwrapped_soa_ty,
                    member_lexeme,
                    target_ty,
                    tok,
                    expr_id,
                );
            }
        }

        const raw_recv_hir = try self.lowerExpr(recv_id, .err_ty);
        if (self.tokens.getToken(member_tok).kind == .int_lit) {
            const ord: u32 = @intCast(@max(extractIntValue(member_lexeme) orelse 0, 0));
            const deref_base = try self.autoDerefPlace(raw_recv_hir, tok);
            const base_cat = self.store.getNode(deref_base).flags.category;
            return self.emitNode(.{
                .tag = .hir_field_proj,
                .flags = .{ .category = if (base_cat == .place_mut) .place_mut else .place_imm },
                .type_id = if (!target_ty.isError()) target_ty else .unit_ty,
                .origin_token = tok,
                .data = .{ .lhs = deref_base.asInt(), .rhs = ord },
            }, expr_id);
        }

        return self.projectNamedMember(raw_recv_hir, member_lexeme, tok, expr_id);
    }

    /// Emits `hir_field_proj` or `hir_bitfield_read` for `member_name` on `raw_recv_hir`.
    fn projectNamedMember(
        self: *HirLowerer,
        raw_recv_hir: HirIndex,
        member_name: []const u8,
        tok: TokenIndex,
        ast_origin: NodeIndex,
    ) !HirIndex {
        const raw_recv_ty = self.store.getNode(raw_recv_hir).type_id;
        const recv_ty = self.pool.unwrapUnderlyingType(self.unwrapRefType(raw_recv_ty));
        const recv_node = self.pool.getNode(recv_ty);

        if (std.mem.eql(u8, member_name, "len") and
            (recv_node.tag == .slice_ty or recv_node.tag == .array_ty or
                recv_node.tag == .soa_slice_ty or recv_node.tag == .soa_array_ty or recv_ty == .str_ty))
        {
            return self.emitSequenceLen(raw_recv_hir, raw_recv_ty, tok);
        }

        const deref_base = try self.autoDerefPlace(raw_recv_hir, tok);
        const base_cat = self.store.getNode(deref_base).flags.category;

        // `#soa [S]` column slice projection `items.field -> [FieldTy]`:
        if (recv_node.tag == .soa_slice_ty or recv_node.tag == .soa_array_ty) {
            const elem_ty = TypeId.fromInt(recv_node.lhs);
            if (self.findStructFieldInfo(elem_ty, member_name)) |f_info| {
                const col_slice_ty = try self.pool.internSlice(f_info.field_ty, base_cat == .place_mut);
                return self.emitNode(.{
                    .tag = .hir_field_proj,
                    .flags = .{ .category = .rvalue },
                    .type_id = col_slice_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = deref_base.asInt(), .rhs = f_info.ordinal },
                }, ast_origin);
            }
        }

        // LSB `bit_field` member read -> `hir_bitfield_read` (`DR-13` §2.2 Rule 7):
        if (recv_node.tag == .bit_field_ty) {
            if (self.computeBitFieldSpec(recv_ty, member_name)) |bf_info| {
                return self.emitNode(.{
                    .tag = .hir_bitfield_read,
                    .flags = .{ .category = .rvalue },
                    .type_id = self.concreteType(bf_info.field_ty),
                    .origin_token = tok,
                    .data = .{ .lhs = deref_base.asInt(), .rhs = bf_info.spec.asU32() },
                }, ast_origin);
            }
        }

        // Nominal `struct` or `union` field projection:
        if (self.findStructFieldInfo(recv_ty, member_name)) |f_info| {
            const proj_cat: ValueCategory = switch (base_cat) {
                .place_mut => .place_mut,
                .place_imm => .place_imm,
                else => .rvalue,
            };
            return self.emitNode(.{
                .tag = .hir_field_proj,
                .flags = .{ .category = proj_cat, .is_unsafe = self.is_in_unsafe or recv_node.tag == .union_ty },
                .type_id = self.concreteType(f_info.field_ty),
                .origin_token = tok,
                .data = .{ .lhs = deref_base.asInt(), .rhs = f_info.ordinal },
            }, ast_origin);
        }

        const fallback_ty = if (!ast_origin.isNone()) self.nodeType(ast_origin) else .unit_ty;
        return self.emitErrorHole(tok, ast_origin, fallback_ty);
    }

    /// Emits `hir_soa_field_ptr` shared by both `items[i].field` and `items.field[i]` (`DR-13` §2.2 Rule 6 & `MAJ-03`).
    fn emitSoaElementFieldPtr(
        self: *HirLowerer,
        soa_base_ast: NodeIndex,
        idx_ast: NodeIndex,
        unwrapped_soa_ty: TypeId,
        field_name: []const u8,
        target_ty: TypeId,
        tok: TokenIndex,
        ast_origin: NodeIndex,
    ) !HirIndex {
        const idx_hir = try self.lowerExpr(idx_ast, .usize_ty);
        const idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
        const idx_decl = try self.emitLocalDeclNode(idx_slot, idx_hir, tok);

        const raw_base_hir = try self.lowerExpr(soa_base_ast, .err_ty);
        const deref_base = try self.autoDerefPlace(raw_base_hir, tok);
        const elem_struct_ty = TypeId.fromInt(self.pool.getNode(unwrapped_soa_ty).lhs);
        const f_info = self.findStructFieldInfo(elem_struct_ty, field_name) orelse
            return self.emitErrorHole(tok, ast_origin, target_ty);

        const base_cat = self.store.getNode(deref_base).flags.category;
        const soa_node = self.pool.getNode(unwrapped_soa_ty);
        const is_mut_slice = (soa_node.tag == .soa_slice_ty and soa_node.rhs != 0) or base_cat == .place_mut;
        const idx_ref = try self.emitVarRef(idx_slot, tok, .none);
        const extra_idx = try self.store.appendExtraSlice(&[2]u32{ f_info.ordinal, idx_ref.asInt() });
        const field_ty = self.concreteType(f_info.field_ty);
        const soa_ptr = try self.emitNode(.{
            .tag = .hir_soa_field_ptr,
            .flags = .{
                .category = if (is_mut_slice) .place_mut else .place_imm,
                .is_synthetic = true,
            },
            .type_id = field_ty,
            .origin_token = tok,
            .data = .{ .lhs = deref_base.asInt(), .rhs = extra_idx },
        }, ast_origin);
        return self.emitSyntheticBlock(&[1]u32{idx_decl.asInt()}, soa_ptr, field_ty, tok);
    }

    /// Lowers `base[index]`, rewriting `#soa` `items.field[i]` to `hir_soa_field_ptr` and `subscript`s to `hir_subscript_call`.
    fn lowerIndexExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .node) {
            return self.emitErrorHole(tok, expr_id, target_ty);
        }
        const base_ast_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const idx_ast_id = NodeIndex.fromInt(ast_node.rhs.payload);
        const base_ast = self.ast_arena.getNode(base_ast_id);

        // [1] Intercept `#soa` columnar syntax `items.field[i] -> hir_soa_field_ptr` (`DR-13` §2.2 Rule 6):
        if (base_ast.tag == .field_access and base_ast.lhs.tag == .node and base_ast.rhs.tag == .token) {
            const soa_cand_ast = NodeIndex.fromInt(base_ast.lhs.payload);
            const unwrapped_soa_ty = self.unwrapRefType(self.nodeType(soa_cand_ast));
            const soa_tag = self.pool.getTag(unwrapped_soa_ty);
            if (soa_tag == .soa_slice_ty or soa_tag == .soa_array_ty) {
                const field_tok = TokenIndex.fromInt(base_ast.rhs.payload);
                const field_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, field_tok);
                return self.emitSoaElementFieldPtr(
                    soa_cand_ast,
                    idx_ast_id,
                    unwrapped_soa_ty,
                    field_name,
                    target_ty,
                    tok,
                    expr_id,
                );
            }
        }

        // [2] Check if `base` is a nominal type defining `subscript(&self, idx)`:
        const raw_base_ty = self.nodeType(base_ast_id);
        const unwrapped_base = self.unwrapRefType(raw_base_ty);
        if (try self.lookupMethodOnType(unwrapped_base, "subscript")) |sub_sym_idx| {
            const idx_hir = try self.lowerExpr(idx_ast_id, .usize_ty);
            const idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
            const idx_decl = try self.emitLocalDeclNode(idx_slot, idx_hir, tok);

            const base_hir = try self.lowerExpr(base_ast_id, .err_ty);
            const sub_sym = self.sym_table.getSymbol(sub_sym_idx).*;
            const sig_view = self.pool.getFnSignatureView(sub_sym.type_id);
            const recv_param_ty = if (sig_view) |sv| sv.getParamType(0) else raw_base_ty;
            const recv_mode = if (sig_view) |sv| sv.getParamMode(0) else .let_mode;
            const idx_mode = if (sig_view) |sv|
                (if (sv.paramCount() > 1) sv.getParamMode(1) else .let_mode)
            else
                .let_mode;

            const adjusted_recv = try self.adjustReceiverForParam(base_hir, recv_param_ty, tok);
            const proj_recv = try self.wrapArgProjection(adjusted_recv, recv_mode, tok);
            const proj_idx = try self.wrapArgProjection(try self.emitVarRef(idx_slot, tok, .none), idx_mode, tok);
            const callee_hir = try self.emitNode(.{
                .tag = .hir_global_ref,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = sub_sym.type_id,
                .origin_token = tok,
                .data = .{ .lhs = sub_sym.def_id.asInt(), .rhs = sub_sym_idx.asInt() },
            }, .none);
            const extra_idx = try self.store.appendLenPrefixedExtra(&[2]u32{ proj_recv.asInt(), proj_idx.asInt() });
            const ret_ty = if (!target_ty.isError())
                target_ty
            else if (sig_view) |sv|
                self.concreteType(sv.ret_ty)
            else
                .unit_ty;
            const sub_call = try self.emitNode(.{
                .tag = .hir_subscript_call,
                .flags = .{ .category = .place_imm, .is_synthetic = true },
                .type_id = ret_ty,
                .origin_token = tok,
                .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
            }, expr_id);
            return self.emitSyntheticBlock(&[1]u32{idx_decl.asInt()}, sub_call, ret_ty, tok);
        }

        // [3] Built-in array / slice / `#soa` element index projection (`DR-02` §2.2 post-arg sequencing: index then base):
        const idx_hir = try self.lowerExpr(idx_ast_id, .usize_ty);
        const idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
        const idx_decl = try self.emitLocalDeclNode(idx_slot, idx_hir, tok);

        const raw_base_hir = try self.lowerExpr(base_ast_id, .err_ty);
        const deref_base = try self.autoDerefPlace(raw_base_hir, tok);
        const base_node = self.store.getNode(deref_base);
        const base_ty_node = self.pool.getNode(base_node.type_id);
        const elem_ty = self.concreteType(if (!target_ty.isError())
            target_ty
        else switch (base_ty_node.tag) {
            .slice_ty, .soa_slice_ty, .array_ty, .soa_array_ty => TypeId.fromInt(base_ty_node.lhs),
            else => .unit_ty,
        });
        const is_mut_seq = base_node.flags.category == .place_mut or
            ((base_ty_node.tag == .slice_ty or base_ty_node.tag == .soa_slice_ty) and base_ty_node.rhs != 0);
        const idx_ref = try self.emitVarRef(idx_slot, tok, .none);
        const proj_hir = try self.emitNode(.{
            .tag = .hir_index_proj,
            .flags = .{ .category = if (is_mut_seq) .place_mut else .place_imm },
            .type_id = elem_ty,
            .origin_token = tok,
            .data = .{ .lhs = deref_base.asInt(), .rhs = idx_ref.asInt() },
        }, expr_id);
        return self.emitSyntheticBlock(&[1]u32{idx_decl.asInt()}, proj_hir, elem_ty, tok);
    }

    /// Lowers direct, generic, `@overload`, `subscript`, and `@intrinsic` calls (`DR-02` §2.2 & `DR-05` §3.3).
    fn lowerCallExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node) return self.emitErrorHole(tok, expr_id, target_ty);
        const callee_ast_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const callee_ast = self.ast_arena.getNode(callee_ast_id);

        const raw_items = self.getAstExtraSlice(expr_id, true);
        var type_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer type_arg_nodes.deinit(self.allocator);
        var val_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer val_arg_nodes.deinit(self.allocator);
        if (ast_node.rhs.tag == .node) {
            try val_arg_nodes.append(self.allocator, NodeIndex.fromInt(ast_node.rhs.payload));
        } else {
            for (raw_items) |raw_item| {
                const item_id = NodeIndex.fromInt(raw_item);
                if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
                if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) {
                    try type_arg_nodes.append(self.allocator, item_id);
                } else {
                    try val_arg_nodes.append(self.allocator, item_id);
                }
            }
        }
        const val_args = val_arg_nodes.items;

        // [1] Compiler `@intrinsic` invocation:
        if (callee_ast.tag == .ident_expr and !callee_ast.main_token.isNone() and
            self.tokens.getToken(callee_ast.main_token).kind == .at)
        {
            return self.lowerIntrinsicCall(
                expr_id,
                callee_ast_id,
                type_arg_nodes.items,
                val_args,
                target_ty,
            );
        }

        // [2] Enum tuple-variant constructor `Enum::Variant(a, b)` resolved via `nodeSymbol` or lexical fallback:
        const call_sym_idx = self.nodeSymbol(expr_id);
        var resolved_sym_idx = if (!call_sym_idx.isNone()) call_sym_idx else self.nodeSymbol(callee_ast_id);
        if (resolved_sym_idx.isNone() and callee_ast.tag == .ident_expr and !callee_ast.main_token.isNone()) {
            const callee_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, callee_ast.main_token);
            if (self.interner.lookup(callee_lex)) |callee_id| {
                if (!self.active_name_to_local.contains(callee_id.asInt())) {
                    switch (self.sym_table.lookupLexical(self.current_scope, callee_id, NamespaceMask.VALUE_ONLY)) {
                        .found => |found_sym| resolved_sym_idx = found_sym,
                        else => {},
                    }
                }
            }
        }
        if (!resolved_sym_idx.isNone()) {
            const sym = self.sym_table.getSymbol(resolved_sym_idx).*;
            if (sym.kind == .enum_variant_sym) {
                var arg_hirs: std.ArrayListUnmanaged(u32) = .empty;
                defer arg_hirs.deinit(self.allocator);
                if (val_args.len == 1) {
                    try arg_hirs.append(self.allocator, (try self.lowerExpr(val_args[0], sym.type_id)).asInt());
                } else {
                    const tup_elems = self.pool.getTupleElements(sym.type_id);
                    for (val_args, 0..) |arg_id, i| {
                        const sub_ty = if (i < tup_elems.len) TypeId.fromInt(tup_elems[i]) else .err_ty;
                        try arg_hirs.append(self.allocator, (try self.lowerExpr(arg_id, sub_ty)).asInt());
                    }
                }
                const extra_idx = try self.store.appendLenPrefixedExtra(arg_hirs.items);
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue },
                    .type_id = self.concreteType(target_ty),
                    .origin_token = tok,
                    .data = .{
                        .lhs = @as(u32, @backingInt(HirConstructKind.enum_variant)) |
                            (@as(u32, sym.member_ordinal) << 8),
                        .rhs = extra_idx,
                    },
                }, expr_id);
            }
        }

        // [3] Resolve concrete `@overload` or direct function symbol if available:
        const is_direct_sym = !resolved_sym_idx.isNone() and
            self.sym_table.getSymbol(resolved_sym_idx).kind == .fn_sym;
        const callee_sig_ty = if (is_direct_sym)
            self.sym_table.getSymbol(resolved_sym_idx).type_id
        else
            self.nodeType(callee_ast_id);
        const sig_view = self.pool.getFnSignatureView(callee_sig_ty);

        var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer seq_stmts.deinit(self.allocator);
        var wrapped_args: std.ArrayListUnmanaged(u32) = .empty;
        defer wrapped_args.deinit(self.allocator);

        for (val_args, 0..) |arg_id, i| {
            const p_ty = if (sig_view) |sv|
                (if (i < sv.paramCount()) sv.getParamType(i) else .err_ty)
            else
                .err_ty;
            const p_mode = if (sig_view) |sv|
                (if (i < sv.paramCount()) sv.getParamMode(i) else .let_mode)
            else
                .let_mode;
            var arg_hir = try self.lowerExpr(arg_id, p_ty);
            if (!is_direct_sym and p_mode == .let_mode) {
                const tmp_slot = try self.allocTempLocal(self.store.getNode(arg_hir).type_id, tok, false);
                try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(tmp_slot, arg_hir, tok)).asInt());
                arg_hir = try self.emitVarRef(tmp_slot, tok, .none);
            }
            try wrapped_args.append(self.allocator, (try self.wrapArgProjection(arg_hir, p_mode, tok)).asInt());
        }

        const callee_hir = if (is_direct_sym) blk: {
            const fn_sym = self.sym_table.getSymbol(resolved_sym_idx).*;
            break :blk try self.emitNode(.{
                .tag = .hir_global_ref,
                .flags = .{ .category = .rvalue },
                .type_id = fn_sym.type_id,
                .origin_token = tok,
                .data = .{ .lhs = fn_sym.def_id.asInt(), .rhs = resolved_sym_idx.asInt() },
            }, callee_ast_id);
        } else try self.lowerExpr(callee_ast_id, .err_ty);

        const ret_ty = if (!target_ty.isError())
            target_ty
        else if (sig_view) |sv|
            self.concreteType(sv.ret_ty)
        else
            .unit_ty;
        const extra_idx = try self.store.appendLenPrefixedExtra(wrapped_args.items);
        const is_sub = self.isCalleeSubscript(callee_hir);
        const call_hir = try self.emitNode(.{
            .tag = if (is_sub) .hir_subscript_call else .hir_call,
            .flags = .{
                .category = if (is_sub) .place_imm else .rvalue,
                .is_unsafe = self.is_in_unsafe,
            },
            .type_id = ret_ty,
            .origin_token = tok,
            .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
        }, expr_id);

        if (seq_stmts.items.len > 0) {
            return self.emitSyntheticBlock(seq_stmts.items, call_hir, ret_ty, tok);
        }
        return call_hir;
    }

    /// Lowers all 12 Phase 5 `@intrinsic` calls (`DR-05` Deliverable 2), folding reflection queries eagerly when concrete.
    fn lowerIntrinsicCall(
        self: *HirLowerer,
        call_id: NodeIndex,
        callee_id: NodeIndex,
        type_arg_nodes: []const NodeIndex,
        val_args: []const NodeIndex,
        target_ty: TypeId,
    ) !HirIndex {
        const callee_node = self.ast_arena.getNode(callee_id);
        const intr_tok = if (callee_node.lhs.tag == .token)
            TokenIndex.fromInt(callee_node.lhs.payload)
        else
            callee_node.main_token;
        const intr_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, intr_tok);
        const intr_kind = parseIntrinsicName(intr_name) orelse
            return self.emitErrorHole(intr_tok, call_id, target_ty);

        const t_cap = @max(type_arg_nodes.len, 1);
        var type_args = try self.allocator.alloc(TypeId, t_cap);
        defer self.allocator.free(type_args);
        @memset(type_args, .unit_ty);
        if (self.side_tables) |tables| {
            if (tables.getCallInstantiation(call_id)) |inst_slice| {
                for (inst_slice[0..@min(inst_slice.len, type_args.len)], 0..) |inst_ty, i| {
                    type_args[i] = inst_ty;
                }
            }
        }
        for (type_arg_nodes, 0..) |t_node_id, i| {
            if (type_args[i] == .unit_ty) {
                const n_ty = self.nodeType(t_node_id);
                if (!n_ty.isError()) type_args[i] = n_ty;
            }
        }

        // [1] `@field(target, comptime field_spec)` -> direct `hir_field_proj` / `hir_bitfield_read` (`DR-05` Tier-1):
        if (intr_kind == .field and val_args.len >= 2) {
            const base_hir = try self.lowerExpr(val_args[0], .err_ty);
            if (try self.tryEvalAstComptime(val_args[1], .err_ty)) |spec_val| {
                if (spec_val == .str_val) {
                    return self.projectNamedMember(base_hir, self.interner.get(spec_val.str_val), intr_tok, call_id);
                }
                if (spec_val == .field_info_mirror) {
                    return self.projectNamedMember(
                        base_hir,
                        self.interner.get(spec_val.field_info_mirror.field_name),
                        intr_tok,
                        call_id,
                    );
                }
            }
        }

        // [2] `@default_init[T]()` -> canonical zero/default aggregate value:
        if (intr_kind == .default_init and type_arg_nodes.len >= 1) {
            const init_ty = if (!target_ty.isError()) target_ty else type_args[0];
            return self.emitDefaultInitValue(init_ty, intr_tok);
        }

        // [3] `@compile_assert(cond, [msg])` inside unrolled `comptime for` / `comptime if`:
        if (intr_kind == .compile_assert and val_args.len >= 1) {
            if (try self.tryEvalAstComptime(val_args[0], .bool_ty)) |cond_val| {
                if (cond_val == .bool_val and !cond_val.bool_val) {
                    var msg_text: []const u8 = "compile-time assertion failed";
                    if (val_args.len >= 2) {
                        if (try self.tryEvalAstComptime(val_args[1], .str_ty)) |m_val| {
                            if (m_val == .str_val) msg_text = self.interner.get(m_val.str_val);
                        }
                    }
                    try self.emitDiagnostic(.e0510_compile_assertion_failed, self.astSpan(call_id), msg_text, "failed here");
                }
                return self.emitUnitConst(intr_tok, call_id);
            }
        }

        // [4] `@compile_error(msg)` inside unrolled `comptime` branch:
        if (intr_kind == .compile_error and val_args.len >= 1) {
            var err_text: []const u8 = "explicit `@compile_error` triggered";
            if (try self.tryEvalAstComptime(val_args[0], .str_ty)) |m_val| {
                if (m_val == .str_val) err_text = self.interner.get(m_val.str_val);
            }
            try self.emitDiagnostic(.e0510_compile_assertion_failed, self.astSpan(call_id), err_text, "triggered here");
            return self.emitErrorHole(intr_tok, call_id, .never_ty);
        }

        // [5] Fold concrete Tier-1 reflection intrinsics (`@size_of`, `@align_of`, `@type_name`, `@has_field`, `@implements`, `@field_attr_lookup`):
        if (try self.tryEvalAstComptime(call_id, target_ty)) |folded_intr| {
            const res_ty = if (!target_ty.isError()) target_ty else self.inferComptimeValType(folded_intr);
            return self.emitConstVal(folded_intr, res_ty, intr_tok, call_id, true);
        }

        // [6] Emit `hir_intrinsic_call` for polymorphic or `MirVm`-evaluated intrinsics (`CRIT-11`):
        var payload_words: std.ArrayListUnmanaged(u32) = .empty;
        defer payload_words.deinit(self.allocator);
        try payload_words.append(self.allocator, @intCast(type_arg_nodes.len));
        try payload_words.append(self.allocator, @intCast(val_args.len));
        for (0..type_arg_nodes.len) |i| {
            try payload_words.append(self.allocator, type_args[i].toU32());
        }
        for (val_args) |v_arg_id| {
            try payload_words.append(self.allocator, (try self.lowerExpr(v_arg_id, .err_ty)).asInt());
        }
        const extra_idx = try self.store.appendExtraSlice(payload_words.items);
        const res_ty = if (!target_ty.isError()) target_ty else .unit_ty;
        return self.emitNode(.{
            .tag = .hir_intrinsic_call,
            .flags = .{ .category = if (res_ty == .never_ty) .diverging else .rvalue },
            .type_id = self.concreteType(res_ty),
            .origin_token = intr_tok,
            .data = .{ .lhs = @backingInt(intr_kind), .rhs = extra_idx },
        }, call_id);
    }

    /// Lowers `receiver.method(a_1, …, a_k)` enforcing Hylo Post-Argument Receiver Sequencing (`DR-02` §2.2).
    fn lowerMethodCallExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node) return self.emitErrorHole(tok, expr_id, target_ty);
        const recv_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const raw_items = self.getAstExtraSlice(expr_id, true);
        if (raw_items.len == 0) return self.emitErrorHole(tok, expr_id, target_ty);

        const member_tok = TokenIndex.fromInt(raw_items[0]);
        const member_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, member_tok);

        var val_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer val_arg_nodes.deinit(self.allocator);
        for (raw_items[1..]) |raw_item| {
            const item_id = NodeIndex.fromInt(raw_item);
            if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
            if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) continue;
            try val_arg_nodes.append(self.allocator, item_id);
        }
        const val_args = val_arg_nodes.items;

        // Built-in `.len()` method on slices, arrays, `#soa`, and `str`:
        if (val_args.len == 0 and std.mem.eql(u8, member_name, "len")) {
            const raw_recv_ty = self.nodeType(recv_id);
            const unwrapped_recv = self.unwrapRefType(raw_recv_ty);
            const recv_tag = self.pool.getTag(unwrapped_recv);
            if (recv_tag == .slice_ty or recv_tag == .array_ty or
                recv_tag == .soa_slice_ty or recv_tag == .soa_array_ty or unwrapped_recv == .str_ty)
            {
                const recv_hir = try self.lowerExpr(recv_id, .err_ty);
                return self.emitSequenceLen(recv_hir, self.store.getNode(recv_hir).type_id, tok);
            }
        }

        var method_sym_idx = self.nodeSymbol(expr_id);
        if (method_sym_idx.isNone()) {
            const recv_ty = self.unwrapRefType(self.nodeType(recv_id));
            if (try self.lookupMethodOnType(recv_ty, member_name)) |found_m| {
                method_sym_idx = found_m;
            }
        }
        if (method_sym_idx.isNone()) return self.emitErrorHole(tok, expr_id, target_ty);

        const method_sym = self.sym_table.getSymbol(method_sym_idx).*;
        const sig_view = self.pool.getFnSignatureView(method_sym.type_id);

        // [1] Evaluate explicit arguments `a_1 .. a_k` strictly left-to-right BEFORE projecting `receiver` (`DR-02` §2.2):
        var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer seq_stmts.deinit(self.allocator);
        var arg_temps = try self.allocator.alloc(u32, val_args.len);
        defer self.allocator.free(arg_temps);

        for (val_args, 0..) |arg_id, i| {
            const param_idx = i + 1;
            const p_ty = if (sig_view) |sv|
                (if (param_idx < sv.paramCount()) sv.getParamType(param_idx) else .err_ty)
            else
                .err_ty;
            const arg_hir = try self.lowerExpr(arg_id, p_ty);
            const tmp_slot = try self.allocTempLocal(self.store.getNode(arg_hir).type_id, tok, false);
            try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(tmp_slot, arg_hir, tok)).asInt());
            arg_temps[i] = tmp_slot;
        }

        // [2] Now evaluate and project `receiver` (auto-referencing `&recv` / `&mut recv` when required by `self` param):
        const raw_recv_hir = try self.lowerExpr(recv_id, .err_ty);
        const self_param_ty = if (sig_view) |sv|
            (if (sv.paramCount() > 0) sv.getParamType(0) else self.store.getNode(raw_recv_hir).type_id)
        else
            self.store.getNode(raw_recv_hir).type_id;
        const self_mode = if (sig_view) |sv|
            (if (sv.paramCount() > 0) sv.getParamMode(0) else .let_mode)
        else
            .let_mode;
        const adjusted_recv = try self.adjustReceiverForParam(raw_recv_hir, self_param_ty, tok);

        var wrapped_args = try self.allocator.alloc(u32, val_args.len + 1);
        defer self.allocator.free(wrapped_args);
        wrapped_args[0] = (try self.wrapArgProjection(adjusted_recv, self_mode, tok)).asInt();
        for (0..val_args.len) |i| {
            const param_idx = i + 1;
            const p_mode = if (sig_view) |sv|
                (if (param_idx < sv.paramCount()) sv.getParamMode(param_idx) else .let_mode)
            else
                .let_mode;
            const arg_ref = try self.emitVarRef(arg_temps[i], tok, .none);
            wrapped_args[i + 1] = (try self.wrapArgProjection(arg_ref, p_mode, tok)).asInt();
        }

        const callee_hir = try self.emitNode(.{
            .tag = .hir_global_ref,
            .flags = .{ .category = .rvalue },
            .type_id = method_sym.type_id,
            .origin_token = tok,
            .data = .{ .lhs = method_sym.def_id.asInt(), .rhs = method_sym_idx.asInt() },
        }, .none);
        const extra_idx = try self.store.appendLenPrefixedExtra(wrapped_args);
        const ret_ty = if (!target_ty.isError())
            target_ty
        else if (sig_view) |sv|
            self.concreteType(sv.ret_ty)
        else
            .unit_ty;
        const call_hir = try self.emitNode(.{
            .tag = if (self.isCalleeSubscript(callee_hir)) .hir_subscript_call else .hir_call,
            .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
            .type_id = ret_ty,
            .origin_token = tok,
            .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
        }, expr_id);

        if (seq_stmts.items.len > 0) {
            return self.emitSyntheticBlock(seq_stmts.items, call_hir, ret_ty, tok);
        }
        return call_hir;
    }

    /// Lowers `if` / `else` and `comptime if`, pruning untaken branches statically when `is_comptime_if` is set.
    fn lowerIfExpr(
        self: *HirLowerer,
        expr_id: NodeIndex,
        target_ty: TypeId,
        is_comptime_if: bool,
    ) anyerror!HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const cond_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;

        var then_id: NodeIndex = .none;
        var else_id: NodeIndex = .none;
        if (ast_node.rhs.tag == .node) {
            then_id = NodeIndex.fromInt(ast_node.rhs.payload);
        } else {
            const branches = self.getAstExtraSlice(expr_id, true);
            if (branches.len >= 1) then_id = NodeIndex.fromInt(branches[0]);
            if (branches.len >= 2) else_id = NodeIndex.fromInt(branches[1]);
        }

        if (is_comptime_if and !cond_id.isNone()) {
            if (try self.tryEvalAstComptime(cond_id, .bool_ty)) |cond_val| {
                const is_taken = switch (cond_val) {
                    .bool_val => |flag| flag,
                    .int_val => |num| num != 0,
                    else => false,
                };
                if (is_taken) {
                    return self.lowerBlockExpr(then_id, target_ty, false);
                }
                if (else_id.isNone()) {
                    return self.emitUnitConst(tok, expr_id);
                }
                if (self.ast_arena.getNode(else_id).tag == .if_expr) {
                    return self.lowerIfExpr(else_id, target_ty, true);
                }
                return self.lowerBlockExpr(else_id, target_ty, false);
            }
        }

        return self.lowerConditionBranch(
            cond_id,
            self.ast_arena.getCstOrigin(expr_id),
            then_id,
            else_id,
            .none,
            if (!target_ty.isError()) target_ty else .unit_ty,
            tok,
            expr_id,
        );
    }

    /// Flattens top-level `.kw_and` / `.ampamp` conjunctions left-to-right for `if a is Pat and guard` (`CRIT-08`).
    fn collectConjunctiveClauses(
        self: *const HirLowerer,
        cond_id: NodeIndex,
        out_clauses: *std.ArrayListUnmanaged(NodeIndex),
        has_is_out: *bool,
    ) !void {
        if (cond_id.isNone() or cond_id.asInt() >= self.ast_arena.countNodes()) return;
        const node = self.ast_arena.getNode(cond_id);
        if (node.tag == .binary_expr and node.lhs.tag == .node and node.rhs.tag == .node and
            !node.main_token.isNone() and node.main_token.asInt() < self.tokens.countTokens())
        {
            const op_kind = self.tokens.getToken(node.main_token).kind;
            if (op_kind == .kw_and or op_kind == .ampamp) {
                try self.collectConjunctiveClauses(
                    NodeIndex.fromInt(node.lhs.payload),
                    out_clauses,
                    has_is_out,
                );
                try self.collectConjunctiveClauses(
                    NodeIndex.fromInt(node.rhs.payload),
                    out_clauses,
                    has_is_out,
                );
                return;
            }
            if (op_kind == .kw_is) has_is_out.* = true;
        }
        try out_clauses.append(self.allocator, cond_id);
    }

    /// Shared condition lowering for `if` and `while` (`if let`, `if opt |cap|`, `if x is Pat`, and boolean `hir_if`).
    fn lowerConditionBranch(
        self: *HirLowerer,
        cond_id: NodeIndex,
        enclosing_cst: CstNodeIndex,
        then_id: NodeIndex,
        else_ast_id: NodeIndex,
        synthetic_else_hir: HirIndex,
        res_ty: TypeId,
        tok: TokenIndex,
        ast_origin: NodeIndex,
    ) anyerror!HirIndex {
        if (cond_id.isNone() or cond_id.asInt() >= self.ast_arena.countNodes()) {
            return self.emitUnitConst(tok, ast_origin);
        }
        if (self.is_in_comptime_for) self.comptime_runtime_cond_depth += 1;
        defer if (self.is_in_comptime_for) {
            self.comptime_runtime_cond_depth -= 1;
        };

        const cond_node = self.ast_arena.getNode(cond_id);

        // [1] `if let pat = scrutinee` / `while let pat = scrutinee`:
        if (cond_node.tag == .binary_expr and cond_node.lhs.tag == .extra) {
            const pair = self.getAstExtraSlice(cond_id, false);
            const pat_id = if (pair.len >= 1) NodeIndex.fromInt(pair[0]) else .none;
            const scrut_id = if (pair.len >= 2) NodeIndex.fromInt(pair[1]) else .none;
            const scrut_hir = try self.lowerExpr(scrut_id, .err_ty);
            const scrut_ty = self.store.getNode(scrut_hir).type_id;

            const then_hir = blk: {
                const local_checkpoint = self.local_shadow_log.items.len;
                defer self.popLexicalLocalsTo(local_checkpoint);
                const pat_idx = try self.lowerTopPattern(pat_id, scrut_ty, false);
                const body_hir = try self.lowerBlockExpr(then_id, res_ty, false);
                const arm_start: u32 = @intCast(self.store.match_arms.items.len);
                try self.store.match_arms.append(self.allocator, .{
                    .pat_idx = pat_idx,
                    .guard_hir = .none,
                    .body_hir = body_hir,
                    .origin_token = tok,
                });
                break :blk arm_start;
            };

            const else_hir = if (!synthetic_else_hir.isNone())
                synthetic_else_hir
            else if (!else_ast_id.isNone())
                (if (self.ast_arena.getNode(else_ast_id).tag == .if_expr)
                    try self.lowerIfExpr(else_ast_id, res_ty, false)
                else
                    try self.lowerBlockExpr(else_ast_id, res_ty, false))
            else
                try self.emitUnitConst(tok, .none);

            const wild_pat = try self.store.appendPat(.{
                .type_id = scrut_ty,
                .origin_token = tok,
                .kind = .wildcard,
            });
            try self.store.match_arms.append(self.allocator, .{
                .pat_idx = wild_pat,
                .guard_hir = .none,
                .body_hir = else_hir,
                .origin_token = tok,
            });
            const match_extra = try self.store.appendExtraSlice(&[2]u32{ then_hir, 2 });
            return self.emitNode(.{
                .tag = .hir_match,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = self.concreteType(res_ty),
                .origin_token = tok,
                .data = .{ .lhs = scrut_hir.asInt(), .rhs = match_extra },
            }, ast_origin);
        }

        // [2] Optional/Result payload bar `if opt_val |cap| { … }`:
        const cap_info = self.extractConditionCaptureBar(enclosing_cst);
        if (!cap_info.token.isNone()) {
            const scrut_hir = try self.lowerExpr(cond_id, .err_ty);
            const scrut_ty = self.store.getNode(scrut_hir).type_id;
            const scr_node = self.pool.getNode(scrut_ty);
            const is_opt = scr_node.tag == .optional_ty;
            var payload_ty = self.concreteType(TypeId.fromInt(scr_node.lhs));
            if (cap_info.is_ref) payload_ty = try self.pool.internRef(payload_ty, false);

            const arm_start: u32 = @intCast(self.store.match_arms.items.len);
            {
                const local_checkpoint = self.local_shadow_log.items.len;
                defer self.popLexicalLocalsTo(local_checkpoint);
                const cap_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, cap_info.token);
                const cap_sym_id = if (cap_lex.len > 0 and !std.mem.eql(u8, cap_lex, "_"))
                    try self.interner.intern(cap_lex)
                else
                    SymbolId.empty;
                const cap_slot = try self.store.appendLocal(.{
                    .name = cap_sym_id,
                    .type_id = payload_ty,
                    .decl_span = self.tokens.getTokenSpan(self.store.file_id, cap_info.token),
                    .mode = .let_mode,
                    .is_mut = false,
                    .is_param = false,
                    .is_temp = cap_sym_id == .empty,
                });
                try self.pushLexicalLocal(cap_sym_id, cap_slot);
                const bind_pat = try self.store.appendPat(.{
                    .type_id = payload_ty,
                    .origin_token = cap_info.token,
                    .kind = .{ .bind = .{ .local_id = cap_slot, .is_mut = false, .is_ref = cap_info.is_ref } },
                });
                const sub_start = try self.store.appendExtraSlice(&[1]u32{bind_pat});
                const some_pat = try self.store.appendPat(.{
                    .type_id = scrut_ty,
                    .origin_token = tok,
                    .kind = .{
                        .variant = .{
                            .tag_ordinal = if (is_opt) 1 else 0,
                            .payload_ty = TypeId.fromInt(scr_node.lhs),
                            .sub_start = sub_start,
                            .sub_len = 1,
                        },
                    },
                });
                const then_hir = try self.lowerBlockExpr(then_id, res_ty, false);
                try self.store.match_arms.append(self.allocator, .{
                    .pat_idx = some_pat,
                    .guard_hir = .none,
                    .body_hir = then_hir,
                    .origin_token = tok,
                });
            }

            const else_hir = if (!synthetic_else_hir.isNone())
                synthetic_else_hir
            else if (!else_ast_id.isNone())
                (if (self.ast_arena.getNode(else_ast_id).tag == .if_expr)
                    try self.lowerIfExpr(else_ast_id, res_ty, false)
                else
                    try self.lowerBlockExpr(else_ast_id, res_ty, false))
            else
                try self.emitUnitConst(tok, .none);

            const wild_pat = try self.store.appendPat(.{
                .type_id = scrut_ty,
                .origin_token = tok,
                .kind = .wildcard,
            });
            try self.store.match_arms.append(self.allocator, .{
                .pat_idx = wild_pat,
                .guard_hir = .none,
                .body_hir = else_hir,
                .origin_token = tok,
            });
            const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, 2 });
            return self.emitNode(.{
                .tag = .hir_match,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = self.concreteType(res_ty),
                .origin_token = tok,
                .data = .{ .lhs = scrut_hir.asInt(), .rhs = match_extra },
            }, ast_origin);
        }

        // [3] Positive `if x is Pattern { … }` and conjunctive `if x is Pattern and guard { … }` (`CRIT-08`):
        if (cond_node.tag == .binary_expr and !cond_node.main_token.isNone()) {
            const top_op = self.tokens.getToken(cond_node.main_token).kind;
            if (top_op == .kw_is and cond_node.lhs.tag == .node and cond_node.rhs.tag == .node) {
                const scrut_hir = try self.lowerExpr(NodeIndex.fromInt(cond_node.lhs.payload), .err_ty);
                const scrut_ty = self.store.getNode(scrut_hir).type_id;
                const arm_start: u32 = @intCast(self.store.match_arms.items.len);
                {
                    const local_checkpoint = self.local_shadow_log.items.len;
                    defer self.popLexicalLocalsTo(local_checkpoint);
                    const pat_idx = try self.lowerTopPattern(NodeIndex.fromInt(cond_node.rhs.payload), scrut_ty, false);
                    const then_hir = try self.lowerBlockExpr(then_id, res_ty, false);
                    try self.store.match_arms.append(self.allocator, .{
                        .pat_idx = pat_idx,
                        .guard_hir = .none,
                        .body_hir = then_hir,
                        .origin_token = tok,
                    });
                }
                const else_hir = if (!synthetic_else_hir.isNone())
                    synthetic_else_hir
                else if (!else_ast_id.isNone())
                    (if (self.ast_arena.getNode(else_ast_id).tag == .if_expr)
                        try self.lowerIfExpr(else_ast_id, res_ty, false)
                    else
                        try self.lowerBlockExpr(else_ast_id, res_ty, false))
                else
                    try self.emitUnitConst(tok, .none);

                const wild_pat = try self.store.appendPat(.{
                    .type_id = scrut_ty,
                    .origin_token = tok,
                    .kind = .wildcard,
                });
                try self.store.match_arms.append(self.allocator, .{
                    .pat_idx = wild_pat,
                    .guard_hir = .none,
                    .body_hir = else_hir,
                    .origin_token = tok,
                });
                const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, 2 });
                return self.emitNode(.{
                    .tag = .hir_match,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = self.concreteType(res_ty),
                    .origin_token = tok,
                    .data = .{ .lhs = scrut_hir.asInt(), .rhs = match_extra },
                }, ast_origin);
            }

            if (top_op == .kw_and or top_op == .ampamp) {
                var clauses: std.ArrayListUnmanaged(NodeIndex) = .empty;
                defer clauses.deinit(self.allocator);
                var has_is_clause = false;
                try self.collectConjunctiveClauses(cond_id, &clauses, &has_is_clause);
                if (has_is_clause and clauses.items.len >= 2) {
                    const ConjStep = union(enum) {
                        is_pat: struct {
                            scrut_hir: HirIndex,
                            scrut_ty: TypeId,
                            pat_idx: u32,
                            clause_tok: TokenIndex,
                        },
                        bool_cond: struct {
                            cond_hir: HirIndex,
                            clause_tok: TokenIndex,
                        },
                    };
                    var steps: std.ArrayListUnmanaged(ConjStep) = .empty;
                    defer steps.deinit(self.allocator);

                    const has_else = !synthetic_else_hir.isNone() or !else_ast_id.isNone();
                    const concrete_res_ty = self.concreteType(res_ty);

                    if (!has_else) {
                        const local_checkpoint = self.local_shadow_log.items.len;
                        defer self.popLexicalLocalsTo(local_checkpoint);

                        for (clauses.items) |clause_id| {
                            const c_node = self.ast_arena.getNode(clause_id);
                            if (c_node.tag == .binary_expr and c_node.lhs.tag == .node and c_node.rhs.tag == .node and
                                !c_node.main_token.isNone() and
                                self.tokens.getToken(c_node.main_token).kind == .kw_is)
                            {
                                const scr_hir = try self.lowerExpr(NodeIndex.fromInt(c_node.lhs.payload), .err_ty);
                                const scr_ty = self.store.getNode(scr_hir).type_id;
                                const pat_idx = try self.lowerTopPattern(
                                    NodeIndex.fromInt(c_node.rhs.payload),
                                    scr_ty,
                                    false,
                                );
                                try steps.append(self.allocator, .{
                                    .is_pat = .{
                                        .scrut_hir = scr_hir,
                                        .scrut_ty = scr_ty,
                                        .pat_idx = pat_idx,
                                        .clause_tok = c_node.main_token,
                                    },
                                });
                            } else {
                                try steps.append(self.allocator, .{
                                    .bool_cond = .{
                                        .cond_hir = try self.lowerExpr(clause_id, .bool_ty),
                                        .clause_tok = c_node.main_token,
                                    },
                                });
                            }
                        }

                        var cur_hir = try self.lowerBlockExpr(then_id, .unit_ty, false);
                        var rev_i = steps.items.len;
                        while (rev_i > 0) {
                            rev_i -= 1;
                            switch (steps.items[rev_i]) {
                                .bool_cond => |bc| {
                                    const if_extra = try self.store.appendExtraSlice(&[2]u32{
                                        cur_hir.asInt(),
                                        HirIndex.none.asInt(),
                                    });
                                    cur_hir = try self.emitNode(.{
                                        .tag = .hir_if,
                                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                                        .type_id = .unit_ty,
                                        .origin_token = bc.clause_tok,
                                        .data = .{ .lhs = bc.cond_hir.asInt(), .rhs = if_extra },
                                    }, .none);
                                },
                                .is_pat => |ip| {
                                    const wild_pat = try self.store.appendPat(.{
                                        .type_id = ip.scrut_ty,
                                        .origin_token = ip.clause_tok,
                                        .kind = .wildcard,
                                    });
                                    const arm_start: u32 = @intCast(self.store.match_arms.items.len);
                                    try self.store.match_arms.append(self.allocator, .{
                                        .pat_idx = ip.pat_idx,
                                        .guard_hir = .none,
                                        .body_hir = cur_hir,
                                        .origin_token = ip.clause_tok,
                                    });
                                    try self.store.match_arms.append(self.allocator, .{
                                        .pat_idx = wild_pat,
                                        .guard_hir = .none,
                                        .body_hir = try self.emitUnitConst(ip.clause_tok, .none),
                                        .origin_token = ip.clause_tok,
                                    });
                                    const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, 2 });
                                    cur_hir = try self.emitNode(.{
                                        .tag = .hir_match,
                                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                                        .type_id = .unit_ty,
                                        .origin_token = ip.clause_tok,
                                        .data = .{ .lhs = ip.scrut_hir.asInt(), .rhs = match_extra },
                                    }, .none);
                                },
                            }
                        }
                        return cur_hir;
                    }

                    const done_loop_id = self.next_loop_id;
                    self.next_loop_id += 1;
                    const mismatch_loop_id = self.next_loop_id;
                    self.next_loop_id += 1;

                    const guarded_chain = blk: {
                        const local_checkpoint = self.local_shadow_log.items.len;
                        defer self.popLexicalLocalsTo(local_checkpoint);

                        for (clauses.items) |clause_id| {
                            const c_node = self.ast_arena.getNode(clause_id);
                            if (c_node.tag == .binary_expr and c_node.lhs.tag == .node and c_node.rhs.tag == .node and
                                !c_node.main_token.isNone() and
                                self.tokens.getToken(c_node.main_token).kind == .kw_is)
                            {
                                const scr_hir = try self.lowerExpr(NodeIndex.fromInt(c_node.lhs.payload), .err_ty);
                                const scr_ty = self.store.getNode(scr_hir).type_id;
                                const pat_idx = try self.lowerTopPattern(
                                    NodeIndex.fromInt(c_node.rhs.payload),
                                    scr_ty,
                                    false,
                                );
                                try steps.append(self.allocator, .{
                                    .is_pat = .{
                                        .scrut_hir = scr_hir,
                                        .scrut_ty = scr_ty,
                                        .pat_idx = pat_idx,
                                        .clause_tok = c_node.main_token,
                                    },
                                });
                            } else {
                                try steps.append(self.allocator, .{
                                    .bool_cond = .{
                                        .cond_hir = try self.lowerExpr(clause_id, .bool_ty),
                                        .clause_tok = c_node.main_token,
                                    },
                                });
                            }
                        }

                        const then_val = try self.lowerBlockExpr(then_id, concrete_res_ty, false);
                        var cur_hir = if (self.store.getNode(then_val).type_id == .never_ty)
                            then_val
                        else
                            try self.emitNode(.{
                                .tag = .hir_break,
                                .flags = .{ .category = .diverging, .is_synthetic = true },
                                .type_id = .never_ty,
                                .origin_token = tok,
                                .data = .{ .lhs = done_loop_id, .rhs = then_val.asInt() },
                            }, .none);

                        var rev_i = steps.items.len;
                        while (rev_i > 0) {
                            rev_i -= 1;
                            switch (steps.items[rev_i]) {
                                .bool_cond => |bc| {
                                    const break_miss = try self.emitNode(.{
                                        .tag = .hir_break,
                                        .flags = .{ .category = .diverging, .is_synthetic = true },
                                        .type_id = .never_ty,
                                        .origin_token = bc.clause_tok,
                                        .data = .{
                                            .lhs = mismatch_loop_id,
                                            .rhs = (try self.emitUnitConst(bc.clause_tok, .none)).asInt(),
                                        },
                                    }, .none);
                                    const if_extra = try self.store.appendExtraSlice(&[2]u32{
                                        cur_hir.asInt(),
                                        break_miss.asInt(),
                                    });
                                    cur_hir = try self.emitNode(.{
                                        .tag = .hir_if,
                                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                                        .type_id = .unit_ty,
                                        .origin_token = bc.clause_tok,
                                        .data = .{ .lhs = bc.cond_hir.asInt(), .rhs = if_extra },
                                    }, .none);
                                },
                                .is_pat => |ip| {
                                    const break_miss = try self.emitNode(.{
                                        .tag = .hir_break,
                                        .flags = .{ .category = .diverging, .is_synthetic = true },
                                        .type_id = .never_ty,
                                        .origin_token = ip.clause_tok,
                                        .data = .{
                                            .lhs = mismatch_loop_id,
                                            .rhs = (try self.emitUnitConst(ip.clause_tok, .none)).asInt(),
                                        },
                                    }, .none);
                                    const wild_pat = try self.store.appendPat(.{
                                        .type_id = ip.scrut_ty,
                                        .origin_token = ip.clause_tok,
                                        .kind = .wildcard,
                                    });
                                    const arm_start: u32 = @intCast(self.store.match_arms.items.len);
                                    try self.store.match_arms.append(self.allocator, .{
                                        .pat_idx = ip.pat_idx,
                                        .guard_hir = .none,
                                        .body_hir = cur_hir,
                                        .origin_token = ip.clause_tok,
                                    });
                                    try self.store.match_arms.append(self.allocator, .{
                                        .pat_idx = wild_pat,
                                        .guard_hir = .none,
                                        .body_hir = break_miss,
                                        .origin_token = ip.clause_tok,
                                    });
                                    const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, 2 });
                                    cur_hir = try self.emitNode(.{
                                        .tag = .hir_match,
                                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                                        .type_id = .unit_ty,
                                        .origin_token = ip.clause_tok,
                                        .data = .{ .lhs = ip.scrut_hir.asInt(), .rhs = match_extra },
                                    }, .none);
                                },
                            }
                        }
                        break :blk cur_hir;
                    };

                    const mismatch_loop = try self.emitNode(.{
                        .tag = .hir_loop,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = guarded_chain.asInt(), .rhs = mismatch_loop_id },
                    }, .none);

                    const else_val = if (!synthetic_else_hir.isNone())
                        synthetic_else_hir
                    else if (self.ast_arena.getNode(else_ast_id).tag == .if_expr)
                        try self.lowerIfExpr(else_ast_id, concrete_res_ty, false)
                    else
                        try self.lowerBlockExpr(else_ast_id, concrete_res_ty, false);

                    const else_exit = if (self.store.getNode(else_val).type_id == .never_ty)
                        else_val
                    else
                        try self.emitNode(.{
                            .tag = .hir_break,
                            .flags = .{ .category = .diverging, .is_synthetic = true },
                            .type_id = .never_ty,
                            .origin_token = tok,
                            .data = .{ .lhs = done_loop_id, .rhs = else_val.asInt() },
                        }, .none);

                    const done_body = try self.emitSyntheticBlock(
                        &[1]u32{mismatch_loop.asInt()},
                        else_exit,
                        .never_ty,
                        tok,
                    );
                    return self.emitNode(.{
                        .tag = .hir_loop,
                        .flags = .{
                            .category = if (concrete_res_ty == .never_ty) .diverging else .rvalue,
                            .is_synthetic = true,
                        },
                        .type_id = concrete_res_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = done_body.asInt(), .rhs = done_loop_id },
                    }, ast_origin);
                }
            }
        }

        // [4] Standard boolean `hir_if`:
        const cond_hir = try self.lowerExpr(cond_id, .bool_ty);
        const then_hir = try self.lowerBlockExpr(then_id, res_ty, false);
        const else_hir = if (!synthetic_else_hir.isNone())
            synthetic_else_hir
        else if (!else_ast_id.isNone())
            (if (self.ast_arena.getNode(else_ast_id).tag == .if_expr)
                try self.lowerIfExpr(else_ast_id, res_ty, false)
            else
                try self.lowerBlockExpr(else_ast_id, res_ty, false))
        else
            HirIndex.none;

        const extra_idx = try self.store.appendExtraSlice(&[2]u32{ then_hir.asInt(), else_hir.asInt() });
        return self.emitNode(.{
            .tag = .hir_if,
            .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
            .type_id = self.concreteType(res_ty),
            .origin_token = tok,
            .data = .{ .lhs = cond_hir.asInt(), .rhs = extra_idx },
        }, ast_origin);
    }

    /// Lowers `match scrutinee { arms… }`, statically selecting the matching arm when `is_comptime_match` is set.
    fn lowerMatchExpr(
        self: *HirLowerer,
        expr_id: NodeIndex,
        target_ty: TypeId,
        is_comptime_match: bool,
    ) anyerror!HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const scrutinee_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;
        const arm_entries = self.getAstExtraSlice(expr_id, true);
        const arm_count = arm_entries.len / 2;

        var arm_guards = try self.allocator.alloc(NodeIndex, arm_count);
        defer self.allocator.free(arm_guards);
        @memset(arm_guards, .none);
        self.extractMatchArmGuards(expr_id, arm_guards);

        if (is_comptime_match and !scrutinee_id.isNone()) {
            if (try self.tryEvalAstComptime(scrutinee_id, .err_ty)) |scrut_val| {
                const ct_scrut_ty = self.nodeType(scrutinee_id);
                for (0..arm_count) |arm_i| {
                    const pat_ast_id = NodeIndex.fromInt(arm_entries[arm_i * 2]);
                    const body_ast_id = NodeIndex.fromInt(arm_entries[arm_i * 2 + 1]);
                    const ct_checkpoint = self.comptime_shadow_log.items.len;
                    if (try self.matchComptimePattern(pat_ast_id, scrut_val, ct_scrut_ty)) {
                        var is_guard_ok = true;
                        if (arm_i < arm_guards.len and !arm_guards[arm_i].isNone()) {
                            if (try self.tryEvalAstComptime(arm_guards[arm_i], .bool_ty)) |g_val| {
                                is_guard_ok = (g_val == .bool_val and g_val.bool_val);
                            } else {
                                is_guard_ok = false;
                            }
                        }
                        if (is_guard_ok) {
                            defer self.popComptimeBindingsTo(ct_checkpoint);
                            return self.lowerExpr(body_ast_id, target_ty);
                        }
                    }
                    self.popComptimeBindingsTo(ct_checkpoint);
                }
            }
        }

        const scrut_hir = try self.lowerExpr(scrutinee_id, .err_ty);
        const scrut_ty = self.store.getNode(scrut_hir).type_id;
        const res_ty = if (!target_ty.isError()) target_ty else .unit_ty;

        if (self.is_in_comptime_for) self.comptime_runtime_cond_depth += 1;
        defer if (self.is_in_comptime_for) {
            self.comptime_runtime_cond_depth -= 1;
        };

        var temp_arms: std.ArrayListUnmanaged(HirMatchArm) = .empty;
        defer temp_arms.deinit(self.allocator);

        for (0..arm_count) |arm_i| {
            const pat_ast_id = NodeIndex.fromInt(arm_entries[arm_i * 2]);
            const body_ast_id = NodeIndex.fromInt(arm_entries[arm_i * 2 + 1]);

            const local_checkpoint = self.local_shadow_log.items.len;
            defer self.popLexicalLocalsTo(local_checkpoint);

            const pat_idx = try self.lowerTopPattern(pat_ast_id, scrut_ty, false);
            const guard_hir = if (arm_i < arm_guards.len and !arm_guards[arm_i].isNone())
                try self.lowerExpr(arm_guards[arm_i], .bool_ty)
            else
                HirIndex.none;
            const body_hir = try self.lowerExpr(body_ast_id, res_ty);
            const arm_tok = if (!pat_ast_id.isNone())
                self.ast_arena.getNode(pat_ast_id).main_token
            else
                tok;
            try temp_arms.append(self.allocator, .{
                .pat_idx = pat_idx,
                .guard_hir = guard_hir,
                .body_hir = body_hir,
                .origin_token = arm_tok,
            });
        }

        const arm_start: u32 = @intCast(self.store.match_arms.items.len);
        try self.store.match_arms.appendSlice(self.allocator, temp_arms.items);
        const match_extra = try self.store.appendExtraSlice(&[2]u32{ arm_start, @intCast(temp_arms.items.len) });
        return self.emitNode(.{
            .tag = .hir_match,
            .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
            .type_id = self.concreteType(res_ty),
            .origin_token = tok,
            .data = .{ .lhs = scrut_hir.asInt(), .rhs = match_extra },
        }, expr_id);
    }

    /// Lowers `loop { … }` (`loop_expr`) into `hir_loop` with its `break` value type.
    fn lowerLoopExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const body_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;
        const loop_id = self.next_loop_id;
        self.next_loop_id += 1;
        const saved_loop_id = self.current_loop_id;
        const saved_in_ct_for = self.is_in_comptime_for;
        self.current_loop_id = loop_id;
        self.is_in_comptime_for = false;
        defer {
            self.current_loop_id = saved_loop_id;
            self.is_in_comptime_for = saved_in_ct_for;
        }

        const body_hir = try self.lowerBlockExpr(body_id, .unit_ty, false);
        const res_ty = if (!target_ty.isError()) target_ty else .unit_ty;
        return self.emitNode(.{
            .tag = .hir_loop,
            .flags = .{
                .category = if (res_ty == .never_ty) .diverging else .rvalue,
                .is_unsafe = self.is_in_unsafe,
            },
            .type_id = self.concreteType(res_ty),
            .origin_token = ast_node.main_token,
            .data = .{ .lhs = body_hir.asInt(), .rhs = loop_id },
        }, expr_id);
    }

    /// Lowers `|p1, p2| body` (`closure_expr`) into `hir_closure` + `HirStore.functions` entry with explicit capture list.
    fn lowerClosureExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const param_tokens = self.getAstExtraSlice(expr_id, false);
        const sig_view = self.pool.getFnSignatureView(target_ty);
        const ret_ty = if (sig_view) |sv| self.concreteType(sv.ret_ty) else .unit_ty;

        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_loop_id = self.current_loop_id;
        const saved_in_ct_for = self.is_in_comptime_for;
        const saved_ceil = self.closure_outer_local_ceil;
        const saved_captures_len = self.active_closure_captures.items.len;
        const local_checkpoint = self.local_shadow_log.items.len;
        defer {
            self.popLexicalLocalsTo(local_checkpoint);
            self.active_closure_captures.shrinkRetainingCapacity(saved_captures_len);
            self.closure_outer_local_ceil = saved_ceil;
            self.is_in_comptime_for = saved_in_ct_for;
            self.current_loop_id = saved_loop_id;
            self.current_fn_ret_ty = saved_ret_ty;
        }

        const return_local_id = try self.store.appendLocal(.{
            .name = .empty,
            .type_id = ret_ty,
            .decl_span = self.astSpan(expr_id),
            .mode = .set_mode,
            .is_mut = true,
            .is_param = false,
            .is_temp = true,
        });
        const param_local_start: u32 = @intCast(self.store.locals.items.len);
        self.closure_outer_local_ceil = return_local_id;
        self.current_fn_ret_ty = ret_ty;
        self.current_loop_id = null;
        self.is_in_comptime_for = false;

        for (param_tokens, 0..) |raw_tok, i| {
            const p_tok = TokenIndex.fromInt(raw_tok);
            const p_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, p_tok);
            const p_name = if (p_lex.len > 0 and !std.mem.eql(u8, p_lex, "_"))
                try self.interner.intern(p_lex)
            else
                SymbolId.empty;
            const p_ty = if (sig_view) |sv|
                (if (i < sv.paramCount()) self.concreteType(sv.getParamType(i)) else .i32_ty)
            else
                .i32_ty;
            const slot_id = try self.store.appendLocal(.{
                .name = p_name,
                .type_id = p_ty,
                .decl_span = self.tokens.getTokenSpan(self.store.file_id, p_tok),
                .mode = .let_mode,
                .is_mut = false,
                .is_param = true,
                .is_temp = false,
            });
            try self.pushLexicalLocal(p_name, slot_id);
        }

        const is_local_clos = self.hasAttrNamedInCst(self.ast_arena.getCstOrigin(expr_id), "local");
        const fn_meta_idx: u32 = @intCast(self.store.functions.items.len);
        try self.store.functions.append(self.allocator, .{
            .fn_ty = self.concreteType(target_ty),
            .ret_ty = ret_ty,
            .return_local_id = return_local_id,
            .param_local_start = param_local_start,
            .param_len = @intCast(param_tokens.len),
            .is_local_closure = is_local_clos,
        });

        const body_hir = if (ast_node.rhs.tag == .node) blk: {
            const body_id = NodeIndex.fromInt(ast_node.rhs.payload);
            if (self.ast_arena.getNode(body_id).tag == .block) {
                break :blk try self.lowerBlockExpr(body_id, ret_ty, true);
            }
            const expr_body = try self.lowerExpr(body_id, ret_ty);
            break :blk try self.wrapSyntheticReturnBlock(expr_body, ret_ty, tok);
        } else try self.emitUnitConst(tok, .none);

        const cap_slice = self.active_closure_captures.items[saved_captures_len..];
        const cap_extra_start = if (cap_slice.len > 0) try self.store.appendExtraSlice(cap_slice) else 0;

        self.store.functions.items[fn_meta_idx].body_hir = body_hir;
        self.store.functions.items[fn_meta_idx].total_local_len =
            @intCast(self.store.locals.items.len - return_local_id);
        self.store.functions.items[fn_meta_idx].capture_extra_start = cap_extra_start;
        self.store.functions.items[fn_meta_idx].capture_len = @intCast(cap_slice.len / 2);

        return self.emitNode(.{
            .tag = .hir_closure,
            .flags = .{ .category = .rvalue },
            .type_id = self.concreteType(target_ty),
            .origin_token = tok,
            .data = .{ .lhs = fn_meta_idx, .rhs = body_hir.asInt() },
        }, expr_id);
    }

    // ---------- CST, Member, Pattern & Comptime Helpers -----------

    /// Returns `true` if any direct shallow token leaf of `cst_id` matches `target_kind` (`MAJ-05`).
    fn hasKeywordInCst(self: *const HirLowerer, cst_id: CstNodeIndex, target_kind: TokenKind) bool {
        if (cst_id.isNone() or cst_id.asInt() >= self.cst_arena.countNodes()) return false;
        const start_idx: usize = cst_id.asInt();
        const rec = self.cst_arena.getNode(cst_id);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var cur = start_idx + 1;
        while (cur < end_idx) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.subtree_size > 1) {
                cur += sub.subtree_size;
                continue;
            }
            if (!sub.flags.is_missing_or_injected and
                !sub.token.isNone() and sub.token.asInt() < self.tokens.countTokens())
            {
                const leaf_kind = self.tokens.getToken(sub.token).kind;
                if (rec.kind == .local_decl_stmt and (leaf_kind == .colon or leaf_kind == .eq)) {
                    break;
                }
                if (leaf_kind == target_kind) return true;
            }
            cur += 1;
        }
        return false;
    }

    /// Extracts optional `label:` identifiers from `.call_arg` CST children of `call_id`.
    fn extractCallArgLabels(self: *HirLowerer, call_id: NodeIndex, out_labels: []SymbolId) !void {
        const call_cst = self.ast_arena.getCstOrigin(call_id);
        if (call_cst.isNone() or call_cst.asInt() >= self.cst_arena.countNodes()) return;
        const start_idx: usize = call_cst.asInt();
        const rec = self.cst_arena.getNode(call_cst);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var arg_ord: usize = 0;
        var cur = start_idx + 1;
        while (cur < end_idx and arg_ord < out_labels.len) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.kind == .call_arg) {
                const arg_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                if (cur + 2 < arg_end) {
                    const first_leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur + 1)));
                    const second_leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur + 2)));
                    if (first_leaf.subtree_size <= 1 and second_leaf.subtree_size <= 1 and
                        !first_leaf.token.isNone() and !second_leaf.token.isNone() and
                        first_leaf.token.asInt() < self.tokens.countTokens() and
                        second_leaf.token.asInt() < self.tokens.countTokens())
                    {
                        const sep_kind = self.tokens.getToken(second_leaf.token).kind;
                        if (symbol_resolver.isIdentifierToken(self.tokens.getToken(first_leaf.token).kind) and
                            (sep_kind == .colon or sep_kind == .eq))
                        {
                            const lbl_text = symbol_resolver.extractTokenSlice(
                                self.source,
                                self.tokens,
                                first_leaf.token,
                            );
                            out_labels[arg_ord] = try self.interner.intern(lbl_text);
                        }
                    }
                }
                arg_ord += 1;
                cur = arg_end;
                continue;
            }
            cur += 1;
        }
    }

    /// Extracts the interned `SymbolId` of a `.bind_pat` AST node (`SymbolId.empty` for `_` or non-bind patterns).
    fn extractBindPatNameId(self: *HirLowerer, pat_id: NodeIndex) SymbolId {
        if (pat_id.isNone() or pat_id.asInt() >= self.ast_arena.countNodes()) return .empty;
        const pat_node = self.ast_arena.getNode(pat_id);
        if (pat_node.tag != .bind_pat or pat_node.main_token.isNone()) return .empty;
        const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, pat_node.main_token);
        if (lexeme.len == 0 or std.mem.eql(u8, lexeme, "_")) return .empty;
        return self.interner.intern(lexeme) catch .empty;
    }

    /// Extracts the optional `|err|` capture token following `catch_tok` inside `expr_id`'s CST subtree.
    fn extractCatchCaptureToken(
        self: *const HirLowerer,
        expr_id: NodeIndex,
        catch_tok: TokenIndex,
    ) TokenIndex {
        const cst_id = self.ast_arena.getCstOrigin(expr_id);
        if (cst_id.isNone() or cst_id.asInt() >= self.cst_arena.countNodes()) return .none;
        const start_idx: usize = cst_id.asInt();
        const rec = self.cst_arena.getNode(cst_id);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var has_seen_catch = false;
        var has_seen_open_pipe = false;
        var cur = start_idx + 1;
        while (cur < end_idx) : (cur += 1) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (has_seen_catch and sub.kind == .block) break;
            if (sub.subtree_size <= 1 and !sub.flags.is_missing_or_injected and
                !sub.token.isNone() and sub.token.asInt() < self.tokens.countTokens())
            {
                if (sub.token == catch_tok) {
                    has_seen_catch = true;
                    continue;
                }
                if (has_seen_catch) {
                    const tok_kind = self.tokens.getToken(sub.token).kind;
                    if (!has_seen_open_pipe) {
                        if (tok_kind == .pipe) {
                            has_seen_open_pipe = true;
                            continue;
                        }
                        break;
                    }
                    if (symbol_resolver.isIdentifierToken(tok_kind)) return sub.token;
                    break;
                }
            }
        }
        return .none;
    }

    /// Extracts an optional `|cap|` or `|&cap|` payload capture bar from an `if` or `while` CST header.
    fn extractConditionCaptureBar(
        self: *const HirLowerer,
        enclosing_cst: CstNodeIndex,
    ) struct { token: TokenIndex, is_ref: bool } {
        if (enclosing_cst.isNone() or enclosing_cst.asInt() >= self.cst_arena.countNodes()) {
            return .{ .token = .none, .is_ref = false };
        }
        const start_idx: usize = enclosing_cst.asInt();
        const rec = self.cst_arena.getNode(enclosing_cst);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var cur = start_idx + 1;
        while (cur < end_idx) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.kind == .block) break;
            if (sub.subtree_size <= 1 and !sub.token.isNone() and
                sub.token.asInt() < self.tokens.countTokens() and
                self.tokens.getToken(sub.token).kind == .pipe)
            {
                var is_ref = false;
                var scan = cur + 1;
                while (scan < end_idx) : (scan += 1) {
                    const next_leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(scan)));
                    if (next_leaf.subtree_size <= 1 and !next_leaf.token.isNone() and
                        next_leaf.token.asInt() < self.tokens.countTokens())
                    {
                        const nk = self.tokens.getToken(next_leaf.token).kind;
                        if (nk == .amp) {
                            is_ref = true;
                            continue;
                        }
                        if (symbol_resolver.isIdentifierToken(nk)) {
                            return .{ .token = next_leaf.token, .is_ref = is_ref };
                        }
                        break;
                    }
                }
            }
            cur += 1;
        }
        return .{ .token = .none, .is_ref = false };
    }

    /// Scans `.match_arm` CST subtrees of `match_expr_id` to recover optional `if guard_expr` AST nodes (`CRIT-11`).
    fn extractMatchArmGuards(
        self: *const HirLowerer,
        match_expr_id: NodeIndex,
        out_guards: []NodeIndex,
    ) void {
        const match_cst = self.ast_arena.getCstOrigin(match_expr_id);
        if (match_cst.isNone() or match_cst.asInt() >= self.cst_arena.countNodes()) return;
        const start_idx: usize = match_cst.asInt();
        const rec = self.cst_arena.getNode(match_cst);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var arm_idx: usize = 0;
        var cur = start_idx + 1;
        while (cur < end_idx and arm_idx < out_guards.len) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.kind == .match_arm) {
                const arm_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                var inner = cur + 1;
                var if_pos: ?usize = null;
                var arrow_pos: usize = arm_end;
                while (inner < arm_end) {
                    const arm_sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(inner)));
                    if (arm_sub.subtree_size > 1) {
                        inner += arm_sub.subtree_size;
                        continue;
                    }
                    if (!arm_sub.token.isNone() and arm_sub.token.asInt() < self.tokens.countTokens()) {
                        const tk = self.tokens.getToken(arm_sub.token).kind;
                        if (tk == .kw_if and if_pos == null) {
                            if_pos = inner + 1;
                        } else if (tk == .fat_arrow) {
                            arrow_pos = inner;
                            break;
                        }
                    }
                    inner += 1;
                }
                if (if_pos) |guard_start| {
                    if (guard_start < arrow_pos) {
                        out_guards[arm_idx] = self.findFirstAstInCstRange(guard_start, arrow_pos);
                    }
                }
                arm_idx += 1;
                cur = arm_end;
                continue;
            }
            if (sub.subtree_size > 1) {
                cur += sub.subtree_size;
                continue;
            }
            cur += 1;
        }
    }

    /// Inserts explicit `hir_unary_op(.deref)` layers through `&T` / `&mut T` references up to 16 levels deep.
    fn autoDerefPlace(self: *HirLowerer, raw_hir: HirIndex, tok: TokenIndex) !HirIndex {
        var cur_hir = raw_hir;
        var i: u32 = 0;
        while (i < 16) : (i += 1) {
            const cur_ty = self.store.getNode(cur_hir).type_id;
            const ty_node = self.pool.getNode(cur_ty);
            if (ty_node.tag != .ref_ty and ty_node.tag != .mut_ref_ty) break;
            const is_mut = ty_node.tag == .mut_ref_ty;
            cur_hir = try self.emitNode(.{
                .tag = .hir_unary_op,
                .flags = .{
                    .category = if (is_mut) .place_mut else .place_imm,
                    .is_synthetic = true,
                },
                .type_id = self.concreteType(TypeId.fromInt(ty_node.lhs)),
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(HirUnaryOp.deref), .rhs = cur_hir.asInt() },
            }, .none);
        }
        return cur_hir;
    }

    /// Adjusts `raw_recv_hir` to match `param_ty` (`&Self`, `&mut Self`, or by-value `Self`) on method/subscript calls.
    fn adjustReceiverForParam(
        self: *HirLowerer,
        raw_recv_hir: HirIndex,
        param_ty: TypeId,
        tok: TokenIndex,
    ) !HirIndex {
        const recv_ty = self.store.getNode(raw_recv_hir).type_id;
        if (recv_ty == param_ty) return raw_recv_hir;

        const param_node = self.pool.getNode(param_ty);
        if (param_node.tag == .ref_ty or param_node.tag == .mut_ref_ty) {
            const wanted_inner = TypeId.fromInt(param_node.lhs);
            const deref_recv = try self.autoDerefPlace(raw_recv_hir, tok);
            if (self.store.getNode(deref_recv).type_id == wanted_inner) {
                return self.emitSyntheticAddrOf(
                    deref_recv,
                    param_ty,
                    param_node.tag == .mut_ref_ty,
                    tok,
                );
            }
        }
        return self.autoDerefPlace(raw_recv_hir, tok);
    }

    /// Wraps `arg_hir` in `hir_project_arg(mode, arg_hir)` (`DR-02` §2.2).
    fn wrapArgProjection(
        self: *HirLowerer,
        arg_hir: HirIndex,
        mode: ParamMode,
        tok: TokenIndex,
    ) !HirIndex {
        return self.emitNode(.{
            .tag = .hir_project_arg,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = self.store.getNode(arg_hir).type_id,
            .origin_token = tok,
            .data = .{ .lhs = @backingInt(mode), .rhs = arg_hir.asInt() },
        }, .none);
    }

    /// Returns `true` if `callee_hir` resolves to a `subscript` declaration.
    fn isCalleeSubscript(self: *const HirLowerer, callee_hir: HirIndex) bool {
        if (callee_hir.isNone()) return false;
        const callee_node = self.store.getNode(callee_hir);
        if (callee_node.tag != .hir_global_ref) return false;
        const sym_idx = SymbolIndex.fromInt(callee_node.data.rhs);
        if (sym_idx.isNone() or sym_idx.asInt() >= self.sym_table.symbols.items.len) return false;
        const sym = self.sym_table.getSymbol(sym_idx).*;
        if (sym.ast_node.isNone() or sym.ast_node.asInt() >= self.ast_arena.countNodes()) return false;
        const main_tok = self.ast_arena.getNode(sym.ast_node).main_token;
        if (main_tok.isNone() or main_tok.asInt() >= self.tokens.countTokens()) return false;
        return std.mem.eql(
            u8,
            symbol_resolver.extractTokenSlice(self.source, self.tokens, main_tok),
            "subscript",
        );
    }

    /// Looks up `field_name`'s zero-based declaration ordinal and `TypeId` on a `struct` or `union` type.
    fn findStructFieldInfo(
        self: *const HirLowerer,
        nominal_ty: TypeId,
        field_name: []const u8,
    ) ?struct { ordinal: u32, field_ty: TypeId } {
        const unwrapped = self.pool.unwrapUnderlyingType(nominal_ty);
        const ty_node = self.pool.getNode(unwrapped);
        if (ty_node.tag != .struct_ty and ty_node.tag != .union_ty) return null;
        const sym_idx = SymbolIndex.fromInt(ty_node.rhs);
        if (sym_idx.isNone() or sym_idx.asInt() >= self.sym_table.symbols.items.len) return null;
        const nom_sym = self.sym_table.getSymbol(sym_idx).*;
        if (nom_sym.target_scope.isNone()) return null;

        var ord: u32 = 0;
        for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
            const mem_sym = self.sym_table.getSymbol(mem_idx).*;
            if (mem_sym.kind != .field_sym) continue;
            if (std.mem.eql(u8, mem_sym.name_text, field_name)) {
                return .{ .ordinal = ord, .field_ty = mem_sym.type_id };
            }
            ord += 1;
        }
        return null;
    }

    /// Computes the LSB-first `BitSpec` (`bit_offset`, `bit_width`, `backing_bits`, `is_signed`) for `field_name` on `bit_field_ty`.
    fn computeBitFieldSpec(
        self: *const HirLowerer,
        bit_field_ty: TypeId,
        field_name: []const u8,
    ) ?struct { spec: BitSpec, field_ty: TypeId } {
        const unwrapped_bf_ty = self.pool.unwrapUnderlyingType(bit_field_ty);
        const ty_node = self.pool.getNode(unwrapped_bf_ty);
        if (ty_node.tag != .bit_field_ty) return null;
        const backing_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
        const backing_bits: u8 = if (type_system.getTargetPrimitiveIntBits(backing_ty, self.store.target_layout)) |bits|
            @intCast(bits)
        else
            32;

        const sym_idx = SymbolIndex.fromInt(ty_node.rhs);
        if (sym_idx.isNone() or sym_idx.asInt() >= self.sym_table.symbols.items.len) return null;
        const bf_sym = self.sym_table.getSymbol(sym_idx).*;
        if (bf_sym.target_scope.isNone()) return null;

        var running_offset: u16 = 0;
        for (self.sym_table.getScopeMembers(bf_sym.target_scope)) |mem_idx| {
            const mem_sym = self.sym_table.getSymbol(mem_idx).*;
            if (mem_sym.kind != .field_sym) continue;
            const base_field_ty = self.pool.unwrapUnderlyingType(mem_sym.type_id);
            const width: u16 = if (mem_sym.bit_width > 0)
                mem_sym.bit_width
            else if (base_field_ty == .bool_ty)
                1
            else if (type_system.getTargetPrimitiveIntBits(base_field_ty, self.store.target_layout)) |f_bits|
                f_bits
            else
                1;

            if (std.mem.eql(u8, mem_sym.name_text, field_name)) {
                const is_signed = switch (base_field_ty) {
                    .i8_ty, .i16_ty, .i32_ty, .i64_ty, .i128_ty, .isize_ty => true,
                    else => false,
                };
                return .{
                    .spec = .{
                        .bit_offset = @intCast(@min(running_offset, 127)),
                        .bit_width = @intCast(@min(width, 128)),
                        .backing_bits = backing_bits,
                        .is_signed = is_signed,
                    },
                    .field_ty = mem_sym.type_id,
                };
            }
            running_offset +|= width;
        }
        return null;
    }

    /// Synthesizes canonical recursive default initialization for `@default_init[T]()` and struct spread holes.
    fn emitDefaultInitValue(self: *HirLowerer, raw_ty: TypeId, tok: TokenIndex) anyerror!HirIndex {
        const ty = self.concreteType(raw_ty);
        switch (ty) {
            .unit_ty => return self.emitUnitConst(tok, .none),
            .bool_ty => return self.emitConstVal(.{ .bool_val = false }, .bool_ty, tok, .none, true),
            .char_ty => return self.emitConstVal(.{ .char_val = 0 }, .char_ty, tok, .none, true),
            .str_ty => {
                const empty_id = try self.interner.intern("");
                return self.emitConstVal(.{ .str_val = empty_id }, .str_ty, tok, .none, true);
            },
            .f32_ty, .f64_ty => return self.emitConstVal(.{ .float_val = 0.0 }, ty, tok, .none, true),
            else => {
                if (ty.isIntegerPrimitive()) {
                    return self.emitConstVal(.{ .int_val = 0 }, ty, tok, .none, true);
                }
            },
        }
        const ty_node = self.pool.getNode(ty);
        switch (ty_node.tag) {
            .distinct_ty => {
                const base_init = try self.emitDefaultInitValue(TypeId.fromInt(ty_node.lhs), tok);
                return self.emitNode(.{
                    .tag = .hir_cast,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = ty,
                    .origin_token = tok,
                    .data = .{ .lhs = base_init.asInt(), .rhs = @backingInt(HirCastKind.distinct_wrap) },
                }, .none);
            },
            .optional_ty => {
                const extra_idx = try self.store.appendLenPrefixedExtra(&.{});
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirConstructKind.optional_none), .rhs = extra_idx },
                }, .none);
            },
            .bit_field_ty => {
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirConstructKind.bitfield_zero), .rhs = 0 },
                }, .none);
            },
            .tuple_ty => {
                const elems = self.pool.getTupleElements(ty);
                var sub_hirs = try self.allocator.alloc(u32, elems.len);
                defer self.allocator.free(sub_hirs);
                for (elems, 0..) |raw_elem, i| {
                    sub_hirs[i] = (try self.emitDefaultInitValue(TypeId.fromInt(raw_elem), tok)).asInt();
                }
                const extra_idx = try self.store.appendLenPrefixedExtra(sub_hirs);
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirConstructKind.tuple_init), .rhs = extra_idx },
                }, .none);
            },
            .array_ty, .soa_array_ty => {
                const elem_def = try self.emitDefaultInitValue(TypeId.fromInt(ty_node.lhs), tok);
                const extra_idx = try self.store.appendExtraSlice(&[2]u32{
                    ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG,
                    elem_def.asInt(),
                });
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirConstructKind.array_repeat), .rhs = extra_idx },
                }, .none);
            },
            .struct_ty => {
                const struct_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(ty_node.rhs)).*;
                var f_hirs: std.ArrayListUnmanaged(u32) = .empty;
                defer f_hirs.deinit(self.allocator);
                if (!struct_sym.target_scope.isNone()) {
                    for (self.sym_table.getScopeMembers(struct_sym.target_scope)) |mem_idx| {
                        const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .field_sym) continue;
                        try f_hirs.append(
                            self.allocator,
                            (try self.emitDefaultInitValue(mem_sym.type_id, tok)).asInt(),
                        );
                    }
                }
                const extra_idx = try self.store.appendLenPrefixedExtra(f_hirs.items);
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirConstructKind.struct_init), .rhs = extra_idx },
                }, .none);
            },
            else => return self.emitConstVal(.{ .int_val = 0 }, ty, tok, .none, true),
        }
    }

    /// Infers a fallback concrete `TypeId` from a `ComptimeValue`.
    fn inferComptimeValType(self: *const HirLowerer, val: ComptimeValue) TypeId {
        _ = self;
        return switch (val) {
            .unit_val => .unit_ty,
            .bool_val => .bool_ty,
            .int_val => .i64_ty,
            .float_val => .f64_ty,
            .char_val => .char_ty,
            .str_val => .str_ty,
            .bytes_val => .str_ty,
            .aggregate => |agg| agg.type_id,
            .variant => |var_val| var_val.type_id,
            .type_info_mirror, .field_info_mirror, .variant_info_mirror => .usize_ty,
        };
    }

    /// Lowers a top-level pattern, scoping `or_pat` slot-reuse to bindings within this pattern (`CRIT-09`).
    fn lowerTopPattern(
        self: *HirLowerer,
        pat_id: NodeIndex,
        scrut_ty: TypeId,
        is_decl_mut: bool,
    ) anyerror!u32 {
        const saved_floor = self.current_pat_shadow_floor;
        self.current_pat_shadow_floor = self.local_shadow_log.items.len;
        defer self.current_pat_shadow_floor = saved_floor;
        return self.lowerPattern(pat_id, scrut_ty, is_decl_mut);
    }

    /// Lowers an AST pattern subtree into `HirStore.patterns`, registering bound locals in `active_name_to_local`.
    fn lowerPattern(
        self: *HirLowerer,
        pat_id: NodeIndex,
        scrut_ty: TypeId,
        is_decl_mut: bool,
    ) anyerror!u32 {
        const concrete_scrut = self.concreteType(scrut_ty);
        if (pat_id.isNone() or pat_id.asInt() >= self.ast_arena.countNodes()) {
            return self.store.appendPat(.{
                .type_id = concrete_scrut,
                .origin_token = TokenIndex.fromInt(0),
                .kind = .wildcard,
            });
        }
        const pat_node = self.ast_arena.getNode(pat_id);
        const tok = pat_node.main_token;
        if (!try self.enterDepth(pat_id)) {
            return self.store.appendPat(.{ .type_id = concrete_scrut, .origin_token = tok, .kind = .wildcard });
        }
        defer self.leaveDepth();

        switch (pat_node.tag) {
            .wildcard_pat, .pattern_hole => {
                return self.store.appendPat(.{ .type_id = concrete_scrut, .origin_token = tok, .kind = .wildcard });
            },
            .bind_pat => {
                const pat_cst = self.ast_arena.getCstOrigin(pat_id);
                const is_ref = self.hasKeywordInCst(pat_cst, .kw_ref) or self.hasKeywordInCst(pat_cst, .amp);
                const has_pat_mut = self.hasKeywordInCst(pat_cst, .kw_mut);
                const is_ref_mut = is_ref and has_pat_mut;
                const is_local_mut = is_decl_mut or (!is_ref and has_pat_mut);
                const bind_ty = if (is_ref) try self.pool.internRef(concrete_scrut, is_ref_mut) else concrete_scrut;
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                if (std.mem.eql(u8, lexeme, "_")) {
                    return self.store.appendPat(.{
                        .type_id = concrete_scrut,
                        .origin_token = tok,
                        .kind = .wildcard,
                    });
                }
                const existing_local = blk: {
                    if (self.interner.lookup(lexeme)) |existing_id| {
                        // Reuse binding slot ONLY across `P1 | P2` alternatives in the SAME top-level pattern (`CRIT-09`):
                        const floor = @min(self.current_pat_shadow_floor, self.local_shadow_log.items.len);
                        for (self.local_shadow_log.items[floor..]) |shadow_item| {
                            if (shadow_item.name_id == existing_id.asInt()) {
                                if (self.active_name_to_local.get(existing_id.asInt())) |cur_slot| {
                                    if (self.store.locals.items[cur_slot].type_id == bind_ty) {
                                        break :blk @as(?u32, cur_slot);
                                    }
                                }
                                break;
                            }
                        }
                    }
                    break :blk null;
                };
                const slot_id = existing_local orelse try self.bindSimplePatternLocal(pat_id, bind_ty, is_local_mut);
                return self.store.appendPat(.{
                    .type_id = concrete_scrut,
                    .origin_token = tok,
                    .kind = .{ .bind = .{ .local_id = slot_id, .is_mut = is_ref_mut or is_local_mut, .is_ref = is_ref } },
                });
            },
            .lit_pat => {
                // Range pattern `low..=high` or `low..high` (`CRIT-07`):
                if (pat_node.lhs.tag == .node and pat_node.rhs.tag == .token) {
                    const low_val = self.evalLitPatScalar(NodeIndex.fromInt(pat_node.lhs.payload));
                    const high_raw = self.evalTokenPatScalar(TokenIndex.fromInt(pat_node.rhs.payload), pat_id);
                    const is_excl = self.tokens.getToken(tok).kind == .dotdot;
                    const base_scrut = self.pool.unwrapUnderlyingType(self.unwrapRefType(concrete_scrut));

                    var final_min: i128 = 1;
                    var final_max: i128 = 0;
                    if (base_scrut == .u128_ty) {
                        const low_u: u128 = @bitCast(low_val);
                        const high_raw_u: u128 = @bitCast(high_raw);
                        if (is_excl) {
                            if (high_raw_u > low_u) {
                                final_min = low_val;
                                final_max = @bitCast(high_raw_u - 1);
                            }
                        } else if (high_raw_u >= low_u) {
                            final_min = low_val;
                            final_max = high_raw;
                        }
                    } else {
                        if (is_excl) {
                            if (high_raw > low_val) {
                                final_min = low_val;
                                final_max = high_raw - 1;
                            }
                        } else if (high_raw >= low_val) {
                            final_min = low_val;
                            final_max = high_raw;
                        }
                    }
                    return self.store.appendPat(.{
                        .type_id = concrete_scrut,
                        .origin_token = tok,
                        .kind = .{ .lit_int_range = .{ .min_val = final_min, .max_val = final_max } },
                    });
                }
                const tok_kind = self.tokens.getToken(tok).kind;
                switch (tok_kind) {
                    .kw_true, .kw_false => {
                        return self.store.appendPat(.{
                            .type_id = .bool_ty,
                            .origin_token = tok,
                            .kind = .{ .lit_bool = tok_kind == .kw_true },
                        });
                    },
                    .string_lit => {
                        const raw_str = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                        if (type_system.extractRawStringContent(raw_str)) |raw_body| {
                            const raw_id = try self.interner.intern(raw_body);
                            return self.store.appendPat(.{
                                .type_id = .str_ty,
                                .origin_token = tok,
                                .kind = .{ .lit_str = raw_id },
                            });
                        }
                        const unescaped = try type_system.decodeStandardStringSegment(
                            self.allocator,
                            extractQuotedBody(raw_str),
                        );
                        defer self.allocator.free(unescaped);
                        const str_id = try self.interner.intern(unescaped);
                        return self.store.appendPat(.{
                            .type_id = .str_ty,
                            .origin_token = tok,
                            .kind = .{ .lit_str = str_id },
                        });
                    },
                    .float_lit => {
                        const raw_flt = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                        return self.store.appendPat(.{
                            .type_id = concrete_scrut,
                            .origin_token = tok,
                            .kind = .{ .lit_float = extractFloatValue(raw_flt) orelse 0.0 },
                        });
                    },
                    else => {
                        const scalar_val = self.evalLitPatScalar(pat_id);
                        return self.store.appendPat(.{
                            .type_id = concrete_scrut,
                            .origin_token = tok,
                            .kind = .{ .lit_int_range = .{ .min_val = scalar_val, .max_val = scalar_val } },
                        });
                    },
                }
            },
            .tuple_pat => {
                const sub_nodes = self.getAstExtraSlice(pat_id, false);
                if (sub_nodes.len == 1 and !type_system.hasShallowCommaInTupleCst(
                    self.cst_arena,
                    self.tokens,
                    self.ast_arena.getCstOrigin(pat_id),
                )) {
                    return self.lowerPattern(NodeIndex.fromInt(sub_nodes[0]), concrete_scrut, is_decl_mut);
                }
                const tup_elems = self.pool.getTupleElements(self.unwrapRefType(concrete_scrut));
                var lowered_subs = try self.allocator.alloc(u32, sub_nodes.len);
                defer self.allocator.free(lowered_subs);
                for (sub_nodes, 0..) |raw_sub, i| {
                    const elem_ty = if (i < tup_elems.len) TypeId.fromInt(tup_elems[i]) else .unit_ty;
                    lowered_subs[i] = try self.lowerPattern(NodeIndex.fromInt(raw_sub), elem_ty, is_decl_mut);
                }
                const sub_start = try self.store.appendExtraSlice(lowered_subs);
                return self.store.appendPat(.{
                    .type_id = concrete_scrut,
                    .origin_token = tok,
                    .kind = .{ .tuple = .{ .sub_start = sub_start, .sub_len = @intCast(sub_nodes.len) } },
                });
            },
            .struct_pat => {
                const sub_nodes = self.getAstExtraSlice(pat_id, false);
                var field_names: std.ArrayListUnmanaged(TokenIndex) = .empty;
                defer field_names.deinit(self.allocator);
                try self.extractStructPatFieldTokens(pat_id, &field_names);
                const unwrapped = self.unwrapRefType(concrete_scrut);

                var pairs: std.ArrayListUnmanaged(u32) = .empty;
                defer pairs.deinit(self.allocator);
                for (sub_nodes, 0..) |raw_sub, i| {
                    var f_ord: u32 = @intCast(i);
                    var f_ty: TypeId = .unit_ty;
                    if (i < field_names.items.len and !field_names.items[i].isNone()) {
                        const f_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, field_names.items[i]);
                        if (self.findStructFieldInfo(unwrapped, f_lex)) |f_info| {
                            f_ord = f_info.ordinal;
                            f_ty = f_info.field_ty;
                        }
                    }
                    const sub_pat_idx = try self.lowerPattern(NodeIndex.fromInt(raw_sub), f_ty, is_decl_mut);
                    try pairs.append(self.allocator, f_ord);
                    try pairs.append(self.allocator, sub_pat_idx);
                }
                const field_start = try self.store.appendExtraSlice(pairs.items);
                return self.store.appendPat(.{
                    .type_id = concrete_scrut,
                    .origin_token = tok,
                    .kind = .{
                        .struct_pat = .{
                            .field_start = field_start,
                            .field_len = @intCast(pairs.items.len / 2),
                        },
                    },
                });
            },
            .variant_pat => {
                const sub_nodes = self.getAstExtraSlice(pat_id, false);
                const unwrapped = self.unwrapRefType(concrete_scrut);
                const scr_ty_node = self.pool.getNode(unwrapped);
                const var_name = self.extractVariantPatName(pat_id);

                var tag_ordinal: u32 = 0;
                var payload_ty: TypeId = .unit_ty;
                switch (scr_ty_node.tag) {
                    .optional_ty => {
                        if (std.mem.eql(u8, var_name, "Some")) {
                            tag_ordinal = 1;
                            payload_ty = TypeId.fromInt(scr_ty_node.lhs);
                        } else {
                            tag_ordinal = 0;
                        }
                    },
                    .result_ty => {
                        if (std.mem.eql(u8, var_name, "Err")) {
                            tag_ordinal = 1;
                            payload_ty = TypeId.fromInt(scr_ty_node.rhs);
                        } else {
                            tag_ordinal = 0;
                            payload_ty = TypeId.fromInt(scr_ty_node.lhs);
                        }
                    },
                    .enum_ty => {
                        const enum_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(scr_ty_node.rhs)).*;
                        if (!enum_sym.target_scope.isNone()) {
                            var ord: u32 = 0;
                            for (self.sym_table.getScopeMembers(enum_sym.target_scope)) |m_idx| {
                                const m_sym = self.sym_table.getSymbol(m_idx).*;
                                if (m_sym.kind != .enum_variant_sym) continue;
                                if (std.mem.eql(u8, m_sym.name_text, var_name)) {
                                    tag_ordinal = ord;
                                    payload_ty = m_sym.type_id;
                                    break;
                                }
                                ord += 1;
                            }
                        }
                    },
                    else => {},
                }

                var lowered_subs = try self.allocator.alloc(u32, sub_nodes.len);
                defer self.allocator.free(lowered_subs);
                if (sub_nodes.len == 1) {
                    lowered_subs[0] = try self.lowerPattern(
                        NodeIndex.fromInt(sub_nodes[0]),
                        payload_ty,
                        is_decl_mut,
                    );
                } else if (sub_nodes.len > 1) {
                    const tup_elems = self.pool.getTupleElements(payload_ty);
                    for (sub_nodes, 0..) |raw_sub, i| {
                        const elem_ty = if (i < tup_elems.len) TypeId.fromInt(tup_elems[i]) else .unit_ty;
                        lowered_subs[i] = try self.lowerPattern(NodeIndex.fromInt(raw_sub), elem_ty, is_decl_mut);
                    }
                }
                const sub_start = if (lowered_subs.len > 0) try self.store.appendExtraSlice(lowered_subs) else 0;
                return self.store.appendPat(.{
                    .type_id = concrete_scrut,
                    .origin_token = tok,
                    .kind = .{
                        .variant = .{
                            .tag_ordinal = tag_ordinal,
                            .payload_ty = self.concreteType(payload_ty),
                            .sub_start = sub_start,
                            .sub_len = @intCast(lowered_subs.len),
                        },
                    },
                });
            },
            .or_pat => {
                const lhs_idx = if (pat_node.lhs.tag == .node)
                    try self.lowerPattern(NodeIndex.fromInt(pat_node.lhs.payload), concrete_scrut, is_decl_mut)
                else
                    try self.store.appendPat(.{ .type_id = concrete_scrut, .origin_token = tok, .kind = .wildcard });
                const rhs_idx = if (pat_node.rhs.tag == .node)
                    try self.lowerPattern(NodeIndex.fromInt(pat_node.rhs.payload), concrete_scrut, is_decl_mut)
                else
                    try self.store.appendPat(.{ .type_id = concrete_scrut, .origin_token = tok, .kind = .wildcard });
                return self.store.appendPat(.{
                    .type_id = concrete_scrut,
                    .origin_token = tok,
                    .kind = .{ .or_pat = .{ .lhs_pat = lhs_idx, .rhs_pat = rhs_idx } },
                });
            },
            else => {
                return self.store.appendPat(.{ .type_id = concrete_scrut, .origin_token = tok, .kind = .wildcard });
            },
        }
    }

    /// Evaluates a singleton `.lit_pat` AST node (`int_lit`, `-int_lit`, `char_lit`, or `CONST_IDENT`) into `i128`.
    fn evalLitPatScalar(self: *HirLowerer, lit_pat_id: NodeIndex) i128 {
        if (lit_pat_id.isNone() or lit_pat_id.asInt() >= self.ast_arena.countNodes()) return 0;
        const node = self.ast_arena.getNode(lit_pat_id);
        return self.evalTokenPatScalar(node.main_token, lit_pat_id);
    }

    /// Evaluates a pattern scalar token (detecting preceding `-` inside `pat_owner_id`'s CST) into `i128`.
    fn evalTokenPatScalar(self: *HirLowerer, tok: TokenIndex, pat_owner_id: NodeIndex) i128 {
        if (tok.isNone() or tok.asInt() >= self.tokens.countTokens()) return 0;
        const tok_rec = self.tokens.getToken(tok);
        if (tok_rec.kind == .minus and tok.asInt() + 1 < self.tokens.countTokens()) {
            const next_tok = TokenIndex.fromInt(tok.asInt() + 1);
            const lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, next_tok);
            return extractNegatedIntValue(lex) orelse 0;
        }
        const is_preceded_by_minus = blk: {
            if (tok.asInt() == 0) break :blk false;
            const prev_tok = TokenIndex.fromInt(tok.asInt() - 1);
            if (self.tokens.getToken(prev_tok).kind != .minus) break :blk false;
            const owner_cst = self.ast_arena.getCstOrigin(pat_owner_id);
            if (owner_cst.isNone() or owner_cst.asInt() >= self.cst_arena.countNodes()) break :blk false;
            const start_idx: usize = owner_cst.asInt();
            const rec = self.cst_arena.getNode(owner_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var cur = start_idx;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.subtree_size <= 1 and sub.token == prev_tok) break :blk true;
            }
            break :blk false;
        };
        const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
        if (tok_rec.kind == .char_lit) return @as(i128, extractCharValue(lexeme));
        if (tok_rec.kind == .int_lit) {
            return if (is_preceded_by_minus)
                (extractNegatedIntValue(lexeme) orelse 0)
            else
                (extractIntValue(lexeme) orelse 0);
        }
        if (symbol_resolver.isIdentifierToken(tok_rec.kind)) {
            if (self.interner.lookup(lexeme)) |name_id| {
                if (self.active_comptime_vals.get(name_id.asInt())) |ct_val| {
                    if (ct_val == .int_val) return ct_val.int_val;
                }
                switch (self.sym_table.lookupLexical(self.current_scope, name_id, NamespaceMask.ALL)) {
                    .found => |sym_idx| {
                        if (self.evalConstSymbol(sym_idx) catch null) |c_val| {
                            if (c_val == .int_val) return c_val.int_val;
                        }
                    },
                    else => {},
                }
            }
        }
        return 0;
    }

    /// Extracts field name tokens from `.field_pat` CST children inside a `.struct_pat` (`CRIT-11`).
    fn extractStructPatFieldTokens(
        self: *const HirLowerer,
        pat_id: NodeIndex,
        out_tokens: *std.ArrayListUnmanaged(TokenIndex),
    ) !void {
        const pat_cst = self.ast_arena.getCstOrigin(pat_id);
        if (pat_cst.isNone() or pat_cst.asInt() >= self.cst_arena.countNodes()) return;
        const start_idx: usize = pat_cst.asInt();
        const rec = self.cst_arena.getNode(pat_cst);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var cur = start_idx + 1;
        while (cur < end_idx) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.kind == .field_pat) {
                const f_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                var inner = cur + 1;
                while (inner < f_end) : (inner += 1) {
                    const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(inner)));
                    if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                        leaf.token.asInt() < self.tokens.countTokens())
                    {
                        if (symbol_resolver.isIdentifierToken(self.tokens.getToken(leaf.token).kind)) {
                            try out_tokens.append(self.allocator, leaf.token);
                            break;
                        }
                    }
                }
                cur = f_end;
                continue;
            }
            cur += 1;
        }
    }

    /// Extracts the variant identifier slice (`Some`, `Ok`, `Red`, etc.) from a `.variant_pat` CST subtree.
    fn extractVariantPatName(self: *const HirLowerer, pat_id: NodeIndex) []const u8 {
        const pat_cst = self.ast_arena.getCstOrigin(pat_id);
        if (!pat_cst.isNone() and pat_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = pat_cst.asInt();
            const rec = self.cst_arena.getNode(pat_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var last_ident_tok: TokenIndex = .none;
            var cur = start_idx + 1;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.subtree_size <= 1 and !sub.token.isNone() and
                    sub.token.asInt() < self.tokens.countTokens())
                {
                    const tk = self.tokens.getToken(sub.token).kind;
                    if (tk == .lparen or tk == .lbrace) break;
                    if (symbol_resolver.isIdentifierToken(tk)) last_ident_tok = sub.token;
                }
            }
            if (!last_ident_tok.isNone()) {
                return symbol_resolver.extractTokenSlice(self.source, self.tokens, last_ident_tok);
            }
        }
        const main_tok = self.ast_arena.getNode(pat_id).main_token;
        return symbol_resolver.extractTokenSlice(self.source, self.tokens, main_tok);
    }

    /// Evaluates whether `pat_id` matches `scrut_val` during `comptime match`, binding captures in `active_comptime_vals`.
    fn matchComptimePattern(
        self: *HirLowerer,
        pat_id: NodeIndex,
        scrut_val: ComptimeValue,
        scrut_ty: TypeId,
    ) anyerror!bool {
        if (pat_id.isNone() or pat_id.asInt() >= self.ast_arena.countNodes()) return false;
        const pat_node = self.ast_arena.getNode(pat_id);
        switch (pat_node.tag) {
            .wildcard_pat => return true,
            .bind_pat => {
                const name_id = self.extractBindPatNameId(pat_id);
                try self.pushComptimeBinding(name_id, scrut_val);
                return true;
            },
            .or_pat => {
                const checkpoint = self.comptime_shadow_log.items.len;
                if (pat_node.lhs.tag == .node and
                    try self.matchComptimePattern(NodeIndex.fromInt(pat_node.lhs.payload), scrut_val, scrut_ty))
                {
                    return true;
                }
                self.popComptimeBindingsTo(checkpoint);
                if (pat_node.rhs.tag == .node) {
                    return self.matchComptimePattern(NodeIndex.fromInt(pat_node.rhs.payload), scrut_val, scrut_ty);
                }
                return false;
            },
            .lit_pat => {
                if (pat_node.lhs.tag == .node and pat_node.rhs.tag == .token) {
                    const low_val = self.evalLitPatScalar(NodeIndex.fromInt(pat_node.lhs.payload));
                    const high_raw = self.evalTokenPatScalar(TokenIndex.fromInt(pat_node.rhs.payload), pat_id);
                    const is_excl = self.tokens.getToken(pat_node.main_token).kind == .dotdot;
                    const base_scrut = self.pool.unwrapUnderlyingType(self.unwrapRefType(scrut_ty));
                    if (base_scrut == .u128_ty) {
                        const low_u: u128 = @bitCast(low_val);
                        const high_raw_u: u128 = @bitCast(high_raw);
                        if (is_excl) {
                            if (high_raw_u <= low_u) return false;
                            const high_u = high_raw_u - 1;
                            return scrut_val == .int_val and
                                @as(u128, @bitCast(scrut_val.int_val)) >= low_u and
                                @as(u128, @bitCast(scrut_val.int_val)) <= high_u;
                        }
                        if (high_raw_u < low_u) return false;
                        return scrut_val == .int_val and
                            @as(u128, @bitCast(scrut_val.int_val)) >= low_u and
                            @as(u128, @bitCast(scrut_val.int_val)) <= high_raw_u;
                    }
                    if (is_excl and high_raw <= low_val) return false;
                    if (!is_excl and high_raw < low_val) return false;
                    const high_val = if (is_excl) high_raw - 1 else high_raw;
                    return switch (scrut_val) {
                        .int_val => |iv| iv >= low_val and iv <= high_val,
                        .char_val => |cv| @as(i128, cv) >= low_val and @as(i128, cv) <= high_val,
                        else => false,
                    };
                }
                const tk = self.tokens.getToken(pat_node.main_token).kind;
                if (tk == .kw_true or tk == .kw_false) {
                    return scrut_val == .bool_val and scrut_val.bool_val == (tk == .kw_true);
                }
                if (tk == .string_lit) {
                    if (scrut_val != .str_val) return false;
                    const raw_str = symbol_resolver.extractTokenSlice(
                        self.source,
                        self.tokens,
                        pat_node.main_token,
                    );
                    if (type_system.extractRawStringContent(raw_str)) |raw_body| {
                        return std.mem.eql(u8, self.interner.get(scrut_val.str_val), raw_body);
                    }
                    const unescaped = try type_system.decodeStandardStringSegment(
                        self.allocator,
                        extractQuotedBody(raw_str),
                    );
                    defer self.allocator.free(unescaped);
                    return std.mem.eql(u8, self.interner.get(scrut_val.str_val), unescaped);
                }
                const expected_int = self.evalLitPatScalar(pat_id);
                return switch (scrut_val) {
                    .int_val => |iv| iv == expected_int,
                    .char_val => |cv| @as(i128, cv) == expected_int,
                    else => false,
                };
            },
            .variant_pat => {
                if (scrut_val != .variant) return false;
                const var_name = self.extractVariantPatName(pat_id);
                const scr_ty_node = self.pool.getNode(scrut_val.variant.type_id);
                var expected_ord: ?u32 = null;
                var payload_ty: TypeId = .unit_ty;
                switch (scr_ty_node.tag) {
                    .optional_ty => {
                        if (std.mem.eql(u8, var_name, "Some")) {
                            expected_ord = 1;
                            payload_ty = TypeId.fromInt(scr_ty_node.lhs);
                        } else {
                            expected_ord = 0;
                        }
                    },
                    .result_ty => {
                        if (std.mem.eql(u8, var_name, "Err")) {
                            expected_ord = 1;
                            payload_ty = TypeId.fromInt(scr_ty_node.rhs);
                        } else {
                            expected_ord = 0;
                            payload_ty = TypeId.fromInt(scr_ty_node.lhs);
                        }
                    },
                    .enum_ty => {
                        const enum_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(scr_ty_node.rhs)).*;
                        if (!enum_sym.target_scope.isNone()) {
                            var ord: u32 = 0;
                            for (self.sym_table.getScopeMembers(enum_sym.target_scope)) |m_idx| {
                                const m_sym = self.sym_table.getSymbol(m_idx).*;
                                if (m_sym.kind != .enum_variant_sym) continue;
                                if (std.mem.eql(u8, m_sym.name_text, var_name)) {
                                    expected_ord = ord;
                                    payload_ty = m_sym.type_id;
                                    break;
                                }
                                ord += 1;
                            }
                        }
                    },
                    else => {},
                }
                if (expected_ord == null or scrut_val.variant.tag_ordinal != expected_ord.?) return false;
                const sub_nodes = self.getAstExtraSlice(pat_id, false);
                if (sub_nodes.len == 0) return true;
                if (scrut_val.variant.payload_const_idx >= self.store.const_pool.items.len) return false;
                const payload_val = self.store.const_pool.items[scrut_val.variant.payload_const_idx];
                return self.matchComptimePattern(NodeIndex.fromInt(sub_nodes[0]), payload_val, payload_ty);
            },
            else => return false,
        }
    }

    /// Evaluates a `const_sym` declaration at compile time with `const_eval_stack` cycle detection (`E0509`).
    fn evalConstSymbol(self: *HirLowerer, sym_idx: SymbolIndex) anyerror!?ComptimeValue {
        if (sym_idx.isNone() or sym_idx.asInt() >= self.sym_table.symbols.items.len) return null;
        const sym = self.sym_table.getSymbol(sym_idx).*;
        if (sym.kind != .const_sym) return null;

        for (self.const_eval_stack[0..self.const_eval_depth]) |active_sym| {
            if (active_sym == sym_idx) {
                try self.emitDiagnostic(
                    .e0509_comptime_evaluation_cycle,
                    sym.decl_span,
                    "cyclic compile-time constant dependency detected",
                    "constant evaluation re-entered here",
                );
                return null;
            }
        }
        if (self.const_eval_depth >= self.const_eval_stack.len) return null;

        if (!sym.decl_span.file_id.isNone() and sym.decl_span.file_id != self.store.file_id) {
            if (self.eval_hook.eval_const_def_fn) |ext_fn| {
                if (!sym.def_id.isNone()) {
                    return ext_fn(
                        self.eval_hook.compiler_db,
                        self.eval_hook.session_id,
                        sym.def_id,
                        sym.type_id,
                        self.diagnostic_sink,
                    );
                }
            }
            return null;
        }

        var const_ast_node = sym.ast_node;
        if (self.eval_hook.compiler_db) |db| {
            if (!sym.def_id.isNone() and sym.def_id.asInt() != self.eval_hook.session_id) {
                _ = try db.getDefSignature(sym.def_id);
                const const_win = try db.getBodyAstProj(sym.def_id);
                if (!const_win.item_ast_node.isNone()) {
                    const_ast_node = const_win.item_ast_node;
                }
            }
        }

        if (const_ast_node.isNone() or const_ast_node.asInt() >= self.ast_arena.countNodes()) return null;
        const const_ast = self.ast_arena.getNode(const_ast_node);
        if (const_ast.rhs.tag != .node) return null;

        self.const_eval_stack[self.const_eval_depth] = sym_idx;
        self.const_eval_depth += 1;
        defer self.const_eval_depth -= 1;

        const saved_scope = self.current_scope;
        self.current_scope = sym.scope_id;
        defer self.current_scope = saved_scope;

        return self.tryEvalAstComptime(NodeIndex.fromInt(const_ast.rhs.payload), sym.type_id);
    }

    /// Evaluates Tier-1 compile-time AST expressions (`const`, `comptime`, reflection intrinsics, and `@field_attr_lookup`).
    fn tryEvalAstComptime(
        self: *HirLowerer,
        expr_id: NodeIndex,
        expected_ty: TypeId,
    ) anyerror!?ComptimeValue {
        if (expr_id.isNone() or expr_id.asInt() >= self.ast_arena.countNodes()) return null;
        if (!try self.enterDepth(expr_id)) return null;
        defer self.leaveDepth();

        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;

        switch (ast_node.tag) {
            .bool_lit => {
                return .{ .bool_val = !tok.isNone() and self.tokens.getToken(tok).kind == .kw_true };
            },
            .int_lit => {
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                return .{ .int_val = extractIntValue(lexeme) orelse return null };
            },
            .float_lit => {
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                return .{ .float_val = extractFloatValue(lexeme) orelse return null };
            },
            .char_lit => {
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                return .{ .char_val = extractCharValue(lexeme) };
            },
            .string_lit => {
                const raw_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                if (type_system.extractRawStringContent(raw_lex)) |raw_body| {
                    return .{ .str_val = try self.interner.intern(raw_body) };
                }
                const body = extractQuotedBody(raw_lex);
                if (type_system.scanNextInterpolationSegment(body, 0) != null) return null;
                const unescaped = try type_system.decodeStandardStringSegment(self.allocator, body);
                defer self.allocator.free(unescaped);
                return .{ .str_val = try self.interner.intern(unescaped) };
            },
            .tuple_lit, .array_lit => {
                const elems = self.getAstExtraSlice(expr_id, false);
                if (ast_node.tag == .tuple_lit and elems.len == 0) return .unit_val;
                var elem_indices: std.ArrayListUnmanaged(u32) = .empty;
                defer elem_indices.deinit(self.allocator);
                for (elems) |raw_elem| {
                    const elem_val = (try self.tryEvalAstComptime(NodeIndex.fromInt(raw_elem), .err_ty)) orelse
                        return null;
                    try elem_indices.append(self.allocator, try self.store.appendConst(elem_val));
                }
                const elem_start: u32 = @intCast(self.store.const_elements.items.len);
                try self.store.const_elements.appendSlice(self.allocator, elem_indices.items);
                const agg_ty = if (!expected_ty.isError()) expected_ty else self.nodeType(expr_id);
                return .{
                    .aggregate = .{
                        .type_id = self.concreteType(agg_ty),
                        .elem_start = elem_start,
                        .elem_len = @intCast(elem_indices.items.len),
                    },
                };
            },
            .ident_expr, .path_expr => {
                if (ast_node.tag == .ident_expr and !tok.isNone()) {
                    const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                    if (self.interner.lookup(lexeme)) |name_id| {
                        if (self.active_comptime_vals.get(name_id.asInt())) |ct_val| return ct_val;
                    }
                }
                var sym_idx = self.nodeSymbol(expr_id);
                if (sym_idx.isNone() and ast_node.tag == .ident_expr and !tok.isNone()) {
                    const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                    if (self.interner.lookup(lexeme)) |name_id| {
                        switch (self.sym_table.lookupLexical(self.current_scope, name_id, NamespaceMask.ALL)) {
                            .found => |found_idx| sym_idx = found_idx,
                            else => {},
                        }
                    }
                }
                if (!sym_idx.isNone()) {
                    const sym = self.sym_table.getSymbol(sym_idx).*;
                    if (sym.kind == .const_sym) return self.evalConstSymbol(sym_idx);
                    if (sym.kind == .enum_variant_sym and sym.type_id == .unit_ty) {
                        const enum_ty = if (!expected_ty.isError()) expected_ty else self.nodeType(expr_id);
                        return .{
                            .variant = .{
                                .type_id = self.concreteType(enum_ty),
                                .tag_ordinal = sym.member_ordinal,
                                .payload_const_idx = NONE_U32,
                            },
                        };
                    }
                }
                return null;
            },
            .contextual_variant => {
                const var_tok = if (ast_node.lhs.tag == .token)
                    TokenIndex.fromInt(ast_node.lhs.payload)
                else
                    tok;
                const var_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, var_tok);
                const args = self.getAstExtraSlice(expr_id, true);
                const res_ty = self.concreteType(if (!expected_ty.isError()) expected_ty else self.nodeType(expr_id));
                const unwrapped_res = self.pool.unwrapUnderlyingType(res_ty);
                const ty_node = self.pool.getNode(unwrapped_res);
                switch (ty_node.tag) {
                    .optional_ty => {
                        if (std.mem.eql(u8, var_name, "None")) {
                            return .{
                                .variant = .{ .type_id = res_ty, .tag_ordinal = 0, .payload_const_idx = NONE_U32 },
                            };
                        }
                        if (args.len >= 1) {
                            const inner = (try self.tryEvalAstComptime(
                                NodeIndex.fromInt(args[0]),
                                TypeId.fromInt(ty_node.lhs),
                            )) orelse return null;
                            return .{
                                .variant = .{
                                    .type_id = res_ty,
                                    .tag_ordinal = 1,
                                    .payload_const_idx = try self.store.appendConst(inner),
                                },
                            };
                        }
                    },
                    .result_ty => {
                        const is_ok = std.mem.eql(u8, var_name, "Ok");
                        const payload_ty = TypeId.fromInt(if (is_ok) ty_node.lhs else ty_node.rhs);
                        const payload_idx = if (args.len >= 1) blk: {
                            const inner = (try self.tryEvalAstComptime(
                                NodeIndex.fromInt(args[0]),
                                payload_ty,
                            )) orelse return null;
                            break :blk try self.store.appendConst(inner);
                        } else NONE_U32;
                        return .{
                            .variant = .{
                                .type_id = res_ty,
                                .tag_ordinal = if (is_ok) 0 else 1,
                                .payload_const_idx = payload_idx,
                            },
                        };
                    },
                    .enum_ty => {
                        const enum_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(ty_node.rhs)).*;
                        if (!enum_sym.target_scope.isNone()) {
                            for (self.sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
                                const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                                if (mem_sym.kind != .enum_variant_sym) continue;
                                if (std.mem.eql(u8, mem_sym.name_text, var_name)) {
                                    const payload_idx = if (args.len == 0 or mem_sym.type_id == .unit_ty)
                                        NONE_U32
                                    else blk: {
                                        const inner = (try self.tryEvalAstComptime(
                                            NodeIndex.fromInt(args[0]),
                                            mem_sym.type_id,
                                        )) orelse return null;
                                        break :blk try self.store.appendConst(inner);
                                    };
                                    return .{
                                        .variant = .{
                                            .type_id = res_ty,
                                            .tag_ordinal = mem_sym.member_ordinal,
                                            .payload_const_idx = payload_idx,
                                        },
                                    };
                                }
                            }
                        }
                    },
                    else => {},
                }
                return null;
            },
            .unary_expr => {
                if (ast_node.lhs.tag != .node) return null;
                const inner_id = NodeIndex.fromInt(ast_node.lhs.payload);
                const op_kind = self.tokens.getToken(tok).kind;
                if (op_kind == .kw_comptime) return self.tryEvalAstComptime(inner_id, expected_ty);
                if (op_kind == .minus and self.ast_arena.getNode(inner_id).tag == .int_lit) {
                    const inner_tok = self.ast_arena.getNode(inner_id).main_token;
                    const lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, inner_tok);
                    return .{ .int_val = extractNegatedIntValue(lex) orelse return null };
                }
                const sub_val = (try self.tryEvalAstComptime(inner_id, expected_ty)) orelse return null;
                return switch (op_kind) {
                    .minus => switch (sub_val) {
                        .int_val => |iv| .{ .int_val = -%iv },
                        .float_val => |fv| .{ .float_val = -fv },
                        else => null,
                    },
                    .kw_not => if (sub_val == .bool_val) .{ .bool_val = !sub_val.bool_val } else null,
                    .bang => switch (sub_val) {
                        .bool_val => |bv| .{ .bool_val = !bv },
                        .int_val => |iv| .{ .int_val = ~iv },
                        else => null,
                    },
                    else => null,
                };
            },
            .binary_expr => {
                if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .node) return null;
                const op_kind = self.tokens.getToken(tok).kind;
                const lhs_val = (try self.tryEvalAstComptime(NodeIndex.fromInt(ast_node.lhs.payload), .err_ty)) orelse
                    return null;
                if ((op_kind == .ampamp or op_kind == .kw_and) and lhs_val == .bool_val) {
                    if (!lhs_val.bool_val) return .{ .bool_val = false };
                    return self.tryEvalAstComptime(NodeIndex.fromInt(ast_node.rhs.payload), .bool_ty);
                }
                if ((op_kind == .pipepipe or op_kind == .kw_or) and lhs_val == .bool_val) {
                    if (lhs_val.bool_val) return .{ .bool_val = true };
                    return self.tryEvalAstComptime(NodeIndex.fromInt(ast_node.rhs.payload), .bool_ty);
                }
                const rhs_val = (try self.tryEvalAstComptime(NodeIndex.fromInt(ast_node.rhs.payload), .err_ty)) orelse
                    return null;
                if (lhs_val == .int_val and rhs_val == .int_val) {
                    const lv = lhs_val.int_val;
                    const rv = rhs_val.int_val;
                    return switch (op_kind) {
                        .plus, .plus_percent => .{ .int_val = lv +% rv },
                        .minus, .minus_percent => .{ .int_val = lv -% rv },
                        .star, .star_percent => .{ .int_val = lv *% rv },
                        .slash => if (rv != 0 and !(lv == std.math.minInt(i128) and rv == -1))
                            .{ .int_val = @divTrunc(lv, rv) }
                        else
                            null,
                        .percent => if (rv != 0 and !(lv == std.math.minInt(i128) and rv == -1))
                            .{ .int_val = @rem(lv, rv) }
                        else
                            null,
                        .amp => .{ .int_val = lv & rv },
                        .pipe => .{ .int_val = lv | rv },
                        .caret => .{ .int_val = lv ^ rv },
                        .shl => if (rv >= 0 and rv < 128) .{ .int_val = lv << @intCast(rv) } else null,
                        .shr => if (rv >= 0 and rv < 128) .{ .int_val = lv >> @intCast(rv) } else null,
                        .eqeq => .{ .bool_val = lv == rv },
                        .bang_eq => .{ .bool_val = lv != rv },
                        .lt => .{ .bool_val = lv < rv },
                        .le => .{ .bool_val = lv <= rv },
                        .gt => .{ .bool_val = lv > rv },
                        .ge => .{ .bool_val = lv >= rv },
                        else => null,
                    };
                }
                if (lhs_val == .bool_val and rhs_val == .bool_val) {
                    return switch (op_kind) {
                        .eqeq => .{ .bool_val = lhs_val.bool_val == rhs_val.bool_val },
                        .bang_eq => .{ .bool_val = lhs_val.bool_val != rhs_val.bool_val },
                        else => null,
                    };
                }
                if (lhs_val == .str_val and rhs_val == .str_val) {
                    return switch (op_kind) {
                        .eqeq => .{ .bool_val = lhs_val.str_val == rhs_val.str_val },
                        .bang_eq => .{ .bool_val = lhs_val.str_val != rhs_val.str_val },
                        else => null,
                    };
                }
                return null;
            },
            .field_access => {
                if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .token) return null;
                const base_val = (try self.tryEvalAstComptime(NodeIndex.fromInt(ast_node.lhs.payload), .err_ty)) orelse
                    return null;
                const member_name = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.tokens,
                    TokenIndex.fromInt(ast_node.rhs.payload),
                );
                switch (base_val) {
                    .type_info_mirror => |ti| {
                        if (std.mem.eql(u8, member_name, "name") or std.mem.eql(u8, member_name, "qualified_name")) {
                            return .{ .str_val = ti.type_name_id };
                        }
                        if (std.mem.eql(u8, member_name, "size")) return .{ .int_val = @as(i128, ti.size_bytes) };
                        if (std.mem.eql(u8, member_name, "align") or std.mem.eql(u8, member_name, "alignment")) {
                            return .{ .int_val = @as(i128, ti.align_bytes) };
                        }
                        if (std.mem.eql(u8, member_name, "id") or std.mem.eql(u8, member_name, "meta_id")) {
                            return .{ .int_val = @as(i128, ti.reflected_ty.toU32()) };
                        }
                    },
                    .field_info_mirror => |fi| {
                        if (std.mem.eql(u8, member_name, "name")) return .{ .str_val = fi.field_name };
                        if (std.mem.eql(u8, member_name, "index") or std.mem.eql(u8, member_name, "ordinal")) {
                            return .{ .int_val = @as(i128, fi.field_ordinal) };
                        }
                        if (std.mem.eql(u8, member_name, "offset") or std.mem.eql(u8, member_name, "byte_offset")) {
                            return .{ .int_val = @as(i128, fi.byte_offset) };
                        }
                        if (std.mem.eql(u8, member_name, "ty_id")) {
                            return .{ .int_val = @as(i128, fi.field_ty.toU32()) };
                        }
                        if (std.mem.eql(u8, member_name, "owner_id")) {
                            return .{ .int_val = @as(i128, fi.owner_ty.toU32()) };
                        }
                    },
                    .variant_info_mirror => |vi| {
                        if (std.mem.eql(u8, member_name, "name")) return .{ .str_val = vi.variant_name };
                        if (std.mem.eql(u8, member_name, "index") or std.mem.eql(u8, member_name, "ordinal")) {
                            return .{ .int_val = @as(i128, vi.variant_ordinal) };
                        }
                        if (std.mem.eql(u8, member_name, "owner_id")) {
                            return .{ .int_val = @as(i128, vi.owner_ty.toU32()) };
                        }
                    },
                    .aggregate => |agg| {
                        const ty_rec = self.pool.getNode(agg.type_id);
                        if (ty_rec.tag == .struct_ty) {
                            if (self.findStructFieldInfo(agg.type_id, member_name)) |f_info| {
                                if (f_info.ordinal < agg.elem_len) {
                                    const c_idx = self.store.const_elements.items[agg.elem_start + f_info.ordinal];
                                    return self.store.const_pool.items[c_idx];
                                }
                            }
                        }
                    },
                    else => {},
                }
                return null;
            },
            .method_call => {
                if (ast_node.lhs.tag != .node) return null;
                const recv_val = (try self.tryEvalAstComptime(NodeIndex.fromInt(ast_node.lhs.payload), .err_ty)) orelse
                    return null;
                const raw_items = self.getAstExtraSlice(expr_id, true);
                if (raw_items.len == 0) return null;
                const method_name = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.tokens,
                    TokenIndex.fromInt(raw_items[0]),
                );
                if (recv_val == .type_info_mirror and
                    (std.mem.eql(u8, method_name, "as_struct") or std.mem.eql(u8, method_name, "as_enum")))
                {
                    return recv_val;
                }
                if (recv_val == .field_info_mirror and std.mem.eql(u8, method_name, "get_attr")) {
                    var schema_ty: TypeId = .err_ty;
                    if (self.side_tables) |tables| {
                        if (tables.getCallInstantiation(expr_id)) |inst_slice| {
                            if (inst_slice.len >= 1) schema_ty = inst_slice[0];
                        }
                    }
                    if (schema_ty.isError()) {
                        for (raw_items[1..]) |raw_item| {
                            const item_id = NodeIndex.fromInt(raw_item);
                            if (item_id.asInt() < self.ast_arena.countNodes() and
                                isTypeAstTag(self.ast_arena.getNode(item_id).tag))
                            {
                                schema_ty = self.resolveSimpleTypeAstFallback(item_id);
                                break;
                            }
                        }
                    }
                    if (!schema_ty.isError()) {
                        return self.evalFieldAttrLookupDirect(
                            schema_ty,
                            recv_val.field_info_mirror.owner_ty,
                            recv_val.field_info_mirror.field_ordinal,
                            expected_ty,
                        );
                    }
                }
                return null;
            },
            .call_expr, .generic_call => {
                if (ast_node.lhs.tag != .node) return null;
                const callee_id = NodeIndex.fromInt(ast_node.lhs.payload);
                const callee_ast = self.ast_arena.getNode(callee_id);
                if (callee_ast.tag != .ident_expr or callee_ast.main_token.isNone() or
                    self.tokens.getToken(callee_ast.main_token).kind != .at)
                {
                    return null;
                }
                const intr_tok = if (callee_ast.lhs.tag == .token)
                    TokenIndex.fromInt(callee_ast.lhs.payload)
                else
                    callee_ast.main_token;
                const intr_kind = parseIntrinsicName(
                    symbol_resolver.extractTokenSlice(self.source, self.tokens, intr_tok),
                ) orelse return null;

                var type_args: std.ArrayListUnmanaged(TypeId) = .empty;
                defer type_args.deinit(self.allocator);
                var val_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
                defer val_arg_nodes.deinit(self.allocator);
                if (self.side_tables) |tables| {
                    if (tables.getCallInstantiation(expr_id)) |inst_slice| {
                        try type_args.appendSlice(self.allocator, inst_slice);
                    }
                }
                var t_count: usize = 0;
                for (self.getAstExtraSlice(expr_id, true)) |raw_item| {
                    const item_id = NodeIndex.fromInt(raw_item);
                    if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
                    if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) {
                        if (t_count < type_args.items.len) {
                            if (type_args.items[t_count].isError()) {
                                type_args.items[t_count] = self.resolveSimpleTypeAstFallback(item_id);
                            }
                        } else {
                            try type_args.append(self.allocator, self.resolveSimpleTypeAstFallback(item_id));
                        }
                        t_count += 1;
                    } else {
                        try val_arg_nodes.append(self.allocator, item_id);
                    }
                }
                const t_arg_0 = if (type_args.items.len >= 1) type_args.items[0] else .err_ty;
                const t_arg_1 = if (type_args.items.len >= 2) type_args.items[1] else .err_ty;
                const v_count = val_arg_nodes.items.len;

                switch (intr_kind) {
                    .size_of => {
                        if (t_arg_0.isError() or self.pool.getFlags(t_arg_0).has_type_vars) return null;
                        const layout = type_system.computeTypeLayoutWithPool(
                            self.pool,
                            self.sym_table,
                            t_arg_0,
                            self.store.target_layout,
                        );
                        if (!layout.is_sized) return null;
                        return .{ .int_val = @as(i128, layout.byte_size) };
                    },
                    .align_of => {
                        if (t_arg_0.isError() or self.pool.getFlags(t_arg_0).has_type_vars) return null;
                        const layout = type_system.computeTypeLayoutWithPool(
                            self.pool,
                            self.sym_table,
                            t_arg_0,
                            self.store.target_layout,
                        );
                        return .{ .int_val = @as(i128, layout.align_bytes) };
                    },
                    .type_name => {
                        if (t_arg_0.isError() or self.pool.getFlags(t_arg_0).has_type_vars) return null;
                        const rendered = try self.formatConcreteTypeName(t_arg_0);
                        defer self.allocator.free(rendered);
                        return .{ .str_val = try self.interner.intern(rendered) };
                    },
                    .has_field => {
                        if (t_arg_0.isError() or self.pool.getFlags(t_arg_0).has_type_vars or v_count < 1) {
                            return null;
                        }
                        const name_val = (try self.tryEvalAstComptime(val_arg_nodes.items[0], .str_ty)) orelse
                            return null;
                        if (name_val != .str_val) return null;
                        const f_name = self.interner.get(name_val.str_val);
                        return .{
                            .bool_val = self.findStructFieldInfo(self.unwrapRefType(t_arg_0), f_name) != null,
                        };
                    },
                    .implements => {
                        if (t_arg_0.isError() or t_arg_1.isError()) return null;
                        if (self.pool.getFlags(t_arg_0).has_type_vars or
                            self.pool.getFlags(t_arg_1).has_type_vars)
                        {
                            return null;
                        }
                        const bound_ty = self.pool.unwrapUnderlyingType(t_arg_1);
                        if (bound_ty.isBuiltinGroup() or self.pool.getTag(bound_ty) == .user_group) {
                            const sat = type_system.checkGroupSatisfaction(self.pool, t_arg_0, bound_ty);
                            return .{ .bool_val = sat != .rejected and sat != .rejected_distinct_without_tilde };
                        }
                        const trait_node = self.pool.getNode(bound_ty);
                        if (trait_node.tag == .trait_ty) {
                            const unwrapped_impl = self.pool.unwrapUnderlyingType(t_arg_0);
                            const unwrapped_key = (@as(u64, unwrapped_impl.toU32()) << 32) |
                                @as(u64, trait_node.rhs);
                            const raw_key = (@as(u64, t_arg_0.toU32()) << 32) | @as(u64, trait_node.rhs);
                            return .{
                                .bool_val = self.sym_table.trait_impl_pairs.contains(unwrapped_key) or
                                    self.sym_table.trait_impl_pairs.contains(raw_key),
                            };
                        }
                        return .{ .bool_val = false };
                    },
                    .type_info => {
                        if (t_arg_0.isError() or self.pool.getFlags(t_arg_0).has_type_vars) return null;
                        const layout = type_system.computeTypeLayoutWithPool(
                            self.pool,
                            self.sym_table,
                            t_arg_0,
                            self.store.target_layout,
                        );
                        const rendered = try self.formatConcreteTypeName(t_arg_0);
                        defer self.allocator.free(rendered);
                        const ty_rec = self.pool.getNode(self.unwrapRefType(t_arg_0));
                        var owner_def: DefId = .NONE;
                        if (ty_rec.tag == .struct_ty or ty_rec.tag == .enum_ty or
                            ty_rec.tag == .union_ty or ty_rec.tag == .bit_field_ty)
                        {
                            owner_def = self.sym_table.getSymbol(SymbolIndex.fromInt(ty_rec.rhs)).def_id;
                        }
                        return .{
                            .type_info_mirror = .{
                                .reflected_ty = t_arg_0,
                                .size_bytes = layout.byte_size,
                                .align_bytes = layout.align_bytes,
                                .type_name_id = try self.interner.intern(rendered),
                                .owner_def_id = owner_def,
                            },
                        };
                    },
                    .field_attr_lookup => {
                        if (t_arg_0.isError() or v_count < 2) return null;
                        return self.evalFieldAttrLookupComptime(
                            t_arg_0,
                            val_arg_nodes.items[0],
                            val_arg_nodes.items[1],
                            expected_ty,
                        );
                    },
                    else => return null,
                }
            },
            else => return null,
        }
    }

    /// Evaluates `@field_attr_lookup[A](id, idx) -> A?` into `ComptimeValue.variant` (`Some(A)` or `None`).
    fn evalFieldAttrLookupComptime(
        self: *HirLowerer,
        schema_ty: TypeId,
        meta_id_arg: NodeIndex,
        idx_arg: NodeIndex,
        expected_ty: TypeId,
    ) anyerror!?ComptimeValue {
        const id_val = (try self.tryEvalAstComptime(meta_id_arg, .err_ty)) orelse return null;
        const idx_val = (try self.tryEvalAstComptime(idx_arg, .u32_ty)) orelse return null;
        if (idx_val != .int_val or idx_val.int_val < 0) return null;
        const member_ord: u32 = @intCast(idx_val.int_val);

        var target_nominal_ty: TypeId = .err_ty;
        switch (id_val) {
            .int_val => |raw_id| {
                if (raw_id >= 0 and raw_id <= std.math.maxInt(u32)) {
                    target_nominal_ty = TypeId.fromInt(@intCast(raw_id));
                }
            },
            .type_info_mirror => |ti| target_nominal_ty = ti.reflected_ty,
            .field_info_mirror => |fi| target_nominal_ty = fi.owner_ty,
            .variant_info_mirror => |vi| target_nominal_ty = vi.owner_ty,
            else => {},
        }
        if (target_nominal_ty.isError()) return null;
        return self.evalFieldAttrLookupDirect(schema_ty, target_nominal_ty, member_ord, expected_ty);
    }

    /// Evaluates attribute metadata lookup `(schema_ty, target_nominal_ty, member_ord)` into `ComptimeValue.variant`.
    fn evalFieldAttrLookupDirect(
        self: *HirLowerer,
        schema_ty: TypeId,
        target_nominal_ty: TypeId,
        member_ord: u32,
        expected_ty: TypeId,
    ) anyerror!?ComptimeValue {
        const unwrapped_nom = self.unwrapRefType(target_nominal_ty);
        const nom_node = self.pool.getNode(unwrapped_nom);
        if (nom_node.tag != .struct_ty and nom_node.tag != .enum_ty and
            nom_node.tag != .union_ty and nom_node.tag != .bit_field_ty)
        {
            return null;
        }
        const nom_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(nom_node.rhs)).*;
        if (nom_sym.target_scope.isNone()) return null;

        var target_member_sym: SymbolIndex = .none;
        var cur_ord: u32 = 0;
        for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
            const mem_sym = self.sym_table.getSymbol(mem_idx).*;
            if (mem_sym.kind != .field_sym and mem_sym.kind != .enum_variant_sym) continue;
            if (cur_ord == member_ord) {
                target_member_sym = mem_idx;
                break;
            }
            cur_ord += 1;
        }

        const opt_ty = if (!expected_ty.isError()) expected_ty else try self.pool.internOptional(schema_ty);
        if (target_member_sym.isNone()) {
            return .{ .variant = .{ .type_id = opt_ty, .tag_ordinal = 0, .payload_const_idx = NONE_U32 } };
        }

        const unwrapped_schema = self.pool.unwrapUnderlyingType(schema_ty);
        if (self.side_tables) |tables| {
            for (tables.attr_instances) |attr_inst| {
                if (attr_inst.target_symbol == target_member_sym and
                    self.pool.unwrapUnderlyingType(attr_inst.schema_type_id) == unwrapped_schema)
                {
                    const schema_rec = self.pool.getNode(unwrapped_schema);
                    const schema_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(schema_rec.rhs)).*;
                    var field_consts: std.ArrayListUnmanaged(u32) = .empty;
                    defer field_consts.deinit(self.allocator);
                    if (!schema_sym.target_scope.isNone()) {
                        for (self.sym_table.getScopeMembers(schema_sym.target_scope)) |sf_idx| {
                            const sf_sym = self.sym_table.getSymbol(sf_idx).*;
                            if (sf_sym.kind != .field_sym) continue;
                            const cur_f_ord = field_consts.items.len;
                            var matched_val: ComptimeValue = .{ .int_val = 0 };
                            for (attr_inst.fields) |init_item| {
                                if (init_item.field_ordinal == cur_f_ord) {
                                    matched_val = attrArgToComptimeVal(init_item.value, sf_sym.type_id);
                                    break;
                                }
                            }
                            try field_consts.append(self.allocator, try self.store.appendConst(matched_val));
                        }
                    }
                    const elem_start: u32 = @intCast(self.store.const_elements.items.len);
                    try self.store.const_elements.appendSlice(self.allocator, field_consts.items);
                    const agg_const_idx = try self.store.appendConst(.{
                        .aggregate = .{
                            .type_id = schema_ty,
                            .elem_start = elem_start,
                            .elem_len = @intCast(field_consts.items.len),
                        },
                    });
                    return .{
                        .variant = .{
                            .type_id = opt_ty,
                            .tag_ordinal = 1,
                            .payload_const_idx = agg_const_idx,
                        },
                    };
                }
            }
        }

        return .{ .variant = .{ .type_id = opt_ty, .tag_ordinal = 0, .payload_const_idx = NONE_U32 } };
    }

    /// Converts a validated `AttrArgValue` into a `ComptimeValue` in `HirStore.const_pool`.
    fn attrArgToComptimeVal(arg_val: AttrArgValue, field_ty: TypeId) ComptimeValue {
        return switch (arg_val) {
            .bool_val => |bv| .{ .bool_val = bv },
            .char_val => |cv| .{ .char_val = cv },
            .int_val => |iv| .{ .int_val = iv },
            .float_val => |fv| .{ .float_val = fv },
            .str_val => |sv| .{ .str_val = sv },
            .enum_tag => |tag| .{
                .variant = .{
                    .type_id = field_ty,
                    .tag_ordinal = tag,
                    .payload_const_idx = NONE_U32,
                },
            },
            .none_opt => .{
                .variant = .{
                    .type_id = field_ty,
                    .tag_ordinal = 0,
                    .payload_const_idx = NONE_U32,
                },
            },
        };
    }

    /// Lightweight fallback resolver for simple primitive/named type AST arguments when `side_tables` is absent.
    fn resolveSimpleTypeAstFallback(self: *HirLowerer, type_node_id: NodeIndex) TypeId {
        if (type_node_id.isNone() or type_node_id.asInt() >= self.ast_arena.countNodes()) return .err_ty;
        const t_node = self.ast_arena.getNode(type_node_id);
        const lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, t_node.main_token);
        if (t_node.tag == .prim_type) {
            if (std.mem.eql(u8, lex, "bool")) return .bool_ty;
            if (std.mem.eql(u8, lex, "i8")) return .i8_ty;
            if (std.mem.eql(u8, lex, "i16")) return .i16_ty;
            if (std.mem.eql(u8, lex, "i32")) return .i32_ty;
            if (std.mem.eql(u8, lex, "i64")) return .i64_ty;
            if (std.mem.eql(u8, lex, "i128")) return .i128_ty;
            if (std.mem.eql(u8, lex, "isize")) return .isize_ty;
            if (std.mem.eql(u8, lex, "u8")) return .u8_ty;
            if (std.mem.eql(u8, lex, "u16")) return .u16_ty;
            if (std.mem.eql(u8, lex, "u32")) return .u32_ty;
            if (std.mem.eql(u8, lex, "u64")) return .u64_ty;
            if (std.mem.eql(u8, lex, "u128")) return .u128_ty;
            if (std.mem.eql(u8, lex, "usize")) return .usize_ty;
            if (std.mem.eql(u8, lex, "f32")) return .f32_ty;
            if (std.mem.eql(u8, lex, "f64")) return .f64_ty;
            if (std.mem.eql(u8, lex, "char")) return .char_ty;
            if (std.mem.eql(u8, lex, "str")) return .str_ty;
        }
        if (t_node.tag == .named_type and lex.len > 0) {
            if (self.interner.lookup(lex)) |name_id| {
                switch (self.sym_table.lookupLexical(self.current_scope, name_id, NamespaceMask.TYPE_ONLY)) {
                    .found => |sym_idx| return self.sym_table.getSymbol(sym_idx).type_id,
                    else => {},
                }
            }
        }
        return .err_ty;
    }

    /// Formats a canonical monochrome type name string for `@type_name[T]()` (`DR-05` §3.3).
    fn formatConcreteTypeName(self: *const HirLowerer, ty: TypeId) ![]u8 {
        var buf: std.ArrayListUnmanaged(u8) = .empty;
        errdefer buf.deinit(self.allocator);
        try writeTypeName(self.allocator, self.pool, self.sym_table, ty, &buf);
        return buf.toOwnedSlice(self.allocator);
    }
};

// ----------------- Standalone Literal Helpers -----------------

/// Returns `true` if `tag` is a syntactic type AST node tag.
fn isTypeAstTag(tag: AstTag) bool {
    return switch (tag) {
        .type_hole,
        .prim_type,
        .named_type,
        .generic_type,
        .tuple_type,
        .array_type,
        .slice_type,
        .ref_type,
        .ptr_type,
        .optional_type,
        .fn_type,
        .mode_type,
        => true,
        else => false,
    };
}

/// Parses an integer literal lexeme (`0x`, `0b`, `0o`, `_`, suffixes) into `i128`.
fn extractIntValue(lexeme: []const u8) ?i128 {
    const parsed = type_system.extractIntLiteralValue(lexeme) orelse return null;
    if (parsed.is_above_i128_max) return @bitCast(parsed.magnitude);
    return parsed.value;
}

/// Parses `-<int_lit>` without overflowing `minInt(i128)`.
fn extractNegatedIntValue(lexeme: []const u8) ?i128 {
    var buf: [160]u8 = undefined;
    if (lexeme.len + 1 > buf.len) return null;
    buf[0] = '-';
    @memcpy(buf[1 .. 1 + lexeme.len], lexeme);
    const parsed = type_system.extractIntLiteralValue(buf[0 .. 1 + lexeme.len]) orelse return null;
    return parsed.value;
}

/// Parses a floating-point literal lexeme (`_`, `f32`/`f64` suffixes) into `f64`.
fn extractFloatValue(raw_lexeme: []const u8) ?f64 {
    var trimmed = raw_lexeme;
    if (std.mem.endsWith(u8, trimmed, "f32") or std.mem.endsWith(u8, trimmed, "f64")) {
        trimmed = trimmed[0 .. trimmed.len - 3];
    }
    var clean_buf: [128]u8 = undefined;
    var clean_len: usize = 0;
    for (trimmed) |ch| {
        if (ch == '_') continue;
        if (clean_len >= clean_buf.len) return null;
        clean_buf[clean_len] = ch;
        clean_len += 1;
    }
    if (clean_len == 0) return null;
    return std.fmt.parseFloat(f64, clean_buf[0..clean_len]) catch null;
}

/// Decodes a `'c'`, `'\n'`, `'\xHH'`, or `'\u{…}'` character literal lexeme into its Unicode scalar `u21`.
fn extractCharValue(raw_lexeme: []const u8) u21 {
    return type_system.extractCharLiteralCodepoint(raw_lexeme) orelse 0;
}

/// Strips enclosing `"…"`, `r"…"`, or `'…'` delimiters from `raw_lexeme`.
fn extractQuotedBody(raw_lexeme: []const u8) []const u8 {
    if (type_system.extractRawStringContent(raw_lexeme)) |raw_body| return raw_body;
    if (raw_lexeme.len >= 2 and
        ((raw_lexeme[0] == '"' and raw_lexeme[raw_lexeme.len - 1] == '"') or
            (raw_lexeme[0] == '\'' and raw_lexeme[raw_lexeme.len - 1] == '\'')))
    {
        return raw_lexeme[1 .. raw_lexeme.len - 1];
    }
    return raw_lexeme;
}

/// Returns `true` if `segment_src` is a plain `ident(.ident)*` member chain (excluding `true`/`false`).
fn isPlainMemberChain(segment_src: []const u8) bool {
    if (segment_src.len == 0) return false;
    if (std.mem.eql(u8, segment_src, "true") or std.mem.eql(u8, segment_src, "false")) return false;
    var is_expecting_start = true;
    for (segment_src) |byte_ch| {
        if (byte_ch == '.') {
            if (is_expecting_start) return false;
            is_expecting_start = true;
            continue;
        }
        if (is_expecting_start) {
            if (!std.ascii.isAlphabetic(byte_ch) and byte_ch != '_') return false;
            is_expecting_start = false;
        } else {
            if (!std.ascii.isAlphanumeric(byte_ch) and byte_ch != '_') return false;
        }
    }
    return !is_expecting_start;
}

/// Resolves an `@snake_case` intrinsic identifier in $O(1)$ via `type_system.INTRINSIC_NAME_MAP`.
fn parseIntrinsicName(name_slice: []const u8) ?IntrinsicKind {
    return type_system.INTRINSIC_NAME_MAP.get(name_slice);
}

/// Appends the canonical CoreX display name of `ty` to `out_buf`.
fn writeTypeName(
    allocator: std.mem.Allocator,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    ty: TypeId,
    out_buf: *std.ArrayListUnmanaged(u8),
) anyerror!void {
    switch (ty) {
        .unit_ty => return out_buf.appendSlice(allocator, "unit"),
        .never_ty => return out_buf.appendSlice(allocator, "never"),
        .bool_ty => return out_buf.appendSlice(allocator, "bool"),
        .i8_ty => return out_buf.appendSlice(allocator, "i8"),
        .i16_ty => return out_buf.appendSlice(allocator, "i16"),
        .i32_ty, .untyped_int_ty => return out_buf.appendSlice(allocator, "i32"),
        .i64_ty => return out_buf.appendSlice(allocator, "i64"),
        .i128_ty => return out_buf.appendSlice(allocator, "i128"),
        .isize_ty => return out_buf.appendSlice(allocator, "isize"),
        .u8_ty => return out_buf.appendSlice(allocator, "u8"),
        .u16_ty => return out_buf.appendSlice(allocator, "u16"),
        .u32_ty => return out_buf.appendSlice(allocator, "u32"),
        .u64_ty => return out_buf.appendSlice(allocator, "u64"),
        .u128_ty => return out_buf.appendSlice(allocator, "u128"),
        .usize_ty => return out_buf.appendSlice(allocator, "usize"),
        .f32_ty => return out_buf.appendSlice(allocator, "f32"),
        .f64_ty, .untyped_float_ty => return out_buf.appendSlice(allocator, "f64"),
        .char_ty => return out_buf.appendSlice(allocator, "char"),
        .str_ty => return out_buf.appendSlice(allocator, "str"),
        .err_ty => return out_buf.appendSlice(allocator, "<err>"),
        else => {},
    }
    const ty_node = pool.getNode(ty);
    switch (ty_node.tag) {
        .struct_ty, .enum_ty, .union_ty, .bit_field_ty, .distinct_ty, .trait_ty => {
            const sym_idx = SymbolIndex.fromInt(ty_node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                try out_buf.appendSlice(allocator, sym_table.getSymbol(sym_idx).name_text);
            } else {
                try out_buf.appendSlice(allocator, "<nominal>");
            }
        },
        .ref_ty => {
            try out_buf.append(allocator, '&');
            try writeTypeName(allocator, pool, sym_table, TypeId.fromInt(ty_node.lhs), out_buf);
        },
        .mut_ref_ty => {
            try out_buf.appendSlice(allocator, "&mut ");
            try writeTypeName(allocator, pool, sym_table, TypeId.fromInt(ty_node.lhs), out_buf);
        },
        .raw_ptr_ty => {
            try out_buf.appendSlice(allocator, if (ty_node.rhs != 0) "*mut " else "*");
            try writeTypeName(allocator, pool, sym_table, TypeId.fromInt(ty_node.lhs), out_buf);
        },
        .slice_ty => {
            try out_buf.append(allocator, '[');
            try writeTypeName(allocator, pool, sym_table, TypeId.fromInt(ty_node.lhs), out_buf);
            try out_buf.append(allocator, ']');
        },
        .soa_slice_ty => {
            try out_buf.appendSlice(allocator, "#soa [");
            try writeTypeName(allocator, pool, sym_table, TypeId.fromInt(ty_node.lhs), out_buf);
            try out_buf.append(allocator, ']');
        },
        .array_ty, .soa_array_ty => {
            if (ty_node.tag == .soa_array_ty) try out_buf.appendSlice(allocator, "#soa ");
            try out_buf.append(allocator, '[');
            try writeTypeName(allocator, pool, sym_table, TypeId.fromInt(ty_node.lhs), out_buf);
            var len_buf: [24]u8 = undefined;
            try out_buf.appendSlice(
                allocator,
                std.fmt.bufPrint(
                    &len_buf,
                    "; {d}]",
                    .{pool.getNode(ty).rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG},
                ) catch "]",
            );
        },
        .optional_ty => {
            try writeTypeName(allocator, pool, sym_table, TypeId.fromInt(ty_node.lhs), out_buf);
            try out_buf.append(allocator, '?');
        },
        .result_ty => {
            try out_buf.appendSlice(allocator, "Result[");
            try writeTypeName(allocator, pool, sym_table, TypeId.fromInt(ty_node.lhs), out_buf);
            try out_buf.appendSlice(allocator, ", ");
            try writeTypeName(allocator, pool, sym_table, TypeId.fromInt(ty_node.rhs), out_buf);
            try out_buf.append(allocator, ']');
        },
        .tuple_ty => {
            try out_buf.append(allocator, '(');
            for (pool.getTupleElements(ty), 0..) |raw_elem, i| {
                if (i > 0) try out_buf.appendSlice(allocator, ", ");
                try writeTypeName(allocator, pool, sym_table, TypeId.fromInt(raw_elem), out_buf);
            }
            try out_buf.append(allocator, ')');
        },
        else => try out_buf.appendSlice(allocator, "<type>"),
    }
}

/// Recursively formats `hir_id` into monochrome indented text for golden snapshot testing.
fn renderHirNodeRecursive(
    allocator: std.mem.Allocator,
    store: *const HirStore,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    hir_id: HirIndex,
    indent: usize,
    out_buf: *std.ArrayListUnmanaged(u8),
) anyerror!void {
    if (hir_id.isNone() or hir_id.asInt() >= store.nodes.len) return;
    const node = store.getNode(hir_id);

    for (0..indent) |_| try out_buf.appendSlice(allocator, "  ");
    try out_buf.appendSlice(allocator, @tagName(node.tag));
    try out_buf.appendSlice(allocator, " : ");
    try writeTypeName(allocator, pool, sym_table, node.type_id, out_buf);

    switch (node.tag) {
        .hir_const_val => {
            if (node.data.lhs < store.const_pool.items.len) {
                var scratch: [64]u8 = undefined;
                switch (store.const_pool.items[node.data.lhs]) {
                    .unit_val => try out_buf.appendSlice(allocator, " = ()"),
                    .bool_val => |bv| try out_buf.appendSlice(allocator, if (bv) " = true" else " = false"),
                    .int_val => |iv| {
                        try out_buf.appendSlice(
                            allocator,
                            std.fmt.bufPrint(&scratch, " = {d}", .{iv}) catch "",
                        );
                    },
                    .float_val => |fv| {
                        try out_buf.appendSlice(
                            allocator,
                            std.fmt.bufPrint(&scratch, " = {d}", .{fv}) catch "",
                        );
                    },
                    .str_val => |sv| {
                        try out_buf.appendSlice(allocator, " = \"");
                        try out_buf.appendSlice(allocator, interner.get(sv));
                        try out_buf.append(allocator, '"');
                    },
                    else => {},
                }
            }
            try out_buf.append(allocator, '\n');
        },
        .hir_var_ref, .hir_param_decl => {
            var scratch: [32]u8 = undefined;
            try out_buf.appendSlice(
                allocator,
                std.fmt.bufPrint(&scratch, " _l{d}", .{node.data.lhs}) catch "",
            );
            if (node.data.lhs < store.locals.items.len) {
                const l_name = store.locals.items[node.data.lhs].name;
                if (l_name != .empty) {
                    try out_buf.appendSlice(allocator, " (");
                    try out_buf.appendSlice(allocator, interner.get(l_name));
                    try out_buf.append(allocator, ')');
                }
            }
            try out_buf.append(allocator, '\n');
        },
        .hir_module => {
            try out_buf.append(allocator, '\n');
            const items = store.extra_data.items[node.data.lhs .. node.data.lhs + node.data.rhs];
            for (items) |raw_child| {
                try renderHirNodeRecursive(
                    allocator,
                    store,
                    pool,
                    sym_table,
                    interner,
                    HirIndex.fromInt(raw_child),
                    indent + 1,
                    out_buf,
                );
            }
        },
        .hir_fn_decl, .hir_closure => {
            if (node.data.lhs < store.functions.items.len) {
                const fn_meta = store.functions.items[node.data.lhs];
                if (fn_meta.name != .empty) {
                    try out_buf.appendSlice(allocator, " @");
                    try out_buf.appendSlice(allocator, interner.get(fn_meta.name));
                }
                if (fn_meta.is_derived) try out_buf.appendSlice(allocator, " [derived]");
                if (fn_meta.is_subscript) try out_buf.appendSlice(allocator, " [subscript]");
            }
            try out_buf.append(allocator, '\n');
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.rhs),
                indent + 1,
                out_buf,
            );
        },
        .hir_block => {
            try out_buf.append(allocator, '\n');
            for (store.getLenPrefixedExtra(node.data.lhs)) |raw_stmt| {
                try renderHirNodeRecursive(
                    allocator,
                    store,
                    pool,
                    sym_table,
                    interner,
                    HirIndex.fromInt(raw_stmt),
                    indent + 1,
                    out_buf,
                );
            }
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.rhs),
                indent + 1,
                out_buf,
            );
        },
        .hir_local_decl => {
            var scratch: [32]u8 = undefined;
            try out_buf.appendSlice(
                allocator,
                std.fmt.bufPrint(&scratch, " _l{d}\n", .{node.data.lhs}) catch "\n",
            );
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.rhs),
                indent + 1,
                out_buf,
            );
        },
        .hir_binary_op => {
            const bin_op: HirBinaryOp = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.rhs))));
            try out_buf.appendSlice(allocator, " [");
            try out_buf.appendSlice(allocator, @tagName(bin_op));
            try out_buf.appendSlice(allocator, "]\n");
            if (node.data.lhs + 2 <= store.extra_data.items.len) {
                try renderHirNodeRecursive(
                    allocator,
                    store,
                    pool,
                    sym_table,
                    interner,
                    HirIndex.fromInt(store.extra_data.items[node.data.lhs]),
                    indent + 1,
                    out_buf,
                );
                try renderHirNodeRecursive(
                    allocator,
                    store,
                    pool,
                    sym_table,
                    interner,
                    HirIndex.fromInt(store.extra_data.items[node.data.lhs + 1]),
                    indent + 1,
                    out_buf,
                );
            }
        },
        .hir_unary_op, .hir_project_arg => {
            try out_buf.append(allocator, '\n');
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.rhs),
                indent + 1,
                out_buf,
            );
        },
        .hir_field_proj, .hir_bitfield_read, .hir_cast, .hir_return, .hir_yield => {
            try out_buf.append(allocator, '\n');
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.lhs),
                indent + 1,
                out_buf,
            );
        },
        .hir_index_proj, .hir_assign => {
            try out_buf.append(allocator, '\n');
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.lhs),
                indent + 1,
                out_buf,
            );
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.rhs),
                indent + 1,
                out_buf,
            );
        },
        .hir_soa_field_ptr, .hir_bitfield_rmw => {
            var scratch: [32]u8 = undefined;
            try out_buf.appendSlice(
                allocator,
                std.fmt.bufPrint(&scratch, " [meta={d}]\n", .{store.extra_data.items[node.data.rhs]}) catch "\n",
            );
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.lhs),
                indent + 1,
                out_buf,
            );
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(store.extra_data.items[node.data.rhs + 1]),
                indent + 1,
                out_buf,
            );
        },
        .hir_call, .hir_subscript_call => {
            try out_buf.append(allocator, '\n');
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.lhs),
                indent + 1,
                out_buf,
            );
            for (store.getLenPrefixedExtra(node.data.rhs)) |raw_arg| {
                try renderHirNodeRecursive(
                    allocator,
                    store,
                    pool,
                    sym_table,
                    interner,
                    HirIndex.fromInt(raw_arg),
                    indent + 1,
                    out_buf,
                );
            }
        },
        .hir_if => {
            try out_buf.append(allocator, '\n');
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.lhs),
                indent + 1,
                out_buf,
            );
            if (node.data.rhs + 2 <= store.extra_data.items.len) {
                try renderHirNodeRecursive(
                    allocator,
                    store,
                    pool,
                    sym_table,
                    interner,
                    HirIndex.fromInt(store.extra_data.items[node.data.rhs]),
                    indent + 1,
                    out_buf,
                );
                try renderHirNodeRecursive(
                    allocator,
                    store,
                    pool,
                    sym_table,
                    interner,
                    HirIndex.fromInt(store.extra_data.items[node.data.rhs + 1]),
                    indent + 1,
                    out_buf,
                );
            }
        },
        .hir_match => {
            try out_buf.append(allocator, '\n');
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.lhs),
                indent + 1,
                out_buf,
            );
            const arm_start = store.extra_data.items[node.data.rhs];
            const arm_len = store.extra_data.items[node.data.rhs + 1];
            for (store.match_arms.items[arm_start .. arm_start + arm_len]) |arm| {
                try renderHirNodeRecursive(
                    allocator,
                    store,
                    pool,
                    sym_table,
                    interner,
                    arm.body_hir,
                    indent + 1,
                    out_buf,
                );
            }
        },
        .hir_loop => {
            var scratch: [24]u8 = undefined;
            try out_buf.appendSlice(
                allocator,
                std.fmt.bufPrint(&scratch, " ^loop{d}\n", .{node.data.rhs}) catch "\n",
            );
            try renderHirNodeRecursive(
                allocator,
                store,
                pool,
                sym_table,
                interner,
                HirIndex.fromInt(node.data.lhs),
                indent + 1,
                out_buf,
            );
        },
        else => try out_buf.append(allocator, '\n'),
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Self-contained pipeline bundle returned by `lowerSourceToHir` for testing and standalone tools.
pub const HirSourceBundle = struct {
    /// Backing allocator.
    allocator: std.mem.Allocator,
    /// String interner owning all identifier and string literal bytes.
    interner: StringInterner,
    /// Lexical token buffer.
    tokens: TokenBuffer,
    /// Lossless CST arena.
    cst_arena: LosslessCstArena,
    /// Compact AST arena.
    ast_arena: AstArena,
    /// Resolved symbol table.
    sym_table: SymbolTable,
    /// Canonical interned type pool.
    pool: InternPool,
    /// File-wide semantic side tables.
    side_tables: BodySemanticSideTables,
    /// Lowered SoA `HirStore`.
    hir_store: HirStore,
    /// Collected frontend + lowering diagnostics.
    diagnostics: DiagnosticSink,

    /// Releases all arenas, pools, side tables, and diagnostics owned by `self`.
    pub fn deinit(self: *HirSourceBundle) void {
        self.hir_store.deinit();
        self.side_tables.deinit();
        self.pool.deinit();
        self.sym_table.deinit();
        self.ast_arena.deinit();
        self.cst_arena.deinit();
        self.tokens.deinit();
        self.diagnostics.deinit();
        self.interner.deinit();
        self.* = undefined;
    }
};

/// Lowers an entire parsed and resolved `file_id` into a canonical `HirStore`.
pub fn lowerFileToHir(
    allocator: std.mem.Allocator,
    file_id: FileId,
    source: []const u8,
    tokens: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    interner: *StringInterner,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    side_tables: ?*const BodySemanticSideTables,
    diagnostic_sink: ?*DiagnosticSink,
    target_layout: TargetLayout,
    eval_hook: ComptimeEvalHook,
) !HirStore {
    var store = HirStore.init(allocator, file_id);
    store.target_layout = target_layout;
    errdefer store.deinit();

    var lowerer = try HirLowerer.init(
        allocator,
        &store,
        interner,
        pool,
        sym_table,
        source,
        tokens,
        cst_arena,
        ast_arena,
        side_tables,
        diagnostic_sink,
        eval_hook,
    );
    defer lowerer.deinit();

    _ = try lowerer.lowerModule();
    return store;
}

/// Lowers a single `DefId` (and any synthesized `@derive` methods if `DefId` is a nominal type) into a `HirStore`.
pub fn lowerDefToHir(
    allocator: std.mem.Allocator,
    def_id: DefId,
    source: []const u8,
    tokens: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    interner: *StringInterner,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    side_tables: ?*const BodySemanticSideTables,
    diagnostic_sink: ?*DiagnosticSink,
    target_layout: TargetLayout,
    eval_hook: ComptimeEvalHook,
) !HirStore {
    const file_id = def_id.fileId();
    var store = HirStore.init(allocator, file_id);
    store.target_layout = target_layout;
    errdefer store.deinit();

    var lowerer = try HirLowerer.init(
        allocator,
        &store,
        interner,
        pool,
        sym_table,
        source,
        tokens,
        cst_arena,
        ast_arena,
        side_tables,
        diagnostic_sink,
        eval_hook,
    );
    defer lowerer.deinit();

    _ = try lowerer.lowerSingleDef(def_id);
    return store;
}

/// End-to-end helper parsing, resolving, type-checking, and lowering `source` into a `HirSourceBundle`.
pub fn lowerSourceToHir(
    allocator: std.mem.Allocator,
    source: []const u8,
    target_layout: TargetLayout,
) !HirSourceBundle {
    const file_id = FileId.fromInt(0);
    var interner = try StringInterner.init(allocator);
    errdefer interner.deinit();
    var diagnostics = DiagnosticSink.init(allocator);
    errdefer diagnostics.deinit();
    var tokens = TokenBuffer.init(allocator);
    errdefer tokens.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    errdefer cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    errdefer ast_arena.deinit();

    _ = try parser.parseSource(
        source,
        file_id,
        &tokens,
        &cst_arena,
        &ast_arena,
        &diagnostics,
        &interner,
    );

    var sym_table = try symbol_resolver.SymbolTable.init(allocator, &interner);
    errdefer sym_table.deinit();
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
    errdefer pool.deinit();

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
    errdefer side_tables.deinit();

    const hir_store = try lowerFileToHir(
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
        .{},
    );

    return .{
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
}

/// Renders `store` as a deterministic, monochrome indented `HIR` tree owned by `allocator`.
pub fn renderHir(
    allocator: std.mem.Allocator,
    store: *const HirStore,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
) ![]u8 {
    var out_buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer out_buf.deinit(allocator);
    try renderHirNodeRecursive(
        allocator,
        store,
        pool,
        sym_table,
        interner,
        store.root_hir,
        0,
        &out_buf,
    );
    return out_buf.toOwnedSlice(allocator);
}

// ---------------------------------------- MAIN -----------------------------------------

/// Counts how many `HirNode`s in `store` match `target_tag`.
fn countHirNodesByTag(store: *const HirStore, target_tag: HirTag) usize {
    var count: usize = 0;
    for (store.nodes.items(.tag)) |node_tag| {
        if (node_tag == target_tag) count += 1;
    }
    return count;
}

/// Helper parsing and lowering `source` without `TypeChecker` for syntax-desugaring unit tests.
fn lowerResolvedSourceOnly(allocator: std.mem.Allocator, source: []const u8) !HirSourceBundle {
    const file_id = FileId.fromInt(0);
    var interner = try StringInterner.init(allocator);
    errdefer interner.deinit();
    var diagnostics = DiagnosticSink.init(allocator);
    errdefer diagnostics.deinit();
    var tokens = TokenBuffer.init(allocator);
    errdefer tokens.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    errdefer cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    errdefer ast_arena.deinit();

    _ = try parser.parseSource(
        source,
        file_id,
        &tokens,
        &cst_arena,
        &ast_arena,
        &diagnostics,
        &interner,
    );

    var sym_table = try symbol_resolver.SymbolTable.init(allocator, &interner);
    errdefer sym_table.deinit();
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
    errdefer pool.deinit();
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
        null,
    );
    defer checker.deinit();
    try checker.resolveModuleSignatures();
    const side_tables: BodySemanticSideTables = .{
        .allocator = allocator,
        .def_id = .NONE,
        .ast_start = 0,
        .ast_end = 0,
        .node_types = &.{},
        .node_symbols = &.{},
    };

    const hir_store = try lowerFileToHir(
        allocator,
        file_id,
        source,
        &tokens,
        &cst_arena,
        &ast_arena,
        &interner,
        &pool,
        &sym_table,
        null,
        &diagnostics,
        TargetLayout.NATIVE_64,
        .{},
    );

    return .{
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
}

test "test_hir_soa_byte_layout_invariants_and_exact_multitoken_span_lookup" {
    const allocator = std.testing.allocator;
    try std.testing.expectEqual(@as(usize, 18), @sizeOf(HirTag) + @sizeOf(HirFlags) + @sizeOf(TypeId) +
        @sizeOf(TokenIndex) + @sizeOf(HirNode.Data));
    try std.testing.expectEqual(@as(usize, 20), @sizeOf(HirNode));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(BitSpec));

    const source =
        \\pub fn compute(alpha: i32, beta: i32) -> i32 {
        \\    return alpha + beta;
        \\}
    ;
    var bundle = try lowerSourceToHir(allocator, source, TargetLayout.NATIVE_64);
    defer bundle.deinit();
    try std.testing.expect(!bundle.diagnostics.hasErrors());

    var has_found_bin = false;
    for (0..bundle.hir_store.nodes.len) |i| {
        const hid = HirIndex.fromInt(@intCast(i));
        const node = bundle.hir_store.getNode(hid);
        if (node.tag == .hir_binary_op) {
            const span = bundle.hir_store.getSpan(
                hid,
                &bundle.ast_arena,
                &bundle.cst_arena,
                &bundle.tokens,
            );
            try std.testing.expectEqualStrings(
                "alpha + beta",
                source[span.start_byte..span.end_byte],
            );
            has_found_bin = true;
        }
    }
    try std.testing.expect(has_found_bin);

    const rendered = try renderHir(
        allocator,
        &bundle.hir_store,
        &bundle.pool,
        &bundle.sym_table,
        &bundle.interner,
    );
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.indexOf(u8, rendered, "hir_fn_decl") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered, "hir_binary_op : i32 [add]") != null);
}

test "test_hir_pipeline_try_catch_let_else_if_let_and_pattern_is_desugarings" {
    const allocator = std.testing.allocator;

    const pipe_src =
        \\pub fn add_pair(lhs_val: i32, rhs_val: i32) -> i32 { return lhs_val + rhs_val; }
        \\pub fn run_pipe(seed: i32) -> i32 {
        \\    return seed |> add_pair(10);
        \\}
    ;
    var pipe_bundle = try lowerResolvedSourceOnly(allocator, pipe_src);
    defer pipe_bundle.deinit();
    try std.testing.expect(countHirNodesByTag(&pipe_bundle.hir_store, .hir_call) >= 1);
    try std.testing.expect(countHirNodesByTag(&pipe_bundle.hir_store, .hir_project_arg) >= 1);

    const err_src =
        \\pub fn helper_opt(maybe_num: i32?) -> i32? {
        \\    let unwrapped = maybe_num?;
        \\    let safe_val = maybe_num catch 0;
        \\    let .Some(bound) = maybe_num else { return .None; };
        \\    if let .Some(inner) = maybe_num {
        \\        if maybe_num is .Some(_) {
        \\            return .Some(unwrapped + safe_val + bound + inner);
        \\        }
        \\    }
        \\    return .None;
        \\}
    ;
    var err_bundle = try lowerSourceToHir(allocator, err_src, TargetLayout.NATIVE_64);
    defer err_bundle.deinit();
    try std.testing.expect(!err_bundle.diagnostics.hasErrors());
    try std.testing.expect(countHirNodesByTag(&err_bundle.hir_store, .hir_match) >= 4);

    var has_explicit_err_return = false;
    for (0..err_bundle.hir_store.nodes.len) |i| {
        const node = err_bundle.hir_store.getNode(HirIndex.fromInt(@intCast(i)));
        if (node.tag == .hir_return and node.data.rhs == @backingInt(ReturnErrorKind.explicit_err)) {
            has_explicit_err_return = true;
            break;
        }
    }
    try std.testing.expect(has_explicit_err_return);
}

test "test_hir_for_loop_continue_safety_u8_inclusive_range_and_soa_zip" {
    const allocator = std.testing.allocator;
    const range_src =
        \\pub fn sum_bytes() -> u32 {
        \\    let mut total: u32 = 0;
        \\    let start_byte: u8 = 0;
        \\    let end_byte: u8 = 255;
        \\    for idx in start_byte..=end_byte {
        \\        if idx == 10 { continue; }
        \\        total = total + 1;
        \\    }
        \\    return total;
        \\}
    ;
    var range_bundle = try lowerSourceToHir(allocator, range_src, TargetLayout.NATIVE_64);
    defer range_bundle.deinit();
    try std.testing.expect(!range_bundle.diagnostics.hasErrors());
    try std.testing.expectEqual(@as(usize, 1), countHirNodesByTag(&range_bundle.hir_store, .hir_loop));
    try std.testing.expect(countHirNodesByTag(&range_bundle.hir_store, .hir_continue) >= 1);

    // Inclusive range `0u8..=255u8` synthesizes `_cur`, `_end`, `_is_done`, and `idx` locals:
    var has_done_bool_local = false;
    for (range_bundle.hir_store.locals.items) |loc_meta| {
        if (loc_meta.is_temp and loc_meta.type_id == .bool_ty) {
            has_done_bool_local = true;
            break;
        }
    }
    try std.testing.expect(has_done_bool_local);

    const zip_src =
        \\pub fn integrate(xs: &[i32], ys: &[i32]) -> i32 {
        \\    let mut acc: i32 = 0;
        \\    for pair in soa_zip(pos: xs, vel: ys) {
        \\        acc = acc + pair.pos + pair.1;
        \\    }
        \\    return acc;
        \\}
    ;
    var zip_bundle = try lowerResolvedSourceOnly(allocator, zip_src);
    defer zip_bundle.deinit();
    // Zero AoS tuple temporary constructed inside the loop body; direct `hir_index_proj` used:
    try std.testing.expectEqual(@as(usize, 0), countHirNodesByTag(&zip_bundle.hir_store, .hir_construct));
    try std.testing.expect(countHirNodesByTag(&zip_bundle.hir_store, .hir_index_proj) >= 2);
}

test "test_hir_soa_element_projection_equivalence_and_bit_field_lsb_lowering" {
    const allocator = std.testing.allocator;
    const soa_src =
        \\pub struct Vec2 { pub x: f32, pub y: f32 }
        \\pub fn read_both(pts: &#soa [Vec2], idx: usize) -> f32 {
        \\    let first = pts[idx].x;
        \\    let second = pts.x[idx];
        \\    return first + second;
        \\}
    ;
    var soa_bundle = try lowerSourceToHir(allocator, soa_src, TargetLayout.NATIVE_64);
    defer soa_bundle.deinit();
    try std.testing.expect(!soa_bundle.diagnostics.hasErrors());
    try std.testing.expectEqual(@as(usize, 2), countHirNodesByTag(&soa_bundle.hir_store, .hir_soa_field_ptr));

    var ords: [2]u32 = undefined;
    var ord_idx: usize = 0;
    for (0..soa_bundle.hir_store.nodes.len) |i| {
        const node = soa_bundle.hir_store.getNode(HirIndex.fromInt(@intCast(i)));
        if (node.tag == .hir_soa_field_ptr and ord_idx < 2) {
            ords[ord_idx] = soa_bundle.hir_store.extra_data.items[node.data.rhs];
            ord_idx += 1;
        }
    }
    try std.testing.expectEqual(@as(usize, 2), ord_idx);
    try std.testing.expectEqual(ords[0], ords[1]);

    const bf_src =
        \\pub bit_field StatusReg : u16 {
        \\    pub enabled: bool | 1,
        \\    pub mode: u8 | 3,
        \\    pub count: u16 | 12,
        \\}
        \\pub fn update_reg(reg: inout StatusReg) -> bool {
        \\    reg.enabled = true;
        \\    return reg.enabled;
        \\}
    ;
    var bf_bundle = try lowerSourceToHir(allocator, bf_src, TargetLayout.NATIVE_64);
    defer bf_bundle.deinit();
    try std.testing.expect(!bf_bundle.diagnostics.hasErrors());
    try std.testing.expectEqual(@as(usize, 1), countHirNodesByTag(&bf_bundle.hir_store, .hir_bitfield_rmw));
    try std.testing.expectEqual(@as(usize, 1), countHirNodesByTag(&bf_bundle.hir_store, .hir_bitfield_read));
}

test "test_hir_two_phase_derive_synthesis_and_attribute_schema_folding" {
    const allocator = std.testing.allocator;
    const derive_src =
        \\@derive(Eq, Hash, Clone, Debug)
        \\pub struct Point {
        \\    pub x: i32,
        \\    pub y: i32,
        \\}
    ;
    var derive_bundle = try lowerSourceToHir(allocator, derive_src, TargetLayout.NATIVE_64);
    defer derive_bundle.deinit();
    try std.testing.expect(!derive_bundle.diagnostics.hasErrors());

    var derived_fn_count: usize = 0;
    for (derive_bundle.hir_store.functions.items) |fn_meta| {
        if (fn_meta.is_derived) derived_fn_count += 1;
    }
    try std.testing.expectEqual(@as(usize, 4), derived_fn_count);

    const attr_src =
        \\@attribute_schema(targets = [.StructField])
        \\pub struct Column {
        \\    pub width: i32 = 8,
        \\}
        \\pub struct Row {
        \\    @Column(width = 32)
        \\    pub id: i32,
        \\}
        \\pub fn first_col() -> Column? {
        \\    return comptime @field_attr_lookup[Column](@type_info[Row]().id, 0);
        \\}
    ;
    var attr_bundle = try lowerSourceToHir(allocator, attr_src, TargetLayout.NATIVE_64);
    defer attr_bundle.deinit();
    try std.testing.expect(!attr_bundle.diagnostics.hasErrors());

    var has_some_variant = false;
    for (attr_bundle.hir_store.const_pool.items) |cval| {
        if (cval == .variant and cval.variant.tag_ordinal == 1) {
            has_some_variant = true;
            break;
        }
    }
    try std.testing.expect(has_some_variant);
}

test "test_hir_comptime_unrolling_hylo_eval_order_and_resource_caps" {
    const allocator = std.testing.allocator;
    const ct_src =
        \\pub struct Pair { pub first: i32, pub second: i64 }
        \\pub fn reflected_sum() -> usize {
        \\    let mut total: usize = 0;
        \\    comptime if @has_field[Pair]("first") {
        \\        comptime for fld in @type_info[Pair]().as_struct().fields {
        \\            let _ = fld;
        \\            total = total + @size_of[i32]();
        \\        }
        \\    }
        \\    return total;
        \\}
    ;
    var ct_bundle = try lowerSourceToHir(allocator, ct_src, TargetLayout.NATIVE_64);
    defer ct_bundle.deinit();
    try std.testing.expect(!ct_bundle.diagnostics.hasErrors());
    // Unrolled into two sequential blocks with zero runtime `hir_if` or `hir_loop`:
    try std.testing.expectEqual(@as(usize, 0), countHirNodesByTag(&ct_bundle.hir_store, .hir_if));
    try std.testing.expectEqual(@as(usize, 0), countHirNodesByTag(&ct_bundle.hir_store, .hir_loop));
    try std.testing.expectEqual(@as(usize, 2), countHirNodesByTag(&ct_bundle.hir_store, .hir_assign));

    // Exceeding `MAX_UNROLL = 4096` in `comptime for` emits `E0501`:
    const overflow_src =
        \\pub fn too_many_iters() -> i32 {
        \\    let mut count: i32 = 0;
        \\    comptime for step in 0..5000 {
        \\        let _ = step;
        \\        count = count + 1;
        \\    }
        \\    return count;
        \\}
    ;
    var overflow_bundle = try lowerResolvedSourceOnly(allocator, overflow_src);
    defer overflow_bundle.deinit();
    var has_e0501 = false;
    for (overflow_bundle.diagnostics.diagnostics.items) |diag_item| {
        if (diag_item.code == .e0501_comptime_step_limit_exceeded) {
            has_e0501 = true;
            break;
        }
    }
    try std.testing.expect(has_e0501);
}

test "test_redteam_3a_hir_conjunctive_is_shadow_isolation_comptime_for_and_operator_eq" {
    const allocator = std.testing.allocator;

    // [1] `CRIT-08`, `CRIT-09`, `CRIT-10`, `CRIT-13`, `MAJ-06`, `MAJ-07`, `MAJ-08`, `MAJ-09`:
    const valid_src =
        \\@derive(Eq)
        \\pub struct Key {
        \\    pub id: i32,
        \\}
        \\@derive(Eq, Hash, Clone, Debug)
        \\pub enum Packet {
        \\    Empty,
        \\    Single(i32),
        \\    Pair(i32, i64),
        \\}
        \\pub struct Counter {
        \\    pub val: i32,
        \\}
        \\impl Counter {
        \\    pub fn add_piped(&self, piped_val: i32, delta: i32) -> i32 {
        \\        return self.val + piped_val + delta;
        \\    }
        \\}
        \\type RawBits = distinct u64;
        \\pub bit_field WideReg : RawBits {
        \\    pub full_word: u64 | 64,
        \\}
        \\pub bit_field PtrReg : usize {
        \\    pub tag: u8 | 3,
        \\    pub rest: usize | 61,
        \\}
        \\pub fn exercise_all(outer_shadow: i32, maybe_val: i32?, lhs_key: Key, rhs_key: Key, pkt: Packet) -> i32 {
        \\    let saved_outer: i32 = outer_shadow;
        \\    let mut else_hits: i32 = 0;
        \\    if maybe_val is .Some(bound_num) and bound_num > 0 {
        \\        if lhs_key == rhs_key {
        \\            return bound_num;
        \\        }
        \\    } else {
        \\        else_hits = else_hits + 1;
        \\    }
        \\    let matched_shadow: i32 = match (maybe_val, 1) {
        \\        (.Some(outer_shadow), 1) | (.None, outer_shadow) => outer_shadow,
        \\        _ => 0,
        \\    };
        \\    let mut unrolled_sum: i32 = 0;
        \\    comptime for step in 0..6 {
        \\        comptime if step == 1 { continue; }
        \\        comptime if step == 4 { break; }
        \\        unrolled_sum = unrolled_sum + 10;
        \\    }
        \\    comptime for empty_step in 5..5 {
        \\        let _ = empty_step;
        \\        unrolled_sum = unrolled_sum + 999;
        \\    }
        \\    let ctr = Counter { val: 7 };
        \\    let piped: i32 = 5 |> ctr.add_piped(2);
        \\    let cloned_pkt: Packet = pkt.clone();
        \\    let _ = cloned_pkt.hash();
        \\    let raw_s: str = r"a\nb";
        \\    let fmt_str: str = "raw={raw_s} hex=\x41 uni=\u{03B1} sum={unrolled_sum}";
        \\    let _ = fmt_str;
        \\    return saved_outer + outer_shadow + else_hits + matched_shadow + unrolled_sum + piped;
        \\}
    ;
    var ok_bundle = try lowerSourceToHir(allocator, valid_src, TargetLayout.NATIVE_64);
    defer ok_bundle.deinit();
    try std.testing.expect(!ok_bundle.diagnostics.hasErrors());

    // Verify `else_hits = else_hits + 1` was lowered only ONCE (`CRIT-08`) and `comptime for` left zero user `hir_loop`s:
    var user_loop_count: usize = 0;
    var user_assign_count: usize = 0;
    for (0..ok_bundle.hir_store.nodes.len) |node_i| {
        const cur_node = ok_bundle.hir_store.getNode(HirIndex.fromInt(@intCast(node_i)));
        if (cur_node.flags.is_synthetic) continue;
        if (cur_node.tag == .hir_loop) user_loop_count += 1;
        if (cur_node.tag == .hir_assign) user_assign_count += 1;
    }
    try std.testing.expectEqual(@as(usize, 0), user_loop_count);
    // 1 `else_hits` assign + 3 unrolled `unrolled_sum` assigns (`step = 0, 2, 3`; `5..5` is empty!) = 4 assigns:
    try std.testing.expectEqual(@as(usize, 4), user_assign_count);

    // [2] `CRIT-10`: runtime-guarded `break` targeting an outer `comptime for` emits `E0503`:
    const bad_ct_break_src =
        \\pub fn bad_runtime_break(runtime_cond: bool) -> i32 {
        \\    let mut acc: i32 = 0;
        \\    comptime for idx in 0..3 {
        \\        let _ = idx;
        \\        if runtime_cond {
        \\            break;
        \\        }
        \\        acc = acc + 1;
        \\    }
        \\    return acc;
        \\}
    ;
    var bad_ct_bundle = try lowerSourceToHir(allocator, bad_ct_break_src, TargetLayout.NATIVE_64);
    defer bad_ct_bundle.deinit();
    var has_e0503 = false;
    for (bad_ct_bundle.diagnostics.diagnostics.items) |diag_item| {
        if (diag_item.code == .e0503_forbidden_comptime_operation) {
            has_e0503 = true;
            break;
        }
    }
    try std.testing.expect(has_e0503);

    // [3] `MAJ-02`, `MAJ-03`, `MAJ-04`: compound assign `rhs`-before-`&mut lhs`, post-arg index order, and `for` mutability:
    const eval_order_src =
        \\pub fn bump_and_get(mut counter: inout usize) -> usize {
        \\    counter = counter + 1;
        \\    return counter - 1;
        \\}
        \\pub fn loop_and_assign(slice_mut: &mut [i32]) -> i32 {
        \\    var arr: [i32; 4] = [10, 20, 30, 40];
        \\    var cursor: usize = 0;
        \\    let picked: i32 = arr[bump_and_get(cursor)];
        \\    var total: i32 = picked;
        \\    total += arr[0];
        \\    for ref elem_ref in 0..3 {
        \\        total += *elem_ref;
        \\    }
        \\    for ref mut slot_ref in slice_mut {
        \\        *slot_ref = *slot_ref + 1;
        \\    }
        \\    return total;
        \\}
    ;
    var order_bundle = try lowerSourceToHir(allocator, eval_order_src, TargetLayout.NATIVE_64);
    defer order_bundle.deinit();
    try std.testing.expect(!order_bundle.diagnostics.hasErrors());

    // [4] `CRIT-11`: `> 64` struct fields lowered into HIR without silent truncation:
    var big_struct_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer big_struct_buf.deinit(allocator);
    var field_line_buf: [64]u8 = undefined;
    try big_struct_buf.appendSlice(allocator, "pub struct WideStruct {\n");
    var i: usize = 0;
    while (i < 70) : (i += 1) {
        try big_struct_buf.appendSlice(
            allocator,
            try std.fmt.bufPrint(&field_line_buf, "    pub fld_{d}: i32,\n", .{i}),
        );
    }
    try big_struct_buf.appendSlice(allocator, "}\npub fn build_wide() -> i32 {\n    let inst = WideStruct {\n");
    i = 0;
    while (i < 70) : (i += 1) {
        try big_struct_buf.appendSlice(
            allocator,
            try std.fmt.bufPrint(&field_line_buf, "        fld_{d}: {d},\n", .{ i, i }),
        );
    }
    try big_struct_buf.appendSlice(allocator, "    };\n    return inst.fld_69;\n}\n");

    var wide_bundle = try lowerSourceToHir(allocator, big_struct_buf.items, TargetLayout.NATIVE_64);
    defer wide_bundle.deinit();
    try std.testing.expect(!wide_bundle.diagnostics.hasErrors());
}

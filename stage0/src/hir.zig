//! High-Level Intermediate Representation (`HIR`) Arena & Desugaring Engine
//!
//! Implements Phase 5 (`PLAN.md` §2.1, `DR-02`, `DR-05`, and `DR-13` Deliverable 2) Structure-of-Arrays
//! `HirNode` / `HirStore` lowering from typed `AST` + `BodySemanticSideTables`:
//! - Zero-padding 18-byte SoA `HirNode` layout (`20` bytes AoS) with bounded `MAX_HIR_NODES` and depth caps,
//! - Canonical desugaring of `|>`, postfix `?`, `catch`, `let … else`, and `is` patterns,
//! - Continue-safe and `u8`-overflow-safe `for` / `while` loop canonicalization, `#soa` projections, and `bit_field` RMW,
//! - Two-phase `@derive(Eq, Hash, Debug, Clone)` body synthesis, `comptime if`/`match`/`for` unrolling, and `renderHir`.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const diagnostic = @import("diag/diagnostic.zig");
const lexer = @import("lexer.zig");
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
const CfgEnv = type_system.CfgEnv;
const StringInterpMeta = type_system.StringInterpMeta;
const InterpHoleSpec = type_system.InterpHoleSpec;
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

    // Control Flow, Scopes & Recovery (`25..44`):
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
    /// Conjunctive `is` / `:=` conditional branch (`lhs = extra{clause_count, clauses…, then_hir, else_hir_or_none}, rhs = 0`).
    hir_cond_if = 34,
    /// Conjunctive `is` / `:=` conditional loop (`lhs = extra{clause_count, clauses…, body_hir, result_opt_local_or_none}, rhs = loop_id`).
    hir_cond_while = 35,
    /// Short-circuiting `Option[T]` fallback (`lhs = opt_hir, rhs = fallback_hir`).
    hir_orelse = 36,
    /// Diverging `unreachable` assertion (`lhs = 0, rhs = 0`).
    hir_unreachable = 37,
    /// Implicit `Context` slot read (`lhs = slot_ordinal, rhs = 0`).
    hir_ctx_get = 38,
    /// Implicit `Context` slot write (`lhs = slot_ordinal, rhs = val_hir`).
    hir_ctx_set = 39,
    /// Implicit `Context` allocator/temp region push (`lhs = slot_ordinal, rhs = val_hir`).
    hir_ctx_region_push = 40,
    /// Implicit `Context` allocator/temp region pop (`lhs = slot_ordinal, rhs = 0`).
    hir_ctx_region_pop = 41,
    /// Subslice range projection (`lhs = base_hir, rhs = extra{start_hir_or_none, end_hir_or_none, is_inclusive}`).
    hir_slice_range = 42,
    /// Error-recovery poison node preserving downstream IR invariants (`lhs = 0, rhs = 0`).
    hir_error_hole = 43,
    /// Postfix `.await` suspension point (`lhs = fut_hir, rhs = 0`).
    hir_await = 44,
};

/// Clause discriminant encoded inside `hir_cond_if` and `hir_cond_while` `extra_data` streams (`DR-21` `SE-01`/`SE-02`).
pub const HirCondClauseKind = enum(u32) {
    /// Boolean predicate clause (`extra_data`: `[0, bool_expr_hir]`).
    bool_pred = 0,
    /// Pattern `is` match clause (`extra_data`: `[1, scrutinee_hir, pat_idx]`).
    is_match = 1,
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
    /// `true` on `hir_binary_op(.sub)` when the left operand is `$` (`$ - k` traps on underflow even in release, `SE-04`).
    is_dollar_sub: bool = false,
    /// Reserved zero padding bit.
    _reserved: u1 = 0,
};

/// Zero-padding 18-byte Structure-of-Arrays `HIR` node (`20` bytes AoS).
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

/// Packed 32-bit bit-slice specification for LSB-first `bit_field` extraction and RMW (`DR-13` §2.2, `ADR-22D`).
pub const BitSpec = packed struct(u32) {
    /// Low 8 bits of zero-based bit offset (`0..255`).
    bit_offset: u8 = 0,
    /// Width of the bit-field member in bits (`1..128`).
    bit_width: u8 = 0,
    /// Width of the enclosing scalar backing integer in bits (`8..128`, or `0` for `[u8; N]` backing).
    backing_bits: u8 = 0,
    /// `true` if the extracted field type requires arithmetic sign-extension.
    is_signed: bool = false,
    /// Upper 7 bits of zero-based bit offset (`fullBitOffset() <= 32767` for `[u8; N]` backing).
    bit_offset_hi: u7 = 0,

    /// Returns the full 15-bit zero-based bit offset (`0..32767`).
    pub inline fn fullBitOffset(self: BitSpec) u15 {
        return @as(u15, self.bit_offset) | (@as(u15, self.bit_offset_hi) << 8);
    }

    /// Represents `self` as a raw 32-bit unsigned integer.
    pub inline fn asU32(self: BitSpec) u32 {
        return @bitCast(self);
    }

    /// Decodes a `BitSpec` from a raw 32-bit unsigned integer.
    pub inline fn fromU32(raw_bits: u32) BitSpec {
        return @bitCast(raw_bits);
    }
};

/// Classification of `hir_return` for `defer` vs. `errdefer` cleanup routing.
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
    /// Boolean logical negation (`not b`).
    logical_not = 1,
    /// Bitwise complement (`~x` on integers, `bit_field`, and integer SIMD vectors).
    bit_not = 2,
    /// Shared address-of borrow (`&place`).
    addr_of = 3,
    /// Exclusive mutable or out-reference address-of borrow (`&mut place` / `&out place`).
    addr_of_mut = 4,
    /// Pointer or reference dereference (`ptr.*`).
    deref = 5,
    /// Shared raw pointer address-of (`&raw place` -> `*T`, zero MVS loan).
    addr_of_raw = 6,
    /// Mutable raw pointer address-of (`&raw mut place` -> `*mut T`, zero MVS loan, allows uninitialized place).
    addr_of_raw_mut = 7,
};

/// Compiler-internal `HIR` intrinsic sub-kinds encoded via `HIR_INTERNAL_INTRINSIC_FLAG` (`D-11`, `DR-08`).
pub const HirInternalIntrinsic = enum(u8) {
    /// Checked `.narrow[Dst]()` conversion (`extra = [1, 3, dst_ty, src_hir, min_hir, max_hir]`).
    narrow_check = 0,
    /// Fallible `.try_narrow[Dst]()` conversion (`extra = [1, 3, dst_ty, src_hir, min_hir, max_hir]`).
    try_narrow = 1,
    /// Inline `Future[T]` frame construction (`extra = [0, 3 + N, def_const, sym_const, callee_hir, args…]`).
    async_future_make = 2,
    /// Structured `TaskGroup` nursery scope entry (`extra = [0, 0]`).
    async_task_group_enter = 3,
    /// Nursery child task spawn (`extra = [0, 3 + K, is_local_const, group_hir, task_hir, loan_hirs…]`).
    async_spawn = 4,
    /// Linear `TaskHandle.join()` future construction (`extra = [0, 1, handle_hir]`).
    async_join = 5,
    /// Linear `TaskHandle.cancel()` or `TaskGroup.cancel_all()` (`extra = [0, 1, target_hir]`).
    async_cancel = 6,
    /// Structured `TaskGroup` nursery exit barrier (`extra = [0, 1, group_hir]`).
    async_task_group_exit = 7,
    /// Cooperative reactor yield future construction (`extra = [0, 0]`).
    async_yield = 8,
    /// Synchronous root executor entry (`block_on(fut)`, `extra = [0, 1, fut_hir]`).
    async_block_on = 9,
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
    /// `Option[T].None` (`tag = 0`, no payload).
    optional_none = 5,
    /// `Option[T].Some(val)` (`tag = 1`, `extra = {1, val_hir}`).
    optional_some = 6,
    /// `Result[T, E].Ok(val)` (`tag = 0`, `extra = {1, val_hir}`).
    result_ok = 7,
    /// `Result[T, E].Err(err)` (`tag = 1`, `extra = {1, err_hir}`).
    result_err = 8,
    /// Zero-initialized backing integer for `bit_field` default construction.
    bitfield_zero = 9,
    /// Runtime string interpolation sequence (`extra = {part_len, part_0_hir, …}`).
    str_interp = 10,
    /// Zero-allocation `FmtArgs` descriptor (`extra = {elem_len, piece_0..piece_k, arg_ref_0, spec_0, …}`).
    fmt_args = 11,
    /// Single-value formatted `str` conversion (`extra = {2, val_hir, spec_u64_hir}`).
    fmt_value = 12,
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
    /// `true` if bound by `:=` inside a `ConditionScope` (`hir_cond_if` / `hir_cond_while`) for pre-`else` drop (`SE-01`).
    is_cond_binding: bool = false,
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
    /// `true` if this `HirFnMeta` represents the `inout` arm of a dual-arm `subscript` (`SE-21`).
    is_subscript_inout_arm: bool = false,
    /// `true` if annotated or inferred as `contextless` / `@no_alloc`.
    is_contextless: bool = false,
    /// `true` if declared `comptime fn`.
    is_comptime: bool = false,
    /// `true` if synthesized for `@derive(Eq, Hash, Debug, Clone)`.
    is_derived: bool = false,
    /// `true` if this closure carries an explicit `@local` attribute or Tier-1 borrow capture (`SE-19`).
    is_local_closure: bool = false,
    /// `true` if this closure captures outer bindings by ownership transfer (`own |…|`, Tier-2 `SE-19`).
    is_move_closure: bool = false,
    /// `true` if lowered from `async fn`, `async |…|`, `async { … }`, `async test`, or `task_group` nursery body.
    is_async: bool = false,
    /// Capture local pairs `(outer_local_id, inner_local_id)` range in `HirStore.extra_data` for closures.
    capture_extra_start: u32 = 0,
    /// Number of captured bindings for closures (`0` for non-capturing functions).
    capture_len: u32 = 0,
    /// `true` when lowered solely by `populateReferencedSameFileSubscripts` for `MirLowerer` arm splicing.
    is_splice_helper_only: bool = false,
    /// `true` when synthesized solely to capture default parameter/field capabilities during MIR SAST (`P1-5`).
    is_sast_default_probe: bool = false,
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
        /// Whole-value binding with nested sub-pattern (`x @ sub_pat`, `mut x @ sub_pat`, `ref x @ sub_pat`).
        at_pat: struct {
            /// Target `LocalId` in `HirStore.locals`.
            local_id: u32,
            /// `true` if mutable binding.
            is_mut: bool,
            /// `true` if borrowed by reference (`ref` / `&`).
            is_ref: bool,
            /// Nested `HirPat` index matched against the same scrutinee.
            sub_pat: u32,
        },
        /// Fixed-array or slice destructuring (`[p0, ..rest, s0]`; `extra_data[prefix_start..]` stores prefix then suffix `HirPat` indices).
        slice_pat: struct {
            /// Start offset in `HirStore.extra_data` of `prefix_len + suffix_len` child `HirPat` indices.
            prefix_start: u32,
            /// Number of leading element patterns before `..`.
            prefix_len: u16,
            /// Number of trailing element patterns after `..`.
            suffix_len: u16,
            /// `true` if a `..` rest wildcard or capture is present.
            has_rest: bool,
            /// Captured subslice `LocalId` in `HirStore.locals`, or `NONE_U32` when unnamed (`..`).
            rest_local_id: u32,
            /// `true` if the captured rest binding is mutable (`mut rest`).
            is_rest_mut: bool,
            /// `true` if the captured rest binding is a reference (`ref rest`).
            is_rest_ref: bool,
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

/// Packed 1-byte boolean flags governing `@must_vectorize` and `@vectorize_width` checks (`DR-19` §1, `DR-20` Seam #4).
pub const LoopContractMask = packed struct(u8) {
    /// `true` when `@must_vectorize` requires backend loop vectorization.
    is_must_vectorize: bool = false,
    /// `true` when predicated early exits are permitted inside the vectorized loop.
    has_predicated_early_exit: bool = false,
    /// `true` when scalable vectorization (`vscale`) is allowed on SVE/RVV targets.
    is_scalable_allowed: bool = true,
    /// `true` when SLP / unroll-and-jam satisfaction is permitted.
    is_slp_unroll_allowed: bool = true,
    /// `true` when floating-point reduction reassociation is permitted.
    has_reassoc_fp_reduce: bool = false,
    /// Reserved bits (`0`).
    _reserved: u3 = 0,
};

/// 8-byte SIMD loop contract payload recorded per `loop_id` (`DR-19` §1, `DR-20` Seam #4).
pub const LoopContractMeta = extern struct {
    /// Packed loop contract flags (`1B`).
    contract_flags: LoopContractMask = .{},
    /// Target override mask (`0` when target-default).
    target_override_mask: u8 = 0,
    /// Explicit `@vectorize_width(N)` lane count (`0` = canonical target vector width / `sizeof(elem)`).
    min_lanes: u16 = 0,
    /// Pre-allocated diagnostic handle (`DiagId.none` when unused).
    diag_id: mem_foundation.DiagId = .none,

    /// Alias matching `DR-19` `LoopContractMeta.Flags`.
    pub const Flags = LoopContractMask;
};

comptime {
    std.debug.assert(@sizeOf(LoopContractMask) == 1 and @bitSizeOf(LoopContractMask) == 8);
    std.debug.assert(@sizeOf(LoopContractMeta) == 8);
}

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

/// Slice descriptor in `HirStore.extra_data` storing concrete `TypeId` words for a generic `hir_call`.
pub const CallTypeArgsSpan = struct {
    /// Start index in `HirStore.extra_data`.
    start: u32,
    /// Number of `TypeId` words recorded for the call instantiation.
    len: u16,
};

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
    /// Sparse `@must_vectorize` / `@vectorize_width(N)` contracts keyed by `hir_loop` `loop_id`.
    loop_contracts: std.AutoHashMapUnmanaged(u32, LoopContractMeta) = .empty,
    /// Sparse explicit/inferred generic type-argument spans keyed by `hir_call` `HirIndex`.
    call_type_args: std.AutoHashMapUnmanaged(u32, CallTypeArgsSpan) = .empty,
    /// Synthetic `hir_block` statement spans grouping Phase 3 parallel assignment commit stores (`SE-15`).
    parallel_assign_blocks: std.AutoHashMapUnmanaged(u32, ParallelAssignSpan) = .empty,
    /// Labeled `fsm: match` metadata keyed by `hir_match` `HirIndex` (`SE-23`).
    labeled_matches: std.AutoHashMapUnmanaged(u32, LabeledMatchMeta) = .empty,
    /// Lexical declaration `FileId` recorded per `@embed_bytes` `hir_intrinsic_call` `HirIndex` (`P1-5`).
    embed_origin_files: std.AutoHashMapUnmanaged(u32, FileId) = .empty,
    /// Root `hir_module` or single-item `HirIndex` (`.none` when empty).
    root_hir: HirIndex = .none,
    /// `true` if `MAX_HIR_NODES` or `MAX_HIR_LOWER_DEPTH` was exceeded (`E0508`).
    has_overflowed_limits: bool = false,

    /// Contiguous statement slice `[first_assign_idx .. first_assign_idx + assign_count)` inside a parallel `hir_block`.
    pub const ParallelAssignSpan = struct {
        /// First `hir_assign` index within the enclosing `hir_block` statement list.
        first_assign_idx: u32,
        /// Number of parallel leaf `hir_assign` statements committed together.
        assign_count: u32,
    };

    /// Metadata recorded for a labeled `fsm: match` expression (`SE-23`).
    pub const LabeledMatchMeta = struct {
        /// Tagged FSM identifier (`LABELED_MATCH_CONTINUE_FLAG | ordinal`) matched by `hir_continue.lhs`.
        fsm_id: u32,
        /// Mutable temporary `LocalId` holding the active FSM scrutinee across `continue :fsm next` transitions.
        scrutinee_local: u32,
    };

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
        self.loop_contracts.deinit(self.allocator);
        self.call_type_args.deinit(self.allocator);
        self.parallel_assign_blocks.deinit(self.allocator);
        self.labeled_matches.deinit(self.allocator);
        self.embed_origin_files.deinit(self.allocator);
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

/// Enclosing closure capture frame tracking per-level `(outer_local_id, inner_local_id)` pairs.
const ClosureCaptureFrame = struct {
    /// Function boundary local floor (`return_local_id`) of this closure/async frame.
    ceil: u32,
    /// Dedicated `(outer_local_id, inner_local_id)` pair buffer for this frame.
    captures: std.ArrayListUnmanaged(u32) = .empty,
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

/// High-bit tag in `hir_intrinsic_call.data.lhs` selecting `HirInternalIntrinsic` over `IntrinsicKind`.
pub const HIR_INTERNAL_INTRINSIC_FLAG: u32 = 1 << 16;

/// High-bit tag in `hir_continue.data.lhs` selecting a labeled `fsm: match` target (`SE-23`).
pub const LABELED_MATCH_CONTINUE_FLAG: u32 = 1 << 31;

/// Sentinel value indicating no `HirIndex` or optional child (`0xFFFF_FFFF`).
pub const NONE_U32: u32 = std.math.maxInt(u32);

/// FNV-1a 64-bit offset basis used by synthesized `@derive(Hash)` implementations.
const FNV1A_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;

/// FNV-1a 64-bit prime multiplier used by synthesized `@derive(Hash)` implementations.
const FNV1A_PRIME: u64 = 0x0000_0100_0000_01b3;

/// $O(1)$ static lookup map of structured `core.async` / `cx.async` entry function names.
const CORE_ASYNC_ENTRY_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "block_on", {} },
    .{ "task_group", {} },
    .{ "yield_now", {} },
});

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

/// Unrolled loop control-flow state for `break` / `continue` inside `comptime for`.
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

/// Active loop frame on `HirLowerer.loop_stack` for `:label` jumps and `Option[T]` value-breaking `for`/`while` (`SE-05`/`SE-06`).
const ActiveLoopEntry = struct {
    /// Canonical `hir_loop` / `hir_cond_while` identifier.
    loop_id: u32,
    /// Optional `:label` symbol (`SymbolId.empty` when unlabeled).
    label_id: SymbolId = .empty,
    /// `true` when this frame corresponds to an unrolled `comptime for` loop.
    is_comptime_for: bool = false,
    /// Synthetic `Option[T]` local (`__loop_res`) for value-breaking `for`/`while`, or `NONE_U32` otherwise.
    result_opt_local: u32 = NONE_U32,
    /// Expected `break val` payload `TypeId` (`.unit_ty` when unit-breaking).
    payload_ty: TypeId = .unit_ty,
    /// Concrete `Option[T]` `TypeId` when `result_opt_local != NONE_U32` (`.unit_ty` otherwise).
    opt_ty: TypeId = .unit_ty,
};

/// Active `@builder` block state binding on `HirLowerer.builder_scope_stack` (`SE-22`).
const BuilderScopeEntry = struct {
    /// Underlying builder state struct `TypeId` (`S` in `&mut S`).
    state_ty: TypeId,
    /// Local slot holding `&mut S` or `S` inside the trailing `@builder` block.
    local_id: u32,
};

/// Active labeled `fsm: match` entry on `HirLowerer.labeled_match_stack` (`SE-23`).
const ActiveLabeledMatch = struct {
    /// AST `NodeIndex` of the enclosing `.match_expr`.
    match_ast: NodeIndex = .none,
    /// Tagged FSM identifier (`LABELED_MATCH_CONTINUE_FLAG | ordinal`).
    fsm_id: u32,
    /// Interned `:label` identifier (`SymbolId.empty` when unnamed).
    label_id: SymbolId = .empty,
    /// Mutable temporary `LocalId` holding the active FSM scrutinee.
    scrutinee_local: u32,
    /// Expected scrutinee `TypeId` for `continue :fsm next_state`.
    scrutinee_ty: TypeId,
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
    /// `true` while lowering inside a `task_group` nursery callback body.
    is_in_nursery_body: bool = false,
    /// `true` if `E0508` has already been emitted for this `HirStore` (prevents diagnostic floods).
    has_emitted_limit_diag: bool = false,
    /// Active function boundary local floor for closure capture detection (`0` at module level).
    closure_outer_local_ceil: u32 = 0,
    /// Enclosing top-level item `DefId` used to mint collision-free synthetic closure `DefId`s.
    active_owner_def_id: DefId = .NONE,
    /// Monotonic closure ordinal within `active_owner_def_id` (deterministic across module vs per-`DefId` lowering).
    closure_ordinal_in_owner: u32 = 0,
    /// Collected `(outer_local_id, inner_local_id)` pairs for single-level fallback capture tracking.
    active_closure_captures: std.ArrayListUnmanaged(u32) = .empty,
    /// Stack of active nested closure / `async` block / `task_group` capture frames.
    closure_frame_stack: std.ArrayListUnmanaged(ClosureCaptureFrame) = .empty,

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
    /// Floor index in `local_shadow_log` marking bindings introduced by the currently lowering pattern.
    current_pat_shadow_floor: usize = 0,
    /// `true` when unrolling the body of a `comptime for` loop.
    is_in_comptime_for: bool = false,
    /// Nesting depth of runtime conditional branches inside an active `comptime for` body.
    comptime_runtime_cond_depth: u32 = 0,
    /// Pending `break` / `continue` control-flow state for the active `comptime for` iteration.
    comptime_loop_state: ComptimeLoopState = .normal,
    /// Override outer token stamped onto sub-parsed `{expr}` string interpolation HIR nodes.
    interp_override_token: TokenIndex = .none,
    /// Override outer span used while lowering sub-parsed `{expr}` string interpolation HIR nodes.
    interp_override_span: ?Span = null,
    /// Override caller source buffer paired with `interp_override_span` for cross-file `@caller_location()` (`SE-17`).
    interp_override_source: ?[]const u8 = null,
    /// Stack of active loops in the current function for `:label` and `Option[T]` `break` resolution (`SE-05`/`SE-06`).
    loop_stack: std.ArrayListUnmanaged(ActiveLoopEntry) = .empty,
    /// Floor index in `loop_stack` isolating inner closures from outer function loops.
    closure_loop_stack_floor: usize = 0,
    /// Stack of active indexing receiver length locals (`usize`) bound to `$` (`SE-04`).
    dollar_len_stack: std.ArrayListUnmanaged(u32) = .empty,
    /// `true` while lowering a `ConditionScope` (`hir_cond_if` / `hir_cond_while`) outside nested `{ … }` blocks (`SE-01`).
    is_in_cond_scope: bool = false,
    /// `true` while lowering the direct target place of an assignment, `&mut`, or `inout` / `set` receiver (`SE-04`).
    is_mut_lvalue_ctx: bool = false,
    /// Target `@cfg(…)` evaluation context matching `store.target_layout` (`SE-18`).
    cfg_env: CfgEnv = .{},
    /// Interned name of the currently lowering function or method (`SE-17`).
    active_fn_name: SymbolId = .empty,
    /// Formal `loc: SourceLoc = @caller_location()` parameter slot in the active function (`null` if none, `SE-17`).
    active_caller_loc_local: ?u32 = null,
    /// `true` while lowering the body of an `inout` `subscript` arm (`SE-21`).
    is_in_subscript_inout_arm: bool = false,
    /// Active `@builder` state stack for implicit `@builder_item` receiver injection (`SE-22`).
    builder_scope_stack: std.ArrayListUnmanaged(BuilderScopeEntry) = .empty,
    /// Active labeled `fsm: match` stack for `continue :fsm next` state transitions (`SE-23`).
    labeled_match_stack: std.ArrayListUnmanaged(ActiveLabeledMatch) = .empty,
    /// Monotonic counter assigning unique `fsm_id` handles to labeled `match` expressions (`SE-23`).
    next_fsm_id: u32 = 0,
    /// Pre-evaluated LHS index/pointer HIR nodes keyed by `NodeIndex.asInt()` during Phase-0 parallel assignment (`SE-15`).
    parallel_pre_eval: std.AutoHashMapUnmanaged(u32, HirIndex) = .empty,
    /// Active lexical declaration `FileId` for `@embed_bytes` jail attribution and `pkg.` / dep-alias resolution (`P1-5`).
    active_lexical_file_id: FileId,
    /// `true` while `populateReferencedSameFileSubscripts` lowers cross-item helper templates.
    is_lowering_splice_helper: bool = false,

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
        const base_cfg = sym_table.effectiveCfgEnvForFile(store.file_id);
        const derived_cfg: CfgEnv = if (store.target_layout.ptr_byte_size == 4 and base_cfg.ptr_width != 32)
            .{
                .os = .wasi,
                .arch = .wasm32,
                .abi = .wasi,
                .ptr_width = 32,
                .is_debug = base_cfg.is_debug,
                .is_test_mode = base_cfg.is_test_mode,
                .is_sim_mode = base_cfg.is_sim_mode,
                .is_fuzz_mode = base_cfg.is_fuzz_mode,
                .enabled_features = base_cfg.enabled_features,
                .enabled_cpu_features = base_cfg.enabled_cpu_features,
                .owner_pkg_id = base_cfg.owner_pkg_id,
            }
        else if (store.target_layout.cache_line_align_log2 == 7 and base_cfg.arch != .aarch64)
            .{
                .os = .macos,
                .arch = .aarch64,
                .abi = .apple,
                .ptr_width = 64,
                .is_debug = base_cfg.is_debug,
                .is_test_mode = base_cfg.is_test_mode,
                .is_sim_mode = base_cfg.is_sim_mode,
                .is_fuzz_mode = base_cfg.is_fuzz_mode,
                .enabled_features = base_cfg.enabled_features,
                .enabled_cpu_features = base_cfg.enabled_cpu_features,
                .owner_pkg_id = base_cfg.owner_pkg_id,
            }
        else
            base_cfg;
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
            .cfg_env = derived_cfg,
            .active_lexical_file_id = store.file_id,
        };
    }

    /// Releases temporary lookup maps and precomputed AST/CST index slices owned by `self`.
    fn deinit(self: *HirLowerer) void {
        if (self.node_extra_end.len > 0) self.allocator.free(self.node_extra_end);
        if (self.cst_to_ast.len > 0) self.allocator.free(self.cst_to_ast);
        self.zip_arena.deinit();
        for (self.closure_frame_stack.items) |*frame| frame.captures.deinit(self.allocator);
        self.closure_frame_stack.deinit(self.allocator);
        self.active_closure_captures.deinit(self.allocator);
        self.symbol_to_local.deinit(self.allocator);
        self.active_name_to_local.deinit(self.allocator);
        self.local_shadow_log.deinit(self.allocator);
        self.active_comptime_vals.deinit(self.allocator);
        self.comptime_shadow_log.deinit(self.allocator);
        self.active_zip_bindings.deinit(self.allocator);
        self.zip_shadow_log.deinit(self.allocator);
        self.loop_stack.deinit(self.allocator);
        self.dollar_len_stack.deinit(self.allocator);
        self.builder_scope_stack.deinit(self.allocator);
        self.labeled_match_stack.deinit(self.allocator);
        self.parallel_pre_eval.deinit(self.allocator);
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

    /// Returns the element `TypeId` when `ty` is an `SE-09` union-bounded slice/str type variable (`[Data: str | &[u8]]`).
    fn unionSliceElemType(self: *const HirLowerer, ty: TypeId) ?TypeId {
        const node = self.pool.getNode(ty);
        if (node.tag != .type_param and node.tag != .bind_once_group_var and node.tag != .bind_many_any_var) {
            return null;
        }
        const grp_ty = TypeId.fromInt(node.lhs);
        const grp_node = self.pool.getNode(grp_ty);
        if (grp_node.tag != .user_group or grp_node.rhs == type_system.INTERSECT_GROUP_SENTINEL) return null;
        const view = self.pool.getUserGroupView(grp_ty) orelse return null;
        var member_count: usize = 0;
        var common_elem: TypeId = .u8_ty;
        const combined_prim_mask = view.prim_mask | view.tilde_prim_mask;
        var prim_idx: u32 = 0;
        while (prim_idx <= 18) : (prim_idx += 1) {
            const prim_tid = TypeId.fromInt(prim_idx);
            if (!type_system.TypeGroupMask.containsPrimitive(combined_prim_mask, prim_tid)) continue;
            if (prim_tid != .str_ty) return null;
            if (member_count == 0) common_elem = .u8_ty else if (common_elem != .u8_ty) common_elem = .u8_ty;
            member_count += 1;
        }
        const lists = [2][]const u32{ view.exact_members, view.tilde_members };
        for (lists) |mem_list| {
            for (mem_list) |raw_mem| {
                const unwrapped_mem = self.unwrapRefType(self.pool.unwrapUnderlyingType(TypeId.fromInt(raw_mem)));
                var mem_elem: TypeId = .u8_ty;
                if (unwrapped_mem != .str_ty) {
                    const mem_node = self.pool.getNode(unwrapped_mem);
                    if (mem_node.tag != .slice_ty and mem_node.tag != .array_ty) return null;
                    mem_elem = TypeId.fromInt(mem_node.lhs);
                }
                if (member_count == 0) common_elem = mem_elem else if (common_elem != mem_elem) common_elem = .u8_ty;
                member_count += 1;
            }
        }
        return if (member_count > 0) common_elem else null;
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

    /// Records or reuses an inner capture slot across all enclosing closure/async frames (`outer -> … -> inner`).
    fn captureOuterLocalInClosure(self: *HirLowerer, outer_local_id: u32) !u32 {
        if (self.closure_frame_stack.items.len > 0) {
            var cur_slot = outer_local_id;
            var has_entered_chain = false;
            for (self.closure_frame_stack.items) |*frame| {
                if (!has_entered_chain) {
                    if (cur_slot >= frame.ceil) continue;
                    has_entered_chain = true;
                }
                var found_inner: ?u32 = null;
                var i: usize = 0;
                while (i + 1 < frame.captures.items.len) : (i += 2) {
                    if (frame.captures.items[i] == cur_slot) {
                        found_inner = frame.captures.items[i + 1];
                        break;
                    }
                }
                if (found_inner) |existing_inner| {
                    cur_slot = existing_inner;
                } else {
                    const outer_decl = self.store.locals.items[cur_slot];
                    const inner_local = try self.store.appendLocal(.{
                        .name = outer_decl.name,
                        .type_id = outer_decl.type_id,
                        .decl_span = outer_decl.decl_span,
                        .mode = .let_mode,
                        .is_mut = outer_decl.is_mut,
                        .is_param = true,
                        .is_temp = false,
                    });
                    try frame.captures.append(self.allocator, cur_slot);
                    try frame.captures.append(self.allocator, inner_local);
                    cur_slot = inner_local;
                }
            }
            return cur_slot;
        }
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

    /// Lowers a single `DefId` item (and any `@derive` methods or referenced same-file `subscript`s) in isolation.
    fn lowerSingleDef(self: *HirLowerer, def_id: DefId) !HirIndex {
        if (def_id.isNone()) return .none;
        self.active_owner_def_id = def_id;
        self.closure_ordinal_in_owner = 0;
        const mod_scope = self.sym_table.file_module_scopes.get(self.store.file_id.asInt()) orelse
            self.sym_table.prelude_scope;
        self.current_scope = mod_scope;

        var root_result: HirIndex = .none;
        if (self.sym_table.def_to_symbol.get(def_id.asInt())) |sym_idx| {
            const sym = self.sym_table.getSymbol(sym_idx).*;
            self.current_scope = sym.scope_id;
            const fresh_override: ?NodeIndex = if (sym.owner_def_id.isNone() and
                def_id.fileId() == self.store.file_id)
                self.findTopLevelDefAstNode(def_id.itemIndex())
            else
                null;
            const lowered = try self.lowerSymbolItemWithAstOverride(sym_idx, fresh_override);
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
            root_result = lowered;
        } else if (self.ast_arena.countNodes() > 0) {
            const root_node = self.ast_arena.getNode(.root);
            if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
                const item_slice = self.ast_arena.getExtraSlice(
                    ExtraIndex.fromInt(root_node.lhs.payload),
                    root_node.rhs.payload,
                );
                const is_file_including_tests = self.sym_table.is_including_tests and
                    (self.sym_table.getFilePackageId(self.store.file_id) == .root);
                var ordinal: u12 = 0;
                for (item_slice) |raw_idx| {
                    const item_id = NodeIndex.fromInt(raw_idx);
                    if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
                    const item_tag = self.ast_arena.getNode(item_id).tag;
                    if (item_tag == .item_hole) continue;
                    if (!is_file_including_tests and (item_tag == .test_decl or item_tag == .bench_decl)) continue;
                    if (item_tag == .extern_block_decl) {
                        for (self.ast_arena.getExternBlockItems(item_id)) |ext_raw_idx| {
                            const ext_id = NodeIndex.fromInt(ext_raw_idx);
                            if (ext_id.asInt() >= self.ast_arena.countNodes()) continue;
                            const ext_tag = self.ast_arena.getNode(ext_id).tag;
                            if (ext_tag == .fn_decl or ext_tag == .extern_static_decl or ext_tag == .const_decl) {
                                if (ordinal == def_id.itemIndex()) break;
                                if (ordinal < std.math.maxInt(u12)) ordinal += 1;
                            }
                        }
                        if (ordinal == def_id.itemIndex()) break;
                        continue;
                    }
                    if (ordinal == def_id.itemIndex()) {
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
                                if (!self.isSymbolCfgEnabled(cand_sym_idx)) continue;

                                var matched_ast_override: ?NodeIndex = null;
                                while (mem_cursor < impl_members.len) {
                                    const mem_ast_idx = NodeIndex.fromInt(impl_members[mem_cursor]);
                                    mem_cursor += 1;
                                    if (mem_ast_idx.asInt() >= self.ast_arena.countNodes()) continue;
                                    const mem_ast = self.ast_arena.getNode(mem_ast_idx);
                                    const is_fn_like = mem_ast.tag == .fn_decl or mem_ast.tag == .subscript_decl or
                                        mem_ast.tag == .test_decl or mem_ast.tag == .bench_decl;
                                    const is_kind_match = (cand_sym.kind == .fn_sym and is_fn_like) or
                                        (cand_sym.kind == .const_sym and mem_ast.tag == .const_decl);
                                    if (!is_kind_match) continue;
                                    if (!self.isCstNodeCfgEnabled(self.ast_arena.getCstOrigin(mem_ast_idx))) continue;
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
                            root_result = try self.emitNode(.{
                                .tag = .hir_module,
                                .flags = .{ .category = .rvalue },
                                .type_id = .unit_ty,
                                .origin_token = self.ast_arena.getNode(item_id).main_token,
                                .data = .{
                                    .lhs = extra_start,
                                    .rhs = @intCast(lowered_members.items.len),
                                },
                            }, item_id);
                        } else {
                            root_result = try self.lowerBlockExpr(item_id, .unit_ty, false);
                        }
                        break;
                    }
                    if (ordinal < std.math.maxInt(u12)) ordinal += 1;
                }
            }
        }

        if (!root_result.isNone()) {
            try self.populateReferencedSameFileSubscripts();
            self.store.root_hir = root_result;
        }
        return root_result;
    }

    /// Resolves the flattened top-level `AstArena` node matching `target_ordinal`, expanding `extern_block_decl` items.
    fn findTopLevelDefAstNode(self: *const HirLowerer, target_ordinal: u12) ?NodeIndex {
        if (self.ast_arena.countNodes() == 0) return null;
        const root_node = self.ast_arena.getNode(.root);
        if (root_node.lhs.tag != .extra or root_node.rhs.tag != .extra or root_node.rhs.payload == 0) return null;
        const item_slice = self.ast_arena.getExtraSlice(
            ExtraIndex.fromInt(root_node.lhs.payload),
            root_node.rhs.payload,
        );
        const is_file_including_tests = self.sym_table.is_including_tests and
            (self.sym_table.getFilePackageId(self.store.file_id) == .root);
        var ordinal: u12 = 0;
        for (item_slice) |raw_idx| {
            const item_id = NodeIndex.fromInt(raw_idx);
            if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
            const item_tag = self.ast_arena.getNode(item_id).tag;
            if (item_tag == .item_hole) continue;
            if (!is_file_including_tests and (item_tag == .test_decl or item_tag == .bench_decl)) continue;
            if (item_tag == .extern_block_decl) {
                for (self.ast_arena.getExternBlockItems(item_id)) |ext_raw_idx| {
                    const ext_id = NodeIndex.fromInt(ext_raw_idx);
                    if (ext_id.asInt() >= self.ast_arena.countNodes()) continue;
                    const ext_tag = self.ast_arena.getNode(ext_id).tag;
                    if (ext_tag == .fn_decl or ext_tag == .extern_static_decl or ext_tag == .const_decl) {
                        if (ordinal == target_ordinal) return ext_id;
                        if (ordinal < std.math.maxInt(u12)) ordinal += 1;
                    }
                }
                continue;
            }
            if (ordinal == target_ordinal) return item_id;
            if (ordinal < std.math.maxInt(u12)) ordinal += 1;
        }
        return null;
    }

    /// Scans `self.store.nodes` to a bounded fixpoint and lowers any referenced same-file `subscript` templates
    /// declared in separate `impl` or top-level `DefId`s so `MirLowerer` can splice both `let` and `inout` arms.
    fn populateReferencedSameFileSubscripts(self: *HirLowerer) !void {
        var scan_idx: usize = 0;
        while (scan_idx < self.store.nodes.len) : (scan_idx += 1) {
            const cur_node = self.store.nodes.get(scan_idx);
            if (cur_node.tag != .hir_subscript_call) continue;
            const callee_hir = HirIndex.fromInt(cur_node.data.lhs);
            if (callee_hir.isNone() or callee_hir.asInt() >= self.store.nodes.len) continue;
            const callee_node = self.store.getNode(callee_hir);
            if (callee_node.tag != .hir_global_ref) continue;
            const sub_sym_idx = SymbolIndex.fromInt(callee_node.data.rhs);
            if (sub_sym_idx.isNone() or sub_sym_idx.asInt() >= self.sym_table.symbols.items.len) continue;

            var has_existing = false;
            for (self.store.functions.items) |fn_meta| {
                if (fn_meta.is_subscript and fn_meta.symbol_index == sub_sym_idx) {
                    has_existing = true;
                    break;
                }
            }
            if (has_existing) continue;

            const sub_sym = self.sym_table.getSymbol(sub_sym_idx).*;
            if (!sub_sym.decl_span.file_id.isNone() and sub_sym.decl_span.file_id != self.store.file_id) continue;
            if (!self.isSymbolCfgEnabled(sub_sym_idx)) continue;

            const matched_ast = self.resolveSameFileSubscriptAst(sub_sym_idx);
            const saved_tables = self.side_tables;
            const saved_scope = self.current_scope;
            const saved_splice_flag = self.is_lowering_splice_helper;
            self.side_tables = null;
            self.current_scope = sub_sym.scope_id;
            self.is_lowering_splice_helper = true;
            defer {
                self.side_tables = saved_tables;
                self.current_scope = saved_scope;
                self.is_lowering_splice_helper = saved_splice_flag;
            }
            const fn_floor = self.store.functions.items.len;
            _ = try self.lowerSymbolItemWithAstOverride(sub_sym_idx, matched_ast);
            for (self.store.functions.items[fn_floor..]) |*meta_item| {
                meta_item.is_splice_helper_only = true;
            }
        }
    }

    /// Resolves the `.subscript_decl` `NodeIndex` for `sub_sym_idx` inside `self.ast_arena` when `ast_node` was cleared.
    fn resolveSameFileSubscriptAst(
        self: *const HirLowerer,
        sub_sym_idx: SymbolIndex,
    ) ?NodeIndex {
        const sub_sym = self.sym_table.getSymbol(sub_sym_idx).*;
        if (!sub_sym.ast_node.isNone() and sub_sym.ast_node.asInt() < self.ast_arena.countNodes() and
            self.ast_arena.getNode(sub_sym.ast_node).tag == .subscript_decl)
        {
            return sub_sym.ast_node;
        }
        if (!sub_sym.owner_def_id.isNone() and self.ast_arena.countNodes() > 0) {
            const root_node = self.ast_arena.getNode(.root);
            if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
                const item_slice = self.ast_arena.getExtraSlice(
                    ExtraIndex.fromInt(root_node.lhs.payload),
                    root_node.rhs.payload,
                );
                const is_file_including_tests = self.sym_table.is_including_tests and
                    (self.sym_table.getFilePackageId(self.store.file_id) == .root);
                var ordinal: u12 = 0;
                for (item_slice) |raw_idx| {
                    const item_id = NodeIndex.fromInt(raw_idx);
                    if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
                    const item_tag = self.ast_arena.getNode(item_id).tag;
                    if (item_tag == .item_hole) continue;
                    if (!is_file_including_tests and (item_tag == .test_decl or item_tag == .bench_decl)) continue;
                    if (item_tag == .extern_block_decl) {
                        for (self.ast_arena.getExternBlockItems(item_id)) |ext_raw_idx| {
                            const ext_id = NodeIndex.fromInt(ext_raw_idx);
                            if (ext_id.asInt() >= self.ast_arena.countNodes()) continue;
                            const ext_tag = self.ast_arena.getNode(ext_id).tag;
                            if (ext_tag == .fn_decl or ext_tag == .extern_static_decl or ext_tag == .const_decl) {
                                if (ordinal < std.math.maxInt(u12)) ordinal += 1;
                            }
                        }
                        continue;
                    }
                    if (ordinal == sub_sym.owner_def_id.itemIndex()) {
                        if (item_tag == .impl_decl) {
                            const impl_members = symbol_resolver.extractImplMemberItems(self.ast_arena, item_id);
                            var mem_cursor: usize = 0;
                            var sym_raw: u32 = 0;
                            while (sym_raw < self.sym_table.symbols.items.len) : (sym_raw += 1) {
                                const cand_sym_idx = SymbolIndex.fromInt(sym_raw);
                                const cand_sym = self.sym_table.getSymbol(cand_sym_idx).*;
                                if (cand_sym.owner_def_id != sub_sym.owner_def_id) continue;
                                if (cand_sym.kind != .fn_sym and cand_sym.kind != .const_sym) continue;
                                if (!self.isSymbolCfgEnabled(cand_sym_idx)) continue;

                                var matched_override: ?NodeIndex = null;
                                while (mem_cursor < impl_members.len) {
                                    const mem_ast_idx = NodeIndex.fromInt(impl_members[mem_cursor]);
                                    mem_cursor += 1;
                                    if (mem_ast_idx.asInt() >= self.ast_arena.countNodes()) continue;
                                    const mem_ast = self.ast_arena.getNode(mem_ast_idx);
                                    const is_fn_like = mem_ast.tag == .fn_decl or mem_ast.tag == .subscript_decl or
                                        mem_ast.tag == .test_decl or mem_ast.tag == .bench_decl;
                                    const is_kind_match = (cand_sym.kind == .fn_sym and is_fn_like) or
                                        (cand_sym.kind == .const_sym and mem_ast.tag == .const_decl);
                                    if (!is_kind_match) continue;
                                    if (!self.isCstNodeCfgEnabled(self.ast_arena.getCstOrigin(mem_ast_idx))) continue;
                                    matched_override = mem_ast_idx;
                                    break;
                                }
                                if (cand_sym_idx == sub_sym_idx) return matched_override;
                            }
                        }
                        break;
                    }
                    if (ordinal < std.math.maxInt(u12)) ordinal += 1;
                }
            }
        }
        var raw_node_idx: u32 = 0;
        while (raw_node_idx < self.ast_arena.countNodes()) : (raw_node_idx += 1) {
            const cand_id = NodeIndex.fromInt(raw_node_idx);
            const cand_node = self.ast_arena.getNode(cand_id);
            if (cand_node.tag != .subscript_decl or cand_node.main_token.isNone() or
                cand_node.main_token.asInt() >= self.tokens.countTokens()) continue;
            const tok_span = self.tokens.getTokenSpan(self.store.file_id, cand_node.main_token);
            if (tok_span.start_byte == sub_sym.decl_span.start_byte) return cand_id;
        }
        return null;
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
            if (!self.isSymbolCfgEnabled(sym_idx)) continue;

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
                                if (!self.isSymbolCfgEnabled(member_idx)) continue;
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
                    if (!sym.target_scope.isNone() and !sym.ast_node.isNone() and
                        self.sym_table.scope_arena.getScope(sym.target_scope).file_id == self.store.file_id)
                    {
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
                if (sym.kind == .struct_sym and !self.is_lowering_splice_helper and
                    !sym.flags.is_imported and !sym.flags.is_builtin)
                {
                    try self.synthesizeStructFieldDefaultSastProbe(sym_idx, tok);
                }
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
            if (proto_ast.rhs.tag != .node and proto_ast.rhs.tag != .extra) return .none;
        }
        if (eff_ast.isNone()) return .none;

        const fn_ast = self.ast_arena.getNode(eff_ast);
        const sig_view = self.pool.getFnSignatureView(fn_sym.type_id) orelse return .none;

        const is_subscript = fn_ast.tag == .subscript_decl or (!fn_ast.main_token.isNone() and
            fn_ast.main_token.asInt() < self.tokens.countTokens() and
            std.mem.eql(
                u8,
                symbol_resolver.extractTokenSlice(self.source, self.tokens, fn_ast.main_token),
                "subscript",
            ));
        const is_async_fn = sig_view.is_async or
            self.hasKeywordInCst(self.ast_arena.getCstOrigin(eff_ast), .kw_async);
        const is_contextless = !is_async_fn and (self.hasContextlessAttr(fn_sym_idx) or sig_view.is_c_abi);

        if (fn_ast.tag == .subscript_decl and fn_ast.rhs.tag == .extra) {
            return self.lowerSubscriptDeclArms(fn_sym_idx, eff_ast, sig_view, is_contextless);
        }

        const saved_scope = self.current_scope;
        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_loop_id = self.current_loop_id;
        const saved_closure_ceil = self.closure_outer_local_ceil;
        const saved_owner_def = self.active_owner_def_id;
        const saved_closure_ord = self.closure_ordinal_in_owner;
        const saved_fn_name = self.active_fn_name;
        const saved_caller_loc = self.active_caller_loc_local;
        const saved_in_sub_inout = self.is_in_subscript_inout_arm;
        const saved_in_unsafe = self.is_in_unsafe;
        const saved_in_nursery = self.is_in_nursery_body;
        const saved_closure_frames = self.closure_frame_stack;
        self.closure_frame_stack = .empty;
        const builder_floor = self.builder_scope_stack.items.len;
        const fsm_floor = self.labeled_match_stack.items.len;
        const local_checkpoint = self.local_shadow_log.items.len;
        const ct_checkpoint = self.comptime_shadow_log.items.len;
        defer {
            for (self.closure_frame_stack.items) |*frame| frame.captures.deinit(self.allocator);
            self.closure_frame_stack.deinit(self.allocator);
            self.closure_frame_stack = saved_closure_frames;
            self.popComptimeBindingsTo(ct_checkpoint);
            self.popLexicalLocalsTo(local_checkpoint);
            self.builder_scope_stack.items.len = builder_floor;
            self.labeled_match_stack.items.len = fsm_floor;
            self.current_scope = saved_scope;
            self.current_fn_ret_ty = saved_ret_ty;
            self.current_loop_id = saved_loop_id;
            self.closure_outer_local_ceil = saved_closure_ceil;
            self.active_owner_def_id = saved_owner_def;
            self.closure_ordinal_in_owner = saved_closure_ord;
            self.active_fn_name = saved_fn_name;
            self.active_caller_loc_local = saved_caller_loc;
            self.is_in_subscript_inout_arm = saved_in_sub_inout;
            self.is_in_unsafe = saved_in_unsafe;
            self.is_in_nursery_body = saved_in_nursery;
        }
        self.is_in_nursery_body = false;

        self.is_in_unsafe = if (self.sym_table.getFfiContract(fn_sym_idx)) |fc| fc.is_unsafe_extern else false;
        self.current_scope = if (!fn_sym.target_scope.isNone()) fn_sym.target_scope else fn_sym.scope_id;
        self.current_fn_ret_ty = sig_view.ret_ty;
        self.current_loop_id = null;
        self.loop_stack.clearRetainingCapacity();
        self.closure_loop_stack_floor = 0;
        self.dollar_len_stack.clearRetainingCapacity();
        self.is_in_cond_scope = false;
        self.closure_outer_local_ceil = 0;
        self.active_fn_name = fn_sym.name;
        self.active_caller_loc_local = null;
        self.is_in_subscript_inout_arm = false;
        if (!fn_sym.def_id.isNone()) {
            self.active_owner_def_id = fn_sym.def_id;
            self.closure_ordinal_in_owner = 0;
        }

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
        const fn_param_specs = self.sym_table.fn_param_specs.get(fn_sym_idx.asInt());

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
            if (fn_param_specs) |specs| {
                if (param_idx < specs.len and specs[param_idx].is_caller_location_default) {
                    self.active_caller_loc_local = slot_id;
                }
            }
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
            .is_async = is_async_fn,
        });

        // [3] Lower function body block or single-expression `= Expr;` body if present:
        var body_hir: HirIndex = .none;
        if (fn_ast.rhs.tag == .node) {
            const body_ast_id = NodeIndex.fromInt(fn_ast.rhs.payload);
            if (!body_ast_id.isNone() and body_ast_id.asInt() < self.ast_arena.countNodes() and
                self.ast_arena.getNode(body_ast_id).tag == .block)
            {
                body_hir = try self.lowerBlockExpr(body_ast_id, sig_view.ret_ty, !is_subscript);
            } else {
                const expr_hir = try self.lowerExpr(body_ast_id, sig_view.ret_ty);
                var body_stmts: [1]u32 = undefined;
                if (is_subscript) {
                    const yield_node = try self.emitNode(.{
                        .tag = .hir_yield,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = self.store.getNode(expr_hir).type_id,
                        .origin_token = fn_ast.main_token,
                        .data = .{ .lhs = expr_hir.asInt(), .rhs = 0 },
                    }, body_ast_id);
                    body_stmts[0] = yield_node.asInt();
                    body_hir = try self.emitSyntheticBlock(&body_stmts, .none, .unit_ty, fn_ast.main_token);
                } else if (!expr_hir.isNone() and self.store.getNode(expr_hir).type_id == .never_ty) {
                    body_stmts[0] = expr_hir.asInt();
                    body_hir = try self.emitSyntheticBlock(&body_stmts, .none, .never_ty, fn_ast.main_token);
                } else {
                    const err_kind = self.classifyReturnExpr(expr_hir, sig_view.ret_ty);
                    const ret_node = try self.emitNode(.{
                        .tag = .hir_return,
                        .flags = .{ .category = .diverging, .is_synthetic = true },
                        .type_id = .never_ty,
                        .origin_token = fn_ast.main_token,
                        .data = .{ .lhs = expr_hir.asInt(), .rhs = @backingInt(err_kind) },
                    }, body_ast_id);
                    body_stmts[0] = ret_node.asInt();
                    body_hir = try self.emitSyntheticBlock(&body_stmts, .none, .never_ty, fn_ast.main_token);
                }
            }
        }

        const total_locals: u32 = @intCast(self.store.locals.items.len - return_local_id);
        self.store.functions.items[fn_meta_idx].body_hir = body_hir;
        self.store.functions.items[fn_meta_idx].total_local_len = total_locals;

        const decl_hir = try self.emitNode(.{
            .tag = .hir_fn_decl,
            .flags = .{ .category = .rvalue },
            .type_id = fn_sym.type_id,
            .origin_token = fn_ast.main_token,
            .data = .{ .lhs = fn_meta_idx, .rhs = body_hir.asInt() },
        }, eff_ast);
        if (!self.is_lowering_splice_helper and !fn_sym.flags.is_imported and !fn_sym.flags.is_builtin) {
            try self.synthesizeFnParamDefaultSastProbe(fn_sym_idx, sig_view, fn_ast.main_token);
        }
        return decl_hir;
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
            if (sub.kind == .fn_introducer or sub.kind == .block or sub.kind == .fn_expr_body) break;
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

    /// Lowers `subscript(…) -> Elem { let { … } inout { … } }` accessor arms into `HirStore.functions` (`SE-21`).
    fn lowerSubscriptDeclArms(
        self: *HirLowerer,
        fn_sym_idx: SymbolIndex,
        eff_ast: NodeIndex,
        sig_view: type_system.FnSignatureView,
        is_contextless: bool,
    ) anyerror!HirIndex {
        const fn_sym = self.sym_table.getSymbol(fn_sym_idx).*;
        const fn_ast = self.ast_arena.getNode(eff_ast);
        const extra_start: usize = fn_ast.rhs.payload;
        if (extra_start >= self.ast_arena.extra_data.items.len) return .none;
        const arm_count: usize = self.ast_arena.extra_data.items[extra_start];
        if (arm_count == 0) return .none;

        const self_sym_id = try self.interner.intern("self");
        const self_type_sym_id = try self.interner.intern("Self");
        const base_fn_scope = if (!fn_sym.target_scope.isNone()) fn_sym.target_scope else fn_sym.scope_id;
        const has_explicit_self = self.hasSubscriptExplicitSelf(fn_sym_idx);
        const enclosing_self_ty: TypeId = switch (self.sym_table.lookupLexical(
            fn_sym.scope_id,
            self_type_sym_id,
            NamespaceMask.TYPE_ONLY,
        )) {
            .found => |self_ty_idx| self.sym_table.getSymbol(self_ty_idx).type_id,
            else => .err_ty,
        };

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

        const saved_scope = self.current_scope;
        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_loop_id = self.current_loop_id;
        const saved_closure_ceil = self.closure_outer_local_ceil;
        const saved_owner_def = self.active_owner_def_id;
        const saved_closure_ord = self.closure_ordinal_in_owner;
        const saved_fn_name = self.active_fn_name;
        const saved_caller_loc = self.active_caller_loc_local;
        const saved_in_sub_inout = self.is_in_subscript_inout_arm;
        defer {
            self.current_scope = saved_scope;
            self.current_fn_ret_ty = saved_ret_ty;
            self.current_loop_id = saved_loop_id;
            self.closure_outer_local_ceil = saved_closure_ceil;
            self.active_owner_def_id = saved_owner_def;
            self.closure_ordinal_in_owner = saved_closure_ord;
            self.active_fn_name = saved_fn_name;
            self.active_caller_loc_local = saved_caller_loc;
            self.is_in_subscript_inout_arm = saved_in_sub_inout;
        }

        if (!fn_sym.def_id.isNone()) {
            self.active_owner_def_id = fn_sym.def_id;
            self.closure_ordinal_in_owner = 0;
        }

        var first_decl_hir: HirIndex = .none;
        var arm_idx: usize = 0;
        while (arm_idx < arm_count) : (arm_idx += 1) {
            const pair_base = extra_start + 1 + arm_idx * 2;
            if (pair_base + 1 >= self.ast_arena.extra_data.items.len) break;
            const arm_mode = self.ast_arena.extra_data.items[pair_base];
            const arm_blk_id = NodeIndex.fromInt(self.ast_arena.extra_data.items[pair_base + 1]);
            if (arm_blk_id.isNone() or arm_blk_id.asInt() >= self.ast_arena.countNodes()) continue;

            const local_checkpoint = self.local_shadow_log.items.len;
            const ct_checkpoint = self.comptime_shadow_log.items.len;
            defer {
                self.popComptimeBindingsTo(ct_checkpoint);
                self.popLexicalLocalsTo(local_checkpoint);
            }

            self.current_scope = base_fn_scope;
            self.current_fn_ret_ty = sig_view.ret_ty;
            self.current_loop_id = null;
            self.loop_stack.clearRetainingCapacity();
            self.closure_loop_stack_floor = 0;
            self.dollar_len_stack.clearRetainingCapacity();
            self.is_in_cond_scope = false;
            self.closure_outer_local_ceil = 0;
            self.active_fn_name = fn_sym.name;
            self.active_caller_loc_local = null;
            self.is_in_subscript_inout_arm = (arm_mode == 1);

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
            var total_params: u32 = 0;

            if (!has_explicit_self and !enclosing_self_ty.isError()) {
                const arm_self_ty = try self.pool.internRef(self.concreteType(enclosing_self_ty), arm_mode == 1);
                const self_slot = try self.store.appendLocal(.{
                    .name = self_sym_id,
                    .type_id = arm_self_ty,
                    .decl_span = fn_sym.decl_span,
                    .mode = .let_mode,
                    .is_mut = false,
                    .is_param = true,
                    .is_temp = false,
                });
                try self.pushLexicalLocal(self_sym_id, self_slot);
                _ = try self.emitNode(.{
                    .tag = .hir_param_decl,
                    .flags = .{ .category = .place_imm },
                    .type_id = arm_self_ty,
                    .origin_token = fn_ast.main_token,
                    .data = .{ .lhs = self_slot, .rhs = @backingInt(ParamMode.let_mode) },
                }, .none);
                total_params += 1;
            }

            var param_i: usize = 0;
            while (param_i < sig_view.paramCount()) : (param_i += 1) {
                const p_ty = self.concreteType(sig_view.getParamType(param_i));
                const p_mode = sig_view.getParamMode(param_i);
                const p_sym_idx = if (param_i < param_syms.len) param_syms[param_i] else SymbolIndex.none;
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
                total_params += 1;
            }

            const arm_meta_idx: u32 = @intCast(self.store.functions.items.len);
            try self.store.functions.append(self.allocator, .{
                .def_id = fn_sym.def_id,
                .symbol_index = fn_sym_idx,
                .name = fn_sym.name,
                .fn_ty = fn_sym.type_id,
                .ret_ty = self.concreteType(sig_view.ret_ty),
                .return_local_id = return_local_id,
                .param_local_start = param_local_start,
                .param_len = total_params,
                .is_subscript = true,
                .is_subscript_inout_arm = (arm_mode == 1),
                .is_contextless = is_contextless,
                .is_comptime = fn_sym.flags.is_comptime,
                .is_derived = false,
            });

            const arm_body_hir = try self.lowerBlockExpr(arm_blk_id, .unit_ty, false);
            const total_locals: u32 = @intCast(self.store.locals.items.len - return_local_id);
            self.store.functions.items[arm_meta_idx].body_hir = arm_body_hir;
            self.store.functions.items[arm_meta_idx].total_local_len = total_locals;

            const decl_hir = try self.emitNode(.{
                .tag = .hir_fn_decl,
                .flags = .{ .category = .rvalue },
                .type_id = fn_sym.type_id,
                .origin_token = fn_ast.main_token,
                .data = .{ .lhs = arm_meta_idx, .rhs = arm_body_hir.asInt() },
            }, eff_ast);
            if (first_decl_hir.isNone()) first_decl_hir = decl_hir;
        }
        if (!self.is_lowering_splice_helper and !fn_sym.flags.is_imported and !fn_sym.flags.is_builtin) {
            try self.synthesizeFnParamDefaultSastProbe(fn_sym_idx, sig_view, fn_ast.main_token);
        }
        return first_decl_hir;
    }

    /// Synthesizes an `is_sast_default_probe` `HirFnMeta` lowering declared struct field defaults in `struct_sym_idx` (`P1-5`).
    fn synthesizeStructFieldDefaultSastProbe(
        self: *HirLowerer,
        struct_sym_idx: SymbolIndex,
        origin_tok: TokenIndex,
    ) anyerror!void {
        const struct_sym = self.sym_table.getSymbol(struct_sym_idx).*;
        if (struct_sym.target_scope.isNone()) return;

        var has_any_default = false;
        for (self.sym_table.getScopeMembers(struct_sym.target_scope)) |mem_idx| {
            const field_sym = self.sym_table.getSymbol(mem_idx).*;
            if (field_sym.kind != .field_sym) continue;
            if (!field_sym.decl_span.file_id.isNone() and field_sym.decl_span.file_id != self.store.file_id) continue;
            const def_ast = extractStructFieldDefaultAst(
                field_sym,
                self.ast_arena,
                self.cst_arena,
                self.tokens,
                self.cst_to_ast,
            );
            if (!def_ast.isNone()) {
                has_any_default = true;
                break;
            }
        }
        if (!has_any_default) return;

        const saved_scope = self.current_scope;
        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_loop_id = self.current_loop_id;
        const saved_closure_ceil = self.closure_outer_local_ceil;
        const saved_owner_def = self.active_owner_def_id;
        const saved_closure_ord = self.closure_ordinal_in_owner;
        const saved_fn_name = self.active_fn_name;
        const saved_caller_loc = self.active_caller_loc_local;
        const saved_in_sub_inout = self.is_in_subscript_inout_arm;
        const saved_in_unsafe = self.is_in_unsafe;
        const saved_in_nursery = self.is_in_nursery_body;
        const saved_lex_file = self.active_lexical_file_id;
        const saved_closure_frames = self.closure_frame_stack;
        self.closure_frame_stack = .empty;
        const builder_floor = self.builder_scope_stack.items.len;
        const fsm_floor = self.labeled_match_stack.items.len;
        const local_checkpoint = self.local_shadow_log.items.len;
        const ct_checkpoint = self.comptime_shadow_log.items.len;
        defer {
            for (self.closure_frame_stack.items) |*frame| frame.captures.deinit(self.allocator);
            self.closure_frame_stack.deinit(self.allocator);
            self.closure_frame_stack = saved_closure_frames;
            self.popComptimeBindingsTo(ct_checkpoint);
            self.popLexicalLocalsTo(local_checkpoint);
            self.builder_scope_stack.items.len = builder_floor;
            self.labeled_match_stack.items.len = fsm_floor;
            self.current_scope = saved_scope;
            self.current_fn_ret_ty = saved_ret_ty;
            self.current_loop_id = saved_loop_id;
            self.closure_outer_local_ceil = saved_closure_ceil;
            self.active_owner_def_id = saved_owner_def;
            self.closure_ordinal_in_owner = saved_closure_ord;
            self.active_fn_name = saved_fn_name;
            self.active_caller_loc_local = saved_caller_loc;
            self.is_in_subscript_inout_arm = saved_in_sub_inout;
            self.is_in_unsafe = saved_in_unsafe;
            self.is_in_nursery_body = saved_in_nursery;
            self.active_lexical_file_id = saved_lex_file;
        }

        self.current_scope = struct_sym.target_scope;
        self.current_fn_ret_ty = .unit_ty;
        self.current_loop_id = null;
        self.loop_stack.clearRetainingCapacity();
        self.closure_loop_stack_floor = 0;
        self.dollar_len_stack.clearRetainingCapacity();
        self.is_in_cond_scope = false;
        self.closure_outer_local_ceil = 0;
        self.active_fn_name = struct_sym.name;
        self.active_caller_loc_local = null;
        self.is_in_subscript_inout_arm = false;
        self.is_in_unsafe = false;
        self.is_in_nursery_body = false;
        if (!struct_sym.def_id.isNone()) {
            self.active_owner_def_id = struct_sym.def_id;
        }

        const return_local_id = try self.store.appendLocal(.{
            .name = .empty,
            .type_id = .unit_ty,
            .decl_span = struct_sym.decl_span,
            .mode = .set_mode,
            .is_mut = true,
            .is_param = false,
            .is_temp = true,
        });
        const param_local_start: u32 = @intCast(self.store.locals.items.len);
        const probe_meta_idx: u32 = @intCast(self.store.functions.items.len);
        try self.store.functions.append(self.allocator, .{
            .def_id = struct_sym.def_id,
            .symbol_index = struct_sym_idx,
            .name = struct_sym.name,
            .fn_ty = .unit_ty,
            .ret_ty = .unit_ty,
            .return_local_id = return_local_id,
            .param_local_start = param_local_start,
            .param_len = 0,
            .is_sast_default_probe = true,
        });

        var probe_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer probe_stmts.deinit(self.allocator);
        for (self.sym_table.getScopeMembers(struct_sym.target_scope)) |mem_idx| {
            const field_sym = self.sym_table.getSymbol(mem_idx).*;
            if (field_sym.kind != .field_sym) continue;
            if (!field_sym.decl_span.file_id.isNone() and field_sym.decl_span.file_id != self.store.file_id) continue;
            const def_ast = extractStructFieldDefaultAst(
                field_sym,
                self.ast_arena,
                self.cst_arena,
                self.tokens,
                self.cst_to_ast,
            );
            if (def_ast.isNone()) continue;
            self.active_lexical_file_id = if (!field_sym.decl_span.file_id.isNone())
                field_sym.decl_span.file_id
            else
                self.store.file_id;
            const expr_hir = try self.lowerExpr(def_ast, self.concreteType(field_sym.type_id));
            if (!expr_hir.isNone()) {
                try probe_stmts.append(self.allocator, expr_hir.asInt());
            }
        }
        const probe_body_hir = try self.emitSyntheticBlock(probe_stmts.items, .none, .unit_ty, origin_tok);
        const total_locals: u32 = @intCast(self.store.locals.items.len - return_local_id);
        self.store.functions.items[probe_meta_idx].body_hir = probe_body_hir;
        self.store.functions.items[probe_meta_idx].total_local_len = total_locals;
    }

    /// Synthesizes an `is_sast_default_probe` `HirFnMeta` lowering declared parameter defaults on `fn_sym_idx` (`P1-5`).
    fn synthesizeFnParamDefaultSastProbe(
        self: *HirLowerer,
        fn_sym_idx: SymbolIndex,
        sig_view: type_system.FnSignatureView,
        origin_tok: TokenIndex,
    ) anyerror!void {
        const specs = self.sym_table.fn_param_specs.get(fn_sym_idx.asInt()) orelse return;
        var has_any_default = false;
        for (specs) |spec| {
            if (spec.has_default and !spec.is_caller_location_default and !spec.default_ast_node.isNone() and
                (spec.decl_file_id.isNone() or spec.decl_file_id == self.store.file_id))
            {
                has_any_default = true;
                break;
            }
        }
        if (!has_any_default) return;

        const fn_sym = self.sym_table.getSymbol(fn_sym_idx).*;
        const saved_scope = self.current_scope;
        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_loop_id = self.current_loop_id;
        const saved_closure_ceil = self.closure_outer_local_ceil;
        const saved_owner_def = self.active_owner_def_id;
        const saved_closure_ord = self.closure_ordinal_in_owner;
        const saved_fn_name = self.active_fn_name;
        const saved_caller_loc = self.active_caller_loc_local;
        const saved_in_sub_inout = self.is_in_subscript_inout_arm;
        const saved_in_unsafe = self.is_in_unsafe;
        const saved_in_nursery = self.is_in_nursery_body;
        const saved_lex_file = self.active_lexical_file_id;
        const saved_sym_to_local = self.symbol_to_local;
        self.symbol_to_local = .empty;
        const saved_closure_frames = self.closure_frame_stack;
        self.closure_frame_stack = .empty;
        const builder_floor = self.builder_scope_stack.items.len;
        const fsm_floor = self.labeled_match_stack.items.len;
        const local_checkpoint = self.local_shadow_log.items.len;
        const ct_checkpoint = self.comptime_shadow_log.items.len;
        defer {
            self.symbol_to_local.deinit(self.allocator);
            self.symbol_to_local = saved_sym_to_local;
            for (self.closure_frame_stack.items) |*frame| frame.captures.deinit(self.allocator);
            self.closure_frame_stack.deinit(self.allocator);
            self.closure_frame_stack = saved_closure_frames;
            self.popComptimeBindingsTo(ct_checkpoint);
            self.popLexicalLocalsTo(local_checkpoint);
            self.builder_scope_stack.items.len = builder_floor;
            self.labeled_match_stack.items.len = fsm_floor;
            self.current_scope = saved_scope;
            self.current_fn_ret_ty = saved_ret_ty;
            self.current_loop_id = saved_loop_id;
            self.closure_outer_local_ceil = saved_closure_ceil;
            self.active_owner_def_id = saved_owner_def;
            self.closure_ordinal_in_owner = saved_closure_ord;
            self.active_fn_name = saved_fn_name;
            self.active_caller_loc_local = saved_caller_loc;
            self.is_in_subscript_inout_arm = saved_in_sub_inout;
            self.is_in_unsafe = saved_in_unsafe;
            self.is_in_nursery_body = saved_in_nursery;
            self.active_lexical_file_id = saved_lex_file;
        }

        self.current_scope = if (!fn_sym.target_scope.isNone()) fn_sym.target_scope else fn_sym.scope_id;
        self.current_fn_ret_ty = .unit_ty;
        self.current_loop_id = null;
        self.loop_stack.clearRetainingCapacity();
        self.closure_loop_stack_floor = 0;
        self.dollar_len_stack.clearRetainingCapacity();
        self.is_in_cond_scope = false;
        self.closure_outer_local_ceil = 0;
        self.active_fn_name = fn_sym.name;
        self.active_caller_loc_local = null;
        self.is_in_subscript_inout_arm = false;
        self.is_in_unsafe = false;
        self.is_in_nursery_body = false;
        if (!fn_sym.def_id.isNone()) {
            self.active_owner_def_id = fn_sym.def_id;
        }

        const return_local_id = try self.store.appendLocal(.{
            .name = .empty,
            .type_id = .unit_ty,
            .decl_span = fn_sym.decl_span,
            .mode = .set_mode,
            .is_mut = true,
            .is_param = false,
            .is_temp = true,
        });
        const param_local_start: u32 = @intCast(self.store.locals.items.len);

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
            const param_ty = self.concreteType(sig_view.getParamType(param_idx));
            const param_mode = sig_view.getParamMode(param_idx);
            const param_sym_idx = if (param_idx < param_syms.len) param_syms[param_idx] else SymbolIndex.none;
            const param_name = if (!param_sym_idx.isNone())
                self.sym_table.getSymbol(param_sym_idx).name
            else
                SymbolId.empty;
            const param_span = if (!param_sym_idx.isNone())
                self.sym_table.getSymbol(param_sym_idx).decl_span
            else
                fn_sym.decl_span;
            const is_param_mut = (!param_sym_idx.isNone() and self.sym_table.getSymbol(param_sym_idx).flags.is_mut) or
                param_mode == .inout_mode or param_mode == .set_mode;
            const slot_id = try self.store.appendLocal(.{
                .name = param_name,
                .type_id = param_ty,
                .decl_span = param_span,
                .mode = param_mode,
                .is_mut = is_param_mut,
                .is_param = true,
                .is_temp = false,
                .is_comptime = !param_sym_idx.isNone() and self.sym_table.getSymbol(param_sym_idx).flags.is_comptime,
                .symbol_index = param_sym_idx,
            });
            if (!param_sym_idx.isNone()) {
                try self.symbol_to_local.put(self.allocator, param_sym_idx.asInt(), slot_id);
            }
            try self.pushLexicalLocal(param_name, slot_id);
        }

        const probe_meta_idx: u32 = @intCast(self.store.functions.items.len);
        try self.store.functions.append(self.allocator, .{
            .def_id = fn_sym.def_id,
            .symbol_index = fn_sym_idx,
            .name = fn_sym.name,
            .fn_ty = fn_sym.type_id,
            .ret_ty = .unit_ty,
            .return_local_id = return_local_id,
            .param_local_start = param_local_start,
            .param_len = @intCast(sig_view.paramCount()),
            .is_sast_default_probe = true,
        });

        var probe_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer probe_stmts.deinit(self.allocator);
        for (specs, 0..) |spec, spec_idx| {
            if (!spec.has_default or spec.is_caller_location_default or spec.default_ast_node.isNone()) continue;
            if (!spec.decl_file_id.isNone() and spec.decl_file_id != self.store.file_id) continue;
            self.active_lexical_file_id = if (!spec.decl_file_id.isNone()) spec.decl_file_id else self.store.file_id;
            const expected_ty = if (spec_idx < sig_view.paramCount())
                self.concreteType(sig_view.getParamType(spec_idx))
            else
                .err_ty;
            const expr_hir = try self.lowerExpr(spec.default_ast_node, expected_ty);
            if (!expr_hir.isNone()) {
                try probe_stmts.append(self.allocator, expr_hir.asInt());
            }
        }
        const probe_body_hir = try self.emitSyntheticBlock(probe_stmts.items, .none, .unit_ty, origin_tok);
        const total_locals: u32 = @intCast(self.store.locals.items.len - return_local_id);
        self.store.functions.items[probe_meta_idx].body_hir = probe_body_hir;
        self.store.functions.items[probe_meta_idx].total_local_len = total_locals;
    }

    /// Checks whether `fn_sym_idx` carries a `@contextless` attribute in CST.
    fn hasContextlessAttr(self: *const HirLowerer, fn_sym_idx: SymbolIndex) bool {
        const sym = self.sym_table.getSymbol(fn_sym_idx).*;
        return self.hasAttrNamedInCst(sym.cst_node, "contextless");
    }

    /// Returns `true` unless `sym_idx` was pruned by `@cfg(…)` in `TypeChecker` or CST evaluation (`SE-18`).
    fn isSymbolCfgEnabled(self: *const HirLowerer, sym_idx: SymbolIndex) bool {
        if (sym_idx.isNone() or sym_idx.asInt() >= self.sym_table.symbols.items.len) return false;
        const sym = self.sym_table.getSymbol(sym_idx).*;
        if (sym.flags.is_builtin or sym.flags.is_imported) return true;
        if (!self.hasAttrNamedInCst(sym.cst_node, "cfg")) return true;
        if (!sym.scope_id.isNone()) {
            const scoped_key: u64 = (@as(u64, sym.name.asInt()) << 32) |
                (@as(u64, @backingInt(sym.namespace)) << 30) |
                @as(u64, sym.scope_id.asInt() & 0x3FFF_FFFF);
            if (!self.sym_table.scoped_map.contains(scoped_key)) return false;
        }
        return self.isCstNodeCfgEnabled(sym.cst_node);
    }

    /// Returns `true` unless statement `stmt_id` was pruned by `@cfg(…)` (`SE-18`).
    fn isAstStmtCfgEnabled(self: *const HirLowerer, stmt_id: NodeIndex) bool {
        if (stmt_id.isNone() or stmt_id.asInt() >= self.ast_arena.countNodes()) return false;
        const stmt_cst = self.ast_arena.getCstOrigin(stmt_id);
        if (!self.hasAttrNamedInCst(stmt_cst, "cfg")) return true;
        if (self.side_tables != null) {
            const stmt_node = self.ast_arena.getNode(stmt_id);
            if (stmt_node.lhs.tag == .node) {
                const lhs_id = NodeIndex.fromInt(stmt_node.lhs.payload);
                if (!lhs_id.isNone() and lhs_id.asInt() < self.ast_arena.countNodes()) {
                    return !self.nodeType(lhs_id).isError();
                }
            }
            if (stmt_node.rhs.tag == .node) {
                const rhs_id = NodeIndex.fromInt(stmt_node.rhs.payload);
                if (!rhs_id.isNone() and rhs_id.asInt() < self.ast_arena.countNodes()) {
                    return !self.nodeType(rhs_id).isError();
                }
            }
        }
        return self.isCstNodeCfgEnabled(stmt_cst);
    }

    /// Evaluates leading `@cfg(…)` CST attributes on `cst_id` against `self.cfg_env` (`SE-18`).
    fn isCstNodeCfgEnabled(self: *const HirLowerer, cst_id: CstNodeIndex) bool {
        if (cst_id.isNone() or cst_id.asInt() >= self.cst_arena.countNodes()) return true;
        const start_idx: usize = cst_id.asInt();
        const root_rec = self.cst_arena.getNode(cst_id);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, root_rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var cursor: usize = start_idx + 1;
        while (cursor < end_idx) : (cursor += 1) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
            if (sub.kind == .block or sub.kind == .fn_expr_body or sub.kind == .param_list or
                sub.kind == .type_params or sub.kind == .struct_introducer or
                sub.kind == .enum_introducer or sub.kind == .union_introducer)
            {
                break;
            }
            if (sub.subtree_size <= 1 and !sub.token.isNone() and
                sub.token.asInt() < self.tokens.countTokens() and
                self.tokens.getToken(sub.token).kind == .lbrace)
            {
                break;
            }
            if (sub.kind == .attribute) {
                const attr_end = @min(cursor + @max(@as(usize, sub.subtree_size), 1), end_idx);
                if (!self.isSingleCfgAttrActive(cursor, attr_end)) return false;
                if (sub.subtree_size > 1) cursor += @as(usize, sub.subtree_size) - 1;
            }
        }
        return true;
    }

    /// Evaluates a single `.attribute` CST range `[attr_start .. attr_end)` if named `cfg`.
    fn isSingleCfgAttrActive(self: *const HirLowerer, attr_start: usize, attr_end: usize) bool {
        var attr_tokens: [128]TokenIndex = undefined;
        var tok_count: usize = 0;
        var has_name = false;
        var has_lparen = false;
        var paren_depth: u32 = 0;

        var cur = attr_start + 1;
        while (cur < attr_end) : (cur += 1) {
            const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (leaf.subtree_size > 1 or leaf.flags.is_missing_or_injected or
                leaf.token.isNone() or leaf.token.asInt() >= self.tokens.countTokens())
            {
                continue;
            }
            const tok = leaf.token;
            const kind = self.tokens.getToken(tok).kind;
            if (kind == .at) continue;
            if (!has_name) {
                has_name = true;
                const attr_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                if (!std.mem.eql(u8, attr_lex, "cfg")) return true;
                continue;
            }
            if (!has_lparen) {
                if (kind == .lparen) {
                    has_lparen = true;
                    paren_depth = 1;
                }
                continue;
            }
            if (kind == .lparen) {
                paren_depth += 1;
            } else if (kind == .rparen) {
                if (paren_depth == 1) break;
                if (paren_depth > 0) paren_depth -= 1;
            }
            if (tok_count < attr_tokens.len) {
                attr_tokens[tok_count] = tok;
                tok_count += 1;
            }
        }
        if (!has_lparen or tok_count == 0) return true;
        var pos: usize = 0;
        return self.evalCfgOrTokens(attr_tokens[0..tok_count], &pos);
    }

    /// Evaluates `OrExpr = AndExpr { "or" AndExpr }` over `@cfg` tokens (`SE-18`).
    fn evalCfgOrTokens(self: *const HirLowerer, cfg_tokens: []const TokenIndex, pos: *usize) bool {
        var lhs = self.evalCfgAndTokens(cfg_tokens, pos);
        while (pos.* < cfg_tokens.len and self.tokens.getToken(cfg_tokens[pos.*]).kind == .kw_or) {
            pos.* += 1;
            const rhs = self.evalCfgAndTokens(cfg_tokens, pos);
            lhs = lhs or rhs;
        }
        return lhs;
    }

    /// Evaluates `AndExpr = UnaryExpr { "and" UnaryExpr }` over `@cfg` tokens (`SE-18`).
    fn evalCfgAndTokens(self: *const HirLowerer, cfg_tokens: []const TokenIndex, pos: *usize) bool {
        var lhs = self.evalCfgUnaryTokens(cfg_tokens, pos);
        while (pos.* < cfg_tokens.len and self.tokens.getToken(cfg_tokens[pos.*]).kind == .kw_and) {
            pos.* += 1;
            const rhs = self.evalCfgUnaryTokens(cfg_tokens, pos);
            lhs = lhs and rhs;
        }
        return lhs;
    }

    /// Evaluates `UnaryExpr = "not" UnaryExpr | AtomExpr` over `@cfg` tokens (`SE-18`).
    fn evalCfgUnaryTokens(self: *const HirLowerer, cfg_tokens: []const TokenIndex, pos: *usize) bool {
        if (pos.* >= cfg_tokens.len) return true;
        if (self.tokens.getToken(cfg_tokens[pos.*]).kind == .kw_not) {
            pos.* += 1;
            return !self.evalCfgUnaryTokens(cfg_tokens, pos);
        }
        return self.evalCfgAtomTokens(cfg_tokens, pos);
    }

    /// Evaluates an atomic `@cfg` predicate against `self.cfg_env` (`SE-18`).
    fn evalCfgAtomTokens(self: *const HirLowerer, cfg_tokens: []const TokenIndex, pos: *usize) bool {
        if (pos.* >= cfg_tokens.len) return true;
        const start_tok = cfg_tokens[pos.*];
        const start_kind = self.tokens.getToken(start_tok).kind;
        if (start_kind == .lparen) {
            pos.* += 1;
            const inner = self.evalCfgOrTokens(cfg_tokens, pos);
            if (pos.* < cfg_tokens.len and self.tokens.getToken(cfg_tokens[pos.*]).kind == .rparen) pos.* += 1;
            return inner;
        }
        if (start_kind == .kw_true) {
            pos.* += 1;
            return true;
        }
        if (start_kind == .kw_false) {
            pos.* += 1;
            return false;
        }
        var segs: [4][]const u8 = undefined;
        var seg_count: usize = 0;
        if (!symbol_resolver.isIdentifierToken(start_kind) and start_kind != .kw_pub and start_kind != .prim_type) {
            pos.* += 1;
            return true;
        }
        segs[0] = symbol_resolver.extractTokenSlice(self.source, self.tokens, start_tok);
        seg_count = 1;
        pos.* += 1;
        while (seg_count < segs.len and pos.* + 1 < cfg_tokens.len and
            self.tokens.getToken(cfg_tokens[pos.*]).kind == .dot)
        {
            const next_tok = cfg_tokens[pos.* + 1];
            if (!symbol_resolver.isIdentifierToken(self.tokens.getToken(next_tok).kind)) break;
            segs[seg_count] = symbol_resolver.extractTokenSlice(self.source, self.tokens, next_tok);
            seg_count += 1;
            pos.* += 2;
        }
        var eff_segs: []const []const u8 = segs[0..seg_count];
        if (eff_segs.len >= 2 and std.mem.eql(u8, eff_segs[0], "core")) eff_segs = eff_segs[1..];
        if (eff_segs.len >= 2 and (std.mem.eql(u8, eff_segs[0], "target") or std.mem.eql(u8, eff_segs[0], "cfg"))) {
            eff_segs = eff_segs[1..];
        }
        if (eff_segs.len == 2 and std.mem.eql(u8, eff_segs[0], "feature")) {
            if (self.sym_table.has_package_feature_manifest.contains(self.cfg_env.owner_pkg_id)) {
                return self.sym_table.isPackageFeatureEnabled(self.cfg_env.owner_pkg_id, eff_segs[1]);
            }
            if (self.sym_table.isPackageFeatureEnabled(self.cfg_env.owner_pkg_id, eff_segs[1])) {
                return true;
            }
            for (self.cfg_env.enabled_features) |feat| {
                if (std.mem.eql(u8, feat, eff_segs[1])) return true;
            }
            return false;
        }
        if (eff_segs.len != 1) return true;
        const key = eff_segs[0];
        if (std.mem.eql(u8, key, "feature") or std.mem.eql(u8, key, "cpu_has")) {
            if (pos.* + 2 < cfg_tokens.len and
                self.tokens.getToken(cfg_tokens[pos.*]).kind == .lparen and
                self.tokens.getToken(cfg_tokens[pos.* + 1]).kind == .string_lit and
                self.tokens.getToken(cfg_tokens[pos.* + 2]).kind == .rparen)
            {
                const raw_lit = symbol_resolver.extractTokenSlice(self.source, self.tokens, cfg_tokens[pos.* + 1]);
                pos.* += 3;
                const item_name = if (raw_lit.len >= 2) raw_lit[1 .. raw_lit.len - 1] else "";
                if (std.mem.eql(u8, key, "feature")) {
                    if (self.sym_table.has_package_feature_manifest.contains(self.cfg_env.owner_pkg_id)) {
                        return self.sym_table.isPackageFeatureEnabled(self.cfg_env.owner_pkg_id, item_name);
                    }
                    if (self.sym_table.isPackageFeatureEnabled(self.cfg_env.owner_pkg_id, item_name)) {
                        return true;
                    }
                }
                const slice = if (std.mem.eql(u8, key, "feature"))
                    self.cfg_env.enabled_features
                else
                    self.cfg_env.enabled_cpu_features;
                for (slice) |entry| {
                    if (std.mem.eql(u8, entry, item_name)) return true;
                }
                return false;
            }
            return false;
        }
        if (std.mem.eql(u8, key, "debug") or std.mem.eql(u8, key, "test") or
            std.mem.eql(u8, key, "test_mode") or std.mem.eql(u8, key, "sim_mode") or
            std.mem.eql(u8, key, "fuzz_mode"))
        {
            const flag_val = if (std.mem.eql(u8, key, "debug"))
                self.cfg_env.is_debug
            else if (std.mem.eql(u8, key, "test") or std.mem.eql(u8, key, "test_mode"))
                self.cfg_env.is_test_mode
            else if (std.mem.eql(u8, key, "sim_mode"))
                self.cfg_env.is_sim_mode
            else
                self.cfg_env.is_fuzz_mode;
            if (pos.* + 1 < cfg_tokens.len) {
                const op_kind = self.tokens.getToken(cfg_tokens[pos.*]).kind;
                const rhs_kind = self.tokens.getToken(cfg_tokens[pos.* + 1]).kind;
                if ((op_kind == .eqeq or op_kind == .bang_eq) and (rhs_kind == .kw_true or rhs_kind == .kw_false)) {
                    pos.* += 2;
                    const rhs_bool = (rhs_kind == .kw_true);
                    return if (op_kind == .eqeq) flag_val == rhs_bool else flag_val != rhs_bool;
                }
            }
            return flag_val;
        }
        if (std.mem.eql(u8, key, "ptr_width") and pos.* + 1 < cfg_tokens.len) {
            const op_kind = self.tokens.getToken(cfg_tokens[pos.*]).kind;
            const val_tok = cfg_tokens[pos.* + 1];
            if ((op_kind == .eqeq or op_kind == .bang_eq) and self.tokens.getToken(val_tok).kind == .int_lit) {
                const lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, val_tok);
                pos.* += 2;
                if (std.fmt.parseInt(u16, lex, 10) catch null) |parsed_w| {
                    return if (op_kind == .eqeq) parsed_w == self.cfg_env.ptr_width else parsed_w != self.cfg_env.ptr_width;
                }
            }
            return true;
        }
        if (pos.* < cfg_tokens.len) {
            const op_kind = self.tokens.getToken(cfg_tokens[pos.*]).kind;
            if (op_kind == .eqeq or op_kind == .bang_eq) {
                pos.* += 1;
                const is_matched = self.isMatchingCfgTargetToken(key, cfg_tokens, pos);
                return if (op_kind == .eqeq) is_matched else !is_matched;
            }
            if (op_kind == .kw_is) {
                pos.* += 1;
                var is_neg = false;
                if (pos.* < cfg_tokens.len and self.tokens.getToken(cfg_tokens[pos.*]).kind == .kw_not) {
                    is_neg = true;
                    pos.* += 1;
                }
                const has_paren = pos.* < cfg_tokens.len and self.tokens.getToken(cfg_tokens[pos.*]).kind == .lparen;
                if (has_paren) pos.* += 1;
                var has_any_matched = false;
                while (pos.* < cfg_tokens.len) {
                    if (self.isMatchingCfgTargetToken(key, cfg_tokens, pos)) has_any_matched = true;
                    if (pos.* < cfg_tokens.len and self.tokens.getToken(cfg_tokens[pos.*]).kind == .pipe) {
                        pos.* += 1;
                    } else {
                        break;
                    }
                }
                if (has_paren and pos.* < cfg_tokens.len and self.tokens.getToken(cfg_tokens[pos.*]).kind == .rparen) {
                    pos.* += 1;
                }
                return if (is_neg) !has_any_matched else has_any_matched;
            }
        }
        return true;
    }

    /// Matches a single `.Variant` or `"string"` value against `key` (`os`, `arch`, `abi`, `endian`) in `self.cfg_env`.
    fn isMatchingCfgTargetToken(self: *const HirLowerer, key: []const u8, cfg_tokens: []const TokenIndex, pos: *usize) bool {
        if (pos.* >= cfg_tokens.len) return false;
        var val_text: []const u8 = "";
        if (self.tokens.getToken(cfg_tokens[pos.*]).kind == .dot and pos.* + 1 < cfg_tokens.len) {
            val_text = symbol_resolver.extractTokenSlice(self.source, self.tokens, cfg_tokens[pos.* + 1]);
            pos.* += 2;
        } else if (self.tokens.getToken(cfg_tokens[pos.*]).kind == .string_lit) {
            const raw = symbol_resolver.extractTokenSlice(self.source, self.tokens, cfg_tokens[pos.*]);
            val_text = if (raw.len >= 2) raw[1 .. raw.len - 1] else "";
            pos.* += 1;
        } else {
            val_text = symbol_resolver.extractTokenSlice(self.source, self.tokens, cfg_tokens[pos.*]);
            pos.* += 1;
        }
        if (std.mem.eql(u8, key, "os")) {
            return switch (self.cfg_env.os) {
                .linux => std.ascii.eqlIgnoreCase(val_text, "linux"),
                .macos => std.ascii.eqlIgnoreCase(val_text, "macos"),
                .windows => std.ascii.eqlIgnoreCase(val_text, "windows"),
                .wasi => std.ascii.eqlIgnoreCase(val_text, "wasi"),
                .freestanding => std.ascii.eqlIgnoreCase(val_text, "freestanding") or std.ascii.eqlIgnoreCase(val_text, "none"),
            };
        }
        if (std.mem.eql(u8, key, "arch")) {
            return switch (self.cfg_env.arch) {
                .x86_64 => std.ascii.eqlIgnoreCase(val_text, "x86_64"),
                .aarch64 => std.ascii.eqlIgnoreCase(val_text, "aarch64"),
                .wasm32 => std.ascii.eqlIgnoreCase(val_text, "wasm32"),
                .riscv64 => std.ascii.eqlIgnoreCase(val_text, "riscv64"),
            };
        }
        if (std.mem.eql(u8, key, "abi")) {
            return switch (self.cfg_env.abi) {
                .gnu => std.ascii.eqlIgnoreCase(val_text, "gnu"),
                .msvc => std.ascii.eqlIgnoreCase(val_text, "msvc"),
                .musl => std.ascii.eqlIgnoreCase(val_text, "musl"),
                .apple => std.ascii.eqlIgnoreCase(val_text, "apple"),
                .wasi => std.ascii.eqlIgnoreCase(val_text, "wasi"),
                .none => std.ascii.eqlIgnoreCase(val_text, "none"),
            };
        }
        if (std.mem.eql(u8, key, "endian")) {
            return switch (self.cfg_env.endian) {
                .little => std.ascii.eqlIgnoreCase(val_text, "little"),
                .big => std.ascii.eqlIgnoreCase(val_text, "big"),
            };
        }
        return false;
    }

    /// Extracts leading `@must_vectorize` and `@vectorize_width(N)` CST attributes on `ast_id` into `store.loop_contracts`.
    fn recordLoopContractFromAst(self: *HirLowerer, ast_id: NodeIndex, loop_id: u32) !void {
        if (ast_id.isNone() or ast_id.asInt() >= self.ast_arena.countNodes()) return;
        const cst_id = self.ast_arena.getCstOrigin(ast_id);
        if (cst_id.isNone() or cst_id.asInt() >= self.cst_arena.countNodes()) return;
        const start_idx: usize = cst_id.asInt();
        const rec = self.cst_arena.getNode(cst_id);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var meta: LoopContractMeta = .{};
        var has_contract = false;
        var cur = start_idx + 1;
        while (cur < end_idx) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.kind == .block or sub.kind == .for_stmt or sub.kind == .while_stmt) break;
            if (sub.kind == .attribute) {
                const attr_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                var attr_name: []const u8 = "";
                var width_val: ?u16 = null;
                var leaf_cur = cur + 1;
                while (leaf_cur < attr_end) : (leaf_cur += 1) {
                    const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(leaf_cur)));
                    if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                        leaf.token.asInt() < self.tokens.countTokens())
                    {
                        const tk = self.tokens.getToken(leaf.token).kind;
                        if (attr_name.len == 0 and symbol_resolver.isIdentifierToken(tk)) {
                            attr_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, leaf.token);
                        } else if (tk == .int_lit and width_val == null) {
                            const num_text = symbol_resolver.extractTokenSlice(self.source, self.tokens, leaf.token);
                            if (std.fmt.parseInt(u32, num_text, 0) catch null) |parsed_width| {
                                if (parsed_width >= 1 and parsed_width <= std.math.maxInt(u16)) {
                                    width_val = @intCast(parsed_width);
                                }
                            }
                        }
                    }
                }
                if (std.mem.eql(u8, attr_name, "must_vectorize")) {
                    meta.contract_flags.is_must_vectorize = true;
                    if (width_val) |lanes| meta.min_lanes = lanes;
                    has_contract = true;
                } else if (std.mem.eql(u8, attr_name, "vectorize_width")) {
                    if (width_val) |lanes| meta.min_lanes = lanes;
                    has_contract = true;
                }
                cur = attr_end;
                continue;
            }
            if (sub.subtree_size > 1) {
                cur += sub.subtree_size;
                continue;
            }
            cur += 1;
        }
        if (has_contract) {
            try self.store.loop_contracts.put(self.allocator, loop_id, meta);
        }
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
                if (mem_sym.kind != .field_sym or !self.isSymbolCfgEnabled(mem_idx)) continue;
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
                if (mem_sym.kind != .enum_variant_sym or !self.isSymbolCfgEnabled(mem_idx)) continue;

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

    /// Computes a `u64` hash contribution for `val_hir` (`val_ty`) in `@derive(Hash)`.
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
                if (mem_sym.kind != .field_sym or !self.isSymbolCfgEnabled(mem_idx)) continue;
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
                if (mem_sym.kind != .enum_variant_sym or !self.isSymbolCfgEnabled(mem_idx)) continue;

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

    /// Clones a single member `place_hir` (`member_ty`) for `@derive(Clone)`.
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
                if (mem_sym.kind != .field_sym or !self.isSymbolCfgEnabled(mem_idx)) continue;
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
                if (mem_sym.kind != .enum_variant_sym or !self.isSymbolCfgEnabled(mem_idx)) continue;

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

    /// Returns `true` if `hir_id` is a side-effect-free place expression (`var_ref`, `field_proj`, or `*deref`).
    fn isPurePlaceHir(self: *const HirLowerer, hir_id: HirIndex) bool {
        var cur_id = hir_id;
        var depth: u32 = 0;
        while (!cur_id.isNone() and cur_id.asInt() < self.store.nodes.len and depth < 32) : (depth += 1) {
            const node = self.store.getNode(cur_id);
            switch (node.tag) {
                .hir_var_ref => return true,
                .hir_field_proj => cur_id = HirIndex.fromInt(node.data.lhs),
                .hir_unary_op => {
                    const uop: HirUnaryOp = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))));
                    if (uop != .deref) return false;
                    cur_id = HirIndex.fromInt(node.data.rhs);
                },
                else => return false,
            }
        }
        return false;
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

    /// Emits a synthetic `hir_call` to `callee_sym_idx`, adjusting and projecting `args` per formal signature.
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

    /// Lowers a lexical `.block` expression, routing `async { … }` blocks to `lowerAsyncBlockExpr`.
    fn lowerBlockExpr(
        self: *HirLowerer,
        block_id: NodeIndex,
        expected_ty: TypeId,
        is_auto_return_fn_body: bool,
    ) anyerror!HirIndex {
        if (block_id.isNone() or block_id.asInt() >= self.ast_arena.countNodes()) {
            return self.emitUnitConst(TokenIndex.fromInt(0), .none);
        }
        if (!is_auto_return_fn_body and
            self.hasKeywordInCst(self.ast_arena.getCstOrigin(block_id), .kw_async))
        {
            return self.lowerAsyncBlockExpr(block_id, expected_ty);
        }
        return self.lowerBlockBodyContents(block_id, expected_ty, is_auto_return_fn_body);
    }

    /// Lowers the statement sequence and optional tail expression of `block_id` into a `hir_block`.
    fn lowerBlockBodyContents(
        self: *HirLowerer,
        block_id: NodeIndex,
        expected_ty: TypeId,
        is_auto_return_fn_body: bool,
    ) anyerror!HirIndex {
        const block_node = self.ast_arena.getNode(block_id);
        if (!try self.enterDepth(block_id)) {
            return self.emitErrorHole(block_node.main_token, block_id, expected_ty);
        }
        defer self.leaveDepth();

        const saved_unsafe = self.is_in_unsafe;
        const was_in_cond_scope = self.is_in_cond_scope;
        self.is_in_cond_scope = false;
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
            self.is_in_cond_scope = was_in_cond_scope;
            self.is_in_unsafe = saved_unsafe;
        }

        var stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer stmts.deinit(self.allocator);

        var has_diverged = false;
        for (self.getAstExtraSlice(block_id, false)) |raw_stmt_id| {
            const stmt_id = NodeIndex.fromInt(raw_stmt_id);
            if (!self.isAstStmtCfgEnabled(stmt_id)) continue;
            try self.lowerStmt(stmt_id, &stmts, &has_diverged);
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

    /// Classifies `val_hir` for `defer` vs. `errdefer` cleanup routing.
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
            .fn_decl => {
                const nested_sym = self.nodeSymbol(stmt_id);
                if (!nested_sym.isNone() and nested_sym.asInt() < self.sym_table.symbols.items.len and
                    self.sym_table.getSymbol(nested_sym).kind == .fn_sym)
                {
                    _ = try self.lowerFnDeclSymbolWithAstOverride(nested_sym, stmt_id);
                }
            },
            .subscript_decl,
            .test_decl,
            .bench_decl,
            .struct_decl,
            .enum_decl,
            .union_decl,
            .type_alias_decl,
            .trait_decl,
            .impl_decl,
            .use_decl,
            .extern_block_decl,
            .extern_static_decl,
            => {},
            .local_var_decl => try self.lowerLocalVarDecl(stmt_id, out_stmts),
            .const_decl => try self.lowerLocalConstDecl(stmt_id, out_stmts),
            .defer_stmt => {
                const def_hir = try self.lowerDeferStmt(stmt_id);
                if (!def_hir.isNone()) try out_stmts.append(self.allocator, def_hir.asInt());
            },
            .return_stmt => {
                const ret_hir = try self.lowerReturnNode(stmt_id);
                if (!ret_hir.isNone()) try out_stmts.append(self.allocator, ret_hir.asInt());
                has_diverged.* = true;
            },
            .yield_stmt => {
                var val_hir = if (stmt_node.lhs.tag == .node)
                    try self.lowerPlaceWithMutCtx(
                        NodeIndex.fromInt(stmt_node.lhs.payload),
                        self.current_fn_ret_ty,
                        self.is_in_subscript_inout_arm,
                    )
                else
                    try self.emitUnitConst(stmt_node.main_token, .none);
                if (!val_hir.isNone()) {
                    const val_node = self.store.getNode(val_hir);
                    if (val_node.tag == .hir_unary_op) {
                        const un_op: HirUnaryOp = @fromBackingInt(@as(u8, @truncate(val_node.data.lhs)));
                        if (un_op == .addr_of or un_op == .addr_of_mut or
                            un_op == .addr_of_raw or un_op == .addr_of_raw_mut)
                        {
                            val_hir = HirIndex.fromInt(val_node.data.rhs);
                        }
                    }
                }
                const yielded_ty = if (!val_hir.isNone())
                    self.store.getNode(val_hir).type_id
                else
                    self.concreteType(self.current_fn_ret_ty);
                const yield_hir = try self.emitNode(.{
                    .tag = .hir_yield,
                    .flags = .{
                        .category = if (self.is_in_subscript_inout_arm) .place_mut else .place_imm,
                        .is_unsafe = self.is_in_unsafe,
                    },
                    .type_id = yielded_ty,
                    .origin_token = stmt_node.main_token,
                    .data = .{
                        .lhs = val_hir.asInt(),
                        .rhs = @intFromBool(self.is_in_subscript_inout_arm),
                    },
                }, stmt_id);
                try out_stmts.append(self.allocator, yield_hir.asInt());
                has_diverged.* = true;
            },
            .break_stmt => {
                const brk_hir = try self.lowerBreakNode(stmt_id, true);
                if (!brk_hir.isNone()) try out_stmts.append(self.allocator, brk_hir.asInt());
                has_diverged.* = true;
            },
            .continue_stmt => {
                const cont_hir = try self.lowerContinueNode(stmt_id, true);
                if (!cont_hir.isNone()) try out_stmts.append(self.allocator, cont_hir.asInt());
                has_diverged.* = true;
            },
            .for_stmt => try self.lowerForStmt(stmt_id, out_stmts, .unit_ty),
            .while_stmt => {
                const while_hir = try self.lowerWhileStmt(stmt_id, .unit_ty);
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
            const is_ref_pat = self.hasKeywordInCst(pat_cst, .amp);
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
        const is_ref_pat = self.hasKeywordInCst(pat_cst, .amp);
        const is_mut = is_decl_mut or
            (!is_ref_pat and (self.hasKeywordInCst(pat_cst, .kw_mut) or self.hasKeywordInCst(pat_cst, .kw_var)));
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

    /// Interns an optional loop label token (`label:` or `:label`), stripping any leading/trailing `:`.
    fn internLabelToken(self: *HirLowerer, label_tok: TokenIndex) !SymbolId {
        if (label_tok.isNone() or label_tok.asInt() >= self.tokens.countTokens()) return .empty;
        var lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, label_tok);
        if (lexeme.len > 0 and lexeme[0] == ':') lexeme = lexeme[1..];
        if (lexeme.len > 0 and lexeme[lexeme.len - 1] == ':') lexeme = lexeme[0 .. lexeme.len - 1];
        if (lexeme.len == 0) return .empty;
        return self.interner.intern(lexeme);
    }

    /// Resolves the innermost matching `ActiveLoopEntry` in the current function/closure for `label_tok`.
    fn findTargetLoop(self: *const HirLowerer, label_tok: TokenIndex) ?ActiveLoopEntry {
        const floor = @min(self.closure_loop_stack_floor, self.loop_stack.items.len);
        const visible = self.loop_stack.items[floor..];
        if (visible.len == 0) return null;
        if (label_tok.isNone() or label_tok.asInt() >= self.tokens.countTokens()) {
            return visible[visible.len - 1];
        }
        var lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, label_tok);
        if (lexeme.len > 0 and lexeme[0] == ':') lexeme = lexeme[1..];
        if (lexeme.len > 0 and lexeme[lexeme.len - 1] == ':') lexeme = lexeme[0 .. lexeme.len - 1];
        const target_id = self.interner.lookup(lexeme) orelse return null;
        var rev_idx = visible.len;
        while (rev_idx > 0) {
            rev_idx -= 1;
            if (visible[rev_idx].label_id == target_id) return visible[rev_idx];
        }
        return null;
    }

    /// Constructs a synthetic `.None` value for `opt_ty` (`Option[T]` or distinct wrapper around `Option[T]`).
    fn emitOptionalNoneConstruct(self: *HirLowerer, opt_ty: TypeId, tok: TokenIndex) !HirIndex {
        const concrete_opt = self.concreteType(opt_ty);
        const unwrapped_opt = self.pool.unwrapUnderlyingType(concrete_opt);
        const extra_idx = try self.store.appendLenPrefixedExtra(&.{});
        var none_hir = try self.emitNode(.{
            .tag = .hir_construct,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = unwrapped_opt,
            .origin_token = tok,
            .data = .{ .lhs = @backingInt(HirConstructKind.optional_none), .rhs = extra_idx },
        }, .none);
        if (unwrapped_opt != concrete_opt) {
            none_hir = try self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = concrete_opt,
                .origin_token = tok,
                .data = .{ .lhs = none_hir.asInt(), .rhs = @backingInt(HirCastKind.distinct_wrap) },
            }, .none);
        }
        return none_hir;
    }

    /// Lowers `return [expr]` (in statement or expression position) into `hir_return` (`never`).
    fn lowerReturnNode(self: *HirLowerer, node_id: NodeIndex) anyerror!HirIndex {
        const stmt_node = self.ast_arena.getNode(node_id);
        const val_hir = if (stmt_node.lhs.tag == .node)
            try self.lowerExpr(NodeIndex.fromInt(stmt_node.lhs.payload), self.current_fn_ret_ty)
        else
            try self.emitUnitConst(stmt_node.main_token, .none);
        const err_kind = self.classifyReturnExpr(val_hir, self.current_fn_ret_ty);
        return self.emitNode(.{
            .tag = .hir_return,
            .flags = .{ .category = .diverging, .is_unsafe = self.is_in_unsafe },
            .type_id = .never_ty,
            .origin_token = stmt_node.main_token,
            .data = .{ .lhs = val_hir.asInt(), .rhs = @backingInt(err_kind) },
        }, node_id);
    }

    /// Lowers `break [:label] [val]` (in statement or expression position) into `hir_break` (wrapping `Some(val)` on `for`/`while`).
    fn lowerBreakNode(self: *HirLowerer, node_id: NodeIndex, is_stmt_pos: bool) anyerror!HirIndex {
        const stmt_node = self.ast_arena.getNode(node_id);
        const tok = stmt_node.main_token;
        const label_tok = if (stmt_node.rhs.tag == .token) TokenIndex.fromInt(stmt_node.rhs.payload) else .none;
        const target_entry = self.findTargetLoop(label_tok);

        const is_ct_target = if (target_entry) |entry| entry.is_comptime_for else self.is_in_comptime_for;
        if (is_ct_target) {
            if (self.comptime_runtime_cond_depth > 0) {
                try self.emitDiagnostic(
                    .e0503_forbidden_comptime_operation,
                    self.astSpan(node_id),
                    "`break` targeting a `comptime for` loop cannot depend on a runtime condition",
                    "use `comptime if` or a runtime `for` loop instead",
                );
            } else {
                self.comptime_loop_state = .broken;
            }
            return if (is_stmt_pos) .none else self.emitErrorHole(tok, node_id, .never_ty);
        }

        const target_loop_id = if (target_entry) |entry| entry.loop_id else (self.current_loop_id orelse 0);
        if (stmt_node.lhs.tag == .node) {
            const val_ast_id = NodeIndex.fromInt(stmt_node.lhs.payload);
            const expected_val_ty = if (target_entry) |entry| entry.payload_ty else .err_ty;
            const val_hir = try self.lowerExpr(val_ast_id, expected_val_ty);
            if (target_entry != null and target_entry.?.result_opt_local != NONE_U32) {
                const opt_ty = self.concreteType(target_entry.?.opt_ty);
                const unwrapped_opt = self.pool.unwrapUnderlyingType(opt_ty);
                const payload_ty = TypeId.fromInt(self.pool.getNode(unwrapped_opt).lhs);
                const coerced_val = try self.applyImplicitCoercionIfNeeded(val_hir, payload_ty, tok);
                const some_extra = try self.store.appendLenPrefixedExtra(&[1]u32{coerced_val.asInt()});
                var some_hir = try self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = unwrapped_opt,
                    .origin_token = tok,
                    .data = .{
                        .lhs = @as(u32, @backingInt(HirConstructKind.optional_some)) | (1 << 8),
                        .rhs = some_extra,
                    },
                }, .none);
                if (unwrapped_opt != opt_ty) {
                    some_hir = try self.emitNode(.{
                        .tag = .hir_cast,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = opt_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = some_hir.asInt(), .rhs = @backingInt(HirCastKind.distinct_wrap) },
                    }, .none);
                }
                const assign_res = try self.emitSyntheticAssign(
                    try self.emitVarRef(target_entry.?.result_opt_local, tok, .none),
                    some_hir,
                    tok,
                );
                const brk_hir = try self.emitNode(.{
                    .tag = .hir_break,
                    .flags = .{ .category = .diverging, .is_unsafe = self.is_in_unsafe },
                    .type_id = .never_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = target_loop_id, .rhs = NONE_U32 },
                }, node_id);
                return self.emitSyntheticBlock(
                    &[2]u32{ assign_res.asInt(), brk_hir.asInt() },
                    .none,
                    .never_ty,
                    tok,
                );
            }
            return self.emitNode(.{
                .tag = .hir_break,
                .flags = .{ .category = .diverging, .is_unsafe = self.is_in_unsafe },
                .type_id = .never_ty,
                .origin_token = tok,
                .data = .{ .lhs = target_loop_id, .rhs = val_hir.asInt() },
            }, node_id);
        }

        return self.emitNode(.{
            .tag = .hir_break,
            .flags = .{ .category = .diverging, .is_unsafe = self.is_in_unsafe },
            .type_id = .never_ty,
            .origin_token = tok,
            .data = .{ .lhs = target_loop_id, .rhs = NONE_U32 },
        }, node_id);
    }

    /// Resolves the innermost matching `ActiveLabeledMatch` (`SE-23`) for `node_id` / `label_tok`.
    fn findTargetLabeledMatch(self: *const HirLowerer, node_id: NodeIndex, label_tok: TokenIndex) ?ActiveLabeledMatch {
        if (self.labeled_match_stack.items.len == 0) return null;
        if (self.side_tables) |tables| {
            if (tables.getLabeledMatchContinueTarget(node_id)) |target_match_ast| {
                var rev_idx = self.labeled_match_stack.items.len;
                while (rev_idx > 0) {
                    rev_idx -= 1;
                    const entry = self.labeled_match_stack.items[rev_idx];
                    if (entry.match_ast == target_match_ast) return entry;
                }
            }
        }
        if (label_tok.isNone() or label_tok.asInt() >= self.tokens.countTokens()) return null;
        var lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, label_tok);
        if (lexeme.len > 0 and lexeme[0] == ':') lexeme = lexeme[1..];
        if (lexeme.len > 0 and lexeme[lexeme.len - 1] == ':') lexeme = lexeme[0 .. lexeme.len - 1];
        const target_id = self.interner.lookup(lexeme) orelse return null;
        var rev_idx = self.labeled_match_stack.items.len;
        while (rev_idx > 0) {
            rev_idx -= 1;
            if (self.labeled_match_stack.items[rev_idx].label_id == target_id) {
                return self.labeled_match_stack.items[rev_idx];
            }
        }
        return null;
    }

    /// Lowers `continue [:label] [next_state]` (`SE-23`) into `hir_continue` (`never`).
    fn lowerContinueNode(self: *HirLowerer, node_id: NodeIndex, is_stmt_pos: bool) anyerror!HirIndex {
        const stmt_node = self.ast_arena.getNode(node_id);
        const tok = stmt_node.main_token;
        const label_tok = if (stmt_node.lhs.tag == .token) TokenIndex.fromInt(stmt_node.lhs.payload) else .none;

        // `SE-23`: `continue :fsm next_state;` targeting a labeled `match` expression:
        if (stmt_node.rhs.tag == .node) {
            const next_val_ast = NodeIndex.fromInt(stmt_node.rhs.payload);
            const match_entry = self.findTargetLabeledMatch(node_id, label_tok);
            const expected_scrut_ty = if (match_entry) |entry| entry.scrutinee_ty else .err_ty;
            const next_val_hir = try self.lowerExpr(next_val_ast, expected_scrut_ty);
            const fsm_target_id = if (match_entry) |entry|
                entry.fsm_id
            else
                (LABELED_MATCH_CONTINUE_FLAG | 0);
            return self.emitNode(.{
                .tag = .hir_continue,
                .flags = .{ .category = .diverging, .is_unsafe = self.is_in_unsafe },
                .type_id = .never_ty,
                .origin_token = tok,
                .data = .{ .lhs = fsm_target_id, .rhs = next_val_hir.asInt() },
            }, node_id);
        }

        const target_entry = self.findTargetLoop(label_tok);

        const is_ct_target = if (target_entry) |entry| entry.is_comptime_for else self.is_in_comptime_for;
        if (is_ct_target) {
            if (self.comptime_runtime_cond_depth > 0) {
                try self.emitDiagnostic(
                    .e0503_forbidden_comptime_operation,
                    self.astSpan(node_id),
                    "`continue` targeting a `comptime for` loop cannot depend on a runtime condition",
                    "use `comptime if` or a runtime `for` loop instead",
                );
            } else {
                self.comptime_loop_state = .continued;
            }
            return if (is_stmt_pos) .none else self.emitErrorHole(tok, node_id, .never_ty);
        }

        const target_loop_id = if (target_entry) |entry| entry.loop_id else (self.current_loop_id orelse 0);
        return self.emitNode(.{
            .tag = .hir_continue,
            .flags = .{ .category = .diverging, .is_unsafe = self.is_in_unsafe },
            .type_id = .never_ty,
            .origin_token = tok,
            .data = .{ .lhs = target_loop_id, .rhs = NONE_U32 },
        }, node_id);
    }

    /// Extracts `(start_id, end_id, is_inclusive)` when `iter_id` is a `.range_expr` or `..`/`..=` `.binary_expr`.
    const RangeAstInfo = struct {
        /// Optional range start expression (`NodeIndex.none` for `..end` / `..=end` / `..`).
        start_id: NodeIndex,
        /// Optional range end expression (`NodeIndex.none` for `start..` / `..`).
        end_id: NodeIndex,
        /// `true` when operator token is `..=`.
        is_inclusive: bool,
    };

    /// Inspects `node_id` and returns `RangeAstInfo` if it represents a range expression.
    fn extractRangeAstInfo(self: *const HirLowerer, node_id: NodeIndex) ?RangeAstInfo {
        if (node_id.isNone() or node_id.asInt() >= self.ast_arena.countNodes()) return null;
        const node = self.ast_arena.getNode(node_id);
        if (node.tag == .range_expr) {
            const is_incl = !node.main_token.isNone() and
                node.main_token.asInt() < self.tokens.countTokens() and
                self.tokens.getToken(node.main_token).kind == .dotdoteq;
            return .{
                .start_id = if (node.lhs.tag == .node) NodeIndex.fromInt(node.lhs.payload) else .none,
                .end_id = if (node.rhs.tag == .node) NodeIndex.fromInt(node.rhs.payload) else .none,
                .is_inclusive = is_incl,
            };
        }
        if (node.tag == .binary_expr and !node.main_token.isNone() and
            node.main_token.asInt() < self.tokens.countTokens())
        {
            const op_kind = self.tokens.getToken(node.main_token).kind;
            if (op_kind == .dotdot or op_kind == .dotdoteq) {
                return .{
                    .start_id = if (node.lhs.tag == .node) NodeIndex.fromInt(node.lhs.payload) else .none,
                    .end_id = if (node.rhs.tag == .node) NodeIndex.fromInt(node.rhs.payload) else .none,
                    .is_inclusive = op_kind == .dotdoteq,
                };
            }
        }
        return null;
    }

    /// Binds the optional `, i` (`usize`) counter token of a `for` loop in the current iteration scope (`SE-05`).
    fn bindForIndexLocal(
        self: *HirLowerer,
        index_tok: TokenIndex,
        idx_val_hir: HirIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
    ) !void {
        if (index_tok.isNone() or index_tok.asInt() >= self.tokens.countTokens()) return;
        const idx_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, index_tok);
        if (idx_lex.len == 0 or std.mem.eql(u8, idx_lex, "_")) return;
        const idx_name_id = try self.interner.intern(idx_lex);
        const idx_slot = try self.store.appendLocal(.{
            .name = idx_name_id,
            .type_id = .usize_ty,
            .decl_span = self.tokens.getTokenSpan(self.store.file_id, index_tok),
            .mode = .let_mode,
            .is_mut = false,
            .is_param = false,
            .is_temp = false,
        });
        try self.pushLexicalLocal(idx_name_id, idx_slot);
        try out_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_slot, idx_val_hir, index_tok)).asInt());
    }

    /// Dispatches `comptime for` unrolling (`MAX_UNROLL = 4096`) vs. runtime `for` canonicalization (`SE-05`/`SE-06`).
    fn lowerForStmt(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
        expected_ty: TypeId,
    ) anyerror!void {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const extra = self.getAstExtraSlice(stmt_id, false);
        const pat_id = if (extra.len >= 1) NodeIndex.fromInt(extra[0]) else .none;
        const iter_id = if (extra.len >= 2) NodeIndex.fromInt(extra[1]) else .none;
        const index_tok = if (extra.len >= 3) TokenIndex.fromInt(extra[2]) else .none;
        const label_tok = if (extra.len >= 4) TokenIndex.fromInt(extra[3]) else .none;
        const ref_mode: u32 = if (extra.len >= 5) extra[4] else 0;
        const body_id = if (stmt_node.rhs.tag == .node) NodeIndex.fromInt(stmt_node.rhs.payload) else .none;

        const is_comptime_for = !stmt_node.main_token.isNone() and
            self.tokens.getToken(stmt_node.main_token).kind == .kw_comptime;
        if (is_comptime_for) {
            try self.lowerComptimeForStmt(stmt_id, pat_id, iter_id, index_tok, label_tok, body_id, out_stmts);
            return;
        }
        const loop_hir = try self.lowerRuntimeForStmt(
            stmt_id,
            pat_id,
            iter_id,
            index_tok,
            label_tok,
            ref_mode,
            body_id,
            expected_ty,
        );
        if (!loop_hir.isNone()) try out_stmts.append(self.allocator, loop_hir.asInt());
    }

    /// Statically unrolls `comptime for pat[, idx] in iter_expr { body }` up to `MAX_UNROLL = 4096` (`E0501`).
    fn lowerComptimeForStmt(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        pat_id: NodeIndex,
        iter_id: NodeIndex,
        index_tok: TokenIndex,
        label_tok: TokenIndex,
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

        const label_id = try self.internLabelToken(label_tok);
        try self.loop_stack.append(self.allocator, .{
            .loop_id = 0,
            .label_id = label_id,
            .is_comptime_for = true,
        });
        defer _ = self.loop_stack.pop();

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
        const idx_name_id: SymbolId = if (!index_tok.isNone() and index_tok.asInt() < self.tokens.countTokens()) blk: {
            const idx_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, index_tok);
            if (idx_lex.len > 0 and !std.mem.eql(u8, idx_lex, "_")) {
                break :blk try self.interner.intern(idx_lex);
            }
            break :blk .empty;
        } else .empty;

        for (elements.items, 0..) |elem_val, iter_i| {
            const ct_checkpoint = self.comptime_shadow_log.items.len;
            defer self.popComptimeBindingsTo(ct_checkpoint);
            try self.pushComptimeBinding(pat_name_id, elem_val);
            if (idx_name_id != .empty) {
                try self.pushComptimeBinding(idx_name_id, .{ .int_val = @intCast(iter_i) });
            }

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

    /// Collects compile-time elements for `comptime for` (`a..b`, `a..=b`, `..b`, `..=b`, array/tuple literals, `.fields`, `.variants`).
    /// Returns `true` if the sequence exceeds `MAX_UNROLL` (`4,096`).
    fn collectComptimeForSequence(
        self: *HirLowerer,
        iter_id: NodeIndex,
        out_elems: *std.ArrayListUnmanaged(ComptimeValue),
    ) !bool {
        if (iter_id.isNone() or iter_id.asInt() >= self.ast_arena.countNodes()) return false;
        const iter_node = self.ast_arena.getNode(iter_id);

        // [1] Compile-time integer range `start..end`, `start..=end`, `..end`, or `..=end`:
        if (self.extractRangeAstInfo(iter_id)) |range_info| {
            if (range_info.end_id.isNone()) return true;
            const start_val: ComptimeValue = if (!range_info.start_id.isNone())
                (try self.tryEvalAstComptime(range_info.start_id, .i64_ty)) orelse return false
            else
                .{ .int_val = 0 };
            const end_val = (try self.tryEvalAstComptime(range_info.end_id, .i64_ty)) orelse return false;
            if (start_val != .int_val or end_val != .int_val) return false;
            const is_inclusive = range_info.is_inclusive;
            const lhs_ty = if (!range_info.start_id.isNone())
                self.pool.unwrapUnderlyingType(self.nodeType(range_info.start_id))
            else
                .usize_ty;
            const rhs_ty = self.pool.unwrapUnderlyingType(self.nodeType(range_info.end_id));
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
                                if (m_sym.kind != .field_sym or !self.isSymbolCfgEnabled(m_idx)) continue;
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
                                if (m_sym.kind != .enum_variant_sym or !self.isSymbolCfgEnabled(m_idx)) continue;
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

    /// Wraps `elem_hir` (`elem_ty`) in `&` / `&mut` when `for ref` / `for ref mut` (`ref_mode != 0`) is active.
    fn wrapForRefModeIfNeeded(
        self: *HirLowerer,
        pat_id: NodeIndex,
        elem_hir: HirIndex,
        elem_ty: TypeId,
        ref_mode: u32,
        tok: TokenIndex,
    ) !struct { val_hir: HirIndex, val_ty: TypeId } {
        const concrete_elem = self.concreteType(elem_ty);
        if (ref_mode == 0) return .{ .val_hir = elem_hir, .val_ty = concrete_elem };
        if (!pat_id.isNone() and pat_id.asInt() < self.ast_arena.countNodes() and
            self.ast_arena.getNode(pat_id).tag == .bind_pat)
        {
            const pat_cst = self.ast_arena.getCstOrigin(pat_id);
            if (self.hasKeywordInCst(pat_cst, .amp)) {
                return .{ .val_hir = elem_hir, .val_ty = concrete_elem };
            }
        }
        const is_mut_ref = ref_mode == 2;
        const ref_ty = try self.pool.internRef(concrete_elem, is_mut_ref);
        const addr_hir = try self.emitSyntheticAddrOf(elem_hir, ref_ty, is_mut_ref, tok);
        return .{ .val_hir = addr_hir, .val_ty = ref_ty };
    }

    /// Lowers runtime `for [ref [mut]] pat[, idx] in iter_expr { body }` into canonical `hir_loop` (`SE-05`/`SE-06`).
    fn lowerRuntimeForStmt(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        pat_id: NodeIndex,
        iter_id: NodeIndex,
        index_tok: TokenIndex,
        label_tok: TokenIndex,
        ref_mode: u32,
        body_id: NodeIndex,
        expected_ty: TypeId,
    ) anyerror!HirIndex {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const tok = stmt_node.main_token;
        if (iter_id.isNone() or iter_id.asInt() >= self.ast_arena.countNodes()) {
            return self.emitUnitConst(tok, stmt_id);
        }
        const iter_node = self.ast_arena.getNode(iter_id);

        const recorded_loop_ty = self.nodeType(stmt_id);
        const loop_ty = self.concreteType(if (!recorded_loop_ty.isError()) recorded_loop_ty else expected_ty);
        const unwrapped_loop_ty = self.pool.unwrapUnderlyingType(loop_ty);
        const is_opt_result = loop_ty != .unit_ty and self.pool.getTag(unwrapped_loop_ty) == .optional_ty;
        const opt_payload_ty: TypeId = if (is_opt_result)
            self.concreteType(TypeId.fromInt(self.pool.getNode(unwrapped_loop_ty).lhs))
        else
            .unit_ty;

        var outer_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer outer_stmts.deinit(self.allocator);

        var res_opt_local: u32 = NONE_U32;
        if (is_opt_result) {
            res_opt_local = try self.allocTempLocal(loop_ty, tok, true);
            const init_none = try self.emitOptionalNoneConstruct(loop_ty, tok);
            try outer_stmts.append(
                self.allocator,
                (try self.emitLocalDeclNode(res_opt_local, init_none, tok)).asInt(),
            );
        }

        const loop_id = self.next_loop_id;
        self.next_loop_id += 1;
        try self.recordLoopContractFromAst(stmt_id, loop_id);
        const label_id = try self.internLabelToken(label_tok);
        try self.loop_stack.append(self.allocator, .{
            .loop_id = loop_id,
            .label_id = label_id,
            .is_comptime_for = false,
            .result_opt_local = res_opt_local,
            .payload_ty = opt_payload_ty,
            .opt_ty = if (is_opt_result) loop_ty else .unit_ty,
        });
        defer _ = self.loop_stack.pop();

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

        // [1] Integer ranges `start..end`, `start..=end`, `..end`, `..=end`, and unbounded `start..`:
        if (self.extractRangeAstInfo(iter_id)) |range_info| {
            const elem_ty = self.concreteType(blk: {
                const p_ty = self.unwrapRefType(self.nodeType(pat_id));
                if (!p_ty.isError() and p_ty != .unit_ty) break :blk p_ty;
                if (!range_info.start_id.isNone()) {
                    const s_ty = self.nodeType(range_info.start_id);
                    if (!s_ty.isError()) break :blk s_ty;
                }
                if (!range_info.end_id.isNone()) {
                    const e_ty = self.nodeType(range_info.end_id);
                    if (!e_ty.isError()) break :blk e_ty;
                }
                break :blk .usize_ty;
            });
            const start_hir = if (!range_info.start_id.isNone())
                try self.lowerExpr(range_info.start_id, elem_ty)
            else
                try self.emitConstVal(.{ .int_val = 0 }, elem_ty, tok, .none, true);

            const cur_local = try self.allocTempLocal(elem_ty, tok, true);
            try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(cur_local, start_hir, tok)).asInt());

            var range_ord_local: u32 = NONE_U32;
            if (!index_tok.isNone()) {
                range_ord_local = try self.allocTempLocal(.usize_ty, tok, true);
                const zero_ord = try self.emitConstVal(.{ .int_val = 0 }, .usize_ty, tok, .none, true);
                try outer_stmts.append(
                    self.allocator,
                    (try self.emitLocalDeclNode(range_ord_local, zero_ord, tok)).asInt(),
                );
            }

            var loop_stmts: std.ArrayListUnmanaged(u32) = .empty;
            defer loop_stmts.deinit(self.allocator);

            if (range_info.end_id.isNone()) {
                // Unbounded range `start..` or `..`:
                const iter_elem_local = try self.allocTempLocal(elem_ty, tok, ref_mode == 2);
                try loop_stmts.append(
                    self.allocator,
                    (try self.emitLocalDeclNode(iter_elem_local, try self.emitVarRef(cur_local, tok, .none), tok)).asInt(),
                );
                const elem_val = try self.emitVarRef(iter_elem_local, tok, .none);
                const wrapped_elem = try self.wrapForRefModeIfNeeded(pat_id, elem_val, elem_ty, ref_mode, tok);
                try self.emitPatternBindStmts(pat_id, wrapped_elem.val_hir, wrapped_elem.val_ty, tok, &loop_stmts);

                const one_const = try self.emitConstVal(.{ .int_val = 1 }, elem_ty, tok, .none, true);
                const next_val = try self.emitSyntheticBinOp(
                    .add,
                    try self.emitVarRef(cur_local, tok, .none),
                    one_const,
                    elem_ty,
                    tok,
                );
                try loop_stmts.append(
                    self.allocator,
                    (try self.emitSyntheticAssign(try self.emitVarRef(cur_local, tok, .none), next_val, tok)).asInt(),
                );
            } else if (!range_info.is_inclusive) {
                const end_hir = try self.lowerExpr(range_info.end_id, elem_ty);
                const end_local = try self.allocTempLocal(elem_ty, tok, false);
                try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(end_local, end_hir, tok)).asInt());

                const lt_cond = try self.emitSyntheticBinOp(
                    .lt,
                    try self.emitVarRef(cur_local, tok, .none),
                    try self.emitVarRef(end_local, tok, .none),
                    .bool_ty,
                    tok,
                );
                try loop_stmts.append(self.allocator, (try self.emitLoopBreakIfFalse(lt_cond, loop_id, tok)).asInt());

                const iter_elem_local = try self.allocTempLocal(elem_ty, tok, ref_mode == 2);
                try loop_stmts.append(
                    self.allocator,
                    (try self.emitLocalDeclNode(iter_elem_local, try self.emitVarRef(cur_local, tok, .none), tok)).asInt(),
                );
                const elem_val = try self.emitVarRef(iter_elem_local, tok, .none);
                const wrapped_elem = try self.wrapForRefModeIfNeeded(pat_id, elem_val, elem_ty, ref_mode, tok);
                try self.emitPatternBindStmts(pat_id, wrapped_elem.val_hir, wrapped_elem.val_ty, tok, &loop_stmts);

                const one_const = try self.emitConstVal(.{ .int_val = 1 }, elem_ty, tok, .none, true);
                const next_val = try self.emitSyntheticBinOp(
                    .wrap_add,
                    try self.emitVarRef(cur_local, tok, .none),
                    one_const,
                    elem_ty,
                    tok,
                );
                try loop_stmts.append(
                    self.allocator,
                    (try self.emitSyntheticAssign(try self.emitVarRef(cur_local, tok, .none), next_val, tok)).asInt(),
                );
            } else {
                const end_hir = try self.lowerExpr(range_info.end_id, elem_ty);
                const end_local = try self.allocTempLocal(elem_ty, tok, false);
                try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(end_local, end_hir, tok)).asInt());

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

                const done_break = try self.emitLoopBreakIfTrue(
                    try self.emitVarRef(done_local, tok, .none),
                    loop_id,
                    tok,
                );
                try loop_stmts.append(self.allocator, done_break.asInt());

                const iter_elem_local = try self.allocTempLocal(elem_ty, tok, ref_mode == 2);
                try loop_stmts.append(
                    self.allocator,
                    (try self.emitLocalDeclNode(iter_elem_local, try self.emitVarRef(cur_local, tok, .none), tok)).asInt(),
                );
                const elem_val = try self.emitVarRef(iter_elem_local, tok, .none);
                const wrapped_elem = try self.wrapForRefModeIfNeeded(pat_id, elem_val, elem_ty, ref_mode, tok);
                try self.emitPatternBindStmts(pat_id, wrapped_elem.val_hir, wrapped_elem.val_ty, tok, &loop_stmts);

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

            if (range_ord_local != NONE_U32) {
                const cur_ord_local = try self.allocTempLocal(.usize_ty, tok, false);
                try loop_stmts.append(
                    self.allocator,
                    (try self.emitLocalDeclNode(
                        cur_ord_local,
                        try self.emitVarRef(range_ord_local, tok, .none),
                        tok,
                    )).asInt(),
                );
                const one_ord = try self.emitConstVal(.{ .int_val = 1 }, .usize_ty, tok, .none, true);
                const next_ord = try self.emitSyntheticBinOp(
                    .add,
                    try self.emitVarRef(range_ord_local, tok, .none),
                    one_ord,
                    .usize_ty,
                    tok,
                );
                try loop_stmts.append(
                    self.allocator,
                    (try self.emitSyntheticAssign(
                        try self.emitVarRef(range_ord_local, tok, .none),
                        next_ord,
                        tok,
                    )).asInt(),
                );
                try self.bindForIndexLocal(index_tok, try self.emitVarRef(cur_ord_local, tok, .none), &loop_stmts);
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
            const tail_res = if (is_opt_result) try self.emitVarRef(res_opt_local, tok, .none) else .none;
            return self.emitSyntheticBlock(
                outer_stmts.items,
                tail_res,
                if (is_opt_result) loop_ty else .unit_ty,
                tok,
            );
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
                    return self.lowerSoaZipLoop(
                        stmt_id,
                        pat_id,
                        iter_id,
                        index_tok,
                        ref_mode,
                        body_id,
                        loop_id,
                        res_opt_local,
                        if (is_opt_result) loop_ty else .unit_ty,
                        &outer_stmts,
                    );
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

        const seq_local = try self.allocTempLocal(seq_ty, tok, ref_mode == 2);
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
        const wrapped_elem = try self.wrapForRefModeIfNeeded(pat_id, elem_proj, elem_ty, ref_mode, tok);
        try self.emitPatternBindStmts(pat_id, wrapped_elem.val_hir, wrapped_elem.val_ty, tok, &loop_stmts);
        try self.bindForIndexLocal(index_tok, try self.emitVarRef(cur_idx_local, tok, .none), &loop_stmts);

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
        const tail_res = if (is_opt_result) try self.emitVarRef(res_opt_local, tok, .none) else .none;
        return self.emitSyntheticBlock(
            outer_stmts.items,
            tail_res,
            if (is_opt_result) loop_ty else .unit_ty,
            tok,
        );
    }

    /// Lowers `for pat[, idx] in soa_zip(s0, s1, …) { body }` without allocating an intermediate AoS tuple on stack.
    fn lowerSoaZipLoop(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        pat_id: NodeIndex,
        iter_id: NodeIndex,
        index_tok: TokenIndex,
        ref_mode: u32,
        body_id: NodeIndex,
        loop_id: u32,
        res_opt_local: u32,
        res_ty: TypeId,
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
            if (arg_ast.tag == .named_arg) {
                if (!arg_ast.main_token.isNone() and arg_ast.main_token.asInt() < self.tokens.countTokens()) {
                    const lbl_text = symbol_resolver.extractTokenSlice(self.source, self.tokens, arg_ast.main_token);
                    if (lbl_text.len > 0) item_label = try self.interner.intern(lbl_text);
                }
                if (arg_ast.lhs.tag == .node) arg_id = NodeIndex.fromInt(arg_ast.lhs.payload);
            }

            const seq_hir = try self.lowerExpr(arg_id, .err_ty);
            const seq_ty = self.store.getNode(seq_hir).type_id;
            const is_seq_mut = self.store.getNode(seq_hir).flags.category == .place_mut or ref_mode == 2;
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
                    const sub_pat_id = NodeIndex.fromInt(raw_sub);
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
                    const wrapped_sub = try self.wrapForRefModeIfNeeded(
                        sub_pat_id,
                        elem_proj,
                        elem_ty,
                        ref_mode,
                        tok,
                    );
                    try self.emitPatternBindStmts(
                        sub_pat_id,
                        wrapped_sub.val_hir,
                        wrapped_sub.val_ty,
                        tok,
                        &loop_stmts,
                    );
                }
            }
        }
        try self.bindForIndexLocal(index_tok, try self.emitVarRef(cur_idx_local, tok, .none), &loop_stmts);

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
        const tail_res = if (res_opt_local != NONE_U32) try self.emitVarRef(res_opt_local, tok, .none) else .none;
        return self.emitSyntheticBlock(outer_stmts.items, tail_res, res_ty, tok);
    }

    /// Lowers `while cond { body }` into `hir_cond_while` (when `is` / `:=` is present) or canonical `hir_loop` (`SE-01`/`SE-02`/`SE-06`).
    fn lowerWhileStmt(self: *HirLowerer, stmt_id: NodeIndex, expected_ty: TypeId) anyerror!HirIndex {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const tok = stmt_node.main_token;
        var cond_id: NodeIndex = .none;
        var label_tok: TokenIndex = .none;
        if (stmt_node.lhs.tag == .extra) {
            const pair = self.getAstExtraSlice(stmt_id, false);
            if (pair.len >= 1) cond_id = NodeIndex.fromInt(pair[0]);
            if (pair.len >= 2) label_tok = TokenIndex.fromInt(pair[1]);
        } else if (stmt_node.lhs.tag == .node) {
            cond_id = NodeIndex.fromInt(stmt_node.lhs.payload);
        }
        const body_id = if (stmt_node.rhs.tag == .node) NodeIndex.fromInt(stmt_node.rhs.payload) else .none;

        const recorded_loop_ty = self.nodeType(stmt_id);
        const loop_ty = self.concreteType(if (!recorded_loop_ty.isError()) recorded_loop_ty else expected_ty);
        const unwrapped_loop_ty = self.pool.unwrapUnderlyingType(loop_ty);
        const is_opt_result = loop_ty != .unit_ty and self.pool.getTag(unwrapped_loop_ty) == .optional_ty;
        const opt_payload_ty: TypeId = if (is_opt_result)
            self.concreteType(TypeId.fromInt(self.pool.getNode(unwrapped_loop_ty).lhs))
        else
            .unit_ty;

        var outer_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer outer_stmts.deinit(self.allocator);

        var res_opt_local: u32 = NONE_U32;
        if (is_opt_result) {
            res_opt_local = try self.allocTempLocal(loop_ty, tok, true);
            const init_none = try self.emitOptionalNoneConstruct(loop_ty, tok);
            try outer_stmts.append(
                self.allocator,
                (try self.emitLocalDeclNode(res_opt_local, init_none, tok)).asInt(),
            );
        }

        const loop_id = self.next_loop_id;
        self.next_loop_id += 1;
        try self.recordLoopContractFromAst(stmt_id, loop_id);
        const label_id = try self.internLabelToken(label_tok);
        try self.loop_stack.append(self.allocator, .{
            .loop_id = loop_id,
            .label_id = label_id,
            .is_comptime_for = false,
            .result_opt_local = res_opt_local,
            .payload_ty = opt_payload_ty,
            .opt_ty = if (is_opt_result) loop_ty else .unit_ty,
        });
        defer _ = self.loop_stack.pop();

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

        if (self.hasConditionScope(cond_id)) {
            var clauses: std.ArrayListUnmanaged(NodeIndex) = .empty;
            defer clauses.deinit(self.allocator);
            var has_unused_is = false;
            try self.collectConjunctiveClauses(cond_id, &clauses, &has_unused_is);

            var extra_words: std.ArrayListUnmanaged(u32) = .empty;
            defer extra_words.deinit(self.allocator);
            try extra_words.append(self.allocator, @intCast(clauses.items.len));

            const was_in_cond = self.is_in_cond_scope;
            self.is_in_cond_scope = true;
            {
                errdefer self.is_in_cond_scope = was_in_cond;
                try self.lowerCondClauseList(clauses.items, &extra_words);
            }
            self.is_in_cond_scope = was_in_cond;

            const body_hir = try self.lowerBlockExpr(body_id, .unit_ty, false);
            try extra_words.append(self.allocator, body_hir.asInt());
            try extra_words.append(self.allocator, res_opt_local);

            const extra_idx = try self.store.appendExtraSlice(extra_words.items);
            const cond_while_ty = if (is_opt_result) loop_ty else .unit_ty;
            const cond_while_hir = try self.emitNode(.{
                .tag = .hir_cond_while,
                .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
                .type_id = cond_while_ty,
                .origin_token = tok,
                .data = .{ .lhs = extra_idx, .rhs = loop_id },
            }, stmt_id);
            if (is_opt_result) {
                return self.emitSyntheticBlock(outer_stmts.items, cond_while_hir, loop_ty, tok);
            }
            return cond_while_hir;
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
            body_id,
            .none,
            brk_blk,
            .unit_ty,
            tok,
            stmt_id,
        );
        const loop_blk = try self.wrapSingleStmtBlock(step_hir, tok);
        const loop_node = try self.emitNode(.{
            .tag = .hir_loop,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = loop_blk.asInt(), .rhs = loop_id },
        }, stmt_id);
        if (is_opt_result) {
            try outer_stmts.append(self.allocator, loop_node.asInt());
            return self.emitSyntheticBlock(
                outer_stmts.items,
                try self.emitVarRef(res_opt_local, tok, .none),
                loop_ty,
                tok,
            );
        }
        return loop_node;
    }

    /// Lowers `place_ast_id` with `is_mut_lvalue_ctx = is_mut_needed` so `$` receivers acquire `&mut` only when mutated.
    fn lowerPlaceWithMutCtx(
        self: *HirLowerer,
        place_ast_id: NodeIndex,
        target_ty: TypeId,
        is_mut_needed: bool,
    ) anyerror!HirIndex {
        const saved_mut_ctx = self.is_mut_lvalue_ctx;
        self.is_mut_lvalue_ctx = is_mut_needed;
        defer self.is_mut_lvalue_ctx = saved_mut_ctx;
        return self.lowerExpr(place_ast_id, target_ty);
    }

    /// Lowers `lhs = rhs;`, `_ = rhs;`, `SE-15` parallel destructuring `(a, b) = (b, a);`, and compound assignments (`+=`, `-=`, etc.).
    fn lowerAssignStmt(self: *HirLowerer, stmt_id: NodeIndex) anyerror!HirIndex {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const tok = stmt_node.main_token;
        const lhs_id = if (stmt_node.lhs.tag == .node) NodeIndex.fromInt(stmt_node.lhs.payload) else .none;
        const rhs_id = if (stmt_node.rhs.tag == .node) NodeIndex.fromInt(stmt_node.rhs.payload) else .none;

        const op_kind = if (!tok.isNone() and tok.asInt() < self.tokens.countTokens())
            self.tokens.getToken(tok).kind
        else
            TokenKind.eq;

        // [0] Wildcard discard `_ = rhs;` and `SE-15` 3-phase parallel destructuring assignment:
        if (op_kind == .eq and !lhs_id.isNone() and lhs_id.asInt() < self.ast_arena.countNodes()) {
            const lhs_ast = self.ast_arena.getNode(lhs_id);
            if (lhs_ast.tag == .wildcard_pat) {
                if (rhs_id.isNone()) return self.emitUnitConst(tok, stmt_id);
                const discarded_hir = try self.lowerExpr(rhs_id, self.nodeType(lhs_id));
                const tmp_slot = try self.allocTempLocal(self.store.getNode(discarded_hir).type_id, tok, false);
                return self.emitNode(.{
                    .tag = .hir_local_decl,
                    .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                    .type_id = .unit_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = tmp_slot, .rhs = discarded_hir.asInt() },
                }, stmt_id);
            }
            const is_parallel = switch (lhs_ast.tag) {
                .tuple_lit => blk: {
                    const elems = self.getAstExtraSlice(lhs_id, false);
                    break :blk elems.len != 1 or type_system.hasShallowCommaInTupleCst(
                        self.cst_arena,
                        self.tokens,
                        self.ast_arena.getCstOrigin(lhs_id),
                    );
                },
                .array_lit, .struct_lit => true,
                else => false,
            };
            if (is_parallel) {
                return self.lowerParallelAssignStmt(stmt_id, lhs_id, rhs_id, tok);
            }
        }

        // [1] Direct `=` assignment:
        if (op_kind == .eq) {
            const lhs_hir = try self.lowerPlaceWithMutCtx(lhs_id, .err_ty, true);
            const lhs_node = self.store.getNode(lhs_hir);
            const rhs_hir = try self.lowerPlaceWithMutCtx(rhs_id, lhs_node.type_id, false);
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

        // [2] Compound assignment (`+=`, `-=`, etc.): evaluate `rhs` BEFORE `&mut lhs` (`DR-02` §2.2):
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
        const raw_rhs_hir = try self.lowerPlaceWithMutCtx(rhs_id, expected_rhs_ty, false);
        const rhs_local = try self.allocTempLocal(self.store.getNode(raw_rhs_hir).type_id, tok, false);
        const decl_rhs = try self.emitLocalDeclNode(rhs_local, raw_rhs_hir, tok);

        const lhs_hir = try self.lowerPlaceWithMutCtx(lhs_id, .err_ty, true);
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

    /// Lowers a 3-phase parallel place destructuring assignment (`(a.*, b.*) = (b.*, a.*);`, `SE-15`).
    fn lowerParallelAssignStmt(
        self: *HirLowerer,
        stmt_id: NodeIndex,
        lhs_id: NodeIndex,
        rhs_id: NodeIndex,
        tok: TokenIndex,
    ) anyerror!HirIndex {
        var stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer stmts.deinit(self.allocator);

        // Phase 0: Pre-evaluate dynamic LHS index/pointer sub-expressions L-to-R into immutable SSA temps
        // without opening `.ghost_access_inout` loans yet (`SE-15`).
        try self.preEvalParallelPlaceSubexprs(lhs_id, lhs_id, tok, &stmts);

        // Phase 1: Evaluate RHS into an immutable temporary (`ghost_storage_move` + `place_load` on `~Copy` places).
        const rhs_expected = self.nodeType(lhs_id);
        const rhs_hir = try self.lowerExpr(rhs_id, rhs_expected);
        const rhs_ty = self.store.getNode(rhs_hir).type_id;
        const rhs_root_slot = try self.allocTempLocal(rhs_ty, tok, false);
        try stmts.append(self.allocator, (try self.emitLocalDeclNode(rhs_root_slot, rhs_hir, tok)).asInt());

        // Phase 2 & 3: Project each RHS leaf into its own temp, then commit LHS stores L-to-R and record
        // the contiguous store slice in `store.parallel_assign_blocks` for `mir_sast.zig` `E0305` verification.
        var leaf_stores: std.ArrayListUnmanaged(u32) = .empty;
        defer leaf_stores.deinit(self.allocator);
        const rhs_root_ref = try self.emitVarRef(rhs_root_slot, tok, .none);
        try self.lowerParallelDestructureTargets(lhs_id, rhs_root_ref, rhs_ty, tok, &stmts, &leaf_stores);

        const first_assign_idx: u32 = @intCast(stmts.items.len);
        const assign_count: u32 = @intCast(leaf_stores.items.len);
        try stmts.appendSlice(self.allocator, leaf_stores.items);

        const blk_hir = try self.emitSyntheticBlock(stmts.items, .none, .unit_ty, tok);
        self.store.origin_ast.items[blk_hir.asInt()] = stmt_id;
        if (assign_count >= 2) {
            try self.store.parallel_assign_blocks.put(self.allocator, blk_hir.asInt(), .{
                .first_assign_idx = first_assign_idx,
                .assign_count = assign_count,
            });
        }
        return blk_hir;
    }

    /// Returns `true` if `sub_id` is a bare `.ident_expr` / `.self_val` directly overwritten as a leaf in `root_lhs_id`.
    fn hasDirectIdentTargetInParallelLhs(
        self: *const HirLowerer,
        cur_lhs_id: NodeIndex,
        target_ident_ast: NodeIndex,
    ) bool {
        if (cur_lhs_id.isNone() or cur_lhs_id.asInt() >= self.ast_arena.countNodes()) return false;
        if (cur_lhs_id == target_ident_ast) return false;
        const target_node = self.ast_arena.getNode(target_ident_ast);
        const target_lex = if (target_node.tag == .self_val)
            "self"
        else if (target_node.tag == .ident_expr)
            symbol_resolver.extractTokenSlice(self.source, self.tokens, target_node.main_token)
        else
            return false;

        const cur_node = self.ast_arena.getNode(cur_lhs_id);
        switch (cur_node.tag) {
            .ident_expr => return std.mem.eql(
                u8,
                symbol_resolver.extractTokenSlice(self.source, self.tokens, cur_node.main_token),
                target_lex,
            ),
            .self_val => return std.mem.eql(u8, "self", target_lex),
            .tuple_lit, .array_lit => {
                for (self.getAstExtraSlice(cur_lhs_id, false)) |raw_elem| {
                    if (self.hasDirectIdentTargetInParallelLhs(NodeIndex.fromInt(raw_elem), target_ident_ast)) {
                        return true;
                    }
                }
                return false;
            },
            .struct_lit => {
                for (self.getAstExtraSlice(cur_lhs_id, true)) |raw_field| {
                    if (self.hasDirectIdentTargetInParallelLhs(NodeIndex.fromInt(raw_field), target_ident_ast)) {
                        return true;
                    }
                }
                return false;
            },
            else => return false,
        }
    }

    /// Recursively pre-evaluates dynamic index and pointer rvalues inside `lhs_id` during Phase 0 (`SE-15`).
    fn preEvalParallelPlaceSubexprs(
        self: *HirLowerer,
        root_lhs_id: NodeIndex,
        lhs_id: NodeIndex,
        tok: TokenIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
    ) anyerror!void {
        if (lhs_id.isNone() or lhs_id.asInt() >= self.ast_arena.countNodes()) return;
        const node = self.ast_arena.getNode(lhs_id);
        switch (node.tag) {
            .wildcard_pat => {},
            .tuple_lit, .array_lit => {
                for (self.getAstExtraSlice(lhs_id, false)) |raw_elem| {
                    try self.preEvalParallelPlaceSubexprs(root_lhs_id, NodeIndex.fromInt(raw_elem), tok, out_stmts);
                }
            },
            .struct_lit => {
                for (self.getAstExtraSlice(lhs_id, true)) |raw_field| {
                    try self.preEvalParallelPlaceSubexprs(root_lhs_id, NodeIndex.fromInt(raw_field), tok, out_stmts);
                }
            },
            .field_access => {
                if (node.lhs.tag == .node) {
                    try self.preEvalParallelPlaceSubexprs(
                        root_lhs_id,
                        NodeIndex.fromInt(node.lhs.payload),
                        tok,
                        out_stmts,
                    );
                }
            },
            .deref_expr => {
                if (node.lhs.tag == .node) {
                    const ptr_ast = NodeIndex.fromInt(node.lhs.payload);
                    const ptr_tag = self.ast_arena.getNode(ptr_ast).tag;
                    const ptr_ty = self.pool.unwrapUnderlyingType(self.nodeType(ptr_ast));
                    const is_mut_ref = !ptr_ty.isError() and self.pool.getNode(ptr_ty).tag == .mut_ref_ty;
                    if (!is_mut_ref or
                        (ptr_tag != .ident_expr and ptr_tag != .self_val) or
                        self.hasDirectIdentTargetInParallelLhs(root_lhs_id, ptr_ast))
                    {
                        const ptr_hir = try self.lowerExpr(ptr_ast, .err_ty);
                        const ptr_slot = try self.allocTempLocal(self.store.getNode(ptr_hir).type_id, tok, false);
                        try out_stmts.append(
                            self.allocator,
                            (try self.emitLocalDeclNode(ptr_slot, ptr_hir, tok)).asInt(),
                        );
                        try self.parallel_pre_eval.put(
                            self.allocator,
                            ptr_ast.asInt(),
                            try self.emitVarRef(ptr_slot, tok, .none),
                        );
                    }
                }
            },
            .unary_expr => {
                if (!node.main_token.isNone() and self.tokens.getToken(node.main_token).kind == .star and
                    node.lhs.tag == .node)
                {
                    const ptr_ast = NodeIndex.fromInt(node.lhs.payload);
                    const ptr_tag = self.ast_arena.getNode(ptr_ast).tag;
                    const ptr_ty = self.pool.unwrapUnderlyingType(self.nodeType(ptr_ast));
                    const is_mut_ref = !ptr_ty.isError() and self.pool.getNode(ptr_ty).tag == .mut_ref_ty;
                    if (!is_mut_ref or
                        (ptr_tag != .ident_expr and ptr_tag != .self_val) or
                        self.hasDirectIdentTargetInParallelLhs(root_lhs_id, ptr_ast))
                    {
                        const ptr_hir = try self.lowerExpr(ptr_ast, .err_ty);
                        const ptr_slot = try self.allocTempLocal(self.store.getNode(ptr_hir).type_id, tok, false);
                        try out_stmts.append(
                            self.allocator,
                            (try self.emitLocalDeclNode(ptr_slot, ptr_hir, tok)).asInt(),
                        );
                        try self.parallel_pre_eval.put(
                            self.allocator,
                            ptr_ast.asInt(),
                            try self.emitVarRef(ptr_slot, tok, .none),
                        );
                    }
                }
            },
            .index_expr => {
                if (node.lhs.tag == .node) {
                    try self.preEvalParallelPlaceSubexprs(
                        root_lhs_id,
                        NodeIndex.fromInt(node.lhs.payload),
                        tok,
                        out_stmts,
                    );
                }
                if (node.rhs.tag == .node) {
                    const idx_ast = NodeIndex.fromInt(node.rhs.payload);
                    if (self.extractRangeAstInfo(idx_ast) == null and !self.hasDollarAst(idx_ast)) {
                        const idx_hir = try self.lowerExpr(idx_ast, .usize_ty);
                        const idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
                        try out_stmts.append(
                            self.allocator,
                            (try self.emitLocalDeclNode(idx_slot, idx_hir, tok)).asInt(),
                        );
                        try self.parallel_pre_eval.put(
                            self.allocator,
                            idx_ast.asInt(),
                            try self.emitVarRef(idx_slot, tok, .none),
                        );
                    }
                } else if (node.rhs.tag == .extra) {
                    for (self.getAstExtraSlice(lhs_id, true)) |raw_idx| {
                        const idx_ast = NodeIndex.fromInt(raw_idx);
                        if (!self.hasDollarAst(idx_ast)) {
                            const idx_hir = try self.lowerExpr(idx_ast, .usize_ty);
                            const idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
                            try out_stmts.append(
                                self.allocator,
                                (try self.emitLocalDeclNode(idx_slot, idx_hir, tok)).asInt(),
                            );
                            try self.parallel_pre_eval.put(
                                self.allocator,
                                idx_ast.asInt(),
                                try self.emitVarRef(idx_slot, tok, .none),
                            );
                        }
                    }
                }
            },
            .call_expr, .method_call => {
                const call_hir = try self.lowerExpr(lhs_id, .err_ty);
                const call_slot = try self.allocTempLocal(self.store.getNode(call_hir).type_id, tok, false);
                try out_stmts.append(
                    self.allocator,
                    (try self.emitLocalDeclNode(call_slot, call_hir, tok)).asInt(),
                );
                try self.parallel_pre_eval.put(
                    self.allocator,
                    lhs_id.asInt(),
                    try self.emitVarRef(call_slot, tok, .none),
                );
            },
            else => {},
        }
    }

    /// Recursively decomposes `lhs_id` against `rhs_val_hir` (`rhs_ty`), emitting temp projections into `out_stmts`
    /// and leaf `hir_assign` / `hir_bitfield_rmw` nodes into `out_stores` (`SE-15`).
    fn lowerParallelDestructureTargets(
        self: *HirLowerer,
        lhs_id: NodeIndex,
        rhs_val_hir: HirIndex,
        rhs_ty: TypeId,
        tok: TokenIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
        out_stores: *std.ArrayListUnmanaged(u32),
    ) anyerror!void {
        if (lhs_id.isNone() or lhs_id.asInt() >= self.ast_arena.countNodes()) return;
        const lhs_node = self.ast_arena.getNode(lhs_id);
        const unwrapped_rhs = self.pool.unwrapUnderlyingType(rhs_ty);
        switch (lhs_node.tag) {
            .wildcard_pat => return,
            .tuple_lit => {
                const elems = self.getAstExtraSlice(lhs_id, false);
                if (elems.len == 1 and !type_system.hasShallowCommaInTupleCst(
                    self.cst_arena,
                    self.tokens,
                    self.ast_arena.getCstOrigin(lhs_id),
                )) {
                    return self.lowerParallelDestructureTargets(
                        NodeIndex.fromInt(elems[0]),
                        rhs_val_hir,
                        rhs_ty,
                        tok,
                        out_stmts,
                        out_stores,
                    );
                }
                const tup_elems = self.pool.getTupleElements(unwrapped_rhs);
                for (elems, 0..) |raw_sub, i| {
                    const sub_id = NodeIndex.fromInt(raw_sub);
                    if (sub_id.isNone() or self.ast_arena.getNode(sub_id).tag == .wildcard_pat) continue;
                    const elem_ty = self.concreteType(
                        if (i < tup_elems.len) TypeId.fromInt(tup_elems[i]) else self.nodeType(sub_id),
                    );
                    const proj_hir = try self.emitNode(.{
                        .tag = .hir_field_proj,
                        .flags = .{ .category = .place_imm, .is_synthetic = true },
                        .type_id = elem_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = rhs_val_hir.asInt(), .rhs = @intCast(i) },
                    }, .none);
                    const sub_slot = try self.allocTempLocal(elem_ty, tok, false);
                    try out_stmts.append(
                        self.allocator,
                        (try self.emitLocalDeclNode(sub_slot, proj_hir, tok)).asInt(),
                    );
                    try self.lowerParallelDestructureTargets(
                        sub_id,
                        try self.emitVarRef(sub_slot, tok, .none),
                        elem_ty,
                        tok,
                        out_stmts,
                        out_stores,
                    );
                }
                return;
            },
            .array_lit => {
                const elems = self.getAstExtraSlice(lhs_id, false);
                const arr_node = self.pool.getNode(unwrapped_rhs);
                const elem_ty = self.concreteType(
                    if (arr_node.tag == .array_ty or arr_node.tag == .slice_ty)
                        TypeId.fromInt(arr_node.lhs)
                    else
                        .unit_ty,
                );
                for (elems, 0..) |raw_sub, i| {
                    const sub_id = NodeIndex.fromInt(raw_sub);
                    if (sub_id.isNone() or self.ast_arena.getNode(sub_id).tag == .wildcard_pat) continue;
                    const idx_const = try self.emitConstVal(.{ .int_val = @intCast(i) }, .usize_ty, tok, .none, true);
                    const proj_hir = try self.emitNode(.{
                        .tag = .hir_index_proj,
                        .flags = .{ .category = .place_imm, .is_synthetic = true },
                        .type_id = elem_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = rhs_val_hir.asInt(), .rhs = idx_const.asInt() },
                    }, .none);
                    const sub_slot = try self.allocTempLocal(elem_ty, tok, false);
                    try out_stmts.append(
                        self.allocator,
                        (try self.emitLocalDeclNode(sub_slot, proj_hir, tok)).asInt(),
                    );
                    try self.lowerParallelDestructureTargets(
                        sub_id,
                        try self.emitVarRef(sub_slot, tok, .none),
                        elem_ty,
                        tok,
                        out_stmts,
                        out_stores,
                    );
                }
                return;
            },
            .struct_lit => {
                const field_exprs = self.getAstExtraSlice(lhs_id, true);
                var init_names: std.ArrayListUnmanaged(TokenIndex) = .empty;
                defer init_names.deinit(self.allocator);
                var has_spread = false;
                const lit_cst = self.ast_arena.getCstOrigin(lhs_id);
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
                                    const lk = self.tokens.getToken(leaf.token).kind;
                                    if (lk == .dotdot) {
                                        has_spread = true;
                                        break;
                                    }
                                    if (symbol_resolver.isIdentifierToken(lk)) {
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
                const named_len = if (has_spread and field_exprs.len > 0) field_exprs.len - 1 else field_exprs.len;
                for (field_exprs[0..named_len], 0..) |raw_sub, i| {
                    const sub_id = NodeIndex.fromInt(raw_sub);
                    if (sub_id.isNone() or self.ast_arena.getNode(sub_id).tag == .wildcard_pat) continue;
                    var f_ord: u32 = @intCast(i);
                    var f_ty: TypeId = self.nodeType(sub_id);
                    if (i < init_names.items.len and !init_names.items[i].isNone()) {
                        const f_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, init_names.items[i]);
                        if (self.findStructFieldInfo(unwrapped_rhs, f_lex)) |f_info| {
                            f_ord = f_info.ordinal;
                            f_ty = self.concreteType(f_info.field_ty);
                        }
                    }
                    const proj_hir = try self.emitNode(.{
                        .tag = .hir_field_proj,
                        .flags = .{ .category = .place_imm, .is_synthetic = true },
                        .type_id = f_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = rhs_val_hir.asInt(), .rhs = f_ord },
                    }, .none);
                    const sub_slot = try self.allocTempLocal(f_ty, tok, false);
                    try out_stmts.append(
                        self.allocator,
                        (try self.emitLocalDeclNode(sub_slot, proj_hir, tok)).asInt(),
                    );
                    try self.lowerParallelDestructureTargets(
                        sub_id,
                        try self.emitVarRef(sub_slot, tok, .none),
                        f_ty,
                        tok,
                        out_stmts,
                        out_stores,
                    );
                }
                return;
            },
            else => {},
        }

        const lhs_place_hir = try self.lowerPlaceWithMutCtx(lhs_id, .err_ty, true);
        const lhs_place_node = self.store.getNode(lhs_place_hir);
        const coerced_rhs = try self.applyImplicitCoercionIfNeeded(rhs_val_hir, lhs_place_node.type_id, tok);
        if (lhs_place_node.tag == .hir_bitfield_read) {
            const rmw_extra = try self.store.appendExtraSlice(&[2]u32{
                lhs_place_node.data.rhs,
                coerced_rhs.asInt(),
            });
            self.store.nodes.set(lhs_place_hir.asInt(), .{
                .tag = .hir_bitfield_rmw,
                .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                .type_id = .unit_ty,
                .origin_token = tok,
                .data = .{ .lhs = lhs_place_node.data.lhs, .rhs = rmw_extra },
            });
            try out_stores.append(self.allocator, lhs_place_hir.asInt());
            return;
        }
        const assign_hir = try self.emitNode(.{
            .tag = .hir_assign,
            .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = lhs_place_hir.asInt(), .rhs = coerced_rhs.asInt() },
        }, lhs_id);
        try out_stores.append(self.allocator, assign_hir.asInt());
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
        const tail_cat: ValueCategory = if (block_ty == .never_ty)
            .diverging
        else if (!tail_hir.isNone() and tail_hir.asInt() < self.store.nodes.len) blk: {
            const tail_node = self.store.getNode(tail_hir);
            break :blk switch (tail_node.tag) {
                .hir_index_proj, .hir_soa_field_ptr, .hir_subscript_call, .hir_field_proj => tail_node.flags.category,
                else => .rvalue,
            };
        } else .rvalue;
        return self.emitNode(.{
            .tag = .hir_block,
            .flags = .{
                .category = tail_cat,
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
            const is_ref_pat = self.hasKeywordInCst(pat_cst, .amp);
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
        if (self.parallel_pre_eval.fetchRemove(expr_id.asInt())) |pre_kv| {
            return pre_kv.value;
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
            .byte_lit => blk: {
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, ast_node.main_token);
                const byte_val = lexer.extractByteLiteralValue(lexeme) orelse 0;
                break :blk try self.emitConstVal(
                    .{ .int_val = byte_val },
                    .u8_ty,
                    ast_node.main_token,
                    expr_id,
                    false,
                );
            },
            .byte_string_lit => blk: {
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, ast_node.main_token);
                const cooked = lexer.cookStringLiteral(self.allocator, lexeme) catch
                    try self.allocator.dupe(u8, "");
                defer self.allocator.free(cooked);
                const bytes_sym = try self.interner.intern(cooked);
                const arr_ty = try self.pool.internArray(.u8_ty, @intCast(cooked.len), false);
                const ref_arr_ty = try self.pool.internRef(arr_ty, false);
                break :blk try self.emitConstVal(
                    .{ .bytes_val = bytes_sym },
                    ref_arr_ty,
                    ast_node.main_token,
                    expr_id,
                    false,
                );
            },
            .string_lit => try self.lowerStringLitOrInterp(expr_id, target_ty),
            .self_val, .ident_expr, .path_expr => try self.lowerIdentOrPathExpr(expr_id, target_ty),
            .contextual_variant => try self.lowerContextualVariant(expr_id, target_ty),
            .tuple_lit => try self.lowerTupleLit(expr_id, target_ty),
            .array_lit => try self.lowerArrayLit(expr_id, target_ty),
            .struct_lit => try self.lowerStructLit(expr_id, target_ty),
            .unary_expr => try self.lowerUnaryExpr(expr_id, target_ty),
            .deref_expr => try self.lowerPostfixDerefExpr(expr_id, target_ty),
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
            .for_stmt => try self.lowerForExpr(expr_id, target_ty),
            .while_stmt => try self.lowerWhileStmt(expr_id, target_ty),
            .return_stmt => try self.lowerReturnNode(expr_id),
            .break_stmt => try self.lowerBreakNode(expr_id, false),
            .continue_stmt => try self.lowerContinueNode(expr_id, false),
            .walrus_expr => try self.lowerWalrusExpr(expr_id, target_ty),
            .is_expr => try self.lowerStandaloneIsExpr(expr_id),
            .range_expr => try self.lowerRangeValueExpr(expr_id, target_ty),
            .dollar_expr => try self.lowerDollarExpr(expr_id),
            .context_expr => try self.lowerContextExpr(expr_id, target_ty),
            .unreachable_expr => try self.emitNode(.{
                .tag = .hir_unreachable,
                .flags = .{ .category = .diverging, .is_unsafe = self.is_in_unsafe },
                .type_id = .never_ty,
                .origin_token = ast_node.main_token,
            }, expr_id),
            .with_expr => try self.lowerWithExpr(expr_id, target_ty),
            .named_arg => if (ast_node.lhs.tag == .node)
                try self.lowerExpr(NodeIndex.fromInt(ast_node.lhs.payload), target_ty)
            else
                try self.emitErrorHole(ast_node.main_token, expr_id, target_ty),
            .closure_expr => try self.lowerClosureExpr(expr_id, target_ty),
            .await_expr => try self.lowerAwaitExpr(expr_id, target_ty),
            else => try self.emitErrorHole(ast_node.main_token, expr_id, target_ty),
        };

        const coerce_ty = if (!expected_ty.isError()) expected_ty else target_ty;
        return self.applyImplicitCoercionIfNeeded(raw_hir, coerce_ty, ast_node.main_token);
    }

    /// Unwraps `.named_arg` (`label = expr`) to its inner value `NodeIndex`, leaving positional args unchanged.
    fn unwrapCallArgAst(self: *const HirLowerer, arg_id: NodeIndex) NodeIndex {
        if (!arg_id.isNone() and arg_id.asInt() < self.ast_arena.countNodes()) {
            const arg_node = self.ast_arena.getNode(arg_id);
            if (arg_node.tag == .named_arg and arg_node.lhs.tag == .node) {
                return NodeIndex.fromInt(arg_node.lhs.payload);
            }
        }
        return arg_id;
    }

    /// Lowers a `.for_stmt` appearing in expression position (`for x in xs { break x; } orelse fallback`).
    fn lowerForExpr(self: *HirLowerer, expr_id: NodeIndex, expected_ty: TypeId) anyerror!HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        var stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer stmts.deinit(self.allocator);
        try self.lowerForStmt(expr_id, &stmts, expected_ty);
        if (stmts.items.len == 0) return self.emitUnitConst(ast_node.main_token, expr_id);
        if (stmts.items.len == 1) return HirIndex.fromInt(stmts.items[0]);
        return self.emitSyntheticBlock(stmts.items, .none, .unit_ty, ast_node.main_token);
    }

    /// Shared local allocation and initializer lowering for `x := expr` (`var x := expr`, `x: T := expr`, `SE-01`).
    fn lowerWalrusCore(
        self: *HirLowerer,
        expr_id: NodeIndex,
        expected_ty: TypeId,
    ) anyerror!struct { slot_id: u32, decl_hir: HirIndex, ident_tok: TokenIndex, slot_ty: TypeId } {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const ident_tok = if (ast_node.lhs.tag == .token)
            TokenIndex.fromInt(ast_node.lhs.payload)
        else
            tok;
        const extra = self.getAstExtraSlice(expr_id, true);
        const is_var = extra.len >= 1 and extra[0] != 0;
        const type_node = if (extra.len >= 2) NodeIndex.fromInt(extra[1]) else .none;
        const init_id = if (extra.len >= 3) NodeIndex.fromInt(extra[2]) else .none;

        const sym_idx = self.nodeSymbol(expr_id);
        const expected_init_ty = if (!sym_idx.isNone())
            self.concreteType(self.sym_table.getSymbol(sym_idx).type_id)
        else if (!type_node.isNone())
            self.concreteType(self.nodeType(type_node))
        else if (!expected_ty.isError() and expected_ty != .unit_ty)
            self.concreteType(expected_ty)
        else
            self.nodeType(expr_id);

        const raw_init_hir = try self.lowerExpr(init_id, expected_init_ty);
        if (!raw_init_hir.isNone() and self.store.getNode(raw_init_hir).tag == .hir_closure and
            self.hasAttrNamedInCst(self.ast_arena.getCstOrigin(expr_id), "local"))
        {
            const fn_meta_idx = self.store.getNode(raw_init_hir).data.lhs;
            if (fn_meta_idx < self.store.functions.items.len) {
                self.store.functions.items[fn_meta_idx].is_local_closure = true;
            }
        }

        const slot_ty = self.concreteType(if (!expected_init_ty.isError())
            expected_init_ty
        else
            self.store.getNode(raw_init_hir).type_id);
        const init_hir = try self.applyImplicitCoercionIfNeeded(raw_init_hir, slot_ty, tok);

        const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, ident_tok);
        const is_wildcard = lexeme.len == 0 or std.mem.eql(u8, lexeme, "_");
        const name_id = if (is_wildcard) SymbolId.empty else try self.interner.intern(lexeme);
        const decl_span = if (!ident_tok.isNone() and ident_tok.asInt() < self.tokens.countTokens())
            self.tokens.getTokenSpan(self.store.file_id, ident_tok)
        else
            self.astSpan(expr_id);

        const slot_id = try self.store.appendLocal(.{
            .name = name_id,
            .type_id = slot_ty,
            .decl_span = decl_span,
            .mode = .let_mode,
            .is_mut = is_var,
            .is_param = false,
            .is_temp = is_wildcard,
            .is_cond_binding = self.is_in_cond_scope,
            .symbol_index = sym_idx,
        });
        if (!sym_idx.isNone()) {
            try self.symbol_to_local.put(self.allocator, sym_idx.asInt(), slot_id);
        }
        try self.pushLexicalLocal(name_id, slot_id);

        const decl_hir = try self.emitNode(.{
            .tag = .hir_local_decl,
            .flags = .{ .category = .rvalue, .is_synthetic = is_wildcard, .is_unsafe = self.is_in_unsafe },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = slot_id, .rhs = init_hir.asInt() },
        }, expr_id);
        return .{ .slot_id = slot_id, .decl_hir = decl_hir, .ident_tok = ident_tok, .slot_ty = slot_ty };
    }

    /// Lowers `x := expr` in expression or `ConditionScope` position, yielding the bound local reference (`SE-01`).
    fn lowerWalrusExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) anyerror!HirIndex {
        const walrus = try self.lowerWalrusCore(expr_id, target_ty);
        const ref_hir = try self.emitVarRef(walrus.slot_id, walrus.ident_tok, .none);
        const blk_hir = try self.emitSyntheticBlock(
            &[1]u32{walrus.decl_hir.asInt()},
            ref_hir,
            walrus.slot_ty,
            self.ast_arena.getNode(expr_id).main_token,
        );
        self.store.nodes.items(.flags)[blk_hir.asInt()].category = self.store.getNode(ref_hir).flags.category;
        return blk_hir;
    }

    /// Lowers standalone `expr is Pattern` and `expr is not Pattern` into a two-arm boolean `hir_match` (`SE-02`).
    fn lowerStandaloneIsExpr(self: *HirLowerer, expr_id: NodeIndex) anyerror!HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const is_negated = !tok.isNone() and tok.asInt() < self.tokens.countTokens() and
            self.tokens.getToken(tok).kind == .kw_not;
        const scrut_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;
        const pat_id = if (ast_node.rhs.tag == .node) NodeIndex.fromInt(ast_node.rhs.payload) else .none;

        const scrutinee_hir = try self.lowerExpr(scrut_id, .err_ty);
        const scrut_ty = self.store.getNode(scrutinee_hir).type_id;
        const local_checkpoint = self.local_shadow_log.items.len;
        defer self.popLexicalLocalsTo(local_checkpoint);

        const pat_idx = try self.lowerTopPattern(pat_id, scrut_ty, false);
        const wild_pat = try self.store.appendPat(.{
            .type_id = scrut_ty,
            .origin_token = tok,
            .kind = .wildcard,
        });
        const arm_start: u32 = @intCast(self.store.match_arms.items.len);
        try self.store.match_arms.append(self.allocator, .{
            .pat_idx = pat_idx,
            .guard_hir = .none,
            .body_hir = try self.emitConstVal(.{ .bool_val = !is_negated }, .bool_ty, tok, .none, true),
            .origin_token = tok,
        });
        try self.store.match_arms.append(self.allocator, .{
            .pat_idx = wild_pat,
            .guard_hir = .none,
            .body_hir = try self.emitConstVal(.{ .bool_val = is_negated }, .bool_ty, tok, .none, true),
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

    /// Lowers a standalone `.range_expr` value (`a..b`, `a..=b`, `..b`, `a..`, `..`) into `hir_construct`.
    fn lowerRangeValueExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) anyerror!HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const range_info = self.extractRangeAstInfo(expr_id) orelse
            return self.emitErrorHole(tok, expr_id, target_ty);

        var bound_ty: TypeId = .usize_ty;
        const res_ty = if (!target_ty.isError())
            self.concreteType(target_ty)
        else
            self.concreteType(self.nodeType(expr_id));
        if (!res_ty.isError() and self.pool.getTag(res_ty) == .tuple_ty) {
            const elems = self.pool.getTupleElements(res_ty);
            if (elems.len >= 1) bound_ty = self.concreteType(TypeId.fromInt(elems[0]));
        } else if (!range_info.start_id.isNone()) {
            const start_ty = self.nodeType(range_info.start_id);
            if (!start_ty.isError()) bound_ty = self.concreteType(start_ty);
        } else if (!range_info.end_id.isNone()) {
            const end_ty = self.nodeType(range_info.end_id);
            if (!end_ty.isError()) bound_ty = self.concreteType(end_ty);
        }

        const start_hir = if (!range_info.start_id.isNone())
            try self.lowerExpr(range_info.start_id, bound_ty)
        else
            try self.emitConstVal(.{ .int_val = 0 }, bound_ty, tok, .none, true);
        const end_hir = if (!range_info.end_id.isNone())
            try self.lowerExpr(range_info.end_id, bound_ty)
        else
            try self.emitConstVal(.{ .int_val = std.math.maxInt(i64) }, bound_ty, tok, .none, true);

        const final_ty = if (!res_ty.isError()) res_ty else try self.pool.internTuple(&[2]TypeId{ bound_ty, bound_ty });
        if (self.pool.getTag(final_ty) == .tuple_ty) {
            const tup_elems = self.pool.getTupleElements(final_ty);
            if (tup_elems.len >= 3) {
                const incl_hir = try self.emitConstVal(
                    .{ .bool_val = range_info.is_inclusive },
                    .bool_ty,
                    tok,
                    .none,
                    true,
                );
                const extra_idx = try self.store.appendLenPrefixedExtra(
                    &[3]u32{ start_hir.asInt(), end_hir.asInt(), incl_hir.asInt() },
                );
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = final_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirConstructKind.tuple_init), .rhs = extra_idx },
                }, expr_id);
            }
        }
        const extra_idx = try self.store.appendLenPrefixedExtra(&[2]u32{ start_hir.asInt(), end_hir.asInt() });
        const construct_kind: HirConstructKind = if (self.pool.getTag(final_ty) == .struct_ty)
            .struct_init
        else
            .tuple_init;
        return self.emitNode(.{
            .tag = .hir_construct,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = final_ty,
            .origin_token = tok,
            .data = .{ .lhs = @backingInt(construct_kind), .rhs = extra_idx },
        }, expr_id);
    }

    /// Lowers `$` (`AstTag.dollar_expr`) inside `base[…]` to the innermost active receiver length local (`SE-04`).
    fn lowerDollarExpr(self: *HirLowerer, expr_id: NodeIndex) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (self.dollar_len_stack.items.len > 0) {
            const len_local = self.dollar_len_stack.items[self.dollar_len_stack.items.len - 1];
            return self.emitVarRef(len_local, ast_node.main_token, expr_id);
        }
        return self.emitErrorHole(ast_node.main_token, expr_id, .usize_ty);
    }

    /// Resolves the canonical `TypeId` of an implicit `Context` slot (`SE-08`), synchronized with `type_system.zig`.
    fn resolveContextSlotType(self: *HirLowerer, layout: type_system.ContextFieldLayout) !TypeId {
        switch (layout.kind) {
            .rng_seed => return .u64_ty,
            .allocator, .temp_allocator => {
                if (self.lookupNominalTypeByName("Allocator")) |found_ty| return found_ty;
                return self.pool.internRawPtr(.u8_ty, true);
            },
            .scratch => {
                if (self.lookupNominalTypeByName("BumpArena")) |arena_ty| {
                    return self.pool.internArray(arena_ty, 2, false);
                }
                if (self.lookupNominalTypeByName("Arena")) |found_ty| return found_ty;
                return self.pool.internRawPtr(.u8_ty, true);
            },
            .trace_sink => {
                if (self.lookupNominalTypeByName("TraceSink")) |found_ty| return found_ty;
                return self.pool.internRawPtr(.u8_ty, true);
            },
            .logger => {
                if (self.lookupNominalTypeByName("Logger")) |found_ty| return found_ty;
                return self.pool.internRawPtr(.u8_ty, true);
            },
            .diagnostics => {
                if (self.lookupNominalTypeByName("DiagSink")) |found_ty| return found_ty;
                if (self.lookupNominalTypeByName("Diagnostics")) |found_ty| return found_ty;
                if (self.lookupNominalTypeByName("DiagnosticSink")) |sink_ty| {
                    return self.pool.internRawPtr(sink_ty, true);
                }
                return self.pool.internRawPtr(.u8_ty, true);
            },
            .cancel_token => {
                if (self.lookupNominalTypeByName("CancelToken")) |found_ty| return found_ty;
                return self.pool.internOptional(try self.pool.internRawPtr(.u8_ty, true));
            },
            .reactor => {
                if (self.lookupNominalTypeByName("Reactor")) |found_ty| return found_ty;
                return self.pool.internRawPtr(.u8_ty, false);
            },
            .reactor_ctx => {
                if (self.lookupNominalTypeByName("ReactorCtx")) |found_ty| return found_ty;
                return self.pool.internRawPtr(.u8_ty, true);
            },
        }
    }

    /// Looks up a nominal `TypeId` by `type_name` in `current_scope` or `prelude_scope`.
    fn lookupNominalTypeByName(self: *const HirLowerer, type_name: []const u8) ?TypeId {
        const name_id = self.interner.lookup(type_name) orelse return null;
        switch (self.sym_table.lookupLexical(self.current_scope, name_id, NamespaceMask.TYPE_ONLY)) {
            .found => |sym_idx| {
                const sym_ty = self.sym_table.getSymbol(sym_idx).type_id;
                if (!sym_ty.isError()) return self.concreteType(sym_ty);
            },
            else => {},
        }
        return null;
    }

    /// Lowers a standalone `context` expression (`AstTag.context_expr`) by materializing its canonical slots (`SE-08`).
    fn lowerContextExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const res_ty = if (!target_ty.isError())
            self.concreteType(target_ty)
        else
            self.concreteType(self.nodeType(expr_id));
        if (!res_ty.isError() and self.pool.getTag(res_ty) == .struct_ty) {
            const struct_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(self.pool.getNode(res_ty).rhs)).*;
            if (!struct_sym.target_scope.isNone()) {
                var field_hirs: std.ArrayListUnmanaged(u32) = .empty;
                defer field_hirs.deinit(self.allocator);
                for (self.sym_table.getScopeMembers(struct_sym.target_scope)) |mem_idx| {
                    const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                    if (mem_sym.kind != .field_sym) continue;
                    const slot_ord: u32 = if (type_system.ContextFieldLayout.fromFieldName(mem_sym.name_text)) |info|
                        info.slot_ordinal
                    else
                        0;
                    const get_hir = try self.emitNode(.{
                        .tag = .hir_ctx_get,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = self.concreteType(mem_sym.type_id),
                        .origin_token = tok,
                        .data = .{ .lhs = slot_ord, .rhs = 0 },
                    }, .none);
                    try field_hirs.append(self.allocator, get_hir.asInt());
                }
                const extra_idx = try self.store.appendLenPrefixedExtra(field_hirs.items);
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = res_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirConstructKind.struct_init), .rhs = extra_idx },
                }, expr_id);
            }
        }
        const fallback_ty = if (!res_ty.isError()) res_ty else try self.pool.internRawPtr(.u8_ty, true);
        return self.emitNode(.{
            .tag = .hir_ctx_get,
            .flags = .{ .category = .rvalue },
            .type_id = fallback_ty,
            .origin_token = tok,
            .data = .{ .lhs = 0, .rhs = 0 },
        }, expr_id);
    }

    /// Lowers `with context.slot = val { body }` with `hir_defer` LIFO restoration and region push/pop (`SE-08`).
    fn lowerWithExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) anyerror!HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const extra = self.getAstExtraSlice(expr_id, false);
        const override_count: usize = if (extra.len >= 1) extra[0] else 0;
        const body_id = if (ast_node.rhs.tag == .node) NodeIndex.fromInt(ast_node.rhs.payload) else .none;
        if (override_count == 0) {
            return self.lowerBlockExpr(body_id, target_ty, false);
        }

        var with_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer with_stmts.deinit(self.allocator);

        var ov_i: usize = 0;
        while (ov_i < override_count and 1 + 2 * ov_i + 1 < extra.len) : (ov_i += 1) {
            const slot_tok = TokenIndex.fromInt(extra[1 + 2 * ov_i]);
            const val_ast_id = NodeIndex.fromInt(extra[1 + 2 * ov_i + 1]);
            const slot_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, slot_tok);
            const maybe_layout = type_system.ContextFieldLayout.fromFieldName(slot_name);
            if (maybe_layout == null or !maybe_layout.?.kind.isWithOverridable()) {
                const discarded = try self.lowerExpr(val_ast_id, .err_ty);
                const tmp_slot = try self.allocTempLocal(self.store.getNode(discarded).type_id, slot_tok, false);
                try with_stmts.append(self.allocator, (try self.emitLocalDeclNode(tmp_slot, discarded, slot_tok)).asInt());
                continue;
            }
            const layout = maybe_layout.?;
            const slot_ord: u32 = layout.slot_ordinal;
            const is_region_slot = layout.kind.isWithOverridable();

            const canonical_slot_ty = try self.resolveContextSlotType(layout);
            const raw_val_hir = try self.lowerPlaceWithMutCtx(val_ast_id, .err_ty, false);
            const raw_val_ty = self.store.getNode(raw_val_hir).type_id;
            const has_nominal_slot_ty = !canonical_slot_ty.isError() and
                self.pool.getTag(canonical_slot_ty) == .struct_ty;
            const is_raw_ptr_or_ref = switch (self.pool.getTag(self.pool.unwrapUnderlyingType(raw_val_ty))) {
                .ref_ty, .mut_ref_ty, .raw_ptr_ty => true,
                else => false,
            };
            const effective_slot_ty = if ((has_nominal_slot_ty and
                (raw_val_ty == canonical_slot_ty or is_raw_ptr_or_ref)) or
                layout.kind == .rng_seed or raw_val_ty.isError())
                canonical_slot_ty
            else
                raw_val_ty;

            // Keep coerced borrows (e.g., `&mut arena`) anchored in a live local across `body` for `mir_sast` borrow safety:
            const hold_local = try self.allocTempLocal(raw_val_ty, slot_tok, false);
            try with_stmts.append(self.allocator, (try self.emitLocalDeclNode(hold_local, raw_val_hir, slot_tok)).asInt());
            var new_slot_hir = try self.emitVarRef(hold_local, slot_tok, .none);
            if (raw_val_ty != effective_slot_ty) {
                new_slot_hir = try self.emitNode(.{
                    .tag = .hir_cast,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = effective_slot_ty,
                    .origin_token = slot_tok,
                    .data = .{ .lhs = new_slot_hir.asInt(), .rhs = @backingInt(HirCastKind.ptr_cast) },
                }, .none);
            }

            const prev_ctx_hir = try self.emitNode(.{
                .tag = .hir_ctx_get,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = effective_slot_ty,
                .origin_token = slot_tok,
                .data = .{ .lhs = slot_ord, .rhs = 0 },
            }, .none);
            const saved_local = try self.allocTempLocal(effective_slot_ty, slot_tok, false);
            try with_stmts.append(
                self.allocator,
                (try self.emitLocalDeclNode(saved_local, prev_ctx_hir, slot_tok)).asInt(),
            );

            const set_new_hir = try self.emitNode(.{
                .tag = .hir_ctx_set,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = .unit_ty,
                .origin_token = slot_tok,
                .data = .{ .lhs = slot_ord, .rhs = new_slot_hir.asInt() },
            }, .none);
            try with_stmts.append(self.allocator, set_new_hir.asInt());

            if (is_region_slot) {
                const region_val = if (raw_val_ty != effective_slot_ty)
                    try self.emitNode(.{
                        .tag = .hir_cast,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = effective_slot_ty,
                        .origin_token = slot_tok,
                        .data = .{
                            .lhs = (try self.emitVarRef(hold_local, slot_tok, .none)).asInt(),
                            .rhs = @backingInt(HirCastKind.ptr_cast),
                        },
                    }, .none)
                else
                    try self.emitVarRef(hold_local, slot_tok, .none);
                const push_hir = try self.emitNode(.{
                    .tag = .hir_ctx_region_push,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .origin_token = slot_tok,
                    .data = .{ .lhs = slot_ord, .rhs = region_val.asInt() },
                }, .none);
                try with_stmts.append(self.allocator, push_hir.asInt());
            }

            var cleanup_stmts: [2]u32 = undefined;
            var cleanup_len: usize = 0;
            if (is_region_slot) {
                const pop_hir = try self.emitNode(.{
                    .tag = .hir_ctx_region_pop,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .origin_token = slot_tok,
                    .data = .{ .lhs = slot_ord, .rhs = 0 },
                }, .none);
                cleanup_stmts[cleanup_len] = pop_hir.asInt();
                cleanup_len += 1;
            }
            const restore_set_hir = try self.emitNode(.{
                .tag = .hir_ctx_set,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = .unit_ty,
                .origin_token = slot_tok,
                .data = .{
                    .lhs = slot_ord,
                    .rhs = (try self.emitVarRef(saved_local, slot_tok, .none)).asInt(),
                },
            }, .none);
            cleanup_stmts[cleanup_len] = restore_set_hir.asInt();
            cleanup_len += 1;

            const cleanup_blk = try self.emitSyntheticBlock(
                cleanup_stmts[0..cleanup_len],
                .none,
                .unit_ty,
                slot_tok,
            );
            const defer_hir = try self.emitNode(.{
                .tag = .hir_defer,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = .unit_ty,
                .origin_token = slot_tok,
                .data = .{ .lhs = 0, .rhs = cleanup_blk.asInt() },
            }, .none);
            try with_stmts.append(self.allocator, defer_hir.asInt());
        }

        const body_hir = try self.lowerBlockExpr(body_id, target_ty, false);
        const body_ty = self.store.getNode(body_hir).type_id;
        const final_ty = if (!target_ty.isError()) self.concreteType(target_ty) else body_ty;
        return self.emitSyntheticBlock(with_stmts.items, body_hir, final_ty, tok);
    }

    /// Inserts an explicit `hir_cast` or zero-hole `fmt_args` node when `expected_ty` requires implicit coercion.
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

        if (actual_ty == .str_ty and concrete_exp == .fmt_args_ty) {
            const fmt_extra = try self.store.appendExtraSlice(&[3]u32{ 1, 0, hir_id.asInt() });
            return self.emitNode(.{
                .tag = .hir_construct,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = .fmt_args_ty,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(HirConstructKind.fmt_args), .rhs = fmt_extra },
            }, .none);
        }

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
        if (act_node.tag == .mut_ref_ty and exp_node.tag == .mut_ref_ty and
            act_node.lhs == exp_node.lhs and act_node.rhs != exp_node.rhs)
        {
            return self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = concrete_exp,
                .origin_token = tok,
                .data = .{ .lhs = hir_id.asInt(), .rhs = @backingInt(HirCastKind.ref_coerce) },
            }, .none);
        }
        if (act_node.tag == .closure_ty and exp_node.tag == .fn_ty) {
            return self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = concrete_exp,
                .origin_token = tok,
                .data = .{ .lhs = hir_id.asInt(), .rhs = @backingInt(HirCastKind.ptr_cast) },
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

    /// Lowers `.string_lit`, `"""…"""`, and `r"…"` literals, supporting dual-mode `FmtArgs` vs `String` (`SE-12`).
    fn lowerStringLitOrInterp(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const raw_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
        const interp_meta_opt = if (self.side_tables) |tables| tables.getStringInterp(expr_id) else null;
        const is_fmt_args_mode = (if (interp_meta_opt) |meta| meta.is_fmt_args_mode else false) or
            target_ty == .fmt_args_ty;

        // Check raw string literal `r"…"`, `r#"…"#`, `r"""…"""`, or `r#"""…"""#` with verbatim UTF-8 bytes:
        if (raw_lex.len > 0 and raw_lex[0] == 'r') {
            const cooked_raw = lexer.cookStringLiteral(self.allocator, raw_lex) catch
                try self.allocator.dupe(u8, type_system.extractRawStringContent(raw_lex) orelse "");
            defer self.allocator.free(cooked_raw);
            const raw_id = try self.interner.intern(cooked_raw);
            const str_hir = try self.emitConstVal(.{ .str_val = raw_id }, .str_ty, tok, expr_id, false);
            if (is_fmt_args_mode) {
                const fmt_extra = try self.store.appendExtraSlice(&[3]u32{ 1, 0, str_hir.asInt() });
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .fmt_args_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirConstructKind.fmt_args), .rhs = fmt_extra },
                }, expr_id);
            }
            return str_hir;
        }

        const is_multiline = raw_lex.len >= 6 and std.mem.startsWith(u8, raw_lex, "\"\"\"") and
            std.mem.endsWith(u8, raw_lex, "\"\"\"");
        var body_slice = if (is_multiline) raw_lex[3 .. raw_lex.len - 3] else extractQuotedBody(raw_lex);
        var dedent_cols: usize = 0;
        if (is_multiline) {
            if (body_slice.len >= 2 and body_slice[0] == '\r' and body_slice[1] == '\n') {
                body_slice = body_slice[2..];
            } else if (body_slice.len >= 1 and body_slice[0] == '\n') {
                body_slice = body_slice[1..];
            }
            if (std.mem.lastIndexOfScalar(u8, body_slice, '\n')) |last_nl| {
                const closing_indent = body_slice[last_nl + 1 ..];
                var is_all_ws = true;
                for (closing_indent) |ch| {
                    if (ch != ' ' and ch != '\t') {
                        is_all_ws = false;
                        break;
                    }
                }
                if (is_all_ws) {
                    dedent_cols = closing_indent.len;
                    body_slice = if (last_nl > 0 and body_slice[last_nl - 1] == '\r')
                        body_slice[0 .. last_nl - 1]
                    else
                        body_slice[0..last_nl];
                }
            }
        }

        if (type_system.scanNextInterpolationSegment(body_slice, 0) == null) {
            const cooked = lexer.cookStringLiteral(self.allocator, raw_lex) catch
                try type_system.decodeStandardStringSegment(self.allocator, body_slice);
            defer self.allocator.free(cooked);
            const str_id = try self.interner.intern(cooked);
            const str_hir = try self.emitConstVal(.{ .str_val = str_id }, .str_ty, tok, expr_id, false);
            if (is_fmt_args_mode) {
                const fmt_extra = try self.store.appendExtraSlice(&[3]u32{ 1, 0, str_hir.asInt() });
                return self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .fmt_args_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirConstructKind.fmt_args), .rhs = fmt_extra },
                }, expr_id);
            }
            return str_hir;
        }

        var piece_hirs: std.ArrayListUnmanaged(u32) = .empty;
        defer piece_hirs.deinit(self.allocator);
        var hole_hirs: std.ArrayListUnmanaged(HirIndex) = .empty;
        defer hole_hirs.deinit(self.allocator);
        var hole_specs: std.ArrayListUnmanaged(u64) = .empty;
        defer hole_specs.deinit(self.allocator);
        var hole_has_spec: std.ArrayListUnmanaged(bool) = .empty;
        defer hole_has_spec.deinit(self.allocator);

        var scan_pos: usize = 0;
        var is_at_line_start = is_multiline;
        while (type_system.scanNextInterpolationSegment(body_slice, scan_pos)) |seg| {
            const raw_seg = body_slice[scan_pos..seg.open_brace];
            const hole_raw = body_slice[seg.expr_start..seg.expr_end];
            const split = type_system.splitInterpolationHole(hole_raw);

            var piece_buf: std.ArrayListUnmanaged(u8) = .empty;
            defer piece_buf.deinit(self.allocator);
            const decoded_lit = try decodeInterpolatedStaticPiece(
                self.allocator,
                raw_seg,
                dedent_cols,
                &is_at_line_start,
            );
            defer self.allocator.free(decoded_lit);
            try piece_buf.appendSlice(self.allocator, decoded_lit);
            if (split.has_debug_eq) {
                try piece_buf.appendSlice(self.allocator, split.debug_prefix_slice);
            }
            const piece_id = try self.interner.intern(piece_buf.items);
            const piece_hir = try self.emitConstVal(.{ .str_val = piece_id }, .str_ty, tok, .none, true);
            try piece_hirs.append(self.allocator, piece_hir.asInt());

            const expr_trimmed = std.mem.trim(u8, split.expr_slice, " \t\r\n");
            const lowered_hole = try self.lowerInterpolatedSegment(expr_trimmed, tok);
            const fmt_spec = lexer.parseFormatSpec(split.spec_slice orelse "", split.has_debug_eq) catch
                lexer.FmtSpec.pack(
                    ' ',
                    .none,
                    .default,
                    false,
                    false,
                    if (split.has_debug_eq) .debug else .display,
                    split.has_debug_eq,
                    null,
                    null,
                );
            const packed_spec: u64 = @as(u64, fmt_spec.flags_and_fill) |
                (@as(u64, fmt_spec.width_or_none) << 32) |
                (@as(u64, fmt_spec.precision_or_none) << 48);
            try hole_hirs.append(self.allocator, lowered_hole);
            try hole_specs.append(self.allocator, packed_spec);
            try hole_has_spec.append(self.allocator, split.spec_slice != null or split.has_debug_eq);

            is_at_line_start = false;
            scan_pos = seg.after_close;
        }

        const tail_decoded = try decodeInterpolatedStaticPiece(
            self.allocator,
            body_slice[scan_pos..],
            dedent_cols,
            &is_at_line_start,
        );
        defer self.allocator.free(tail_decoded);
        const tail_id = try self.interner.intern(tail_decoded);
        const tail_hir = try self.emitConstVal(.{ .str_val = tail_id }, .str_ty, tok, .none, true);
        try piece_hirs.append(self.allocator, tail_hir.asInt());

        // [1] Checking Mode (`FmtArgs`, `SE-12`): stack-scoped `[FmtArg; k]` + static `pieces` with zero `alloc` taint!
        if (is_fmt_args_mode) {
            var extra_words: std.ArrayListUnmanaged(u32) = .empty;
            defer extra_words.deinit(self.allocator);
            try extra_words.append(self.allocator, @intCast(piece_hirs.items.len));
            try extra_words.append(self.allocator, @intCast(hole_hirs.items.len));
            try extra_words.appendSlice(self.allocator, piece_hirs.items);

            for (hole_hirs.items, 0..) |h_hir, idx| {
                const spec_u64 = hole_specs.items[idx];
                try extra_words.append(self.allocator, h_hir.asInt());
                try extra_words.append(self.allocator, @truncate(spec_u64));
                try extra_words.append(self.allocator, @truncate(spec_u64 >> 32));
            }
            const fmt_extra = try self.store.appendExtraSlice(extra_words.items);
            return self.emitNode(.{
                .tag = .hir_construct,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = .fmt_args_ty,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(HirConstructKind.fmt_args), .rhs = fmt_extra },
            }, expr_id);
        }

        // [2] Synthesis Mode (`str` / `String`, `SE-12`): interleave non-empty pieces and formatted hole values!
        var part_hirs: std.ArrayListUnmanaged(u32) = .empty;
        defer part_hirs.deinit(self.allocator);
        for (hole_hirs.items, 0..) |h_hir, idx| {
            const p_hir = HirIndex.fromInt(piece_hirs.items[idx]);
            const p_node = self.store.getNode(p_hir);
            if (p_node.tag == .hir_const_val and p_node.data.lhs < self.store.const_pool.items.len) {
                const cval = self.store.const_pool.items[p_node.data.lhs];
                if (cval == .str_val and self.interner.get(cval.str_val).len > 0) {
                    try part_hirs.append(self.allocator, p_hir.asInt());
                }
            }
            const h_ty = self.store.getNode(h_hir).type_id;
            if (h_ty == .str_ty and !hole_has_spec.items[idx]) {
                try part_hirs.append(self.allocator, h_hir.asInt());
            } else {
                const spec_u64 = hole_specs.items[idx];
                const fv_extra = try self.store.appendExtraSlice(&[3]u32{
                    h_hir.asInt(),
                    @truncate(spec_u64),
                    @truncate(spec_u64 >> 32),
                });
                const fv_hir = try self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .str_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @backingInt(HirConstructKind.fmt_value), .rhs = fv_extra },
                }, .none);
                try part_hirs.append(self.allocator, fv_hir.asInt());
            }
        }
        const last_p_hir = HirIndex.fromInt(piece_hirs.items[piece_hirs.items.len - 1]);
        const last_p_node = self.store.getNode(last_p_hir);
        if (last_p_node.tag == .hir_const_val and last_p_node.data.lhs < self.store.const_pool.items.len) {
            const cval = self.store.const_pool.items[last_p_node.data.lhs];
            if (cval == .str_val and self.interner.get(cval.str_val).len > 0) {
                try part_hirs.append(self.allocator, last_p_hir.asInt());
            }
        }

        const extra_idx = try self.store.appendLenPrefixedExtra(part_hirs.items);
        return self.emitNode(.{
            .tag = .hir_construct,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .str_ty,
            .origin_token = tok,
            .data = .{ .lhs = @backingInt(HirConstructKind.str_interp), .rhs = extra_idx },
        }, expr_id);
    }

    /// Lowers a `{expr}` segment inside an interpolated string literal.
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

        const outer_span = if (self.interp_override_span) |existing_span|
            existing_span
        else if (!tok.isNone() and tok.asInt() < self.tokens.countTokens())
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
        const saved_ov_src = self.interp_override_source;

        self.source = wrapper_buf.items;
        self.tokens = &sub_tokens;
        self.cst_arena = &sub_cst;
        self.ast_arena = &sub_ast;
        self.side_tables = null;
        self.node_extra_end = sub_extra_ends;
        self.cst_to_ast = sub_cst_map;
        self.interp_override_token = if (!saved_ov_tok.isNone()) saved_ov_tok else tok;
        self.interp_override_span = outer_span;
        if (self.interp_override_source == null) self.interp_override_source = saved_source;
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
            self.interp_override_source = saved_ov_src;
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
            const resolved_sym_idx = self.unwrapAliasSymbolIdx(sym_idx);
            const sym = self.sym_table.getSymbol(resolved_sym_idx).*;
            if (sym.kind == .const_sym) {
                if (try self.evalConstSymbol(resolved_sym_idx)) |folded_const| {
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
            const ref_cat: ValueCategory = if (sym.kind == .extern_static_sym)
                (if (sym.flags.is_mut) .place_mut else .place_imm)
            else
                .rvalue;
            return self.emitNode(.{
                .tag = .hir_global_ref,
                .flags = .{ .category = ref_cat, .is_unsafe = self.is_in_unsafe },
                .type_id = if (!target_ty.isError()) target_ty else self.concreteType(sym.type_id),
                .origin_token = tok,
                .data = .{ .lhs = sym.def_id.asInt(), .rhs = resolved_sym_idx.asInt() },
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
                    try self.lowerExpr(self.unwrapCallArgAst(NodeIndex.fromInt(arg_nodes[0])), payload_ty)
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
                    try self.lowerExpr(self.unwrapCallArgAst(NodeIndex.fromInt(arg_nodes[0])), payload_ty)
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
                const enum_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, target_ty);
                var_payload_ty = try enum_subst.applyMut(self.allocator, self.pool, var_payload_ty);
                var lowered_args: std.ArrayListUnmanaged(u32) = .empty;
                defer lowered_args.deinit(self.allocator);
                if (arg_nodes.len == 1) {
                    const first_arg = self.unwrapCallArgAst(NodeIndex.fromInt(arg_nodes[0]));
                    try lowered_args.append(
                        self.allocator,
                        (try self.lowerExpr(first_arg, var_payload_ty)).asInt(),
                    );
                } else if (arg_nodes.len > 1) {
                    const tup_elems = self.pool.getTupleElements(var_payload_ty);
                    for (arg_nodes, 0..) |raw_arg, i| {
                        const sub_ty = if (i < tup_elems.len) TypeId.fromInt(tup_elems[i]) else .err_ty;
                        const unwrapped_arg = self.unwrapCallArgAst(NodeIndex.fromInt(raw_arg));
                        try lowered_args.append(
                            self.allocator,
                            (try self.lowerExpr(unwrapped_arg, sub_ty)).asInt(),
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

        // Collect canonical `@cfg`-enabled struct / `bit_field` member declarations dynamically (`SE-18`):
        var canonical_tys: std.ArrayListUnmanaged(TypeId) = .empty;
        defer canonical_tys.deinit(self.allocator);
        var canonical_names: std.ArrayListUnmanaged(SymbolId) = .empty;
        defer canonical_names.deinit(self.allocator);
        var canonical_texts: std.ArrayListUnmanaged([]const u8) = .empty;
        defer canonical_texts.deinit(self.allocator);
        var canonical_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty;
        defer canonical_syms.deinit(self.allocator);
        const struct_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, target_ty);
        for (self.sym_table.getScopeMembers(struct_sym.target_scope)) |mem_idx| {
            const mem_sym = self.sym_table.getSymbol(mem_idx).*;
            if (mem_sym.kind != .field_sym) continue;
            if (!self.isSymbolCfgEnabled(mem_idx)) continue;
            try canonical_tys.append(
                self.allocator,
                try struct_subst.applyMut(self.allocator, self.pool, mem_sym.type_id),
            );
            try canonical_names.append(self.allocator, mem_sym.name);
            try canonical_texts.append(self.allocator, mem_sym.name_text);
            try canonical_syms.append(self.allocator, mem_idx);
        }
        const total_fields = canonical_tys.items.len;

        // Extract field names (and optional trailing `..` / `..base` / `..own base`) from CST `.field_init` subtrees:
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
                if (sub.subtree_size <= 1 and !sub.token.isNone() and
                    sub.token.asInt() < self.tokens.countTokens() and
                    self.tokens.getToken(sub.token).kind == .dotdot)
                {
                    has_spread = true;
                }
                cur += 1;
            }
        }

        const has_spread_base = has_spread and field_exprs.len > init_names.items.len and field_exprs.len > 0;
        var stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer stmts.deinit(self.allocator);
        var field_slots = try self.allocator.alloc(HirIndex, total_fields);
        defer self.allocator.free(field_slots);
        @memset(field_slots, .none);
        var is_out_of_order = false;
        var prev_ord: usize = 0;

        const named_expr_len = if (has_spread_base) field_exprs.len - 1 else field_exprs.len;
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
            const base_bf_hir = if (has_spread_base)
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

        if (has_spread_base) {
            const raw_spread_id = NodeIndex.fromInt(field_exprs[field_exprs.len - 1]);
            const spread_ast = self.ast_arena.getNode(raw_spread_id);
            const is_own_spread = spread_ast.tag == .unary_expr and spread_ast.lhs.tag == .node and
                !spread_ast.main_token.isNone() and
                (self.tokens.getToken(spread_ast.main_token).kind == .kw_own or
                    std.mem.eql(u8, symbol_resolver.extractTokenSlice(self.source, self.tokens, spread_ast.main_token), "own"));
            const base_expr_id = if (is_own_spread) NodeIndex.fromInt(spread_ast.lhs.payload) else raw_spread_id;

            if (is_own_spread) {
                // `..own base` (`SE-14`): move `base` into `spread_local`; omitted fields move out, while
                // overridden `AutoDrop` fields drop at scope exit and overridden `@linear` fields trigger `E0304`!
                const spread_hir = try self.lowerExpr(base_expr_id, target_ty);
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
            } else {
                // `..base` (`SE-14`): project omitted `Copy` fields directly on pure places so moving an overridden
                // `own` field from `base` never conflicts with a whole-struct `&base` borrow, or bind rvalue `base` once:
                const base_place_hir = try self.lowerPlaceWithMutCtx(base_expr_id, target_ty, false);
                if (self.isPurePlaceHir(base_place_hir)) {
                    var has_used_first_place = false;
                    for (0..total_fields) |ord_idx| {
                        if (field_slots[ord_idx].isNone()) {
                            const proj_base = if (!has_used_first_place) blk_first: {
                                has_used_first_place = true;
                                break :blk_first base_place_hir;
                            } else try self.lowerPlaceWithMutCtx(base_expr_id, target_ty, false);
                            field_slots[ord_idx] = try self.emitNode(.{
                                .tag = .hir_field_proj,
                                .flags = .{ .category = .place_imm, .is_synthetic = true },
                                .type_id = self.concreteType(canonical_tys.items[ord_idx]),
                                .origin_token = tok,
                                .data = .{
                                    .lhs = proj_base.asInt(),
                                    .rhs = @intCast(ord_idx),
                                },
                            }, .none);
                        }
                    }
                } else if (self.store.getNode(base_place_hir).flags.category == .rvalue) {
                    const spread_local = try self.allocTempLocal(target_ty, tok, false);
                    try stmts.append(
                        self.allocator,
                        (try self.emitLocalDeclNode(spread_local, base_place_hir, tok)).asInt(),
                    );
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
                } else {
                    const ref_ty = try self.pool.internRef(target_ty, false);
                    const addr_hir = try self.emitSyntheticAddrOf(base_place_hir, ref_ty, false, tok);
                    const ref_local = try self.allocTempLocal(ref_ty, tok, false);
                    try stmts.append(self.allocator, (try self.emitLocalDeclNode(ref_local, addr_hir, tok)).asInt());
                    for (0..total_fields) |ord_idx| {
                        if (field_slots[ord_idx].isNone()) {
                            const deref_base = try self.emitSyntheticDeref(
                                try self.emitVarRef(ref_local, tok, .none),
                                target_ty,
                                tok,
                            );
                            field_slots[ord_idx] = try self.emitNode(.{
                                .tag = .hir_field_proj,
                                .flags = .{ .category = .place_imm, .is_synthetic = true },
                                .type_id = self.concreteType(canonical_tys.items[ord_idx]),
                                .origin_token = tok,
                                .data = .{
                                    .lhs = deref_base.asInt(),
                                    .rhs = @intCast(ord_idx),
                                },
                            }, .none);
                        }
                    }
                }
            }
        } else if (has_spread) {
            // `S { explicit…, .. }` (`SE-14`): evaluate omitted fields' declared `= default_expr` in field order!
            const field_scope = if (!struct_sym.target_scope.isNone())
                struct_sym.target_scope
            else
                struct_sym.scope_id;
            for (0..total_fields) |ord_idx| {
                if (!field_slots[ord_idx].isNone()) continue;
                const f_ty = self.concreteType(canonical_tys.items[ord_idx]);
                const def_hir = try self.lowerStructFieldDefaultExpr(
                    field_scope,
                    canonical_syms.items[ord_idx],
                    f_ty,
                    tok,
                );
                const tmp_local = try self.allocTempLocal(self.store.getNode(def_hir).type_id, tok, false);
                try stmts.append(self.allocator, (try self.emitLocalDeclNode(tmp_local, def_hir, tok)).asInt());
                field_slots[ord_idx] = try self.emitVarRef(tmp_local, tok, .none);
            }
        }

        var final_fields: std.ArrayListUnmanaged(u32) = .empty;
        defer final_fields.deinit(self.allocator);
        if (struct_node.tag == .union_ty) {
            for (0..total_fields) |ord_idx| {
                if (!field_slots[ord_idx].isNone()) {
                    try final_fields.append(self.allocator, field_slots[ord_idx].asInt());
                }
            }
        } else {
            try final_fields.ensureTotalCapacity(self.allocator, total_fields);
            for (0..total_fields) |ord_idx| {
                const f_hir = if (!field_slots[ord_idx].isNone())
                    field_slots[ord_idx]
                else
                    try self.emitErrorHole(tok, expr_id, self.concreteType(canonical_tys.items[ord_idx]));
                final_fields.appendAssumeCapacity(f_hir.asInt());
            }
        }
        const extra_idx = try self.store.appendLenPrefixedExtra(final_fields.items);
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

    /// Resolves the `= default_expr` `NodeIndex` inside a `.struct_field` CST subtree (`SE-14`).
    fn extractStructFieldDefaultAst(
        field_sym: symbol_resolver.SymbolRecord,
        ast_arena: *const AstArena,
        cst_arena: *const LosslessCstArena,
        tokens: *const TokenBuffer,
        cst_map: []const NodeIndex,
    ) NodeIndex {
        if (!field_sym.ast_node.isNone() and field_sym.ast_node.asInt() < ast_arena.countNodes()) {
            const f_ast = ast_arena.getNode(field_sym.ast_node);
            if (f_ast.rhs.tag == .node) return NodeIndex.fromInt(f_ast.rhs.payload);
        }

        var field_cst = field_sym.cst_node;
        if (field_cst.isNone() or field_cst.asInt() >= cst_arena.countNodes() or
            cst_arena.getNode(field_cst).kind != .struct_field)
        {
            field_cst = .none;
            var scan_cst: u32 = 0;
            while (scan_cst < cst_arena.countNodes()) : (scan_cst += 1) {
                const cand_cst = CstNodeIndex.fromInt(scan_cst);
                const cand_rec = cst_arena.getNode(cand_cst);
                if (cand_rec.kind != .struct_field) continue;
                const f_end = @min(
                    @as(usize, scan_cst) + @max(@as(usize, cand_rec.subtree_size), 1),
                    cst_arena.countNodes(),
                );
                var leaf_cur: usize = @as(usize, scan_cst) + 1;
                while (leaf_cur < f_end) : (leaf_cur += 1) {
                    const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(leaf_cur)));
                    if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                        leaf.token.asInt() < tokens.countTokens())
                    {
                        const tok_kind = tokens.getToken(leaf.token).kind;
                        if (symbol_resolver.isIdentifierToken(tok_kind)) {
                            const span = tokens.getTokenSpan(field_sym.decl_span.file_id, leaf.token);
                            if (span.start_byte == field_sym.decl_span.start_byte) {
                                field_cst = cand_cst;
                            }
                            break;
                        }
                    }
                }
                if (!field_cst.isNone()) break;
            }
        }
        if (field_cst.isNone() or field_cst.asInt() >= cst_arena.countNodes()) return .none;

        const start_idx: usize = field_cst.asInt();
        const rec = cst_arena.getNode(field_cst);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            cst_arena.countNodes(),
        );
        var has_seen_colon = false;
        var bracket_depth: u32 = 0;
        var eq_pos: ?usize = null;
        var cur = start_idx + 1;
        while (cur < end_idx) : (cur += 1) {
            const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.subtree_size <= 1 and !sub.token.isNone() and sub.token.asInt() < tokens.countTokens()) {
                const kind = tokens.getToken(sub.token).kind;
                switch (kind) {
                    .lparen, .lbracket, .lbrace => bracket_depth += 1,
                    .rparen, .rbracket, .rbrace => {
                        if (bracket_depth > 0) bracket_depth -= 1;
                    },
                    .colon => {
                        if (bracket_depth == 0) has_seen_colon = true;
                    },
                    .eq => {
                        if (has_seen_colon and bracket_depth == 0) {
                            eq_pos = cur;
                            break;
                        }
                    },
                    else => {},
                }
            }
        }
        const found_eq = eq_pos orelse return .none;
        const clamped_end = @min(end_idx, cst_map.len);
        var map_cur = found_eq + 1;
        while (map_cur < clamped_end) : (map_cur += 1) {
            const mapped = cst_map[map_cur];
            if (!mapped.isNone()) return mapped;
        }
        return .none;
    }

    /// Lowers a declared `field: T = DefaultExpr` initializer on `struct_sym` when `S { .. }` omits `field_sym_idx` (`SE-14`).
    fn lowerStructFieldDefaultExpr(
        self: *HirLowerer,
        field_scope: symbol_resolver.ScopeId,
        field_sym_idx: SymbolIndex,
        field_ty: TypeId,
        lit_tok: TokenIndex,
    ) anyerror!HirIndex {
        const field_sym = self.sym_table.getSymbol(field_sym_idx).*;
        const decl_file = field_sym.decl_span.file_id;

        const saved_scope = self.current_scope;
        const saved_mut_ctx = self.is_mut_lvalue_ctx;
        const saved_lex_file = self.active_lexical_file_id;
        self.current_scope = field_scope;
        self.is_mut_lvalue_ctx = false;
        self.active_lexical_file_id = if (!decl_file.isNone()) decl_file else self.store.file_id;
        defer {
            self.current_scope = saved_scope;
            self.is_mut_lvalue_ctx = saved_mut_ctx;
            self.active_lexical_file_id = saved_lex_file;
        }

        if (decl_file.isNone() or decl_file == self.store.file_id) {
            const same_def_ast = extractStructFieldDefaultAst(
                field_sym,
                self.ast_arena,
                self.cst_arena,
                self.tokens,
                self.cst_to_ast,
            );
            if (!same_def_ast.isNone()) {
                const saved_tables = self.side_tables;
                const saved_ov_tok = self.interp_override_token;
                if (self.interp_override_token.isNone()) self.interp_override_token = lit_tok;
                defer {
                    self.side_tables = saved_tables;
                    self.interp_override_token = saved_ov_tok;
                }
                if (self.eval_hook.compiler_db) |db| {
                    if (try db.getExternalFileSyntaxView(self.store.file_id)) |same_view| {
                        if (same_view.file_side_tables) |file_st| self.side_tables = file_st;
                    }
                }
                return self.lowerExpr(same_def_ast, field_ty);
            }
            return self.emitDefaultInitValue(field_ty, lit_tok);
        }

        const db = self.eval_hook.compiler_db orelse return self.emitDefaultInitValue(field_ty, lit_tok);
        const ext_view = (try db.getExternalFileSyntaxView(decl_file)) orelse
            return self.emitDefaultInitValue(field_ty, lit_tok);

        const ext_extra_ends = try syntax_arenas.computeAstNodeExtraEnds(self.allocator, ext_view.ast_arena);
        defer if (ext_extra_ends.len > 0) self.allocator.free(ext_extra_ends);
        const ext_cst_map = try syntax_arenas.computeCstToAstMap(
            self.allocator,
            ext_view.cst_arena.countNodes(),
            ext_view.ast_arena,
        );
        defer if (ext_cst_map.len > 0) self.allocator.free(ext_cst_map);

        const ext_def_ast = extractStructFieldDefaultAst(
            field_sym,
            ext_view.ast_arena,
            ext_view.cst_arena,
            ext_view.tokens,
            ext_cst_map,
        );
        if (ext_def_ast.isNone()) return self.emitDefaultInitValue(field_ty, lit_tok);

        const outer_span = if (self.interp_override_span) |existing_span|
            existing_span
        else if (!lit_tok.isNone() and lit_tok.asInt() < self.tokens.countTokens())
            self.tokens.getTokenSpan(self.store.file_id, lit_tok)
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
        const saved_ov_src = self.interp_override_source;

        self.source = ext_view.source;
        self.tokens = ext_view.tokens;
        self.cst_arena = ext_view.cst_arena;
        self.ast_arena = ext_view.ast_arena;
        self.side_tables = ext_view.file_side_tables;
        self.node_extra_end = ext_extra_ends;
        self.cst_to_ast = ext_cst_map;
        self.interp_override_token = if (!saved_ov_tok.isNone()) saved_ov_tok else lit_tok;
        self.interp_override_span = outer_span;
        if (self.interp_override_source == null) self.interp_override_source = saved_source;
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
            self.interp_override_source = saved_ov_src;
        }
        return self.lowerExpr(ext_def_ast, field_ty);
    }

    /// Lowers prefix unary operations (`comptime`, `own`, `yield`, `-`, `not`, `~`, `&`, `&mut`, `&out`, `&raw [mut]`).
    fn lowerUnaryExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node) return self.emitErrorHole(tok, expr_id, target_ty);
        const inner_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const op_kind = self.tokens.getToken(tok).kind;
        const op_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);

        // [0] `own expr` explicit ownership-transfer prefix (`ADR-22B`, including `own async { … }`):
        if (op_kind == .kw_own or (op_kind == .ident and std.mem.eql(u8, op_lex, "own"))) {
            if (self.ast_arena.getNode(inner_id).tag == .block and
                self.hasKeywordInCst(self.ast_arena.getCstOrigin(inner_id), .kw_async))
            {
                return self.lowerAsyncBlockExprWithMode(inner_id, target_ty, true);
            }
            return self.lowerExpr(inner_id, target_ty);
        }

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
        if (op_kind == .ident and std.mem.eql(u8, op_lex, "yield")) {
            var yielded_hir = try self.lowerPlaceWithMutCtx(
                inner_id,
                self.current_fn_ret_ty,
                self.is_in_subscript_inout_arm,
            );
            if (!yielded_hir.isNone()) {
                const yn = self.store.getNode(yielded_hir);
                if (yn.tag == .hir_unary_op) {
                    const u_op: HirUnaryOp = @fromBackingInt(@as(u8, @truncate(yn.data.lhs)));
                    if (u_op == .addr_of or u_op == .addr_of_mut or
                        u_op == .addr_of_raw or u_op == .addr_of_raw_mut)
                    {
                        yielded_hir = HirIndex.fromInt(yn.data.rhs);
                    }
                }
            }
            return self.emitNode(.{
                .tag = .hir_yield,
                .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
                .type_id = self.store.getNode(yielded_hir).type_id,
                .origin_token = tok,
                .data = .{ .lhs = yielded_hir.asInt(), .rhs = @intFromBool(self.is_in_subscript_inout_arm) },
            }, expr_id);
        }

        // [3] Fold negated integer literal (`-128_i8`, `-170141183460469231731687303715884105728_i128`) directly:
        if (op_kind == .minus and self.ast_arena.getNode(inner_id).tag == .int_lit) {
            const inner_tok = self.ast_arena.getNode(inner_id).main_token;
            const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, inner_tok);
            const neg_val = extractNegatedIntValue(lexeme) orelse 0;
            const int_ty = if (!target_ty.isError()) target_ty else .i32_ty;
            return self.emitConstVal(.{ .int_val = neg_val }, int_ty, tok, expr_id, false);
        }

        const expr_cst = self.ast_arena.getCstOrigin(expr_id);
        const has_raw = self.hasModifierInCst(expr_cst, .ident, "raw");
        const has_mut = self.hasKeywordInCst(expr_cst, .kw_mut);
        const has_out = self.hasModifierInCst(expr_cst, .ident, "out");
        const is_mut_borrow_op = op_kind == .amp and
            (has_mut or has_out or (!has_raw and self.pool.getTag(target_ty) == .mut_ref_ty));
        const inner_hir = try self.lowerPlaceWithMutCtx(inner_id, .err_ty, is_mut_borrow_op);
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
            .tilde => return self.emitNode(.{
                .tag = .hir_unary_op,
                .flags = .{ .category = .rvalue },
                .type_id = if (!target_ty.isError()) target_ty else inner_node.type_id,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(HirUnaryOp.bit_not), .rhs = inner_hir.asInt() },
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
            .amp => {
                if (has_raw) {
                    const raw_ptr_ty = if (!target_ty.isError())
                        target_ty
                    else
                        try self.pool.internRawPtr(inner_node.type_id, has_mut);
                    const raw_op: HirUnaryOp = if (has_mut) .addr_of_raw_mut else .addr_of_raw;
                    return self.emitNode(.{
                        .tag = .hir_unary_op,
                        .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
                        .type_id = raw_ptr_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = @backingInt(raw_op), .rhs = inner_hir.asInt() },
                    }, expr_id);
                }
                const ref_ty = if (!target_ty.isError())
                    target_ty
                else if (has_out)
                    try self.pool.internOutRef(inner_node.type_id)
                else
                    try self.pool.internRef(inner_node.type_id, is_mut_borrow_op);
                return self.emitNode(.{
                    .tag = .hir_unary_op,
                    .flags = .{ .category = .rvalue },
                    .type_id = ref_ty,
                    .origin_token = tok,
                    .data = .{
                        .lhs = @backingInt(if (is_mut_borrow_op) HirUnaryOp.addr_of_mut else HirUnaryOp.addr_of),
                        .rhs = inner_hir.asInt(),
                    },
                }, expr_id);
            },
            .star => return self.emitPostfixOrPrefixDeref(expr_id, inner_hir, target_ty, tok),
            else => return inner_hir,
        }
    }

    /// Lowers postfix `ptr.*` (`AstTag.deref_expr`) into `hir_unary_op(.deref)` (`ADR-22A`, `ADR-22D`).
    fn lowerPostfixDerefExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node) return self.emitErrorHole(tok, expr_id, target_ty);
        const inner_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const inner_hir = try self.lowerPlaceWithMutCtx(inner_id, .err_ty, false);
        return self.emitPostfixOrPrefixDeref(expr_id, inner_hir, target_ty, tok);
    }

    /// Emits `hir_unary_op(.deref)` over `inner_hir`, flagging `is_unsafe = true` when dereferencing `*T` / `*mut T`.
    fn emitPostfixOrPrefixDeref(
        self: *HirLowerer,
        expr_id: NodeIndex,
        inner_hir: HirIndex,
        target_ty: TypeId,
        tok: TokenIndex,
    ) !HirIndex {
        const inner_node = self.store.getNode(inner_hir);
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
    }

    /// Summarizes whether a generic / Type-Group variable bound admits integer-like or float members (`SE-09`).
    const TypeVarNumericInfo = struct {
        /// `true` if the bound admits at least one integer, `bool`, `char`, `bit_field`, or backed `enum` member.
        has_int: bool = false,
        /// `true` if the bound admits at least one floating-point (`f32` / `f64`) member.
        has_float: bool = false,
    };

    /// Inspects a `.type_param`, `.bind_once_group_var`, or `.bind_many_any_var` bound for numeric cast lowering.
    fn classifyTypeVarNumericInfo(self: *const HirLowerer, ty: TypeId) TypeVarNumericInfo {
        if (ty.isError()) return .{};
        const node = self.pool.getNode(ty);
        if (node.tag != .type_param and node.tag != .bind_once_group_var and node.tag != .bind_many_any_var) {
            return .{};
        }
        const grp_ty = TypeId.fromInt(node.lhs);
        if (grp_ty.isError()) return .{};
        if (grp_ty.isBuiltinGroup()) {
            const mask = type_system.TypeGroupMask.forBuiltinGroup(grp_ty);
            const int_like_mask = type_system.TypeGroupMask.INTEGER |
                TypeId.bool_ty.primitiveBit() |
                TypeId.char_ty.primitiveBit();
            return .{
                .has_int = (mask & int_like_mask) != 0,
                .has_float = (mask & type_system.TypeGroupMask.FLOAT) != 0,
            };
        }
        if (self.pool.getTag(grp_ty) == .user_group) {
            if (self.pool.getUserGroupView(grp_ty)) |view| {
                const mask = view.prim_mask | view.tilde_prim_mask;
                const int_like_mask = type_system.TypeGroupMask.INTEGER |
                    TypeId.bool_ty.primitiveBit() |
                    TypeId.char_ty.primitiveBit();
                var info = TypeVarNumericInfo{
                    .has_int = (mask & int_like_mask) != 0,
                    .has_float = (mask & type_system.TypeGroupMask.FLOAT) != 0,
                };
                const member_lists = [2][]const u32{ view.exact_members, view.tilde_members };
                for (member_lists) |mem_list| {
                    for (mem_list) |raw_mem| {
                        const unwrapped_mem = self.pool.unwrapUnderlyingType(TypeId.fromInt(raw_mem));
                        if (unwrapped_mem.isError()) continue;
                        const mem_tag = self.pool.getTag(unwrapped_mem);
                        if (unwrapped_mem.isIntegerPrimitive() or unwrapped_mem == .bool_ty or
                            unwrapped_mem == .char_ty or mem_tag == .bit_field_ty or
                            self.pool.getEnumBackingIntType(unwrapped_mem) != null)
                        {
                            info.has_int = true;
                        } else if (unwrapped_mem.isFloatPrimitive()) {
                            info.has_float = true;
                        }
                    }
                }
                return info;
            }
        }
        return .{};
    }

    /// Lowers `src as TargetType` into `hir_cast` with exact `HirCastKind` (`ADR-22C`).
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
        const src_var_num = self.classifyTypeVarNumericInfo(src_ty);
        const dst_var_num = self.classifyTypeVarNumericInfo(dst_ty);
        const is_src_scalar_bf = src_tag == .bit_field_ty and
            self.pool.getTag(self.pool.unwrapUnderlyingType(TypeId.fromInt(
                self.pool.getNode(self.pool.unwrapUnderlyingType(src_ty)).lhs,
            ))) != .array_ty;
        const is_dst_scalar_bf = dst_tag == .bit_field_ty and
            self.pool.getTag(self.pool.unwrapUnderlyingType(TypeId.fromInt(
                self.pool.getNode(self.pool.unwrapUnderlyingType(dst_ty)).lhs,
            ))) != .array_ty;
        const is_src_int_like = src_ty.isIntegerPrimitive() or src_ty == .bool_ty or src_ty == .char_ty or
            is_src_scalar_bf or self.pool.getEnumBackingIntType(src_ty) != null or src_var_num.has_int;
        const is_dst_int_like = dst_ty.isIntegerPrimitive() or dst_ty == .char_ty or
            is_dst_scalar_bf or self.pool.getEnumBackingIntType(dst_ty) != null or dst_var_num.has_int;
        const is_src_float_like = src_ty.isFloatPrimitive() or src_var_num.has_float;
        const is_dst_float_like = dst_ty.isFloatPrimitive() or dst_var_num.has_float;

        const cast_kind: HirCastKind = if (src_tag == .distinct_ty and dst_tag != .distinct_ty)
            .distinct_unwrap
        else if (src_tag != .distinct_ty and dst_tag == .distinct_ty)
            .distinct_wrap
        else if (is_src_int_like and is_dst_int_like)
            .int_to_int
        else if (is_src_int_like and is_dst_float_like)
            .int_to_float
        else if (is_src_float_like and is_dst_int_like)
            .float_to_int
        else if (is_src_float_like and is_dst_float_like)
            .float_to_float
        else if (src_tag == .raw_ptr_ty or dst_tag == .raw_ptr_ty or
            src_tag == .ref_ty or src_tag == .mut_ref_ty or
            (src_tag == .closure_ty and dst_tag == .fn_ty))
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

    /// Classification of a `.` receiver expression under `DR-21` Unified `.` resolution.
    const StaticDotKind = enum(u8) {
        /// Runtime value expression (`instance.field` / `instance.method()`).
        none = 0,
        /// Module namespace (`cx.mem`, `pkg.sub`).
        module_ns = 1,
        /// Nominal, primitive, or built-in sum type namespace (`Point`, `Option`, `u32`).
        type_ns = 2,
    };

    /// Unwraps `.use_alias_sym` hops up to a bounded depth (`16`) to reach the defining `SymbolIndex`.
    fn unwrapAliasSymbolIdx(self: *const HirLowerer, sym_idx: SymbolIndex) SymbolIndex {
        var cur = sym_idx;
        var hops: u8 = 0;
        while (!cur.isNone() and cur.asInt() < self.sym_table.countSymbols() and hops < 16) : (hops += 1) {
            const sym = self.sym_table.getSymbol(cur).*;
            if (sym.kind != .use_alias_sym or sym.target_symbol.isNone()) break;
            cur = sym.target_symbol;
        }
        return cur;
    }

    /// Resolved static module or nominal type namespace target for Unified `.` path expressions (`P2-3`).
    const StaticNamespaceTarget = struct {
        /// Whether the target denotes a module/package namespace or nominal type namespace.
        kind: StaticDotKind,
        /// Member `ScopeId` of the target module/package/type (`.none` for built-in `Option`/`Result`/primitives).
        scope_id: ScopeId,
    };

    /// Classifies `sym_idx` (after unwrapping `use` aliases) into a `StaticNamespaceTarget` if it is a module or type.
    fn classifyStaticNamespaceSymbol(self: *const HirLowerer, sym_idx: SymbolIndex) ?StaticNamespaceTarget {
        if (sym_idx.isNone()) return null;
        const resolved_idx = self.unwrapAliasSymbolIdx(sym_idx);
        const sym = self.sym_table.getSymbol(resolved_idx).*;
        if (!sym.target_scope.isNone() and
            (sym.kind == .module_sym or sym.kind == .const_sym or
                sym.kind == .local_let_sym or sym.kind == .local_var_sym))
        {
            return .{ .kind = .module_ns, .scope_id = sym.target_scope };
        }
        if (self.symbol_to_local.contains(resolved_idx.asInt())) return null;
        return switch (sym.kind) {
            .module_sym => .{ .kind = .module_ns, .scope_id = sym.target_scope },
            .struct_sym,
            .enum_sym,
            .union_sym,
            .bit_field_sym,
            .trait_sym,
            .type_alias_sym,
            .distinct_type_sym,
            .refined_type_sym,
            .type_param_sym,
            => .{ .kind = .type_ns, .scope_id = sym.target_scope },
            else => null,
        };
    }

    /// Resolves `recv_id` up to `depth < 16` into a `StaticNamespaceTarget` supporting `pkg.`, `dep_alias.`, and chained paths.
    fn resolveStaticNamespaceAst(self: *const HirLowerer, recv_id: NodeIndex, depth: u8) ?StaticNamespaceTarget {
        if (depth >= 16 or recv_id.isNone() or recv_id.asInt() >= self.ast_arena.countNodes()) return null;
        const recv_node = self.ast_arena.getNode(recv_id);
        if (recv_node.tag == .index_expr and recv_node.lhs.tag == .node) {
            return self.resolveStaticNamespaceAst(NodeIndex.fromInt(recv_node.lhs.payload), depth + 1);
        }

        const recorded_sym = self.nodeSymbol(recv_id);
        if (!recorded_sym.isNone()) {
            if (self.classifyStaticNamespaceSymbol(recorded_sym)) |target| return target;
        }

        if (recv_node.tag == .ident_expr and !recv_node.main_token.isNone()) {
            const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, recv_node.main_token);
            // [1] `pkg` always resolves to the caller package's root module scope (`src/root.cx`) BEFORE `lookupLexical`:
            if (std.mem.eql(u8, lexeme, "pkg")) {
                const pkg_scope = self.sym_table.resolveCallerPackageRootScope(
                    self.active_lexical_file_id,
                    self.current_scope,
                );
                if (!pkg_scope.isNone()) {
                    return .{ .kind = .module_ns, .scope_id = pkg_scope };
                }
            }
            if (self.interner.lookup(lexeme)) |name_id| {
                if (self.active_name_to_local.contains(name_id.asInt()) or
                    self.active_comptime_vals.contains(name_id.asInt()) or
                    self.active_zip_bindings.contains(name_id.asInt()))
                {
                    return null;
                }
                if (std.mem.eql(u8, lexeme, "core") and
                    !self.sym_table.isCoreAllowedForFile(self.active_lexical_file_id))
                {
                    return null;
                }
                switch (self.sym_table.lookupLexical(self.current_scope, name_id, NamespaceMask.ALL)) {
                    .found => |found_idx| {
                        if (self.classifyStaticNamespaceSymbol(found_idx)) |target| return target;
                    },
                    else => {},
                }
                if (self.sym_table.lookupExternalPackageScope(self.active_lexical_file_id, name_id)) |dep_scope| {
                    if (!dep_scope.isNone()) {
                        return .{ .kind = .module_ns, .scope_id = dep_scope };
                    }
                }
            }
            if (std.mem.eql(u8, lexeme, "Option") or std.mem.eql(u8, lexeme, "Result") or
                self.resolveBuiltinPrimitiveLexeme(lexeme) != null)
            {
                return .{ .kind = .type_ns, .scope_id = .none };
            }
            return null;
        }

        if (recv_node.tag == .field_access and recv_node.lhs.tag == .node and recv_node.rhs.tag == .token) {
            const base_id = NodeIndex.fromInt(recv_node.lhs.payload);
            const field_lex = symbol_resolver.extractTokenSlice(
                self.source,
                self.tokens,
                TokenIndex.fromInt(recv_node.rhs.payload),
            );
            if (self.resolveStaticNamespaceAst(base_id, depth + 1)) |base_ns| {
                if (!base_ns.scope_id.isNone()) {
                    if (self.interner.lookup(field_lex)) |member_id| {
                        const member_sym = self.sym_table.lookupInScopeDirect(
                            base_ns.scope_id,
                            member_id,
                            NamespaceMask.ALL,
                        );
                        if (self.classifyStaticNamespaceSymbol(member_sym)) |target| return target;
                    }
                    if (base_ns.scope_id == self.sym_table.cx_root_scope and
                        (std.mem.eql(u8, field_lex, "async") or std.mem.eql(u8, field_lex, "ffi")))
                    {
                        return .{ .kind = .module_ns, .scope_id = .none };
                    }
                }
            }
        }
        return null;
    }

    /// Classifies whether `recv_id` denotes a static module or type namespace rather than a runtime value.
    fn resolveStaticDotTargetAst(self: *const HirLowerer, recv_id: NodeIndex) StaticDotKind {
        if (self.resolveStaticNamespaceAst(recv_id, 0)) |target| return target.kind;
        return .none;
    }

    /// Maps an unshadowed primitive type identifier lexeme (`u32`, `f64`, etc.) to its canonical `TypeId`.
    fn resolveBuiltinPrimitiveLexeme(self: *const HirLowerer, lexeme: []const u8) ?TypeId {
        if (self.interner.lookup(lexeme)) |name_id| {
            if (self.active_name_to_local.contains(name_id.asInt()) or
                self.active_comptime_vals.contains(name_id.asInt()))
            {
                return null;
            }
        }
        if (symbol_resolver.BUILTIN_TYPE_AND_GROUP_MAP.get(lexeme)) |builtin_ty| {
            if (!builtin_ty.isBuiltinGroup() and builtin_ty != .never_ty and builtin_ty != .unit_ty) {
                return builtin_ty;
            }
        }
        return null;
    }

    /// Resolves `recv_id` when it denotes a primitive type or alias/distinct/refined wrapper (`u32`, `f64`, etc.).
    fn resolveBuiltinPrimitiveAst(self: *const HirLowerer, recv_id: NodeIndex) ?TypeId {
        if (recv_id.isNone() or recv_id.asInt() >= self.ast_arena.countNodes()) return null;
        const recv_node = self.ast_arena.getNode(recv_id);
        if (recv_node.tag == .ident_expr and !recv_node.main_token.isNone()) {
            const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, recv_node.main_token);
            if (self.resolveBuiltinPrimitiveLexeme(lexeme)) |prim_ty| return prim_ty;
        }
        var sym_idx = self.nodeSymbol(recv_id);
        if (sym_idx.isNone() and recv_node.tag == .ident_expr and !recv_node.main_token.isNone()) {
            const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, recv_node.main_token);
            if (self.interner.lookup(lexeme)) |name_id| {
                if (!self.active_name_to_local.contains(name_id.asInt()) and
                    !self.active_comptime_vals.contains(name_id.asInt()))
                {
                    switch (self.sym_table.lookupLexical(self.current_scope, name_id, NamespaceMask.ALL)) {
                        .found => |found_idx| sym_idx = found_idx,
                        else => {},
                    }
                }
            }
        }
        if (!sym_idx.isNone() and !self.symbol_to_local.contains(sym_idx.asInt())) {
            const sym = self.sym_table.getSymbol(sym_idx);
            switch (sym.kind) {
                .type_alias_sym, .distinct_type_sym, .refined_type_sym, .type_param_sym => {
                    const concrete_ty = self.concreteType(sym.type_id);
                    const base_prim = self.pool.unwrapRefinementBase(self.pool.unwrapUnderlyingType(concrete_ty));
                    if (base_prim.isIntegerPrimitive() or base_prim.isFloatPrimitive()) return concrete_ty;
                },
                else => {},
            }
        }
        return null;
    }

    /// Evaluates built-in associated constants on integer and floating-point primitives (`u32.MAX`, `f64.PI`, etc.).
    fn evalPrimitiveAssocConst(
        self: *const HirLowerer,
        raw_prim_ty: TypeId,
        member_name: []const u8,
    ) ?struct { val: ComptimeValue, ty: TypeId } {
        const prim_ty = self.pool.unwrapRefinementBase(self.pool.unwrapUnderlyingType(raw_prim_ty));
        if (prim_ty.isIntegerPrimitive()) {
            const int_assoc = type_system.INT_ASSOC_CONST_MAP.get(member_name) orelse return null;
            const ptr_bits: u32 = @as(u32, self.store.target_layout.ptr_byte_size) * 8;
            const bits: u32 = switch (prim_ty) {
                .i8_ty, .u8_ty => 8,
                .i16_ty, .u16_ty => 16,
                .i32_ty, .u32_ty => 32,
                .i64_ty, .u64_ty => 64,
                .i128_ty, .u128_ty => 128,
                .isize_ty, .usize_ty => ptr_bits,
                else => return null,
            };
            const is_signed = prim_ty.isSignedIntPrimitive();
            return switch (int_assoc) {
                .bits => .{ .val = .{ .int_val = @as(i128, bits) }, .ty = .u32_ty },
                .min => blk_min: {
                    if (!is_signed) break :blk_min .{ .val = .{ .int_val = 0 }, .ty = prim_ty };
                    const min_val: i128 = if (bits >= 128)
                        std.math.minInt(i128)
                    else
                        -(@as(i128, 1) << @intCast(bits - 1));
                    break :blk_min .{ .val = .{ .int_val = min_val }, .ty = prim_ty };
                },
                .max => blk_max: {
                    if (is_signed) {
                        const max_signed: i128 = if (bits >= 128)
                            std.math.maxInt(i128)
                        else
                            (@as(i128, 1) << @intCast(bits - 1)) - 1;
                        break :blk_max .{ .val = .{ .int_val = max_signed }, .ty = prim_ty };
                    }
                    const max_unsigned: i128 = if (bits >= 128)
                        @bitCast(@as(u128, std.math.maxInt(u128)))
                    else
                        (@as(i128, 1) << @intCast(bits)) - 1;
                    break :blk_max .{ .val = .{ .int_val = max_unsigned }, .ty = prim_ty };
                },
            };
        } else if (prim_ty.isFloatPrimitive()) {
            const float_assoc = type_system.FLOAT_ASSOC_CONST_MAP.get(member_name) orelse return null;
            return switch (float_assoc) {
                .bits => .{
                    .val = .{
                        .int_val = switch (prim_ty) {
                            .f32_ty => 32,
                            .f64_ty => 64,
                            else => 64,
                        },
                    },
                    .ty = .u32_ty,
                },
                .infinity => .{ .val = .{ .float_val = std.math.inf(f64) }, .ty = prim_ty },
                .neg_infinity => .{ .val = .{ .float_val = -std.math.inf(f64) }, .ty = prim_ty },
                .nan => .{ .val = .{ .float_val = std.math.nan(f64) }, .ty = prim_ty },
                .pi => .{
                    .val = .{
                        .float_val = switch (prim_ty) {
                            .f32_ty => @floatCast(@as(f32, std.math.pi)),
                            else => std.math.pi,
                        },
                    },
                    .ty = prim_ty,
                },
                .tau => .{
                    .val = .{
                        .float_val = switch (prim_ty) {
                            .f32_ty => @floatCast(@as(f32, std.math.tau)),
                            else => std.math.tau,
                        },
                    },
                    .ty = prim_ty,
                },
                .epsilon => .{
                    .val = .{
                        .float_val = switch (prim_ty) {
                            .f32_ty => @floatCast(std.math.floatEps(f32)),
                            else => std.math.floatEps(f64),
                        },
                    },
                    .ty = prim_ty,
                },
                .min => .{
                    .val = .{
                        .float_val = switch (prim_ty) {
                            .f32_ty => -@as(f64, @floatCast(std.math.floatMax(f32))),
                            else => -std.math.floatMax(f64),
                        },
                    },
                    .ty = prim_ty,
                },
                .max => .{
                    .val = .{
                        .float_val = switch (prim_ty) {
                            .f32_ty => @floatCast(std.math.floatMax(f32)),
                            else => std.math.floatMax(f64),
                        },
                    },
                    .ty = prim_ty,
                },
            };
        }
        return null;
    }

    /// Resolves a member symbol inside a static module/type AST receiver when `side_tables` are absent.
    fn lookupStaticMemberSymbolFallback(
        self: *const HirLowerer,
        recv_id: NodeIndex,
        member_name: []const u8,
    ) SymbolIndex {
        const member_id = self.interner.lookup(member_name) orelse return .none;
        if (self.resolveStaticNamespaceAst(recv_id, 0)) |target_ns| {
            if (!target_ns.scope_id.isNone()) {
                return self.sym_table.lookupInScopeDirect(target_ns.scope_id, member_id, NamespaceMask.ALL);
            }
        }
        return .none;
    }

    /// Desugars `lhs |> f(a_1, …, a_k)`, `lhs |> mod.f(a_1, …, a_k)`, and `lhs |> recv.m(a_1, …, a_k)` (`DR-13` §2.2 Rule 1).
    fn lowerPipeExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .node) {
            return self.emitErrorHole(tok, expr_id, target_ty);
        }
        const lhs_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const rhs_id = NodeIndex.fromInt(ast_node.rhs.payload);
        const rhs_node = self.ast_arena.getNode(rhs_id);

        // [1] `.method_call` pipeline (`lhs |> recv.method(…)` OR static `lhs |> mod.func(…)` under Unified `.`):
        if (rhs_node.tag == .method_call and rhs_node.lhs.tag == .node) {
            const recv_id = NodeIndex.fromInt(rhs_node.lhs.payload);
            const raw_items = self.getAstExtraSlice(rhs_id, true);
            if (raw_items.len == 0) return self.emitErrorHole(tok, expr_id, target_ty);
            const member_tok = TokenIndex.fromInt(raw_items[0]);
            const member_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, member_tok);
            const is_static_recv = self.resolveStaticDotTargetAst(recv_id) != .none;

            var type_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
            defer type_arg_nodes.deinit(self.allocator);
            var pipe_val_args: std.ArrayListUnmanaged(NodeIndex) = .empty;
            defer pipe_val_args.deinit(self.allocator);
            try pipe_val_args.append(self.allocator, lhs_id);
            for (raw_items[1..]) |raw_item| {
                const item_id = NodeIndex.fromInt(raw_item);
                if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
                if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) {
                    try type_arg_nodes.append(self.allocator, item_id);
                } else {
                    try pipe_val_args.append(self.allocator, item_id);
                }
            }

            const expr_method_sym = self.nodeSymbol(expr_id);
            var method_sym_idx = if (!expr_method_sym.isNone()) expr_method_sym else self.nodeSymbol(rhs_id);
            if (method_sym_idx.isNone()) {
                if (is_static_recv) {
                    method_sym_idx = self.lookupStaticMemberSymbolFallback(recv_id, member_name);
                } else {
                    const recv_ty = self.unwrapRefType(self.nodeType(recv_id));
                    if (try self.lookupMethodOnType(recv_ty, member_name)) |found_m| {
                        method_sym_idx = found_m;
                    }
                }
            }
            if (method_sym_idx.isNone()) return self.emitErrorHole(tok, expr_id, target_ty);

            const method_sym = self.sym_table.getSymbol(method_sym_idx).*;
            const sig_view = self.pool.getFnSignatureView(method_sym.type_id);
            const has_self_receiver = !is_static_recv;

            var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
            defer seq_stmts.deinit(self.allocator);
            var ordered_args: std.ArrayListUnmanaged(HirIndex) = .empty;
            defer ordered_args.deinit(self.allocator);

            try self.lowerMappedDirectArgs(
                expr_id,
                method_sym_idx,
                method_sym.type_id,
                has_self_receiver,
                pipe_val_args.items,
                tok,
                &seq_stmts,
                &ordered_args,
            );

            var wrapped_args: std.ArrayListUnmanaged(u32) = .empty;
            defer wrapped_args.deinit(self.allocator);
            if (has_self_receiver) {
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
                try wrapped_args.append(
                    self.allocator,
                    (try self.wrapArgProjection(adjusted_recv, self_mode, tok)).asInt(),
                );
            }
            const param_offset: usize = if (has_self_receiver) 1 else 0;
            for (ordered_args.items, 0..) |arg_hir, i| {
                const param_idx = param_offset + i;
                var adj_arg = arg_hir;
                const param_mode: ParamMode = if (sig_view) |sv|
                    (if (param_idx < sv.paramCount()) sv.getParamMode(param_idx) else .let_mode)
                else
                    .let_mode;
                if (sig_view) |sv| {
                    if (param_idx < sv.paramCount()) {
                        adj_arg = try self.adjustReceiverForParam(adj_arg, sv.getParamType(param_idx), tok);
                    }
                }
                try wrapped_args.append(
                    self.allocator,
                    (try self.wrapArgProjection(adj_arg, param_mode, tok)).asInt(),
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
            const is_sub_pipe = self.isCalleeSubscript(callee_hir);
            const call_hir = try self.emitNode(.{
                .tag = if (is_sub_pipe) .hir_subscript_call else .hir_call,
                .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                .type_id = ret_ty,
                .origin_token = tok,
                .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
            }, expr_id);
            if (!is_sub_pipe) {
                const inst_ast = if (self.side_tables != null and
                    self.side_tables.?.getCallInstantiation(expr_id) != null) expr_id else rhs_id;
                try self.recordCallTypeArgs(inst_ast, call_hir, type_arg_nodes.items);
            }
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

        var pipe_type_args: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer pipe_type_args.deinit(self.allocator);
        var pipe_val_args: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer pipe_val_args.deinit(self.allocator);
        try pipe_val_args.append(self.allocator, lhs_id);
        for (raw_call_items) |raw_item| {
            const item_id = NodeIndex.fromInt(raw_item);
            if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
            if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) {
                try pipe_type_args.append(self.allocator, item_id);
            } else {
                try pipe_val_args.append(self.allocator, item_id);
            }
        }
        if (self.ast_arena.getNode(callee_ast_id).tag == .generic_call and
            self.ast_arena.getNode(callee_ast_id).lhs.tag == .node)
        {
            const inner_gen_id = callee_ast_id;
            callee_ast_id = NodeIndex.fromInt(self.ast_arena.getNode(inner_gen_id).lhs.payload);
            for (self.getAstExtraSlice(inner_gen_id, true)) |raw_item| {
                const item_id = NodeIndex.fromInt(raw_item);
                if (item_id.asInt() < self.ast_arena.countNodes()) {
                    try pipe_type_args.append(self.allocator, item_id);
                }
            }
        }

        const expr_sym_idx = self.nodeSymbol(expr_id);
        const rhs_sym_idx = if (!expr_sym_idx.isNone()) expr_sym_idx else self.nodeSymbol(rhs_id);
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
        var lowered_call_args: std.ArrayListUnmanaged(HirIndex) = .empty;
        defer lowered_call_args.deinit(self.allocator);

        if (is_direct_sym) {
            try self.lowerMappedDirectArgs(
                expr_id,
                resolved_sym_idx,
                pre_callee_ty,
                false,
                pipe_val_args.items,
                tok,
                &seq_stmts,
                &lowered_call_args,
            );
        } else {
            for (pipe_val_args.items, 0..) |val_item_id, i| {
                const param_ty: TypeId = if (sig_view) |sv|
                    (if (i < sv.paramCount()) sv.getParamType(i) else .err_ty)
                else
                    .err_ty;
                const param_mode_pre: ParamMode = if (sig_view) |sv|
                    (if (i < sv.paramCount()) sv.getParamMode(i) else .let_mode)
                else
                    .let_mode;
                var arg_hir = try self.lowerExpr(self.unwrapCallArgAst(val_item_id), param_ty);
                arg_hir = try self.applyCVariadicPromotionIfNeeded(arg_hir, sig_view, i, tok);
                if (param_mode_pre != .inout_mode and param_mode_pre != .set_mode) {
                    const tmp_slot = try self.allocTempLocal(self.store.getNode(arg_hir).type_id, tok, false);
                    try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(tmp_slot, arg_hir, tok)).asInt());
                    arg_hir = try self.emitVarRef(tmp_slot, tok, .none);
                }
                try lowered_call_args.append(self.allocator, arg_hir);
            }
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

        for (lowered_call_args.items, 0..) |raw_arg_hir, i| {
            var adj_arg = raw_arg_hir;
            const param_mode: ParamMode = if (sig_view) |sv|
                (if (i < sv.paramCount()) sv.getParamMode(i) else .let_mode)
            else
                .let_mode;
            if (sig_view) |sv| {
                if (i < sv.paramCount()) {
                    adj_arg = try self.adjustReceiverForParam(adj_arg, sv.getParamType(i), tok);
                } else if (!is_direct_sym) {
                    adj_arg = try self.applyCVariadicPromotionIfNeeded(adj_arg, sig_view, i, tok);
                }
            }
            try wrapped_args.append(self.allocator, (try self.wrapArgProjection(adj_arg, param_mode, tok)).asInt());
        }

        const ret_ty = if (!target_ty.isError())
            target_ty
        else if (sig_view) |sv|
            self.concreteType(sv.ret_ty)
        else
            .unit_ty;

        const extra_idx = try self.store.appendLenPrefixedExtra(wrapped_args.items);
        const is_sub_call = self.isCalleeSubscript(callee_hir);
        const call_hir = try self.emitNode(.{
            .tag = if (is_sub_call) .hir_subscript_call else .hir_call,
            .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
            .type_id = ret_ty,
            .origin_token = tok,
            .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
        }, expr_id);
        if (!is_sub_call) {
            const inst_ast = if (self.side_tables != null and
                self.side_tables.?.getCallInstantiation(expr_id) != null) expr_id else rhs_id;
            try self.recordCallTypeArgs(inst_ast, call_hir, pipe_type_args.items);
        }
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
                } else if (tables.getTryFromVariant(expr_id)) |variant_ord| {
                    // `SE-10` `@derive(From)` zero-overhead enum variant wrap:
                    const unwrapped_outer_err = self.pool.unwrapUnderlyingType(outer_err_ty);
                    const wrap_extra = try self.store.appendLenPrefixedExtra(&[1]u32{converted_err.asInt()});
                    converted_err = try self.emitNode(.{
                        .tag = .hir_construct,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = unwrapped_outer_err,
                        .origin_token = tok,
                        .data = .{
                            .lhs = @as(u32, @backingInt(HirConstructKind.enum_variant)) |
                                (@as(u32, variant_ord) << 8),
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
                    has_converted_err = true;
                }
            }
            if (!has_converted_err and err_ty != outer_err_ty) {
                const unwrapped_outer_err = self.pool.unwrapUnderlyingType(outer_err_ty);
                if (self.pool.getDerivedFromVariant(err_ty, unwrapped_outer_err)) |derived_ord| {
                    const wrap_extra = try self.store.appendLenPrefixedExtra(&[1]u32{converted_err.asInt()});
                    converted_err = try self.emitNode(.{
                        .tag = .hir_construct,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = unwrapped_outer_err,
                        .origin_token = tok,
                        .data = .{
                            .lhs = @as(u32, @backingInt(HirConstructKind.enum_variant)) |
                                (@as(u32, derived_ord) << 8),
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
                    has_converted_err = true;
                }
                const outer_err_node = self.pool.getNode(unwrapped_outer_err);
                if (!has_converted_err and outer_err_node.tag == .enum_ty) {
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

    /// Lowers infix binary operators, `expr orelse fallback`, `expr catch |err| fallback`, and `expr is Pattern`.
    fn lowerBinaryOrCatchExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const op_kind = self.tokens.getToken(tok).kind;

        if (op_kind == .kw_catch) {
            return self.lowerCatchExpr(expr_id, target_ty);
        }
        if (op_kind == .kw_orelse) {
            return self.lowerOrelseExpr(expr_id, target_ty);
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

        // [2] Resolved operator trait call (`side_tables` or nominal `Eq.eq` for `==` / `!=`):
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
        const rhs_expected = if (op_kind == .kw_and or op_kind == .kw_or) .bool_ty else lhs_ty;
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
            .kw_and => .logical_and,
            .kw_or => .logical_or,
            else => .add,
        };

        const res_ty = switch (bin_op) {
            .eq, .ne, .lt, .le, .gt, .ge, .logical_and, .logical_or => .bool_ty,
            else => if (!target_ty.isError()) target_ty else lhs_ty,
        };
        const is_dollar_sub = bin_op == .sub and self.ast_arena.getNode(lhs_id).tag == .dollar_expr;
        const pair = [2]u32{ lhs_hir.asInt(), rhs_hir.asInt() };
        const extra_idx = try self.store.appendExtraSlice(&pair);
        return self.emitNode(.{
            .tag = .hir_binary_op,
            .flags = .{
                .category = .rvalue,
                .is_unsafe = self.is_in_unsafe,
                .is_dollar_sub = is_dollar_sub,
            },
            .type_id = self.concreteType(res_ty),
            .origin_token = tok,
            .data = .{ .lhs = extra_idx, .rhs = @backingInt(bin_op) },
        }, expr_id);
    }

    /// Lowers short-circuiting `opt_expr orelse fallback_expr` into `hir_orelse` (`SE-03`).
    fn lowerOrelseExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        const lhs_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;
        const rhs_id = if (ast_node.rhs.tag == .node) NodeIndex.fromInt(ast_node.rhs.payload) else .none;

        var opt_hir = try self.lowerExpr(lhs_id, .err_ty);
        const raw_opt_ty = self.store.getNode(opt_hir).type_id;
        const opt_ty = self.pool.unwrapUnderlyingType(raw_opt_ty);
        if (opt_ty != raw_opt_ty) {
            opt_hir = try self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = opt_ty,
                .origin_token = tok,
                .data = .{ .lhs = opt_hir.asInt(), .rhs = @backingInt(HirCastKind.distinct_unwrap) },
            }, .none);
        }
        const opt_ty_node = self.pool.getNode(opt_ty);
        const payload_ty = if (opt_ty_node.tag == .optional_ty)
            self.concreteType(TypeId.fromInt(opt_ty_node.lhs))
        else
            .unit_ty;
        const res_ty = self.concreteType(if (!target_ty.isError()) target_ty else payload_ty);

        if (self.is_in_comptime_for) self.comptime_runtime_cond_depth += 1;
        defer if (self.is_in_comptime_for) {
            self.comptime_runtime_cond_depth -= 1;
        };
        const fallback_hir = try self.lowerExpr(rhs_id, res_ty);

        return self.emitNode(.{
            .tag = .hir_orelse,
            .flags = .{
                .category = if (res_ty == .never_ty) .diverging else .rvalue,
                .is_unsafe = self.is_in_unsafe,
            },
            .type_id = res_ty,
            .origin_token = tok,
            .data = .{ .lhs = opt_hir.asInt(), .rhs = fallback_hir.asInt() },
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

    /// Lowers `.field_access` (`s.field`, `tup.0`, `.len`, `#soa` `items[i].x`, `bit_field`, `context.slot`, and Unified `.`).
    fn lowerFieldAccess(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .token) {
            return self.emitErrorHole(tok, expr_id, target_ty);
        }
        const recv_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const member_tok = TokenIndex.fromInt(ast_node.rhs.payload);
        const member_lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, member_tok);
        const recv_ast = self.ast_arena.getNode(recv_id);

        // [0] Implicit `context.<slot>` read (`SE-08`):
        if (recv_ast.tag == .context_expr) {
            if (type_system.ContextFieldLayout.fromFieldName(member_lexeme)) |slot_layout| {
                const recorded_ty = self.concreteType(self.nodeType(expr_id));
                const slot_ty = if (!recorded_ty.isError())
                    recorded_ty
                else if (!target_ty.isError())
                    self.concreteType(target_ty)
                else
                    try self.resolveContextSlotType(slot_layout);
                return self.emitNode(.{
                    .tag = .hir_ctx_get,
                    .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
                    .type_id = slot_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = slot_layout.slot_ordinal, .rhs = 0 },
                }, expr_id);
            }
            return self.emitErrorHole(tok, expr_id, target_ty);
        }

        // [1] Fold compile-time `TypeInfo` / `FieldInfo` / `VariantInfo` / associated constants directly:
        if (try self.tryEvalAstComptime(expr_id, target_ty)) |folded_meta| {
            const res_ty = if (!target_ty.isError()) target_ty else self.inferComptimeValType(folded_meta);
            return self.emitConstVal(folded_meta, res_ty, tok, expr_id, true);
        }

        // [1b] Static Unified `.` (`u32.MAX`, `Option.None`, `Enum.UnitVariant`, `mod.CONST`, `mod.fn`):
        if (self.resolveBuiltinPrimitiveAst(recv_id)) |prim_ty| {
            if (self.evalPrimitiveAssocConst(prim_ty, member_lexeme)) |assoc| {
                const out_ty = if (!target_ty.isError()) target_ty else assoc.ty;
                return self.emitConstVal(assoc.val, out_ty, tok, expr_id, true);
            }
        }
        const static_kind = self.resolveStaticDotTargetAst(recv_id);
        var static_sym_idx = self.nodeSymbol(expr_id);
        if (static_sym_idx.isNone() and static_kind != .none) {
            static_sym_idx = self.lookupStaticMemberSymbolFallback(recv_id, member_lexeme);
        }
        if (!static_sym_idx.isNone()) {
            const resolved_static_idx = self.unwrapAliasSymbolIdx(static_sym_idx);
            const sym = self.sym_table.getSymbol(resolved_static_idx).*;
            if (sym.kind == .const_sym) {
                if (try self.evalConstSymbol(resolved_static_idx)) |folded_const| {
                    const const_ty = if (!target_ty.isError()) target_ty else sym.type_id;
                    return self.emitConstVal(folded_const, const_ty, tok, expr_id, true);
                }
                return self.emitNode(.{
                    .tag = .hir_global_ref,
                    .flags = .{ .category = .rvalue },
                    .type_id = if (!target_ty.isError()) target_ty else self.concreteType(sym.type_id),
                    .origin_token = tok,
                    .data = .{ .lhs = sym.def_id.asInt(), .rhs = resolved_static_idx.asInt() },
                }, expr_id);
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
            if (sym.kind == .fn_sym or sym.kind == .extern_static_sym) {
                const ref_cat: ValueCategory = if (sym.kind == .extern_static_sym)
                    (if (sym.flags.is_mut) .place_mut else .place_imm)
                else
                    .rvalue;
                return self.emitNode(.{
                    .tag = .hir_global_ref,
                    .flags = .{ .category = ref_cat, .is_unsafe = self.is_in_unsafe },
                    .type_id = if (!target_ty.isError()) target_ty else self.concreteType(sym.type_id),
                    .origin_token = tok,
                    .data = .{ .lhs = sym.def_id.asInt(), .rhs = resolved_static_idx.asInt() },
                }, expr_id);
            }
        }
        if (static_kind == .type_ns and std.mem.eql(u8, member_lexeme, "None")) {
            const unwrapped_target = self.pool.unwrapUnderlyingType(target_ty);
            if (!unwrapped_target.isError() and self.pool.getTag(unwrapped_target) == .optional_ty) {
                return self.emitOptionalNoneConstruct(target_ty, tok);
            }
        }

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
                recv_node.tag == .soa_slice_ty or recv_node.tag == .soa_array_ty or
                recv_ty == .str_ty or self.unionSliceElemType(recv_ty) != null))
        {
            return self.emitSequenceLen(raw_recv_hir, raw_recv_ty, tok);
        }

        const deref_base = try self.autoDerefPlace(raw_recv_hir, tok);
        const base_cat = self.store.getNode(deref_base).flags.category;

        // Built-in `SourceLoc` (`SE-17`) fields: `.file` (`0`), `.fn_name` (`1`), `.line` (`2`), `.col` (`3`):
        if (recv_ty == .source_loc_ty) {
            const loc_field_ord: ?u32 = if (std.mem.eql(u8, member_name, "file"))
                0
            else if (std.mem.eql(u8, member_name, "fn_name"))
                1
            else if (std.mem.eql(u8, member_name, "line"))
                2
            else if (std.mem.eql(u8, member_name, "col"))
                3
            else
                null;
            if (loc_field_ord) |f_ord| {
                const f_ty: TypeId = if (f_ord <= 1) .str_ty else .u32_ty;
                return self.emitNode(.{
                    .tag = .hir_field_proj,
                    .flags = .{ .category = if (base_cat == .place_mut) .place_mut else .place_imm },
                    .type_id = f_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = deref_base.asInt(), .rhs = f_ord },
                }, ast_origin);
            }
        }

        // `#soa [S]` column slice projection `items.field -> [FieldTy]` (`is_soa = false`):
        if (recv_node.tag == .soa_slice_ty or recv_node.tag == .soa_array_ty) {
            const elem_ty = TypeId.fromInt(recv_node.lhs);
            if (self.findStructFieldInfo(elem_ty, member_name)) |f_info| {
                const elem_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, elem_ty);
                const subst_f_ty = try elem_subst.applyMut(self.allocator, self.pool, f_info.field_ty);
                const col_slice_ty = try self.pool.internSlice(subst_f_ty, false);
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
            const recv_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, recv_ty);
            const subst_f_ty = try recv_subst.applyMut(self.allocator, self.pool, f_info.field_ty);
            const proj_cat: ValueCategory = switch (base_cat) {
                .place_mut => .place_mut,
                .place_imm => .place_imm,
                else => .rvalue,
            };
            return self.emitNode(.{
                .tag = .hir_field_proj,
                .flags = .{ .category = proj_cat, .is_unsafe = self.is_in_unsafe or recv_node.tag == .union_ty },
                .type_id = self.concreteType(subst_f_ty),
                .origin_token = tok,
                .data = .{ .lhs = deref_base.asInt(), .rhs = f_info.ordinal },
            }, ast_origin);
        }

        const fallback_ty = if (!ast_origin.isNone()) self.nodeType(ast_origin) else .unit_ty;
        return self.emitErrorHole(tok, ast_origin, fallback_ty);
    }

    /// Returns `true` if `root_id` references `$` (`AstTag.dollar_expr`) bound to the enclosing index receiver (`SE-04`).
    fn hasDollarAst(self: *const HirLowerer, root_id: NodeIndex) bool {
        return self.hasDollarAstDepth(root_id, 0);
    }

    /// Bounded recursive helper for `hasDollarAst` stopping at nested `.index_expr` RHS, items, types, and closures.
    fn hasDollarAstDepth(self: *const HirLowerer, node_id: NodeIndex, depth: u32) bool {
        if (depth > 128 or node_id.isNone() or node_id == .root or node_id.asInt() >= self.ast_arena.countNodes()) {
            return false;
        }
        const node = self.ast_arena.getNode(node_id);
        if (isTypeAstTag(node.tag)) return false;
        switch (node.tag) {
            .dollar_expr => return true,
            .root,
            .mod_decl,
            .use_decl,
            .const_decl,
            .type_alias_decl,
            .struct_decl,
            .enum_decl,
            .union_decl,
            .trait_decl,
            .impl_decl,
            .bit_field_decl,
            .subscript_decl,
            .test_decl,
            .bench_decl,
            .fn_decl,
            .extern_block_decl,
            .extern_static_decl,
            .closure_expr,
            .wildcard_pat,
            .bind_pat,
            .lit_pat,
            .variant_pat,
            .struct_pat,
            .tuple_pat,
            .or_pat,
            .at_pat,
            .slice_pat,
            .item_hole,
            .stmt_hole,
            .expr_hole,
            .type_hole,
            .pattern_hole,
            => return false,
            .index_expr => {
                // Only `lhs` (inner base) sees the outer `$`; `rhs` rebinds `$` to the inner receiver:
                return if (node.lhs.tag == .node)
                    self.hasDollarAstDepth(NodeIndex.fromInt(node.lhs.payload), depth + 1)
                else
                    false;
            },
            .method_call => {
                if (node.lhs.tag == .node and
                    self.hasDollarAstDepth(NodeIndex.fromInt(node.lhs.payload), depth + 1))
                {
                    return true;
                }
                const raw_items = self.getAstExtraSlice(node_id, true);
                if (raw_items.len > 1) {
                    for (raw_items[1..]) |raw_arg| {
                        if (self.hasDollarAstDepth(NodeIndex.fromInt(raw_arg), depth + 1)) return true;
                    }
                }
                return false;
            },
            .walrus_expr => {
                const extra = self.getAstExtraSlice(node_id, true);
                return extra.len >= 3 and self.hasDollarAstDepth(NodeIndex.fromInt(extra[2]), depth + 1);
            },
            .with_expr => {
                const extra = self.getAstExtraSlice(node_id, false);
                if (extra.len >= 1) {
                    const pair_count: usize = extra[0];
                    var pair_idx: usize = 0;
                    while (pair_idx < pair_count and 2 + pair_idx * 2 < extra.len) : (pair_idx += 1) {
                        if (self.hasDollarAstDepth(NodeIndex.fromInt(extra[2 + pair_idx * 2]), depth + 1)) {
                            return true;
                        }
                    }
                }
                return node.rhs.tag == .node and
                    self.hasDollarAstDepth(NodeIndex.fromInt(node.rhs.payload), depth + 1);
            },
            .for_stmt => {
                const extra = self.getAstExtraSlice(node_id, false);
                if (extra.len >= 2 and self.hasDollarAstDepth(NodeIndex.fromInt(extra[1]), depth + 1)) {
                    return true;
                }
                return node.rhs.tag == .node and
                    self.hasDollarAstDepth(NodeIndex.fromInt(node.rhs.payload), depth + 1);
            },
            .local_var_decl => {
                if (node.lhs.tag == .extra) {
                    const extra = self.getAstExtraSlice(node_id, false);
                    if (extra.len >= 3 and self.hasDollarAstDepth(NodeIndex.fromInt(extra[2]), depth + 1)) {
                        return true;
                    }
                    if (extra.len >= 4 and self.hasDollarAstDepth(NodeIndex.fromInt(extra[3]), depth + 1)) {
                        return true;
                    }
                    return false;
                }
                return node.rhs.tag == .node and
                    self.hasDollarAstDepth(NodeIndex.fromInt(node.rhs.payload), depth + 1);
            },
            .array_lit => {
                const elems = if (node.lhs.tag == .extra and node.rhs.tag == .extra)
                    self.ast_arena.getExtraSlice(ExtraIndex.fromInt(node.lhs.payload), node.rhs.payload)
                else
                    self.getAstExtraSlice(node_id, false);
                for (elems) |raw_elem| {
                    if (self.hasDollarAstDepth(NodeIndex.fromInt(raw_elem), depth + 1)) return true;
                }
                return false;
            },
            .tuple_lit, .block => {
                if (node.lhs.tag == .extra) {
                    for (self.getAstExtraSlice(node_id, false)) |raw_child| {
                        if (self.hasDollarAstDepth(NodeIndex.fromInt(raw_child), depth + 1)) return true;
                    }
                }
                return node.rhs.tag == .node and
                    self.hasDollarAstDepth(NodeIndex.fromInt(node.rhs.payload), depth + 1);
            },
            .call_expr, .generic_call, .contextual_variant, .struct_lit, .if_expr, .match_expr => {
                if (node.lhs.tag == .node and
                    self.hasDollarAstDepth(NodeIndex.fromInt(node.lhs.payload), depth + 1))
                {
                    return true;
                }
                if (node.rhs.tag == .node) {
                    return self.hasDollarAstDepth(NodeIndex.fromInt(node.rhs.payload), depth + 1);
                }
                if (node.rhs.tag == .extra) {
                    for (self.getAstExtraSlice(node_id, true)) |raw_child| {
                        if (self.hasDollarAstDepth(NodeIndex.fromInt(raw_child), depth + 1)) return true;
                    }
                }
                return false;
            },
            else => {
                if (node.lhs.tag == .node and
                    self.hasDollarAstDepth(NodeIndex.fromInt(node.lhs.payload), depth + 1))
                {
                    return true;
                }
                if (node.rhs.tag == .node and
                    self.hasDollarAstDepth(NodeIndex.fromInt(node.rhs.payload), depth + 1))
                {
                    return true;
                }
                return false;
            },
        }
    }

    /// Evaluates an indexing receiver once and binds its length (`usize`) into a temp local for `$` (`SE-04`).
    fn bindIndexReceiverForDollar(
        self: *HirLowerer,
        base_ast_id: NodeIndex,
        is_mut_access_needed: bool,
        tok: TokenIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
    ) !struct { base_hir: HirIndex, len_slot: u32 } {
        const raw_base_hir = try self.lowerPlaceWithMutCtx(base_ast_id, .err_ty, is_mut_access_needed);
        const raw_node = self.store.getNode(raw_base_hir);
        const raw_ty = raw_node.type_id;

        var reusable_base: HirIndex = raw_base_hir;
        var seq_len_ty: TypeId = raw_ty;
        if (raw_node.tag == .hir_var_ref) {
            reusable_base = raw_base_hir;
        } else {
            const deref_base = try self.autoDerefPlace(raw_base_hir, tok);
            const deref_node = self.store.getNode(deref_base);
            if (deref_node.flags.category == .place_mut or deref_node.flags.category == .place_imm) {
                const is_mut = is_mut_access_needed and deref_node.flags.category == .place_mut;
                const deref_ty = deref_node.type_id;
                const ptr_ty = try self.pool.internRef(deref_ty, is_mut);
                const addr_hir = try self.emitSyntheticAddrOf(deref_base, ptr_ty, is_mut, tok);
                const ptr_slot = try self.allocTempLocal(ptr_ty, tok, false);
                try out_stmts.append(self.allocator, (try self.emitLocalDeclNode(ptr_slot, addr_hir, tok)).asInt());
                reusable_base = try self.emitNode(.{
                    .tag = .hir_unary_op,
                    .flags = .{ .category = if (is_mut) .place_mut else .place_imm, .is_synthetic = true },
                    .type_id = deref_ty,
                    .origin_token = tok,
                    .data = .{
                        .lhs = @backingInt(HirUnaryOp.deref),
                        .rhs = (try self.emitVarRef(ptr_slot, tok, .none)).asInt(),
                    },
                }, .none);
                seq_len_ty = deref_ty;
            } else {
                const val_slot = try self.allocTempLocal(raw_ty, tok, false);
                try out_stmts.append(
                    self.allocator,
                    (try self.emitLocalDeclNode(val_slot, raw_base_hir, tok)).asInt(),
                );
                reusable_base = try self.emitVarRef(val_slot, tok, .none);
            }
        }

        // Re-emit a fresh handle for `.len` computation so `reusable_base` is not aliased in the HIR tree:
        const len_base_copy = blk_copy: {
            const reusable_node = self.store.getNode(reusable_base);
            if (reusable_node.tag == .hir_var_ref) {
                break :blk_copy try self.emitVarRef(reusable_node.data.lhs, tok, .none);
            }
            const ptr_var = self.store.getNode(HirIndex.fromInt(reusable_node.data.rhs));
            const ptr_ref = try self.emitVarRef(ptr_var.data.lhs, tok, .none);
            break :blk_copy try self.emitNode(.{
                .tag = .hir_unary_op,
                .flags = reusable_node.flags,
                .type_id = reusable_node.type_id,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(HirUnaryOp.deref), .rhs = ptr_ref.asInt() },
            }, .none);
        };

        const unwrapped_ty = self.unwrapRefType(seq_len_ty);
        const unwrapped_tag = self.pool.getTag(unwrapped_ty);
        const len_hir: HirIndex = if (unwrapped_tag == .slice_ty or unwrapped_tag == .array_ty or
            unwrapped_tag == .soa_slice_ty or unwrapped_tag == .soa_array_ty or unwrapped_ty == .str_ty)
            try self.emitSequenceLen(len_base_copy, seq_len_ty, tok)
        else if (try self.lookupMethodOnType(unwrapped_ty, "len")) |len_sym_idx| blk_m: {
            const len_sym = self.sym_table.getSymbol(len_sym_idx).*;
            const len_sig = self.pool.getFnSignatureView(len_sym.type_id);
            const self_ty = if (len_sig) |sv|
                (if (sv.paramCount() > 0) sv.getParamType(0) else seq_len_ty)
            else
                seq_len_ty;
            const self_mode = if (len_sig) |sv|
                (if (sv.paramCount() > 0) sv.getParamMode(0) else .let_mode)
            else
                .let_mode;
            const adj_recv = try self.adjustReceiverForParam(len_base_copy, self_ty, tok);
            const proj_recv = try self.wrapArgProjection(adj_recv, self_mode, tok);
            const callee_hir = try self.emitNode(.{
                .tag = .hir_global_ref,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = len_sym.type_id,
                .origin_token = tok,
                .data = .{ .lhs = len_sym.def_id.asInt(), .rhs = len_sym_idx.asInt() },
            }, .none);
            const extra_idx = try self.store.appendLenPrefixedExtra(&[1]u32{proj_recv.asInt()});
            break :blk_m try self.emitNode(.{
                .tag = .hir_call,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = .usize_ty,
                .origin_token = tok,
                .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
            }, .none);
        } else try self.emitConstVal(.{ .int_val = 0 }, .usize_ty, tok, .none, true);

        const len_slot = try self.allocTempLocal(.usize_ty, tok, false);
        try out_stmts.append(self.allocator, (try self.emitLocalDeclNode(len_slot, len_hir, tok)).asInt());
        return .{ .base_hir = reusable_base, .len_slot = len_slot };
    }

    /// Emits `hir_soa_field_ptr` shared by both `items[i].field` and `items.field[i]` (`DR-13` §2.2 Rule 6).
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
        const is_mut_access_needed = self.is_mut_lvalue_ctx;
        const has_dollar = self.hasDollarAst(idx_ast);
        var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer seq_stmts.deinit(self.allocator);

        var deref_base: HirIndex = .none;
        var idx_slot: u32 = 0;
        if (has_dollar) {
            const bound = try self.bindIndexReceiverForDollar(soa_base_ast, is_mut_access_needed, tok, &seq_stmts);
            deref_base = try self.autoDerefPlace(bound.base_hir, tok);
            try self.dollar_len_stack.append(self.allocator, bound.len_slot);
            const idx_hir = blk_idx: {
                defer _ = self.dollar_len_stack.pop();
                break :blk_idx try self.lowerPlaceWithMutCtx(idx_ast, .usize_ty, false);
            };
            idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
            try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_slot, idx_hir, tok)).asInt());
        } else {
            const idx_hir = try self.lowerPlaceWithMutCtx(idx_ast, .usize_ty, false);
            idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
            try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_slot, idx_hir, tok)).asInt());
            const raw_base_hir = try self.lowerPlaceWithMutCtx(soa_base_ast, .err_ty, is_mut_access_needed);
            deref_base = try self.autoDerefPlace(raw_base_hir, tok);
        }

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
        return self.emitSyntheticBlock(seq_stmts.items, soa_ptr, field_ty, tok);
    }

    /// Lowers `base[index]`, `base[i, j, …]` (`SE-21`), and `base[start..end]` (`SE-04`, `SE-09`).
    fn lowerIndexExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const outer_mut_ctx = self.is_mut_lvalue_ctx;
        self.is_mut_lvalue_ctx = false;
        defer self.is_mut_lvalue_ctx = outer_mut_ctx;

        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node) {
            return self.emitErrorHole(tok, expr_id, target_ty);
        }
        const base_ast_id = NodeIndex.fromInt(ast_node.lhs.payload);

        // [-1] Multi-index `base[i, j, …]` (`SE-21` `subscript(r, c, …)`):
        if (ast_node.rhs.tag == .extra) {
            const raw_indices = self.getAstExtraSlice(expr_id, true);
            if (raw_indices.len == 0) return self.emitErrorHole(tok, expr_id, target_ty);
            const raw_base_ty = self.nodeType(base_ast_id);
            const unwrapped_base = self.unwrapRefType(raw_base_ty);
            const recorded_sym = self.nodeSymbol(expr_id);
            const sub_sym_idx = if (!recorded_sym.isNone() and !self.sym_table.getSymbol(recorded_sym).flags.is_overload)
                recorded_sym
            else
                (try self.lookupMethodOnType(unwrapped_base, "subscript")) orelse
                    return self.emitErrorHole(tok, expr_id, target_ty);
            const sub_sym = self.sym_table.getSymbol(sub_sym_idx).*;
            const sig_view = self.pool.getFnSignatureView(sub_sym.type_id);
            const has_explicit_self = self.hasSubscriptExplicitSelf(sub_sym_idx);
            const idx_param_offset: usize = if (has_explicit_self) 1 else 0;
            const is_inout_arm_call = outer_mut_ctx and sub_sym.flags.is_mut;
            const recv_param_ty = if (has_explicit_self)
                (if (sig_view) |sv| self.concreteType(sv.getParamType(0)) else raw_base_ty)
            else
                try self.pool.internRef(self.concreteType(unwrapped_base), is_inout_arm_call);
            const recv_mode: ParamMode = if (has_explicit_self)
                (if (sig_view) |sv| sv.getParamMode(0) else .let_mode)
            else
                .let_mode;
            const is_mut_sub_needed = outer_mut_ctx or recv_mode == .inout_mode or recv_mode == .set_mode or
                self.pool.getTag(recv_param_ty) == .mut_ref_ty;

            var has_any_dollar = false;
            for (raw_indices) |raw_idx| {
                if (self.hasDollarAst(NodeIndex.fromInt(raw_idx))) {
                    has_any_dollar = true;
                    break;
                }
            }

            var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
            defer seq_stmts.deinit(self.allocator);
            var idx_slots = try self.allocator.alloc(u32, raw_indices.len);
            defer self.allocator.free(idx_slots);

            var base_hir: HirIndex = .none;
            if (has_any_dollar) {
                const bound = try self.bindIndexReceiverForDollar(base_ast_id, is_mut_sub_needed, tok, &seq_stmts);
                base_hir = bound.base_hir;
                try self.dollar_len_stack.append(self.allocator, bound.len_slot);
                defer _ = self.dollar_len_stack.pop();
                for (raw_indices, 0..) |raw_idx, i| {
                    const param_ord = idx_param_offset + i;
                    const param_ty = if (sig_view) |sv|
                        (if (param_ord < sv.paramCount()) self.concreteType(sv.getParamType(param_ord)) else .usize_ty)
                    else
                        .usize_ty;
                    const idx_hir = try self.lowerExpr(NodeIndex.fromInt(raw_idx), param_ty);
                    idx_slots[i] = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
                    try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_slots[i], idx_hir, tok)).asInt());
                }
            } else {
                for (raw_indices, 0..) |raw_idx, i| {
                    const param_ord = idx_param_offset + i;
                    const param_ty = if (sig_view) |sv|
                        (if (param_ord < sv.paramCount()) self.concreteType(sv.getParamType(param_ord)) else .usize_ty)
                    else
                        .usize_ty;
                    const idx_hir = try self.lowerExpr(NodeIndex.fromInt(raw_idx), param_ty);
                    idx_slots[i] = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
                    try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_slots[i], idx_hir, tok)).asInt());
                }
                base_hir = try self.lowerPlaceWithMutCtx(base_ast_id, .err_ty, is_mut_sub_needed);
            }

            var wrapped_sub_args: std.ArrayListUnmanaged(u32) = .empty;
            defer wrapped_sub_args.deinit(self.allocator);
            const adjusted_recv = try self.adjustReceiverForParam(base_hir, recv_param_ty, tok);
            try wrapped_sub_args.append(
                self.allocator,
                (try self.wrapArgProjection(adjusted_recv, recv_mode, tok)).asInt(),
            );
            for (idx_slots, 0..) |slot_id, i| {
                const param_ord = idx_param_offset + i;
                const idx_mode = if (sig_view) |sv|
                    (if (param_ord < sv.paramCount()) sv.getParamMode(param_ord) else .let_mode)
                else
                    .let_mode;
                const idx_ref = try self.emitVarRef(slot_id, tok, .none);
                try wrapped_sub_args.append(
                    self.allocator,
                    (try self.wrapArgProjection(idx_ref, idx_mode, tok)).asInt(),
                );
            }
            const callee_hir = try self.emitNode(.{
                .tag = .hir_global_ref,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = sub_sym.type_id,
                .origin_token = tok,
                .data = .{ .lhs = sub_sym.def_id.asInt(), .rhs = sub_sym_idx.asInt() },
            }, .none);
            const extra_idx = try self.store.appendLenPrefixedExtra(wrapped_sub_args.items);
            const expr_ty = self.nodeType(expr_id);
            const ret_ty = if (!expr_ty.isError())
                expr_ty
            else if (!target_ty.isError())
                target_ty
            else if (sig_view) |sv|
                self.concreteType(sv.ret_ty)
            else
                .unit_ty;
            const sub_call = try self.emitNode(.{
                .tag = .hir_subscript_call,
                .flags = .{
                    .category = if (is_inout_arm_call) .place_mut else .place_imm,
                    .is_synthetic = true,
                },
                .type_id = ret_ty,
                .origin_token = tok,
                .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
            }, expr_id);
            return self.emitSyntheticBlock(seq_stmts.items, sub_call, ret_ty, tok);
        }

        if (ast_node.rhs.tag != .node) {
            return self.emitErrorHole(tok, expr_id, target_ty);
        }
        const idx_ast_id = NodeIndex.fromInt(ast_node.rhs.payload);
        const base_ast = self.ast_arena.getNode(base_ast_id);

        // [0] Subslice range indexing `base[start..end]`, `base[..end]`, `base[start..]`, `base[..]` (`SE-04`):
        if (self.extractRangeAstInfo(idx_ast_id)) |range_info| {
            var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
            defer seq_stmts.deinit(self.allocator);

            const is_mut_slice_needed = outer_mut_ctx or
                (!target_ty.isError() and self.pool.getTag(self.concreteType(target_ty)) == .mut_ref_ty);
            const has_dollar = self.hasDollarAst(range_info.start_id) or
                self.hasDollarAst(range_info.end_id);
            var deref_base: HirIndex = .none;
            var start_hir: HirIndex = .none;
            var end_hir: HirIndex = .none;
            if (has_dollar) {
                const bound = try self.bindIndexReceiverForDollar(base_ast_id, is_mut_slice_needed, tok, &seq_stmts);
                deref_base = try self.autoDerefPlace(bound.base_hir, tok);
                try self.dollar_len_stack.append(self.allocator, bound.len_slot);
                defer _ = self.dollar_len_stack.pop();
                if (!range_info.start_id.isNone()) {
                    start_hir = try self.lowerExpr(range_info.start_id, .usize_ty);
                }
                if (!range_info.end_id.isNone()) {
                    end_hir = try self.lowerExpr(range_info.end_id, .usize_ty);
                }
            } else {
                const raw_base_hir = try self.lowerPlaceWithMutCtx(base_ast_id, .err_ty, is_mut_slice_needed);
                deref_base = try self.autoDerefPlace(raw_base_hir, tok);
                if (!range_info.start_id.isNone()) {
                    start_hir = try self.lowerExpr(range_info.start_id, .usize_ty);
                }
                if (!range_info.end_id.isNone()) {
                    end_hir = try self.lowerExpr(range_info.end_id, .usize_ty);
                }
            }

            var seq_base = deref_base;
            var base_node = self.store.getNode(seq_base);
            var base_ty_node = self.pool.getNode(base_node.type_id);
            const is_mut_seq = base_node.flags.category == .place_mut;
            if (base_ty_node.tag == .struct_ty) {
                const method_name = if (try self.lookupMethodOnType(base_node.type_id, "as_str") != null)
                    "as_str"
                else if (is_mut_seq and try self.lookupMethodOnType(base_node.type_id, "as_mut_slice") != null)
                    "as_mut_slice"
                else
                    "as_slice";
                if (try self.lookupMethodOnType(base_node.type_id, method_name)) |view_sym_idx| {
                    const view_sym = self.sym_table.getSymbol(view_sym_idx).*;
                    const view_sig = self.pool.getFnSignatureView(view_sym.type_id);
                    const self_ty = if (view_sig) |sv|
                        (if (sv.paramCount() > 0) sv.getParamType(0) else base_node.type_id)
                    else
                        base_node.type_id;
                    const self_mode = if (view_sig) |sv|
                        (if (sv.paramCount() > 0) sv.getParamMode(0) else .let_mode)
                    else
                        .let_mode;
                    const adj_recv = try self.adjustReceiverForParam(seq_base, self_ty, tok);
                    const proj_recv = try self.wrapArgProjection(adj_recv, self_mode, tok);
                    const callee_hir = try self.emitNode(.{
                        .tag = .hir_global_ref,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = view_sym.type_id,
                        .origin_token = tok,
                        .data = .{ .lhs = view_sym.def_id.asInt(), .rhs = view_sym_idx.asInt() },
                    }, .none);
                    const extra_idx = try self.store.appendLenPrefixedExtra(&[1]u32{proj_recv.asInt()});
                    const ret_ty = if (view_sig) |sv| self.concreteType(sv.ret_ty) else .str_ty;
                    const call_hir = try self.emitNode(.{
                        .tag = .hir_call,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = ret_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
                    }, .none);
                    seq_base = try self.autoDerefPlace(call_hir, tok);
                    base_node = self.store.getNode(seq_base);
                    base_ty_node = self.pool.getNode(base_node.type_id);
                }
            }
            const slice_res_ty = if (!target_ty.isError())
                self.concreteType(target_ty)
            else if (base_node.type_id == .str_ty or self.unionSliceElemType(base_node.type_id) != null)
                base_node.type_id
            else switch (base_ty_node.tag) {
                .slice_ty, .array_ty => try self.pool.internRef(
                    try self.pool.internSlice(TypeId.fromInt(base_ty_node.lhs), false),
                    base_node.flags.category == .place_mut,
                ),
                .soa_slice_ty, .soa_array_ty => try self.pool.internRef(
                    try self.pool.internSlice(TypeId.fromInt(base_ty_node.lhs), true),
                    base_node.flags.category == .place_mut,
                ),
                else => .str_ty,
            };

            const range_extra = try self.store.appendExtraSlice(&[3]u32{
                start_hir.asInt(),
                end_hir.asInt(),
                @intFromBool(range_info.is_inclusive),
            });
            const slice_hir = try self.emitNode(.{
                .tag = .hir_slice_range,
                .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
                .type_id = slice_res_ty,
                .origin_token = tok,
                .data = .{ .lhs = seq_base.asInt(), .rhs = range_extra },
            }, expr_id);
            if (seq_stmts.items.len > 0) {
                return self.emitSyntheticBlock(seq_stmts.items, slice_hir, slice_res_ty, tok);
            }
            return slice_hir;
        }

        // [1] Intercept `#soa` columnar syntax `items.field[i] -> hir_soa_field_ptr` (`DR-13` §2.2 Rule 6):
        if (base_ast.tag == .field_access and base_ast.lhs.tag == .node and base_ast.rhs.tag == .token) {
            const soa_cand_ast = NodeIndex.fromInt(base_ast.lhs.payload);
            const unwrapped_soa_ty = self.unwrapRefType(self.nodeType(soa_cand_ast));
            const soa_tag = self.pool.getTag(unwrapped_soa_ty);
            if (soa_tag == .soa_slice_ty or soa_tag == .soa_array_ty) {
                const field_tok = TokenIndex.fromInt(base_ast.rhs.payload);
                const field_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, field_tok);
                self.is_mut_lvalue_ctx = outer_mut_ctx;
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

        const has_dollar = self.hasDollarAst(idx_ast_id);

        // [2] Check if `base` is a nominal type defining `subscript(idx)` (`SE-21`):
        const raw_base_ty = self.nodeType(base_ast_id);
        const unwrapped_base = self.unwrapRefType(raw_base_ty);
        const recorded_single_sub = self.nodeSymbol(expr_id);
        const maybe_sub_sym_idx: ?SymbolIndex = if (!recorded_single_sub.isNone() and
            !self.sym_table.getSymbol(recorded_single_sub).flags.is_overload)
            recorded_single_sub
        else
            try self.lookupMethodOnType(unwrapped_base, "subscript");
        if (maybe_sub_sym_idx) |sub_sym_idx| {
            const sub_sym = self.sym_table.getSymbol(sub_sym_idx).*;
            const sig_view = self.pool.getFnSignatureView(sub_sym.type_id);
            const has_explicit_self = self.hasSubscriptExplicitSelf(sub_sym_idx);
            const idx_param_ord: usize = if (has_explicit_self) 1 else 0;
            const is_inout_arm_call = outer_mut_ctx and sub_sym.flags.is_mut;
            const recv_param_ty = if (has_explicit_self)
                (if (sig_view) |sv| self.concreteType(sv.getParamType(0)) else raw_base_ty)
            else
                try self.pool.internRef(self.concreteType(unwrapped_base), is_inout_arm_call);
            const recv_mode: ParamMode = if (has_explicit_self)
                (if (sig_view) |sv| sv.getParamMode(0) else .let_mode)
            else
                .let_mode;
            const idx_param_ty = if (sig_view) |sv|
                (if (idx_param_ord < sv.paramCount()) self.concreteType(sv.getParamType(idx_param_ord)) else .usize_ty)
            else
                .usize_ty;
            const idx_mode = if (sig_view) |sv|
                (if (idx_param_ord < sv.paramCount()) sv.getParamMode(idx_param_ord) else .let_mode)
            else
                .let_mode;
            const is_mut_sub_needed = outer_mut_ctx or recv_mode == .inout_mode or recv_mode == .set_mode or
                self.pool.getTag(recv_param_ty) == .mut_ref_ty;

            var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
            defer seq_stmts.deinit(self.allocator);

            var base_hir: HirIndex = .none;
            var idx_slot: u32 = 0;
            if (has_dollar) {
                const bound = try self.bindIndexReceiverForDollar(base_ast_id, is_mut_sub_needed, tok, &seq_stmts);
                base_hir = bound.base_hir;
                try self.dollar_len_stack.append(self.allocator, bound.len_slot);
                const idx_hir = blk_sub_idx: {
                    defer _ = self.dollar_len_stack.pop();
                    break :blk_sub_idx try self.lowerExpr(idx_ast_id, idx_param_ty);
                };
                idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
                try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_slot, idx_hir, tok)).asInt());
            } else {
                const idx_hir = try self.lowerExpr(idx_ast_id, idx_param_ty);
                idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
                try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_slot, idx_hir, tok)).asInt());
                base_hir = try self.lowerPlaceWithMutCtx(base_ast_id, .err_ty, is_mut_sub_needed);
            }

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
            const expr_ty = self.nodeType(expr_id);
            const ret_ty = if (!expr_ty.isError())
                expr_ty
            else if (!target_ty.isError())
                target_ty
            else if (sig_view) |sv|
                self.concreteType(sv.ret_ty)
            else
                .unit_ty;
            const sub_call = try self.emitNode(.{
                .tag = .hir_subscript_call,
                .flags = .{
                    .category = if (is_inout_arm_call) .place_mut else .place_imm,
                    .is_synthetic = true,
                },
                .type_id = ret_ty,
                .origin_token = tok,
                .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
            }, expr_id);
            return self.emitSyntheticBlock(seq_stmts.items, sub_call, ret_ty, tok);
        }

        // [3] Built-in array / slice / `#soa` element index projection (`SE-04` `$` or `DR-02` §2.2 index-then-base):
        var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer seq_stmts.deinit(self.allocator);

        var deref_base: HirIndex = .none;
        var idx_slot: u32 = 0;
        if (has_dollar) {
            const bound = try self.bindIndexReceiverForDollar(base_ast_id, outer_mut_ctx, tok, &seq_stmts);
            deref_base = try self.autoDerefPlace(bound.base_hir, tok);
            try self.dollar_len_stack.append(self.allocator, bound.len_slot);
            const idx_hir = blk_arr_idx: {
                defer _ = self.dollar_len_stack.pop();
                break :blk_arr_idx try self.lowerExpr(idx_ast_id, .usize_ty);
            };
            idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
            try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_slot, idx_hir, tok)).asInt());
        } else {
            const idx_hir = try self.lowerExpr(idx_ast_id, .usize_ty);
            idx_slot = try self.allocTempLocal(self.store.getNode(idx_hir).type_id, tok, false);
            try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(idx_slot, idx_hir, tok)).asInt());
            const raw_base_hir = try self.lowerPlaceWithMutCtx(base_ast_id, .err_ty, outer_mut_ctx);
            deref_base = try self.autoDerefPlace(raw_base_hir, tok);
        }

        const base_node = self.store.getNode(deref_base);
        const base_ty_node = self.pool.getNode(base_node.type_id);
        const elem_ty = self.concreteType(if (!target_ty.isError())
            target_ty
        else if (base_node.type_id == .str_ty)
            .u8_ty
        else switch (base_ty_node.tag) {
            .slice_ty, .soa_slice_ty, .array_ty, .soa_array_ty, .raw_ptr_ty => TypeId.fromInt(base_ty_node.lhs),
            else => .unit_ty,
        });
        const is_mut_seq = if (base_ty_node.tag == .raw_ptr_ty)
            base_ty_node.rhs != 0
        else
            base_node.flags.category == .place_mut or
                ((base_ty_node.tag == .slice_ty or base_ty_node.tag == .soa_slice_ty) and base_ty_node.rhs != 0);
        const idx_ref = try self.emitVarRef(idx_slot, tok, .none);
        const proj_hir = try self.emitNode(.{
            .tag = .hir_index_proj,
            .flags = .{ .category = if (is_mut_seq) .place_mut else .place_imm, .is_unsafe = self.is_in_unsafe },
            .type_id = elem_ty,
            .origin_token = tok,
            .data = .{ .lhs = deref_base.asInt(), .rhs = idx_ref.asInt() },
        }, expr_id);
        return self.emitSyntheticBlock(seq_stmts.items, proj_hir, elem_ty, tok);
    }

    /// Lowers an omitted default argument expression (`param: T = DefaultExpr`) in the callee's lexical scope (`SE-07`).
    fn lowerCalleeDefaultExpr(
        self: *HirLowerer,
        callee_sym: SymbolIndex,
        full_param_idx: usize,
        param_offset: usize,
        slot_locals: []const u32,
        param_ty: TypeId,
        call_tok: TokenIndex,
    ) anyerror!HirIndex {
        const concrete_param_ty = self.concreteType(if (!param_ty.isError()) param_ty else .unit_ty);
        var active_callee_sym = callee_sym;
        if (!callee_sym.isNone() and callee_sym.asInt() < self.sym_table.symbols.items.len) {
            const raw_callee = self.sym_table.getSymbol(callee_sym).*;
            if (!raw_callee.def_id.isNone()) {
                if (self.sym_table.def_to_symbol.get(raw_callee.def_id.asInt())) |latest_callee| {
                    if (!latest_callee.isNone()) active_callee_sym = latest_callee;
                }
            }
        }
        const specs = self.sym_table.fn_param_specs.get(active_callee_sym.asInt()) orelse
            return self.emitDefaultInitValue(concrete_param_ty, call_tok);
        if (full_param_idx < specs.len and specs[full_param_idx].is_caller_location_default) {
            if (self.active_caller_loc_local) |loc_slot| {
                return self.emitVarRef(loc_slot, call_tok, .none);
            }
            return self.emitCallerLocationConst(call_tok, .none);
        }
        if (full_param_idx >= specs.len or !specs[full_param_idx].has_default or
            specs[full_param_idx].default_ast_node.isNone())
        {
            return self.emitDefaultInitValue(concrete_param_ty, call_tok);
        }
        const spec = specs[full_param_idx];
        const callee_rec = self.sym_table.getSymbol(active_callee_sym).*;
        const callee_scope = if (!callee_rec.target_scope.isNone())
            callee_rec.target_scope
        else
            callee_rec.scope_id;

        const saved_locals = self.active_name_to_local;
        const saved_ct = self.active_comptime_vals;
        const saved_zips = self.active_zip_bindings;
        const saved_scope = self.current_scope;
        const saved_mut_ctx = self.is_mut_lvalue_ctx;
        const saved_lex_file = self.active_lexical_file_id;
        self.active_name_to_local = .empty;
        self.active_comptime_vals = .empty;
        self.active_zip_bindings = .empty;
        self.current_scope = callee_scope;
        self.is_mut_lvalue_ctx = false;
        self.active_lexical_file_id = if (!spec.decl_file_id.isNone()) spec.decl_file_id else self.store.file_id;
        defer {
            self.active_name_to_local.deinit(self.allocator);
            self.active_comptime_vals.deinit(self.allocator);
            self.active_zip_bindings.deinit(self.allocator);
            self.active_name_to_local = saved_locals;
            self.active_comptime_vals = saved_ct;
            self.active_zip_bindings = saved_zips;
            self.current_scope = saved_scope;
            self.is_mut_lvalue_ctx = saved_mut_ctx;
            self.active_lexical_file_id = saved_lex_file;
        }

        // Bind earlier evaluated parameter slots (`0 .. full_param_idx`) so `hi: i32 = lo + 10` resolves `lo`:
        for (0..@min(full_param_idx, specs.len)) |prior_full_idx| {
            if (prior_full_idx < param_offset) continue;
            const rel_prior = prior_full_idx - param_offset;
            if (rel_prior >= slot_locals.len or slot_locals[rel_prior] == NONE_U32) continue;
            const prior_spec = specs[prior_full_idx];
            const param_name_id = if (prior_spec.name != .empty)
                prior_spec.name
            else if (prior_spec.name_text.len > 0)
                try self.interner.intern(prior_spec.name_text)
            else
                SymbolId.empty;
            if (param_name_id != .empty) {
                try self.active_name_to_local.put(self.allocator, param_name_id.asInt(), slot_locals[rel_prior]);
            }
        }

        if (spec.decl_file_id.isNone() or spec.decl_file_id == self.store.file_id) {
            const saved_tables = self.side_tables;
            const saved_ov_tok = self.interp_override_token;
            if (self.interp_override_token.isNone()) self.interp_override_token = call_tok;
            defer {
                self.side_tables = saved_tables;
                self.interp_override_token = saved_ov_tok;
            }
            if (self.eval_hook.compiler_db) |db| {
                if (try db.getExternalFileSyntaxView(self.store.file_id)) |same_view| {
                    if (same_view.file_side_tables) |file_st| {
                        self.side_tables = file_st;
                    }
                }
            }
            return self.lowerExpr(spec.default_ast_node, concrete_param_ty);
        }

        const db = self.eval_hook.compiler_db orelse
            return self.emitDefaultInitValue(concrete_param_ty, call_tok);
        const ext_view = (try db.getExternalFileSyntaxView(spec.decl_file_id)) orelse
            return self.emitDefaultInitValue(concrete_param_ty, call_tok);

        const ext_extra_ends = try syntax_arenas.computeAstNodeExtraEnds(self.allocator, ext_view.ast_arena);
        defer if (ext_extra_ends.len > 0) self.allocator.free(ext_extra_ends);
        const ext_cst_map = try syntax_arenas.computeCstToAstMap(
            self.allocator,
            ext_view.cst_arena.countNodes(),
            ext_view.ast_arena,
        );
        defer if (ext_cst_map.len > 0) self.allocator.free(ext_cst_map);

        const outer_span = if (self.interp_override_span) |existing_span|
            existing_span
        else if (!call_tok.isNone() and call_tok.asInt() < self.tokens.countTokens())
            self.tokens.getTokenSpan(self.store.file_id, call_tok)
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
        const saved_ov_src = self.interp_override_source;

        self.source = ext_view.source;
        self.tokens = ext_view.tokens;
        self.cst_arena = ext_view.cst_arena;
        self.ast_arena = ext_view.ast_arena;
        self.side_tables = ext_view.file_side_tables;
        self.node_extra_end = ext_extra_ends;
        self.cst_to_ast = ext_cst_map;
        self.interp_override_token = if (!saved_ov_tok.isNone()) saved_ov_tok else call_tok;
        self.interp_override_span = outer_span;
        if (self.interp_override_source == null) self.interp_override_source = saved_source;
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
            self.interp_override_source = saved_ov_src;
        }

        return self.lowerExpr(spec.default_ast_node, concrete_param_ty);
    }

    /// Evaluates `@caller_location()` at `tok` into `ComptimeValue.aggregate` (`type_id = .source_loc_ty`, `SE-17`).
    fn evalCallerLocationValue(self: *HirLowerer, tok: TokenIndex) !ComptimeValue {
        const eff_tok = if (!self.interp_override_token.isNone()) self.interp_override_token else tok;
        const src_bytes = if (self.interp_override_span != null)
            (self.interp_override_source orelse self.source)
        else
            self.source;
        var byte_off: u32 = 0;
        if (self.interp_override_span) |ov_span| {
            byte_off = ov_span.start_byte;
        } else if (!eff_tok.isNone() and eff_tok.asInt() < self.tokens.countTokens()) {
            byte_off = self.tokens.getTokenSpan(self.store.file_id, eff_tok).start_byte;
        }
        var line: u32 = 1;
        var col: u32 = 1;
        const limit = @min(@as(usize, byte_off), src_bytes.len);
        for (src_bytes[0..limit]) |byte_ch| {
            if (byte_ch == '\n') {
                line += 1;
                col = 1;
            } else if (byte_ch != '\r') {
                col += 1;
            }
        }
        var file_name_buf: [64]u8 = undefined;
        const file_label = if (!self.store.file_id.isNone())
            std.fmt.bufPrint(&file_name_buf, "file_{d}.cx", .{self.store.file_id.asInt()}) catch "<source>"
        else
            "<source>";
        const file_sym = try self.interner.intern(file_label);
        const fn_sym = if (self.active_fn_name != .empty)
            self.active_fn_name
        else
            try self.interner.intern("<top>");
        const loc_elems = [4]u32{
            try self.store.appendConst(.{ .str_val = file_sym }),
            try self.store.appendConst(.{ .str_val = fn_sym }),
            try self.store.appendConst(.{ .int_val = @as(i128, line) }),
            try self.store.appendConst(.{ .int_val = @as(i128, col) }),
        };
        const elem_start: u32 = @intCast(self.store.const_elements.items.len);
        try self.store.const_elements.appendSlice(self.allocator, &loc_elems);
        return .{
            .aggregate = .{
                .type_id = .source_loc_ty,
                .elem_start = elem_start,
                .elem_len = 4,
            },
        };
    }

    /// Emits a `.source_loc_ty` constant HIR node for `@caller_location()` (`SE-17`).
    fn emitCallerLocationConst(self: *HirLowerer, tok: TokenIndex, ast_origin: NodeIndex) !HirIndex {
        const loc_val = try self.evalCallerLocationValue(tok);
        return self.emitConstVal(loc_val, .source_loc_ty, tok, ast_origin, true);
    }

    /// Applies C default argument promotions (`enum`/`bit_field` unwrap, `< 32`-bit int/bool -> `i32`, `f32` -> `f64`) (`Fix-07`).
    fn applyCVariadicPromotionIfNeeded(
        self: *HirLowerer,
        arg_hir: HirIndex,
        sig_view: ?type_system.FnSignatureView,
        full_param_idx: usize,
        tok: TokenIndex,
    ) !HirIndex {
        const sv = sig_view orelse return arg_hir;
        if (!sv.is_variadic or !sv.is_c_abi or full_param_idx < sv.paramCount() or arg_hir.isNone()) {
            return arg_hir;
        }
        var cur_hir = arg_hir;
        var cur_ty = self.pool.unwrapRefinementBase(
            self.pool.unwrapUnderlyingType(self.store.getNode(cur_hir).type_id),
        );
        const cur_tag = self.pool.getTag(cur_ty);
        if (cur_tag == .enum_ty) {
            const backing_int = self.pool.getEnumBackingIntType(cur_ty) orelse .i32_ty;
            cur_hir = try self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                .type_id = backing_int,
                .origin_token = tok,
                .data = .{ .lhs = cur_hir.asInt(), .rhs = @backingInt(HirCastKind.int_to_int) },
            }, .none);
            cur_ty = backing_int;
        } else if (cur_tag == .bit_field_ty) {
            const bf_backing = self.pool.unwrapUnderlyingType(TypeId.fromInt(self.pool.getNode(cur_ty).lhs));
            if (bf_backing.isIntegerPrimitive()) {
                cur_hir = try self.emitNode(.{
                    .tag = .hir_cast,
                    .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                    .type_id = bf_backing,
                    .origin_token = tok,
                    .data = .{ .lhs = cur_hir.asInt(), .rhs = @backingInt(HirCastKind.int_to_int) },
                }, .none);
                cur_ty = bf_backing;
            }
        }
        if (cur_ty == .bool_ty or cur_ty == .i8_ty or cur_ty == .u8_ty or
            cur_ty == .i16_ty or cur_ty == .u16_ty)
        {
            return self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                .type_id = .i32_ty,
                .origin_token = tok,
                .data = .{ .lhs = cur_hir.asInt(), .rhs = @backingInt(HirCastKind.int_to_int) },
            }, .none);
        }
        if (cur_ty == .f32_ty) {
            return self.emitNode(.{
                .tag = .hir_cast,
                .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                .type_id = .f64_ty,
                .origin_token = tok,
                .data = .{ .lhs = cur_hir.asInt(), .rhs = @backingInt(HirCastKind.float_to_float) },
            }, .none);
        }
        return cur_hir;
    }

    /// Unwraps explicit `&place` / `&mut place` / `&out place` address-of wrappers on `.inout_mode`/`.set_mode` arguments.
    fn unwrapPlaceProjectionArg(self: *const HirLowerer, arg_hir: HirIndex, mode: ParamMode) HirIndex {
        if ((mode != .inout_mode and mode != .set_mode) or arg_hir.isNone()) return arg_hir;
        var inner_hir = arg_hir;
        var cur_node = self.store.getNode(inner_hir);
        if (cur_node.tag == .hir_cast and cur_node.data.rhs == @backingInt(HirCastKind.ref_coerce)) {
            inner_hir = HirIndex.fromInt(cur_node.data.lhs);
            cur_node = self.store.getNode(inner_hir);
        }
        if (cur_node.tag == .hir_unary_op) {
            const un_op: HirUnaryOp = @fromBackingInt(@intCast(@as(u8, @truncate(cur_node.data.lhs))));
            if (un_op == .addr_of or un_op == .addr_of_mut) {
                inner_hir = HirIndex.fromInt(cur_node.data.rhs);
            }
        }
        return inner_hir;
    }

    /// Synthesizes a closure HIR node for a trailing `{ … }` `@builder` or `TaskGroup.spawn` block (`SE-20`, `SE-22`).
    fn lowerBuilderTrailingBlockClosure(
        self: *HirLowerer,
        block_id: NodeIndex,
        state_ty: TypeId,
        closure_sig_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!HirIndex {
        const sig_view = self.pool.getFnSignatureView(closure_sig_ty);
        const has_builder_param = state_ty != .unit_ty and
            (if (sig_view) |sv| sv.paramCount() >= 1 else true);
        const ret_ty = if (sig_view) |sv|
            self.concreteType(sv.ret_ty)
        else blk_ret: {
            const blk_ty = self.nodeType(block_id);
            break :blk_ret if (!blk_ty.isError()) self.concreteType(blk_ty) else .unit_ty;
        };
        const out_clos_ty = if (!closure_sig_ty.isError())
            self.concreteType(closure_sig_ty)
        else blk_cty: {
            if (has_builder_param) {
                const p_ref = try self.pool.internRef(self.concreteType(state_ty), true);
                break :blk_cty try self.pool.internClosureSignatureExt(
                    &[1]TypeId{p_ref},
                    &[1]ParamMode{.let_mode},
                    ret_ty,
                    .{},
                    .copy_tier,
                    false,
                    false,
                    true,
                );
            }
            break :blk_cty try self.pool.internClosureSignatureExt(
                &.{},
                &.{},
                ret_ty,
                .{},
                .copy_tier,
                false,
                false,
                true,
            );
        };

        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_loop_id = self.current_loop_id;
        const saved_loop_floor = self.closure_loop_stack_floor;
        const saved_in_ct_for = self.is_in_comptime_for;
        const was_in_cond_scope = self.is_in_cond_scope;
        const saved_ceil = self.closure_outer_local_ceil;
        const saved_caller_loc = self.active_caller_loc_local;
        const saved_captures_len = self.active_closure_captures.items.len;
        const local_checkpoint = self.local_shadow_log.items.len;
        defer {
            self.popLexicalLocalsTo(local_checkpoint);
            self.active_closure_captures.shrinkRetainingCapacity(saved_captures_len);
            self.active_caller_loc_local = saved_caller_loc;
            self.closure_outer_local_ceil = saved_ceil;
            self.is_in_cond_scope = was_in_cond_scope;
            self.is_in_comptime_for = saved_in_ct_for;
            self.closure_loop_stack_floor = saved_loop_floor;
            self.current_loop_id = saved_loop_id;
            self.current_fn_ret_ty = saved_ret_ty;
        }

        const return_local_id = try self.store.appendLocal(.{
            .name = .empty,
            .type_id = ret_ty,
            .decl_span = self.astSpan(block_id),
            .mode = .set_mode,
            .is_mut = true,
            .is_param = false,
            .is_temp = true,
        });
        const param_local_start: u32 = @intCast(self.store.locals.items.len);
        self.closure_outer_local_ceil = return_local_id;
        try self.closure_frame_stack.append(self.allocator, .{ .ceil = return_local_id });
        defer {
            var popped_frame = self.closure_frame_stack.pop().?;
            popped_frame.captures.deinit(self.allocator);
        }
        self.active_caller_loc_local = null;
        self.current_fn_ret_ty = ret_ty;
        self.current_loop_id = null;
        self.closure_loop_stack_floor = self.loop_stack.items.len;
        self.is_in_comptime_for = false;
        self.is_in_cond_scope = false;

        var builder_slot_opt: ?u32 = null;
        if (has_builder_param) {
            const b_param_ty = if (sig_view) |sv|
                (if (sv.paramCount() >= 1) self.concreteType(sv.getParamType(0)) else try self.pool.internRef(self.concreteType(state_ty), true))
            else
                try self.pool.internRef(self.concreteType(state_ty), true);
            const b_slot = try self.store.appendLocal(.{
                .name = .empty,
                .type_id = b_param_ty,
                .decl_span = self.astSpan(block_id),
                .mode = .let_mode,
                .is_mut = false,
                .is_param = true,
                .is_temp = true,
            });
            builder_slot_opt = b_slot;
            try self.builder_scope_stack.append(self.allocator, .{
                .state_ty = self.concreteType(state_ty),
                .local_id = b_slot,
            });
        }
        defer if (builder_slot_opt != null) {
            _ = self.builder_scope_stack.pop();
        };

        const is_move_clos = if (sig_view) |sv| sv.capture_tier != .copy_tier else false;
        const is_async_clos = if (sig_view) |sv| sv.is_async else false;
        const fn_meta_idx: u32 = @intCast(self.store.functions.items.len);
        const clos_ord = self.closure_ordinal_in_owner;
        self.closure_ordinal_in_owner += 1;
        const file_bits: u32 = if (!self.store.file_id.isNone()) self.store.file_id.asInt() & 0x01FF else 0;
        const owner_bits: u32 = if (!self.active_owner_def_id.isNone())
            @as(u32, self.active_owner_def_id.itemIndex()) & 0x0FFF
        else
            0x0FFF;
        const synth_closure_def = DefId.fromInt(
            0x5000_0000 + (file_bits << 20) + (owner_bits << 8) + (clos_ord & 0x00FF),
        );
        try self.store.functions.append(self.allocator, .{
            .def_id = synth_closure_def,
            .fn_ty = out_clos_ty,
            .ret_ty = ret_ty,
            .return_local_id = return_local_id,
            .param_local_start = param_local_start,
            .param_len = if (has_builder_param) 1 else 0,
            .is_local_closure = !is_move_clos,
            .is_move_closure = is_move_clos,
            .is_async = is_async_clos,
        });

        const body_hir = try self.lowerBlockExpr(block_id, ret_ty, true);
        const cap_slice = self.closure_frame_stack.items[self.closure_frame_stack.items.len - 1].captures.items;
        const cap_extra_start = if (cap_slice.len > 0) try self.store.appendExtraSlice(cap_slice) else 0;

        self.store.functions.items[fn_meta_idx].body_hir = body_hir;
        self.store.functions.items[fn_meta_idx].total_local_len =
            @intCast(self.store.locals.items.len - return_local_id);
        self.store.functions.items[fn_meta_idx].capture_extra_start = cap_extra_start;
        self.store.functions.items[fn_meta_idx].capture_len = @intCast(cap_slice.len / 2);

        return self.emitNode(.{
            .tag = .hir_closure,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = out_clos_ty,
            .origin_token = tok,
            .data = .{ .lhs = fn_meta_idx, .rhs = body_hir.asInt() },
        }, block_id);
    }

    /// Finds the innermost active `@builder` scope local matching `sig_view`'s parameter `0` (`SE-22`).
    fn findMatchingBuilderLocal(self: *HirLowerer, sig_view: ?type_system.FnSignatureView, tok: TokenIndex) !?HirIndex {
        if (self.builder_scope_stack.items.len == 0) return null;
        const wanted_state_ty: ?TypeId = if (sig_view) |sv| blk_w: {
            if (sv.paramCount() == 0) break :blk_w null;
            break :blk_w self.unwrapRefType(self.pool.unwrapUnderlyingType(sv.getParamType(0)));
        } else null;
        const wanted_base: ?TypeId = if (wanted_state_ty) |ws|
            self.pool.unwrapNominalInstantiationBase(ws)
        else
            null;

        var idx = self.builder_scope_stack.items.len;
        while (idx > 0) {
            idx -= 1;
            const entry = self.builder_scope_stack.items[idx];
            if (wanted_state_ty == null or
                entry.state_ty == wanted_state_ty.? or
                self.pool.unwrapNominalInstantiationBase(entry.state_ty) == wanted_base.?)
            {
                return try self.emitVarRef(entry.local_id, tok, .none);
            }
        }
        return null;
    }

    /// Evaluates positional, named, and omitted default arguments for a direct `fn_sym` call (`SE-07`).
    /// Preserves call-site evaluation order for supplied arguments followed by formal order for omitted defaults.
    fn lowerMappedDirectArgs(
        self: *HirLowerer,
        call_ast_id: NodeIndex,
        callee_sym: SymbolIndex,
        callee_sig_ty: TypeId,
        has_self_receiver: bool,
        raw_val_args: []const NodeIndex,
        tok: TokenIndex,
        out_seq_stmts: *std.ArrayListUnmanaged(u32),
        out_arg_hirs: *std.ArrayListUnmanaged(HirIndex),
    ) !void {
        const sig_view = self.pool.getFnSignatureView(callee_sig_ty);
        const param_offset: usize = if (has_self_receiver) 1 else 0;

        const builder_block_state_opt = if (self.side_tables) |st|
            st.getBuilderBlockStateType(call_ast_id)
        else
            null;

        if (self.side_tables) |tables| {
            if (tables.getCallArgMapping(call_ast_id)) |mapping| {
                const formal_non_self: usize = mapping.total_params;
                var total_non_self: usize = formal_non_self;
                for (mapping.provided_slots) |slot| {
                    if (@as(usize, slot.param_index) + 1 > total_non_self) {
                        total_non_self = @as(usize, slot.param_index) + 1;
                    }
                }
                const slot_hirs = try self.allocator.alloc(HirIndex, total_non_self);
                defer self.allocator.free(slot_hirs);
                @memset(slot_hirs, .none);
                const slot_locals = try self.allocator.alloc(u32, total_non_self);
                defer self.allocator.free(slot_locals);
                @memset(slot_locals, NONE_U32);

                const has_omitted_default = mapping.provided_slots.len < formal_non_self;
                const must_sequence = has_self_receiver or mapping.has_reordered_or_default or has_omitted_default;
                for (mapping.provided_slots) |slot| {
                    if (slot.param_index >= total_non_self) continue;
                    const full_idx = param_offset + @as(usize, slot.param_index);
                    const p_ty = if (sig_view) |sv|
                        (if (full_idx < sv.paramCount()) sv.getParamType(full_idx) else .err_ty)
                    else
                        .err_ty;
                    const p_mode = if (sig_view) |sv|
                        (if (full_idx < sv.paramCount()) sv.getParamMode(full_idx) else .let_mode)
                    else
                        .let_mode;

                    const is_mut_arg = p_mode == .inout_mode or p_mode == .set_mode;
                    const unwrapped_arg_ast = self.unwrapCallArgAst(slot.arg_ast_node);
                    var arg_hir = if (builder_block_state_opt != null and
                        !unwrapped_arg_ast.isNone() and
                        self.ast_arena.getNode(unwrapped_arg_ast).tag == .block)
                        try self.lowerBuilderTrailingBlockClosure(
                            unwrapped_arg_ast,
                            builder_block_state_opt.?,
                            p_ty,
                            tok,
                        )
                    else
                        try self.lowerPlaceWithMutCtx(unwrapped_arg_ast, p_ty, is_mut_arg);
                    if (is_mut_arg) {
                        arg_hir = self.unwrapPlaceProjectionArg(arg_hir, p_mode);
                    } else {
                        arg_hir = try self.applyCVariadicPromotionIfNeeded(arg_hir, sig_view, full_idx, tok);
                    }
                    if (!must_sequence) {
                        slot_hirs[slot.param_index] = arg_hir;
                    } else if (is_mut_arg) {
                        if (self.store.getNode(arg_hir).tag == .hir_var_ref) {
                            slot_hirs[slot.param_index] = arg_hir;
                            slot_locals[slot.param_index] = self.store.getNode(arg_hir).data.lhs;
                        } else {
                            const place_ty = self.store.getNode(arg_hir).type_id;
                            const ptr_ty = try self.pool.internRef(place_ty, true);
                            const addr_hir = try self.emitSyntheticAddrOf(arg_hir, ptr_ty, true, tok);
                            const ptr_tmp = try self.allocTempLocal(ptr_ty, tok, false);
                            try out_seq_stmts.append(
                                self.allocator,
                                (try self.emitLocalDeclNode(ptr_tmp, addr_hir, tok)).asInt(),
                            );
                            slot_hirs[slot.param_index] = try self.emitNode(.{
                                .tag = .hir_unary_op,
                                .flags = .{ .category = .place_mut, .is_synthetic = true },
                                .type_id = place_ty,
                                .origin_token = tok,
                                .data = .{
                                    .lhs = @backingInt(HirUnaryOp.deref),
                                    .rhs = (try self.emitVarRef(ptr_tmp, tok, .none)).asInt(),
                                },
                            }, .none);
                        }
                    } else {
                        const tmp_slot = try self.allocTempLocal(self.store.getNode(arg_hir).type_id, tok, false);
                        try out_seq_stmts.append(
                            self.allocator,
                            (try self.emitLocalDeclNode(tmp_slot, arg_hir, tok)).asInt(),
                        );
                        slot_locals[slot.param_index] = tmp_slot;
                        slot_hirs[slot.param_index] = try self.emitVarRef(tmp_slot, tok, .none);
                    }
                }

                for (0..formal_non_self) |rel_idx| {
                    if (!slot_hirs[rel_idx].isNone()) continue;
                    const full_idx = param_offset + rel_idx;
                    const p_ty = if (sig_view) |sv|
                        (if (full_idx < sv.paramCount()) sv.getParamType(full_idx) else .err_ty)
                    else
                        .err_ty;
                    const def_hir = try self.lowerCalleeDefaultExpr(
                        callee_sym,
                        full_idx,
                        param_offset,
                        slot_locals,
                        p_ty,
                        tok,
                    );
                    const tmp_slot = try self.allocTempLocal(self.store.getNode(def_hir).type_id, tok, false);
                    try out_seq_stmts.append(
                        self.allocator,
                        (try self.emitLocalDeclNode(tmp_slot, def_hir, tok)).asInt(),
                    );
                    slot_locals[rel_idx] = tmp_slot;
                    slot_hirs[rel_idx] = try self.emitVarRef(tmp_slot, tok, .none);
                }

                for (slot_hirs) |sh| {
                    if (!sh.isNone()) try out_arg_hirs.append(self.allocator, sh);
                }
                return;
            }
        }

        // Fallback when `side_tables` are absent (`lowerResolvedSourceOnly` tests):
        const specs_opt = self.sym_table.fn_param_specs.get(callee_sym.asInt());
        const formal_total: usize = if (sig_view) |sv|
            sv.paramCount()
        else if (specs_opt) |specs|
            specs.len
        else
            param_offset + raw_val_args.len;
        const formal_non_self_fb: usize = formal_total -| param_offset;
        const total_non_self: usize = @max(formal_non_self_fb, raw_val_args.len);
        const slot_hirs = try self.allocator.alloc(HirIndex, total_non_self);
        defer self.allocator.free(slot_hirs);
        @memset(slot_hirs, .none);
        const slot_locals = try self.allocator.alloc(u32, total_non_self);
        defer self.allocator.free(slot_locals);
        @memset(slot_locals, NONE_U32);

        var has_any_named = false;
        for (raw_val_args) |raw_arg| {
            if (!raw_arg.isNone() and raw_arg.asInt() < self.ast_arena.countNodes() and
                self.ast_arena.getNode(raw_arg).tag == .named_arg)
            {
                has_any_named = true;
                break;
            }
        }
        const has_omitted_fallback = raw_val_args.len < formal_non_self_fb;
        const is_seq_fallback_required = has_self_receiver or has_any_named or has_omitted_fallback;

        for (raw_val_args, 0..) |raw_arg, call_i| {
            var target_rel: usize = call_i;
            if (!raw_arg.isNone() and raw_arg.asInt() < self.ast_arena.countNodes()) {
                const raw_node = self.ast_arena.getNode(raw_arg);
                if (raw_node.tag == .named_arg and !raw_node.main_token.isNone()) {
                    const lbl = symbol_resolver.extractTokenSlice(self.source, self.tokens, raw_node.main_token);
                    if (specs_opt) |specs| {
                        for (param_offset..specs.len) |full_k| {
                            if (std.mem.eql(u8, specs[full_k].name_text, lbl)) {
                                target_rel = full_k - param_offset;
                                break;
                            }
                        }
                    }
                }
            }
            if (target_rel >= total_non_self) continue;
            const full_idx = param_offset + target_rel;
            const p_ty = if (sig_view) |sv|
                (if (full_idx < sv.paramCount()) sv.getParamType(full_idx) else .err_ty)
            else
                .err_ty;
            const p_mode = if (sig_view) |sv|
                (if (full_idx < sv.paramCount()) sv.getParamMode(full_idx) else .let_mode)
            else
                .let_mode;
            const is_mut_arg = p_mode == .inout_mode or p_mode == .set_mode;
            const unwrapped_arg_ast = self.unwrapCallArgAst(raw_arg);
            var arg_hir = if (builder_block_state_opt != null and
                !unwrapped_arg_ast.isNone() and
                self.ast_arena.getNode(unwrapped_arg_ast).tag == .block)
                try self.lowerBuilderTrailingBlockClosure(
                    unwrapped_arg_ast,
                    builder_block_state_opt.?,
                    p_ty,
                    tok,
                )
            else
                try self.lowerPlaceWithMutCtx(unwrapped_arg_ast, p_ty, is_mut_arg);
            if (is_mut_arg) {
                arg_hir = self.unwrapPlaceProjectionArg(arg_hir, p_mode);
            } else {
                arg_hir = try self.applyCVariadicPromotionIfNeeded(arg_hir, sig_view, full_idx, tok);
            }
            if (is_seq_fallback_required and !is_mut_arg) {
                const tmp_slot = try self.allocTempLocal(self.store.getNode(arg_hir).type_id, tok, false);
                try out_seq_stmts.append(
                    self.allocator,
                    (try self.emitLocalDeclNode(tmp_slot, arg_hir, tok)).asInt(),
                );
                slot_locals[target_rel] = tmp_slot;
                slot_hirs[target_rel] = try self.emitVarRef(tmp_slot, tok, .none);
            } else {
                if (self.store.getNode(arg_hir).tag == .hir_var_ref) {
                    slot_locals[target_rel] = self.store.getNode(arg_hir).data.lhs;
                }
                slot_hirs[target_rel] = arg_hir;
            }
        }

        for (0..formal_non_self_fb) |rel_idx| {
            if (!slot_hirs[rel_idx].isNone()) continue;
            const full_idx = param_offset + rel_idx;
            const p_ty = if (sig_view) |sv|
                (if (full_idx < sv.paramCount()) sv.getParamType(full_idx) else .err_ty)
            else
                .err_ty;
            const def_hir = try self.lowerCalleeDefaultExpr(
                callee_sym,
                full_idx,
                param_offset,
                slot_locals,
                p_ty,
                tok,
            );
            const tmp_slot = try self.allocTempLocal(self.store.getNode(def_hir).type_id, tok, false);
            try out_seq_stmts.append(
                self.allocator,
                (try self.emitLocalDeclNode(tmp_slot, def_hir, tok)).asInt(),
            );
            slot_locals[rel_idx] = tmp_slot;
            slot_hirs[rel_idx] = try self.emitVarRef(tmp_slot, tok, .none);
        }
        for (slot_hirs) |sh| {
            if (!sh.isNone()) try out_arg_hirs.append(self.allocator, sh);
        }
    }

    /// Lowers built-in `Option.Some(x)`, `Result.Ok(x)`, `Result.Err(e)`, and `Enum.Variant(args)` under Unified `.`.
    fn tryLowerStaticSumConstructor(
        self: *HirLowerer,
        expr_id: NodeIndex,
        member_name: []const u8,
        val_args: []const NodeIndex,
        target_ty: TypeId,
        tok: TokenIndex,
    ) !?HirIndex {
        const concrete_target = self.concreteType(if (!target_ty.isError()) target_ty else self.nodeType(expr_id));
        if (concrete_target.isError()) return null;
        const unwrapped_ty = self.pool.unwrapUnderlyingType(concrete_target);
        const ty_node = self.pool.getNode(unwrapped_ty);

        switch (ty_node.tag) {
            .optional_ty => {
                if (!std.mem.eql(u8, member_name, "Some")) return null;
                const payload_ty = TypeId.fromInt(ty_node.lhs);
                const payload_hir = if (val_args.len >= 1)
                    try self.lowerExpr(self.unwrapCallArgAst(val_args[0]), payload_ty)
                else
                    try self.emitUnitConst(tok, .none);
                const extra_idx = try self.store.appendLenPrefixedExtra(&[1]u32{payload_hir.asInt()});
                var out_hir = try self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue },
                    .type_id = unwrapped_ty,
                    .origin_token = tok,
                    .data = .{
                        .lhs = @as(u32, @backingInt(HirConstructKind.optional_some)) | (1 << 8),
                        .rhs = extra_idx,
                    },
                }, expr_id);
                if (unwrapped_ty != concrete_target) {
                    out_hir = try self.emitNode(.{
                        .tag = .hir_cast,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = concrete_target,
                        .origin_token = tok,
                        .data = .{ .lhs = out_hir.asInt(), .rhs = @backingInt(HirCastKind.distinct_wrap) },
                    }, .none);
                }
                return out_hir;
            },
            .result_ty => {
                const is_ok = std.mem.eql(u8, member_name, "Ok");
                const is_err = std.mem.eql(u8, member_name, "Err");
                if (!is_ok and !is_err) return null;
                const payload_ty = TypeId.fromInt(if (is_ok) ty_node.lhs else ty_node.rhs);
                const payload_hir = if (val_args.len >= 1)
                    try self.lowerExpr(self.unwrapCallArgAst(val_args[0]), payload_ty)
                else
                    try self.emitUnitConst(tok, .none);
                const extra_idx = try self.store.appendLenPrefixedExtra(&[1]u32{payload_hir.asInt()});
                const kind: HirConstructKind = if (is_ok) .result_ok else .result_err;
                const tag_shift: u32 = if (is_ok) 0 else (1 << 8);
                var out_hir = try self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue },
                    .type_id = unwrapped_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = @as(u32, @backingInt(kind)) | tag_shift, .rhs = extra_idx },
                }, expr_id);
                if (unwrapped_ty != concrete_target) {
                    out_hir = try self.emitNode(.{
                        .tag = .hir_cast,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = concrete_target,
                        .origin_token = tok,
                        .data = .{ .lhs = out_hir.asInt(), .rhs = @backingInt(HirCastKind.distinct_wrap) },
                    }, .none);
                }
                return out_hir;
            },
            .enum_ty => {
                const enum_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(ty_node.rhs)).*;
                if (enum_sym.target_scope.isNone()) return null;
                const var_name_id = self.interner.lookup(member_name) orelse return null;
                const found_idx = self.sym_table.lookupInScopeDirect(
                    enum_sym.target_scope,
                    var_name_id,
                    NamespaceMask.VALUE_ONLY,
                );
                if (found_idx.isNone()) return null;
                const v_sym = self.sym_table.getSymbol(found_idx).*;
                if (v_sym.kind != .enum_variant_sym) return null;
                const enum_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, unwrapped_ty);
                const subst_var_ty = try enum_subst.applyMut(self.allocator, self.pool, v_sym.type_id);
                var arg_hirs: std.ArrayListUnmanaged(u32) = .empty;
                defer arg_hirs.deinit(self.allocator);
                if (val_args.len == 1) {
                    const a0 = self.unwrapCallArgAst(val_args[0]);
                    try arg_hirs.append(self.allocator, (try self.lowerExpr(a0, subst_var_ty)).asInt());
                } else {
                    const tup_elems = self.pool.getTupleElements(subst_var_ty);
                    for (val_args, 0..) |arg_id, i| {
                        const sub_ty = if (i < tup_elems.len) TypeId.fromInt(tup_elems[i]) else .err_ty;
                        const unwrapped_arg = self.unwrapCallArgAst(arg_id);
                        try arg_hirs.append(self.allocator, (try self.lowerExpr(unwrapped_arg, sub_ty)).asInt());
                    }
                }
                const extra_idx = try self.store.appendLenPrefixedExtra(arg_hirs.items);
                return try self.emitNode(.{
                    .tag = .hir_construct,
                    .flags = .{ .category = .rvalue },
                    .type_id = concrete_target,
                    .origin_token = tok,
                    .data = .{
                        .lhs = @as(u32, @backingInt(HirConstructKind.enum_variant)) |
                            (@as(u32, v_sym.member_ordinal) << 8),
                        .rhs = extra_idx,
                    },
                }, expr_id);
            },
            else => return null,
        }
    }

    /// Reverses a fixed `[u8; byte_count]` array expression in `HIR` for big-endian byte conversions.
    fn reverseByteArrayHir(
        self: *HirLowerer,
        arr_hir: HirIndex,
        arr_ty: TypeId,
        byte_count: usize,
        tok: TokenIndex,
        out_stmts: *std.ArrayListUnmanaged(u32),
    ) !HirIndex {
        if (byte_count <= 1) return arr_hir;
        const arr_slot = try self.allocTempLocal(arr_ty, tok, false);
        try out_stmts.append(self.allocator, (try self.emitLocalDeclNode(arr_slot, arr_hir, tok)).asInt());
        var elems: std.ArrayListUnmanaged(u32) = .empty;
        defer elems.deinit(self.allocator);
        var rev_i: usize = byte_count;
        while (rev_i > 0) {
            rev_i -= 1;
            const idx_const = try self.emitConstVal(.{ .int_val = @intCast(rev_i) }, .usize_ty, tok, .none, true);
            const proj = try self.emitNode(.{
                .tag = .hir_index_proj,
                .flags = .{ .category = .place_imm, .is_synthetic = true },
                .type_id = .u8_ty,
                .origin_token = tok,
                .data = .{
                    .lhs = (try self.emitVarRef(arr_slot, tok, .none)).asInt(),
                    .rhs = idx_const.asInt(),
                },
            }, .none);
            try elems.append(self.allocator, proj.asInt());
        }
        const extra_idx = try self.store.appendLenPrefixedExtra(elems.items);
        return self.emitNode(.{
            .tag = .hir_construct,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = arr_ty,
            .origin_token = tok,
            .data = .{ .lhs = @backingInt(HirConstructKind.array_elements), .rhs = extra_idx },
        }, .none);
    }

    /// Lowers built-in integer and float endian helpers (`from_{le,be,ne}_bytes`, `to_{le,be,ne}_bytes`).
    fn tryLowerPrimitiveEndianHelper(
        self: *HirLowerer,
        expr_id: NodeIndex,
        static_or_recv_ty: TypeId,
        is_static_call: bool,
        recv_id: NodeIndex,
        member_name: []const u8,
        val_args: []const NodeIndex,
        tok: TokenIndex,
    ) !?HirIndex {
        const raw_base = self.pool.unwrapRefinementBase(self.pool.unwrapUnderlyingType(static_or_recv_ty));
        const prim_ty: TypeId = switch (raw_base) {
            .untyped_int_ty => .i32_ty,
            .untyped_float_ty => .f64_ty,
            else => raw_base,
        };
        if (!prim_ty.isIntegerPrimitive() and !prim_ty.isFloatPrimitive()) return null;
        const byte_count: usize = switch (prim_ty) {
            .i8_ty, .u8_ty => 1,
            .i16_ty, .u16_ty => 2,
            .i32_ty, .u32_ty, .f32_ty => 4,
            .i64_ty, .u64_ty, .f64_ty => 8,
            .i128_ty, .u128_ty => 16,
            .isize_ty, .usize_ty => self.store.target_layout.ptr_byte_size,
            else => return null,
        };
        const byte_arr_ty = try self.pool.internArray(.u8_ty, @intCast(byte_count), false);

        if (is_static_call and val_args.len == 1 and
            (std.mem.eql(u8, member_name, "from_le_bytes") or
                std.mem.eql(u8, member_name, "from_be_bytes") or
                std.mem.eql(u8, member_name, "from_ne_bytes")))
        {
            const is_be = std.mem.eql(u8, member_name, "from_be_bytes");
            const out_ty = if (!static_or_recv_ty.isError() and
                raw_base != .untyped_int_ty and
                raw_base != .untyped_float_ty)
                static_or_recv_ty
            else
                prim_ty;
            var stmts: std.ArrayListUnmanaged(u32) = .empty;
            defer stmts.deinit(self.allocator);
            var bytes_hir = try self.lowerExpr(self.unwrapCallArgAst(val_args[0]), byte_arr_ty);
            bytes_hir = try self.autoDerefPlace(bytes_hir, tok);
            if (is_be) {
                bytes_hir = try self.reverseByteArrayHir(bytes_hir, byte_arr_ty, byte_count, tok, &stmts);
            }
            const extra_idx = try self.store.appendExtraSlice(&[4]u32{ 1, 1, out_ty.toU32(), bytes_hir.asInt() });
            const cast_hir = try self.emitNode(.{
                .tag = .hir_intrinsic_call,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = out_ty,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(IntrinsicKind.bit_cast), .rhs = extra_idx },
            }, expr_id);
            if (stmts.items.len > 0) return try self.emitSyntheticBlock(stmts.items, cast_hir, out_ty, tok);
            return cast_hir;
        }

        if (!is_static_call and val_args.len == 0 and
            (std.mem.eql(u8, member_name, "to_le_bytes") or
                std.mem.eql(u8, member_name, "to_be_bytes") or
                std.mem.eql(u8, member_name, "to_ne_bytes")))
        {
            const is_be = std.mem.eql(u8, member_name, "to_be_bytes");
            var stmts: std.ArrayListUnmanaged(u32) = .empty;
            defer stmts.deinit(self.allocator);
            const recv_expect: TypeId = if (raw_base == .untyped_int_ty or raw_base == .untyped_float_ty)
                prim_ty
            else
                .err_ty;
            const raw_recv = try self.lowerExpr(recv_id, recv_expect);
            const deref_recv = try self.autoDerefPlace(raw_recv, tok);
            const extra_idx = try self.store.appendExtraSlice(
                &[4]u32{ 1, 1, byte_arr_ty.toU32(), deref_recv.asInt() },
            );
            var out_hir = try self.emitNode(.{
                .tag = .hir_intrinsic_call,
                .flags = .{ .category = .rvalue, .is_synthetic = true },
                .type_id = byte_arr_ty,
                .origin_token = tok,
                .data = .{ .lhs = @backingInt(IntrinsicKind.bit_cast), .rhs = extra_idx },
            }, expr_id);
            if (is_be) {
                out_hir = try self.reverseByteArrayHir(out_hir, byte_arr_ty, byte_count, tok, &stmts);
            }
            if (stmts.items.len > 0) return try self.emitSyntheticBlock(stmts.items, out_hir, byte_arr_ty, tok);
            return out_hir;
        }
        return null;
    }

    /// Lowers direct, generic, `@overload`, `subscript`, and `@intrinsic` calls (`DR-02` §2.2, `DR-05` §3.3 & `SE-07`).
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

        // [2] Enum tuple-variant, `@constructor` nominal call (`SE-22`), or static `Option.Some` / `Result.Ok` / endian helper:
        const call_sym_idx = self.nodeSymbol(expr_id);
        var resolved_sym_idx = if (!call_sym_idx.isNone()) call_sym_idx else self.nodeSymbol(callee_ast_id);
        if (resolved_sym_idx.isNone() and callee_ast.tag == .ident_expr and !callee_ast.main_token.isNone()) {
            const callee_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, callee_ast.main_token);
            if (self.interner.lookup(callee_lex)) |callee_id| {
                if (!self.active_name_to_local.contains(callee_id.asInt())) {
                    switch (self.sym_table.lookupLexical(self.current_scope, callee_id, NamespaceMask.TYPE_OR_VALUE)) {
                        .found => |found_sym| resolved_sym_idx = found_sym,
                        else => {},
                    }
                }
            }
        }
        if (!resolved_sym_idx.isNone()) {
            const cand_sym = self.sym_table.getSymbol(resolved_sym_idx).*;
            if ((cand_sym.kind == .struct_sym or cand_sym.kind == .enum_sym or cand_sym.kind == .distinct_type_sym) and
                !cand_sym.target_scope.isNone())
            {
                for (self.sym_table.getScopeMembers(cand_sym.target_scope)) |mem_idx| {
                    if (!self.isSymbolCfgEnabled(mem_idx)) continue;
                    const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                    if (mem_sym.kind == .fn_sym and mem_sym.extra_flags.is_constructor) {
                        resolved_sym_idx = mem_idx;
                        break;
                    }
                }
            }
        }
        if (resolved_sym_idx.isNone() and callee_ast.tag == .field_access and
            callee_ast.lhs.tag == .node and callee_ast.rhs.tag == .token)
        {
            const recv_id = NodeIndex.fromInt(callee_ast.lhs.payload);
            const member_name = symbol_resolver.extractTokenSlice(
                self.source,
                self.tokens,
                TokenIndex.fromInt(callee_ast.rhs.payload),
            );
            const static_kind = self.resolveStaticDotTargetAst(recv_id);
            if (static_kind != .none) {
                resolved_sym_idx = self.lookupStaticMemberSymbolFallback(recv_id, member_name);
                if (resolved_sym_idx.isNone() and static_kind == .type_ns) {
                    if (self.resolveBuiltinPrimitiveAst(recv_id)) |prim_ty| {
                        if (try self.tryLowerPrimitiveEndianHelper(
                            expr_id,
                            prim_ty,
                            true,
                            recv_id,
                            member_name,
                            val_args,
                            tok,
                        )) |endian_hir| return endian_hir;
                    }
                    if (try self.tryLowerStaticSumConstructor(
                        expr_id,
                        member_name,
                        val_args,
                        target_ty,
                        tok,
                    )) |ctor_hir| return ctor_hir;
                }
            }
        }
        if (!resolved_sym_idx.isNone()) {
            const sym = self.sym_table.getSymbol(resolved_sym_idx).*;
            if (sym.kind == .enum_variant_sym) {
                const enum_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, target_ty);
                const subst_var_ty = try enum_subst.applyMut(self.allocator, self.pool, sym.type_id);
                var arg_hirs: std.ArrayListUnmanaged(u32) = .empty;
                defer arg_hirs.deinit(self.allocator);
                if (val_args.len == 1) {
                    const a0 = self.unwrapCallArgAst(val_args[0]);
                    try arg_hirs.append(self.allocator, (try self.lowerExpr(a0, subst_var_ty)).asInt());
                } else {
                    const tup_elems = self.pool.getTupleElements(subst_var_ty);
                    for (val_args, 0..) |arg_id, i| {
                        const sub_ty = if (i < tup_elems.len) TypeId.fromInt(tup_elems[i]) else .err_ty;
                        const unwrapped_arg = self.unwrapCallArgAst(arg_id);
                        try arg_hirs.append(self.allocator, (try self.lowerExpr(unwrapped_arg, sub_ty)).asInt());
                    }
                }
                const extra_idx = try self.store.appendLenPrefixedExtra(arg_hirs.items);
                return try self.emitNode(.{
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

        // [2b] Structured `core.async` entry functions (`yield_now`, `block_on`, `task_group`):
        if (try self.tryLowerStructuredAsyncEntryCall(
            expr_id,
            resolved_sym_idx,
            callee_ast_id,
            null,
            val_args,
            target_ty,
            tok,
        )) |async_entry_hir| return async_entry_hir;

        // [3] Resolve concrete `@overload`, named/default `fn_sym` call (`SE-07`), or indirect closure/fn-ptr call:
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

        if (is_direct_sym) {
            const has_implicit_builder = if (self.side_tables) |tables|
                tables.getImplicitBuilderParamIndex(expr_id) != null
            else
                false;
            var ordered_args: std.ArrayListUnmanaged(HirIndex) = .empty;
            defer ordered_args.deinit(self.allocator);
            try self.lowerMappedDirectArgs(
                expr_id,
                resolved_sym_idx,
                callee_sig_ty,
                has_implicit_builder,
                val_args,
                tok,
                &seq_stmts,
                &ordered_args,
            );
            if (has_implicit_builder) {
                const self_mode = if (sig_view) |sv|
                    (if (sv.paramCount() > 0) sv.getParamMode(0) else .let_mode)
                else
                    .let_mode;
                const self_ty = if (sig_view) |sv|
                    (if (sv.paramCount() > 0) sv.getParamType(0) else .err_ty)
                else
                    .err_ty;
                const raw_builder_ref = (try self.findMatchingBuilderLocal(sig_view, tok)) orelse
                    try self.emitErrorHole(tok, expr_id, self_ty);
                const adj_builder = if (!self_ty.isError())
                    try self.adjustReceiverForParam(raw_builder_ref, self_ty, tok)
                else
                    raw_builder_ref;
                try wrapped_args.append(
                    self.allocator,
                    (try self.wrapArgProjection(adj_builder, self_mode, tok)).asInt(),
                );
            }
            const param_offset: usize = if (has_implicit_builder) 1 else 0;
            for (ordered_args.items, 0..) |arg_hir, i| {
                const param_idx = param_offset + i;
                const p_mode = if (sig_view) |sv|
                    (if (param_idx < sv.paramCount()) sv.getParamMode(param_idx) else .let_mode)
                else
                    .let_mode;
                try wrapped_args.append(self.allocator, (try self.wrapArgProjection(arg_hir, p_mode, tok)).asInt());
            }
        } else {
            const fixed_arity: usize = if (sig_view) |sv| sv.paramCount() else 0;
            const is_c_variadic = if (sig_view) |sv| sv.is_variadic else false;
            const builder_state_ty = if (self.side_tables) |tables|
                tables.getBuilderBlockStateType(expr_id)
            else
                null;
            for (val_args, 0..) |arg_id, i| {
                const unwrapped_arg = self.unwrapCallArgAst(arg_id);
                const p_ty = if (sig_view) |sv|
                    (if (i < fixed_arity) sv.getParamType(i) else .err_ty)
                else
                    .err_ty;
                const p_mode = if (sig_view) |sv|
                    (if (i < fixed_arity) sv.getParamMode(i) else .let_mode)
                else
                    .let_mode;
                var arg_hir: HirIndex = .none;
                if (builder_state_ty != null and i + 1 == val_args.len and
                    self.ast_arena.getNode(unwrapped_arg).tag == .block)
                {
                    arg_hir = try self.lowerBuilderTrailingBlockClosure(
                        unwrapped_arg,
                        builder_state_ty.?,
                        p_ty,
                        tok,
                    );
                } else {
                    const is_mut_arg = p_mode == .inout_mode or p_mode == .set_mode;
                    arg_hir = try self.lowerPlaceWithMutCtx(unwrapped_arg, p_ty, is_mut_arg);
                    arg_hir = self.unwrapPlaceProjectionArg(arg_hir, p_mode);
                    if (is_c_variadic and i >= fixed_arity) {
                        arg_hir = try self.applyCVariadicPromotionIfNeeded(arg_hir, sig_view, i, tok);
                    }
                }
                if (p_mode == .let_mode) {
                    const tmp_slot = try self.allocTempLocal(self.store.getNode(arg_hir).type_id, tok, false);
                    try seq_stmts.append(self.allocator, (try self.emitLocalDeclNode(tmp_slot, arg_hir, tok)).asInt());
                    arg_hir = try self.emitVarRef(tmp_slot, tok, .none);
                }
                try wrapped_args.append(self.allocator, (try self.wrapArgProjection(arg_hir, p_mode, tok)).asInt());
            }
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

        const is_async_call = if (sig_view) |sv| sv.is_async else false;
        const ret_ty = if (!target_ty.isError())
            target_ty
        else if (sig_view) |sv| blk_async_ret: {
            const inner_ret = self.concreteType(sv.ret_ty);
            if (sv.is_async) {
                const prod_id = if (is_direct_sym) resolved_sym_idx.asInt() else 0;
                break :blk_async_ret try self.pool.internFuture(inner_ret, prod_id);
            }
            break :blk_async_ret inner_ret;
        } else .unit_ty;
        const call_hir = if (is_async_call) blk_fut_call: {
            const prod_def = if (is_direct_sym) self.sym_table.getSymbol(resolved_sym_idx).def_id else DefId.NONE;
            const prod_sym = if (is_direct_sym) resolved_sym_idx else SymbolIndex.none;
            break :blk_fut_call try self.emitAsyncFutureMake(
                prod_def,
                prod_sym,
                callee_hir,
                wrapped_args.items,
                self.concreteType(ret_ty),
                tok,
                expr_id,
            );
        } else blk_sync_call: {
            const extra_idx = try self.store.appendLenPrefixedExtra(wrapped_args.items);
            const is_sub = self.isCalleeSubscript(callee_hir);
            const emitted_call = try self.emitNode(.{
                .tag = if (is_sub) .hir_subscript_call else .hir_call,
                .flags = .{
                    .category = if (is_sub) .place_imm else .rvalue,
                    .is_unsafe = self.is_in_unsafe,
                },
                .type_id = ret_ty,
                .origin_token = tok,
                .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
            }, expr_id);
            if (!is_sub) {
                try self.recordCallTypeArgs(expr_id, emitted_call, type_arg_nodes.items);
            }
            break :blk_sync_call emitted_call;
        };

        if (seq_stmts.items.len > 0) {
            return self.emitSyntheticBlock(seq_stmts.items, call_hir, ret_ty, tok);
        }
        return call_hir;
    }

    /// Persists explicit or `TypeChecker`-instantiated generic type arguments for `call_hir` in `store.call_type_args`.
    fn recordCallTypeArgs(
        self: *HirLowerer,
        call_ast_id: NodeIndex,
        call_hir: HirIndex,
        type_arg_nodes: []const NodeIndex,
    ) !void {
        if (call_hir.isNone()) return;
        if (self.side_tables) |tables| {
            if (tables.getCallInstantiation(call_ast_id)) |inst_slice| {
                if (inst_slice.len > 0) {
                    const start_idx: u32 = @intCast(self.store.extra_data.items.len);
                    for (inst_slice) |inst_ty| {
                        try self.store.extra_data.append(self.allocator, self.concreteType(inst_ty).toU32());
                    }
                    try self.store.call_type_args.put(self.allocator, call_hir.asInt(), .{
                        .start = start_idx,
                        .len = @intCast(inst_slice.len),
                    });
                    return;
                }
            }
        }
        if (type_arg_nodes.len == 0) return;
        const start_idx: u32 = @intCast(self.store.extra_data.items.len);
        for (type_arg_nodes) |t_node_id| {
            const node_ty = self.nodeType(t_node_id);
            const resolved_ty = if (!node_ty.isError())
                node_ty
            else blk: {
                const fallback_ty = self.resolveSimpleTypeAstFallback(t_node_id);
                break :blk if (!fallback_ty.isError()) fallback_ty else TypeId.unit_ty;
            };
            try self.store.extra_data.append(self.allocator, self.concreteType(resolved_ty).toU32());
        }
        try self.store.call_type_args.put(self.allocator, call_hir.asInt(), .{
            .start = start_idx,
            .len = @intCast(type_arg_nodes.len),
        });
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
                if (!n_ty.isError()) {
                    type_args[i] = n_ty;
                } else {
                    const fb_ty = self.resolveSimpleTypeAstFallback(t_node_id);
                    if (!fb_ty.isError()) type_args[i] = fb_ty;
                }
            }
        }

        // [0] `@c_import("header.h")` & `@caller_location()` (`SE-17`):
        if (intr_kind == .c_import) {
            return self.emitUnitConst(intr_tok, call_id);
        }
        if (intr_kind == .caller_location) {
            return self.emitCallerLocationConst(intr_tok, call_id);
        }

        // [1] `@field(target, comptime field_spec)` -> direct `hir_field_proj` / `hir_bitfield_read` (`DR-05` Tier-1):
        if (intr_kind == .field and val_args.len >= 2) {
            const base_hir = try self.lowerExpr(self.unwrapCallArgAst(val_args[0]), .err_ty);
            if (try self.tryEvalAstComptime(self.unwrapCallArgAst(val_args[1]), .err_ty)) |spec_val| {
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
            if (try self.tryEvalAstComptime(self.unwrapCallArgAst(val_args[0]), .bool_ty)) |cond_val| {
                if (cond_val == .bool_val and !cond_val.bool_val) {
                    var msg_text: []const u8 = "compile-time assertion failed";
                    if (val_args.len >= 2) {
                        if (try self.tryEvalAstComptime(self.unwrapCallArgAst(val_args[1]), .str_ty)) |m_val| {
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
            if (try self.tryEvalAstComptime(self.unwrapCallArgAst(val_args[0]), .str_ty)) |m_val| {
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

        // [6] Emit `hir_intrinsic_call` for polymorphic or `MirVm`-evaluated intrinsics:
        var payload_words: std.ArrayListUnmanaged(u32) = .empty;
        defer payload_words.deinit(self.allocator);
        try payload_words.append(self.allocator, @intCast(type_arg_nodes.len));
        try payload_words.append(self.allocator, @intCast(val_args.len));
        for (0..type_arg_nodes.len) |i| {
            try payload_words.append(self.allocator, type_args[i].toU32());
        }
        for (val_args) |v_arg_id| {
            const unwrapped_v = self.unwrapCallArgAst(v_arg_id);
            const expected_arg_ty: TypeId = if (intr_kind == .panic) .fmt_args_ty else .err_ty;
            try payload_words.append(self.allocator, (try self.lowerExpr(unwrapped_v, expected_arg_ty)).asInt());
        }
        const extra_idx = try self.store.appendExtraSlice(payload_words.items);
        const checked_call_ty = if (!target_ty.isError()) target_ty else self.nodeType(call_id);
        const res_ty = if (!checked_call_ty.isError())
            checked_call_ty
        else switch (intr_kind) {
            .bit_cast => type_args[0],
            .from_bytes => try self.pool.internOptional(type_args[0]),
            .view_bytes => try self.pool.internOptional(try self.pool.internRef(type_args[0], false)),
            .as_bytes, .embed_bytes => try self.pool.internRef(try self.pool.internSlice(.u8_ty, false), false),
            .type_name => .str_ty,
            .size_of, .align_of => .usize_ty,
            .has_field, .implements, .poll_reload => .bool_ty,
            .compile_error, .panic, .trap, .sys_exit => .never_ty,
            .sys_write => .isize_ty,
            .atomic_load, .atomic_rmw_add, .atomic_rmw_sub, .atomic_rmw_xchg => if (type_arg_nodes.len >= 1)
                type_args[0]
            else
                .usize_ty,
            .atomic_cmpxchg => blk_cmpxchg_ty: {
                const elem_ty = if (type_arg_nodes.len >= 1) type_args[0] else .usize_ty;
                const pair_elems = [2]TypeId{ elem_ty, .bool_ty };
                break :blk_cmpxchg_ty try self.pool.internTuple(&pair_elems);
            },
            .simd_splat, .simd_add, .simd_sub, .simd_mul => if (type_arg_nodes.len >= 1)
                type_args[0]
            else
                .f32_ty,
            .simd_reduce_add => blk_reduce_ty: {
                if (type_arg_nodes.len >= 1) {
                    const vec_ty = self.pool.unwrapUnderlyingType(type_args[0]);
                    if (!vec_ty.isPrimitive() and self.pool.getTag(vec_ty) == .array_ty) {
                        break :blk_reduce_ty TypeId.fromInt(self.pool.getNode(vec_ty).lhs);
                    }
                }
                break :blk_reduce_ty .f32_ty;
            },
            else => .unit_ty,
        };
        const intr_hir = try self.emitNode(.{
            .tag = .hir_intrinsic_call,
            .flags = .{ .category = if (res_ty == .never_ty) .diverging else .rvalue },
            .type_id = self.concreteType(res_ty),
            .origin_token = intr_tok,
            .data = .{ .lhs = @backingInt(intr_kind), .rhs = extra_idx },
        }, call_id);
        if (intr_kind == .embed_bytes and !intr_hir.isNone()) {
            try self.store.embed_origin_files.put(self.allocator, intr_hir.asInt(), self.active_lexical_file_id);
        }
        return intr_hir;
    }

    /// Lowers `receiver.method(…)` and Unified `.` static calls `mod.fn(…)` / `Type.assoc_fn(…)` (`DR-02` §2.2 & `SE-07`).
    fn lowerMethodCallExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node) return self.emitErrorHole(tok, expr_id, target_ty);
        const recv_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const raw_items = self.getAstExtraSlice(expr_id, true);
        if (raw_items.len == 0) return self.emitErrorHole(tok, expr_id, target_ty);

        const member_tok = TokenIndex.fromInt(raw_items[0]);
        const member_name = symbol_resolver.extractTokenSlice(self.source, self.tokens, member_tok);
        const static_kind = self.resolveStaticDotTargetAst(recv_id);
        const is_static_dot_call = static_kind != .none;

        var type_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer type_arg_nodes.deinit(self.allocator);
        var val_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer val_arg_nodes.deinit(self.allocator);
        for (raw_items[1..]) |raw_item| {
            const item_id = NodeIndex.fromInt(raw_item);
            if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
            if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) {
                try type_arg_nodes.append(self.allocator, item_id);
                continue;
            }
            try val_arg_nodes.append(self.allocator, item_id);
        }
        const val_args = val_arg_nodes.items;

        // Built-in `.len()`, `.is_empty()`, `.as_ptr()`, and `.as_mut_ptr()` methods on slices, arrays, `#soa`, `str`, and `SE-09` bounds:
        if (!is_static_dot_call and val_args.len == 0) {
            const raw_recv_ty = self.nodeType(recv_id);
            const unwrapped_recv = self.pool.unwrapUnderlyingType(self.unwrapRefType(raw_recv_ty));
            const recv_tag = self.pool.getTag(unwrapped_recv);
            const union_elem_opt = self.unionSliceElemType(unwrapped_recv);
            const is_seq_ty = recv_tag == .slice_ty or recv_tag == .array_ty or
                recv_tag == .soa_slice_ty or recv_tag == .soa_array_ty or
                unwrapped_recv == .str_ty or union_elem_opt != null;
            if (is_seq_ty and std.mem.eql(u8, member_name, "len")) {
                const recv_hir = try self.lowerExpr(recv_id, .err_ty);
                return self.emitSequenceLen(recv_hir, self.store.getNode(recv_hir).type_id, tok);
            }
            if (is_seq_ty and std.mem.eql(u8, member_name, "is_empty")) {
                const recv_hir = try self.lowerExpr(recv_id, .err_ty);
                const len_hir = try self.emitSequenceLen(recv_hir, self.store.getNode(recv_hir).type_id, tok);
                const zero_hir = try self.emitConstVal(.{ .int_val = 0 }, .usize_ty, tok, .none, true);
                const eq_extra = try self.store.appendExtraSlice(&[2]u32{ len_hir.asInt(), zero_hir.asInt() });
                return self.emitNode(.{
                    .tag = .hir_binary_op,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = .bool_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = eq_extra, .rhs = @backingInt(HirBinaryOp.eq) },
                }, expr_id);
            }
            const is_as_ptr = std.mem.eql(u8, member_name, "as_ptr");
            const is_as_mut_ptr = std.mem.eql(u8, member_name, "as_mut_ptr");
            if ((is_as_ptr or is_as_mut_ptr) and
                (recv_tag == .slice_ty or recv_tag == .array_ty or
                    unwrapped_recv == .str_ty or union_elem_opt != null))
            {
                const elem_ty: TypeId = if (unwrapped_recv == .str_ty)
                    .u8_ty
                else if (union_elem_opt) |u_elem|
                    self.concreteType(u_elem)
                else
                    self.concreteType(TypeId.fromInt(self.pool.getNode(unwrapped_recv).lhs));
                const resolved_ptr_ty = if (!target_ty.isError())
                    target_ty
                else blk_ptr_ty: {
                    const node_ty = self.nodeType(expr_id);
                    break :blk_ptr_ty if (!node_ty.isError())
                        node_ty
                    else
                        try self.pool.internRawPtr(elem_ty, is_as_mut_ptr);
                };
                const raw_recv_hir = try self.lowerPlaceWithMutCtx(recv_id, .err_ty, is_as_mut_ptr);
                const deref_recv_hir = try self.autoDerefPlace(raw_recv_hir, tok);
                if (recv_tag == .array_ty) {
                    const arr_ptr_ty = try self.pool.internRawPtr(
                        self.store.getNode(deref_recv_hir).type_id,
                        is_as_mut_ptr,
                    );
                    const raw_addr = try self.emitNode(.{
                        .tag = .hir_unary_op,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = arr_ptr_ty,
                        .origin_token = tok,
                        .data = .{
                            .lhs = @backingInt(
                                if (is_as_mut_ptr) HirUnaryOp.addr_of_raw_mut else HirUnaryOp.addr_of_raw,
                            ),
                            .rhs = deref_recv_hir.asInt(),
                        },
                    }, .none);
                    return self.emitNode(.{
                        .tag = .hir_cast,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = self.concreteType(resolved_ptr_ty),
                        .origin_token = tok,
                        .data = .{ .lhs = raw_addr.asInt(), .rhs = @backingInt(HirCastKind.ptr_cast) },
                    }, expr_id);
                }
                return self.emitNode(.{
                    .tag = .hir_field_proj,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = self.concreteType(resolved_ptr_ty),
                    .origin_token = tok,
                    .data = .{ .lhs = deref_recv_hir.asInt(), .rhs = 0 },
                }, expr_id);
            }
        }

        // Built-in `.narrow[Dst]()` / `.try_narrow[Dst]()` checked integer conversions (`DR-20` `D-11`):
        if (self.side_tables) |tables| {
            if (tables.getNarrowCall(expr_id)) |narrow_info| {
                const raw_recv_hir = try self.lowerExpr(recv_id, .err_ty);
                const deref_recv_hir = try self.autoDerefPlace(raw_recv_hir, tok);
                const min_hir = try self.emitConstVal(
                    .{ .int_val = narrow_info.min_val },
                    .i128_ty,
                    tok,
                    .none,
                    true,
                );
                const max_hir = try self.emitConstVal(
                    .{ .int_val = narrow_info.max_val },
                    .i128_ty,
                    tok,
                    .none,
                    true,
                );
                const narrow_payload = [6]u32{
                    1,
                    3,
                    narrow_info.dst_ty.toU32(),
                    deref_recv_hir.asInt(),
                    min_hir.asInt(),
                    max_hir.asInt(),
                };
                const extra_idx = try self.store.appendExtraSlice(&narrow_payload);
                const internal_kind: HirInternalIntrinsic = if (narrow_info.kind == .try_narrow)
                    .try_narrow
                else
                    .narrow_check;
                const resolved_ty = if (!target_ty.isError()) target_ty else self.nodeType(expr_id);
                const fallback_ty = if (narrow_info.kind == .try_narrow)
                    try self.pool.internOptional(narrow_info.dst_ty)
                else
                    narrow_info.dst_ty;
                return self.emitNode(.{
                    .tag = .hir_intrinsic_call,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = self.concreteType(if (!resolved_ty.isError()) resolved_ty else fallback_ty),
                    .origin_token = tok,
                    .data = .{
                        .lhs = HIR_INTERNAL_INTRINSIC_FLAG | @backingInt(internal_kind),
                        .rhs = extra_idx,
                    },
                }, expr_id);
            }
        }

        var method_sym_idx = self.nodeSymbol(expr_id);
        if (method_sym_idx.isNone()) {
            if (is_static_dot_call) {
                method_sym_idx = self.lookupStaticMemberSymbolFallback(recv_id, member_name);
            } else {
                const recv_ty = self.unwrapRefType(self.nodeType(recv_id));
                if (try self.lookupMethodOnType(recv_ty, member_name)) |found_m| {
                    method_sym_idx = found_m;
                }
            }
        }

        // Structured `core.async` static calls (`cx.async.task_group`, `cx.async.yield_now`, `cx.async.block_on`):
        if (is_static_dot_call) {
            if (try self.tryLowerStructuredAsyncEntryCall(
                expr_id,
                method_sym_idx,
                recv_id,
                member_name,
                val_args,
                target_ty,
                tok,
            )) |async_static_hir| return async_static_hir;
        } else {
            // Structured `TaskGroup` (`spawn`, `spawn_local`, `cancel_all`, `is_cancelled`) and `TaskHandle` (`join`, `cancel`):
            if (try self.tryLowerTaskGroupOrHandleMethod(
                expr_id,
                recv_id,
                member_name,
                val_args,
                target_ty,
                tok,
            )) |nursery_method_hir| return nursery_method_hir;
        }

        // Static `Enum.Variant(args)` constructor resolved via `nodeSymbol` or `target_scope`:
        if (!method_sym_idx.isNone() and self.sym_table.getSymbol(method_sym_idx).kind == .enum_variant_sym) {
            const v_sym = self.sym_table.getSymbol(method_sym_idx).*;
            const out_enum_ty = self.concreteType(if (!target_ty.isError()) target_ty else self.nodeType(expr_id));
            const enum_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, out_enum_ty);
            const subst_var_ty = try enum_subst.applyMut(self.allocator, self.pool, v_sym.type_id);
            var arg_hirs: std.ArrayListUnmanaged(u32) = .empty;
            defer arg_hirs.deinit(self.allocator);
            if (val_args.len == 1) {
                const a0 = self.unwrapCallArgAst(val_args[0]);
                try arg_hirs.append(self.allocator, (try self.lowerExpr(a0, subst_var_ty)).asInt());
            } else {
                const tup_elems = self.pool.getTupleElements(subst_var_ty);
                for (val_args, 0..) |arg_id, i| {
                    const sub_ty = if (i < tup_elems.len) TypeId.fromInt(tup_elems[i]) else .err_ty;
                    const unwrapped_arg = self.unwrapCallArgAst(arg_id);
                    try arg_hirs.append(self.allocator, (try self.lowerExpr(unwrapped_arg, sub_ty)).asInt());
                }
            }
            const extra_idx = try self.store.appendLenPrefixedExtra(arg_hirs.items);
            return self.emitNode(.{
                .tag = .hir_construct,
                .flags = .{ .category = .rvalue },
                .type_id = out_enum_ty,
                .origin_token = tok,
                .data = .{
                    .lhs = @as(u32, @backingInt(HirConstructKind.enum_variant)) |
                        (@as(u32, v_sym.member_ordinal) << 8),
                    .rhs = extra_idx,
                },
            }, expr_id);
        }

        if (method_sym_idx.isNone()) {
            if (is_static_dot_call and static_kind == .type_ns) {
                if (self.resolveBuiltinPrimitiveAst(recv_id)) |prim_ty| {
                    if (try self.tryLowerPrimitiveEndianHelper(
                        expr_id,
                        prim_ty,
                        true,
                        recv_id,
                        member_name,
                        val_args,
                        tok,
                    )) |endian_hir| return endian_hir;
                }
                if (try self.tryLowerStaticSumConstructor(
                    expr_id,
                    member_name,
                    val_args,
                    target_ty,
                    tok,
                )) |ctor_hir| return ctor_hir;
            }
            if (!is_static_dot_call) {
                const recv_prim_ty = self.pool.unwrapUnderlyingType(self.unwrapRefType(self.nodeType(recv_id)));
                if (try self.tryLowerPrimitiveEndianHelper(
                    expr_id,
                    recv_prim_ty,
                    false,
                    recv_id,
                    member_name,
                    val_args,
                    tok,
                )) |endian_hir| return endian_hir;

                // Built-in `.as_bytes()` view on `str`, `SE-09` `[Data: str | &[u8]]`, `[u8]`, and `IntoBytes` (`DR-20` `D-01`):
                if (val_args.len == 0 and std.mem.eql(u8, member_name, "as_bytes")) {
                    const fallback_slice_ty = try self.pool.internRef(
                        try self.pool.internSlice(.u8_ty, false),
                        false,
                    );
                    const resolved_ty = self.concreteType(blk_bytes_ty: {
                        const checked_ty = if (!target_ty.isError()) target_ty else self.nodeType(expr_id);
                        break :blk_bytes_ty if (!checked_ty.isError()) checked_ty else fallback_slice_ty;
                    });
                    const raw_recv_hir = try self.lowerExpr(recv_id, .err_ty);
                    const raw_recv_ty = self.store.getNode(raw_recv_hir).type_id;
                    const deref_recv_hir = try self.autoDerefPlace(raw_recv_hir, tok);
                    const inner_ty = self.pool.unwrapUnderlyingType(self.store.getNode(deref_recv_hir).type_id);
                    const inner_tag = self.pool.getTag(inner_ty);
                    if (inner_ty == .str_ty or self.unionSliceElemType(inner_ty) != null) {
                        return self.emitNode(.{
                            .tag = .hir_cast,
                            .flags = .{ .category = .rvalue, .is_synthetic = true },
                            .type_id = resolved_ty,
                            .origin_token = tok,
                            .data = .{ .lhs = deref_recv_hir.asInt(), .rhs = @backingInt(HirCastKind.noop) },
                        }, expr_id);
                    }
                    if (inner_tag == .slice_ty and TypeId.fromInt(self.pool.getNode(inner_ty).lhs) == .u8_ty) {
                        if (raw_recv_ty == resolved_ty) return raw_recv_hir;
                        return self.emitSyntheticAddrOf(deref_recv_hir, resolved_ty, false, tok);
                    }
                    const ref_ty = try self.pool.internRef(self.store.getNode(deref_recv_hir).type_id, false);
                    const ref_hir = try self.emitSyntheticAddrOf(deref_recv_hir, ref_ty, false, tok);
                    if (inner_tag == .array_ty and TypeId.fromInt(self.pool.getNode(inner_ty).lhs) == .u8_ty) {
                        return self.emitNode(.{
                            .tag = .hir_cast,
                            .flags = .{ .category = .rvalue, .is_synthetic = true },
                            .type_id = resolved_ty,
                            .origin_token = tok,
                            .data = .{ .lhs = ref_hir.asInt(), .rhs = @backingInt(HirCastKind.array_to_slice) },
                        }, expr_id);
                    }
                    const as_bytes_payload = [3]u32{ 0, 1, ref_hir.asInt() };
                    const extra_idx = try self.store.appendExtraSlice(&as_bytes_payload);
                    return self.emitNode(.{
                        .tag = .hir_intrinsic_call,
                        .flags = .{ .category = .rvalue, .is_synthetic = true },
                        .type_id = resolved_ty,
                        .origin_token = tok,
                        .data = .{ .lhs = @backingInt(IntrinsicKind.as_bytes), .rhs = extra_idx },
                    }, expr_id);
                }

                // Built-in `TaskGroup` (`spawn`, `spawn_local`, `cancel`) and `TaskHandle` (`join`) fallback (`SE-20`):
                const recv_unwrapped = self.pool.unwrapUnderlyingType(self.unwrapRefType(self.nodeType(recv_id)));
                if (self.pool.isTaskGroupType(recv_unwrapped) or self.pool.isTaskHandleType(recv_unwrapped)) {
                    var tg_stmts: std.ArrayListUnmanaged(u32) = .empty;
                    defer tg_stmts.deinit(self.allocator);
                    const is_mut_tg = self.pool.isTaskGroupType(recv_unwrapped);
                    const tg_recv = try self.lowerPlaceWithMutCtx(recv_id, .err_ty, is_mut_tg);
                    const recv_tmp = try self.allocTempLocal(self.store.getNode(tg_recv).type_id, tok, false);
                    try tg_stmts.append(
                        self.allocator,
                        (try self.emitLocalDeclNode(recv_tmp, tg_recv, tok)).asInt(),
                    );
                    const builder_state_ty = if (self.side_tables) |tables|
                        tables.getBuilderBlockStateType(expr_id)
                    else
                        null;
                    for (val_args, 0..) |arg_id, arg_i| {
                        const unwrapped_arg = self.unwrapCallArgAst(arg_id);
                        const arg_hir = if (builder_state_ty != null and arg_i + 1 == val_args.len and
                            self.ast_arena.getNode(unwrapped_arg).tag == .block)
                            try self.lowerBuilderTrailingBlockClosure(
                                unwrapped_arg,
                                builder_state_ty.?,
                                .err_ty,
                                tok,
                            )
                        else
                            try self.lowerExpr(unwrapped_arg, .err_ty);
                        const arg_tmp = try self.allocTempLocal(self.store.getNode(arg_hir).type_id, tok, false);
                        try tg_stmts.append(
                            self.allocator,
                            (try self.emitLocalDeclNode(arg_tmp, arg_hir, tok)).asInt(),
                        );
                    }
                    const tg_ret_ty = self.concreteType(blk_tg_ret: {
                        const checked_ty = if (!target_ty.isError()) target_ty else self.nodeType(expr_id);
                        break :blk_tg_ret if (!checked_ty.isError()) checked_ty else .unit_ty;
                    });
                    const tail_hir = try self.emitDefaultInitValue(tg_ret_ty, tok);
                    return self.emitSyntheticBlock(tg_stmts.items, tail_hir, tg_ret_ty, tok);
                }
            }
            return self.emitErrorHole(tok, expr_id, target_ty);
        }

        const method_sym = self.sym_table.getSymbol(method_sym_idx).*;
        const sig_view = self.pool.getFnSignatureView(method_sym.type_id);
        const has_self_receiver = !is_static_dot_call;

        var seq_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer seq_stmts.deinit(self.allocator);
        var ordered_args: std.ArrayListUnmanaged(HirIndex) = .empty;
        defer ordered_args.deinit(self.allocator);

        // [1] Evaluate explicit and default arguments (`SE-07`) BEFORE projecting instance `receiver` (`DR-02` §2.2):
        try self.lowerMappedDirectArgs(
            expr_id,
            method_sym_idx,
            method_sym.type_id,
            has_self_receiver,
            val_args,
            tok,
            &seq_stmts,
            &ordered_args,
        );

        var wrapped_args: std.ArrayListUnmanaged(u32) = .empty;
        defer wrapped_args.deinit(self.allocator);

        // [2] Evaluate and project `receiver` ONLY for instance method calls (never for Unified `.` static calls):
        if (has_self_receiver) {
            const self_mode = if (sig_view) |sv|
                (if (sv.paramCount() > 0) sv.getParamMode(0) else .let_mode)
            else
                .let_mode;
            const sig_self_ty = if (sig_view) |sv|
                (if (sv.paramCount() > 0) sv.getParamType(0) else .err_ty)
            else
                .err_ty;
            const is_mut_self_needed = self_mode == .inout_mode or self_mode == .set_mode or
                (!sig_self_ty.isError() and self.pool.getTag(sig_self_ty) == .mut_ref_ty);
            const raw_recv_hir = try self.lowerPlaceWithMutCtx(recv_id, .err_ty, is_mut_self_needed);
            const self_param_ty = if (!sig_self_ty.isError())
                sig_self_ty
            else
                self.store.getNode(raw_recv_hir).type_id;
            const adjusted_recv = try self.adjustReceiverForParam(raw_recv_hir, self_param_ty, tok);
            try wrapped_args.append(
                self.allocator,
                (try self.wrapArgProjection(adjusted_recv, self_mode, tok)).asInt(),
            );
        }

        const param_offset: usize = if (has_self_receiver) 1 else 0;
        for (ordered_args.items, 0..) |arg_hir, i| {
            const param_idx = param_offset + i;
            const p_mode = if (sig_view) |sv|
                (if (param_idx < sv.paramCount()) sv.getParamMode(param_idx) else .let_mode)
            else
                .let_mode;
            try wrapped_args.append(self.allocator, (try self.wrapArgProjection(arg_hir, p_mode, tok)).asInt());
        }

        const callee_hir = try self.emitNode(.{
            .tag = .hir_global_ref,
            .flags = .{ .category = .rvalue },
            .type_id = method_sym.type_id,
            .origin_token = tok,
            .data = .{ .lhs = method_sym.def_id.asInt(), .rhs = method_sym_idx.asInt() },
        }, .none);
        const is_async_method = if (sig_view) |sv| sv.is_async else false;
        const ret_ty = if (!target_ty.isError())
            target_ty
        else if (sig_view) |sv| blk_method_ret: {
            const inner_ret = self.concreteType(sv.ret_ty);
            if (sv.is_async) {
                break :blk_method_ret try self.pool.internFuture(inner_ret, method_sym_idx.asInt());
            }
            break :blk_method_ret inner_ret;
        } else .unit_ty;
        const call_hir = if (is_async_method)
            try self.emitAsyncFutureMake(
                method_sym.def_id,
                method_sym_idx,
                callee_hir,
                wrapped_args.items,
                self.concreteType(ret_ty),
                tok,
                expr_id,
            )
        else blk_sync_mcall: {
            const extra_idx = try self.store.appendLenPrefixedExtra(wrapped_args.items);
            const is_sub_method = self.isCalleeSubscript(callee_hir);
            const emitted_mcall = try self.emitNode(.{
                .tag = if (is_sub_method) .hir_subscript_call else .hir_call,
                .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
                .type_id = ret_ty,
                .origin_token = tok,
                .data = .{ .lhs = callee_hir.asInt(), .rhs = extra_idx },
            }, expr_id);
            if (!is_sub_method) {
                try self.recordCallTypeArgs(expr_id, emitted_mcall, type_arg_nodes.items);
            }
            break :blk_sync_mcall emitted_mcall;
        };

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
            const ct_checkpoint = self.comptime_shadow_log.items.len;
            defer self.popComptimeBindingsTo(ct_checkpoint);
            if (try self.tryEvalAstComptime(cond_id, .bool_ty)) |cond_val| {
                const is_taken = switch (cond_val) {
                    .bool_val => |flag| flag,
                    .int_val => |num| num != 0,
                    else => false,
                };
                if (is_taken) {
                    return self.lowerBlockExpr(then_id, target_ty, false);
                }
                self.popComptimeBindingsTo(ct_checkpoint);
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
            then_id,
            else_id,
            .none,
            if (!target_ty.isError()) target_ty else .unit_ty,
            tok,
            expr_id,
        );
    }

    /// Returns `true` when `clause_id` is a positive `expr is Pattern` AST clause (`SE-01`).
    fn isPositiveIsClauseAst(self: *const HirLowerer, clause_id: NodeIndex) bool {
        if (clause_id.isNone() or clause_id.asInt() >= self.ast_arena.countNodes()) return false;
        const clause_node = self.ast_arena.getNode(clause_id);
        if (clause_node.lhs.tag != .node or clause_node.rhs.tag != .node) return false;
        if (clause_node.main_token.isNone() or clause_node.main_token.asInt() >= self.tokens.countTokens()) {
            return false;
        }
        const main_kind = self.tokens.getToken(clause_node.main_token).kind;
        if (clause_node.tag == .is_expr) {
            return main_kind != .kw_not;
        }
        return clause_node.tag == .binary_expr and main_kind == .kw_is;
    }

    /// Returns `true` if `expr_id` contains a dominating `.walrus_expr` (`:=`) outside nested blocks/closures (`SE-02`).
    fn hasDominatingWalrusAst(self: *const HirLowerer, expr_id: NodeIndex, depth: u32) bool {
        if (depth >= MAX_HIR_LOWER_DEPTH) return false;
        if (expr_id.isNone() or expr_id.asInt() >= self.ast_arena.countNodes()) return false;
        const node = self.ast_arena.getNode(expr_id);
        switch (node.tag) {
            .walrus_expr => return true,
            .block,
            .if_expr,
            .match_expr,
            .for_stmt,
            .while_stmt,
            .loop_expr,
            .with_expr,
            .closure_expr,
            => return false,
            .unary_expr => {
                if (!node.main_token.isNone() and node.main_token.asInt() < self.tokens.countTokens()) {
                    const op_kind = self.tokens.getToken(node.main_token).kind;
                    if (op_kind == .kw_not or op_kind == .bang) return false;
                }
                if (node.lhs.tag == .node) {
                    return self.hasDominatingWalrusAst(NodeIndex.fromInt(node.lhs.payload), depth + 1);
                }
                return false;
            },
            .binary_expr => {
                if (!node.main_token.isNone() and node.main_token.asInt() < self.tokens.countTokens()) {
                    const op_kind = self.tokens.getToken(node.main_token).kind;
                    if (op_kind == .kw_or) return false;
                    if (op_kind == .kw_orelse or op_kind == .kw_catch) {
                        return node.lhs.tag == .node and
                            self.hasDominatingWalrusAst(NodeIndex.fromInt(node.lhs.payload), depth + 1);
                    }
                }
                if (node.lhs.tag == .node and
                    self.hasDominatingWalrusAst(NodeIndex.fromInt(node.lhs.payload), depth + 1))
                {
                    return true;
                }
                if (node.rhs.tag == .node and
                    self.hasDominatingWalrusAst(NodeIndex.fromInt(node.rhs.payload), depth + 1))
                {
                    return true;
                }
                return false;
            },
            .call_expr, .generic_call, .method_call => {
                if (node.lhs.tag == .node and
                    self.hasDominatingWalrusAst(NodeIndex.fromInt(node.lhs.payload), depth + 1))
                {
                    return true;
                }
                const start_idx: usize = if (node.tag == .method_call) 1 else 0;
                const items = self.getAstExtraSlice(expr_id, true);
                if (items.len > start_idx) {
                    for (items[start_idx..]) |raw_arg| {
                        const arg_id = self.unwrapCallArgAst(NodeIndex.fromInt(raw_arg));
                        if (!isTypeAstTag(self.ast_arena.getNode(arg_id).tag) and
                            self.hasDominatingWalrusAst(arg_id, depth + 1))
                        {
                            return true;
                        }
                    }
                }
                return false;
            },
            .tuple_lit, .array_lit => {
                for (self.getAstExtraSlice(expr_id, false)) |raw_elem| {
                    if (self.hasDominatingWalrusAst(NodeIndex.fromInt(raw_elem), depth + 1)) return true;
                }
                return false;
            },
            .contextual_variant, .struct_lit => {
                for (self.getAstExtraSlice(expr_id, true)) |raw_elem| {
                    const elem_id = self.unwrapCallArgAst(NodeIndex.fromInt(raw_elem));
                    if (self.hasDominatingWalrusAst(elem_id, depth + 1)) return true;
                }
                return false;
            },
            else => {
                if (node.lhs.tag == .node and
                    self.hasDominatingWalrusAst(NodeIndex.fromInt(node.lhs.payload), depth + 1))
                {
                    return true;
                }
                if (node.rhs.tag == .node and
                    self.hasDominatingWalrusAst(NodeIndex.fromInt(node.rhs.payload), depth + 1))
                {
                    return true;
                }
                return false;
            },
        }
    }

    /// Returns `true` if `cond_id` uses `ConditionScope` (`SE-01` positive `is` or `SE-02` dominating `:=` binding).
    fn hasConditionScope(self: *const HirLowerer, cond_id: NodeIndex) bool {
        return self.hasConditionScopeDepth(cond_id, 0);
    }

    /// Bounded recursive helper for `hasConditionScope` along the top-level `and` spine.
    fn hasConditionScopeDepth(self: *const HirLowerer, cond_id: NodeIndex, depth: u32) bool {
        if (depth >= MAX_HIR_LOWER_DEPTH) return false;
        if (cond_id.isNone() or cond_id.asInt() >= self.ast_arena.countNodes()) return false;
        const node = self.ast_arena.getNode(cond_id);
        if (node.tag == .binary_expr and node.lhs.tag == .node and node.rhs.tag == .node and
            !node.main_token.isNone() and node.main_token.asInt() < self.tokens.countTokens())
        {
            const op_kind = self.tokens.getToken(node.main_token).kind;
            if (op_kind == .kw_and) {
                return self.hasConditionScopeDepth(NodeIndex.fromInt(node.lhs.payload), depth + 1) or
                    self.hasConditionScopeDepth(NodeIndex.fromInt(node.rhs.payload), depth + 1);
            }
        }
        return self.isPositiveIsClauseAst(cond_id) or self.hasDominatingWalrusAst(cond_id, depth);
    }

    /// Flattens top-level `.kw_and` conjunctions left-to-right for `hir_cond_if` and `hir_cond_while`.
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
            if (op_kind == .kw_and) {
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
        }
        if (self.isPositiveIsClauseAst(cond_id)) has_is_out.* = true;
        try out_clauses.append(self.allocator, cond_id);
    }

    /// Lowers conjunctive `clauses` into `HirCondClauseKind` words (`[0, bool_hir]` or `[1, scrut_hir, pat_idx]`).
    fn lowerCondClauseList(
        self: *HirLowerer,
        clauses: []const NodeIndex,
        out_words: *std.ArrayListUnmanaged(u32),
    ) anyerror!void {
        for (clauses) |clause_id| {
            if (self.isPositiveIsClauseAst(clause_id)) {
                const clause_node = self.ast_arena.getNode(clause_id);
                const scrutinee_hir = try self.lowerExpr(NodeIndex.fromInt(clause_node.lhs.payload), .err_ty);
                const scrut_ty = self.store.getNode(scrutinee_hir).type_id;
                const locals_before = self.store.locals.items.len;
                const pat_idx = try self.lowerTopPattern(
                    NodeIndex.fromInt(clause_node.rhs.payload),
                    scrut_ty,
                    false,
                );
                for (self.store.locals.items[locals_before..]) |*bound_local| {
                    bound_local.is_cond_binding = true;
                }
                try out_words.appendSlice(self.allocator, &[3]u32{
                    @backingInt(HirCondClauseKind.is_match),
                    scrutinee_hir.asInt(),
                    pat_idx,
                });
            } else {
                const bool_hir = try self.lowerExpr(clause_id, .bool_ty);
                try out_words.appendSlice(self.allocator, &[2]u32{
                    @backingInt(HirCondClauseKind.bool_pred),
                    bool_hir.asInt(),
                });
            }
        }
    }

    /// Shared condition lowering for `if` and `while` (`hir_cond_if` and boolean `hir_if`).
    fn lowerConditionBranch(
        self: *HirLowerer,
        cond_id: NodeIndex,
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

        // [1] `ConditionScope` `if` (`SE-01` positive `is` and/or `SE-02` dominating `:=` bindings):
        if (synthetic_else_hir.isNone() and self.hasConditionScope(cond_id)) {
            var clauses: std.ArrayListUnmanaged(NodeIndex) = .empty;
            defer clauses.deinit(self.allocator);
            var has_unused_is = false;
            try self.collectConjunctiveClauses(cond_id, &clauses, &has_unused_is);

            var extra_words: std.ArrayListUnmanaged(u32) = .empty;
            defer extra_words.deinit(self.allocator);
            try extra_words.append(self.allocator, @intCast(clauses.items.len));

            var then_hir: HirIndex = .none;
            {
                const local_checkpoint = self.local_shadow_log.items.len;
                defer self.popLexicalLocalsTo(local_checkpoint);

                const was_in_cond = self.is_in_cond_scope;
                self.is_in_cond_scope = true;
                {
                    errdefer self.is_in_cond_scope = was_in_cond;
                    try self.lowerCondClauseList(clauses.items, &extra_words);
                }
                self.is_in_cond_scope = was_in_cond;

                then_hir = try self.lowerBlockExpr(then_id, res_ty, false);
            }

            const else_hir = if (!else_ast_id.isNone())
                (if (self.ast_arena.getNode(else_ast_id).tag == .if_expr)
                    try self.lowerIfExpr(else_ast_id, res_ty, false)
                else
                    try self.lowerBlockExpr(else_ast_id, res_ty, false))
            else
                HirIndex.none;

            try extra_words.append(self.allocator, then_hir.asInt());
            try extra_words.append(self.allocator, else_hir.asInt());
            const extra_idx = try self.store.appendExtraSlice(extra_words.items);
            return self.emitNode(.{
                .tag = .hir_cond_if,
                .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
                .type_id = self.concreteType(res_ty),
                .origin_token = tok,
                .data = .{ .lhs = extra_idx, .rhs = 0 },
            }, ast_origin);
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

        const raw_scrut_hir = try self.lowerExpr(scrutinee_id, .err_ty);
        const scrut_ty = self.store.getNode(raw_scrut_hir).type_id;
        const res_ty = if (!target_ty.isError()) target_ty else .unit_ty;
        const label_tok = self.extractMatchLabelToken(expr_id);
        const is_labeled_fsm = !label_tok.isNone();

        var fsm_id: u32 = 0;
        var scrut_local: u32 = NONE_U32;
        var decl_hir: HirIndex = .none;
        const scrut_hir = if (is_labeled_fsm) blk_fsm_scrut: {
            const raw_fsm_id = self.next_fsm_id;
            self.next_fsm_id += 1;
            fsm_id = LABELED_MATCH_CONTINUE_FLAG | raw_fsm_id;
            scrut_local = try self.allocTempLocal(scrut_ty, tok, true);
            decl_hir = try self.emitLocalDeclNode(scrut_local, raw_scrut_hir, tok);
            try self.labeled_match_stack.append(self.allocator, .{
                .match_ast = expr_id,
                .fsm_id = fsm_id,
                .label_id = try self.internLabelToken(label_tok),
                .scrutinee_local = scrut_local,
                .scrutinee_ty = scrut_ty,
            });
            break :blk_fsm_scrut try self.emitVarRef(scrut_local, tok, .none);
        } else raw_scrut_hir;
        defer if (is_labeled_fsm) {
            _ = self.labeled_match_stack.pop();
        };

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
        const match_hir = try self.emitNode(.{
            .tag = .hir_match,
            .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
            .type_id = self.concreteType(res_ty),
            .origin_token = tok,
            .data = .{ .lhs = scrut_hir.asInt(), .rhs = match_extra },
        }, expr_id);
        if (is_labeled_fsm) {
            try self.store.labeled_matches.put(self.allocator, match_hir.asInt(), .{
                .fsm_id = fsm_id,
                .scrutinee_local = scrut_local,
            });
            return self.emitSyntheticBlock(&[1]u32{decl_hir.asInt()}, match_hir, self.concreteType(res_ty), tok);
        }
        return match_hir;
    }

    /// Lowers `loop { … }` (`loop_expr`) into `hir_loop` with its `break` value type and optional `:label` (`SE-06`).
    fn lowerLoopExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) !HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const body_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;
        const label_tok = if (ast_node.rhs.tag == .token) TokenIndex.fromInt(ast_node.rhs.payload) else .none;
        const res_ty = if (!target_ty.isError()) target_ty else .unit_ty;

        const loop_id = self.next_loop_id;
        self.next_loop_id += 1;
        try self.recordLoopContractFromAst(expr_id, loop_id);
        const label_id = try self.internLabelToken(label_tok);
        try self.loop_stack.append(self.allocator, .{
            .loop_id = loop_id,
            .label_id = label_id,
            .is_comptime_for = false,
            .result_opt_local = NONE_U32,
            .payload_ty = self.concreteType(res_ty),
            .opt_ty = .unit_ty,
        });
        defer _ = self.loop_stack.pop();

        const saved_loop_id = self.current_loop_id;
        const saved_in_ct_for = self.is_in_comptime_for;
        self.current_loop_id = loop_id;
        self.is_in_comptime_for = false;
        defer {
            self.current_loop_id = saved_loop_id;
            self.is_in_comptime_for = saved_in_ct_for;
        }

        const body_hir = try self.lowerBlockExpr(body_id, .unit_ty, false);
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
        const saved_loop_floor = self.closure_loop_stack_floor;
        const saved_in_ct_for = self.is_in_comptime_for;
        const was_in_cond_scope = self.is_in_cond_scope;
        const saved_ceil = self.closure_outer_local_ceil;
        const saved_caller_loc = self.active_caller_loc_local;
        const saved_captures_len = self.active_closure_captures.items.len;
        const local_checkpoint = self.local_shadow_log.items.len;
        defer {
            self.popLexicalLocalsTo(local_checkpoint);
            self.active_closure_captures.shrinkRetainingCapacity(saved_captures_len);
            self.active_caller_loc_local = saved_caller_loc;
            self.closure_outer_local_ceil = saved_ceil;
            self.is_in_cond_scope = was_in_cond_scope;
            self.is_in_comptime_for = saved_in_ct_for;
            self.closure_loop_stack_floor = saved_loop_floor;
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
        try self.closure_frame_stack.append(self.allocator, .{ .ceil = return_local_id });
        defer {
            var popped_frame = self.closure_frame_stack.pop().?;
            popped_frame.captures.deinit(self.allocator);
        }
        self.active_caller_loc_local = null;
        self.current_fn_ret_ty = ret_ty;
        self.current_loop_id = null;
        self.closure_loop_stack_floor = self.loop_stack.items.len;
        self.is_in_comptime_for = false;
        self.is_in_cond_scope = false;

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
            const p_mode = if (sig_view) |sv|
                (if (i < sv.paramCount()) sv.getParamMode(i) else .let_mode)
            else
                .let_mode;
            const slot_id = try self.store.appendLocal(.{
                .name = p_name,
                .type_id = p_ty,
                .decl_span = self.tokens.getTokenSpan(self.store.file_id, p_tok),
                .mode = p_mode,
                .is_mut = (p_mode == .inout_mode or p_mode == .set_mode),
                .is_param = true,
                .is_temp = false,
            });
            try self.pushLexicalLocal(p_name, slot_id);
        }

        const clos_cst = self.ast_arena.getCstOrigin(expr_id);
        const is_local_clos = self.hasAttrNamedInCst(clos_cst, "local");
        const is_move_clos = self.hasModifierInCst(clos_cst, .kw_own, "own") or
            (if (sig_view) |sv| sv.capture_tier != .copy_tier else false);
        const is_async_clos = if (sig_view) |sv| sv.is_async else self.hasModifierInCst(clos_cst, .kw_async, "async");
        const fn_meta_idx: u32 = @intCast(self.store.functions.items.len);
        const synth_closure_def = self.mintSyntheticClosureDefId();
        try self.store.functions.append(self.allocator, .{
            .def_id = synth_closure_def,
            .fn_ty = self.concreteType(target_ty),
            .ret_ty = ret_ty,
            .return_local_id = return_local_id,
            .param_local_start = param_local_start,
            .param_len = @intCast(param_tokens.len),
            .is_local_closure = is_local_clos,
            .is_move_closure = is_move_clos,
            .is_async = is_async_clos,
        });

        const body_hir = if (ast_node.rhs.tag == .node) blk: {
            const body_id = NodeIndex.fromInt(ast_node.rhs.payload);
            if (self.ast_arena.getNode(body_id).tag == .block) {
                break :blk try self.lowerBlockExpr(body_id, ret_ty, true);
            }
            const expr_body = try self.lowerExpr(body_id, ret_ty);
            break :blk try self.wrapSyntheticReturnBlock(expr_body, ret_ty, tok);
        } else try self.emitUnitConst(tok, .none);

        const cap_slice = self.closure_frame_stack.items[self.closure_frame_stack.items.len - 1].captures.items;
        const cap_extra_start = if (cap_slice.len > 0) try self.store.appendExtraSlice(cap_slice) else 0;

        self.store.functions.items[fn_meta_idx].body_hir = body_hir;
        self.store.functions.items[fn_meta_idx].total_local_len =
            @intCast(self.store.locals.items.len - return_local_id);
        self.store.functions.items[fn_meta_idx].capture_extra_start = cap_extra_start;
        self.store.functions.items[fn_meta_idx].capture_len = @intCast(cap_slice.len / 2);
        if (!is_move_clos and cap_slice.len > 0) {
            self.store.functions.items[fn_meta_idx].is_local_closure = true;
        }

        return self.emitNode(.{
            .tag = .hir_closure,
            .flags = .{ .category = .rvalue },
            .type_id = self.concreteType(target_ty),
            .origin_token = tok,
            .data = .{ .lhs = fn_meta_idx, .rhs = body_hir.asInt() },
        }, expr_id);
    }

    // -------- Structured Async & Nursery Lowering Helpers ---------

    /// Mints a deterministic synthetic `DefId` within `active_owner_def_id` for closures, `async` blocks, and nurseries.
    fn mintSyntheticClosureDefId(self: *HirLowerer) DefId {
        const clos_ord = self.closure_ordinal_in_owner;
        self.closure_ordinal_in_owner += 1;
        const file_bits: u32 = if (!self.store.file_id.isNone()) self.store.file_id.asInt() & 0x01FF else 0;
        const owner_bits: u32 = if (!self.active_owner_def_id.isNone())
            @as(u32, self.active_owner_def_id.itemIndex()) & 0x0FFF
        else
            0x0FFF;
        return DefId.fromInt(0x5000_0000 + (file_bits << 20) + (owner_bits << 8) + (clos_ord & 0x00FF));
    }

    /// Emits a `hir_intrinsic_call` tagged with `HIR_INTERNAL_INTRINSIC_FLAG | internal_kind`.
    fn emitInternalIntrinsic(
        self: *HirLowerer,
        internal_kind: HirInternalIntrinsic,
        val_arg_hirs: []const u32,
        out_ty: TypeId,
        tok: TokenIndex,
        ast_origin: NodeIndex,
    ) !HirIndex {
        var extra_words: std.ArrayListUnmanaged(u32) = .empty;
        defer extra_words.deinit(self.allocator);
        try extra_words.ensureTotalCapacity(self.allocator, 2 + val_arg_hirs.len);
        extra_words.appendAssumeCapacity(0);
        extra_words.appendAssumeCapacity(@intCast(val_arg_hirs.len));
        extra_words.appendSliceAssumeCapacity(val_arg_hirs);
        const extra_idx = try self.store.appendExtraSlice(extra_words.items);
        return self.emitNode(.{
            .tag = .hir_intrinsic_call,
            .flags = .{ .category = .rvalue, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
            .type_id = self.concreteType(out_ty),
            .origin_token = tok,
            .data = .{
                .lhs = HIR_INTERNAL_INTRINSIC_FLAG | @backingInt(internal_kind),
                .rhs = extra_idx,
            },
        }, ast_origin);
    }

    /// Emits `HirInternalIntrinsic.async_future_make` (`[def_const, sym_const, callee_hir, call_args…] -> Future[T]`).
    fn emitAsyncFutureMake(
        self: *HirLowerer,
        prod_def: DefId,
        prod_sym: SymbolIndex,
        callee_hir: HirIndex,
        call_args: []const u32,
        fut_ty: TypeId,
        tok: TokenIndex,
        ast_origin: NodeIndex,
    ) !HirIndex {
        const def_const = try self.emitConstVal(.{ .int_val = @as(i128, prod_def.asInt()) }, .u32_ty, tok, .none, true);
        const sym_const = try self.emitConstVal(.{ .int_val = @as(i128, prod_sym.asInt()) }, .u32_ty, tok, .none, true);
        var make_args: std.ArrayListUnmanaged(u32) = .empty;
        defer make_args.deinit(self.allocator);
        try make_args.ensureTotalCapacity(self.allocator, 3 + call_args.len);
        make_args.appendAssumeCapacity(def_const.asInt());
        make_args.appendAssumeCapacity(sym_const.asInt());
        make_args.appendAssumeCapacity(callee_hir.asInt());
        make_args.appendSliceAssumeCapacity(call_args);
        return self.emitInternalIntrinsic(.async_future_make, make_args.items, fut_ty, tok, ast_origin);
    }

    /// Lowers postfix `.await` (`AstTag.await_expr`) into `HirTag.hir_await` (`lhs = fut_hir`).
    fn lowerAwaitExpr(self: *HirLowerer, expr_id: NodeIndex, target_ty: TypeId) anyerror!HirIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        const tok = ast_node.main_token;
        if (ast_node.lhs.tag != .node) return self.emitErrorHole(tok, expr_id, target_ty);

        const inner_ast_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const raw_out_ty = if (!target_ty.isError()) target_ty else self.nodeType(expr_id);
        const out_ty = self.concreteType(if (!raw_out_ty.isError()) raw_out_ty else .unit_ty);
        const inner_checked = self.nodeType(inner_ast_id);
        const inner_expected = if (!inner_checked.isError())
            self.concreteType(inner_checked)
        else
            try self.pool.internFuture(out_ty, 0);
        const fut_hir = try self.lowerExpr(inner_ast_id, inner_expected);
        return self.emitNode(.{
            .tag = .hir_await,
            .flags = .{ .category = .rvalue, .is_unsafe = self.is_in_unsafe },
            .type_id = out_ty,
            .origin_token = tok,
            .data = .{ .lhs = fut_hir.asInt(), .rhs = 0 },
        }, expr_id);
    }

    /// Lowers `async { … }` into a dedicated `is_async = true` `HirFnMeta` + `async_future_make` `Future[T]`.
    fn lowerAsyncBlockExpr(self: *HirLowerer, block_id: NodeIndex, expected_ty: TypeId) anyerror!HirIndex {
        return self.lowerAsyncBlockExprWithMode(block_id, expected_ty, false);
    }

    /// Lowers `async { … }` / `own async { … }` into an `is_async = true` `HirFnMeta` + `async_future_make`.
    fn lowerAsyncBlockExprWithMode(
        self: *HirLowerer,
        block_id: NodeIndex,
        expected_ty: TypeId,
        is_forced_own: bool,
    ) anyerror!HirIndex {
        const block_node = self.ast_arena.getNode(block_id);
        const tok = block_node.main_token;
        const checked_ty = if (!expected_ty.isError())
            self.concreteType(expected_ty)
        else
            self.concreteType(self.nodeType(block_id));
        const ret_ty = if (self.pool.getFutureOutputType(checked_ty)) |out_t|
            self.concreteType(out_t)
        else if (!checked_ty.isError())
            checked_ty
        else
            .unit_ty;

        const block_cst = self.ast_arena.getCstOrigin(block_id);
        const has_own_mod = is_forced_own or self.hasModifierInCst(block_cst, .kw_own, "own");
        const clos_sig_ty = try self.pool.internClosureSignatureExt(
            &.{},
            &.{},
            ret_ty,
            .{},
            if (has_own_mod) .auto_drop_tier else .copy_tier,
            false,
            true,
            true,
        );

        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_loop_id = self.current_loop_id;
        const saved_loop_floor = self.closure_loop_stack_floor;
        const saved_in_ct_for = self.is_in_comptime_for;
        const was_in_cond_scope = self.is_in_cond_scope;
        const saved_ceil = self.closure_outer_local_ceil;
        const saved_caller_loc = self.active_caller_loc_local;
        const local_checkpoint = self.local_shadow_log.items.len;
        defer {
            self.popLexicalLocalsTo(local_checkpoint);
            self.active_caller_loc_local = saved_caller_loc;
            self.closure_outer_local_ceil = saved_ceil;
            self.is_in_cond_scope = was_in_cond_scope;
            self.is_in_comptime_for = saved_in_ct_for;
            self.closure_loop_stack_floor = saved_loop_floor;
            self.current_loop_id = saved_loop_id;
            self.current_fn_ret_ty = saved_ret_ty;
        }

        const return_local_id = try self.store.appendLocal(.{
            .name = .empty,
            .type_id = ret_ty,
            .decl_span = self.astSpan(block_id),
            .mode = .set_mode,
            .is_mut = true,
            .is_param = false,
            .is_temp = true,
        });
        const param_local_start: u32 = @intCast(self.store.locals.items.len);
        self.closure_outer_local_ceil = return_local_id;
        try self.closure_frame_stack.append(self.allocator, .{ .ceil = return_local_id });
        defer {
            var popped_frame = self.closure_frame_stack.pop().?;
            popped_frame.captures.deinit(self.allocator);
        }
        self.active_caller_loc_local = null;
        self.current_fn_ret_ty = ret_ty;
        self.current_loop_id = null;
        self.closure_loop_stack_floor = self.loop_stack.items.len;
        self.is_in_comptime_for = false;
        self.is_in_cond_scope = false;

        const fn_meta_idx: u32 = @intCast(self.store.functions.items.len);
        const synth_def = self.mintSyntheticClosureDefId();
        try self.store.functions.append(self.allocator, .{
            .def_id = synth_def,
            .fn_ty = clos_sig_ty,
            .ret_ty = ret_ty,
            .return_local_id = return_local_id,
            .param_local_start = param_local_start,
            .param_len = 0,
            .is_local_closure = !has_own_mod,
            .is_move_closure = has_own_mod,
            .is_async = true,
        });

        const body_hir = try self.lowerBlockBodyContents(block_id, ret_ty, true);
        const cap_slice = self.closure_frame_stack.items[self.closure_frame_stack.items.len - 1].captures.items;
        const cap_extra_start = if (cap_slice.len > 0) try self.store.appendExtraSlice(cap_slice) else 0;

        var final_clos_sig_ty = clos_sig_ty;
        if (has_own_mod) {
            var has_lin_cap = false;
            var cap_i: usize = 0;
            while (cap_i + 1 < cap_slice.len) : (cap_i += 2) {
                const outer_lid = cap_slice[cap_i];
                if (outer_lid < self.store.locals.items.len and
                    type_system.hasLinearObligation(self.pool, self.sym_table, self.store.locals.items[outer_lid].type_id))
                {
                    has_lin_cap = true;
                    break;
                }
            }
            if (has_lin_cap) {
                final_clos_sig_ty = try self.pool.internClosureSignatureExt(
                    &.{},
                    &.{},
                    ret_ty,
                    .{},
                    .linear_tier,
                    true,
                    true,
                    true,
                );
            }
        }

        self.store.functions.items[fn_meta_idx].fn_ty = final_clos_sig_ty;
        self.store.functions.items[fn_meta_idx].body_hir = body_hir;
        self.store.functions.items[fn_meta_idx].total_local_len =
            @intCast(self.store.locals.items.len - return_local_id);
        self.store.functions.items[fn_meta_idx].capture_extra_start = cap_extra_start;
        self.store.functions.items[fn_meta_idx].capture_len = @intCast(cap_slice.len / 2);

        const clos_hir = try self.emitNode(.{
            .tag = .hir_closure,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = final_clos_sig_ty,
            .origin_token = tok,
            .data = .{ .lhs = fn_meta_idx, .rhs = body_hir.asInt() },
        }, block_id);

        var loan_args: std.ArrayListUnmanaged(u32) = .empty;
        defer loan_args.deinit(self.allocator);
        if (!has_own_mod) {
            try self.appendClosureBorrowCaptureLoans(
                fn_meta_idx,
                !self.is_in_nursery_body,
                tok,
                &loan_args,
            );
        }

        const out_fut_ty = try self.pool.internFuture(ret_ty, synth_def.asInt());
        return self.emitAsyncFutureMake(synth_def, .none, clos_hir, loan_args.items, out_fut_ty, tok, block_id);
    }

    /// Returns `true` if `sym_idx` belongs to `core.async` or is a built-in `cx.async` entry function.
    fn isCoreAsyncEntrySymbol(self: *const HirLowerer, sym_idx: SymbolIndex, recv_ast_id: NodeIndex) bool {
        if (!sym_idx.isNone()) {
            const unwrapped_idx = self.unwrapAliasSymbolIdx(sym_idx);
            const sym = self.sym_table.getSymbol(unwrapped_idx).*;
            if (sym.flags.is_builtin) return true;
            if (self.sym_table.getFilePackageId(sym.decl_span.file_id) == .std_core) return true;
            if (!self.sym_table.cx_root_scope.isNone() and !sym.scope_id.isNone()) {
                for (self.sym_table.getScopeMembers(self.sym_table.cx_root_scope)) |cx_mem| {
                    const mem_sym = self.sym_table.getSymbol(cx_mem).*;
                    if (mem_sym.kind == .module_sym and mem_sym.target_scope == sym.scope_id and
                        std.mem.eql(u8, mem_sym.name_text, "async"))
                    {
                        return true;
                    }
                }
            }
            return false;
        }
        if (recv_ast_id.isNone() or recv_ast_id.asInt() >= self.ast_arena.countNodes()) return false;
        const recv_node = self.ast_arena.getNode(recv_ast_id);
        if (recv_node.tag == .field_access and recv_node.lhs.tag == .node and recv_node.rhs.tag == .token) {
            const field_lex = symbol_resolver.extractTokenSlice(
                self.source,
                self.tokens,
                TokenIndex.fromInt(recv_node.rhs.payload),
            );
            if (!std.mem.eql(u8, field_lex, "async")) return false;
            const base_id = NodeIndex.fromInt(recv_node.lhs.payload);
            var base_sym = self.nodeSymbol(base_id);
            if (base_sym.isNone() and self.ast_arena.getNode(base_id).tag == .ident_expr) {
                const base_tok = self.ast_arena.getNode(base_id).main_token;
                if (!base_tok.isNone()) {
                    const base_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, base_tok);
                    if (self.interner.lookup(base_lex)) |base_name_id| {
                        switch (self.sym_table.lookupLexical(self.current_scope, base_name_id, NamespaceMask.ALL)) {
                            .found => |found_idx| base_sym = found_idx,
                            else => {},
                        }
                    }
                }
            }
            if (!base_sym.isNone()) {
                const unwrapped_base = self.unwrapAliasSymbolIdx(base_sym);
                return self.sym_table.getSymbol(unwrapped_base).target_scope == self.sym_table.cx_root_scope;
            }
        }
        return false;
    }

    /// Lowers `core.async` / `cx.async` `yield_now()`, `block_on(fut)`, and `task_group(cb)` calls.
    fn tryLowerStructuredAsyncEntryCall(
        self: *HirLowerer,
        expr_id: NodeIndex,
        resolved_sym_idx: SymbolIndex,
        callee_or_recv_ast: NodeIndex,
        explicit_member_name: ?[]const u8,
        val_args: []const NodeIndex,
        target_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!?HirIndex {
        const entry_name: []const u8 = if (explicit_member_name) |member_lex|
            member_lex
        else if (!resolved_sym_idx.isNone())
            self.sym_table.getSymbol(self.unwrapAliasSymbolIdx(resolved_sym_idx)).name_text
        else blk_name: {
            const callee_node = self.ast_arena.getNode(callee_or_recv_ast);
            if (callee_node.tag == .field_access and callee_node.rhs.tag == .token) {
                break :blk_name symbol_resolver.extractTokenSlice(
                    self.source,
                    self.tokens,
                    TokenIndex.fromInt(callee_node.rhs.payload),
                );
            } else if (callee_node.tag == .ident_expr and !callee_node.main_token.isNone()) {
                break :blk_name symbol_resolver.extractTokenSlice(self.source, self.tokens, callee_node.main_token);
            }
            return null;
        };

        if (!CORE_ASYNC_ENTRY_MAP.has(entry_name)) {
            return null;
        }

        const recv_for_check = if (explicit_member_name != null)
            callee_or_recv_ast
        else blk_recv: {
            const callee_node = self.ast_arena.getNode(callee_or_recv_ast);
            if (callee_node.tag == .field_access and callee_node.lhs.tag == .node) {
                break :blk_recv NodeIndex.fromInt(callee_node.lhs.payload);
            }
            break :blk_recv NodeIndex.none;
        };
        if (!self.isCoreAsyncEntrySymbol(resolved_sym_idx, recv_for_check)) return null;

        const raw_out_ty = if (!target_ty.isError()) target_ty else self.nodeType(expr_id);
        const out_ty = self.concreteType(if (!raw_out_ty.isError()) raw_out_ty else .unit_ty);

        if (std.mem.eql(u8, entry_name, "yield_now")) {
            return try self.emitInternalIntrinsic(.async_yield, &.{}, out_ty, tok, expr_id);
        } else if (std.mem.eql(u8, entry_name, "block_on")) {
            if (val_args.len == 0) return try self.emitErrorHole(tok, expr_id, out_ty);
            const fut_ast = self.unwrapCallArgAst(val_args[0]);
            const fut_hir = try self.lowerExpr(fut_ast, .err_ty);
            return try self.emitInternalIntrinsic(
                .async_block_on,
                &[1]u32{fut_hir.asInt()},
                out_ty,
                tok,
                expr_id,
            );
        } else {
            if (val_args.len == 0) return try self.emitErrorHole(tok, expr_id, out_ty);
            return try self.lowerStructuredTaskGroupCall(
                expr_id,
                self.unwrapCallArgAst(val_args[0]),
                out_ty,
                tok,
            );
        }
    }

    /// Lowers `task_group(cb)` into an `is_async = true` nursery `HirFnMeta` guarded by `async_task_group_enter`/`exit`.
    fn lowerStructuredTaskGroupCall(
        self: *HirLowerer,
        expr_id: NodeIndex,
        cb_ast_id: NodeIndex,
        out_fut_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!HirIndex {
        const res_ty = if (self.pool.getFutureOutputType(out_fut_ty)) |inner_res|
            self.concreteType(inner_res)
        else if (!out_fut_ty.isError())
            out_fut_ty
        else
            .unit_ty;

        const cb_ty = self.nodeType(cb_ast_id);
        const cb_sig = self.pool.getFnSignatureView(cb_ty);
        const group_ref_ty = if (cb_sig) |sv|
            (if (sv.paramCount() >= 1)
                self.concreteType(sv.getParamType(0))
            else
                try self.pool.internRef(try self.pool.internTaskGroup(.never_ty), true))
        else
            try self.pool.internRef(try self.pool.internTaskGroup(.never_ty), true);
        const group_val_ty = self.concreteType(self.unwrapRefType(group_ref_ty));

        const nursery_clos_ty = try self.pool.internClosureSignatureExt(
            &.{},
            &.{},
            res_ty,
            .{},
            .copy_tier,
            false,
            true,
            true,
        );

        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_loop_id = self.current_loop_id;
        const saved_loop_floor = self.closure_loop_stack_floor;
        const saved_in_ct_for = self.is_in_comptime_for;
        const was_in_cond_scope = self.is_in_cond_scope;
        const saved_ceil = self.closure_outer_local_ceil;
        const saved_caller_loc = self.active_caller_loc_local;
        const saved_in_nursery = self.is_in_nursery_body;
        const local_checkpoint = self.local_shadow_log.items.len;
        defer {
            self.popLexicalLocalsTo(local_checkpoint);
            self.is_in_nursery_body = saved_in_nursery;
            self.active_caller_loc_local = saved_caller_loc;
            self.closure_outer_local_ceil = saved_ceil;
            self.is_in_cond_scope = was_in_cond_scope;
            self.is_in_comptime_for = saved_in_ct_for;
            self.closure_loop_stack_floor = saved_loop_floor;
            self.current_loop_id = saved_loop_id;
            self.current_fn_ret_ty = saved_ret_ty;
        }

        const return_local_id = try self.store.appendLocal(.{
            .name = .empty,
            .type_id = res_ty,
            .decl_span = self.astSpan(expr_id),
            .mode = .set_mode,
            .is_mut = true,
            .is_param = false,
            .is_temp = true,
        });
        const param_local_start: u32 = @intCast(self.store.locals.items.len);
        self.closure_outer_local_ceil = return_local_id;
        try self.closure_frame_stack.append(self.allocator, .{ .ceil = return_local_id });
        defer {
            var popped_frame = self.closure_frame_stack.pop().?;
            popped_frame.captures.deinit(self.allocator);
        }
        self.active_caller_loc_local = null;
        self.current_fn_ret_ty = res_ty;
        self.current_loop_id = null;
        self.closure_loop_stack_floor = self.loop_stack.items.len;
        self.is_in_comptime_for = false;
        self.is_in_cond_scope = false;
        self.is_in_nursery_body = true;

        const fn_meta_idx: u32 = @intCast(self.store.functions.items.len);
        const synth_def = self.mintSyntheticClosureDefId();
        try self.store.functions.append(self.allocator, .{
            .def_id = synth_def,
            .fn_ty = nursery_clos_ty,
            .ret_ty = res_ty,
            .return_local_id = return_local_id,
            .param_local_start = param_local_start,
            .param_len = 0,
            .is_local_closure = true,
            .is_move_closure = false,
            .is_async = true,
        });

        // [1] Enter nursery (`let mut _group = async_task_group_enter()`) & register LIFO `defer` exit barrier:
        var outer_stmts: std.ArrayListUnmanaged(u32) = .empty;
        defer outer_stmts.deinit(self.allocator);

        const group_val_slot = try self.allocTempLocal(group_val_ty, tok, true);
        const enter_hir = try self.emitInternalIntrinsic(.async_task_group_enter, &.{}, group_val_ty, tok, .none);
        try outer_stmts.append(self.allocator, (try self.emitLocalDeclNode(group_val_slot, enter_hir, tok)).asInt());

        const exit_group_ref = try self.emitVarRef(group_val_slot, tok, .none);
        const exit_hir = try self.emitInternalIntrinsic(
            .async_task_group_exit,
            &[1]u32{exit_group_ref.asInt()},
            .unit_ty,
            tok,
            .none,
        );
        const defer_hir = try self.emitNode(.{
            .tag = .hir_defer,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = .unit_ty,
            .origin_token = tok,
            .data = .{ .lhs = 0, .rhs = exit_hir.asInt() },
        }, .none);
        try outer_stmts.append(self.allocator, defer_hir.asInt());

        // [2] Bind `&mut _group` to callback parameter and lower callback body inline inside the nursery frame:
        const cb_node = self.ast_arena.getNode(cb_ast_id);
        var callback_res_hir: HirIndex = .none;
        if (cb_node.tag == .closure_expr) {
            const param_tokens = self.getAstExtraSlice(cb_ast_id, false);
            var param_name = SymbolId.empty;
            var param_span = self.astSpan(cb_ast_id);
            if (param_tokens.len >= 1) {
                const param_tok = TokenIndex.fromInt(param_tokens[0]);
                const param_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, param_tok);
                if (param_lex.len > 0 and !std.mem.eql(u8, param_lex, "_")) {
                    param_name = try self.interner.intern(param_lex);
                }
                param_span = self.tokens.getTokenSpan(self.store.file_id, param_tok);
            }
            const group_borrow_hir = try self.emitSyntheticAddrOf(
                try self.emitVarRef(group_val_slot, tok, .none),
                group_ref_ty,
                true,
                tok,
            );
            const group_param_slot = try self.store.appendLocal(.{
                .name = param_name,
                .type_id = group_ref_ty,
                .decl_span = param_span,
                .mode = .let_mode,
                .is_mut = false,
                .is_param = false,
                .is_temp = false,
            });
            try outer_stmts.append(
                self.allocator,
                (try self.emitLocalDeclNode(group_param_slot, group_borrow_hir, tok)).asInt(),
            );
            try self.pushLexicalLocal(param_name, group_param_slot);

            if (cb_node.rhs.tag == .node) {
                const cb_body_id = NodeIndex.fromInt(cb_node.rhs.payload);
                const cb_ret_expected = if (cb_sig) |sv| self.concreteType(sv.ret_ty) else res_ty;
                if (self.ast_arena.getNode(cb_body_id).tag == .block) {
                    callback_res_hir = try self.lowerBlockBodyContents(cb_body_id, cb_ret_expected, false);
                } else {
                    callback_res_hir = try self.lowerExpr(cb_body_id, cb_ret_expected);
                }
            } else {
                callback_res_hir = try self.emitUnitConst(tok, .none);
            }
        } else {
            const callee_hir = try self.lowerExpr(cb_ast_id, .err_ty);
            const group_borrow_hir = try self.emitSyntheticAddrOf(
                try self.emitVarRef(group_val_slot, tok, .none),
                group_ref_ty,
                true,
                tok,
            );
            const proj_arg = try self.wrapArgProjection(group_borrow_hir, .let_mode, tok);
            if (cb_sig != null and cb_sig.?.is_async) {
                const inner_fut_ty = try self.pool.internFuture(res_ty, 0);
                const inner_fut_hir = try self.emitAsyncFutureMake(
                    .NONE,
                    .none,
                    callee_hir,
                    &[1]u32{proj_arg.asInt()},
                    inner_fut_ty,
                    tok,
                    .none,
                );
                callback_res_hir = try self.emitNode(.{
                    .tag = .hir_await,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = res_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = inner_fut_hir.asInt(), .rhs = 0 },
                }, .none);
            } else {
                const call_extra = try self.store.appendLenPrefixedExtra(&[1]u32{proj_arg.asInt()});
                callback_res_hir = try self.emitNode(.{
                    .tag = .hir_call,
                    .flags = .{ .category = .rvalue, .is_synthetic = true },
                    .type_id = res_ty,
                    .origin_token = tok,
                    .data = .{ .lhs = callee_hir.asInt(), .rhs = call_extra },
                }, .none);
            }
        }

        if (!callback_res_hir.isNone() and self.store.getNode(callback_res_hir).type_id == .never_ty) {
            try outer_stmts.append(self.allocator, callback_res_hir.asInt());
        } else {
            const ret_val_hir = if (!callback_res_hir.isNone())
                try self.applyImplicitCoercionIfNeeded(callback_res_hir, res_ty, tok)
            else
                try self.emitUnitConst(tok, .none);
            const err_kind = self.classifyReturnExpr(ret_val_hir, res_ty);
            const ret_node = try self.emitNode(.{
                .tag = .hir_return,
                .flags = .{ .category = .diverging, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
                .type_id = .never_ty,
                .origin_token = tok,
                .data = .{ .lhs = ret_val_hir.asInt(), .rhs = @backingInt(err_kind) },
            }, .none);
            try outer_stmts.append(self.allocator, ret_node.asInt());
        }

        const body_extra = try self.store.appendLenPrefixedExtra(outer_stmts.items);
        const body_hir = try self.emitNode(.{
            .tag = .hir_block,
            .flags = .{ .category = .diverging, .is_synthetic = true, .is_unsafe = self.is_in_unsafe },
            .type_id = .never_ty,
            .origin_token = tok,
            .data = .{ .lhs = body_extra, .rhs = HirIndex.none.asInt() },
        }, .none);

        const cap_slice = self.closure_frame_stack.items[self.closure_frame_stack.items.len - 1].captures.items;
        const cap_extra_start = if (cap_slice.len > 0) try self.store.appendExtraSlice(cap_slice) else 0;
        self.store.functions.items[fn_meta_idx].body_hir = body_hir;
        self.store.functions.items[fn_meta_idx].total_local_len =
            @intCast(self.store.locals.items.len - return_local_id);
        self.store.functions.items[fn_meta_idx].capture_extra_start = cap_extra_start;
        self.store.functions.items[fn_meta_idx].capture_len = @intCast(cap_slice.len / 2);

        const clos_hir = try self.emitNode(.{
            .tag = .hir_closure,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = nursery_clos_ty,
            .origin_token = tok,
            .data = .{ .lhs = fn_meta_idx, .rhs = body_hir.asInt() },
        }, expr_id);

        var loan_args: std.ArrayListUnmanaged(u32) = .empty;
        defer loan_args.deinit(self.allocator);
        try self.appendClosureBorrowCaptureLoans(fn_meta_idx, false, tok, &loan_args);

        const final_fut_ty = try self.pool.internFuture(res_ty, synth_def.asInt());
        return self.emitAsyncFutureMake(synth_def, .none, clos_hir, loan_args.items, final_fut_ty, tok, expr_id);
    }

    /// Returns `true` if `ty` is built-in `TaskGroup[E]` or `core.async.TaskGroup[E]`.
    fn isTaskGroupLikeType(self: *const HirLowerer, raw_ty: TypeId) bool {
        const ty = self.pool.unwrapUnderlyingType(raw_ty);
        if (self.pool.isTaskGroupType(ty)) return true;
        if (self.pool.getTag(ty) == .struct_ty) {
            const sym_idx = SymbolIndex.fromInt(self.pool.getNode(ty).rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) {
                const sym = self.sym_table.getSymbol(sym_idx).*;
                return type_system.isStdCoreOrBuiltinSymbol(self.sym_table, sym) and
                    std.mem.eql(u8, sym.name_text, "TaskGroup");
            }
        }
        return false;
    }

    /// Returns `true` if `ty` is built-in `TaskHandle[T]` or `core.async.TaskHandle[T]`.
    fn isTaskHandleLikeType(self: *const HirLowerer, raw_ty: TypeId) bool {
        const ty = self.pool.unwrapUnderlyingType(raw_ty);
        if (self.pool.isTaskHandleType(ty)) return true;
        if (self.pool.getTag(ty) == .struct_ty) {
            const sym_idx = SymbolIndex.fromInt(self.pool.getNode(ty).rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) {
                const sym = self.sym_table.getSymbol(sym_idx).*;
                return type_system.isStdCoreOrBuiltinSymbol(self.sym_table, sym) and
                    std.mem.eql(u8, sym.name_text, "TaskHandle");
            }
        }
        return false;
    }

    /// Lowers `TaskGroup` (`spawn`, `spawn_local`, `cancel_all`, `is_cancelled`) and `TaskHandle` (`join`, `cancel`) calls.
    fn tryLowerTaskGroupOrHandleMethod(
        self: *HirLowerer,
        expr_id: NodeIndex,
        recv_id: NodeIndex,
        member_name: []const u8,
        val_args: []const NodeIndex,
        target_ty: TypeId,
        tok: TokenIndex,
    ) anyerror!?HirIndex {
        const recv_unwrapped = self.pool.unwrapUnderlyingType(self.unwrapRefType(self.nodeType(recv_id)));
        const raw_out_ty = if (!target_ty.isError()) target_ty else self.nodeType(expr_id);
        const out_ty = self.concreteType(if (!raw_out_ty.isError()) raw_out_ty else .unit_ty);

        if (self.isTaskGroupLikeType(recv_unwrapped)) {
            const is_spawn = std.mem.eql(u8, member_name, "spawn");
            const is_spawn_local = std.mem.eql(u8, member_name, "spawn_local");
            if (is_spawn or is_spawn_local) {
                if (val_args.len == 0) return try self.emitErrorHole(tok, expr_id, out_ty);
                const raw_group_hir = try self.lowerPlaceWithMutCtx(recv_id, .err_ty, true);
                const group_ref_hir = try self.reborrowOrAddrOfTaskGroup(raw_group_hir, true, tok);

                const task_ast = self.unwrapCallArgAst(val_args[0]);
                const builder_state_ty = if (self.side_tables) |tables|
                    tables.getBuilderBlockStateType(expr_id)
                else
                    null;
                const raw_task_hir = if (builder_state_ty != null and self.ast_arena.getNode(task_ast).tag == .block)
                    try self.lowerBuilderTrailingBlockClosure(task_ast, builder_state_ty.?, .err_ty, tok)
                else
                    try self.lowerExpr(task_ast, .err_ty);

                var spawn_args: std.ArrayListUnmanaged(u32) = .empty;
                defer spawn_args.deinit(self.allocator);
                const local_flag = try self.emitConstVal(
                    .{ .int_val = if (is_spawn_local) 1 else 0 },
                    .u32_ty,
                    tok,
                    .none,
                    true,
                );
                try spawn_args.append(self.allocator, local_flag.asInt());
                try spawn_args.append(self.allocator, group_ref_hir.asInt());

                if (!raw_task_hir.isNone() and self.store.getNode(raw_task_hir).tag == .hir_closure) {
                    const clos_meta_idx = self.store.getNode(raw_task_hir).data.lhs;
                    const clos_meta = self.store.functions.items[clos_meta_idx];
                    const fut_ty = try self.pool.internFuture(clos_meta.ret_ty, clos_meta.def_id.asInt());
                    const wrapped_fut = try self.emitAsyncFutureMake(
                        clos_meta.def_id,
                        .none,
                        raw_task_hir,
                        &.{},
                        fut_ty,
                        tok,
                        .none,
                    );
                    try spawn_args.append(self.allocator, wrapped_fut.asInt());
                    if (!clos_meta.is_move_closure) {
                        try self.appendClosureBorrowCaptureLoans(clos_meta_idx, false, tok, &spawn_args);
                    }
                } else {
                    try spawn_args.append(self.allocator, raw_task_hir.asInt());
                }

                return try self.emitInternalIntrinsic(.async_spawn, spawn_args.items, out_ty, tok, expr_id);
            }
            if (std.mem.eql(u8, member_name, "cancel_all") or std.mem.eql(u8, member_name, "cancel")) {
                const raw_group_hir = try self.lowerPlaceWithMutCtx(recv_id, .err_ty, true);
                const group_ref_hir = try self.reborrowOrAddrOfTaskGroup(raw_group_hir, true, tok);
                return try self.emitInternalIntrinsic(
                    .async_cancel,
                    &[1]u32{group_ref_hir.asInt()},
                    .unit_ty,
                    tok,
                    expr_id,
                );
            }
            if (std.mem.eql(u8, member_name, "is_cancelled")) {
                const raw_group_hir = try self.lowerPlaceWithMutCtx(recv_id, .err_ty, false);
                const group_ref_hir = try self.reborrowOrAddrOfTaskGroup(raw_group_hir, false, tok);
                const query_flag = try self.emitConstVal(.{ .int_val = 1 }, .u32_ty, tok, .none, true);
                return try self.emitInternalIntrinsic(
                    .async_cancel,
                    &[2]u32{ group_ref_hir.asInt(), query_flag.asInt() },
                    .bool_ty,
                    tok,
                    expr_id,
                );
            }
        }

        if (self.isTaskHandleLikeType(recv_unwrapped)) {
            if (std.mem.eql(u8, member_name, "join")) {
                const handle_hir = try self.lowerExpr(recv_id, .err_ty);
                return try self.emitInternalIntrinsic(
                    .async_join,
                    &[1]u32{handle_hir.asInt()},
                    out_ty,
                    tok,
                    expr_id,
                );
            }
            if (std.mem.eql(u8, member_name, "cancel")) {
                const handle_hir = try self.lowerExpr(recv_id, .err_ty);
                return try self.emitInternalIntrinsic(
                    .async_cancel,
                    &[1]u32{handle_hir.asInt()},
                    out_ty,
                    tok,
                    expr_id,
                );
            }
        }
        return null;
    }

    /// Reborrows `&mut (group.*)` when `raw_group_hir` is `&mut TaskGroup` so `group` is not moved on method calls.
    fn reborrowOrAddrOfTaskGroup(
        self: *HirLowerer,
        raw_group_hir: HirIndex,
        is_mut: bool,
        tok: TokenIndex,
    ) !HirIndex {
        const raw_group_ty = self.pool.unwrapUnderlyingType(self.store.getNode(raw_group_hir).type_id);
        const tag = self.pool.getTag(raw_group_ty);
        if (tag == .mut_ref_ty) {
            const pointee_ty = self.concreteType(TypeId.fromInt(self.pool.getNode(raw_group_ty).lhs));
            const deref_hir = try self.emitNode(.{
                .tag = .hir_unary_op,
                .flags = .{ .category = .place_mut, .is_synthetic = true },
                .type_id = pointee_ty,
                .origin_token = tok,
                .data = .{
                    .lhs = @backingInt(HirUnaryOp.deref),
                    .rhs = raw_group_hir.asInt(),
                },
            }, .none);
            return self.emitSyntheticAddrOf(
                deref_hir,
                try self.pool.internRef(pointee_ty, is_mut),
                is_mut,
                tok,
            );
        }
        if (tag == .ref_ty and !is_mut) {
            return raw_group_hir;
        }
        return self.emitSyntheticAddrOf(
            raw_group_hir,
            try self.pool.internRef(raw_group_ty, is_mut),
            is_mut,
            tok,
        );
    }

    /// Emits `&outer_local` / `&mut outer_local` loan arguments for outer bindings borrowed by `fn_meta_idx`.
    fn appendClosureBorrowCaptureLoans(
        self: *HirLowerer,
        fn_meta_idx: u32,
        is_skip_immutable_copy: bool,
        tok: TokenIndex,
        out_args: *std.ArrayListUnmanaged(u32),
    ) !void {
        if (fn_meta_idx >= self.store.functions.items.len) return;
        const fn_meta = self.store.functions.items[fn_meta_idx];
        if (fn_meta.is_move_closure) return;
        for (0..fn_meta.capture_len) |cap_i| {
            const outer_slot = self.store.extra_data.items[fn_meta.capture_extra_start + cap_i * 2];
            const inner_slot = self.store.extra_data.items[fn_meta.capture_extra_start + cap_i * 2 + 1];
            if (outer_slot >= self.store.locals.items.len) continue;
            const outer_decl = self.store.locals.items[outer_slot];
            const outer_tag = self.pool.getTag(self.pool.unwrapUnderlyingType(outer_decl.type_id));
            // Reference-typed captures (`&T` / `&mut T`) already propagate their NLL loan via `closure_make`:
            if (outer_tag == .ref_ty or outer_tag == .mut_ref_ty) continue;
            if (fn_meta.is_move_closure and !self.pool.getFlags(outer_decl.type_id).is_copy) continue;

            const is_mutated = self.isHirSlotMutatedInSubtree(fn_meta.body_hir, inner_slot);
            if (!is_mutated and is_skip_immutable_copy and !outer_decl.is_mut) continue;

            const var_ref_hir = try self.emitNode(.{
                .tag = .hir_var_ref,
                .flags = .{
                    .category = if (outer_decl.is_mut or outer_decl.mode == .inout_mode or outer_decl.mode == .set_mode)
                        .place_mut
                    else
                        .place_imm,
                    .is_synthetic = true,
                },
                .type_id = outer_decl.type_id,
                .origin_token = tok,
                .data = .{ .lhs = outer_slot, .rhs = 0 },
            }, .none);
            const ref_ty = try self.pool.internRef(outer_decl.type_id, is_mutated);
            const borrow_hir = try self.emitSyntheticAddrOf(var_ref_hir, ref_ty, is_mutated, tok);
            try out_args.append(self.allocator, borrow_hir.asInt());
        }
    }

    /// Returns `true` if `target_slot` is assigned or mutably borrowed anywhere inside `root_hir`.
    fn isHirSlotMutatedInSubtree(self: *const HirLowerer, root_hir: HirIndex, target_slot: u32) bool {
        return self.isHirSlotMutatedInSubtreeDepth(root_hir, target_slot, 0);
    }

    /// Bounded recursive helper checking whether `target_slot` is mutated across nested expressions and closures.
    fn isHirSlotMutatedInSubtreeDepth(
        self: *const HirLowerer,
        root_hir: HirIndex,
        target_slot: u32,
        depth: u32,
    ) bool {
        if (depth >= 32 or root_hir.isNone() or root_hir.asInt() >= self.store.nodes.len) return false;
        var visit_stack: std.ArrayListUnmanaged(u32) = .empty;
        defer visit_stack.deinit(self.allocator);
        visit_stack.append(self.allocator, root_hir.asInt()) catch return false;

        while (visit_stack.pop()) |cur_raw| {
            if (cur_raw == NONE_U32 or cur_raw >= self.store.nodes.len) continue;
            const cur_node = self.store.getNode(HirIndex.fromInt(cur_raw));
            switch (cur_node.tag) {
                .hir_assign, .hir_bitfield_rmw => {
                    if (self.extractRootHirSlot(HirIndex.fromInt(cur_node.data.lhs)) == target_slot) return true;
                    visit_stack.append(self.allocator, cur_node.data.lhs) catch {};
                    if (cur_node.tag == .hir_assign) {
                        visit_stack.append(self.allocator, cur_node.data.rhs) catch {};
                    } else if (cur_node.data.rhs + 2 <= self.store.extra_data.items.len) {
                        visit_stack.append(self.allocator, self.store.extra_data.items[cur_node.data.rhs + 1]) catch {};
                    }
                },
                .hir_unary_op => {
                    const un_op: HirUnaryOp = @fromBackingInt(@intCast(@as(u8, @truncate(cur_node.data.lhs))));
                    if ((un_op == .addr_of_mut or un_op == .addr_of_raw_mut) and
                        self.extractRootHirSlot(HirIndex.fromInt(cur_node.data.rhs)) == target_slot)
                    {
                        return true;
                    }
                    visit_stack.append(self.allocator, cur_node.data.rhs) catch {};
                },
                .hir_project_arg => {
                    const mode: ParamMode = @fromBackingInt(@intCast(@as(u2, @truncate(cur_node.data.lhs))));
                    if ((mode == .inout_mode or mode == .set_mode) and
                        self.extractRootHirSlot(HirIndex.fromInt(cur_node.data.rhs)) == target_slot)
                    {
                        return true;
                    }
                    visit_stack.append(self.allocator, cur_node.data.rhs) catch {};
                },
                .hir_block => {
                    for (self.store.getLenPrefixedExtra(cur_node.data.lhs)) |stmt_raw| {
                        visit_stack.append(self.allocator, stmt_raw) catch {};
                    }
                    visit_stack.append(self.allocator, cur_node.data.rhs) catch {};
                },
                .hir_local_decl, .hir_const_decl, .hir_defer, .hir_ctx_set, .hir_ctx_region_push, .hir_break => {
                    visit_stack.append(self.allocator, cur_node.data.rhs) catch {};
                },
                .hir_field_proj, .hir_bitfield_read, .hir_cast, .hir_return, .hir_yield, .hir_loop, .hir_await => {
                    visit_stack.append(self.allocator, cur_node.data.lhs) catch {};
                },
                .hir_index_proj, .hir_orelse => {
                    visit_stack.append(self.allocator, cur_node.data.lhs) catch {};
                    visit_stack.append(self.allocator, cur_node.data.rhs) catch {};
                },
                .hir_soa_field_ptr => {
                    visit_stack.append(self.allocator, cur_node.data.lhs) catch {};
                    if (cur_node.data.rhs + 2 <= self.store.extra_data.items.len) {
                        visit_stack.append(self.allocator, self.store.extra_data.items[cur_node.data.rhs + 1]) catch {};
                    }
                },
                .hir_slice_range => {
                    visit_stack.append(self.allocator, cur_node.data.lhs) catch {};
                    if (cur_node.data.rhs + 3 <= self.store.extra_data.items.len) {
                        visit_stack.append(self.allocator, self.store.extra_data.items[cur_node.data.rhs]) catch {};
                        visit_stack.append(self.allocator, self.store.extra_data.items[cur_node.data.rhs + 1]) catch {};
                    }
                },
                .hir_binary_op => {
                    if (cur_node.data.lhs + 2 <= self.store.extra_data.items.len) {
                        visit_stack.append(self.allocator, self.store.extra_data.items[cur_node.data.lhs]) catch {};
                        visit_stack.append(self.allocator, self.store.extra_data.items[cur_node.data.lhs + 1]) catch {};
                    }
                },
                .hir_if => {
                    visit_stack.append(self.allocator, cur_node.data.lhs) catch {};
                    if (cur_node.data.rhs + 2 <= self.store.extra_data.items.len) {
                        visit_stack.append(self.allocator, self.store.extra_data.items[cur_node.data.rhs]) catch {};
                        visit_stack.append(self.allocator, self.store.extra_data.items[cur_node.data.rhs + 1]) catch {};
                    }
                },
                .hir_cond_if, .hir_cond_while => {
                    if (cur_node.data.lhs < self.store.extra_data.items.len) {
                        const clause_count = self.store.extra_data.items[cur_node.data.lhs];
                        var cursor: usize = cur_node.data.lhs + 1;
                        var clause_i: u32 = 0;
                        while (clause_i < clause_count and cursor < self.store.extra_data.items.len) : (clause_i += 1) {
                            const clause_kind = self.store.extra_data.items[cursor];
                            if (clause_kind == @backingInt(HirCondClauseKind.bool_pred) and
                                cursor + 1 < self.store.extra_data.items.len)
                            {
                                visit_stack.append(self.allocator, self.store.extra_data.items[cursor + 1]) catch {};
                                cursor += 2;
                            } else if (clause_kind == @backingInt(HirCondClauseKind.is_match) and
                                cursor + 2 < self.store.extra_data.items.len)
                            {
                                visit_stack.append(self.allocator, self.store.extra_data.items[cursor + 1]) catch {};
                                cursor += 3;
                            } else {
                                break;
                            }
                        }
                        if (cursor < self.store.extra_data.items.len) {
                            visit_stack.append(self.allocator, self.store.extra_data.items[cursor]) catch {};
                        }
                        if (cur_node.tag == .hir_cond_if and cursor + 1 < self.store.extra_data.items.len) {
                            visit_stack.append(self.allocator, self.store.extra_data.items[cursor + 1]) catch {};
                        }
                    }
                },
                .hir_construct => {
                    const ckind: HirConstructKind = @fromBackingInt(@intCast(@as(u8, @truncate(cur_node.data.lhs))));
                    switch (ckind) {
                        .struct_init,
                        .tuple_init,
                        .array_elements,
                        .enum_variant,
                        .optional_some,
                        .result_ok,
                        .result_err,
                        .str_interp,
                        => {
                            for (self.store.getLenPrefixedExtra(cur_node.data.rhs)) |elem_raw| {
                                visit_stack.append(self.allocator, elem_raw) catch {};
                            }
                        },
                        .array_repeat => {
                            if (cur_node.data.rhs + 2 <= self.store.extra_data.items.len) {
                                visit_stack.append(
                                    self.allocator,
                                    self.store.extra_data.items[cur_node.data.rhs + 1],
                                ) catch {};
                            }
                        },
                        .fmt_value => {
                            if (cur_node.data.rhs + 3 <= self.store.extra_data.items.len) {
                                visit_stack.append(self.allocator, self.store.extra_data.items[cur_node.data.rhs]) catch {};
                            }
                        },
                        .fmt_args => {
                            if (cur_node.data.rhs + 2 <= self.store.extra_data.items.len) {
                                const piece_len = self.store.extra_data.items[cur_node.data.rhs];
                                const hole_len = self.store.extra_data.items[cur_node.data.rhs + 1];
                                const holes_start: usize = cur_node.data.rhs + 2 + piece_len;
                                var hole_i: usize = 0;
                                while (hole_i < hole_len) : (hole_i += 1) {
                                    const hole_pos = holes_start + hole_i * 3;
                                    if (hole_pos >= self.store.extra_data.items.len) break;
                                    visit_stack.append(self.allocator, self.store.extra_data.items[hole_pos]) catch {};
                                }
                            }
                        },
                        .optional_none, .bitfield_zero => {},
                    }
                },
                .hir_closure => {
                    if (cur_node.data.lhs < self.store.functions.items.len) {
                        const sub_fn_meta = self.store.functions.items[cur_node.data.lhs];
                        if (!sub_fn_meta.is_move_closure) {
                            for (0..sub_fn_meta.capture_len) |cap_i| {
                                const pair_pos = sub_fn_meta.capture_extra_start + cap_i * 2;
                                if (pair_pos + 1 >= self.store.extra_data.items.len) break;
                                const outer_slot = self.store.extra_data.items[pair_pos];
                                const sub_inner_slot = self.store.extra_data.items[pair_pos + 1];
                                if (outer_slot == target_slot and
                                    self.isHirSlotMutatedInSubtreeDepth(sub_fn_meta.body_hir, sub_inner_slot, depth + 1))
                                {
                                    return true;
                                }
                            }
                        }
                    }
                },
                .hir_match => {
                    visit_stack.append(self.allocator, cur_node.data.lhs) catch {};
                    if (cur_node.data.rhs + 2 <= self.store.extra_data.items.len) {
                        const arm_start = self.store.extra_data.items[cur_node.data.rhs];
                        const arm_len = self.store.extra_data.items[cur_node.data.rhs + 1];
                        for (self.store.match_arms.items[arm_start .. arm_start + arm_len]) |arm| {
                            visit_stack.append(self.allocator, arm.guard_hir.asInt()) catch {};
                            visit_stack.append(self.allocator, arm.body_hir.asInt()) catch {};
                        }
                    }
                },
                .hir_call, .hir_subscript_call => {
                    visit_stack.append(self.allocator, cur_node.data.lhs) catch {};
                    for (self.store.getLenPrefixedExtra(cur_node.data.rhs)) |arg_raw| {
                        visit_stack.append(self.allocator, arg_raw) catch {};
                    }
                },
                .hir_intrinsic_call => {
                    if (cur_node.data.rhs + 2 <= self.store.extra_data.items.len) {
                        const type_len = self.store.extra_data.items[cur_node.data.rhs];
                        const val_len = self.store.extra_data.items[cur_node.data.rhs + 1];
                        const val_start = cur_node.data.rhs + 2 + type_len;
                        if (val_start + val_len <= self.store.extra_data.items.len) {
                            for (self.store.extra_data.items[val_start .. val_start + val_len]) |arg_raw| {
                                visit_stack.append(self.allocator, arg_raw) catch {};
                            }
                        }
                    }
                },
                else => {},
            }
        }
        return false;
    }

    /// Extracts the underlying root `store.locals` slot of a place chain (`var_ref`, `field_proj`, `index_proj`, `#soa`).
    fn extractRootHirSlot(self: *const HirLowerer, place_hir: HirIndex) ?u32 {
        var cur_hir = place_hir;
        var steps: u32 = 0;
        while (!cur_hir.isNone() and cur_hir.asInt() < self.store.nodes.len and steps < 32) : (steps += 1) {
            const cur_node = self.store.getNode(cur_hir);
            switch (cur_node.tag) {
                .hir_var_ref => return cur_node.data.lhs,
                .hir_block => {
                    cur_hir = HirIndex.fromInt(cur_node.data.rhs);
                },
                .hir_field_proj,
                .hir_index_proj,
                .hir_soa_field_ptr,
                .hir_bitfield_read,
                .hir_slice_range,
                => {
                    cur_hir = HirIndex.fromInt(cur_node.data.lhs);
                },
                else => return null,
            }
        }
        return null;
    }

    // ---------- CST, Member, Pattern & Comptime Helpers -----------

    /// Returns `true` if any direct shallow token leaf of `cst_id` matches `target_kind`.
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

    /// Returns `true` if a shallow prefix modifier token (`own`, `raw`, `mut`, `out`) appears on `cst_id`.
    fn hasModifierInCst(
        self: *const HirLowerer,
        cst_id: CstNodeIndex,
        target_kind: TokenKind,
        target_lexeme: []const u8,
    ) bool {
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
                if (rec.kind == .prefix_expr and cur + 1 >= end_idx) break;
                const leaf_kind = self.tokens.getToken(sub.token).kind;
                if (rec.kind == .closure_expr and (leaf_kind == .pipe or leaf_kind == .lbrace)) break;
                if (target_kind != .ident and leaf_kind == target_kind) return true;
                if (symbol_resolver.isIdentifierToken(leaf_kind) and
                    std.mem.eql(u8, symbol_resolver.extractTokenSlice(self.source, self.tokens, sub.token), target_lexeme))
                {
                    return true;
                }
            }
            cur += 1;
        }
        return false;
    }

    /// Extracts the optional `label:` identifier token preceding `match` inside `match_expr_id`'s CST (`SE-23`).
    fn extractMatchLabelToken(self: *const HirLowerer, match_expr_id: NodeIndex) TokenIndex {
        if (match_expr_id.isNone() or match_expr_id.asInt() >= self.ast_arena.countNodes()) return .none;
        const match_node = self.ast_arena.getNode(match_expr_id);
        if (match_node.rhs.tag == .token) {
            return TokenIndex.fromInt(match_node.rhs.payload);
        }
        const match_cst = self.ast_arena.getCstOrigin(match_expr_id);
        if (match_cst.isNone() or match_cst.asInt() >= self.cst_arena.countNodes()) return .none;
        const start_idx: usize = match_cst.asInt();
        const rec = self.cst_arena.getNode(match_cst);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var cur = start_idx + 1;
        while (cur < end_idx) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.kind == .loop_label) {
                const lbl_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                var inner = cur + 1;
                while (inner < lbl_end) : (inner += 1) {
                    const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(inner)));
                    if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                        leaf.token.asInt() < self.tokens.countTokens() and
                        symbol_resolver.isIdentifierToken(self.tokens.getToken(leaf.token).kind))
                    {
                        return leaf.token;
                    }
                }
                return .none;
            }
            if (sub.subtree_size > 1) break;
            if (!sub.token.isNone() and sub.token.asInt() < self.tokens.countTokens()) {
                if (self.tokens.getToken(sub.token).kind == .kw_match) break;
            }
            cur += 1;
        }
        return .none;
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

    /// Scans `.match_arm` CST subtrees of `match_expr_id` to recover optional `if guard_expr` AST nodes.
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
            const deref_ty = self.store.getNode(deref_recv).type_id;
            const is_same_nominal_family = blk_nom: {
                const uw_deref = self.pool.unwrapUnderlyingType(deref_ty);
                const uw_wanted = self.pool.unwrapUnderlyingType(wanted_inner);
                if (uw_deref == uw_wanted) break :blk_nom true;
                const sym_a = self.sym_table.type_to_symbol.get(uw_deref.toU32()) orelse break :blk_nom false;
                const sym_b = self.sym_table.type_to_symbol.get(uw_wanted.toU32()) orelse break :blk_nom false;
                break :blk_nom !sym_a.isNone() and sym_a == sym_b;
            };
            if (deref_ty == wanted_inner or is_same_nominal_family or self.pool.getFlags(wanted_inner).has_type_vars) {
                const actual_ref_ty = if (deref_ty == wanted_inner)
                    param_ty
                else
                    try self.pool.internRef(deref_ty, param_node.tag == .mut_ref_ty);
                return self.emitSyntheticAddrOf(
                    deref_recv,
                    actual_ref_ty,
                    param_node.tag == .mut_ref_ty,
                    tok,
                );
            }
        }
        return self.autoDerefPlace(raw_recv_hir, tok);
    }

    /// Wraps `arg_hir` in `hir_project_arg(mode, arg_hir)` (`DR-02` §2.2 & `ADR-22B`).
    fn wrapArgProjection(
        self: *HirLowerer,
        arg_hir: HirIndex,
        mode: ParamMode,
        tok: TokenIndex,
    ) !HirIndex {
        const inner_hir = self.unwrapPlaceProjectionArg(arg_hir, mode);
        return self.emitNode(.{
            .tag = .hir_project_arg,
            .flags = .{ .category = .rvalue, .is_synthetic = true },
            .type_id = self.store.getNode(inner_hir).type_id,
            .origin_token = tok,
            .data = .{ .lhs = @backingInt(mode), .rhs = inner_hir.asInt() },
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

    /// Returns `true` if `sub_sym_idx` declares an explicit `self` parameter in its signature scope (`SE-21`).
    fn hasSubscriptExplicitSelf(self: *const HirLowerer, sub_sym_idx: SymbolIndex) bool {
        if (sub_sym_idx.isNone()) return false;
        const self_sym_id = self.interner.lookup("self") orelse return false;
        const sub_sym = self.sym_table.getSymbol(sub_sym_idx).*;
        const base_fn_scope = if (!sub_sym.target_scope.isNone()) sub_sym.target_scope else sub_sym.scope_id;
        return !self.sym_table.lookupInScopeDirect(
            base_fn_scope,
            self_sym_id,
            NamespaceMask.VALUE_ONLY,
        ).isNone();
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

        const nom_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, unwrapped);
        var ord: u32 = 0;
        for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
            if (!self.isSymbolCfgEnabled(mem_idx)) continue;
            const mem_sym = self.sym_table.getSymbol(mem_idx).*;
            if (mem_sym.kind != .field_sym) continue;
            if (std.mem.eql(u8, mem_sym.name_text, field_name)) {
                return .{ .ordinal = ord, .field_ty = nom_subst.resolve(mem_sym.type_id) };
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
            0;

        const sym_idx = SymbolIndex.fromInt(ty_node.rhs);
        if (sym_idx.isNone() or sym_idx.asInt() >= self.sym_table.symbols.items.len) return null;
        const bf_sym = self.sym_table.getSymbol(sym_idx).*;
        if (bf_sym.target_scope.isNone()) return null;

        var running_offset: u16 = 0;
        for (self.sym_table.getScopeMembers(bf_sym.target_scope)) |mem_idx| {
            if (!self.isSymbolCfgEnabled(mem_idx)) continue;
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
                const capped_off: u15 = @intCast(@min(running_offset, 32767));
                return .{
                    .spec = .{
                        .bit_offset = @truncate(capped_off),
                        .bit_width = @intCast(@min(width, 128)),
                        .backing_bits = backing_bits,
                        .is_signed = is_signed,
                        .bit_offset_hi = @intCast(capped_off >> 8),
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
                    const st_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, ty);
                    for (self.sym_table.getScopeMembers(struct_sym.target_scope)) |mem_idx| {
                        if (!self.isSymbolCfgEnabled(mem_idx)) continue;
                        const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .field_sym) continue;
                        const subst_f_ty = try st_subst.applyMut(self.allocator, self.pool, mem_sym.type_id);
                        try f_hirs.append(
                            self.allocator,
                            (try self.emitDefaultInitValue(subst_f_ty, tok)).asInt(),
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

    /// Lowers a top-level pattern, scoping `or_pat` slot-reuse to bindings within this pattern.
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
                const is_ref = self.hasKeywordInCst(pat_cst, .amp);
                const has_pat_mut = self.hasKeywordInCst(pat_cst, .kw_mut) or self.hasKeywordInCst(pat_cst, .kw_var);
                if (!is_ref and !has_pat_mut and !is_decl_mut) {
                    if (try self.tryEvalConstPatternValue(pat_id, concrete_scrut)) |const_val| {
                        return self.emitConstPatternVal(const_val, concrete_scrut, tok);
                    }
                }
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
                        // Reuse binding slot ONLY across `P1 | P2` alternatives in the SAME top-level pattern:
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
                // Range pattern `low..=high` or `low..high`:
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
                        const unescaped = lexer.cookStringLiteral(self.allocator, raw_str) catch blk_fallback: {
                            if (raw_str.len > 0 and raw_str[0] == 'r') {
                                break :blk_fallback try self.allocator.dupe(
                                    u8,
                                    type_system.extractRawStringContent(raw_str) orelse "",
                                );
                            }
                            break :blk_fallback try type_system.decodeStandardStringSegment(
                                self.allocator,
                                extractQuotedBody(raw_str),
                            );
                        };
                        defer self.allocator.free(unescaped);
                        const str_id = try self.interner.intern(unescaped);
                        return self.store.appendPat(.{
                            .type_id = .str_ty,
                            .origin_token = tok,
                            .kind = .{ .lit_str = str_id },
                        });
                    },
                    .byte_string_lit => {
                        const raw_str = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                        const cooked = lexer.cookStringLiteral(self.allocator, raw_str) catch
                            try self.allocator.dupe(u8, "");
                        defer self.allocator.free(cooked);
                        const bytes_id = try self.interner.intern(cooked);
                        return self.store.appendPat(.{
                            .type_id = concrete_scrut,
                            .origin_token = tok,
                            .kind = .{ .lit_str = bytes_id },
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
                    const sub_id = NodeIndex.fromInt(raw_sub);
                    if (i >= field_names.items.len and
                        !sub_id.isNone() and
                        sub_id.asInt() < self.ast_arena.countNodes() and
                        self.ast_arena.getNode(sub_id).tag == .wildcard_pat)
                    {
                        continue;
                    }
                    var f_ord: u32 = @intCast(i);
                    var f_ty: TypeId = .unit_ty;
                    if (i < field_names.items.len and !field_names.items[i].isNone()) {
                        const f_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, field_names.items[i]);
                        if (self.findStructFieldInfo(unwrapped, f_lex)) |f_info| {
                            f_ord = f_info.ordinal;
                            f_ty = f_info.field_ty;
                        }
                    }
                    const sub_pat_idx = try self.lowerPattern(sub_id, f_ty, is_decl_mut);
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
                if (sub_nodes.len == 0) {
                    if (try self.tryEvalConstPatternValue(pat_id, concrete_scrut)) |const_val| {
                        return self.emitConstPatternVal(const_val, concrete_scrut, tok);
                    }
                }
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
                            const enum_subst = type_system.NominalTypeSubst.init(self.pool, self.sym_table, unwrapped);
                            var ord: u32 = 0;
                            for (self.sym_table.getScopeMembers(enum_sym.target_scope)) |m_idx| {
                                if (!self.isSymbolCfgEnabled(m_idx)) continue;
                                const m_sym = self.sym_table.getSymbol(m_idx).*;
                                if (m_sym.kind != .enum_variant_sym) continue;
                                if (std.mem.eql(u8, m_sym.name_text, var_name)) {
                                    tag_ordinal = ord;
                                    payload_ty = try enum_subst.applyMut(self.allocator, self.pool, m_sym.type_id);
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
            .at_pat => {
                const pat_cst = self.ast_arena.getCstOrigin(pat_id);
                var is_ref = self.hasKeywordInCst(pat_cst, .amp);
                var has_pat_mut = self.hasKeywordInCst(pat_cst, .kw_mut) or self.hasKeywordInCst(pat_cst, .kw_var);
                if (pat_node.lhs.tag == .token) {
                    const mod_tok = TokenIndex.fromInt(pat_node.lhs.payload);
                    if (!mod_tok.isNone() and mod_tok.asInt() < self.tokens.countTokens()) {
                        const mod_kind = self.tokens.getToken(mod_tok).kind;
                        if (mod_kind == .amp) is_ref = true;
                        if (mod_kind == .kw_mut or mod_kind == .kw_var) has_pat_mut = true;
                    }
                }
                const is_ref_mut = is_ref and has_pat_mut;
                const is_local_mut = is_decl_mut or (!is_ref and has_pat_mut);
                const bind_ty = if (is_ref) try self.pool.internRef(concrete_scrut, is_ref_mut) else concrete_scrut;
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);

                const sub_pat_idx = if (pat_node.rhs.tag == .node)
                    try self.lowerPattern(NodeIndex.fromInt(pat_node.rhs.payload), concrete_scrut, is_decl_mut)
                else
                    try self.store.appendPat(.{ .type_id = concrete_scrut, .origin_token = tok, .kind = .wildcard });

                if (lexeme.len == 0 or std.mem.eql(u8, lexeme, "_")) {
                    return sub_pat_idx;
                }
                const existing_local = blk: {
                    if (self.interner.lookup(lexeme)) |existing_id| {
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
                    .kind = .{
                        .at_pat = .{
                            .local_id = slot_id,
                            .is_mut = is_ref_mut or is_local_mut,
                            .is_ref = is_ref,
                            .sub_pat = sub_pat_idx,
                        },
                    },
                });
            },
            .slice_pat => {
                const sub_nodes = self.getAstExtraSlice(pat_id, false);
                const unwrapped = self.unwrapRefType(concrete_scrut);
                const scr_node = self.pool.getNode(unwrapped);
                const elem_ty: TypeId = if (scr_node.tag == .slice_ty or scr_node.tag == .array_ty or
                    scr_node.tag == .soa_slice_ty or scr_node.tag == .soa_array_ty)
                    self.concreteType(TypeId.fromInt(scr_node.lhs))
                else
                    .unit_ty;
                const is_scr_mut = self.pool.getTag(concrete_scrut) == .mut_ref_ty or is_decl_mut;

                var prefix_pats: std.ArrayListUnmanaged(u32) = .empty;
                defer prefix_pats.deinit(self.allocator);
                var suffix_pats: std.ArrayListUnmanaged(u32) = .empty;
                defer suffix_pats.deinit(self.allocator);

                var has_rest = false;
                var rest_local_id: u32 = NONE_U32;
                var is_rest_mut = false;
                var is_rest_ref = false;

                for (sub_nodes) |raw_sub| {
                    const sub_id = NodeIndex.fromInt(raw_sub);
                    if (self.isSliceRestPatternAst(sub_id)) {
                        if (!has_rest) {
                            has_rest = true;
                            const sub_node = self.ast_arena.getNode(sub_id);
                            if (sub_node.tag == .bind_pat) {
                                const rest_lex = symbol_resolver.extractTokenSlice(
                                    self.source,
                                    self.tokens,
                                    sub_node.main_token,
                                );
                                if (rest_lex.len > 0 and !std.mem.eql(u8, rest_lex, "_")) {
                                    const rest_cst = self.ast_arena.getCstOrigin(sub_id);
                                    is_rest_ref = self.hasKeywordInCst(rest_cst, .amp);
                                    const has_rest_mut = self.hasKeywordInCst(rest_cst, .kw_mut) or
                                        self.hasKeywordInCst(rest_cst, .kw_var);
                                    is_rest_mut = is_decl_mut or has_rest_mut;
                                    const subslice_ty = try self.pool.internRef(
                                        try self.pool.internSlice(elem_ty, false),
                                        is_scr_mut and has_rest_mut,
                                    );
                                    const existing_rest = blk_rest: {
                                        if (self.interner.lookup(rest_lex)) |existing_id| {
                                            const floor = @min(
                                                self.current_pat_shadow_floor,
                                                self.local_shadow_log.items.len,
                                            );
                                            for (self.local_shadow_log.items[floor..]) |shadow_item| {
                                                if (shadow_item.name_id == existing_id.asInt()) {
                                                    if (self.active_name_to_local.get(existing_id.asInt())) |cur_slot| {
                                                        if (self.store.locals.items[cur_slot].type_id == subslice_ty) {
                                                            break :blk_rest @as(?u32, cur_slot);
                                                        }
                                                    }
                                                    break;
                                                }
                                            }
                                        }
                                        break :blk_rest null;
                                    };
                                    rest_local_id = existing_rest orelse
                                        try self.bindSimplePatternLocal(
                                            sub_id,
                                            subslice_ty,
                                            !is_rest_ref and is_rest_mut,
                                        );
                                }
                            }
                        }
                        continue;
                    }
                    const elem_pat_idx = try self.lowerPattern(sub_id, elem_ty, is_decl_mut);
                    if (!has_rest) {
                        try prefix_pats.append(self.allocator, elem_pat_idx);
                    } else {
                        try suffix_pats.append(self.allocator, elem_pat_idx);
                    }
                }

                var combined_subs: std.ArrayListUnmanaged(u32) = .empty;
                defer combined_subs.deinit(self.allocator);
                try combined_subs.appendSlice(self.allocator, prefix_pats.items);
                try combined_subs.appendSlice(self.allocator, suffix_pats.items);
                const prefix_start = if (combined_subs.items.len > 0)
                    try self.store.appendExtraSlice(combined_subs.items)
                else
                    0;

                return self.store.appendPat(.{
                    .type_id = concrete_scrut,
                    .origin_token = tok,
                    .kind = .{
                        .slice_pat = .{
                            .prefix_start = prefix_start,
                            .prefix_len = @intCast(prefix_pats.items.len),
                            .suffix_len = @intCast(suffix_pats.items.len),
                            .has_rest = has_rest,
                            .rest_local_id = rest_local_id,
                            .is_rest_mut = is_rest_mut,
                            .is_rest_ref = is_rest_ref,
                        },
                    },
                });
            },
            else => {
                if (try self.tryEvalConstPatternValue(pat_id, concrete_scrut)) |const_val| {
                    return self.emitConstPatternVal(const_val, concrete_scrut, tok);
                }
                return self.store.appendPat(.{ .type_id = concrete_scrut, .origin_token = tok, .kind = .wildcard });
            },
        }
    }

    /// Evaluates a constant pattern (`if n is MAX_RETRIES` or `if n is u8.MAX`) when `pat_id` denotes a `const`.
    fn tryEvalConstPatternValue(
        self: *HirLowerer,
        pat_id: NodeIndex,
        concrete_scrut: TypeId,
    ) anyerror!?ComptimeValue {
        const pat_sym = self.nodeSymbol(pat_id);
        if (!pat_sym.isNone()) {
            const sym = self.sym_table.getSymbol(pat_sym).*;
            if (sym.kind == .const_sym) {
                if (sym.name != .empty) {
                    if (self.active_comptime_vals.get(sym.name.asInt())) |ct_val| return ct_val;
                }
                return self.evalConstSymbol(pat_sym);
            }
            return null;
        }

        const pat_node = self.ast_arena.getNode(pat_id);
        switch (pat_node.tag) {
            .variant_pat => {
                if (self.getAstExtraSlice(pat_id, false).len > 0) return null;
                const unwrapped = self.pool.unwrapUnderlyingType(self.unwrapRefType(concrete_scrut));
                const scr_tag = self.pool.getTag(unwrapped);
                if (scr_tag == .optional_ty or scr_tag == .result_ty or scr_tag == .enum_ty) return null;
                return self.tryEvalVariantPatPathConst(pat_id);
            },
            .bind_pat => {
                if (self.side_tables != null or pat_node.main_token.isNone()) return null;
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, pat_node.main_token);
                const name_id = self.interner.lookup(lexeme) orelse return null;
                switch (self.sym_table.lookupLexical(self.current_scope, name_id, NamespaceMask.VALUE_ONLY)) {
                    .found => |sym_idx| {
                        if (self.sym_table.getSymbol(sym_idx).kind == .const_sym) {
                            if (self.active_comptime_vals.get(name_id.asInt())) |ct_val| return ct_val;
                            return self.evalConstSymbol(sym_idx);
                        }
                    },
                    else => {},
                }
                return null;
            },
            .ident_expr, .path_expr, .field_access => return self.tryEvalAstComptime(pat_id, concrete_scrut),
            else => return null,
        }
    }

    /// Resolves a zero-argument `.variant_pat` CST path (`MAX_RETRIES`, `Mod.MAX`, or `u8.MAX`) to a `ComptimeValue`.
    fn tryEvalVariantPatPathConst(self: *HirLowerer, pat_id: NodeIndex) anyerror!?ComptimeValue {
        const pat_cst = self.ast_arena.getCstOrigin(pat_id);
        var ident_toks: [8]TokenIndex = undefined;
        var ident_len: usize = 0;
        if (!pat_cst.isNone() and pat_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = pat_cst.asInt();
            const rec = self.cst_arena.getNode(pat_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var cur = start_idx + 1;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.subtree_size <= 1 and !sub.token.isNone() and sub.token.asInt() < self.tokens.countTokens()) {
                    const tk = self.tokens.getToken(sub.token).kind;
                    if (tk == .lparen or tk == .lbrace) break;
                    if (symbol_resolver.isIdentifierToken(tk) and ident_len < ident_toks.len) {
                        ident_toks[ident_len] = sub.token;
                        ident_len += 1;
                    }
                }
            }
        }
        if (ident_len == 0 and !self.ast_arena.getNode(pat_id).main_token.isNone()) {
            ident_toks[0] = self.ast_arena.getNode(pat_id).main_token;
            ident_len = 1;
        }
        if (ident_len == 1) {
            const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, ident_toks[0]);
            if (self.interner.lookup(lexeme)) |name_id| {
                if (self.active_comptime_vals.get(name_id.asInt())) |ct_val| return ct_val;
                switch (self.sym_table.lookupLexical(self.current_scope, name_id, NamespaceMask.VALUE_ONLY)) {
                    .found => |sym_idx| {
                        if (self.sym_table.getSymbol(sym_idx).kind == .const_sym) {
                            return self.evalConstSymbol(sym_idx);
                        }
                    },
                    else => {},
                }
            }
            return null;
        }
        if (ident_len == 2) {
            const base_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, ident_toks[0]);
            const mem_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, ident_toks[1]);
            if (self.resolveBuiltinPrimitiveLexeme(base_lex)) |prim_ty| {
                if (self.evalPrimitiveAssocConst(prim_ty, mem_lex)) |assoc| return assoc.val;
            }
            const base_id = self.interner.lookup(base_lex) orelse return null;
            const mem_id = self.interner.lookup(mem_lex) orelse return null;
            switch (self.sym_table.lookupLexical(self.current_scope, base_id, NamespaceMask.ALL)) {
                .found => |base_sym_idx| {
                    const target_scope = self.sym_table.getSymbol(base_sym_idx).target_scope;
                    if (!target_scope.isNone()) {
                        const found_mem = self.sym_table.lookupInScopeDirect(
                            target_scope,
                            mem_id,
                            NamespaceMask.VALUE_ONLY,
                        );
                        if (!found_mem.isNone() and self.sym_table.getSymbol(found_mem).kind == .const_sym) {
                            return self.evalConstSymbol(found_mem);
                        }
                    }
                },
                else => {},
            }
        }
        return null;
    }

    /// Emits a literal `HirPattern` matching `const_val` against `concrete_scrut`.
    fn emitConstPatternVal(
        self: *HirLowerer,
        const_val: ComptimeValue,
        concrete_scrut: TypeId,
        tok: TokenIndex,
    ) !u32 {
        return switch (const_val) {
            .int_val => |iv| self.store.appendPat(.{
                .type_id = concrete_scrut,
                .origin_token = tok,
                .kind = .{ .lit_int_range = .{ .min_val = iv, .max_val = iv } },
            }),
            .char_val => |cv| self.store.appendPat(.{
                .type_id = concrete_scrut,
                .origin_token = tok,
                .kind = .{ .lit_int_range = .{ .min_val = @as(i128, cv), .max_val = @as(i128, cv) } },
            }),
            .bool_val => |bv| self.store.appendPat(.{
                .type_id = .bool_ty,
                .origin_token = tok,
                .kind = .{ .lit_bool = bv },
            }),
            .str_val => |sv| self.store.appendPat(.{
                .type_id = .str_ty,
                .origin_token = tok,
                .kind = .{ .lit_str = sv },
            }),
            .float_val => |fv| self.store.appendPat(.{
                .type_id = concrete_scrut,
                .origin_token = tok,
                .kind = .{ .lit_float = fv },
            }),
            else => self.store.appendPat(.{ .type_id = concrete_scrut, .origin_token = tok, .kind = .wildcard }),
        };
    }

    /// Compares `scrut_val` against an evaluated constant pattern `const_val` during `comptime` pattern matching.
    fn isMatchingConstPatternVal(
        self: *const HirLowerer,
        scrut_val: ComptimeValue,
        const_val: ComptimeValue,
    ) bool {
        return switch (const_val) {
            .int_val => |iv| (scrut_val == .int_val and scrut_val.int_val == iv) or
                (scrut_val == .char_val and @as(i128, scrut_val.char_val) == iv),
            .char_val => |cv| (scrut_val == .char_val and scrut_val.char_val == cv) or
                (scrut_val == .int_val and scrut_val.int_val == @as(i128, cv)),
            .bool_val => |bv| scrut_val == .bool_val and scrut_val.bool_val == bv,
            .str_val => |sv| scrut_val == .str_val and
                std.mem.eql(u8, self.interner.get(scrut_val.str_val), self.interner.get(sv)),
            .float_val => |fv| scrut_val == .float_val and scrut_val.float_val == fv,
            else => false,
        };
    }

    /// Returns `true` if `sub_pat_id` inside a `.slice_pat` is a `..` or `..rest` spread element.
    fn isSliceRestPatternAst(self: *const HirLowerer, sub_pat_id: NodeIndex) bool {
        if (sub_pat_id.isNone() or sub_pat_id.asInt() >= self.ast_arena.countNodes()) return false;
        const sub_pat = self.ast_arena.getNode(sub_pat_id);
        if (sub_pat.tag == .wildcard_pat and !sub_pat.main_token.isNone() and
            sub_pat.main_token.asInt() < self.tokens.countTokens())
        {
            return self.tokens.getToken(sub_pat.main_token).kind == .dotdot;
        }
        if ((sub_pat.tag == .bind_pat or sub_pat.tag == .wildcard_pat) and sub_pat.lhs.tag == .token) {
            const dotdot_tok = TokenIndex.fromInt(sub_pat.lhs.payload);
            if (!dotdot_tok.isNone() and dotdot_tok.asInt() < self.tokens.countTokens()) {
                return self.tokens.getToken(dotdot_tok).kind == .dotdot;
            }
        }
        return false;
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
        if (tok_rec.kind == .byte_lit) return @as(i128, lexer.extractByteLiteralValue(lexeme) orelse 0);
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

    /// Extracts field name tokens from `.field_pat` CST children inside a `.struct_pat`.
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
                const pat_cst = self.ast_arena.getCstOrigin(pat_id);
                const is_ref = self.hasKeywordInCst(pat_cst, .amp);
                const has_pat_mut = self.hasKeywordInCst(pat_cst, .kw_mut) or self.hasKeywordInCst(pat_cst, .kw_var);
                if (!is_ref and !has_pat_mut) {
                    if (try self.tryEvalConstPatternValue(pat_id, scrut_ty)) |const_val| {
                        return self.isMatchingConstPatternVal(scrut_val, const_val);
                    }
                }
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
                if (tk == .string_lit or tk == .byte_string_lit) {
                    if (scrut_val != .str_val and scrut_val != .bytes_val) return false;
                    const scrut_str_id = if (scrut_val == .str_val) scrut_val.str_val else scrut_val.bytes_val;
                    const raw_str = symbol_resolver.extractTokenSlice(
                        self.source,
                        self.tokens,
                        pat_node.main_token,
                    );
                    const unescaped = lexer.cookStringLiteral(self.allocator, raw_str) catch blk_fallback: {
                        if (raw_str.len > 0 and raw_str[0] == 'r') {
                            break :blk_fallback try self.allocator.dupe(
                                u8,
                                type_system.extractRawStringContent(raw_str) orelse "",
                            );
                        }
                        break :blk_fallback try type_system.decodeStandardStringSegment(
                            self.allocator,
                            extractQuotedBody(raw_str),
                        );
                    };
                    defer self.allocator.free(unescaped);
                    return std.mem.eql(u8, self.interner.get(scrut_str_id), unescaped);
                }
                const expected_int = self.evalLitPatScalar(pat_id);
                return switch (scrut_val) {
                    .int_val => |iv| iv == expected_int,
                    .char_val => |cv| @as(i128, cv) == expected_int,
                    else => false,
                };
            },
            .struct_pat => {
                if (scrut_val != .aggregate) return false;
                const sub_nodes = self.getAstExtraSlice(pat_id, false);
                var field_names: std.ArrayListUnmanaged(TokenIndex) = .empty;
                defer field_names.deinit(self.allocator);
                try self.extractStructPatFieldTokens(pat_id, &field_names);
                const unwrapped = self.unwrapRefType(scrut_ty);
                const checkpoint = self.comptime_shadow_log.items.len;
                for (sub_nodes, 0..) |raw_sub, i| {
                    const sub_id = NodeIndex.fromInt(raw_sub);
                    if (i >= field_names.items.len and
                        !sub_id.isNone() and
                        sub_id.asInt() < self.ast_arena.countNodes() and
                        self.ast_arena.getNode(sub_id).tag == .wildcard_pat)
                    {
                        continue;
                    }
                    var f_ord: u32 = @intCast(i);
                    var f_ty: TypeId = .err_ty;
                    if (i < field_names.items.len and !field_names.items[i].isNone()) {
                        const f_lex = symbol_resolver.extractTokenSlice(
                            self.source,
                            self.tokens,
                            field_names.items[i],
                        );
                        if (self.findStructFieldInfo(unwrapped, f_lex)) |f_info| {
                            f_ord = f_info.ordinal;
                            f_ty = f_info.field_ty;
                        }
                    }
                    if (f_ord >= scrut_val.aggregate.elem_len) {
                        self.popComptimeBindingsTo(checkpoint);
                        return false;
                    }
                    const elem_const_idx = self.store.const_elements.items[scrut_val.aggregate.elem_start + f_ord];
                    const elem_val = self.store.const_pool.items[elem_const_idx];
                    if (!try self.matchComptimePattern(sub_id, elem_val, f_ty)) {
                        self.popComptimeBindingsTo(checkpoint);
                        return false;
                    }
                }
                return true;
            },
            .variant_pat => {
                if (self.getAstExtraSlice(pat_id, false).len == 0) {
                    if (try self.tryEvalConstPatternValue(pat_id, scrut_ty)) |const_val| {
                        return self.isMatchingConstPatternVal(scrut_val, const_val);
                    }
                }
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
                                if (!self.isSymbolCfgEnabled(m_idx)) continue;
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
            .at_pat => {
                const checkpoint = self.comptime_shadow_log.items.len;
                if (pat_node.rhs.tag == .node) {
                    if (!try self.matchComptimePattern(
                        NodeIndex.fromInt(pat_node.rhs.payload),
                        scrut_val,
                        scrut_ty,
                    )) {
                        self.popComptimeBindingsTo(checkpoint);
                        return false;
                    }
                }
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, pat_node.main_token);
                if (lexeme.len > 0 and !std.mem.eql(u8, lexeme, "_")) {
                    try self.pushComptimeBinding(try self.interner.intern(lexeme), scrut_val);
                }
                return true;
            },
            .slice_pat => {
                if (scrut_val != .aggregate) return false;
                const sub_nodes = self.getAstExtraSlice(pat_id, false);
                var prefix_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
                defer prefix_nodes.deinit(self.allocator);
                var suffix_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
                defer suffix_nodes.deinit(self.allocator);
                var has_rest = false;
                var rest_sub_id: NodeIndex = .none;

                for (sub_nodes) |raw_sub| {
                    const sub_id = NodeIndex.fromInt(raw_sub);
                    if (self.isSliceRestPatternAst(sub_id)) {
                        if (!has_rest) {
                            has_rest = true;
                            rest_sub_id = sub_id;
                        }
                        continue;
                    }
                    if (!has_rest) {
                        try prefix_nodes.append(self.allocator, sub_id);
                    } else {
                        try suffix_nodes.append(self.allocator, sub_id);
                    }
                }

                const agg_len: usize = scrut_val.aggregate.elem_len;
                const fixed_len = prefix_nodes.items.len + suffix_nodes.items.len;
                if ((!has_rest and agg_len != fixed_len) or (has_rest and agg_len < fixed_len)) return false;

                const unwrapped = self.unwrapRefType(scrut_ty);
                const scr_node = self.pool.getNode(unwrapped);
                const elem_ty: TypeId = if (scr_node.tag == .slice_ty or scr_node.tag == .array_ty or
                    scr_node.tag == .soa_slice_ty or scr_node.tag == .soa_array_ty)
                    TypeId.fromInt(scr_node.lhs)
                else
                    .err_ty;

                const checkpoint = self.comptime_shadow_log.items.len;
                for (prefix_nodes.items, 0..) |sub_id, i| {
                    const elem_const_idx = self.store.const_elements.items[scrut_val.aggregate.elem_start + i];
                    const elem_val = self.store.const_pool.items[elem_const_idx];
                    if (!try self.matchComptimePattern(sub_id, elem_val, elem_ty)) {
                        self.popComptimeBindingsTo(checkpoint);
                        return false;
                    }
                }
                if (has_rest and !rest_sub_id.isNone()) {
                    const rest_node = self.ast_arena.getNode(rest_sub_id);
                    if (rest_node.tag == .bind_pat) {
                        const rest_lex = symbol_resolver.extractTokenSlice(
                            self.source,
                            self.tokens,
                            rest_node.main_token,
                        );
                        if (rest_lex.len > 0 and !std.mem.eql(u8, rest_lex, "_")) {
                            const subslice_ty = if (elem_ty.isError())
                                scrut_val.aggregate.type_id
                            else
                                try self.pool.internRef(try self.pool.internSlice(elem_ty, false), false);
                            try self.pushComptimeBinding(try self.interner.intern(rest_lex), .{
                                .aggregate = .{
                                    .type_id = subslice_ty,
                                    .elem_start = scrut_val.aggregate.elem_start +
                                        @as(u32, @intCast(prefix_nodes.items.len)),
                                    .elem_len = @intCast(agg_len - fixed_len),
                                },
                            });
                        }
                    }
                }
                const suffix_base = agg_len - suffix_nodes.items.len;
                for (suffix_nodes.items, 0..) |sub_id, i| {
                    const elem_const_idx = self.store.const_elements.items[
                        scrut_val.aggregate.elem_start + @as(u32, @intCast(suffix_base + i))
                    ];
                    const elem_val = self.store.const_pool.items[elem_const_idx];
                    if (!try self.matchComptimePattern(sub_id, elem_val, elem_ty)) {
                        self.popComptimeBindingsTo(checkpoint);
                        return false;
                    }
                }
                return true;
            },
            else => {
                if (try self.tryEvalConstPatternValue(pat_id, scrut_ty)) |const_val| {
                    return self.isMatchingConstPatternVal(scrut_val, const_val);
                }
                return false;
            },
        }
    }

    /// Evaluates a `const_sym` declaration at compile time with `const_eval_stack` cycle detection (`E0509`).
    fn evalConstSymbol(self: *HirLowerer, sym_idx: SymbolIndex) anyerror!?ComptimeValue {
        if (sym_idx.isNone() or sym_idx.asInt() >= self.sym_table.symbols.items.len) return null;
        var active_sym_idx = sym_idx;
        const raw_sym = self.sym_table.getSymbol(sym_idx).*;
        if (!raw_sym.def_id.isNone()) {
            if (self.sym_table.def_to_symbol.get(raw_sym.def_id.asInt())) |latest_idx| {
                if (!latest_idx.isNone()) active_sym_idx = latest_idx;
            }
        }
        const sym = self.sym_table.getSymbol(active_sym_idx).*;
        if (sym.kind != .const_sym) return null;

        for (self.const_eval_stack[0..self.const_eval_depth]) |active_sym| {
            if (active_sym == active_sym_idx) {
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

        self.const_eval_stack[self.const_eval_depth] = active_sym_idx;
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
            .byte_lit => {
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                return .{ .int_val = lexer.extractByteLiteralValue(lexeme) orelse return null };
            },
            .byte_string_lit => {
                const lexeme = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                const cooked = lexer.cookStringLiteral(self.allocator, lexeme) catch return null;
                defer self.allocator.free(cooked);
                return .{ .bytes_val = try self.interner.intern(cooked) };
            },
            .string_lit => {
                const raw_lex = symbol_resolver.extractTokenSlice(self.source, self.tokens, tok);
                if (raw_lex.len > 0 and raw_lex[0] == 'r') {
                    const cooked_raw = lexer.cookStringLiteral(self.allocator, raw_lex) catch return null;
                    defer self.allocator.free(cooked_raw);
                    return .{ .str_val = try self.interner.intern(cooked_raw) };
                }
                const body = extractQuotedBody(raw_lex);
                if (type_system.scanNextInterpolationSegment(body, 0) != null) return null;
                const cooked = lexer.cookStringLiteral(self.allocator, raw_lex) catch
                    try type_system.decodeStandardStringSegment(self.allocator, body);
                defer self.allocator.free(cooked);
                return .{ .str_val = try self.interner.intern(cooked) };
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
            .named_arg => {
                if (ast_node.lhs.tag == .node) {
                    return self.tryEvalAstComptime(NodeIndex.fromInt(ast_node.lhs.payload), expected_ty);
                }
                return null;
            },
            .is_expr => {
                if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .node) return null;
                const scrut_id = NodeIndex.fromInt(ast_node.lhs.payload);
                const scrut_val = (try self.tryEvalAstComptime(scrut_id, .err_ty)) orelse return null;
                const scrut_ty = self.nodeType(scrut_id);
                const is_negated = !tok.isNone() and tok.asInt() < self.tokens.countTokens() and
                    self.tokens.getToken(tok).kind == .kw_not;
                const checkpoint = self.comptime_shadow_log.items.len;
                const is_matched = try self.matchComptimePattern(
                    NodeIndex.fromInt(ast_node.rhs.payload),
                    scrut_val,
                    scrut_ty,
                );
                if (is_negated or !is_matched) {
                    self.popComptimeBindingsTo(checkpoint);
                }
                return .{ .bool_val = if (is_negated) !is_matched else is_matched };
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
                                self.unwrapCallArgAst(NodeIndex.fromInt(args[0])),
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
                                self.unwrapCallArgAst(NodeIndex.fromInt(args[0])),
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
                                if (!self.isSymbolCfgEnabled(mem_idx)) continue;
                                const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                                if (mem_sym.kind != .enum_variant_sym) continue;
                                if (std.mem.eql(u8, mem_sym.name_text, var_name)) {
                                    if (args.len > 1) return null;
                                    const payload_idx = if (args.len == 0 or mem_sym.type_id == .unit_ty)
                                        NONE_U32
                                    else blk: {
                                        const inner = (try self.tryEvalAstComptime(
                                            self.unwrapCallArgAst(NodeIndex.fromInt(args[0])),
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
                    .tilde => switch (sub_val) {
                        .int_val => |iv| .{ .int_val = ~iv },
                        else => null,
                    },
                    .bang => switch (sub_val) {
                        .bool_val => |bv| .{ .bool_val = !bv },
                        else => null,
                    },
                    else => null,
                };
            },
            .binary_expr => {
                if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .node) return null;
                const op_kind = self.tokens.getToken(tok).kind;
                const lhs_id = NodeIndex.fromInt(ast_node.lhs.payload);
                const lhs_val = (try self.tryEvalAstComptime(lhs_id, .err_ty)) orelse return null;
                if (op_kind == .kw_and and lhs_val == .bool_val) {
                    if (!lhs_val.bool_val) return .{ .bool_val = false };
                    return self.tryEvalAstComptime(NodeIndex.fromInt(ast_node.rhs.payload), .bool_ty);
                }
                if (op_kind == .kw_or and lhs_val == .bool_val) {
                    if (lhs_val.bool_val) return .{ .bool_val = true };
                    return self.tryEvalAstComptime(NodeIndex.fromInt(ast_node.rhs.payload), .bool_ty);
                }
                if (op_kind == .kw_orelse and lhs_val == .variant) {
                    if (lhs_val.variant.tag_ordinal == 1 and
                        lhs_val.variant.payload_const_idx < self.store.const_pool.items.len)
                    {
                        return self.store.const_pool.items[lhs_val.variant.payload_const_idx];
                    }
                    return self.tryEvalAstComptime(NodeIndex.fromInt(ast_node.rhs.payload), expected_ty);
                }
                if (op_kind == .kw_is) {
                    const checkpoint = self.comptime_shadow_log.items.len;
                    const is_matched = try self.matchComptimePattern(
                        NodeIndex.fromInt(ast_node.rhs.payload),
                        lhs_val,
                        self.nodeType(lhs_id),
                    );
                    if (!is_matched) self.popComptimeBindingsTo(checkpoint);
                    return .{ .bool_val = is_matched };
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
                const lhs_id = NodeIndex.fromInt(ast_node.lhs.payload);
                const member_name = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.tokens,
                    TokenIndex.fromInt(ast_node.rhs.payload),
                );
                // [1] Primitive associated constants (`u32.MAX`, `f64.INFINITY`, etc.):
                if (self.resolveBuiltinPrimitiveAst(lhs_id)) |recv_prim| {
                    if (self.evalPrimitiveAssocConst(recv_prim, member_name)) |prim_const| {
                        return prim_const.val;
                    }
                }
                // [2] Unified `.` static constants, unit enum variants, and `Option.None`:
                var static_sym_idx = self.nodeSymbol(expr_id);
                if (static_sym_idx.isNone()) {
                    static_sym_idx = self.lookupStaticMemberSymbolFallback(lhs_id, member_name);
                }
                if (!static_sym_idx.isNone()) {
                    const static_sym = self.sym_table.getSymbol(static_sym_idx).*;
                    if (static_sym.kind == .const_sym) return self.evalConstSymbol(static_sym_idx);
                    if (static_sym.kind == .enum_variant_sym and static_sym.type_id == .unit_ty) {
                        const enum_ty = if (!expected_ty.isError()) expected_ty else self.nodeType(expr_id);
                        return .{
                            .variant = .{
                                .type_id = self.concreteType(enum_ty),
                                .tag_ordinal = static_sym.member_ordinal,
                                .payload_const_idx = NONE_U32,
                            },
                        };
                    }
                }
                if (std.mem.eql(u8, member_name, "None") and self.resolveStaticDotTargetAst(lhs_id) == .type_ns) {
                    const opt_ty = self.concreteType(if (!expected_ty.isError())
                        expected_ty
                    else
                        self.nodeType(expr_id));
                    const unwrapped_opt = self.pool.unwrapUnderlyingType(opt_ty);
                    if (!unwrapped_opt.isError() and self.pool.getTag(unwrapped_opt) == .optional_ty) {
                        return .{
                            .variant = .{ .type_id = opt_ty, .tag_ordinal = 0, .payload_const_idx = NONE_U32 },
                        };
                    }
                }

                const base_val = (try self.tryEvalAstComptime(lhs_id, .err_ty)) orelse return null;
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
                        if (agg.type_id == .source_loc_ty and agg.elem_len == 4) {
                            const loc_ord: ?u32 = if (std.mem.eql(u8, member_name, "file"))
                                0
                            else if (std.mem.eql(u8, member_name, "fn_name"))
                                1
                            else if (std.mem.eql(u8, member_name, "line"))
                                2
                            else if (std.mem.eql(u8, member_name, "col"))
                                3
                            else
                                null;
                            if (loc_ord) |ord| {
                                const c_idx = self.store.const_elements.items[agg.elem_start + ord];
                                return self.store.const_pool.items[c_idx];
                            }
                        }
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
                const recv_id = NodeIndex.fromInt(ast_node.lhs.payload);
                const raw_items = self.getAstExtraSlice(expr_id, true);
                if (raw_items.len == 0) return null;
                const method_name = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.tokens,
                    TokenIndex.fromInt(raw_items[0]),
                );
                // Unified `.` static `Option.Some` / `Result.Ok` / `Result.Err` / `Enum.Variant(payload)` comptime fold:
                const static_kind = self.resolveStaticDotTargetAst(recv_id);
                if (static_kind != .none) {
                    var first_val_arg: NodeIndex = .none;
                    var val_arg_count: usize = 0;
                    for (raw_items[1..]) |raw_item| {
                        const cand_id = self.unwrapCallArgAst(NodeIndex.fromInt(raw_item));
                        if (cand_id.asInt() < self.ast_arena.countNodes() and
                            !isTypeAstTag(self.ast_arena.getNode(cand_id).tag))
                        {
                            if (first_val_arg.isNone()) first_val_arg = cand_id;
                            val_arg_count += 1;
                        }
                    }
                    const res_ty = self.concreteType(if (!expected_ty.isError())
                        expected_ty
                    else
                        self.nodeType(expr_id));
                    const ty_node = self.pool.getNode(self.pool.unwrapUnderlyingType(res_ty));
                    if (static_kind == .type_ns and ty_node.tag == .optional_ty) {
                        if (std.mem.eql(u8, method_name, "None")) {
                            return .{
                                .variant = .{ .type_id = res_ty, .tag_ordinal = 0, .payload_const_idx = NONE_U32 },
                            };
                        }
                        if (std.mem.eql(u8, method_name, "Some") and !first_val_arg.isNone()) {
                            const inner = (try self.tryEvalAstComptime(
                                first_val_arg,
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
                    } else if (static_kind == .type_ns and ty_node.tag == .result_ty and
                        (std.mem.eql(u8, method_name, "Ok") or std.mem.eql(u8, method_name, "Err")))
                    {
                        const is_ok = std.mem.eql(u8, method_name, "Ok");
                        const payload_ty = TypeId.fromInt(if (is_ok) ty_node.lhs else ty_node.rhs);
                        const payload_idx = if (!first_val_arg.isNone()) blk_res: {
                            const inner = (try self.tryEvalAstComptime(first_val_arg, payload_ty)) orelse return null;
                            break :blk_res try self.store.appendConst(inner);
                        } else NONE_U32;
                        return .{
                            .variant = .{
                                .type_id = res_ty,
                                .tag_ordinal = if (is_ok) 0 else 1,
                                .payload_const_idx = payload_idx,
                            },
                        };
                    }
                    var call_sym = self.nodeSymbol(expr_id);
                    if (call_sym.isNone()) call_sym = self.lookupStaticMemberSymbolFallback(recv_id, method_name);
                    if (!call_sym.isNone()) {
                        const var_sym = self.sym_table.getSymbol(call_sym).*;
                        if (var_sym.kind == .enum_variant_sym) {
                            if (val_arg_count > 1) return null;
                            const payload_idx = if (first_val_arg.isNone() or var_sym.type_id == .unit_ty)
                                NONE_U32
                            else blk_ev: {
                                const inner = (try self.tryEvalAstComptime(
                                    first_val_arg,
                                    var_sym.type_id,
                                )) orelse return null;
                                break :blk_ev try self.store.appendConst(inner);
                            };
                            return .{
                                .variant = .{
                                    .type_id = res_ty,
                                    .tag_ordinal = var_sym.member_ordinal,
                                    .payload_const_idx = payload_idx,
                                },
                            };
                        }
                    }
                }
                const recv_val = (try self.tryEvalAstComptime(recv_id, .err_ty)) orelse return null;
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
                        try val_arg_nodes.append(self.allocator, self.unwrapCallArgAst(item_id));
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
                            const sat = type_system.checkGroupSatisfaction(
                                self.pool,
                                self.sym_table,
                                self.store.target_layout,
                                t_arg_0,
                                bound_ty,
                            );
                            return .{ .bool_val = sat != .rejected and sat != .rejected_distinct_without_tilde };
                        }
                        const trait_node = self.pool.getNode(bound_ty);
                        if (trait_node.tag == .trait_ty) {
                            const trait_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(trait_node.rhs));
                            if (self.pool.getFlags(t_arg_0).is_secret and
                                (std.mem.eql(u8, trait_sym.name_text, "Debug") or
                                    std.mem.eql(u8, trait_sym.name_text, "Display")))
                            {
                                return .{ .bool_val = false };
                            }
                            if (trait_sym.flags.is_builtin) {
                                if (std.mem.eql(u8, trait_sym.name_text, "Copy")) {
                                    return .{
                                        .bool_val = type_system.classifyOwnershipTier(
                                            self.pool,
                                            self.sym_table,
                                            t_arg_0,
                                        ) == .copy_tier,
                                    };
                                }
                                if (std.mem.eql(u8, trait_sym.name_text, "AutoDrop")) {
                                    return .{
                                        .bool_val = type_system.classifyOwnershipTier(
                                            self.pool,
                                            self.sym_table,
                                            t_arg_0,
                                        ) == .auto_drop_tier,
                                    };
                                }
                            }
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
                    .caller_location => {
                        return try self.evalCallerLocationValue(intr_tok);
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
            if (!self.isSymbolCfgEnabled(mem_idx)) continue;
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

/// Parses a floating-point literal lexeme (`_`, `_f32`/`_f64` suffixes) into `f64` (`SE-13`).
fn extractFloatValue(raw_lexeme: []const u8) ?f64 {
    const trimmed = if (lexer.extractNumericSuffix(raw_lexeme)) |split|
        split.digits_slice
    else |_| blk_fb: {
        var fb = raw_lexeme;
        if (std.mem.endsWith(u8, fb, "_f32") or std.mem.endsWith(u8, fb, "_f64")) {
            fb = fb[0 .. fb.len - 4];
        } else if (std.mem.endsWith(u8, fb, "f32") or std.mem.endsWith(u8, fb, "f64")) {
            fb = fb[0 .. fb.len - 3];
        }
        break :blk_fb fb;
    };
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

/// Decodes an interpolated static piece, applying multiline `dedent_cols` and unescaping `{{`/`}}` + standard escapes.
fn decodeInterpolatedStaticPiece(
    allocator: std.mem.Allocator,
    raw_seg: []const u8,
    dedent_cols: usize,
    is_at_line_start: *bool,
) ![]u8 {
    var pre_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer pre_buf.deinit(allocator);
    var cursor: usize = 0;
    while (cursor < raw_seg.len) {
        if (is_at_line_start.* and dedent_cols > 0) {
            var stripped: usize = 0;
            while (stripped < dedent_cols and cursor < raw_seg.len and
                (raw_seg[cursor] == ' ' or raw_seg[cursor] == '\t'))
            {
                stripped += 1;
                cursor += 1;
            }
            is_at_line_start.* = false;
            if (cursor >= raw_seg.len) break;
        }
        if (raw_seg[cursor] == '\r' and cursor + 1 < raw_seg.len and raw_seg[cursor + 1] == '\n') {
            try pre_buf.append(allocator, '\n');
            cursor += 2;
            is_at_line_start.* = true;
            continue;
        }
        if (raw_seg[cursor] == '\n') {
            try pre_buf.append(allocator, '\n');
            cursor += 1;
            is_at_line_start.* = true;
            continue;
        }
        is_at_line_start.* = false;
        if (cursor + 1 < raw_seg.len and
            ((raw_seg[cursor] == '{' and raw_seg[cursor + 1] == '{') or
                (raw_seg[cursor] == '}' and raw_seg[cursor + 1] == '}')))
        {
            try pre_buf.append(allocator, raw_seg[cursor]);
            cursor += 2;
            continue;
        }
        try pre_buf.append(allocator, raw_seg[cursor]);
        cursor += 1;
    }
    return type_system.decodeStandardStringSegment(allocator, pre_buf.items);
}

/// Decodes a `'c'`, `'\n'`, `'\xHH'`, or `'\u{…}'` character literal lexeme into its Unicode scalar `u21`.
fn extractCharValue(raw_lexeme: []const u8) u21 {
    return type_system.extractCharLiteralCodepoint(raw_lexeme) orelse 0;
}

/// Strips enclosing `"…"`, `"""…"""`, `r"…"`, `r#"""…"""#`, or `'…'` delimiters from `raw_lexeme`.
fn extractQuotedBody(raw_lexeme: []const u8) []const u8 {
    if (raw_lexeme.len > 0 and raw_lexeme[0] == 'r') {
        var hash_count: usize = 0;
        while (1 + hash_count < raw_lexeme.len and raw_lexeme[1 + hash_count] == '#') : (hash_count += 1) {}
        if (1 + hash_count + 6 + hash_count <= raw_lexeme.len and
            std.mem.startsWith(u8, raw_lexeme[1 + hash_count ..], "\"\"\"") and
            std.mem.endsWith(u8, raw_lexeme[0 .. raw_lexeme.len - hash_count], "\"\"\""))
        {
            return raw_lexeme[1 + hash_count + 3 .. raw_lexeme.len - hash_count - 3];
        }
        if (type_system.extractRawStringContent(raw_lexeme)) |raw_body| return raw_body;
    }
    if (raw_lexeme.len >= 6 and std.mem.startsWith(u8, raw_lexeme, "\"\"\"") and
        std.mem.endsWith(u8, raw_lexeme, "\"\"\""))
    {
        return raw_lexeme[3 .. raw_lexeme.len - 3];
    }
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
        .fmt_args_ty => return out_buf.appendSlice(allocator, "FmtArgs"),
        .source_loc_ty => return out_buf.appendSlice(allocator, "SourceLoc"),
        .opaque_ty => return out_buf.appendSlice(allocator, "opaque"),
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
            try out_buf.appendSlice(allocator, if (pool.isOutRef(ty)) "&out " else "&mut ");
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
            try out_buf.append(allocator, ']');
            if (node.flags.is_dollar_sub) {
                try out_buf.appendSlice(allocator, " [dollar_sub]");
            }
            try out_buf.append(allocator, '\n');
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
        .hir_field_proj, .hir_bitfield_read, .hir_cast, .hir_return, .hir_yield, .hir_await => {
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
        .hir_index_proj, .hir_assign, .hir_orelse => {
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
        .hir_cond_if, .hir_cond_while => {
            if (node.tag == .hir_cond_while) {
                var loop_scratch: [24]u8 = undefined;
                try out_buf.appendSlice(
                    allocator,
                    std.fmt.bufPrint(&loop_scratch, " ^loop{d}\n", .{node.data.rhs}) catch "\n",
                );
            } else {
                try out_buf.append(allocator, '\n');
            }
            if (node.data.lhs < store.extra_data.items.len) {
                const clause_count = store.extra_data.items[node.data.lhs];
                var cursor: usize = node.data.lhs + 1;
                var clause_i: u32 = 0;
                while (clause_i < clause_count and cursor < store.extra_data.items.len) : (clause_i += 1) {
                    const clause_kind = store.extra_data.items[cursor];
                    if (clause_kind == @backingInt(HirCondClauseKind.bool_pred) and
                        cursor + 1 < store.extra_data.items.len)
                    {
                        try renderHirNodeRecursive(
                            allocator,
                            store,
                            pool,
                            sym_table,
                            interner,
                            HirIndex.fromInt(store.extra_data.items[cursor + 1]),
                            indent + 1,
                            out_buf,
                        );
                        cursor += 2;
                    } else if (clause_kind == @backingInt(HirCondClauseKind.is_match) and
                        cursor + 2 < store.extra_data.items.len)
                    {
                        try renderHirNodeRecursive(
                            allocator,
                            store,
                            pool,
                            sym_table,
                            interner,
                            HirIndex.fromInt(store.extra_data.items[cursor + 1]),
                            indent + 1,
                            out_buf,
                        );
                        cursor += 3;
                    } else {
                        break;
                    }
                }
                if (cursor < store.extra_data.items.len) {
                    try renderHirNodeRecursive(
                        allocator,
                        store,
                        pool,
                        sym_table,
                        interner,
                        HirIndex.fromInt(store.extra_data.items[cursor]),
                        indent + 1,
                        out_buf,
                    );
                }
                if (node.tag == .hir_cond_if and cursor + 1 < store.extra_data.items.len) {
                    try renderHirNodeRecursive(
                        allocator,
                        store,
                        pool,
                        sym_table,
                        interner,
                        HirIndex.fromInt(store.extra_data.items[cursor + 1]),
                        indent + 1,
                        out_buf,
                    );
                }
            }
        },
        .hir_ctx_get, .hir_ctx_region_pop => {
            var slot_scratch: [32]u8 = undefined;
            try out_buf.appendSlice(
                allocator,
                std.fmt.bufPrint(&slot_scratch, " [slot={d}]\n", .{node.data.lhs}) catch "\n",
            );
        },
        .hir_ctx_set, .hir_ctx_region_push => {
            var slot_scratch: [32]u8 = undefined;
            try out_buf.appendSlice(
                allocator,
                std.fmt.bufPrint(&slot_scratch, " [slot={d}]\n", .{node.data.lhs}) catch "\n",
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
        .hir_slice_range => {
            const is_incl = node.data.rhs + 3 <= store.extra_data.items.len and
                store.extra_data.items[node.data.rhs + 2] != 0;
            try out_buf.appendSlice(
                allocator,
                if (is_incl) " [inclusive=true]\n" else " [inclusive=false]\n",
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
            if (node.data.rhs + 3 <= store.extra_data.items.len) {
                var part_i: usize = 0;
                while (part_i < 2) : (part_i += 1) {
                    const bound_hir = HirIndex.fromInt(store.extra_data.items[node.data.rhs + part_i]);
                    if (!bound_hir.isNone()) {
                        try renderHirNodeRecursive(
                            allocator,
                            store,
                            pool,
                            sym_table,
                            interner,
                            bound_hir,
                            indent + 1,
                            out_buf,
                        );
                    }
                }
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
        .hir_unreachable => try out_buf.append(allocator, '\n'),
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
        \\pub fn helper_opt(maybe_num: i32?, fallible_res: i32!i32) -> i32? {
        \\    let unwrapped = maybe_num?;
        \\    let fallback_opt = maybe_num orelse 0;
        \\    let safe_val = fallible_res catch 0;
        \\    let .Some(bound) = maybe_num else { return .None; };
        \\    let is_present: bool = maybe_num is .Some(_);
        \\    if maybe_num is .Some(inner) and is_present {
        \\        return .Some(unwrapped + fallback_opt + safe_val + bound + inner);
        \\    }
        \\    return .None;
        \\}
    ;
    var err_bundle = try lowerSourceToHir(allocator, err_src, TargetLayout.NATIVE_64);
    defer err_bundle.deinit();
    try std.testing.expect(!err_bundle.diagnostics.hasErrors());
    try std.testing.expect(countHirNodesByTag(&err_bundle.hir_store, .hir_match) >= 4);
    try std.testing.expect(countHirNodesByTag(&err_bundle.hir_store, .hir_orelse) >= 1);
    try std.testing.expect(countHirNodesByTag(&err_bundle.hir_store, .hir_cond_if) >= 1);

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
        \\    var total: u32 = 0;
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
        \\    var acc: i32 = 0;
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
        \\pub fn update_reg(reg: &mut StatusReg) -> bool {
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
        \\@attribute_schema(targets: [.StructField])
        \\pub struct Column {
        \\    pub width: i32 = 8,
        \\}
        \\pub struct Row {
        \\    @Column(width: 32)
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
        \\    var total: usize = 0;
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
        \\    var count: i32 = 0;
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

    // [1] Conjunctive `is`, shadow isolation, `comptime for`, `@derive`, and operator `Eq` lowering:
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
        \\    var else_hits: i32 = 0;
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
        \\    var unrolled_sum: i32 = 0;
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

    // Verify `else_hits = else_hits + 1` was lowered only ONCE and `comptime for` left zero user `hir_loop`s:
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

    // [2] Runtime-guarded `break` targeting an outer `comptime for` emits `E0503`:
    const bad_ct_break_src =
        \\pub fn bad_runtime_break(runtime_cond: bool) -> i32 {
        \\    var acc: i32 = 0;
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

    // [3] Compound assign `rhs`-before-`&mut lhs`, post-arg index order, and `for` mutability:
    const eval_order_src =
        \\pub fn bump_and_get(counter: &mut usize) -> usize {
        \\    counter.* = counter.* + 1;
        \\    return counter.* - 1;
        \\}
        \\pub fn loop_and_assign(slice_mut: &mut [i32]) -> i32 {
        \\    var arr: [i32; 4] = [10, 20, 30, 40];
        \\    var cursor: usize = 0;
        \\    let picked: i32 = arr[bump_and_get(&mut cursor)];
        \\    var total: i32 = picked;
        \\    total += arr[0];
        \\    for &elem_ref in 0..3 {
        \\        total += elem_ref.*;
        \\    }
        \\    for &mut slot_ref in slice_mut {
        \\        slot_ref.* = slot_ref.* + 1;
        \\    }
        \\    return total;
        \\}
    ;
    var order_bundle = try lowerSourceToHir(allocator, eval_order_src, TargetLayout.NATIVE_64);
    defer order_bundle.deinit();
    try std.testing.expect(!order_bundle.diagnostics.hasErrors());

    // [4] `> 64` struct fields lowered into HIR without silent truncation:
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

test "test_phase76_stage4_hir_subscript_single_def_raw_multiline_caller_loc_and_parallel_lhs" {
    const allocator = std.testing.allocator;

    // [1] Verify `lowerDefToHir` populates referenced same-file `subscript` templates (`let` & `inout`):
    {
        const sub_src =
            \\pub struct Grid {
            \\    pub cells: [i32; 2],
            \\}
            \\impl Grid {
            \\    pub subscript(idx: usize) -> i32 {
            \\        let {
            \\            yield self.cells[idx];
            \\        }
            \\        inout {
            \\            yield &mut self.cells[idx];
            \\        }
            \\    }
            \\}
            \\pub fn touch_grid(grid: &mut Grid) -> i32 {
            \\    grid.*[0] = 42;
            \\    return grid.*[0];
            \\}
        ;
        var full_bundle = try lowerSourceToHir(allocator, sub_src, TargetLayout.NATIVE_64);
        defer full_bundle.deinit();
        try std.testing.expect(!full_bundle.diagnostics.hasErrors());

        var touch_def: DefId = DefId.NONE;
        for (full_bundle.sym_table.symbols.items) |sym_item| {
            if (sym_item.kind == .fn_sym and std.mem.eql(u8, sym_item.name_text, "touch_grid")) {
                touch_def = sym_item.def_id;
                break;
            }
        }
        try std.testing.expect(!touch_def.isNone());

        var single_sink = DiagnosticSink.init(allocator);
        defer single_sink.deinit();
        var single_store = try lowerDefToHir(
            allocator,
            touch_def,
            sub_src,
            &full_bundle.tokens,
            &full_bundle.cst_arena,
            &full_bundle.ast_arena,
            &full_bundle.interner,
            &full_bundle.pool,
            &full_bundle.sym_table,
            &full_bundle.side_tables,
            &single_sink,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer single_store.deinit();
        try std.testing.expect(!single_sink.hasErrors());

        var has_let_sub = false;
        var has_inout_sub = false;
        for (single_store.functions.items) |fn_meta| {
            if (!fn_meta.is_subscript) continue;
            if (fn_meta.is_subscript_inout_arm) {
                has_inout_sub = true;
            } else {
                has_let_sub = true;
            }
        }
        try std.testing.expect(has_let_sub);
        try std.testing.expect(has_inout_sub);
    }

    // [2] Verify inner closure `@caller_location()` isolation and raw multiline strings:
    {
        const closure_and_raw_src =
            \\pub fn capture_line(loc: SourceLoc = @caller_location()) -> u32 {
            \\    return loc.line;
            \\}
            \\pub fn outer_caller(loc: SourceLoc = @caller_location()) -> u32 {
            \\    let zero_cap_fn: fn() -> u32 = || -> u32 {
            \\        return capture_line();
            \\    };
            \\    let raw_multi: str = r"""
            \\        alpha\n
            \\        beta
            \\        """;
            \\    let raw_hashed: str = r#"""
            \\        "quoted"
            \\        """#;
            \\    let matched_tag: u32 = match raw_multi {
            \\        r"""
            \\            alpha\n
            \\            beta
            \\            """ => 10,
            \\        _ => 0,
            \\    };
            \\    let _ = raw_hashed;
            \\    return loc.line + zero_cap_fn() + matched_tag;
            \\}
        ;
        var cr_bundle = try lowerSourceToHir(allocator, closure_and_raw_src, TargetLayout.NATIVE_64);
        defer cr_bundle.deinit();
        try std.testing.expect(!cr_bundle.diagnostics.hasErrors());

        var has_seen_zero_capture_closure = false;
        for (cr_bundle.hir_store.functions.items) |fn_meta| {
            if (fn_meta.symbol_index.isNone()) {
                has_seen_zero_capture_closure = true;
                try std.testing.expectEqual(@as(u16, 0), fn_meta.capture_len);
            }
        }
        try std.testing.expect(has_seen_zero_capture_closure);

        var has_seen_stripped_raw_multi = false;
        var has_seen_stripped_raw_hashed = false;
        var has_seen_closure_line_6 = false;
        for (cr_bundle.hir_store.const_pool.items) |const_item| {
            switch (const_item) {
                .str_val => |str_sym| {
                    const text = cr_bundle.interner.get(str_sym);
                    if (std.mem.eql(u8, text, "alpha\\n\nbeta")) has_seen_stripped_raw_multi = true;
                    if (std.mem.eql(u8, text, "\"quoted\"")) has_seen_stripped_raw_hashed = true;
                },
                .aggregate => |agg_val| {
                    if (agg_val.type_id == .source_loc_ty and agg_val.elem_len >= 3) {
                        const line_const_idx = cr_bundle.hir_store.const_elements.items[agg_val.elem_start + 2];
                        const line_item = cr_bundle.hir_store.const_pool.items[line_const_idx];
                        if (line_item == .int_val and line_item.int_val == 6) has_seen_closure_line_6 = true;
                    }
                },
                else => {},
            }
        }
        try std.testing.expect(has_seen_stripped_raw_multi);
        try std.testing.expect(has_seen_stripped_raw_hashed);
        try std.testing.expect(has_seen_closure_line_6);
    }

    // [3] Verify Phase-0 parallel LHS freezes `.deref_expr` on `.ident_expr` and `.call_expr` place roots:
    {
        const par_lhs_src =
            \\pub fn rebind_raw(slot: &mut *mut i32, next_ptr: *mut i32) -> i32 {
            \\    slot.* = next_ptr;
            \\    return 99;
            \\}
            \\pub fn view_arr(arr: &mut [i32; 2]) -> *mut [i32; 2] {
            \\    return &raw mut arr.*;
            \\}
            \\pub fn parallel_freeze() -> i32 {
            \\    var val_a: i32 = 10;
            \\    var val_b: i32 = 20;
            \\    var side_out: i32 = 0;
            \\    var arr_a: [i32; 2] = [1, 2];
            \\    var arr_b: [i32; 2] = [3, 4];
            \\    var raw_p: *mut i32 = &raw mut val_a;
            \\    unsafe {
            \\        (raw_p.*, side_out) = (rebind_raw(&mut raw_p, &raw mut val_b), 55);
            \\        (view_arr(&mut arr_a).*[0], view_arr(&mut arr_b).*[0]) = (7, 8);
            \\    }
            \\    return val_a + val_b + side_out + arr_a[0] + arr_b[0];
            \\}
        ;
        var par_bundle = try lowerSourceToHir(allocator, par_lhs_src, TargetLayout.NATIVE_64);
        defer par_bundle.deinit();
        try std.testing.expect(!par_bundle.diagnostics.hasErrors());
        try std.testing.expectEqual(@as(u32, 2), par_bundle.hir_store.parallel_assign_blocks.count());

        var block_iter = par_bundle.hir_store.parallel_assign_blocks.iterator();
        while (block_iter.next()) |entry| {
            const blk_node = par_bundle.hir_store.getNode(HirIndex.fromInt(entry.key_ptr.*));
            try std.testing.expectEqual(HirTag.hir_block, blk_node.tag);
            const stmts = par_bundle.hir_store.getLenPrefixedExtra(blk_node.data.lhs);
            try std.testing.expect(stmts.len >= 4);
            const first_stmt = par_bundle.hir_store.getNode(HirIndex.fromInt(stmts[0]));
            try std.testing.expectEqual(HirTag.hir_local_decl, first_stmt.tag);
            const pre_eval_ty = par_bundle.hir_store.locals.items[first_stmt.data.lhs].type_id;
            try std.testing.expectEqual(type_system.TypeTag.raw_ptr_ty, par_bundle.pool.getTag(pre_eval_ty));
        }
    }

    // [4] Verify same-file `S { .. }` and cross-file `CompilerDb` `@caller_location()` span slicing without OOB:
    {
        var db = try query_db.CompilerDb.init(allocator);
        defer db.deinit();

        const lib_file = FileId.fromInt(81);
        const caller_file = FileId.fromInt(82);
        const short_lib_src =
            \\pub struct ExtStamp { pub tag: i32 = 1, pub loc: SourceLoc = @caller_location() }
            \\pub fn ext_line(tag: i32 = 0, loc: SourceLoc = @caller_location()) -> u32 { return loc.line; }
        ;
        const padded_caller_src =
            \\use stamp_lib.{ExtStamp, ext_line};
            \\// padding line 2 ensuring caller byte offset exceeds short_lib_src.len (178 bytes)
            \\// padding line 3: 0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
            \\// padding line 4: 0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
            \\pub struct LocalStamp {
            \\    pub id: i32,
            \\    pub loc: SourceLoc = @caller_location(),
            \\}
            \\pub fn make_stamps() -> u32 {
            \\    let same_s = LocalStamp { id: 5, .. };
            \\    let ext_s = ExtStamp { .. };
            \\    let ext_ln = ext_line();
            \\    return same_s.loc.line + ext_s.loc.line + ext_ln;
            \\}
        ;
        try db.registerRootModule("stamp_lib", lib_file);
        _ = try db.setInput(lib_file, short_lib_src, .low);
        _ = try db.setInput(caller_file, padded_caller_src, .low);

        const caller_tree = try db.extractItemTree(caller_file);
        var make_stamps_def: DefId = DefId.NONE;
        for (caller_tree.entries) |tree_entry| {
            if (std.mem.eql(u8, tree_entry.name_text, "make_stamps")) {
                make_stamps_def = tree_entry.def_id;
                break;
            }
        }
        try std.testing.expect(!make_stamps_def.isNone());
        const caller_hir = try db.lowerDefHir(make_stamps_def);

        var has_seen_line_10 = false;
        var has_seen_line_11 = false;
        var has_seen_line_12 = false;
        for (caller_hir.const_pool.items) |const_item| {
            if (const_item == .aggregate and const_item.aggregate.type_id == .source_loc_ty and
                const_item.aggregate.elem_len >= 3)
            {
                const line_const_idx = caller_hir.const_elements.items[const_item.aggregate.elem_start + 2];
                const line_item = caller_hir.const_pool.items[line_const_idx];
                if (line_item == .int_val) {
                    if (line_item.int_val == 10) has_seen_line_10 = true;
                    if (line_item.int_val == 11) has_seen_line_11 = true;
                    if (line_item.int_val == 12) has_seen_line_12 = true;
                }
            }
        }
        try std.testing.expect(has_seen_line_10);
        try std.testing.expect(has_seen_line_11);
        try std.testing.expect(has_seen_line_12);
    }

    // [5] Regression guard: `.method_call` `member_tok` colliding with `.subscript_decl` `NodeIndex` inside
    // `hasDollarAstDepth` must never reinterpret `TokenIndex` or `arm_mode = 0` (`NodeIndex.root`) as AST children:
    {
        const collision_src =
            \\pub fn scoped_arena_non_escaping() -> usize {
            \\    var local_arena = Arena { bump_tag: 64 };
            \\    defer { close_arena(own local_arena); }
            \\    return with context.allocator = &mut local_arena {
            \\        let temp_buf = alloc_ctx_buf(32);
            \\        temp_buf.byte_len
            \\    };
            \\}
            \\@no_alloc
            \\@no_panic
            \\@no_block
            \\@max_stack(512)
            \\pub fn strict_pentagon_probe(data: &[u8], raw_idx: usize, clamped_val: i32) -> u8 {
            \\    if data.len() > 0 and clamped_val >= 0 and clamped_val <= 200 {
            \\        let elem_byte = data[raw_idx % data.len()];
            \\        let narrowed_byte: u8 = clamped_val.narrow[u8]();
            \\        return elem_byte & narrowed_byte;
            \\    }
            \\    return 0;
            \\}
            \\pub fn bad_static_oob() -> i64 {
            \\    let fixed_vals: [i64; 3] = [10, 20, 30];
            \\    return fixed_vals[3];
            \\}
            \\pub struct CheckedLanes {
            \\    pub lanes: [i64; 4],
            \\}
            \\impl CheckedLanes {
            \\    pub subscript(lane_idx: usize, /) -> i64 {
            \\        let { yield self.lanes[lane_idx % 4]; }
            \\        inout { yield &mut self.lanes[lane_idx % 4]; }
            \\    }
            \\}
        ;
        var col_bundle = try lowerSourceToHir(
            allocator,
            collision_src,
            TargetLayout.NATIVE_64,
        );
        defer col_bundle.deinit();
        try std.testing.expect(col_bundle.diagnostics.hasErrors());
    }
}

test "test_hir_async_block_borrow_loans_nested_mutation_scan_and_pipe_variadic_promotion" {
    const allocator = std.testing.allocator;

    // [1] Non-`own` `async { … }` + `hir_cond_if` + `#soa` + nested `task_group` mint `&mut` loans:
    const async_loan_src =
        \\use cx.async.task_group;
        \\pub struct Particle {
        \\    pub x: i32,
        \\    pub y: i32,
        \\}
        \\pub async fn capture_mutations(opt_v: i32?) -> i32 {
        \\    var count: i32 = 0;
        \\    var parts: #soa [Particle; 2] = @default_init[#soa [Particle; 2]]();
        \\    let fut_a = async {
        \\        if opt_v is .Some(val) {
        \\            count += val;
        \\            parts[0].x += val;
        \\        }
        \\        count
        \\    };
        \\    let a_out = fut_a.await;
        \\    let nested_fut = task_group(|grp| {
        \\        let handle = grp.spawn(|| {
        \\            count += 1;
        \\            count
        \\        });
        \\        handle.join().await
        \\    });
        \\    let n_out = nested_fut.await;
        \\    let moved_fut = own async { count };
        \\    return a_out + n_out + moved_fut.await;
        \\}
    ;
    var loan_bundle = try lowerSourceToHir(allocator, async_loan_src, TargetLayout.NATIVE_64);
    defer loan_bundle.deinit();
    try std.testing.expect(!loan_bundle.diagnostics.hasErrors());

    var mut_loan_intrinsic_count: usize = 0;
    var has_seen_borrow_async_clos = false;
    var has_seen_move_async_clos = false;
    for (loan_bundle.hir_store.functions.items) |fn_meta| {
        if (fn_meta.is_async and fn_meta.def_id.asInt() >= 0x5000_0000) {
            if (fn_meta.is_local_closure and !fn_meta.is_move_closure) has_seen_borrow_async_clos = true;
            if (!fn_meta.is_local_closure and fn_meta.is_move_closure) has_seen_move_async_clos = true;
        }
    }
    try std.testing.expect(has_seen_borrow_async_clos);
    try std.testing.expect(has_seen_move_async_clos);

    for (0..loan_bundle.hir_store.nodes.len) |n_idx| {
        const node = loan_bundle.hir_store.getNode(HirIndex.fromInt(@intCast(n_idx)));
        if (node.tag == .hir_intrinsic_call and (node.data.lhs & HIR_INTERNAL_INTRINSIC_FLAG) != 0) {
            const sub_kind: HirInternalIntrinsic = @fromBackingInt(@intCast(@as(u8, @truncate(node.data.lhs))));
            if (sub_kind == .async_future_make) {
                const val_len = loan_bundle.hir_store.extra_data.items[node.data.rhs + 1];
                if (val_len > 3) {
                    const loan_slice = loan_bundle.hir_store.extra_data.items[node.data.rhs + 2 + 3 .. node.data.rhs + 2 + val_len];
                    for (loan_slice) |loan_raw| {
                        const loan_node = loan_bundle.hir_store.getNode(HirIndex.fromInt(loan_raw));
                        if (loan_node.tag == .hir_unary_op and
                            loan_node.data.lhs == @backingInt(HirUnaryOp.addr_of_mut))
                        {
                            mut_loan_intrinsic_count += 1;
                        }
                    }
                }
            }
        }
    }
    // `fut_a` mints `&mut count` + `&mut parts` (2), and `nested_fut` mints `&mut count` (1) -> >= 3 `&mut` loans:
    try std.testing.expect(mut_loan_intrinsic_count >= 3);

    // [2] Indirect C variadic function-pointer call through `|>` promotes `bool`/`i8` -> `i32` & `f32` -> `f64`:
    const pipe_var_src =
        \\pub fn invoke_pipe_variadic(
        \\    fp: extern "C" fn(*u8, ...) -> i32,
        \\    fmt_ptr: *u8,
        \\    small_i8: i8,
        \\    flag: bool,
        \\    half_flt: f32,
        \\) -> i32 {
        \\    return unsafe { fmt_ptr |> fp(small_i8, flag, half_flt) };
        \\}
    ;
    var pipe_bundle = try lowerSourceToHir(allocator, pipe_var_src, TargetLayout.NATIVE_64);
    defer pipe_bundle.deinit();
    try std.testing.expect(!pipe_bundle.diagnostics.hasErrors());

    var has_verified_pipe_call = false;
    for (0..pipe_bundle.hir_store.nodes.len) |n_idx| {
        const node = pipe_bundle.hir_store.getNode(HirIndex.fromInt(@intCast(n_idx)));
        if (node.tag == .hir_call) {
            const call_args = pipe_bundle.hir_store.getLenPrefixedExtra(node.data.rhs);
            if (call_args.len == 4) {
                has_verified_pipe_call = true;
                try std.testing.expectEqual(
                    TypeId.i32_ty,
                    pipe_bundle.hir_store.getNode(HirIndex.fromInt(call_args[1])).type_id,
                );
                try std.testing.expectEqual(
                    TypeId.i32_ty,
                    pipe_bundle.hir_store.getNode(HirIndex.fromInt(call_args[2])).type_id,
                );
                try std.testing.expectEqual(
                    TypeId.f64_ty,
                    pipe_bundle.hir_store.getNode(HirIndex.fromInt(call_args[3])).type_id,
                );
            }
        }
    }
    try std.testing.expect(has_verified_pipe_call);
}

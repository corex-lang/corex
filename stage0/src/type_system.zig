//! Canonical `InternPool` (`TypeArena`), Constrained Type Groups & Bidirectional Type Checker
//!
//! Implements Phase 4 and Phase 5 frontend semantics (`PLAN.md` Sections 2.2–2.3, `DR-02` Deliverable 2,
//! `DR-04` Deliverables 1–4, `DR-05` Deliverables 1–2, and `DR-07` Section 2):
//! - 14-byte zero-padding SoA `TypeNode` (`TypeTag`, `TypeFlags`, `ParamMode`) and `InternPool`
//!   (`TypeArena`) pre-populating static `TypeId` slots `0..63` (19 primitives `0..18`, sentinels
//!   `19..21`, and 11 Constrained Type Groups `32..42` with $O(1)$ 32-bit `TypeGroupMask` checks),
//! - User-defined Type Groups (`type G = A | ~B`), `distinct` newtypes (`~T` approximation, `E0405`),
//!   compile-time range refinements (`T is low..=high`, `E0406`), `bit_field` width verification,
//!   `#soa` column-slice projection, symbolic `[T; N]` & arithmetic `[T; EXPR]` array lengths, and
//!   target-aware `TargetLayout` / `TypeLayout` calculation (`native_64` and `wasm32`),
//! - Spine-local Dunfield–Krishnaswami bidirectional type checking, `comptime` blocks/loops/params,
//!   all 9 `DR-05` reflection intrinsics (`std::meta`), `@attribute_schema`, Two-Phase `@derive`,
//!   `expr is Pattern`, `defer`/`errdefer` control-flow guards, and per-body `BodySemanticSideTables`.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const parser = @import("parser.zig");
const diagnostic = @import("diag/diagnostic.zig");
const query_db = @import("query_db.zig");

/// Re-exported canonical 32-bit `TypeId` handle (`0..63` static, `>= 64` dynamic).
pub const TypeId = mem_foundation.TypeId;

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const NodeIndex = mem_foundation.NodeIndex;
const ExtraIndex = mem_foundation.ExtraIndex;
const ScopeId = mem_foundation.ScopeId;
const DefId = query_db.DefId;
const TokenKind = syntax_arenas.TokenKind;
const CstNodeKind = syntax_arenas.CstNodeKind;
const AstTag = syntax_arenas.AstTag;
const TokenBuffer = syntax_arenas.TokenBuffer;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstArena = syntax_arenas.AstArena;
const Namespace = symbol_resolver.Namespace;
const NamespaceMask = symbol_resolver.NamespaceMask;
const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolKind = symbol_resolver.SymbolKind;
const SymbolRecord = symbol_resolver.SymbolRecord;
const SymbolTable = symbol_resolver.SymbolTable;
const DiagnosticSink = diagnostic.DiagnosticSink;
const DiagnosticCode = diagnostic.DiagnosticCode;
const Severity = diagnostic.Severity;
const LabeledSpan = diagnostic.LabeledSpan;

// ---------------------------------------- TYPES ----------------------------------------

// --------- Constrained Type Group Bitmasks (`DR-04`) ----------

/// 32-bit bitmask of primitive `TypeId`s (`0..18`) for $O(1)$ Constrained Type Group checks (`DR-04` Section 1.2).
pub const TypeGroupMask = struct {
    /// `Signed = i8 | i16 | i32 | i64 | i128 | isize` (slots `5..10`).
    pub const SIGNED: u32 = TypeId.i8_ty.primitiveBit() |
        TypeId.i16_ty.primitiveBit() |
        TypeId.i32_ty.primitiveBit() |
        TypeId.i64_ty.primitiveBit() |
        TypeId.i128_ty.primitiveBit() |
        TypeId.isize_ty.primitiveBit();
    /// `Unsigned = u8 | u16 | u32 | u64 | u128 | usize` (slots `11..16`).
    pub const UNSIGNED: u32 = TypeId.u8_ty.primitiveBit() |
        TypeId.u16_ty.primitiveBit() |
        TypeId.u32_ty.primitiveBit() |
        TypeId.u64_ty.primitiveBit() |
        TypeId.u128_ty.primitiveBit() |
        TypeId.usize_ty.primitiveBit();
    /// `Integer = Signed | Unsigned` (slots `5..16`).
    pub const INTEGER: u32 = SIGNED | UNSIGNED;
    /// `Float = f32 | f64` (slots `17..18`).
    pub const FLOAT: u32 = TypeId.f32_ty.primitiveBit() | TypeId.f64_ty.primitiveBit();
    /// `Number = Integer | Float` (slots `5..18`).
    pub const NUMBER: u32 = INTEGER | FLOAT;
    /// `Numeric = Number` (alias bitmask for numeric algorithms, slots `5..18`).
    pub const NUMERIC: u32 = NUMBER;
    /// `Comparable = Number | bool | char | str` (slots `2..18`).
    pub const COMPARABLE: u32 = NUMBER |
        TypeId.bool_ty.primitiveBit() |
        TypeId.char_ty.primitiveBit() |
        TypeId.str_ty.primitiveBit();
    /// `Equatable = Comparable | unit` (slots `0` and `2..18`).
    pub const EQUATABLE: u32 = COMPARABLE | TypeId.unit_ty.primitiveBit();
    /// `Bytes = u8 | i8` (slots `5` and `11`).
    pub const BYTES: u32 = TypeId.i8_ty.primitiveBit() | TypeId.u8_ty.primitiveBit();
    /// `Scalar = Number | bool | char` (slots `2..3` and `5..18`).
    pub const SCALAR: u32 = NUMBER | TypeId.bool_ty.primitiveBit() | TypeId.char_ty.primitiveBit();
    /// `Copy = Scalar | str | never | unit` (all 19 primitives, slots `0..18`).
    pub const COPY: u32 = (1 << 19) - 1;

    /// Returns `true` if `prim_ty` (`0..18`) is a member of `group_mask` in $O(1)$ bit-test time.
    pub inline fn containsPrimitive(group_mask: u32, prim_ty: TypeId) bool {
        return (group_mask & prim_ty.primitiveBit()) != 0;
    }

    /// Returns `true` if every primitive in `sub_mask` is also in `super_mask` (`(sub & ~super) == 0`).
    pub inline fn isSubsetOf(sub_mask: u32, super_mask: u32) bool {
        return (sub_mask & ~super_mask) == 0;
    }

    /// Returns the canonical 32-bit `TypeGroupMask` for a built-in group `TypeId` (`32..42`).
    pub inline fn forBuiltinGroup(group_id: TypeId) u32 {
        return switch (group_id) {
            .group_signed => SIGNED,
            .group_unsigned => UNSIGNED,
            .group_integer => INTEGER,
            .group_float => FLOAT,
            .group_number => NUMBER,
            .group_numeric => NUMERIC,
            .group_comparable => COMPARABLE,
            .group_equatable => EQUATABLE,
            .group_bytes => BYTES,
            .group_scalar => SCALAR,
            .group_copy => COPY,
            else => 0,
        };
    }
};

// -------------- 14-Byte SoA `TypeNode` (`DR-04`) --------------

/// Discriminant tag for `TypeNode` in `InternPool` (`DR-04` Section 2.2).
pub const TypeTag = enum(u8) {
    /// Built-in primitive type (`i8`..`unit`, or sentinels `untyped_int_ty`/`untyped_float_ty`/`err_ty`).
    primitive = 0,
    /// Built-in Constrained Type Group (`Signed`..`Copy`, `lhs = TypeGroupMask`).
    builtin_group = 1,
    /// User-defined Constrained Type Group (`type G = A | ~B`, `lhs = extra_start`, `rhs = def_id`).
    user_group = 2,
    /// Nominal `distinct` newtype (`type Id = distinct u64`, `lhs = base_ty`, `rhs = sym_idx`).
    distinct_ty = 3,
    /// Range or pattern refinement type (`T is low..=high`, `lhs = base_ty`, `rhs = extra_start`).
    refined_ty = 4,
    /// Underlying-type approximation (`~T`, `lhs = target_ty`).
    tilde_approx = 5,
    /// Nominal `struct` type (`lhs = def_id`, `rhs = sym_idx`).
    struct_ty = 6,
    /// Nominal `enum` type (`lhs = def_id`, `rhs = sym_idx`).
    enum_ty = 7,
    /// Nominal `union` type (`lhs = def_id`, `rhs = sym_idx`).
    union_ty = 8,
    /// Packed `bit_field` integer type (`lhs = backing_ty`, `rhs = sym_idx`).
    bit_field_ty = 9,
    /// Structural tuple type (`(T1, T2)`, `lhs = extra_start`, `rhs = arity`).
    tuple_ty = 10,
    /// Fixed-length array type (`[T; N]`, `lhs = elem_ty`, `rhs = len`).
    array_ty = 11,
    /// Dynamically sized slice type (`[T]`, `lhs = elem_ty`).
    slice_ty = 12,
    /// Structure-of-Arrays slice type (`#soa [T]`, `lhs = elem_ty`).
    soa_slice_ty = 13,
    /// Structure-of-Arrays fixed array type (`#soa [T; N]`, `lhs = elem_ty`, `rhs = len`).
    soa_array_ty = 14,
    /// First-class optional type (`T?`, `lhs = payload_ty`).
    optional_ty = 15,
    /// First-class error result type (`Result[T, E]`, `lhs = ok_ty`, `rhs = err_ty`).
    result_ty = 16,
    /// Shared borrowed reference (`&T` / `ref T`, `lhs = pointee_ty`).
    ref_ty = 17,
    /// Exclusive mutable reference (`&mut T` / `inout T`, `lhs = pointee_ty`).
    mut_ref_ty = 18,
    /// Raw pointer (`*T` or `*mut T`, `lhs = pointee_ty`, `rhs = is_mut`).
    raw_ptr_ty = 19,
    /// Function signature type (`fn(P…) -> R`, `lhs = extra_start`, `rhs = ret_ty`).
    fn_ty = 20,
    /// Anonymous closure type (`|P…| -> R`, `lhs = extra_start`, `rhs = ret_ty`).
    closure_ty = 21,
    /// Nominal `trait` interface (`lhs = def_id`, `rhs = sym_idx`).
    trait_ty = 22,
    /// Type-erased `dyn Trait` existential (`lhs = trait_ty`).
    dyn_trait_ty = 23,
    /// Generic type parameter (`[T: Bound]`, `lhs = bound_ty`, `rhs = name_sym`).
    type_param = 24,
    /// Bind-once Constrained Type Group variable (`x: Number, y: Number`, `lhs = group_ty`, `rhs = name_sym`).
    bind_once_group_var = 25,
    /// Bind-many independent `any Group` variable (`x: any Number`, `lhs = group_ty`, `rhs = ordinal`).
    bind_many_any_var = 26,
    /// Associated trait projection (`T::Item`, `lhs = base_ty`, `rhs = assoc_name_sym`).
    associated_ty = 27,
};

/// 1-byte bit-packed semantic properties cached on every `TypeNode` (`DR-04` Section 2.2).
pub const TypeFlags = packed struct(u8) {
    /// `true` if values of this type are implicitly `Copy` (bitwise copyable).
    is_copy: bool = false,
    /// `true` if this type or any child contains `type_param`, `bind_once_group_var`, or `bind_many_any_var`.
    has_type_vars: bool = false,
    /// `true` if this type contains a borrowed reference (`&T` / `&mut T`).
    has_regions: bool = false,
    /// `true` if this type is or contains `TypeId.err_ty` (suppresses cascading diagnostics).
    has_error: bool = false,
    /// `true` if values of this type must not be silently ignored (`Result[T, E]` or `@must_use`).
    is_must_use: bool = false,
    /// `true` if this type has a statically known compile-time size.
    is_sized: bool = true,
    /// `true` if this type carries `#soa` layout.
    is_soa: bool = false,
    /// `true` if this type has a custom destructor (`Drop`).
    has_drop: bool = false,
};

/// Parameter passing convention mode (`DR-02` Section 1.1 & `DR-04` Section 2.2).
pub const ParamMode = enum(u2) {
    /// Immutable borrow/value convention (`let`, default).
    let_mode = 0,
    /// Exclusive in-place mutation convention (`inout` / `&mut`).
    inout_mode = 1,
    /// Ownership consumption convention (`sink` / `own`).
    sink_mode = 2,
    /// Uninitialized out-parameter initialization convention (`set`).
    set_mode = 3,
};

/// 14-byte SoA type record (`1B tag + 1B flags + 4B hash + 4B lhs + 4B rhs = 14B` across SoA columns).
pub const TypeNode = struct {
    /// Structural category of the type (`1` byte).
    tag: TypeTag,
    /// Cached semantic flags (`1` byte).
    flags: TypeFlags = .{},
    /// Canonical 32-bit structural `Wyhash(0)` digest (`4` bytes).
    hash: u32 = 0,
    /// Primary payload (`TypeId`, `DefId`, `TypeGroupMask`, or `extra` start index, `4` bytes).
    lhs: u32 = 0,
    /// Secondary payload (`TypeId`, `SymbolIndex`, array length, or `extra` count, `4` bytes).
    rhs: u32 = 0,
};

/// Decoded inclusive 128-bit integer refinement bounds (`T is min_val..=max_val`).
pub const RefinementBounds = struct {
    /// Underlying primitive or nominal integer `TypeId`.
    base_ty: TypeId,
    /// Defining `SymbolIndex` of the refined type alias.
    sym_idx: SymbolIndex,
    /// Inclusive lower bound (`i128`).
    min_val: i128,
    /// Inclusive upper bound (`i128`).
    max_val: i128,
};

/// Decoded user-defined Constrained Type Group (`type G = A | ~B`).
pub const UserTypeGroupView = struct {
    /// Defining `SymbolIndex` of the type group.
    sym_idx: SymbolIndex,
    /// Bitmask of exact primitive types (`0..18`) included in the group.
    prim_mask: u32,
    /// Bitmask of `~Primitive` underlying approximations (`0..18`) included in the group.
    tilde_prim_mask: u32,
    /// Slice of exact non-primitive member `TypeId.toU32()` handles.
    exact_members: []const u32,
    /// Slice of `~Nominal` underlying member `TypeId.toU32()` handles.
    tilde_members: []const u32,
};

/// Decoded function or closure signature from `InternPool.extra`.
pub const FnSignatureView = struct {
    /// Return `TypeId`.
    ret_ty: TypeId,
    /// Slice of parameter `TypeId.toU32()` values (`arity` elements).
    param_types: []const u32,
    /// Slice of packed `ParamMode` values (`arity` elements).
    param_modes: []const u32,

    /// Returns the number of parameters in the signature.
    pub inline fn paramCount(self: FnSignatureView) usize {
        return self.param_types.len;
    }

    /// Returns the `TypeId` of parameter `idx`.
    pub inline fn getParamType(self: FnSignatureView, idx: usize) TypeId {
        if (idx >= self.param_types.len) return .err_ty;
        return TypeId.fromInt(self.param_types[idx]);
    }

    /// Returns the `ParamMode` of parameter `idx`.
    pub inline fn getParamMode(self: FnSignatureView, idx: usize) ParamMode {
        if (idx >= self.param_modes.len) return .let_mode;
        return @enumFromInt(@as(u2, @truncate(self.param_modes[idx])));
    }
};

// ---------- `SubstitutionMap` (`DR-04` Section 2.4) -----------

/// Single binding pair mapping a type variable `TypeId` to its instantiated `TypeId`.
pub const SubstEntry = struct {
    /// Type variable (`bind_once_group_var`, `bind_many_any_var`, or `type_param`).
    var_ty: TypeId,
    /// Bound target `TypeId`.
    concrete_ty: TypeId,
    /// Source `Span` of the argument that established this binding (for `E0404` secondary labels).
    first_bind_span: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 },
};

/// Stack-first substitution table for call-site generic and Type Group instantiation (`DR-04` Section 2.4).
pub const SubstitutionMap = struct {
    /// Inline small-buffer storage covering `<= 16` type variables with zero heap allocations.
    inline_entries: [16]SubstEntry = undefined,
    /// Number of active entries in `inline_entries` (`0..16`).
    inline_len: u8 = 0,
    /// Overflow heap list used only when a signature exceeds 16 distinct type variables.
    overflow_entries: std.ArrayListUnmanaged(SubstEntry) = .empty,

    /// Releases any overflow storage back to `allocator`.
    pub fn deinit(self: *SubstitutionMap, allocator: std.mem.Allocator) void {
        self.overflow_entries.deinit(allocator);
        self.* = undefined;
    }

    /// Clears all bindings while retaining overflow capacity.
    pub fn clear(self: *SubstitutionMap) void {
        self.inline_len = 0;
        self.overflow_entries.clearRetainingCapacity();
    }

    /// Looks up the bound `SubstEntry` for `var_ty`, or `null` if unbound.
    pub fn getEntry(self: *const SubstitutionMap, var_ty: TypeId) ?SubstEntry {
        var i: usize = 0;
        while (i < self.inline_len) : (i += 1) {
            if (self.inline_entries[i].var_ty == var_ty) return self.inline_entries[i];
        }
        for (self.overflow_entries.items) |entry| {
            if (entry.var_ty == var_ty) return entry;
        }
        return null;
    }

    /// Looks up the bound `TypeId` for `var_ty`, or `null` if unbound.
    pub inline fn lookup(self: *const SubstitutionMap, var_ty: TypeId) ?TypeId {
        if (self.getEntry(var_ty)) |entry| return entry.concrete_ty;
        return null;
    }

    /// Inserts or updates the binding `var_ty -> concrete_ty` with `bind_span`.
    pub fn put(
        self: *SubstitutionMap,
        allocator: std.mem.Allocator,
        var_ty: TypeId,
        concrete_ty: TypeId,
        bind_span: Span,
    ) !void {
        var i: usize = 0;
        while (i < self.inline_len) : (i += 1) {
            if (self.inline_entries[i].var_ty == var_ty) {
                self.inline_entries[i].concrete_ty = concrete_ty;
                if (self.inline_entries[i].first_bind_span.file_id.isNone()) {
                    self.inline_entries[i].first_bind_span = bind_span;
                }
                return;
            }
        }
        for (self.overflow_entries.items) |*entry| {
            if (entry.var_ty == var_ty) {
                entry.concrete_ty = concrete_ty;
                if (entry.first_bind_span.file_id.isNone()) {
                    entry.first_bind_span = bind_span;
                }
                return;
            }
        }
        if (self.inline_len < self.inline_entries.len) {
            self.inline_entries[self.inline_len] = .{
                .var_ty = var_ty,
                .concrete_ty = concrete_ty,
                .first_bind_span = bind_span,
            };
            self.inline_len += 1;
            return;
        }
        try self.overflow_entries.append(allocator, .{
            .var_ty = var_ty,
            .concrete_ty = concrete_ty,
            .first_bind_span = bind_span,
        });
    }

    /// Recursively substitutes bound type variables inside `ty`, returning immediately in $O(1)$ if `!has_type_vars`.
    pub fn apply(self: *const SubstitutionMap, pool: *InternPool, ty: TypeId) !TypeId {
        return self.applyBounded(pool, ty, 0);
    }

    /// Depth-bounded helper (`MAX_TYPE_DEPTH`) for `apply`.
    fn applyBounded(self: *const SubstitutionMap, pool: *InternPool, ty: TypeId, depth: u32) anyerror!TypeId {
        if (depth >= MAX_TYPE_DEPTH) return .err_ty;
        if (ty.isPrimitiveOrSentinel() or ty.isBuiltinGroup()) return ty;
        const node = pool.getNode(ty);
        if (!node.flags.has_type_vars) return ty;

        return switch (node.tag) {
            .bind_once_group_var, .bind_many_any_var, .type_param => blk: {
                if (self.lookup(ty)) |bound| {
                    if (bound == .untyped_int_ty) break :blk defaultConcreteForGroup(TypeId.fromInt(node.lhs), true);
                    if (bound == .untyped_float_ty) break :blk defaultConcreteForGroup(TypeId.fromInt(node.lhs), false);
                    break :blk bound;
                }
                break :blk ty;
            },
            .optional_ty => try pool.internOptional(
                try self.applyBounded(pool, TypeId.fromInt(node.lhs), depth + 1),
            ),
            .result_ty => try pool.internResult(
                try self.applyBounded(pool, TypeId.fromInt(node.lhs), depth + 1),
                try self.applyBounded(pool, TypeId.fromInt(node.rhs), depth + 1),
            ),
            .slice_ty => try pool.internSlice(
                try self.applyBounded(pool, TypeId.fromInt(node.lhs), depth + 1),
                false,
            ),
            .soa_slice_ty => try pool.internSlice(
                try self.applyBounded(pool, TypeId.fromInt(node.lhs), depth + 1),
                true,
            ),
            .array_ty, .soa_array_ty => blk: {
                const subst_elem = try self.applyBounded(pool, TypeId.fromInt(node.lhs), depth + 1);
                const is_soa = (node.tag == .soa_array_ty);
                if ((node.rhs & SYMBOLIC_ARRAY_LEN_FLAG) != 0) {
                    const const_sym = SymbolId.fromInt(node.rhs & ~SYMBOLIC_ARRAY_LEN_FLAG);
                    const len_key = try pool.internSymbolicArray(.unit_ty, const_sym, false);
                    if (self.lookup(len_key)) |bound_len_ty| {
                        const bound_node = pool.getNode(bound_len_ty);
                        if (bound_node.tag == .array_ty and (bound_node.rhs & SYMBOLIC_ARRAY_LEN_FLAG) == 0) {
                            break :blk try pool.internArray(subst_elem, bound_node.rhs, is_soa);
                        }
                    }
                    break :blk try pool.internSymbolicArray(subst_elem, const_sym, is_soa);
                }
                break :blk try pool.internArray(subst_elem, node.rhs, is_soa);
            },
            .ref_ty => try pool.internRef(
                try self.applyBounded(pool, TypeId.fromInt(node.lhs), depth + 1),
                false,
            ),
            .mut_ref_ty => try pool.internRef(
                try self.applyBounded(pool, TypeId.fromInt(node.lhs), depth + 1),
                true,
            ),
            .raw_ptr_ty => try pool.internRawPtr(
                try self.applyBounded(pool, TypeId.fromInt(node.lhs), depth + 1),
                node.rhs != 0,
            ),
            .tilde_approx => try pool.internTildeApprox(
                try self.applyBounded(pool, TypeId.fromInt(node.lhs), depth + 1),
            ),
            .tuple_ty => blk: {
                const arity: usize = node.rhs;
                if (arity == 0) break :blk .unit_ty;
                const elems = pool.extra.items[node.lhs .. node.lhs + arity];
                const subst_elems = try pool.allocator.alloc(TypeId, arity);
                defer pool.allocator.free(subst_elems);
                for (elems, 0..) |raw_elem, i| {
                    subst_elems[i] = try self.applyBounded(
                        pool,
                        TypeId.fromInt(raw_elem),
                        depth + 1,
                    );
                }
                break :blk try pool.internTuple(subst_elems);
            },
            else => ty,
        };
    }
};

// --------- Target Layout & Body Side Tables (`DR-05`) ---------

/// Target pointer size and alignment parameters shared across `TypeChecker`, `HIR`, `MirVm`, and `MIR`.
pub const TargetLayout = struct {
    /// Target pointer width in bytes (`8` on 64-bit hosts, `4` on `wasm32`).
    ptr_byte_size: u8 = 8,
    /// Base-2 logarithm of target pointer alignment (`3` -> 8-byte align, `2` -> 4-byte align).
    ptr_align_log2: u8 = 3,

    /// Canonical 64-bit native target layout (`x86_64` / `aarch64`).
    pub const NATIVE_64: TargetLayout = .{ .ptr_byte_size = 8, .ptr_align_log2 = 3 };
    /// Canonical 32-bit WebAssembly target layout (`wasm32`).
    pub const WASM32: TargetLayout = .{ .ptr_byte_size = 4, .ptr_align_log2 = 2 };

    /// Returns the pointer alignment in bytes (`1 << ptr_align_log2`).
    pub inline fn ptrAlignBytes(self: TargetLayout) u32 {
        return @as(u32, 1) << @intCast(self.ptr_align_log2);
    }
};

/// Computed target-specific byte size and alignment of a `TypeId`.
pub const TypeLayout = struct {
    /// Total padded size of the type in bytes (`0` for ZSTs and unsized symbolic types).
    byte_size: u64,
    /// Required alignment in bytes (`>= 1`, always a power of two).
    align_bytes: u32,
    /// Base-2 logarithm of `align_bytes`.
    align_log2: u8,
    /// `true` when the type has a statically known concrete size.
    is_sized: bool = true,
};

/// Validated compile-time constant argument value inside an `@attribute_schema` instance.
pub const AttrArgValue = union(enum) {
    /// Boolean literal (`true` / `false`).
    bool_val: bool,
    /// Unicode scalar character literal.
    char_val: u21,
    /// Signed or unsigned 128-bit integer constant.
    int_val: i128,
    /// 64-bit IEEE-754 floating-point constant.
    float_val: f64,
    /// Interned UTF-8 string literal (`SymbolId`).
    str_val: SymbolId,
    /// Enum variant ordinal tag (`0..N-1`).
    enum_tag: u32,
    /// Omitted or `.None` optional value.
    none_opt: void,
};

/// Single validated field argument on an `@attribute_schema` attribute application.
pub const AttrFieldInit = struct {
    /// Interned schema field name (`SymbolId.none` when positional).
    field_name: SymbolId,
    /// Resolved field ordinal (`0..N-1`) inside the `@attribute_schema` struct.
    field_ordinal: u16,
    /// Evaluated compile-time constant argument value.
    value: AttrArgValue,
};

/// Validated user-defined `@attribute_schema` instance attached to a declaration, field, or variant.
pub const AttrInstance = struct {
    /// Schema struct `TypeId` (`struct_ty` annotated with `@attribute_schema`).
    schema_type_id: TypeId,
    /// Target `SymbolIndex` receiving the attribute (`struct_sym`, `field_sym`, `enum_variant_sym`, etc.).
    target_symbol: SymbolIndex,
    /// Enclosing top-level item `DefId` (`DefId.NONE` when module-scoped without a `DefId`).
    owner_def_id: DefId,
    /// Source span of the `@Schema(...)` attribute application.
    attr_span: Span,
    /// Owned slice of validated constant field initializers.
    fields: []AttrFieldInit,
};

/// Per-body AST-window-scoped semantic side tables extracted from `TypeChecker` (`[CRITICAL-11]`).
///
/// Stores resolved types, symbols, generic instantiations, `?` conversions, and `@attribute_schema`
/// instances strictly within `[ast_start .. ast_end)` using window-relative keys (`node_id - ast_start`)
/// so sibling-body edits that shift `ast_start` preserve Early Cutoff via $O(1)$ `rebaseWindow`.
pub const BodySemanticSideTables = struct {
    /// Allocator owning all slices and maps in this artifact.
    allocator: std.mem.Allocator,
    /// Owning definition handle (`DefId.NONE` for whole-file extraction).
    def_id: DefId,
    /// Inclusive AST `NodeIndex` start of the body window.
    ast_start: u32,
    /// Exclusive AST `NodeIndex` end of the body window (`node_types.len == ast_end - ast_start`).
    ast_end: u32,
    /// Dense resolved `TypeId` per AST node in `[ast_start .. ast_end)`.
    node_types: []TypeId,
    /// Dense resolved `SymbolIndex` per AST node in `[ast_start .. ast_end)` (`.none` when unmapped).
    node_symbols: []SymbolIndex,
    /// Concrete generic / Type-Group `[TypeId…]` arguments keyed by relative AST offset (`node_id - ast_start`).
    call_instantiations: std.AutoHashMapUnmanaged(u32, []TypeId) = .empty,
    /// `@from` `FromError` conversion function `DefId`s keyed by relative `.try_expr` AST offset.
    try_conversions: std.AutoHashMapUnmanaged(u32, DefId) = .empty,
    /// Validated `@attribute_schema` instances scoped to `def_id` (or file when `def_id.isNone()`).
    attr_instances: []AttrInstance = &.{},

    /// Releases all owned slices and hash maps in `self`.
    pub fn deinit(self: *BodySemanticSideTables) void {
        if (self.node_types.len > 0) self.allocator.free(self.node_types);
        if (self.node_symbols.len > 0) self.allocator.free(self.node_symbols);
        var inst_iter = self.call_instantiations.valueIterator();
        while (inst_iter.next()) |slice_ptr| {
            if (slice_ptr.*.len > 0) self.allocator.free(slice_ptr.*);
        }
        self.call_instantiations.deinit(self.allocator);
        self.try_conversions.deinit(self.allocator);
        for (self.attr_instances) |attr_inst| {
            if (attr_inst.fields.len > 0) self.allocator.free(attr_inst.fields);
        }
        if (self.attr_instances.len > 0) self.allocator.free(self.attr_instances);
        self.* = undefined;
    }

    /// Rebases `[ast_start .. ast_end)` in $O(1)$ time when preceding sibling bodies shift AST indices.
    pub inline fn rebaseWindow(self: *BodySemanticSideTables, new_ast_start: u32) void {
        const window_len = self.ast_end - self.ast_start;
        self.ast_start = new_ast_start;
        self.ast_end = new_ast_start + window_len;
    }

    /// Looks up the resolved `TypeId` of `node_id` in $O(1)$ time (`.err_ty` if outside window).
    pub inline fn getNodeType(self: *const BodySemanticSideTables, node_id: NodeIndex) TypeId {
        if (node_id.isNone()) return .err_ty;
        const raw_idx = node_id.asInt();
        if (raw_idx < self.ast_start or raw_idx >= self.ast_end) return .err_ty;
        return self.node_types[raw_idx - self.ast_start];
    }

    /// Looks up the resolved `SymbolIndex` of `node_id` in $O(1)$ time (`.none` if unmapped).
    pub inline fn getNodeSymbol(self: *const BodySemanticSideTables, node_id: NodeIndex) SymbolIndex {
        if (node_id.isNone()) return .none;
        const raw_idx = node_id.asInt();
        if (raw_idx < self.ast_start or raw_idx >= self.ast_end) return .none;
        return self.node_symbols[raw_idx - self.ast_start];
    }

    /// Looks up the inferred concrete `TypeId` instantiation tuple for call AST node `call_id`.
    pub inline fn getCallInstantiation(
        self: *const BodySemanticSideTables,
        call_id: NodeIndex,
    ) ?[]const TypeId {
        if (call_id.isNone()) return null;
        const raw_idx = call_id.asInt();
        if (raw_idx < self.ast_start or raw_idx >= self.ast_end) return null;
        return self.call_instantiations.get(raw_idx - self.ast_start);
    }

    /// Looks up the `@from` conversion `DefId` recorded for `.try_expr` AST node `try_id`.
    pub inline fn getTryConversion(self: *const BodySemanticSideTables, try_id: NodeIndex) ?DefId {
        if (try_id.isNone()) return null;
        const raw_idx = try_id.asInt();
        if (raw_idx < self.ast_start or raw_idx >= self.ast_end) return null;
        return self.try_conversions.get(raw_idx - self.ast_start);
    }
};

/// Canonical compiler-intrinsic selector for `@snake_case` expressions (`DR-05` Section 3.3).
pub const IntrinsicKind = enum(u8) {
    /// `@align_of[T]() -> usize` (`0`).
    align_of = 0,
    /// `@compile_assert(cond: bool, msg: str) -> unit` (`1`).
    compile_assert = 1,
    /// `@compile_error(msg: str) -> never` (`2`).
    compile_error = 2,
    /// `@default_init[T]() -> T` (`3`).
    default_init = 3,
    /// `@embed_bytes(comptime path: str) -> &[u8]` (`4`).
    embed_bytes = 4,
    /// `@field(target, comptime field_ref) -> FieldTy` (`5`).
    field = 5,
    /// `@field_attr_lookup[A](id: MetaId, idx: u32) -> A?` (`6`).
    field_attr_lookup = 6,
    /// `@has_field[T](comptime name: str) -> bool` (`7`).
    has_field = 7,
    /// `@implements[T, Trait]() -> bool` (`8`).
    implements = 8,
    /// `@size_of[T]() -> usize` (`9`).
    size_of = 9,
    /// `@type_info[T]() -> std::meta::TypeInfo` (`10`).
    type_info = 10,
    /// `@type_name[T]() -> str` (`11`).
    type_name = 11,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Static slot count reserved in `InternPool` (`0..63`, `DR-04` Section 2.1).
pub const STATIC_TYPE_SLOT_COUNT: u32 = TypeId.first_dynamic.toU32();

/// Maximum recursion depth for type resolution, unification, and expression checking (`AGENTS.md` §2).
pub const MAX_TYPE_DEPTH: u32 = 256;

/// High-bit tag in `TypeNode.rhs` marking a symbolic `[const N: usize]` array length (`[T; N]`).
pub const SYMBOLIC_ARRAY_LEN_FLAG: u32 = 0x8000_0000;

/// Canonical 32-bit `Wyhash` seed for `InternPool` structural hashing.
const TYPE_HASH_SEED: u64 = 0x517C_C1B7_2722_0A95;

/// $O(1)$ static lookup map of built-in compiler attributes skipped during user `@attribute_schema` checks.
const BUILTIN_ATTRIBUTE_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "align", {} },
    .{ "allow", {} },
    .{ "attribute_schema", {} },
    .{ "bench", {} },
    .{ "cold", {} },
    .{ "deprecated", {} },
    .{ "derive", {} },
    .{ "export", {} },
    .{ "extern", {} },
    .{ "from", {} },
    .{ "inline", {} },
    .{ "link_name", {} },
    .{ "local", {} },
    .{ "must_use", {} },
    .{ "noinline", {} },
    .{ "overload", {} },
    .{ "packed", {} },
    .{ "repr", {} },
    .{ "soa", {} },
    .{ "test", {} },
});

/// $O(1)$ static lookup map from `@snake_case` intrinsic identifier to `IntrinsicKind`.
pub const INTRINSIC_NAME_MAP = std.StaticStringMap(IntrinsicKind).initComptime(.{
    .{ "align_of", .align_of },
    .{ "compile_assert", .compile_assert },
    .{ "compile_error", .compile_error },
    .{ "default_init", .default_init },
    .{ "embed_bytes", .embed_bytes },
    .{ "field", .field },
    .{ "field_attr_lookup", .field_attr_lookup },
    .{ "has_field", .has_field },
    .{ "implements", .implements },
    .{ "size_of", .size_of },
    .{ "type_info", .type_info },
    .{ "type_name", .type_name },
});

/// $O(1)$ static lookup map of the 8 `std::meta` value-based reflection mirror type names (`DR-05` §3.3).
const REFLECTION_MIRROR_NAME_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "EnumInfo", {} },
    .{ "FieldInfo", {} },
    .{ "MetaId", {} },
    .{ "PrimKind", {} },
    .{ "StructInfo", {} },
    .{ "TypeInfo", {} },
    .{ "TypeKind", {} },
    .{ "VariantInfo", {} },
});

// -------------------------------------- INTERNALS --------------------------------------

comptime {
    // Enforce the `DR-04` Section 2.2 14-byte zero-padding SoA column footprint invariant:
    const soa_bytes_per_type_node = @sizeOf(TypeTag) + @sizeOf(TypeFlags) +
        @sizeOf(u32) + @sizeOf(u32) + @sizeOf(u32);
    std.debug.assert(soa_bytes_per_type_node == 14);
}

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

/// Computes a 32-bit structural hash for `(tag, flags, lhs, rhs, extra_slice)`.
fn computeStructuralTypeHash(
    tag: TypeTag,
    flags: TypeFlags,
    lhs: u32,
    rhs: u32,
    extra_slice: []const u32,
) u32 {
    var hasher = std.hash.Wyhash.init(TYPE_HASH_SEED);
    const header_bytes = [2]u8{ @intFromEnum(tag), @bitCast(flags) };
    hasher.update(&header_bytes);
    var pair_bytes: [8]u8 = undefined;
    std.mem.writeInt(u32, pair_bytes[0..4], lhs, .little);
    std.mem.writeInt(u32, pair_bytes[4..8], rhs, .little);
    hasher.update(&pair_bytes);
    for (extra_slice) |word| {
        var word_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &word_bytes, word, .little);
        hasher.update(&word_bytes);
    }
    const digest64 = hasher.final();
    return @truncate(digest64 ^ (digest64 >> 32));
}

/// Returns the default concrete primitive type for an unresolved `untyped_int_ty` or `untyped_float_ty` in `group_ty`.
fn defaultConcreteForGroup(group_ty: TypeId, is_int: bool) TypeId {
    if (group_ty.isBuiltinGroup()) {
        const mask = TypeGroupMask.forBuiltinGroup(group_ty);
        if (is_int) {
            if (TypeGroupMask.containsPrimitive(mask, .i32_ty)) return .i32_ty;
            if (TypeGroupMask.containsPrimitive(mask, .u32_ty)) return .u32_ty;
            if (TypeGroupMask.containsPrimitive(mask, .u8_ty)) return .u8_ty;
            if (TypeGroupMask.containsPrimitive(mask, .i64_ty)) return .i64_ty;
        } else {
            if (TypeGroupMask.containsPrimitive(mask, .f64_ty)) return .f64_ty;
            if (TypeGroupMask.containsPrimitive(mask, .f32_ty)) return .f32_ty;
        }
    }
    return if (is_int) .i32_ty else .f64_ty;
}

/// Returns the inclusive `[min_val, max_val]` 128-bit integer bounds of a primitive integer `TypeId`.
pub fn getPrimitiveIntBounds(prim_ty: TypeId) ?struct { min_val: i128, max_val: i128, bits: u16 } {
    return switch (prim_ty) {
        .i8_ty => .{ .min_val = std.math.minInt(i8), .max_val = std.math.maxInt(i8), .bits = 8 },
        .i16_ty => .{ .min_val = std.math.minInt(i16), .max_val = std.math.maxInt(i16), .bits = 16 },
        .i32_ty => .{ .min_val = std.math.minInt(i32), .max_val = std.math.maxInt(i32), .bits = 32 },
        .i64_ty, .isize_ty => .{ .min_val = std.math.minInt(i64), .max_val = std.math.maxInt(i64), .bits = 64 },
        .i128_ty => .{ .min_val = std.math.minInt(i128), .max_val = std.math.maxInt(i128), .bits = 128 },
        .u8_ty => .{ .min_val = 0, .max_val = std.math.maxInt(u8), .bits = 8 },
        .u16_ty => .{ .min_val = 0, .max_val = std.math.maxInt(u16), .bits = 16 },
        .u32_ty => .{ .min_val = 0, .max_val = std.math.maxInt(u32), .bits = 32 },
        .u64_ty, .usize_ty => .{ .min_val = 0, .max_val = std.math.maxInt(u64), .bits = 64 },
        .u128_ty => .{ .min_val = 0, .max_val = std.math.maxInt(i128), .bits = 128 },
        else => null,
    };
}

/// Returns the target-aware bit width of a primitive integer `TypeId` (`32` on `wasm32`, `64` on 64-bit for `usize`/`isize`).
pub fn getTargetPrimitiveIntBits(prim_ty: TypeId, target_layout: TargetLayout) ?u16 {
    if (prim_ty == .usize_ty or prim_ty == .isize_ty) {
        return @as(u16, target_layout.ptr_byte_size) * 8;
    }
    if (getPrimitiveIntBounds(prim_ty)) |bounds| {
        return bounds.bits;
    }
    return null;
}

/// Returns `true` if `arr_cst` is a repeat `[val; count]` array literal with a direct-child `;` separator.
pub fn hasShallowSemicolonInArrayCst(
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    arr_cst: CstNodeIndex,
) bool {
    if (arr_cst.isNone() or arr_cst.asInt() >= cst_arena.countNodes()) return false;
    const start_idx: usize = arr_cst.asInt();
    const rec = cst_arena.getNode(arr_cst);
    const end_idx: usize = @min(start_idx + @max(@as(usize, rec.subtree_size), 1), cst_arena.countNodes());
    var cur = start_idx + 1;
    while (cur < end_idx) {
        const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
        if (sub.subtree_size <= 1 and !sub.token.isNone() and
            sub.token.asInt() < token_buffer.countTokens() and
            token_buffer.getToken(sub.token).kind == .semi)
        {
            return true;
        }
        cur += @max(@as(usize, sub.subtree_size), 1);
    }
    return false;
}

/// Returns `true` if `tup_cst` has a direct-child `,` separator (distinguishing `(pat,)` from `(pat)`).
pub fn hasShallowCommaInTupleCst(
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    tup_cst: CstNodeIndex,
) bool {
    if (tup_cst.isNone() or tup_cst.asInt() >= cst_arena.countNodes()) return false;
    const start_idx: usize = tup_cst.asInt();
    const rec = cst_arena.getNode(tup_cst);
    const end_idx: usize = @min(start_idx + @max(@as(usize, rec.subtree_size), 1), cst_arena.countNodes());
    var cur = start_idx + 1;
    while (cur < end_idx) {
        const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
        if (sub.subtree_size <= 1 and !sub.token.isNone() and
            sub.token.asInt() < token_buffer.countTokens() and
            token_buffer.getToken(sub.token).kind == .comma)
        {
            return true;
        }
        cur += @max(@as(usize, sub.subtree_size), 1);
    }
    return false;
}

/// Returns the inner verbatim slice of a raw string literal (`r"…"` or `r#"…"#`), or `null` if standard `"…"`.
pub fn extractRawStringContent(lexeme: []const u8) ?[]const u8 {
    if (lexeme.len < 3 or lexeme[0] != 'r') return null;
    var hash_count: usize = 0;
    while (1 + hash_count < lexeme.len and lexeme[1 + hash_count] == '#') : (hash_count += 1) {}
    const prefix_len = 1 + hash_count + 1;
    const suffix_len = 1 + hash_count;
    if (prefix_len + suffix_len > lexeme.len) return null;
    if (lexeme[1 + hash_count] != '"' or lexeme[lexeme.len - suffix_len] != '"') return null;
    return lexeme[prefix_len .. lexeme.len - suffix_len];
}

/// Parses a single hexadecimal digit into `0..15`, or returns `null`.
fn parseHexNibble(hex_byte: u8) ?u8 {
    return switch (hex_byte) {
        '0'...'9' => hex_byte - '0',
        'a'...'f' => hex_byte - 'a' + 10,
        'A'...'F' => hex_byte - 'A' + 10,
        else => null,
    };
}

/// Decodes a character literal lexeme (`'a'`, `'\n'`, `'\x41'`, `'\u{1F600}'`) into its Unicode scalar value.
pub fn extractCharLiteralCodepoint(lexeme: []const u8) ?u21 {
    if (lexeme.len < 3 or lexeme[0] != '\'' or lexeme[lexeme.len - 1] != '\'') return null;
    const body = lexeme[1 .. lexeme.len - 1];
    if (body.len == 0) return null;
    if (body[0] != '\\') {
        const seq_len = std.unicode.utf8ByteSequenceLength(body[0]) catch return null;
        if (seq_len > body.len) return null;
        return std.unicode.utf8Decode(body[0..seq_len]) catch null;
    }
    if (body.len < 2) return null;
    return switch (body[1]) {
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        '0' => 0,
        '\\' => '\\',
        '\'' => '\'',
        '"' => '"',
        '{' => '{',
        '}' => '}',
        'x' => blk: {
            if (body.len < 4) break :blk null;
            const hi = parseHexNibble(body[2]) orelse break :blk null;
            const lo = parseHexNibble(body[3]) orelse break :blk null;
            break :blk @as(u21, (hi << 4) | lo);
        },
        'u' => blk: {
            if (body.len < 4 or body[2] != '{') break :blk null;
            const close_rel = std.mem.indexOfScalarPos(u8, body, 3, '}') orelse break :blk null;
            const hex_digits = body[3..close_rel];
            if (hex_digits.len == 0 or hex_digits.len > 6) break :blk null;
            var scalar_val: u32 = 0;
            for (hex_digits) |digit_byte| {
                const nib = parseHexNibble(digit_byte) orelse break :blk null;
                scalar_val = (scalar_val << 4) | nib;
            }
            if (scalar_val > 0x10FFFF or !std.unicode.utf8ValidCodepoint(@intCast(scalar_val))) break :blk null;
            break :blk @intCast(scalar_val);
        },
        else => @as(u21, body[1]),
    };
}

/// Unescapes a non-raw string literal segment (`\n`, `\r`, `\t`, `\0`, `\\`, `\"`, `\'`, `\{`, `\}`, `\xHH`, `\u{…}`).
pub fn decodeStandardStringSegment(allocator: std.mem.Allocator, raw_seg: []const u8) ![]u8 {
    var out_buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer out_buf.deinit(allocator);
    try out_buf.ensureTotalCapacity(allocator, raw_seg.len);

    var cursor: usize = 0;
    while (cursor < raw_seg.len) {
        if (raw_seg[cursor] == '\\' and cursor + 1 < raw_seg.len) {
            const esc = raw_seg[cursor + 1];
            switch (esc) {
                'n' => {
                    try out_buf.append(allocator, '\n');
                    cursor += 2;
                },
                'r' => {
                    try out_buf.append(allocator, '\r');
                    cursor += 2;
                },
                't' => {
                    try out_buf.append(allocator, '\t');
                    cursor += 2;
                },
                '0' => {
                    try out_buf.append(allocator, 0);
                    cursor += 2;
                },
                '\\', '"', '\'', '{', '}' => {
                    try out_buf.append(allocator, esc);
                    cursor += 2;
                },
                '\n' => {
                    cursor += 2;
                },
                '\r' => {
                    cursor += if (cursor + 2 < raw_seg.len and raw_seg[cursor + 2] == '\n') 3 else 2;
                },
                'x' => {
                    if (cursor + 3 < raw_seg.len) {
                        if (parseHexNibble(raw_seg[cursor + 2])) |hi| {
                            if (parseHexNibble(raw_seg[cursor + 3])) |lo| {
                                try out_buf.append(allocator, (hi << 4) | lo);
                                cursor += 4;
                                continue;
                            }
                        }
                    }
                    try out_buf.append(allocator, esc);
                    cursor += 2;
                },
                'u' => {
                    if (cursor + 3 < raw_seg.len and raw_seg[cursor + 2] == '{') {
                        if (std.mem.indexOfScalarPos(u8, raw_seg, cursor + 3, '}')) |close_pos| {
                            const hex_digits = raw_seg[cursor + 3 .. close_pos];
                            if (hex_digits.len > 0 and hex_digits.len <= 6) {
                                var scalar_val: u32 = 0;
                                var is_valid_hex = true;
                                for (hex_digits) |digit_byte| {
                                    if (parseHexNibble(digit_byte)) |nib| {
                                        scalar_val = (scalar_val << 4) | nib;
                                    } else {
                                        is_valid_hex = false;
                                        break;
                                    }
                                }
                                if (is_valid_hex and scalar_val <= 0x10FFFF and
                                    std.unicode.utf8ValidCodepoint(@intCast(scalar_val)))
                                {
                                    var utf8_bytes: [4]u8 = undefined;
                                    const encoded_len = std.unicode.utf8Encode(
                                        @intCast(scalar_val),
                                        &utf8_bytes,
                                    ) catch 0;
                                    try out_buf.appendSlice(allocator, utf8_bytes[0..encoded_len]);
                                    cursor = close_pos + 1;
                                    continue;
                                }
                            }
                        }
                    }
                    try out_buf.append(allocator, esc);
                    cursor += 2;
                },
                else => {
                    try out_buf.append(allocator, esc);
                    cursor += 2;
                },
            }
            continue;
        }
        if ((raw_seg[cursor] == '{' or raw_seg[cursor] == '}') and
            cursor + 1 < raw_seg.len and raw_seg[cursor + 1] == raw_seg[cursor])
        {
            try out_buf.append(allocator, raw_seg[cursor]);
            cursor += 2;
            continue;
        }
        try out_buf.append(allocator, raw_seg[cursor]);
        cursor += 1;
    }
    return out_buf.toOwnedSlice(allocator);
}

/// Byte offsets of an unescaped `{expr}` interpolation segment within a standard string body.
pub const InterpolationSegment = struct {
    /// Byte offset of the `{` delimiter inside `body`.
    open_brace: usize,
    /// Start byte offset of `expr` (`open_brace + 1`).
    expr_start: usize,
    /// End byte offset of `expr` (position of matching `}`).
    expr_end: usize,
    /// Byte offset immediately following matching `}`.
    after_close: usize,
};

/// Advances past a backslash escape starting at `slash_pos` (including braced `\u{…}`).
fn advancePastStringEscape(body: []const u8, slash_pos: usize) usize {
    if (slash_pos + 1 >= body.len) return body.len;
    if (body[slash_pos + 1] == 'u' and slash_pos + 2 < body.len and body[slash_pos + 2] == '{') {
        var scan_idx = slash_pos + 3;
        while (scan_idx < body.len and body[scan_idx] != '}') : (scan_idx += 1) {}
        return if (scan_idx < body.len) scan_idx + 1 else body.len;
    }
    return slash_pos + 2;
}

/// Scans `body[start_pos..]` (inside `"…"`) for the next unescaped `{expr}` segment, respecting nested quotes/comments.
pub fn scanNextInterpolationSegment(body: []const u8, start_pos: usize) ?InterpolationSegment {
    var cursor = start_pos;
    while (cursor < body.len) {
        if (body[cursor] == '\\') {
            cursor = advancePastStringEscape(body, cursor);
            continue;
        }
        if ((body[cursor] == '{' or body[cursor] == '}') and
            cursor + 1 < body.len and body[cursor + 1] == body[cursor])
        {
            cursor += 2;
            continue;
        }
        if (body[cursor] != '{') {
            cursor += 1;
            continue;
        }
        const open_brace = cursor;
        const expr_start = cursor + 1;
        cursor += 1;
        var brace_depth: u32 = 1;
        while (cursor < body.len and brace_depth > 0) {
            const cur_byte = body[cursor];
            if (cur_byte == '{') {
                brace_depth += 1;
                cursor += 1;
            } else if (cur_byte == '}') {
                brace_depth -= 1;
                if (brace_depth == 0) {
                    return .{
                        .open_brace = open_brace,
                        .expr_start = expr_start,
                        .expr_end = cursor,
                        .after_close = cursor + 1,
                    };
                }
                cursor += 1;
            } else if (cur_byte == '"') {
                cursor += 1;
                var inner_interp_depth: u32 = 0;
                while (cursor < body.len) {
                    if (inner_interp_depth == 0) {
                        if (body[cursor] == '\\') {
                            cursor = advancePastStringEscape(body, cursor);
                            continue;
                        }
                        if (body[cursor] == '"') {
                            cursor += 1;
                            break;
                        }
                        if (body[cursor] == '{') {
                            inner_interp_depth = 1;
                        }
                        cursor += 1;
                    } else {
                        if (body[cursor] == '{') inner_interp_depth += 1;
                        if (body[cursor] == '}') inner_interp_depth -= 1;
                        cursor += 1;
                    }
                }
            } else if (cur_byte == 'r' and
                (cursor == expr_start or (!std.ascii.isAlphanumeric(body[cursor - 1]) and body[cursor - 1] != '_')) and
                cursor + 1 < body.len and (body[cursor + 1] == '"' or body[cursor + 1] == '#'))
            {
                cursor += 1;
                var raw_hashes: usize = 0;
                while (cursor < body.len and body[cursor] == '#') : (cursor += 1) {
                    raw_hashes += 1;
                }
                if (cursor < body.len and body[cursor] == '"') {
                    cursor += 1;
                    while (cursor < body.len) {
                        if (body[cursor] == '"') {
                            cursor += 1;
                            var close_hashes: usize = 0;
                            while (close_hashes < raw_hashes and cursor < body.len and body[cursor] == '#') : (cursor += 1) {
                                close_hashes += 1;
                            }
                            if (close_hashes == raw_hashes) break;
                        } else {
                            cursor += 1;
                        }
                    }
                }
            } else if (cur_byte == '\'') {
                cursor += 1;
                while (cursor < body.len and body[cursor] != '\'') {
                    cursor += if (body[cursor] == '\\' and cursor + 1 < body.len) 2 else 1;
                }
                if (cursor < body.len) cursor += 1;
            } else if (cur_byte == '/' and cursor + 1 < body.len and body[cursor + 1] == '/') {
                cursor += 2;
                while (cursor < body.len and body[cursor] != '\n') : (cursor += 1) {}
            } else if (cur_byte == '/' and cursor + 1 < body.len and body[cursor + 1] == '*') {
                cursor += 2;
                var comment_depth: u32 = 1;
                while (cursor + 1 < body.len and comment_depth > 0) {
                    if (body[cursor] == '/' and body[cursor + 1] == '*') {
                        comment_depth += 1;
                        cursor += 2;
                    } else if (body[cursor] == '*' and body[cursor + 1] == '/') {
                        comment_depth -= 1;
                        cursor += 2;
                    } else {
                        cursor += 1;
                    }
                }
            } else {
                cursor += 1;
            }
        }
        return null;
    }
    return null;
}

/// Parses an integer literal lexeme (handling `0x`, `0b`, `0o`, `_`, and type suffixes) into `i128` + optional suffix `TypeId`.
pub fn extractIntLiteralValue(raw_lexeme: []const u8) ?struct {
    value: i128,
    magnitude: u128 = 0,
    is_above_i128_max: bool = false,
    suffix_ty: ?TypeId,
} {
    if (raw_lexeme.len == 0) return null;
    var is_negative = false;
    var slice = raw_lexeme;
    if (slice[0] == '-') {
        is_negative = true;
        slice = slice[1..];
    } else if (slice[0] == '+') {
        slice = slice[1..];
    }
    if (slice.len == 0) return null;

    var base: u8 = 10;
    if (slice.len >= 2 and slice[0] == '0') {
        if (slice[1] == 'x' or slice[1] == 'X') {
            base = 16;
            slice = slice[2..];
        } else if (slice[1] == 'b' or slice[1] == 'B') {
            base = 2;
            slice = slice[2..];
        } else if (slice[1] == 'o' or slice[1] == 'O') {
            base = 8;
            slice = slice[2..];
        }
    }

    // Check for trailing primitive integer suffix (`i8`..`usize`):
    var suffix_ty: ?TypeId = null;
    const suffixes = [_]struct { text: []const u8, ty: TypeId }{
        .{ .text = "isize", .ty = .isize_ty },
        .{ .text = "usize", .ty = .usize_ty },
        .{ .text = "i128", .ty = .i128_ty },
        .{ .text = "u128", .ty = .u128_ty },
        .{ .text = "i64", .ty = .i64_ty },
        .{ .text = "u64", .ty = .u64_ty },
        .{ .text = "i32", .ty = .i32_ty },
        .{ .text = "u32", .ty = .u32_ty },
        .{ .text = "i16", .ty = .i16_ty },
        .{ .text = "u16", .ty = .u16_ty },
        .{ .text = "i8", .ty = .i8_ty },
        .{ .text = "u8", .ty = .u8_ty },
    };
    for (suffixes) |suf| {
        if (slice.len > suf.text.len and std.mem.endsWith(u8, slice, suf.text)) {
            if (base == 16 and (suf.text[0] == 'a' or suf.text[0] == 'b' or suf.text[0] == 'c' or
                suf.text[0] == 'd' or suf.text[0] == 'e' or suf.text[0] == 'f'))
            {
                continue;
            }
            suffix_ty = suf.ty;
            slice = slice[0 .. slice.len - suf.text.len];
            if (slice.len > 0 and slice[slice.len - 1] == '_') {
                slice = slice[0 .. slice.len - 1];
            }
            break;
        }
    }

    var magnitude: u128 = 0;
    var has_digits = false;
    for (slice) |ch| {
        if (ch == '_') continue;
        const digit: u8 = switch (ch) {
            '0'...'9' => ch - '0',
            'a'...'f' => ch - 'a' + 10,
            'A'...'F' => ch - 'A' + 10,
            else => return null,
        };
        if (digit >= base) return null;
        has_digits = true;
        magnitude = std.math.mul(u128, magnitude, base) catch return null;
        magnitude = std.math.add(u128, magnitude, digit) catch return null;
    }
    if (!has_digits) return null;

    if (is_negative) {
        const min_abs: u128 = @as(u128, @intCast(std.math.maxInt(i128))) + 1;
        if (magnitude > min_abs) return null;
        if (magnitude == min_abs) {
            return .{
                .value = std.math.minInt(i128),
                .magnitude = magnitude,
                .is_above_i128_max = false,
                .suffix_ty = suffix_ty,
            };
        }
        return .{
            .value = -@as(i128, @intCast(magnitude)),
            .magnitude = magnitude,
            .is_above_i128_max = false,
            .suffix_ty = suffix_ty,
        };
    }
    if (magnitude > @as(u128, @intCast(std.math.maxInt(i128)))) {
        return .{
            .value = std.math.maxInt(i128),
            .magnitude = magnitude,
            .is_above_i128_max = true,
            .suffix_ty = suffix_ty,
        };
    }
    return .{
        .value = @intCast(magnitude),
        .magnitude = magnitude,
        .is_above_i128_max = false,
        .suffix_ty = suffix_ty,
    };
}

/// Stack-backed slice writer used by `InternPool.formatType` with zero heap allocations.
const SliceBufWriter = struct {
    buf: []u8,
    pos: usize = 0,

    /// Appends `bytes` into `self.buf`, truncating if capacity is exceeded.
    fn writeAll(self: *SliceBufWriter, bytes: []const u8) void {
        if (self.pos >= self.buf.len) return;
        const avail = self.buf.len - self.pos;
        const n = @min(avail, bytes.len);
        @memcpy(self.buf[self.pos .. self.pos + n], bytes[0..n]);
        self.pos += n;
    }

    /// Formats `args` with `fmt_str` into the remaining capacity of `self.buf`.
    fn print(self: *SliceBufWriter, comptime fmt_str: []const u8, args: anytype) void {
        if (self.pos >= self.buf.len) return;
        const written = std.fmt.bufPrint(self.buf[self.pos..], fmt_str, args) catch {
            self.pos = self.buf.len;
            return;
        };
        self.pos += written.len;
    }
};

/// Packs `(src_err_ty, dst_err_ty)` into a 64-bit key for $O(1)$ `FromError` conversion lookup.
inline fn packFromErrorPair(src_err_ty: TypeId, dst_err_ty: TypeId) u64 {
    return (@as(u64, src_err_ty.toU32()) << 32) | @as(u64, dst_err_ty.toU32());
}

/// Packs `(target_ty, trait_sym_idx)` into a 64-bit key for $O(1)$ `@implements` / `@derive` lookup.
pub inline fn packTraitImplPair(target_ty: TypeId, trait_sym_idx: SymbolIndex) u64 {
    return (@as(u64, target_ty.toU32()) << 32) | @as(u64, trait_sym_idx.asInt());
}

/// Converts a `snake_case` identifier into `PascalCase` inside `out_buf` with zero heap allocations.
fn toPascalCase(snake_name: []const u8, out_buf: []u8) []const u8 {
    var write_pos: usize = 0;
    var is_cap_next = true;
    for (snake_name) |byte_val| {
        if (byte_val == '_') {
            is_cap_next = true;
            continue;
        }
        if (write_pos >= out_buf.len) break;
        out_buf[write_pos] = if (is_cap_next and byte_val >= 'a' and byte_val <= 'z')
            byte_val - ('a' - 'A')
        else
            byte_val;
        write_pos += 1;
        is_cap_next = false;
    }
    return out_buf[0..write_pos];
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------ Canonical `InternPool` (`TypeArena`) ------------

/// Canonical Structure-of-Arrays (SoA) type interner with static `0..63` pre-population (`DR-04` Section 2).
pub const InternPool = struct {
    /// Backing allocator for the SoA columns, `extra` array, and deduplication buckets.
    allocator: std.mem.Allocator,
    /// 14-byte zero-padding SoA `TypeNode` table indexed by `TypeId.toU32()`.
    nodes: std.MultiArrayList(TypeNode) = .empty,
    /// Flat `u32` payload trail storing tuple elements, function parameter lists, and refinement bounds.
    extra: std.ArrayListUnmanaged(u32) = .empty,
    /// Map from 32-bit structural hash to candidate `TypeId` bucket for $O(1)$ deduplication.
    dedup_buckets: std.AutoHashMapUnmanaged(u32, std.ArrayListUnmanaged(TypeId)) = .empty,

    /// Initializes a new `InternPool` and pre-populates static `TypeId` slots `0..63`.
    pub fn init(allocator: std.mem.Allocator) !InternPool {
        var self = InternPool{ .allocator = allocator };
        errdefer self.deinit();
        try self.populateStaticSlots();
        return self;
    }

    /// Releases all SoA columns, `extra` payloads, and deduplication buckets.
    pub fn deinit(self: *InternPool) void {
        var bucket_iter = self.dedup_buckets.valueIterator();
        while (bucket_iter.next()) |bucket_ptr| {
            bucket_ptr.deinit(self.allocator);
        }
        self.dedup_buckets.deinit(self.allocator);
        self.extra.deinit(self.allocator);
        self.nodes.deinit(self.allocator);
        self.* = undefined;
    }

    /// Resets dynamic types (`>= 64`) while preserving static slots `0..63` and allocated capacity.
    pub fn resetDynamic(self: *InternPool) !void {
        var bucket_iter = self.dedup_buckets.valueIterator();
        while (bucket_iter.next()) |bucket_ptr| {
            bucket_ptr.clearRetainingCapacity();
        }
        self.extra.clearRetainingCapacity();
        if (self.nodes.len > STATIC_TYPE_SLOT_COUNT) {
            self.nodes.shrinkRetainingCapacity(STATIC_TYPE_SLOT_COUNT);
        } else if (self.nodes.len < STATIC_TYPE_SLOT_COUNT) {
            self.nodes.shrinkRetainingCapacity(0);
            try self.populateStaticSlots();
        }
    }

    /// Pre-populates static slots `0..63` (`DR-04` Section 2.1).
    fn populateStaticSlots(self: *InternPool) !void {
        try self.nodes.ensureTotalCapacity(self.allocator, STATIC_TYPE_SLOT_COUNT);
        var slot_idx: u32 = 0;
        while (slot_idx < STATIC_TYPE_SLOT_COUNT) : (slot_idx += 1) {
            const tid = TypeId.fromInt(slot_idx);
            if (slot_idx <= 18) {
                const flags: TypeFlags = .{ .is_copy = true, .is_sized = true };
                self.nodes.appendAssumeCapacity(.{
                    .tag = .primitive,
                    .flags = flags,
                    .hash = computeStructuralTypeHash(.primitive, flags, slot_idx, 0, &.{}),
                    .lhs = slot_idx,
                    .rhs = 0,
                });
            } else if (slot_idx >= 19 and slot_idx <= 21) {
                const flags: TypeFlags = .{
                    .is_copy = true,
                    .has_error = (tid == .err_ty),
                    .is_sized = true,
                };
                self.nodes.appendAssumeCapacity(.{
                    .tag = .primitive,
                    .flags = flags,
                    .hash = computeStructuralTypeHash(.primitive, flags, slot_idx, 0, &.{}),
                    .lhs = slot_idx,
                    .rhs = 0,
                });
            } else if (slot_idx >= 32 and slot_idx <= 42) {
                const mask = TypeGroupMask.forBuiltinGroup(tid);
                const flags: TypeFlags = .{ .is_copy = true, .is_sized = true };
                self.nodes.appendAssumeCapacity(.{
                    .tag = .builtin_group,
                    .flags = flags,
                    .hash = computeStructuralTypeHash(.builtin_group, flags, mask, slot_idx, &.{}),
                    .lhs = mask,
                    .rhs = slot_idx,
                });
            } else {
                self.nodes.appendAssumeCapacity(.{
                    .tag = .primitive,
                    .flags = .{ .has_error = true },
                    .hash = slot_idx,
                    .lhs = slot_idx,
                    .rhs = 0,
                });
            }
        }
    }

    /// Retrieves the `TypeNode` for `type_id` in $O(1)$ time.
    pub inline fn getNode(self: *const InternPool, type_id: TypeId) TypeNode {
        const idx = type_id.toU32();
        if (idx >= self.nodes.len) return self.nodes.get(TypeId.err_ty.toU32());
        return self.nodes.get(idx);
    }

    /// Retrieves the `TypeTag` for `type_id` in $O(1)$ time.
    pub inline fn getTag(self: *const InternPool, type_id: TypeId) TypeTag {
        const idx = type_id.toU32();
        if (idx >= self.nodes.len) return .primitive;
        return self.nodes.items(.tag)[idx];
    }

    /// Retrieves the `TypeFlags` for `type_id` in $O(1)$ time.
    pub inline fn getFlags(self: *const InternPool, type_id: TypeId) TypeFlags {
        const idx = type_id.toU32();
        if (idx >= self.nodes.len) return .{ .has_error = true };
        return self.nodes.items(.flags)[idx];
    }

    /// Retrieves the canonical 32-bit structural hash of `type_id` (used for position-independent query hashing).
    pub inline fn getHash(self: *const InternPool, type_id: TypeId) u32 {
        const idx = type_id.toU32();
        if (idx >= self.nodes.len) return 0xDEAD_BEEF;
        return self.nodes.items(.hash)[idx];
    }

    /// Returns the total number of `TypeNode` slots in the pool.
    pub inline fn countTypes(self: *const InternPool) usize {
        return self.nodes.len;
    }

    /// Interns a fixed-arity `TypeNode` (`tag`, `flags`, `lhs`, `rhs`) with $O(1)$ structural deduplication.
    pub fn internSimple(
        self: *InternPool,
        tag: TypeTag,
        flags: TypeFlags,
        lhs: u32,
        rhs: u32,
    ) !TypeId {
        const struct_hash = computeStructuralTypeHash(tag, flags, lhs, rhs, &.{});
        const gop = try self.dedup_buckets.getOrPut(self.allocator, struct_hash);
        if (!gop.found_existing) {
            gop.value_ptr.* = .empty;
        } else {
            for (gop.value_ptr.items) |cand_id| {
                const cand = self.getNode(cand_id);
                if (cand.tag == tag and
                    @as(u8, @bitCast(cand.flags)) == @as(u8, @bitCast(flags)) and
                    cand.lhs == lhs and cand.rhs == rhs)
                {
                    return cand_id;
                }
            }
        }

        const new_id = TypeId.fromInt(@intCast(self.nodes.len));
        try self.nodes.append(self.allocator, .{
            .tag = tag,
            .flags = flags,
            .hash = struct_hash,
            .lhs = lhs,
            .rhs = rhs,
        });
        try gop.value_ptr.append(self.allocator, new_id);
        return new_id;
    }

    /// Interns a variable-length `TypeNode` whose `lhs` indexes `extra_slice` in `self.extra`.
    pub fn internExtra(
        self: *InternPool,
        tag: TypeTag,
        flags: TypeFlags,
        rhs: u32,
        extra_slice: []const u32,
    ) !TypeId {
        const len_u32: u32 = @intCast(extra_slice.len);
        const struct_hash = computeStructuralTypeHash(tag, flags, len_u32, rhs, extra_slice);
        const gop = try self.dedup_buckets.getOrPut(self.allocator, struct_hash);
        if (!gop.found_existing) {
            gop.value_ptr.* = .empty;
        } else {
            for (gop.value_ptr.items) |cand_id| {
                const cand = self.getNode(cand_id);
                if (cand.tag == tag and
                    @as(u8, @bitCast(cand.flags)) == @as(u8, @bitCast(flags)) and
                    cand.rhs == rhs and
                    cand.lhs + extra_slice.len <= self.extra.items.len)
                {
                    const existing_slice = self.extra.items[cand.lhs .. cand.lhs + extra_slice.len];
                    if (std.mem.eql(u32, existing_slice, extra_slice)) {
                        return cand_id;
                    }
                }
            }
        }

        const extra_start: u32 = @intCast(self.extra.items.len);
        try self.extra.appendSlice(self.allocator, extra_slice);

        const new_id = TypeId.fromInt(@intCast(self.nodes.len));
        try self.nodes.append(self.allocator, .{
            .tag = tag,
            .flags = flags,
            .hash = struct_hash,
            .lhs = extra_start,
            .rhs = rhs,
        });
        try gop.value_ptr.append(self.allocator, new_id);
        return new_id;
    }

    // --------------- Specialized Type Constructors ----------------

    /// Interns `T?` (`optional_ty`).
    pub fn internOptional(self: *InternPool, payload_ty: TypeId) !TypeId {
        if (payload_ty.isError()) return .err_ty;
        const inner_flags = self.getFlags(payload_ty);
        return self.internSimple(.optional_ty, .{
            .is_copy = inner_flags.is_copy,
            .has_type_vars = inner_flags.has_type_vars,
            .has_regions = inner_flags.has_regions,
            .is_sized = true,
        }, payload_ty.toU32(), 0);
    }

    /// Interns `Result[T, E]` (`result_ty`, always marked `is_must_use = true` per `DR-07` Section 2.7).
    pub fn internResult(self: *InternPool, ok_ty: TypeId, err_ty_arg: TypeId) !TypeId {
        if (ok_ty.isError() or err_ty_arg.isError()) return .err_ty;
        const ok_flags = self.getFlags(ok_ty);
        const err_flags = self.getFlags(err_ty_arg);
        return self.internSimple(.result_ty, .{
            .is_copy = ok_flags.is_copy and err_flags.is_copy,
            .has_type_vars = ok_flags.has_type_vars or err_flags.has_type_vars,
            .has_regions = ok_flags.has_regions or err_flags.has_regions,
            .is_must_use = true,
            .is_sized = true,
        }, ok_ty.toU32(), err_ty_arg.toU32());
    }

    /// Interns `[T]` or `#soa [T]` (`slice_ty` / `soa_slice_ty`).
    pub fn internSlice(self: *InternPool, elem_ty: TypeId, is_soa: bool) !TypeId {
        if (elem_ty.isError()) return .err_ty;
        const elem_flags = self.getFlags(elem_ty);
        return self.internSimple(if (is_soa) .soa_slice_ty else .slice_ty, .{
            .is_copy = true,
            .has_type_vars = elem_flags.has_type_vars,
            .has_regions = true,
            .is_sized = true,
            .is_soa = is_soa,
        }, elem_ty.toU32(), 0);
    }

    /// Interns `[T; N]` or `#soa [T; N]` (`array_ty` / `soa_array_ty`).
    pub fn internArray(self: *InternPool, elem_ty: TypeId, array_len: u32, is_soa: bool) !TypeId {
        if (elem_ty.isError()) return .err_ty;
        const elem_flags = self.getFlags(elem_ty);
        return self.internSimple(if (is_soa) .soa_array_ty else .array_ty, .{
            .is_copy = elem_flags.is_copy,
            .has_type_vars = elem_flags.has_type_vars,
            .has_regions = elem_flags.has_regions,
            .is_sized = true,
            .is_soa = is_soa,
        }, elem_ty.toU32(), array_len);
    }

    /// Interns a symbolic generic `[T; N]` or `#soa [T; N]` array parameterized by `const_param_sym_id`.
    pub fn internSymbolicArray(
        self: *InternPool,
        elem_ty: TypeId,
        const_param_sym_id: SymbolId,
        is_soa: bool,
    ) !TypeId {
        if (elem_ty.isError()) return .err_ty;
        const elem_flags = self.getFlags(elem_ty);
        return self.internSimple(if (is_soa) .soa_array_ty else .array_ty, .{
            .is_copy = elem_flags.is_copy,
            .has_type_vars = true,
            .has_regions = elem_flags.has_regions,
            .is_sized = false,
            .is_soa = is_soa,
        }, elem_ty.toU32(), SYMBOLIC_ARRAY_LEN_FLAG | (const_param_sym_id.asInt() & ~SYMBOLIC_ARRAY_LEN_FLAG));
    }

    /// Interns `&T` or `&mut T` (`ref_ty` / `mut_ref_ty`).
    pub fn internRef(self: *InternPool, inner_ty: TypeId, is_mut: bool) !TypeId {
        if (inner_ty.isError()) return .err_ty;
        const inner_flags = self.getFlags(inner_ty);
        return self.internSimple(if (is_mut) .mut_ref_ty else .ref_ty, .{
            .is_copy = !is_mut,
            .has_type_vars = inner_flags.has_type_vars,
            .has_regions = true,
            .is_sized = true,
        }, inner_ty.toU32(), if (is_mut) 1 else 0);
    }

    /// Interns `*T` or `*mut T` (`raw_ptr_ty`).
    pub fn internRawPtr(self: *InternPool, inner_ty: TypeId, is_mut: bool) !TypeId {
        if (inner_ty.isError()) return .err_ty;
        const inner_flags = self.getFlags(inner_ty);
        return self.internSimple(.raw_ptr_ty, .{
            .is_copy = true,
            .has_type_vars = inner_flags.has_type_vars,
            .is_sized = true,
        }, inner_ty.toU32(), if (is_mut) 1 else 0);
    }

    /// Interns `~T` (`tilde_approx`).
    pub fn internTildeApprox(self: *InternPool, target_ty: TypeId) !TypeId {
        if (target_ty.isError()) return .err_ty;
        const inner_flags = self.getFlags(target_ty);
        return self.internSimple(.tilde_approx, .{
            .is_copy = inner_flags.is_copy,
            .has_type_vars = true,
            .is_sized = true,
        }, target_ty.toU32(), 0);
    }

    /// Interns `(T1, T2, …)` (`tuple_ty`; `()` returns `.unit_ty`).
    pub fn internTuple(self: *InternPool, elem_types: []const TypeId) !TypeId {
        if (elem_types.len == 0) return .unit_ty;
        var is_copy = true;
        var has_vars = false;
        var has_regs = false;
        const raw_words = try self.allocator.alloc(u32, elem_types.len);
        defer self.allocator.free(raw_words);

        for (elem_types, 0..) |elem_ty, i| {
            if (elem_ty.isError()) return .err_ty;
            const fl = self.getFlags(elem_ty);
            if (!fl.is_copy) is_copy = false;
            if (fl.has_type_vars) has_vars = true;
            if (fl.has_regions) has_regs = true;
            raw_words[i] = elem_ty.toU32();
        }
        return self.internExtra(.tuple_ty, .{
            .is_copy = is_copy,
            .has_type_vars = has_vars,
            .has_regions = has_regs,
            .is_sized = true,
        }, @intCast(elem_types.len), raw_words);
    }

    /// Interns a nominal `struct`, `enum`, `union`, `bit_field`, or `trait` type.
    pub fn internNominal(
        self: *InternPool,
        tag: TypeTag,
        lhs_id: u32,
        sym_idx: SymbolIndex,
        is_copy: bool,
        is_must_use: bool,
        is_soa: bool,
    ) !TypeId {
        return self.internSimple(tag, .{
            .is_copy = is_copy,
            .is_must_use = is_must_use,
            .is_sized = (tag != .trait_ty),
            .is_soa = is_soa,
        }, lhs_id, sym_idx.asInt());
    }

    /// Interns a `type New = distinct Base;` type (`distinct_ty`).
    pub fn internDistinct(
        self: *InternPool,
        base_ty: TypeId,
        sym_idx: SymbolIndex,
    ) !TypeId {
        if (base_ty.isError()) return .err_ty;
        const base_flags = self.getFlags(base_ty);
        return self.internSimple(.distinct_ty, .{
            .is_copy = base_flags.is_copy,
            .has_regions = base_flags.has_regions,
            .is_must_use = base_flags.is_must_use,
            .is_sized = true,
        }, base_ty.toU32(), sym_idx.asInt());
    }

    /// Interns a range refinement type `type R = Base is min_val..=max_val;` (`refined_ty`).
    pub fn internRefined(
        self: *InternPool,
        base_ty: TypeId,
        sym_idx: SymbolIndex,
        min_val: i128,
        max_val: i128,
    ) !TypeId {
        if (base_ty.isError()) return .err_ty;
        const base_flags = self.getFlags(base_ty);
        const min_u: u128 = @bitCast(min_val);
        const max_u: u128 = @bitCast(max_val);
        const payload = [6]u32{
            base_ty.toU32(),
            sym_idx.asInt(),
            @truncate(min_u),
            @truncate(min_u >> 32),
            @truncate(max_u),
            @truncate(max_u >> 32),
        };
        // Also store upper 64 bits so full 128-bit bounds are preserved losslessly:
        const full_payload = [10]u32{
            payload[0],
            payload[1],
            @truncate(min_u),
            @truncate(min_u >> 32),
            @truncate(min_u >> 64),
            @truncate(min_u >> 96),
            @truncate(max_u),
            @truncate(max_u >> 32),
            @truncate(max_u >> 64),
            @truncate(max_u >> 96),
        };
        return self.internExtra(.refined_ty, .{
            .is_copy = base_flags.is_copy,
            .is_sized = true,
        }, base_ty.toU32(), &full_payload);
    }

    /// Decodes the `RefinementBounds` of a `.refined_ty` node.
    pub fn getRefinementBounds(self: *const InternPool, refined_ty: TypeId) ?RefinementBounds {
        const node = self.getNode(refined_ty);
        if (node.tag != .refined_ty or node.lhs + 10 > self.extra.items.len) return null;
        const words = self.extra.items[node.lhs .. node.lhs + 10];
        const min_u: u128 = (@as(u128, words[2])) |
            (@as(u128, words[3]) << 32) |
            (@as(u128, words[4]) << 64) |
            (@as(u128, words[5]) << 96);
        const max_u: u128 = (@as(u128, words[6])) |
            (@as(u128, words[7]) << 32) |
            (@as(u128, words[8]) << 64) |
            (@as(u128, words[9]) << 96);
        return .{
            .base_ty = TypeId.fromInt(words[0]),
            .sym_idx = SymbolIndex.fromInt(words[1]),
            .min_val = @bitCast(min_u),
            .max_val = @bitCast(max_u),
        };
    }

    /// Interns a user-defined Constrained Type Group (`type G = A | ~B`).
    pub fn internUserGroup(
        self: *InternPool,
        sym_idx: SymbolIndex,
        prim_mask: u32,
        tilde_prim_mask: u32,
        exact_members: []const u32,
        tilde_members: []const u32,
    ) !TypeId {
        var extra_words: std.ArrayListUnmanaged(u32) = .empty;
        defer extra_words.deinit(self.allocator);
        try extra_words.append(self.allocator, sym_idx.asInt());
        try extra_words.append(self.allocator, prim_mask);
        try extra_words.append(self.allocator, tilde_prim_mask);
        try extra_words.append(self.allocator, @intCast(exact_members.len));
        try extra_words.append(self.allocator, @intCast(tilde_members.len));
        try extra_words.appendSlice(self.allocator, exact_members);
        try extra_words.appendSlice(self.allocator, tilde_members);

        return self.internExtra(.user_group, .{
            .is_copy = true,
            .is_sized = true,
        }, sym_idx.asInt(), extra_words.items);
    }

    /// Decodes a `.user_group` `TypeId` into its `UserTypeGroupView`.
    pub fn getUserGroupView(self: *const InternPool, group_ty: TypeId) ?UserTypeGroupView {
        const node = self.getNode(group_ty);
        if (node.tag != .user_group or node.lhs + 5 > self.extra.items.len) return null;
        const header = self.extra.items[node.lhs .. node.lhs + 5];
        const exact_len: usize = header[3];
        const tilde_len: usize = header[4];
        const exact_start: usize = node.lhs + 5;
        const tilde_start: usize = exact_start + exact_len;
        if (tilde_start + tilde_len > self.extra.items.len) return null;
        return .{
            .sym_idx = SymbolIndex.fromInt(header[0]),
            .prim_mask = header[1],
            .tilde_prim_mask = header[2],
            .exact_members = self.extra.items[exact_start .. exact_start + exact_len],
            .tilde_members = self.extra.items[tilde_start .. tilde_start + tilde_len],
        };
    }

    /// Interns a Bind-Once Type Group variable (`x: Number, y: Number`, `DR-04` Section 1.3).
    pub fn internBindOnceVar(self: *InternPool, group_ty: TypeId, name_sym: SymbolId) !TypeId {
        return self.internSimple(.bind_once_group_var, .{
            .is_copy = true,
            .has_type_vars = true,
            .is_sized = true,
        }, group_ty.toU32(), name_sym.asInt());
    }

    /// Interns a Bind-Many `any Group` variable (`x: any Number`, `DR-04` Section 1.3).
    pub fn internBindManyVar(self: *InternPool, group_ty: TypeId, ordinal: u32) !TypeId {
        return self.internSimple(.bind_many_any_var, .{
            .is_copy = true,
            .has_type_vars = true,
            .is_sized = true,
        }, group_ty.toU32(), ordinal);
    }

    /// Interns a generic type parameter (`[T: Bound]`).
    pub fn internTypeParam(self: *InternPool, bound_ty: TypeId, name_sym: SymbolId) !TypeId {
        return self.internSimple(.type_param, .{
            .is_copy = true,
            .has_type_vars = true,
            .is_sized = true,
        }, bound_ty.toU32(), name_sym.asInt());
    }

    /// Interns a function or closure signature (`fn(P…) -> R`).
    pub fn internFn(
        self: *InternPool,
        tag: TypeTag,
        param_types: []const TypeId,
        param_modes: []const ParamMode,
        ret_ty: TypeId,
        is_must_use: bool,
    ) !TypeId {
        var has_vars = self.getFlags(ret_ty).has_type_vars;
        var extra_words: std.ArrayListUnmanaged(u32) = .empty;
        defer extra_words.deinit(self.allocator);

        const arity: u32 = @intCast(param_types.len);
        try extra_words.append(self.allocator, arity);
        for (param_types) |pty| {
            if (self.getFlags(pty).has_type_vars) has_vars = true;
            try extra_words.append(self.allocator, pty.toU32());
        }
        for (0..param_types.len) |i| {
            const mode: ParamMode = if (i < param_modes.len) param_modes[i] else .let_mode;
            try extra_words.append(self.allocator, @intFromEnum(mode));
        }

        return self.internExtra(tag, .{
            .is_copy = (tag == .fn_ty),
            .has_type_vars = has_vars,
            .is_must_use = is_must_use,
            .is_sized = true,
        }, ret_ty.toU32(), extra_words.items);
    }

    /// Decodes a `.fn_ty` or `.closure_ty` `TypeId` into its `FnSignatureView`.
    pub fn getFnSignatureView(self: *const InternPool, fn_ty: TypeId) ?FnSignatureView {
        const node = self.getNode(fn_ty);
        if (node.tag != .fn_ty and node.tag != .closure_ty) return null;
        if (node.lhs >= self.extra.items.len) return null;
        const arity: usize = self.extra.items[node.lhs];
        const params_start: usize = node.lhs + 1;
        const modes_start: usize = params_start + arity;
        if (modes_start + arity > self.extra.items.len) return null;
        return .{
            .ret_ty = TypeId.fromInt(node.rhs),
            .param_types = self.extra.items[params_start .. params_start + arity],
            .param_modes = self.extra.items[modes_start .. modes_start + arity],
        };
    }

    /// Unwraps chains of `.distinct_ty` and `.refined_ty` to the underlying representation `TypeId`.
    pub fn unwrapUnderlyingType(self: *const InternPool, ty: TypeId) TypeId {
        var cur = ty;
        var steps: usize = 0;
        while (steps < 64) : (steps += 1) {
            const node = self.getNode(cur);
            if (node.tag == .distinct_ty) {
                cur = TypeId.fromInt(node.lhs);
            } else if (node.tag == .refined_ty) {
                cur = TypeId.fromInt(node.rhs);
            } else {
                break;
            }
        }
        return cur;
    }

    /// Unwraps only `.refined_ty` layers (preserving `.distinct_ty` nominal boundaries).
    pub fn unwrapRefinementBase(self: *const InternPool, ty: TypeId) TypeId {
        var cur = ty;
        var steps: usize = 0;
        while (steps < 64) : (steps += 1) {
            const node = self.getNode(cur);
            if (node.tag == .refined_ty) {
                cur = TypeId.fromInt(node.rhs);
            } else {
                break;
            }
        }
        return cur;
    }

    /// Returns the slice of element `TypeId.toU32()` handles for a `.tuple_ty` node.
    pub fn getTupleElements(self: *const InternPool, tuple_ty: TypeId) []const u32 {
        const node = self.getNode(tuple_ty);
        if (node.tag != .tuple_ty) return &.{};
        const start: usize = node.lhs;
        const count: usize = node.rhs;
        if (start + count > self.extra.items.len) return &.{};
        return self.extra.items[start .. start + count];
    }

    /// Formats `ty` into caller-provided `buf` (zero heap allocations).
    pub fn formatType(
        self: *const InternPool,
        ty: TypeId,
        sym_table: *const SymbolTable,
        buf: []u8,
    ) []const u8 {
        var writer = SliceBufWriter{ .buf = buf };
        self.writeTypeToWriter(ty, sym_table, &writer, 0);
        return writer.buf[0..writer.pos];
    }

    /// Recursively writes the human-readable CoreX name of `ty` to `writer` (bounded by `MAX_TYPE_DEPTH`).
    fn writeTypeToWriter(
        self: *const InternPool,
        ty: TypeId,
        sym_table: *const SymbolTable,
        writer: *SliceBufWriter,
        depth: u32,
    ) void {
        if (depth >= MAX_TYPE_DEPTH) return writer.writeAll("<type>");
        for (symbol_resolver.BUILTIN_TYPES_AND_GROUPS) |entry| {
            if (entry.type_id == ty) return writer.writeAll(entry.name);
        }
        if (ty == .untyped_int_ty) return writer.writeAll("{integer}");
        if (ty == .untyped_float_ty) return writer.writeAll("{float}");
        if (ty == .err_ty) return writer.writeAll("<error>");

        const node = self.getNode(ty);
        switch (node.tag) {
            .struct_ty, .enum_ty, .union_ty, .bit_field_ty, .trait_ty, .distinct_ty, .user_group => {
                const sym_idx = SymbolIndex.fromInt(node.rhs);
                if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                    return writer.writeAll(sym_table.getSymbol(sym_idx).name_text);
                }
                return writer.writeAll("<nominal>");
            },
            .refined_ty => {
                if (self.getRefinementBounds(ty)) |bounds| {
                    if (!bounds.sym_idx.isNone() and bounds.sym_idx.asInt() < sym_table.symbols.items.len) {
                        const sym_name = sym_table.getSymbol(bounds.sym_idx).name_text;
                        if (sym_name.len > 0) {
                            return writer.print("{s} ({d}..={d})", .{ sym_name, bounds.min_val, bounds.max_val });
                        }
                    }
                    self.writeTypeToWriter(bounds.base_ty, sym_table, writer, depth + 1);
                    return writer.print(" is {d}..={d}", .{ bounds.min_val, bounds.max_val });
                }
                return writer.writeAll("<refined>");
            },
            .tilde_approx => {
                writer.writeAll("~");
                return self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
            },
            .optional_ty => {
                self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
                return writer.writeAll("?");
            },
            .result_ty => {
                writer.writeAll("Result[");
                self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
                writer.writeAll(", ");
                self.writeTypeToWriter(TypeId.fromInt(node.rhs), sym_table, writer, depth + 1);
                return writer.writeAll("]");
            },
            .slice_ty => {
                writer.writeAll("[");
                self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
                return writer.writeAll("]");
            },
            .soa_slice_ty => {
                writer.writeAll("#soa [");
                self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
                return writer.writeAll("]");
            },
            .array_ty, .soa_array_ty => {
                writer.writeAll(if (node.tag == .soa_array_ty) "#soa [" else "[");
                self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
                if ((node.rhs & SYMBOLIC_ARRAY_LEN_FLAG) != 0) {
                    const const_sym = SymbolId.fromInt(node.rhs & ~SYMBOLIC_ARRAY_LEN_FLAG);
                    for (sym_table.symbols.items) |cand_sym| {
                        const is_sym_len = cand_sym.kind == .const_param_sym or
                            (cand_sym.kind == .param_sym and cand_sym.flags.is_comptime);
                        if (is_sym_len and cand_sym.name == const_sym) {
                            return writer.print("; {s}]", .{cand_sym.name_text});
                        }
                    }
                    return writer.writeAll("; <const>]");
                }
                return writer.print("; {d}]", .{node.rhs});
            },
            .ref_ty => {
                writer.writeAll("&");
                return self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
            },
            .mut_ref_ty => {
                writer.writeAll("&mut ");
                return self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
            },
            .raw_ptr_ty => {
                writer.writeAll(if (node.rhs != 0) "*mut " else "*");
                return self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
            },
            .bind_once_group_var, .type_param => {
                return self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
            },
            .bind_many_any_var => {
                writer.writeAll("any ");
                return self.writeTypeToWriter(TypeId.fromInt(node.lhs), sym_table, writer, depth + 1);
            },
            else => return writer.writeAll("<type>"),
        }
    }
};

/// Canonical alias for `InternPool` (`PLAN.md` Phase 4).
pub const TypeArena = InternPool;

// ------------ Target-Aware Type Layout Calculator -------------

/// Rounds `byte_offset` up to the next power-of-two multiple of `align_bytes` (with saturating `u64` arithmetic).
pub inline fn alignUpU64(byte_offset: u64, align_bytes: u32) u64 {
    if (align_bytes <= 1) return byte_offset;
    const mask: u64 = @as(u64, align_bytes) - 1;
    return (byte_offset +| mask) & ~mask;
}

/// Computes the exact target-architecture `TypeLayout` (`byte_size`, `align_bytes`, `align_log2`) of `type_id`.
pub fn computeTypeLayoutWithPool(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    type_id: TypeId,
    target_layout: TargetLayout,
) TypeLayout {
    return computeTypeLayoutBounded(pool, sym_table, type_id, target_layout, 0);
}

/// Depth-bounded helper (`MAX_TYPE_DEPTH`) for `computeTypeLayoutWithPool`.
fn computeTypeLayoutBounded(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    type_id: TypeId,
    target_layout: TargetLayout,
    depth: u32,
) TypeLayout {
    if (depth >= MAX_TYPE_DEPTH) {
        return .{ .byte_size = 0, .align_bytes = 1, .align_log2 = 0, .is_sized = false };
    }

    switch (type_id) {
        .unit_ty, .never_ty, .err_ty => {
            return .{ .byte_size = 0, .align_bytes = 1, .align_log2 = 0 };
        },
        .bool_ty, .i8_ty, .u8_ty => {
            return .{ .byte_size = 1, .align_bytes = 1, .align_log2 = 0 };
        },
        .i16_ty, .u16_ty => {
            return .{ .byte_size = 2, .align_bytes = 2, .align_log2 = 1 };
        },
        .i32_ty, .u32_ty, .f32_ty, .char_ty, .untyped_int_ty => {
            return .{ .byte_size = 4, .align_bytes = 4, .align_log2 = 2 };
        },
        .i64_ty, .u64_ty, .f64_ty, .untyped_float_ty => {
            return .{ .byte_size = 8, .align_bytes = 8, .align_log2 = 3 };
        },
        .i128_ty, .u128_ty => {
            return .{ .byte_size = 16, .align_bytes = 16, .align_log2 = 4 };
        },
        .isize_ty, .usize_ty => {
            return .{
                .byte_size = target_layout.ptr_byte_size,
                .align_bytes = target_layout.ptrAlignBytes(),
                .align_log2 = target_layout.ptr_align_log2,
            };
        },
        .str_ty => {
            return .{
                .byte_size = @as(u64, target_layout.ptr_byte_size) * 2,
                .align_bytes = target_layout.ptrAlignBytes(),
                .align_log2 = target_layout.ptr_align_log2,
            };
        },
        else => {},
    }

    const node = pool.getNode(type_id);
    switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .fn_ty => {
            return .{
                .byte_size = target_layout.ptr_byte_size,
                .align_bytes = target_layout.ptrAlignBytes(),
                .align_log2 = target_layout.ptr_align_log2,
            };
        },
        .slice_ty, .soa_slice_ty, .closure_ty => {
            return .{
                .byte_size = @as(u64, target_layout.ptr_byte_size) * 2,
                .align_bytes = target_layout.ptrAlignBytes(),
                .align_log2 = target_layout.ptr_align_log2,
            };
        },
        .distinct_ty, .bit_field_ty => {
            return computeTypeLayoutBounded(pool, sym_table, TypeId.fromInt(node.lhs), target_layout, depth + 1);
        },
        .refined_ty => {
            return computeTypeLayoutBounded(pool, sym_table, TypeId.fromInt(node.rhs), target_layout, depth + 1);
        },
        .array_ty, .soa_array_ty => {
            const elem_layout = computeTypeLayoutBounded(
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                target_layout,
                depth + 1,
            );
            if ((node.rhs & SYMBOLIC_ARRAY_LEN_FLAG) != 0 or !elem_layout.is_sized) {
                return .{
                    .byte_size = 0,
                    .align_bytes = elem_layout.align_bytes,
                    .align_log2 = elem_layout.align_log2,
                    .is_sized = false,
                };
            }
            return .{
                .byte_size = elem_layout.byte_size *| @as(u64, node.rhs),
                .align_bytes = elem_layout.align_bytes,
                .align_log2 = elem_layout.align_log2,
            };
        },
        .tuple_ty => {
            var cur_offset: u64 = 0;
            var max_align_log2: u8 = 0;
            var is_all_sized = true;
            for (pool.getTupleElements(type_id)) |raw_elem| {
                const elem_layout = computeTypeLayoutBounded(
                    pool,
                    sym_table,
                    TypeId.fromInt(raw_elem),
                    target_layout,
                    depth + 1,
                );
                if (!elem_layout.is_sized) is_all_sized = false;
                if (elem_layout.align_log2 > max_align_log2) max_align_log2 = elem_layout.align_log2;
                cur_offset = alignUpU64(cur_offset, elem_layout.align_bytes) +| elem_layout.byte_size;
            }
            const max_align_bytes: u32 = @as(u32, 1) << @intCast(max_align_log2);
            return .{
                .byte_size = alignUpU64(cur_offset, max_align_bytes),
                .align_bytes = max_align_bytes,
                .align_log2 = max_align_log2,
                .is_sized = is_all_sized,
            };
        },
        .struct_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) {
                return .{ .byte_size = 0, .align_bytes = 1, .align_log2 = 0 };
            }
            const struct_sym = sym_table.getSymbol(sym_idx).*;
            if (struct_sym.target_scope.isNone()) {
                return .{ .byte_size = 0, .align_bytes = 1, .align_log2 = 0 };
            }
            var cur_offset: u64 = 0;
            var max_align_log2: u8 = 0;
            var is_all_sized = true;
            for (sym_table.getScopeMembers(struct_sym.target_scope)) |mem_idx| {
                const mem_sym = sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .field_sym) continue;
                const field_layout = computeTypeLayoutBounded(
                    pool,
                    sym_table,
                    mem_sym.type_id,
                    target_layout,
                    depth + 1,
                );
                if (!field_layout.is_sized) is_all_sized = false;
                if (field_layout.align_log2 > max_align_log2) max_align_log2 = field_layout.align_log2;
                cur_offset = alignUpU64(cur_offset, field_layout.align_bytes) +| field_layout.byte_size;
            }
            const max_align_bytes: u32 = @as(u32, 1) << @intCast(max_align_log2);
            return .{
                .byte_size = alignUpU64(cur_offset, max_align_bytes),
                .align_bytes = max_align_bytes,
                .align_log2 = max_align_log2,
                .is_sized = is_all_sized,
            };
        },
        .union_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) {
                return .{ .byte_size = 0, .align_bytes = 1, .align_log2 = 0 };
            }
            const union_sym = sym_table.getSymbol(sym_idx).*;
            if (union_sym.target_scope.isNone()) {
                return .{ .byte_size = 0, .align_bytes = 1, .align_log2 = 0 };
            }
            var max_field_size: u64 = 0;
            var max_align_log2: u8 = 0;
            var is_all_sized = true;
            for (sym_table.getScopeMembers(union_sym.target_scope)) |mem_idx| {
                const mem_sym = sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .field_sym) continue;
                const field_layout = computeTypeLayoutBounded(
                    pool,
                    sym_table,
                    mem_sym.type_id,
                    target_layout,
                    depth + 1,
                );
                if (!field_layout.is_sized) is_all_sized = false;
                if (field_layout.byte_size > max_field_size) max_field_size = field_layout.byte_size;
                if (field_layout.align_log2 > max_align_log2) max_align_log2 = field_layout.align_log2;
            }
            const max_align_bytes: u32 = @as(u32, 1) << @intCast(max_align_log2);
            return .{
                .byte_size = alignUpU64(max_field_size, max_align_bytes),
                .align_bytes = max_align_bytes,
                .align_log2 = max_align_log2,
                .is_sized = is_all_sized,
            };
        },
        .optional_ty => {
            const payload_layout = computeTypeLayoutBounded(
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                target_layout,
                depth + 1,
            );
            const max_align_log2: u8 = payload_layout.align_log2;
            const max_align_bytes: u32 = @as(u32, 1) << @intCast(max_align_log2);
            const payload_offset = alignUpU64(1, payload_layout.align_bytes);
            return .{
                .byte_size = alignUpU64(payload_offset +| payload_layout.byte_size, max_align_bytes),
                .align_bytes = max_align_bytes,
                .align_log2 = max_align_log2,
                .is_sized = payload_layout.is_sized,
            };
        },
        .result_ty => {
            const ok_layout = computeTypeLayoutBounded(
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                target_layout,
                depth + 1,
            );
            const err_layout = computeTypeLayoutBounded(
                pool,
                sym_table,
                TypeId.fromInt(node.rhs),
                target_layout,
                depth + 1,
            );
            const max_payload_log2: u8 = @max(ok_layout.align_log2, err_layout.align_log2);
            const max_align_bytes: u32 = @as(u32, 1) << @intCast(max_payload_log2);
            const max_payload_size: u64 = @max(ok_layout.byte_size, err_layout.byte_size);
            const payload_offset = alignUpU64(1, max_align_bytes);
            return .{
                .byte_size = alignUpU64(payload_offset +| max_payload_size, max_align_bytes),
                .align_bytes = max_align_bytes,
                .align_log2 = max_payload_log2,
                .is_sized = ok_layout.is_sized and err_layout.is_sized,
            };
        },
        .enum_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) {
                return .{ .byte_size = 1, .align_bytes = 1, .align_log2 = 0 };
            }
            const enum_sym = sym_table.getSymbol(sym_idx).*;
            if (enum_sym.target_scope.isNone()) {
                return .{ .byte_size = 1, .align_bytes = 1, .align_log2 = 0 };
            }
            var variant_count: usize = 0;
            var max_payload_size: u64 = 0;
            var max_payload_log2: u8 = 0;
            var is_all_sized = true;
            for (sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
                const mem_sym = sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .enum_variant_sym) continue;
                variant_count += 1;
                if (mem_sym.type_id != .unit_ty and !mem_sym.type_id.isError()) {
                    const var_layout = computeTypeLayoutBounded(
                        pool,
                        sym_table,
                        mem_sym.type_id,
                        target_layout,
                        depth + 1,
                    );
                    if (!var_layout.is_sized) is_all_sized = false;
                    if (var_layout.byte_size > max_payload_size) max_payload_size = var_layout.byte_size;
                    if (var_layout.align_log2 > max_payload_log2) max_payload_log2 = var_layout.align_log2;
                }
            }
            if (variant_count == 0) {
                return .{ .byte_size = 0, .align_bytes = 1, .align_log2 = 0 };
            }
            const tag_log2: u8 = if (variant_count <= 256) 0 else if (variant_count <= 65_536) 1 else 2;
            const tag_bytes: u64 = @as(u64, 1) << @intCast(tag_log2);
            const max_align_log2: u8 = @max(tag_log2, max_payload_log2);
            const max_align_bytes: u32 = @as(u32, 1) << @intCast(max_align_log2);
            if (max_payload_size == 0) {
                return .{
                    .byte_size = tag_bytes,
                    .align_bytes = max_align_bytes,
                    .align_log2 = max_align_log2,
                    .is_sized = is_all_sized,
                };
            }
            const payload_align_bytes: u32 = @as(u32, 1) << @intCast(max_payload_log2);
            const payload_offset = alignUpU64(tag_bytes, payload_align_bytes);
            return .{
                .byte_size = alignUpU64(payload_offset +| max_payload_size, max_align_bytes),
                .align_bytes = max_align_bytes,
                .align_log2 = max_align_log2,
                .is_sized = is_all_sized,
            };
        },
        else => {
            return .{ .byte_size = 0, .align_bytes = 1, .align_log2 = 0, .is_sized = false };
        },
    }
}

/// Computes the exact byte offset of `field_ordinal` inside `struct_ty` (`null` if `struct_ty` is not a `struct`).
pub fn computeStructFieldOffset(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    struct_ty: TypeId,
    field_ordinal: u32,
    target_layout: TargetLayout,
) ?u64 {
    const unwrapped = pool.unwrapUnderlyingType(struct_ty);
    const node = pool.getNode(unwrapped);
    if (node.tag != .struct_ty) return null;
    const sym_idx = SymbolIndex.fromInt(node.rhs);
    if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return null;
    const struct_sym = sym_table.getSymbol(sym_idx).*;
    if (struct_sym.target_scope.isNone()) return null;

    var cur_offset: u64 = 0;
    var cur_ordinal: u32 = 0;
    for (sym_table.getScopeMembers(struct_sym.target_scope)) |mem_idx| {
        const mem_sym = sym_table.getSymbol(mem_idx).*;
        if (mem_sym.kind != .field_sym) continue;
        const field_layout = computeTypeLayoutWithPool(pool, sym_table, mem_sym.type_id, target_layout);
        const aligned_offset = alignUpU64(cur_offset, field_layout.align_bytes);
        if (cur_ordinal == field_ordinal) return aligned_offset;
        cur_offset = aligned_offset +| field_layout.byte_size;
        cur_ordinal += 1;
    }
    return null;
}

// ---------- Group Membership & `FromError` Registry -----------

/// Classification of whether a candidate type satisfies a Constrained Type Group or `~T` bound.
pub const GroupMatchResult = enum(u8) {
    /// Candidate is not a member of the group (`E0402`).
    rejected = 0,
    /// Candidate is a `distinct` type whose underlying type is in the group without `~` (`E0405`).
    rejected_distinct_without_tilde = 1,
    /// Candidate matches via `~T` underlying approximation (rank 2 in overload resolution).
    matched_via_tilde = 2,
    /// Candidate matches as an exact member of the group (rank 1 in overload resolution).
    matched_exact = 3,
};

/// Evaluates whether `candidate_ty` satisfies `group_ty` (built-in group, user group, or `~T`).
pub fn checkGroupSatisfaction(
    pool: *const InternPool,
    candidate_ty: TypeId,
    group_ty: TypeId,
) GroupMatchResult {
    return checkGroupSatisfactionBounded(pool, candidate_ty, group_ty, 0);
}

/// Depth-bounded helper (`MAX_TYPE_DEPTH`) for `checkGroupSatisfaction`.
fn checkGroupSatisfactionBounded(
    pool: *const InternPool,
    candidate_ty: TypeId,
    group_ty: TypeId,
    depth: u32,
) GroupMatchResult {
    if (depth >= MAX_TYPE_DEPTH) return .rejected;
    if (candidate_ty.isError() or group_ty.isError() or group_ty == .group_copy) {
        return .matched_exact;
    }
    const unwrapped_refinement = pool.unwrapRefinementBase(candidate_ty);
    const underlying_ty = pool.unwrapUnderlyingType(candidate_ty);
    const is_distinct_candidate = (pool.getTag(unwrapped_refinement) == .distinct_ty);

    // [1] `~Target` underlying-type approximation:
    const group_node = pool.getNode(group_ty);
    if (group_node.tag == .tilde_approx) {
        const inner_target = TypeId.fromInt(group_node.lhs);
        if (inner_target.isBuiltinGroup() or
            pool.getTag(inner_target) == .user_group or
            pool.getTag(inner_target) == .tilde_approx)
        {
            const base_match = checkGroupSatisfactionBounded(pool, underlying_ty, inner_target, depth + 1);
            if (base_match == .matched_exact or base_match == .matched_via_tilde) {
                return if (is_distinct_candidate) .matched_via_tilde else base_match;
            }
            return .rejected;
        }
        const target_ty = pool.unwrapUnderlyingType(inner_target);
        if (unwrapped_refinement == target_ty) return .matched_exact;
        if (underlying_ty == target_ty) return .matched_via_tilde;
        if (candidate_ty == .untyped_int_ty and target_ty.isIntegerPrimitive()) return .matched_exact;
        if (candidate_ty == .untyped_float_ty and target_ty.isFloatPrimitive()) return .matched_exact;
        return .rejected;
    }

    // [2] Built-in Constrained Type Group (`32..42`):
    if (group_ty.isBuiltinGroup() or group_node.tag == .builtin_group) {
        const mask = if (group_ty.isBuiltinGroup())
            TypeGroupMask.forBuiltinGroup(group_ty)
        else
            group_node.lhs;

        if (candidate_ty == .untyped_int_ty) {
            return if ((mask & TypeGroupMask.INTEGER) != 0) .matched_exact else .rejected;
        }
        if (candidate_ty == .untyped_float_ty) {
            return if ((mask & TypeGroupMask.FLOAT) != 0) .matched_exact else .rejected;
        }
        if (!is_distinct_candidate and unwrapped_refinement.isPrimitive()) {
            return if (TypeGroupMask.containsPrimitive(mask, unwrapped_refinement))
                .matched_exact
            else
                .rejected;
        }
        if (is_distinct_candidate and underlying_ty.isPrimitive() and
            TypeGroupMask.containsPrimitive(mask, underlying_ty))
        {
            return .rejected_distinct_without_tilde;
        }
        return .rejected;
    }

    // [3] User-defined Constrained Type Group (`type G = A | ~B`):
    if (pool.getUserGroupView(group_ty)) |view| {
        if (candidate_ty == .untyped_int_ty) {
            if (((view.prim_mask | view.tilde_prim_mask) & TypeGroupMask.INTEGER) != 0) {
                return .matched_exact;
            }
            return .rejected;
        }
        if (candidate_ty == .untyped_float_ty) {
            if (((view.prim_mask | view.tilde_prim_mask) & TypeGroupMask.FLOAT) != 0) {
                return .matched_exact;
            }
            return .rejected;
        }
        if (!is_distinct_candidate and unwrapped_refinement.isPrimitive()) {
            if (TypeGroupMask.containsPrimitive(view.prim_mask, unwrapped_refinement)) {
                return .matched_exact;
            }
            if (TypeGroupMask.containsPrimitive(view.tilde_prim_mask, unwrapped_refinement)) {
                return .matched_via_tilde;
            }
        }
        for (view.exact_members) |exact_raw| {
            if (unwrapped_refinement.toU32() == exact_raw) return .matched_exact;
        }
        for (view.tilde_members) |tilde_raw| {
            if (unwrapped_refinement.toU32() == tilde_raw) return .matched_exact;
            if (underlying_ty.toU32() == tilde_raw) return .matched_via_tilde;
        }
        if (is_distinct_candidate and underlying_ty.isPrimitive()) {
            if (TypeGroupMask.containsPrimitive(view.tilde_prim_mask, underlying_ty)) {
                return .matched_via_tilde;
            }
            if (TypeGroupMask.containsPrimitive(view.prim_mask, underlying_ty)) {
                return .rejected_distinct_without_tilde;
            }
        }
        if (is_distinct_candidate) {
            for (view.exact_members) |exact_raw| {
                if (underlying_ty.toU32() == exact_raw) return .rejected_distinct_without_tilde;
            }
        }
        return .rejected;
    }

    // [4] Nominal trait bound (`[T: MyTrait]`):
    if (unwrapped_refinement == group_ty) return .matched_exact;
    return .rejected;
}

/// Returns `true` if `sub_group` is a mathematical subset of `super_group` (`G_1 <: G_2`, `DR-04` Section 1.2).
pub fn isTypeGroupSubset(
    pool: *const InternPool,
    sub_group: TypeId,
    super_group: TypeId,
) bool {
    if (sub_group == super_group) return true;
    if (sub_group.isBuiltinGroup() and super_group.isBuiltinGroup()) {
        return TypeGroupMask.isSubsetOf(
            TypeGroupMask.forBuiltinGroup(sub_group),
            TypeGroupMask.forBuiltinGroup(super_group),
        );
    }
    if (pool.getUserGroupView(sub_group)) |sub_view| {
        if (super_group.isBuiltinGroup()) {
            const super_mask = TypeGroupMask.forBuiltinGroup(super_group);
            return sub_view.exact_members.len == 0 and
                sub_view.tilde_members.len == 0 and
                sub_view.tilde_prim_mask == 0 and
                TypeGroupMask.isSubsetOf(sub_view.prim_mask, super_mask);
        }
    }
    return false;
}

// ------- Maranget 128-Bit Interval Splitting (`DR-07`) --------

/// Inclusive 128-bit integer range `[min_val, max_val]` for Maranget pattern exhaustiveness.
pub const Interval128 = struct {
    /// Inclusive lower bound.
    min_val: i128,
    /// Inclusive upper bound (`min_val <= max_val`).
    max_val: i128,
};

/// Subtracts `arm_range` (`[min_val, max_val]`) in place from `uncovered_intervals[0..uncovered_count.*]`.
pub fn subtractIntervalFromUncovered(
    uncovered_intervals: *[128]Interval128,
    uncovered_count: *usize,
    arm_range: Interval128,
) void {
    if (arm_range.min_val > arm_range.max_val) return;
    var i: usize = 0;
    while (i < uncovered_count.*) {
        const cur = uncovered_intervals[i];
        if (arm_range.max_val < cur.min_val or arm_range.min_val > cur.max_val) {
            i += 1;
            continue;
        }
        // Overflow-safe boundary checks at `minInt(i128)` and `maxInt(i128)` (Critique H1):
        const has_left_rem = (arm_range.min_val > cur.min_val);
        const has_right_rem = (arm_range.max_val < cur.max_val);

        if (has_left_rem and has_right_rem) {
            uncovered_intervals[i] = .{ .min_val = cur.min_val, .max_val = arm_range.min_val - 1 };
            if (uncovered_count.* < uncovered_intervals.len) {
                var shift_idx: usize = uncovered_count.*;
                while (shift_idx > i + 1) : (shift_idx -= 1) {
                    uncovered_intervals[shift_idx] = uncovered_intervals[shift_idx - 1];
                }
                uncovered_intervals[i + 1] = .{ .min_val = arm_range.max_val + 1, .max_val = cur.max_val };
                uncovered_count.* += 1;
                i += 2;
            } else {
                i += 1;
            }
        } else if (has_left_rem) {
            uncovered_intervals[i] = .{ .min_val = cur.min_val, .max_val = arm_range.min_val - 1 };
            i += 1;
        } else if (has_right_rem) {
            uncovered_intervals[i] = .{ .min_val = arm_range.max_val + 1, .max_val = cur.max_val };
            i += 1;
        } else {
            var rem_idx: usize = i;
            while (rem_idx + 1 < uncovered_count.*) : (rem_idx += 1) {
                uncovered_intervals[rem_idx] = uncovered_intervals[rem_idx + 1];
            }
            uncovered_count.* -= 1;
        }
    }
}

/// Subtracts `arm_range` (`[min_val, max_val]`) in place from an unbounded `uncovered_intervals` list.
fn subtractIntervalFromUncoveredList(
    allocator: std.mem.Allocator,
    uncovered_intervals: *std.ArrayListUnmanaged(Interval128),
    arm_range: Interval128,
) !void {
    if (arm_range.min_val > arm_range.max_val) return;
    var i: usize = 0;
    while (i < uncovered_intervals.items.len) {
        const cur = uncovered_intervals.items[i];
        if (arm_range.max_val < cur.min_val or arm_range.min_val > cur.max_val) {
            i += 1;
            continue;
        }
        const has_left_rem = (arm_range.min_val > cur.min_val);
        const has_right_rem = (arm_range.max_val < cur.max_val);

        if (has_left_rem and has_right_rem) {
            uncovered_intervals.items[i] = .{ .min_val = cur.min_val, .max_val = arm_range.min_val - 1 };
            try uncovered_intervals.insert(
                allocator,
                i + 1,
                .{ .min_val = arm_range.max_val + 1, .max_val = cur.max_val },
            );
            i += 2;
        } else if (has_left_rem) {
            uncovered_intervals.items[i] = .{ .min_val = cur.min_val, .max_val = arm_range.min_val - 1 };
            i += 1;
        } else if (has_right_rem) {
            uncovered_intervals.items[i] = .{ .min_val = arm_range.max_val + 1, .max_val = cur.max_val };
            i += 1;
        } else {
            _ = uncovered_intervals.orderedRemove(i);
        }
    }
}

// ----------- Spine-Local Bidirectional Type Checker -----------

/// Bidirectional type checker and semantic verifier for a single compilation unit or `DefId`.
pub const TypeChecker = struct {
    /// Backing allocator for side tables and scratch buffers.
    allocator: std.mem.Allocator,
    /// Shared string interner.
    interner: *StringInterner,
    /// Shared canonical `InternPool`.
    pool: *InternPool,
    /// Shared `SymbolTable`.
    sym_table: *SymbolTable,
    /// Current source file handle.
    file_id: FileId,
    /// UTF-8 source buffer of `file_id`.
    source: []const u8,
    /// Read-only `TokenBuffer` of `file_id`.
    token_buffer: *const TokenBuffer,
    /// Read-only `LosslessCstArena` of `file_id`.
    cst_arena: *const LosslessCstArena,
    /// Read-only `AstArena` of `file_id`.
    ast_arena: *const AstArena,
    /// Optional diagnostic sink receiving `E0400`–`E0415`, `E0502`–`E0510`, and `W0401`–`W0402`.
    diagnostic_sink: ?*DiagnosticSink,
    /// Optional query database reference for cross-item `comptime` evaluation (`[MAJOR-02]`).
    db: ?*query_db.CompilerDb = null,
    /// Active target pointer layout (`TargetLayout.NATIVE_64` by default).
    target_layout: TargetLayout = TargetLayout.NATIVE_64,
    /// Reverse lookup table mapping each `CstNodeIndex` to the outermost `NodeIndex` anchored at that CST node.
    cst_to_ast: []NodeIndex = &.{},
    /// Dense array mapping each AST `NodeIndex.asInt()` to its inferred/checked `TypeId`.
    node_types: []TypeId = &.{},
    /// Dense array mapping each AST `NodeIndex.asInt()` to its resolved `SymbolIndex` (`.none` by default).
    node_symbols: []SymbolIndex = &.{},
    /// Precomputed end offset in `ast_arena.extra_data` for each AST `NodeIndex` owning an `.extra` slice.
    node_extra_end: []u32 = &.{},
    /// Concrete generic / Type-Group `[TypeId…]` instantiation tuples keyed by call `NodeIndex.asInt()`.
    call_instantiations: std.AutoHashMapUnmanaged(u32, []TypeId) = .empty,
    /// `@from` `FromError` conversion `DefId`s keyed by `.try_expr` `NodeIndex.asInt()`.
    try_conversions: std.AutoHashMapUnmanaged(u32, DefId) = .empty,
    /// Validated `@attribute_schema` instances collected across declarations, fields, and variants.
    attr_instances: std.ArrayListUnmanaged(AttrInstance) = .empty,
    /// Active lexical `ScopeId` during body checking.
    current_scope: ScopeId = .none,
    /// Declared return `TypeId` of the enclosing function (`.unit_ty` at module level).
    current_fn_ret_ty: TypeId = .unit_ty,
    /// Expected break `TypeId` of the innermost `loop` expression.
    current_loop_break_ty: TypeId = .unit_ty,
    /// Counter generating unique ordinals for `bind_many_any_var` parameters.
    next_any_ordinal: u32 = 0,
    /// Active Bind-Once group variables within the current function signature (`SymbolId -> TypeId`).
    active_bind_once_vars: std.AutoHashMapUnmanaged(u32, TypeId) = .empty,
    /// Current recursion depth across type AST resolution, unification, and expression checking (`MAX_TYPE_DEPTH`).
    recursion_depth: u32 = 0,
    /// Nesting depth of active `defer` / `errdefer` cleanup bodies (`[CRITICAL-08]`).
    defer_depth: u32 = 0,
    /// Nesting depth of loops opened *inside* the innermost `defer` / `errdefer` body.
    defer_inner_loop_depth: u32 = 0,
    /// Nesting depth of pure `comptime` evaluation contexts (`const`, `comptime { … }`, `comptime fn`).
    pure_comptime_depth: u32 = 0,
    /// Lexical scope depth boundary separating outer runtime bindings from `comptime`-local bindings.
    comptime_boundary_scope_depth: u16 = 0,
    /// Nesting depth of `comptime if` / `comptime match` branches whose condition is not statically folded yet.
    comptime_branch_guard_depth: u32 = 0,
    /// `true` while binding `comptime for` pattern variables so each binding receives `flags.is_comptime = true`.
    is_binding_comptime: bool = false,
    /// `true` when checking a direct positive `if` / `while` condition where `expr is Pat` bindings scope into `then`.
    is_direct_positive_cond: bool = false,
    /// `true` while resolving a function signature (`extractFnParamFromCst` or return type).
    is_in_fn_signature: bool = false,
    /// `true` while resolving a function return type (rejects existential `-> any Group`).
    is_in_return_type_pos: bool = false,
    /// `true` once the `std::meta` reflection mirror types have been lazily synthesized.
    has_reflection_mirrors: bool = false,
    /// Lazily synthesized `std::meta::MetaId` `TypeId`.
    mirror_meta_id_ty: TypeId = .err_ty,
    /// Lazily synthesized `std::meta::PrimKind` `TypeId`.
    mirror_prim_kind_ty: TypeId = .err_ty,
    /// Lazily synthesized `std::meta::FieldInfo` `TypeId`.
    mirror_field_info_ty: TypeId = .err_ty,
    /// Lazily synthesized `std::meta::StructInfo` `TypeId`.
    mirror_struct_info_ty: TypeId = .err_ty,
    /// Lazily synthesized `std::meta::VariantInfo` `TypeId`.
    mirror_variant_info_ty: TypeId = .err_ty,
    /// Lazily synthesized `std::meta::EnumInfo` `TypeId`.
    mirror_enum_info_ty: TypeId = .err_ty,
    /// Lazily synthesized `std::meta::TypeKind` `TypeId`.
    mirror_type_kind_ty: TypeId = .err_ty,
    /// Lazily synthesized `std::meta::TypeInfo` `TypeId`.
    mirror_type_info_ty: TypeId = .err_ty,
    /// Active `const` evaluation stack for cycle detection (`E0509`).
    active_const_eval: [32]SymbolIndex = @splat(.none),
    /// Current length of `active_const_eval`.
    active_const_eval_len: u8 = 0,

    /// Initializes a `TypeChecker` for `file_id`, building the shared $O(N)$ lookup and side tables.
    pub fn init(
        allocator: std.mem.Allocator,
        interner: *StringInterner,
        pool: *InternPool,
        sym_table: *SymbolTable,
        file_id: FileId,
        source: []const u8,
        token_buffer: *const TokenBuffer,
        cst_arena: *const LosslessCstArena,
        ast_arena: *const AstArena,
        diagnostic_sink: ?*DiagnosticSink,
    ) !TypeChecker {
        const ast_len = ast_arena.countNodes();

        const cst_map = try syntax_arenas.computeCstToAstMap(allocator, cst_arena.countNodes(), ast_arena);
        errdefer if (cst_map.len > 0) allocator.free(cst_map);

        const ty_table = try allocator.alloc(TypeId, ast_len);
        errdefer if (ty_table.len > 0) allocator.free(ty_table);
        @memset(ty_table, .err_ty);

        const sym_node_table = try allocator.alloc(SymbolIndex, ast_len);
        errdefer if (sym_node_table.len > 0) allocator.free(sym_node_table);
        @memset(sym_node_table, .none);

        const extra_end_table = try syntax_arenas.computeAstNodeExtraEnds(allocator, ast_arena);
        errdefer if (extra_end_table.len > 0) allocator.free(extra_end_table);

        const mod_scope = sym_table.file_module_scopes.get(file_id.asInt()) orelse sym_table.prelude_scope;

        return .{
            .allocator = allocator,
            .interner = interner,
            .pool = pool,
            .sym_table = sym_table,
            .file_id = file_id,
            .source = source,
            .token_buffer = token_buffer,
            .cst_arena = cst_arena,
            .ast_arena = ast_arena,
            .diagnostic_sink = diagnostic_sink,
            .cst_to_ast = cst_map,
            .node_types = ty_table,
            .node_symbols = sym_node_table,
            .node_extra_end = extra_end_table,
            .current_scope = mod_scope,
        };
    }

    /// Releases side tables owned by `self`.
    pub fn deinit(self: *TypeChecker) void {
        if (self.cst_to_ast.len > 0) self.allocator.free(self.cst_to_ast);
        if (self.node_types.len > 0) self.allocator.free(self.node_types);
        if (self.node_symbols.len > 0) self.allocator.free(self.node_symbols);
        if (self.node_extra_end.len > 0) self.allocator.free(self.node_extra_end);
        var inst_iter = self.call_instantiations.valueIterator();
        while (inst_iter.next()) |slice_ptr| {
            if (slice_ptr.*.len > 0) self.allocator.free(slice_ptr.*);
        }
        self.call_instantiations.deinit(self.allocator);
        self.try_conversions.deinit(self.allocator);
        for (self.attr_instances.items) |attr_inst| {
            if (attr_inst.fields.len > 0) self.allocator.free(attr_inst.fields);
        }
        self.attr_instances.deinit(self.allocator);
        self.active_bind_once_vars.deinit(self.allocator);
        self.* = undefined;
    }

    /// Records `ty` for `node_id` in `self.node_types` and returns `ty`.
    inline fn recordNodeType(self: *TypeChecker, node_id: NodeIndex, ty: TypeId) TypeId {
        if (!node_id.isNone() and node_id.asInt() < self.node_types.len) {
            self.node_types[node_id.asInt()] = ty;
        }
        return ty;
    }

    /// Records `sym_idx` for `node_id` in `self.node_symbols`.
    inline fn recordNodeSymbol(self: *TypeChecker, node_id: NodeIndex, sym_idx: SymbolIndex) void {
        if (!node_id.isNone() and node_id.asInt() < self.node_symbols.len) {
            self.node_symbols[node_id.asInt()] = sym_idx;
        }
    }

    /// Records inferred concrete `type_args` for `call_id` in `self.call_instantiations`.
    fn recordCallInstantiation(self: *TypeChecker, call_id: NodeIndex, type_args: []const TypeId) !void {
        if (call_id.isNone() or type_args.len == 0) return;
        const owned_slice = try self.allocator.dupe(TypeId, type_args);
        errdefer self.allocator.free(owned_slice);
        if (try self.call_instantiations.fetchPut(self.allocator, call_id.asInt(), owned_slice)) |prev_kv| {
            if (prev_kv.value.len > 0) self.allocator.free(prev_kv.value);
        }
    }

    /// Computes the target-architecture `TypeLayout` of `type_id` using `self.pool` and `self.sym_table`.
    pub fn computeTypeLayout(
        self: *const TypeChecker,
        type_id: TypeId,
        target_layout: TargetLayout,
    ) TypeLayout {
        return computeTypeLayoutWithPool(self.pool, self.sym_table, type_id, target_layout);
    }

    /// Extracts window-scoped `BodySemanticSideTables` (`[ast_start .. ast_end)`) for `def_id` (`[CRITICAL-11]`).
    pub fn extractBodySemanticSideTables(
        self: *const TypeChecker,
        allocator: std.mem.Allocator,
        def_id: DefId,
    ) !BodySemanticSideTables {
        var ast_start: u32 = 0;
        var ast_end: u32 = @intCast(self.ast_arena.countNodes());

        if (!def_id.isNone()) {
            var target_cst: CstNodeIndex = .none;
            var target_ast: NodeIndex = .none;
            if (self.sym_table.def_to_symbol.get(def_id.asInt())) |sym_idx| {
                const sym = self.sym_table.getSymbol(sym_idx).*;
                target_cst = sym.cst_node;
                target_ast = sym.ast_node;
            } else if (self.ast_arena.countNodes() > 0) {
                const root_node = self.ast_arena.getNode(.root);
                if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
                    const item_slice = self.ast_arena.getExtraSlice(
                        ExtraIndex.fromInt(root_node.lhs.payload),
                        root_node.rhs.payload,
                    );
                    var top_ordinal: u12 = 0;
                    for (item_slice) |raw_node_idx| {
                        const cand_idx = NodeIndex.fromInt(raw_node_idx);
                        if (cand_idx.asInt() >= self.ast_arena.countNodes()) continue;
                        if (self.ast_arena.getNode(cand_idx).tag == .item_hole) continue;
                        if (top_ordinal == def_id.itemIndex()) {
                            target_ast = cand_idx;
                            target_cst = self.ast_arena.getCstOrigin(cand_idx);
                            break;
                        }
                        if (top_ordinal < std.math.maxInt(u12)) top_ordinal += 1;
                    }
                }
            }

            if (!target_cst.isNone() and target_cst.asInt() < self.cst_arena.countNodes()) {
                const cst_start: usize = target_cst.asInt();
                const cst_rec = self.cst_arena.getNode(target_cst);
                const cst_end: usize = @min(
                    cst_start + @max(@as(usize, cst_rec.subtree_size), 1),
                    self.cst_to_ast.len,
                );
                var min_ast: u32 = std.math.maxInt(u32);
                var max_ast: u32 = 0;
                for (self.cst_to_ast[cst_start..cst_end]) |mapped_ast| {
                    if (!mapped_ast.isNone()) {
                        if (mapped_ast.asInt() < min_ast) min_ast = mapped_ast.asInt();
                        if (mapped_ast.asInt() > max_ast) max_ast = mapped_ast.asInt();
                    }
                }
                if (min_ast <= max_ast and max_ast < self.ast_arena.countNodes()) {
                    ast_start = min_ast;
                    ast_end = max_ast + 1;
                } else if (!target_ast.isNone() and target_ast.asInt() < self.ast_arena.countNodes()) {
                    ast_start = target_ast.asInt();
                    ast_end = target_ast.asInt() + 1;
                }
            } else if (!target_ast.isNone() and target_ast.asInt() < self.ast_arena.countNodes()) {
                ast_start = target_ast.asInt();
                ast_end = target_ast.asInt() + 1;
            }
        }

        return self.extractWindowSideTables(allocator, def_id, ast_start, ast_end);
    }

    /// Extracts whole-file `BodySemanticSideTables` (`[0 .. ast_arena.countNodes())`).
    pub fn extractFileSemanticSideTables(
        self: *const TypeChecker,
        allocator: std.mem.Allocator,
    ) !BodySemanticSideTables {
        return self.extractWindowSideTables(
            allocator,
            .NONE,
            0,
            @intCast(self.ast_arena.countNodes()),
        );
    }

    /// Copies side tables strictly intersecting `[ast_start .. ast_end)` into a new `BodySemanticSideTables`.
    fn extractWindowSideTables(
        self: *const TypeChecker,
        allocator: std.mem.Allocator,
        def_id: DefId,
        ast_start: u32,
        ast_end: u32,
    ) !BodySemanticSideTables {
        const clamped_end: usize = @min(@as(usize, ast_end), self.node_types.len);
        const clamped_start: usize = @min(@as(usize, ast_start), clamped_end);

        const owned_types = try allocator.dupe(TypeId, self.node_types[clamped_start..clamped_end]);
        errdefer if (owned_types.len > 0) allocator.free(owned_types);

        const owned_symbols = try allocator.dupe(SymbolIndex, self.node_symbols[clamped_start..clamped_end]);
        errdefer if (owned_symbols.len > 0) allocator.free(owned_symbols);

        var result = BodySemanticSideTables{
            .allocator = allocator,
            .def_id = def_id,
            .ast_start = @intCast(clamped_start),
            .ast_end = @intCast(clamped_end),
            .node_types = owned_types,
            .node_symbols = owned_symbols,
        };
        errdefer result.deinit();

        var inst_iter = self.call_instantiations.iterator();
        while (inst_iter.next()) |entry| {
            const raw_node = entry.key_ptr.*;
            if (raw_node >= result.ast_start and raw_node < result.ast_end) {
                const duped_args = try allocator.dupe(TypeId, entry.value_ptr.*);
                errdefer if (duped_args.len > 0) allocator.free(duped_args);
                try result.call_instantiations.put(allocator, raw_node - result.ast_start, duped_args);
            }
        }

        var try_iter = self.try_conversions.iterator();
        while (try_iter.next()) |entry| {
            const raw_node = entry.key_ptr.*;
            if (raw_node >= result.ast_start and raw_node < result.ast_end) {
                try result.try_conversions.put(allocator, raw_node - result.ast_start, entry.value_ptr.*);
            }
        }

        var matching_attrs: std.ArrayListUnmanaged(AttrInstance) = .empty;
        errdefer {
            for (matching_attrs.items) |attr_item| {
                if (attr_item.fields.len > 0) allocator.free(attr_item.fields);
            }
            matching_attrs.deinit(allocator);
        }
        for (self.attr_instances.items) |attr_inst| {
            if (def_id.isNone() or attr_inst.owner_def_id == def_id) {
                const duped_fields = try allocator.dupe(AttrFieldInit, attr_inst.fields);
                errdefer if (duped_fields.len > 0) allocator.free(duped_fields);
                try matching_attrs.append(allocator, .{
                    .schema_type_id = attr_inst.schema_type_id,
                    .target_symbol = attr_inst.target_symbol,
                    .owner_def_id = attr_inst.owner_def_id,
                    .attr_span = attr_inst.attr_span,
                    .fields = duped_fields,
                });
            }
        }
        result.attr_instances = try matching_attrs.toOwnedSlice(allocator);
        return result;
    }

    /// Returns the `extra_data` slice owned by `node_id` in $O(1)$ time.
    pub fn getNodeExtraSlice(self: *const TypeChecker, node_id: NodeIndex, is_rhs: bool) []const u32 {
        if (node_id.isNone() or node_id.asInt() >= self.ast_arena.countNodes()) return &.{};
        const ast_node = self.ast_arena.getNode(node_id);
        const op = if (is_rhs) ast_node.rhs else ast_node.lhs;
        if (op.tag != .extra) return &.{};
        const start_idx: usize = op.payload;
        const end_idx: usize = @min(
            @as(usize, self.node_extra_end[node_id.asInt()]),
            self.ast_arena.extra_data.items.len,
        );
        if (start_idx >= end_idx) return &.{};
        return self.ast_arena.extra_data.items[start_idx..end_idx];
    }

    /// Computes the source `Span` of an AST node from its CST origin or `main_token`.
    pub fn getAstNodeSpan(self: *const TypeChecker, node_id: NodeIndex) Span {
        if (node_id.isNone() or node_id.asInt() >= self.ast_arena.countNodes()) {
            return Span.init(self.file_id, 0, 0);
        }
        const ast_node = self.ast_arena.getNode(node_id);
        if (!ast_node.main_token.isNone() and ast_node.main_token.asInt() < self.token_buffer.countTokens()) {
            return self.token_buffer.getTokenSpan(self.file_id, ast_node.main_token);
        }
        return Span.init(self.file_id, 0, 0);
    }

    /// Finds the outermost AST `NodeIndex` anchored inside the CST range `[cst_start .. cst_end)`.
    fn findFirstAstInCstRange(self: *const TypeChecker, cst_start: usize, cst_end: usize) NodeIndex {
        const clamped_end = @min(cst_end, self.cst_to_ast.len);
        var cur = cst_start;
        while (cur < clamped_end) : (cur += 1) {
            const mapped = self.cst_to_ast[cur];
            if (!mapped.isNone()) return mapped;
        }
        return .none;
    }

    // --------- Pass 1: Module Signature & Type Resolution ---------

    /// Resolves all top-level nominal types, type aliases, type groups, constants, and function signatures.
    pub fn resolveModuleSignatures(self: *TypeChecker) !void {
        const mod_scope = self.sym_table.file_module_scopes.get(self.file_id.asInt()) orelse return;
        try self.resolveScopeSignaturesRecursive(mod_scope);
        if (self.ast_arena.countNodes() > 0) {
            const root_node = self.ast_arena.getNode(.root);
            if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
                const root_items = self.ast_arena.getExtraSlice(
                    ExtraIndex.fromInt(root_node.lhs.payload),
                    root_node.rhs.payload,
                );
                try self.registerImplTraitPairsInItemSlice(mod_scope, root_items);
            }
        }
        try self.verifyScopeDerivesAndAttributesRecursive(mod_scope);
    }

    /// Recursively resolves declarations in `scope_id` and its child module/type scopes.
    fn resolveScopeSignaturesRecursive(self: *TypeChecker, scope_id: ScopeId) anyerror!void {
        const saved_scope = self.current_scope;
        self.current_scope = scope_id;
        defer self.current_scope = saved_scope;

        const members_copy = try self.allocator.dupe(
            SymbolIndex,
            self.sym_table.getScopeMembers(scope_id),
        );
        defer self.allocator.free(members_copy);

        // [1] Pre-assign nominal `TypeId` handles for structs, enums, unions, bit_fields, and traits:
        for (members_copy) |sym_idx| {
            const sym = self.sym_table.getSymbol(sym_idx).*;
            if (sym.flags.is_builtin or sym.flags.is_imported) continue;
            const nominal_ty: ?TypeId = switch (sym.kind) {
                .struct_sym => try self.pool.internNominal(
                    .struct_ty,
                    sym.def_id.asInt(),
                    sym_idx,
                    false,
                    sym.flags.is_must_use,
                    sym.flags.is_soa_annotated,
                ),
                .enum_sym => try self.pool.internNominal(
                    .enum_ty,
                    sym.def_id.asInt(),
                    sym_idx,
                    true,
                    sym.flags.is_must_use,
                    false,
                ),
                .union_sym => try self.pool.internNominal(
                    .union_ty,
                    sym.def_id.asInt(),
                    sym_idx,
                    true,
                    sym.flags.is_must_use,
                    false,
                ),
                .bit_field_sym => blk: {
                    var backing_ty: TypeId = .u32_ty;
                    if (!sym.ast_node.isNone()) {
                        const bf_ast = self.ast_arena.getNode(sym.ast_node);
                        if (bf_ast.lhs.tag == .node) {
                            backing_ty = try self.resolveTypeAst(NodeIndex.fromInt(bf_ast.lhs.payload));
                            if (self.pool.getTag(backing_ty) == .tuple_ty) {
                                const tup_elems = self.pool.getTupleElements(backing_ty);
                                if (tup_elems.len == 1) {
                                    backing_ty = TypeId.fromInt(tup_elems[0]);
                                }
                            }
                        }
                    }
                    break :blk try self.pool.internNominal(
                        .bit_field_ty,
                        backing_ty.toU32(),
                        sym_idx,
                        true,
                        sym.flags.is_must_use,
                        false,
                    );
                },
                .trait_sym => try self.pool.internNominal(
                    .trait_ty,
                    sym.def_id.asInt(),
                    sym_idx,
                    false,
                    false,
                    false,
                ),
                else => null,
            };
            if (nominal_ty) |tid| {
                self.sym_table.getSymbolMut(sym_idx).type_id = tid;
                try self.sym_table.type_to_symbol.put(self.allocator, tid.toU32(), sym_idx);
                if (!sym.target_scope.isNone()) {
                    try self.ensureSelfAliasInTargetScope(sym.target_scope, tid);
                }
            }
        }

        // [2] Resolve `type` aliases, `distinct` newtypes, `is` range refinements, and user Type Groups:
        for (members_copy) |sym_idx| {
            const sym = self.sym_table.getSymbol(sym_idx).*;
            if (sym.flags.is_builtin or sym.flags.is_imported) continue;
            switch (sym.kind) {
                .type_alias_sym, .distinct_type_sym, .refined_type_sym, .type_group_sym => {
                    const resolved_ty = try self.resolveTypeAliasSymbol(sym_idx);
                    self.sym_table.getSymbolMut(sym_idx).type_id = resolved_ty;
                    if (sym.kind != .type_alias_sym) {
                        try self.sym_table.type_to_symbol.put(self.allocator, resolved_ty.toU32(), sym_idx);
                    }
                },
                else => {},
            }
        }

        // [3] Resolve struct/union/bit_field fields, enum variants, `@derive` headers, constants, and functions:
        for (members_copy) |sym_idx| {
            const sym = self.sym_table.getSymbol(sym_idx).*;
            if (sym.flags.is_builtin or sym.flags.is_imported) continue;
            switch (sym.kind) {
                .module_sym => {
                    if (!sym.target_scope.isNone()) {
                        try self.resolveScopeSignaturesRecursive(sym.target_scope);
                        if (!sym.ast_node.isNone()) {
                            const mod_items = self.extractModInnerItemsSlice(sym.ast_node);
                            if (mod_items.len > 0) {
                                try self.registerImplTraitPairsInItemSlice(sym.target_scope, mod_items);
                            }
                        }
                    }
                },
                .struct_sym, .union_sym, .bit_field_sym => {
                    try self.resolveStructOrBitFieldFields(sym_idx);
                    if (sym.derive_mask.hasAny()) {
                        try self.registerDerivedTraitHeaders(sym_idx);
                    }
                    if (!sym.target_scope.isNone()) {
                        try self.resolveScopeSignaturesRecursive(sym.target_scope);
                    }
                },
                .enum_sym => {
                    try self.resolveEnumVariantPayloads(sym_idx);
                    if (sym.derive_mask.hasAny()) {
                        try self.registerDerivedTraitHeaders(sym_idx);
                    }
                    if (!sym.target_scope.isNone()) {
                        try self.resolveScopeSignaturesRecursive(sym.target_scope);
                    }
                },
                .trait_sym => {
                    if (!sym.target_scope.isNone()) {
                        try self.resolveScopeSignaturesRecursive(sym.target_scope);
                    }
                },
                .const_sym => {
                    if (!sym.ast_node.isNone()) {
                        const c_node = self.ast_arena.getNode(sym.ast_node);
                        var const_ty: TypeId = .err_ty;
                        if (c_node.lhs.tag == .node) {
                            const_ty = try self.resolveTypeAst(NodeIndex.fromInt(c_node.lhs.payload));
                        } else if (c_node.rhs.tag == .node) {
                            self.pure_comptime_depth += 1;
                            defer self.pure_comptime_depth -= 1;
                            const_ty = try self.synthExpr(NodeIndex.fromInt(c_node.rhs.payload));
                            if (const_ty == .untyped_int_ty) const_ty = .i32_ty;
                            if (const_ty == .untyped_float_ty) const_ty = .f64_ty;
                        }
                        self.sym_table.getSymbolMut(sym_idx).type_id = const_ty;
                    }
                },
                .fn_sym => {
                    try self.resolveFnSignatureSymbol(sym_idx);
                },
                else => {},
            }
        }
    }

    /// Binds `Self` to `nominal_ty` inside `target_scope` if not already defined.
    fn ensureSelfAliasInTargetScope(
        self: *TypeChecker,
        target_scope: ScopeId,
        nominal_ty: TypeId,
    ) !void {
        const self_sym_id = try self.interner.intern("Self");
        const existing = self.sym_table.lookupInScopeDirect(
            target_scope,
            self_sym_id,
            NamespaceMask.TYPE_ONLY,
        );
        if (!existing.isNone()) return;
        _ = try self.sym_table.defineSymbol(.{
            .name = self_sym_id,
            .name_text = self.interner.get(self_sym_id),
            .kind = .type_alias_sym,
            .namespace = .type_ns,
            .visibility = .private,
            .flags = .{ .is_used = true, .is_builtin = true },
            .scope_id = target_scope,
            .type_id = nominal_ty,
        }, null);
    }

    /// Extracts inner item AST indices from an inline `mod foo { … }` declaration.
    fn extractModInnerItemsSlice(self: *const TypeChecker, mod_node_idx: NodeIndex) []const u32 {
        const mod_node = self.ast_arena.getNode(mod_node_idx);
        if (mod_node.rhs.tag != .extra) return &.{};
        const start_extra: usize = mod_node.rhs.payload;
        if (start_extra >= self.ast_arena.extra_data.items.len) return &.{};
        var end_extra: usize = start_extra;
        while (end_extra < self.ast_arena.extra_data.items.len) : (end_extra += 1) {
            if (self.ast_arena.extra_data.items[end_extra] >= mod_node_idx.asInt()) break;
        }
        return self.ast_arena.extra_data.items[start_extra..end_extra];
    }

    /// Ensures a `.trait_sym` has a resolved `.trait_ty` in `self.pool` and `self.sym_table.type_to_symbol`.
    fn ensureTraitSymbolTypeId(self: *TypeChecker, trait_sym_idx: SymbolIndex) !TypeId {
        const sym = self.sym_table.getSymbol(trait_sym_idx).*;
        if (!sym.type_id.isError()) return sym.type_id;
        const trait_ty = try self.pool.internNominal(
            .trait_ty,
            sym.def_id.asInt(),
            trait_sym_idx,
            false,
            false,
            false,
        );
        self.sym_table.getSymbolMut(trait_sym_idx).type_id = trait_ty;
        try self.sym_table.type_to_symbol.put(self.allocator, trait_ty.toU32(), trait_sym_idx);
        return trait_ty;
    }

    /// Looks up a built-in or in-scope trait by `trait_name` and ensures its `.trait_ty` is interned.
    fn lookupAndEnsureTraitByName(self: *TypeChecker, trait_name: []const u8) !SymbolIndex {
        const sym_id = try self.interner.intern(trait_name);
        switch (self.sym_table.lookupLexical(self.current_scope, sym_id, NamespaceMask.TYPE_ONLY)) {
            .found => |sym_idx| {
                const sym = self.sym_table.getSymbol(sym_idx);
                if (sym.kind == .trait_sym) {
                    _ = try self.ensureTraitSymbolTypeId(sym_idx);
                    return sym_idx;
                }
            },
            else => {},
        }
        return .none;
    }

    /// Registers `(target_ty, trait_sym_idx)` pairs from `impl Trait for TargetType` declarations in `item_slice`.
    fn registerImplTraitPairsInItemSlice(
        self: *TypeChecker,
        enclosing_scope: ScopeId,
        item_slice: []const u32,
    ) !void {
        const saved_scope = self.current_scope;
        defer self.current_scope = saved_scope;

        for (item_slice) |raw_item_id| {
            const item_node_id = NodeIndex.fromInt(raw_item_id);
            if (item_node_id.isNone() or item_node_id.asInt() >= self.ast_arena.countNodes()) continue;
            const item_node = self.ast_arena.getNode(item_node_id);
            if (item_node.tag != .impl_decl) continue;

            const item_cst = self.ast_arena.getCstOrigin(item_node_id);
            if (item_cst.isNone() or item_cst.asInt() >= self.cst_arena.countNodes()) continue;
            const start_idx: usize = item_cst.asInt();
            const root_rec = self.cst_arena.getNode(item_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, root_rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );

            const impl_hdr_scope = try self.sym_table.scope_arena.allocScope(
                .impl_scope,
                enclosing_scope,
                .NONE,
                self.file_id,
                .{},
            );
            self.current_scope = impl_hdr_scope;

            var for_cst_pos: ?usize = null;
            var header_end_pos: usize = end_idx;
            var cursor: usize = start_idx + 1;
            while (cursor < end_idx) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
                if (sub.kind == .type_param) {
                    const param_end = @min(cursor + @max(@as(usize, sub.subtree_size), 1), end_idx);
                    try self.registerGenericTypeParamFromCst(impl_hdr_scope, cursor, param_end);
                    cursor = param_end;
                    continue;
                }
                const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
                if (is_leaf and !sub.flags.is_missing_or_injected and !sub.token.isNone() and
                    sub.token.asInt() < self.token_buffer.countTokens())
                {
                    const tok_kind = self.token_buffer.getToken(sub.token).kind;
                    if (tok_kind == .lbrace or tok_kind == .kw_where or tok_kind == .semi) {
                        header_end_pos = cursor;
                        break;
                    }
                    if (tok_kind == .kw_for and for_cst_pos == null) {
                        for_cst_pos = cursor;
                    }
                }
                cursor += 1;
            }

            if (for_cst_pos) |for_pos| {
                if (item_node.lhs.tag == .node) {
                    const trait_ty = try self.resolveTypeAst(NodeIndex.fromInt(item_node.lhs.payload));
                    const target_ast = self.findFirstAstInCstRange(for_pos + 1, header_end_pos);
                    if (!trait_ty.isError() and !target_ast.isNone()) {
                        const target_ty = try self.resolveTypeAst(target_ast);
                        if (!target_ty.isError()) {
                            if (self.sym_table.type_to_symbol.get(trait_ty.toU32())) |trait_sym_idx| {
                                try self.sym_table.trait_impl_pairs.put(
                                    self.sym_table.allocator,
                                    packTraitImplPair(target_ty, trait_sym_idx),
                                    {},
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// Registers Two-Phase `@derive(Eq, Hash, Debug, Clone)` trait headers and method signatures (`DR-05` §2.2).
    fn registerDerivedTraitHeaders(self: *TypeChecker, nominal_sym_idx: SymbolIndex) !void {
        const nom_sym = self.sym_table.getSymbol(nominal_sym_idx).*;
        if (nom_sym.type_id.isError() or nom_sym.target_scope.isNone()) return;

        const self_ref_ty = try self.pool.internRef(nom_sym.type_id, false);
        const DerivedSpec = struct {
            is_enabled: bool,
            trait_name: []const u8,
            method_name: []const u8,
            has_other_param: bool,
            ret_ty: TypeId,
        };
        const specs = [4]DerivedSpec{
            .{
                .is_enabled = nom_sym.derive_mask.has_eq,
                .trait_name = "Eq",
                .method_name = "eq",
                .has_other_param = true,
                .ret_ty = .bool_ty,
            },
            .{
                .is_enabled = nom_sym.derive_mask.has_hash,
                .trait_name = "Hash",
                .method_name = "hash",
                .has_other_param = false,
                .ret_ty = .u64_ty,
            },
            .{
                .is_enabled = nom_sym.derive_mask.has_debug,
                .trait_name = "Debug",
                .method_name = "debug",
                .has_other_param = false,
                .ret_ty = .str_ty,
            },
            .{
                .is_enabled = nom_sym.derive_mask.has_clone,
                .trait_name = "Clone",
                .method_name = "clone",
                .has_other_param = false,
                .ret_ty = nom_sym.type_id,
            },
        };

        for (specs) |spec| {
            if (!spec.is_enabled) continue;
            const trait_sym_idx = try self.lookupAndEnsureTraitByName(spec.trait_name);
            if (!trait_sym_idx.isNone()) {
                try self.sym_table.trait_impl_pairs.put(
                    self.sym_table.allocator,
                    packTraitImplPair(nom_sym.type_id, trait_sym_idx),
                    {},
                );
            }

            const method_sym_id = try self.interner.intern(spec.method_name);
            const existing_method = self.sym_table.lookupInScopeDirect(
                nom_sym.target_scope,
                method_sym_id,
                NamespaceMask.VALUE_ONLY,
            );
            if (!existing_method.isNone()) continue;

            const two_params = [2]TypeId{ self_ref_ty, self_ref_ty };
            const two_modes = [2]ParamMode{ .let_mode, .let_mode };
            const param_len: usize = if (spec.has_other_param) 2 else 1;
            const method_fn_ty = try self.pool.internFn(
                .fn_ty,
                two_params[0..param_len],
                two_modes[0..param_len],
                spec.ret_ty,
                false,
            );
            _ = try self.sym_table.defineSymbol(.{
                .name = method_sym_id,
                .name_text = self.interner.get(method_sym_id),
                .kind = .fn_sym,
                .namespace = .value_ns,
                .visibility = if (nom_sym.flags.is_pub) .public else .private,
                .flags = .{
                    .is_pub = nom_sym.flags.is_pub,
                    .is_used = true,
                    .is_prototype_only = true,
                },
                .scope_id = nom_sym.target_scope,
                .owner_def_id = nom_sym.def_id,
                .decl_span = nom_sym.decl_span,
                .type_id = method_fn_ty,
            }, null);
        }
    }

    /// Recursively verifies `@attribute_schema` rules, `@derive` member bounds, and user `@Schema(...)` attributes.
    fn verifyScopeDerivesAndAttributesRecursive(self: *TypeChecker, scope_id: ScopeId) anyerror!void {
        const saved_scope = self.current_scope;
        self.current_scope = scope_id;
        defer self.current_scope = saved_scope;

        const members_copy = try self.allocator.dupe(
            SymbolIndex,
            self.sym_table.getScopeMembers(scope_id),
        );
        defer self.allocator.free(members_copy);

        for (members_copy) |sym_idx| {
            const sym = self.sym_table.getSymbol(sym_idx).*;
            if (sym.flags.is_builtin or sym.flags.is_imported) continue;

            if (sym.flags.is_attribute_schema) {
                try self.validateAttributeSchemaDecl(sym_idx);
            }
            if (sym.derive_mask.hasAny()) {
                try self.verifyDerivedTraitMemberBounds(sym_idx);
            }
            try self.validateSymbolAttributes(sym_idx, sym.def_id);

            switch (sym.kind) {
                .module_sym => {
                    if (!sym.target_scope.isNone()) {
                        try self.verifyScopeDerivesAndAttributesRecursive(sym.target_scope);
                    }
                },
                .struct_sym, .union_sym, .bit_field_sym, .enum_sym, .trait_sym => {
                    if (!sym.target_scope.isNone()) {
                        const child_members = try self.allocator.dupe(
                            SymbolIndex,
                            self.sym_table.getScopeMembers(sym.target_scope),
                        );
                        defer self.allocator.free(child_members);
                        for (child_members) |child_idx| {
                            const child_sym = self.sym_table.getSymbol(child_idx).*;
                            if (child_sym.flags.is_builtin or child_sym.flags.is_imported) continue;
                            if (child_sym.kind == .field_sym or child_sym.kind == .enum_variant_sym) {
                                try self.validateSymbolAttributes(child_idx, sym.def_id);
                            } else if (child_sym.kind == .fn_sym) {
                                try self.validateSymbolAttributes(child_idx, child_sym.def_id);
                            }
                        }
                    }
                },
                else => {},
            }
        }
    }

    /// Validates an `@attribute_schema` declaration, rejecting raw pointers, `&mut`, and closures (`E0503`).
    fn validateAttributeSchemaDecl(self: *TypeChecker, sym_idx: SymbolIndex) !void {
        const sym = self.sym_table.getSymbol(sym_idx).*;
        if (sym.kind != .struct_sym) {
            try self.emitDiagnosticSimple(
                .e0503_forbidden_comptime_operation,
                sym.decl_span,
                "`@attribute_schema` is only permitted on `struct` declarations",
                "only value `struct` declarations can define attribute schemas",
            );
            return;
        }
        if (sym.target_scope.isNone()) return;
        for (self.sym_table.getScopeMembers(sym.target_scope)) |member_idx| {
            const member_sym = self.sym_table.getSymbol(member_idx).*;
            if (member_sym.kind != .field_sym) continue;
            if (!self.isAllowedAttributeSchemaFieldType(member_sym.type_id, 0)) {
                try self.emitDiagnosticSimple(
                    .e0503_forbidden_comptime_operation,
                    member_sym.decl_span,
                    "`@attribute_schema` field cannot contain raw pointers, `&mut` references, or function/closure types",
                    "disallowed field type in `@attribute_schema` struct",
                );
            }
        }
    }

    /// Returns `true` if `ty` is a pure compile-time metadata value type permitted in `@attribute_schema`.
    fn isAllowedAttributeSchemaFieldType(self: *const TypeChecker, ty: TypeId, depth: u32) bool {
        if (ty.isError() or depth >= MAX_TYPE_DEPTH) return true;
        if (ty.isPrimitive()) return ty != .never_ty;
        const node = self.pool.getNode(ty);
        return switch (node.tag) {
            .raw_ptr_ty, .mut_ref_ty, .fn_ty, .closure_ty => false,
            .ref_ty, .slice_ty, .soa_slice_ty, .array_ty, .soa_array_ty, .optional_ty => self.isAllowedAttributeSchemaFieldType(
                TypeId.fromInt(node.lhs),
                depth + 1,
            ),
            .result_ty => self.isAllowedAttributeSchemaFieldType(TypeId.fromInt(node.lhs), depth + 1) and
                self.isAllowedAttributeSchemaFieldType(TypeId.fromInt(node.rhs), depth + 1),
            .tuple_ty => blk: {
                for (self.pool.getTupleElements(ty)) |raw_elem| {
                    if (!self.isAllowedAttributeSchemaFieldType(TypeId.fromInt(raw_elem), depth + 1)) {
                        break :blk false;
                    }
                }
                break :blk true;
            },
            .distinct_ty => self.isAllowedAttributeSchemaFieldType(TypeId.fromInt(node.lhs), depth + 1),
            .refined_ty => self.isAllowedAttributeSchemaFieldType(TypeId.fromInt(node.rhs), depth + 1),
            .struct_ty, .union_ty => blk: {
                const nom_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                if (nom_sym.target_scope.isNone()) break :blk true;
                for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |field_idx| {
                    const field_sym = self.sym_table.getSymbol(field_idx).*;
                    if (field_sym.kind != .field_sym) continue;
                    if (!self.isAllowedAttributeSchemaFieldType(field_sym.type_id, depth + 1)) {
                        break :blk false;
                    }
                }
                break :blk true;
            },
            .enum_ty => blk: {
                const enum_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                if (enum_sym.target_scope.isNone()) break :blk true;
                for (self.sym_table.getScopeMembers(enum_sym.target_scope)) |var_idx| {
                    const var_sym = self.sym_table.getSymbol(var_idx).*;
                    if (var_sym.kind != .enum_variant_sym or var_sym.type_id == .unit_ty) continue;
                    if (!self.isAllowedAttributeSchemaFieldType(var_sym.type_id, depth + 1)) {
                        break :blk false;
                    }
                }
                break :blk true;
            },
            else => true,
        };
    }

    /// Verifies that all struct fields / enum variant payloads satisfy each requested `@derive` trait (`E0402`).
    fn verifyDerivedTraitMemberBounds(self: *TypeChecker, nominal_sym_idx: SymbolIndex) !void {
        const nom_sym = self.sym_table.getSymbol(nominal_sym_idx).*;
        if (nom_sym.target_scope.isNone()) return;

        // Validate unknown trait identifiers inside `@derive(...)`:
        if (!nom_sym.cst_node.isNone() and nom_sym.cst_node.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = nom_sym.cst_node.asInt();
            const root_rec = self.cst_arena.getNode(nom_sym.cst_node);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, root_rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var cur = start_idx + 1;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                const is_lbrace_leaf = sub.subtree_size <= 1 and !sub.token.isNone() and
                    sub.token.asInt() < self.token_buffer.countTokens() and
                    self.token_buffer.getToken(sub.token).kind == .lbrace;
                if (is_lbrace_leaf or sub.kind == .struct_introducer or
                    sub.kind == .enum_introducer or sub.kind == .union_introducer) break;
                if (sub.kind == .attribute) {
                    const attr_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                    try self.checkDeriveTraitNamesInAttrCst(cur, attr_end);
                    if (sub.subtree_size > 1) cur += @as(usize, sub.subtree_size) - 1;
                }
            }
        }

        const TraitCheck = struct { is_enabled: bool, name: []const u8 };
        const checks = [4]TraitCheck{
            .{ .is_enabled = nom_sym.derive_mask.has_eq, .name = "Eq" },
            .{ .is_enabled = nom_sym.derive_mask.has_hash, .name = "Hash" },
            .{ .is_enabled = nom_sym.derive_mask.has_debug, .name = "Debug" },
            .{ .is_enabled = nom_sym.derive_mask.has_clone, .name = "Clone" },
        };

        for (checks) |chk| {
            if (!chk.is_enabled) continue;
            const trait_sym_idx = try self.lookupAndEnsureTraitByName(chk.name);
            if (trait_sym_idx.isNone()) continue;
            const trait_ty = self.sym_table.getSymbol(trait_sym_idx).type_id;

            for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |member_idx| {
                const member_sym = self.sym_table.getSymbol(member_idx).*;
                if (member_sym.kind != .field_sym and member_sym.kind != .enum_variant_sym) continue;
                if (member_sym.kind == .enum_variant_sym and member_sym.type_id == .unit_ty) continue;
                if (!(try self.hasTraitImplementation(member_sym.type_id, trait_ty, 0))) {
                    var ty_buf: [96]u8 = undefined;
                    const member_ty_str = self.pool.formatType(member_sym.type_id, self.sym_table, &ty_buf);
                    var msg_buf: [200]u8 = undefined;
                    const msg = std.fmt.bufPrint(
                        &msg_buf,
                        "cannot `@derive({s})`: member `{s}` of type `{s}` does not implement `{s}`",
                        .{ chk.name, member_sym.name_text, member_ty_str, chk.name },
                    ) catch "cannot `@derive`: member type does not implement derived trait";
                    try self.emitDiagnosticSimple(
                        .e0402_unsatisfied_trait_bound,
                        member_sym.decl_span,
                        msg,
                        "member type does not satisfy derived trait bound",
                    );
                }
            }
        }
    }

    /// Checks that every identifier passed to `@derive(...)` resolves to a known trait (`E0403` / `E0402`).
    fn checkDeriveTraitNamesInAttrCst(self: *TypeChecker, attr_start: usize, attr_end: usize) !void {
        var has_seen_derive = false;
        var cur = attr_start + 1;
        while (cur < attr_end) : (cur += 1) {
            const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (leaf.subtree_size > 1 or leaf.token.isNone() or
                leaf.token.asInt() >= self.token_buffer.countTokens()) continue;
            const kind = self.token_buffer.getToken(leaf.token).kind;
            if (!symbol_resolver.isIdentifierToken(kind)) continue;
            const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, leaf.token);
            if (!has_seen_derive) {
                if (!std.mem.eql(u8, lex, "derive")) return;
                has_seen_derive = true;
                continue;
            }
            const sym_id = try self.interner.intern(lex);
            const span = self.token_buffer.getTokenSpan(self.file_id, leaf.token);
            switch (self.sym_table.lookupLexical(self.current_scope, sym_id, NamespaceMask.TYPE_ONLY)) {
                .found => |found_idx| {
                    if (self.sym_table.getSymbol(found_idx).kind != .trait_sym) {
                        try self.emitDiagnosticSimple(
                            .e0402_unsatisfied_trait_bound,
                            span,
                            "`@derive(...)` argument must be a trait",
                            "expected trait identifier here",
                        );
                    }
                },
                else => {
                    if (self.diagnostic_sink) |sink| {
                        try symbol_resolver.emitUnresolvedSymbolDiagnostic(
                            sink,
                            self.interner,
                            lex,
                            span,
                            self.sym_table.suggestClosestSymbol(
                                self.current_scope,
                                lex,
                                NamespaceMask.TYPE_ONLY,
                            ),
                        );
                    }
                },
            }
        }
    }

    /// Returns `true` if `target_ty` implements `trait_ty` (`impl Trait for T`, `@derive`, or built-in capability).
    pub fn hasTraitImplementation(
        self: *TypeChecker,
        target_ty: TypeId,
        trait_ty: TypeId,
        depth: u32,
    ) anyerror!bool {
        if (target_ty.isError() or trait_ty.isError() or depth >= MAX_TYPE_DEPTH) return true;
        if (target_ty == .never_ty) return true;
        const bound_ty = self.pool.unwrapUnderlyingType(trait_ty);
        if (bound_ty.isBuiltinGroup() or self.pool.getTag(bound_ty) == .user_group) {
            const sat = checkGroupSatisfaction(self.pool, target_ty, bound_ty);
            return sat != .rejected and sat != .rejected_distinct_without_tilde;
        }

        const trait_sym_idx = self.sym_table.type_to_symbol.get(bound_ty.toU32()) orelse return false;
        if (self.sym_table.trait_impl_pairs.contains(packTraitImplPair(target_ty, trait_sym_idx))) {
            return true;
        }

        const trait_sym = self.sym_table.getSymbol(trait_sym_idx).*;
        const target_node = self.pool.getNode(target_ty);
        if (target_node.tag == .refined_ty) {
            return self.hasTraitImplementation(TypeId.fromInt(target_node.rhs), trait_ty, depth + 1);
        }

        if (!trait_sym.flags.is_builtin) return false;
        const t_name = trait_sym.name_text;

        if (std.mem.eql(u8, t_name, "Send") or std.mem.eql(u8, t_name, "Sync")) {
            return target_node.tag != .raw_ptr_ty;
        }
        if (std.mem.eql(u8, t_name, "Default")) {
            return switch (target_node.tag) {
                .primitive => target_ty != .never_ty,
                .optional_ty => true,
                .array_ty => (target_node.rhs & SYMBOLIC_ARRAY_LEN_FLAG) == 0 and
                    try self.hasTraitImplementation(TypeId.fromInt(target_node.lhs), trait_ty, depth + 1),
                .tuple_ty => blk: {
                    for (self.pool.getTupleElements(target_ty)) |raw_elem| {
                        if (!(try self.hasTraitImplementation(TypeId.fromInt(raw_elem), trait_ty, depth + 1))) {
                            break :blk false;
                        }
                    }
                    break :blk true;
                },
                else => false,
            };
        }

        const is_eq = std.mem.eql(u8, t_name, "Eq");
        const is_hash = std.mem.eql(u8, t_name, "Hash");
        const is_debug = std.mem.eql(u8, t_name, "Debug") or std.mem.eql(u8, t_name, "Display");
        const is_clone = std.mem.eql(u8, t_name, "Clone");
        const is_ord = std.mem.eql(u8, t_name, "Ord");
        if (!is_eq and !is_hash and !is_debug and !is_clone and !is_ord) return false;

        return switch (target_node.tag) {
            .primitive => if (target_ty.isFloatPrimitive()) !is_hash else true,
            .raw_ptr_ty => !is_ord,
            .fn_ty => is_clone,
            .ref_ty => if (is_clone)
                true
            else
                self.hasTraitImplementation(TypeId.fromInt(target_node.lhs), trait_ty, depth + 1),
            .mut_ref_ty => if (is_clone)
                false
            else
                self.hasTraitImplementation(TypeId.fromInt(target_node.lhs), trait_ty, depth + 1),
            .slice_ty, .soa_slice_ty => if (is_clone)
                true
            else
                self.hasTraitImplementation(TypeId.fromInt(target_node.lhs), trait_ty, depth + 1),
            .array_ty, .soa_array_ty, .optional_ty => self.hasTraitImplementation(
                TypeId.fromInt(target_node.lhs),
                trait_ty,
                depth + 1,
            ),
            .result_ty => (try self.hasTraitImplementation(
                TypeId.fromInt(target_node.lhs),
                trait_ty,
                depth + 1,
            )) and (try self.hasTraitImplementation(
                TypeId.fromInt(target_node.rhs),
                trait_ty,
                depth + 1,
            )),
            .tuple_ty => blk: {
                for (self.pool.getTupleElements(target_ty)) |raw_elem| {
                    if (!(try self.hasTraitImplementation(TypeId.fromInt(raw_elem), trait_ty, depth + 1))) {
                        break :blk false;
                    }
                }
                break :blk true;
            },
            else => false,
        };
    }

    /// Validates user `@Schema(...)` attributes attached to `target_sym_idx`, populating `self.attr_instances`.
    fn validateSymbolAttributes(
        self: *TypeChecker,
        target_sym_idx: SymbolIndex,
        owner_def_id: DefId,
    ) !void {
        const target_sym = self.sym_table.getSymbol(target_sym_idx).*;
        if (target_sym.cst_node.isNone() or target_sym.cst_node.asInt() >= self.cst_arena.countNodes()) return;

        const start_idx: usize = target_sym.cst_node.asInt();
        const root_rec = self.cst_arena.getNode(target_sym.cst_node);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, root_rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );

        var cur = start_idx + 1;
        while (cur < end_idx) : (cur += 1) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.kind == .struct_introducer or sub.kind == .enum_introducer or
                sub.kind == .union_introducer or sub.kind == .fn_introducer or
                sub.kind == .type_alias_introducer or sub.kind == .const_introducer or
                sub.kind == .block) break;
            if (sub.subtree_size <= 1 and !sub.token.isNone() and
                sub.token.asInt() < self.token_buffer.countTokens())
            {
                const leaf_kind = self.token_buffer.getToken(sub.token).kind;
                if (leaf_kind == .colon or leaf_kind == .lbrace or leaf_kind == .lparen) break;
            }
            if (sub.kind == .attribute) {
                const attr_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                try self.validateSingleAttributeCst(target_sym_idx, owner_def_id, cur, attr_end);
                if (sub.subtree_size > 1) cur += @as(usize, sub.subtree_size) - 1;
            }
        }
    }

    /// Validates a single CST `.attribute` subtree `[attr_start .. attr_end)` against an `@attribute_schema` struct.
    fn validateSingleAttributeCst(
        self: *TypeChecker,
        target_sym_idx: SymbolIndex,
        owner_def_id: DefId,
        attr_start: usize,
        attr_end: usize,
    ) !void {
        var name_tok: TokenIndex = .none;
        var name_leaf_pos: usize = attr_start + 1;
        while (name_leaf_pos < attr_end) : (name_leaf_pos += 1) {
            const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(name_leaf_pos)));
            if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                leaf.token.asInt() < self.token_buffer.countTokens())
            {
                const kind = self.token_buffer.getToken(leaf.token).kind;
                if (symbol_resolver.isIdentifierToken(kind)) {
                    name_tok = leaf.token;
                    break;
                }
            }
        }
        if (name_tok.isNone()) return;

        const attr_name = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, name_tok);
        if (attr_name.len == 0 or BUILTIN_ATTRIBUTE_MAP.has(attr_name)) return;

        const attr_span = self.token_buffer.getTokenSpan(self.file_id, name_tok);
        const schema_sym_idx = try self.lookupAttributeSchemaSymbol(attr_name);
        if (schema_sym_idx.isNone()) {
            if (self.diagnostic_sink) |sink| {
                try symbol_resolver.emitUnresolvedSymbolDiagnostic(
                    sink,
                    self.interner,
                    attr_name,
                    attr_span,
                    self.sym_table.suggestClosestSymbol(
                        self.current_scope,
                        attr_name,
                        NamespaceMask.TYPE_ONLY,
                    ),
                );
            }
            return;
        }

        const schema_sym = self.sym_table.getSymbol(schema_sym_idx).*;
        if (schema_sym.kind != .struct_sym or !schema_sym.flags.is_attribute_schema) {
            try self.emitDiagnosticSimple(
                .e0503_forbidden_comptime_operation,
                attr_span,
                "type used as `@attribute` is not annotated with `@attribute_schema`",
                "add `@attribute_schema` to this struct declaration to use it as an attribute",
            );
            return;
        }

        const target_sym = self.sym_table.getSymbol(target_sym_idx).*;
        const is_target_allowed = switch (target_sym.kind) {
            .struct_sym => schema_sym.attr_target_mask.has_struct_target,
            .enum_sym => schema_sym.attr_target_mask.has_enum_target,
            .union_sym => schema_sym.attr_target_mask.has_union_target,
            .field_sym => schema_sym.attr_target_mask.has_field_target,
            .enum_variant_sym => schema_sym.attr_target_mask.has_variant_target,
            .fn_sym => schema_sym.attr_target_mask.has_fn_target,
            .param_sym => schema_sym.attr_target_mask.has_param_target,
            .local_let_sym, .local_var_sym => schema_sym.attr_target_mask.has_local_target,
            else => true,
        };
        if (!is_target_allowed) {
            var msg_buf: [192]u8 = undefined;
            const msg = std.fmt.bufPrint(
                &msg_buf,
                "attribute `@{s}` is not permitted on this declaration target",
                .{attr_name},
            ) catch "attribute is not permitted on this declaration target";
            try self.emitDiagnosticSimple(
                .e0401_type_mismatch,
                attr_span,
                msg,
                "disallowed target for `@attribute_schema(targets = …)`",
            );
            return;
        }

        if (schema_sym.target_scope.isNone()) return;
        var schema_fields: std.ArrayListUnmanaged(SymbolIndex) = .empty;
        defer schema_fields.deinit(self.allocator);
        for (self.sym_table.getScopeMembers(schema_sym.target_scope)) |mem_idx| {
            if (self.sym_table.getSymbol(mem_idx).kind == .field_sym) {
                try schema_fields.append(self.allocator, mem_idx);
            }
        }
        const schema_field_count = schema_fields.items.len;

        const supplied_values = try self.allocator.alloc(?AttrArgValue, schema_field_count);
        defer if (supplied_values.len > 0) self.allocator.free(supplied_values);
        @memset(supplied_values, null);
        var arg_cursor = name_leaf_pos + 1;
        var positional_idx: usize = 0;
        self.pure_comptime_depth += 1;
        defer self.pure_comptime_depth -= 1;

        // Advance past opening `(` if present:
        var has_open_paren = false;
        while (arg_cursor < attr_end) : (arg_cursor += 1) {
            const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(arg_cursor)));
            if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                leaf.token.asInt() < self.token_buffer.countTokens() and
                self.token_buffer.getToken(leaf.token).kind == .lparen)
            {
                has_open_paren = true;
                arg_cursor += 1;
                break;
            }
        }

        if (has_open_paren) {
            while (arg_cursor < attr_end) {
                // Find next top-level `,` or `)` boundary in `[arg_cursor .. attr_end)`:
                var seg_end = arg_cursor;
                var paren_depth: u32 = 0;
                while (seg_end < attr_end) : (seg_end += 1) {
                    const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(seg_end)));
                    if (sub.subtree_size <= 1 and !sub.token.isNone() and
                        sub.token.asInt() < self.token_buffer.countTokens())
                    {
                        const tok_kind = self.token_buffer.getToken(sub.token).kind;
                        if (tok_kind == .lparen or tok_kind == .lbracket or tok_kind == .lbrace) {
                            paren_depth += 1;
                        } else if (tok_kind == .rparen or tok_kind == .rbracket or tok_kind == .rbrace) {
                            if (paren_depth == 0) break;
                            paren_depth -= 1;
                        } else if (tok_kind == .comma and paren_depth == 0) {
                            break;
                        }
                    }
                }
                if (seg_end > arg_cursor) {
                    try self.checkAttributeArgumentSegment(
                        schema_sym.target_scope,
                        schema_fields.items,
                        supplied_values,
                        &positional_idx,
                        arg_cursor,
                        seg_end,
                    );
                }
                if (seg_end >= attr_end) break;
                const delim_sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(seg_end)));
                if (delim_sub.subtree_size <= 1 and !delim_sub.token.isNone() and
                    delim_sub.token.asInt() < self.token_buffer.countTokens() and
                    self.token_buffer.getToken(delim_sub.token).kind == .rparen) break;
                arg_cursor = seg_end + 1;
            }
        }

        var resolved_fields = try self.allocator.alloc(AttrFieldInit, schema_field_count);
        errdefer if (resolved_fields.len > 0) self.allocator.free(resolved_fields);

        for (schema_fields.items, 0..) |field_sym_idx, i| {
            const field_sym = self.sym_table.getSymbol(field_sym_idx).*;
            const val_opt = supplied_values[i] orelse try self.extractFieldDefaultAttrValue(field_sym);
            if (val_opt) |attr_val| {
                resolved_fields[i] = .{
                    .field_name = field_sym.name,
                    .field_ordinal = @intCast(i),
                    .value = attr_val,
                };
            } else {
                var msg_buf: [192]u8 = undefined;
                const msg = std.fmt.bufPrint(
                    &msg_buf,
                    "missing required field `{s}` in `@{s}` attribute",
                    .{ field_sym.name_text, attr_name },
                ) catch "missing required field in attribute";
                try self.emitDiagnosticSimple(
                    .e0401_type_mismatch,
                    attr_span,
                    msg,
                    "required `@attribute_schema` field was not supplied",
                );
                resolved_fields[i] = .{
                    .field_name = field_sym.name,
                    .field_ordinal = @intCast(i),
                    .value = .none_opt,
                };
            }
        }

        try self.attr_instances.append(self.allocator, .{
            .schema_type_id = schema_sym.type_id,
            .target_symbol = target_sym_idx,
            .owner_def_id = owner_def_id,
            .attr_span = attr_span,
            .fields = resolved_fields,
        });
    }

    /// Resolves `attr_name` (`@ArgAttr`, `@arg`, `@cli_command`) to its schema `SymbolIndex` in `type_ns`.
    fn lookupAttributeSchemaSymbol(self: *TypeChecker, attr_name: []const u8) !SymbolIndex {
        const direct_id = try self.interner.intern(attr_name);
        if (self.sym_table.lookupLexical(self.current_scope, direct_id, NamespaceMask.TYPE_ONLY) == .found) {
            return self.sym_table.lookupLexical(self.current_scope, direct_id, NamespaceMask.TYPE_ONLY).found;
        }
        if (attr_name.len > 0 and attr_name[0] >= 'a' and attr_name[0] <= 'z') {
            var pascal_buf: [120]u8 = undefined;
            const pascal_name = toPascalCase(attr_name, &pascal_buf);
            var suffixed_buf: [128]u8 = undefined;
            if (std.fmt.bufPrint(&suffixed_buf, "{s}Attr", .{pascal_name})) |with_attr| {
                const suffixed_id = try self.interner.intern(with_attr);
                switch (self.sym_table.lookupLexical(
                    self.current_scope,
                    suffixed_id,
                    NamespaceMask.TYPE_ONLY,
                )) {
                    .found => |found_idx| return found_idx,
                    else => {},
                }
            } else |_| {}

            const pascal_id = try self.interner.intern(pascal_name);
            switch (self.sym_table.lookupLexical(self.current_scope, pascal_id, NamespaceMask.TYPE_ONLY)) {
                .found => |found_idx| return found_idx,
                else => {},
            }
        }
        return .none;
    }

    /// Validates one `name = expr` or positional `expr` segment inside an `@Schema(...)` call.
    fn checkAttributeArgumentSegment(
        self: *TypeChecker,
        schema_scope: ScopeId,
        schema_fields: []const SymbolIndex,
        supplied_values: []?AttrArgValue,
        positional_idx: *usize,
        seg_start: usize,
        seg_end: usize,
    ) !void {
        var named_tok: TokenIndex = .none;
        var expr_search_start = seg_start;

        var cur = seg_start;
        while (cur < seg_end) : (cur += 1) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.subtree_size > 1) break;
            if (sub.token.isNone() or sub.token.asInt() >= self.token_buffer.countTokens()) continue;
            const kind = self.token_buffer.getToken(sub.token).kind;
            if (named_tok.isNone() and symbol_resolver.isIdentifierToken(kind)) {
                named_tok = sub.token;
            } else if (!named_tok.isNone() and (kind == .eq or kind == .colon)) {
                expr_search_start = cur + 1;
                break;
            } else {
                named_tok = .none;
                break;
            }
        }
        if (expr_search_start == seg_start) named_tok = .none;

        const expr_ast_id = self.findFirstAstInCstRange(expr_search_start, seg_end);
        if (expr_ast_id.isNone()) return;

        var target_field_slot: ?usize = null;
        if (!named_tok.isNone()) {
            const field_lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, named_tok);
            const field_sym_id = try self.interner.intern(field_lex);
            const found_field = self.sym_table.lookupInScopeDirect(
                schema_scope,
                field_sym_id,
                NamespaceMask.VALUE_ONLY,
            );
            if (found_field.isNone()) {
                if (self.diagnostic_sink) |sink| {
                    try symbol_resolver.emitUnresolvedSymbolDiagnostic(
                        sink,
                        self.interner,
                        field_lex,
                        self.token_buffer.getTokenSpan(self.file_id, named_tok),
                        self.sym_table.suggestClosestInScope(
                            schema_scope,
                            field_lex,
                            NamespaceMask.VALUE_ONLY,
                        ),
                    );
                }
                _ = try self.synthExpr(expr_ast_id);
                return;
            }
            for (schema_fields, 0..) |cand_field_idx, i| {
                if (cand_field_idx == found_field) {
                    target_field_slot = i;
                    break;
                }
            }
        } else {
            if (positional_idx.* < schema_fields.len) {
                target_field_slot = positional_idx.*;
            }
            positional_idx.* += 1;
        }

        if (target_field_slot) |slot_i| {
            const expected_ty = self.sym_table.getSymbol(schema_fields[slot_i]).type_id;
            _ = try self.checkExpr(expr_ast_id, expected_ty);
            supplied_values[slot_i] = try self.evalAttrArgValue(expr_ast_id, expected_ty);
        } else {
            _ = try self.synthExpr(expr_ast_id);
        }
    }

    /// Evaluates a `.struct_field`'s optional `= default_expr` into an `AttrArgValue`, or returns `null`.
    fn extractFieldDefaultAttrValue(self: *TypeChecker, field_sym: SymbolRecord) !?AttrArgValue {
        if (field_sym.cst_node.isNone() or field_sym.cst_node.asInt() >= self.cst_arena.countNodes()) return null;
        const start_idx: usize = field_sym.cst_node.asInt();
        const rec = self.cst_arena.getNode(field_sym.cst_node);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, rec.subtree_size), 1),
            self.cst_arena.countNodes(),
        );
        var eq_pos: ?usize = null;
        var cur = start_idx + 1;
        while (cur < end_idx) : (cur += 1) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.subtree_size <= 1 and !sub.token.isNone() and
                sub.token.asInt() < self.token_buffer.countTokens() and
                self.token_buffer.getToken(sub.token).kind == .eq)
            {
                eq_pos = cur;
                break;
            }
        }
        const found_eq = eq_pos orelse return null;
        const default_ast = self.findFirstAstInCstRange(found_eq + 1, end_idx);
        if (default_ast.isNone()) return null;
        return try self.evalAttrArgValue(default_ast, field_sym.type_id);
    }

    /// Evaluates a typechecked attribute argument AST node into a scalar `AttrArgValue`.
    fn evalAttrArgValue(self: *TypeChecker, expr_id: NodeIndex, expected_ty: TypeId) !AttrArgValue {
        if (expr_id.isNone() or expr_id.asInt() >= self.ast_arena.countNodes()) return .none_opt;
        const expr_node = self.ast_arena.getNode(expr_id);
        switch (expr_node.tag) {
            .bool_lit => {
                const is_true = !expr_node.main_token.isNone() and
                    self.token_buffer.getToken(expr_node.main_token).kind == .kw_true;
                return .{ .bool_val = is_true };
            },
            .char_lit => {
                const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, expr_node.main_token);
                return .{ .char_val = extractCharLiteralCodepoint(lex) orelse 0 };
            },
            .string_lit => {
                const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, expr_node.main_token);
                if (extractRawStringContent(lex)) |raw_body| {
                    return .{ .str_val = try self.interner.intern(raw_body) };
                }
                const inner = if (lex.len >= 2 and lex[0] == '"' and lex[lex.len - 1] == '"')
                    lex[1 .. lex.len - 1]
                else
                    lex;
                const decoded = try decodeStandardStringSegment(self.allocator, inner);
                defer self.allocator.free(decoded);
                return .{ .str_val = try self.interner.intern(decoded) };
            },
            .contextual_variant => {
                const var_tok = if (expr_node.lhs.tag == .token)
                    TokenIndex.fromInt(expr_node.lhs.payload)
                else
                    expr_node.main_token;
                const var_name = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, var_tok);
                const unwrapped_exp = self.pool.unwrapUnderlyingType(expected_ty);
                const exp_node = self.pool.getNode(unwrapped_exp);
                if (exp_node.tag == .optional_ty) {
                    if (std.mem.eql(u8, var_name, "None")) return .none_opt;
                    if (std.mem.eql(u8, var_name, "Some")) {
                        const arg_nodes = self.getNodeExtraSlice(expr_id, true);
                        if (arg_nodes.len == 1) {
                            return self.evalAttrArgValue(
                                NodeIndex.fromInt(arg_nodes[0]),
                                TypeId.fromInt(exp_node.lhs),
                            );
                        }
                    }
                }
                const target_enum_ty = if (exp_node.tag == .optional_ty)
                    self.pool.unwrapUnderlyingType(TypeId.fromInt(exp_node.lhs))
                else
                    unwrapped_exp;
                const target_enum_node = self.pool.getNode(target_enum_ty);
                if (target_enum_node.tag == .enum_ty) {
                    const enum_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(target_enum_node.rhs)).*;
                    if (!enum_sym.target_scope.isNone()) {
                        if (self.interner.lookup(var_name)) |var_sym_id| {
                            const found_v = self.sym_table.lookupInScopeDirect(
                                enum_sym.target_scope,
                                var_sym_id,
                                NamespaceMask.VALUE_ONLY,
                            );
                            if (!found_v.isNone()) {
                                return .{ .enum_tag = self.sym_table.getSymbol(found_v).member_ordinal };
                            }
                        }
                    }
                }
                return .{ .enum_tag = 0 };
            },
            .float_lit => {
                const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, expr_node.main_token);
                return .{ .float_val = std.fmt.parseFloat(f64, lex) catch 0.0 };
            },
            else => {
                if (try self.evalConstIntExpr(expr_id, false)) |int_val| {
                    return .{ .int_val = int_val };
                }
                return .none_opt;
            },
        }
    }

    /// Resolves a `type` declaration symbol (`type_alias_sym`, `distinct_type_sym`, `refined_type_sym`, `type_group_sym`).
    fn resolveTypeAliasSymbol(self: *TypeChecker, sym_idx: SymbolIndex) anyerror!TypeId {
        const sym = self.sym_table.getSymbol(sym_idx).*;
        if (!sym.type_id.isError()) return sym.type_id;
        if (sym.ast_node.isNone()) return .err_ty;

        const ast_node = self.ast_arena.getNode(sym.ast_node);

        // [1] User-defined Constrained Type Group (`type G = A | ~B;`):
        if (ast_node.lhs.tag == .extra and ast_node.rhs.tag == .extra) {
            const member_slice = self.ast_arena.getExtraSlice(
                ExtraIndex.fromInt(ast_node.lhs.payload),
                ast_node.rhs.payload,
            );
            var prim_mask: u32 = 0;
            var tilde_prim_mask: u32 = 0;
            var exact_members: std.ArrayListUnmanaged(u32) = .empty;
            defer exact_members.deinit(self.allocator);
            var tilde_members: std.ArrayListUnmanaged(u32) = .empty;
            defer tilde_members.deinit(self.allocator);

            for (member_slice) |raw_mem_ast| {
                const mem_ast_id = NodeIndex.fromInt(raw_mem_ast);
                const mem_ty = try self.resolveTypeAst(mem_ast_id);
                if (mem_ty.isError()) continue;

                const mem_node = self.pool.getNode(mem_ty);
                if (mem_node.tag == .tilde_approx) {
                    const inner_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(mem_node.lhs));
                    if (inner_ty.isPrimitive()) {
                        tilde_prim_mask |= inner_ty.primitiveBit();
                    } else if (inner_ty.isBuiltinGroup()) {
                        tilde_prim_mask |= TypeGroupMask.forBuiltinGroup(inner_ty);
                    } else {
                        try tilde_members.append(self.allocator, inner_ty.toU32());
                    }
                } else if (mem_ty.isPrimitive()) {
                    prim_mask |= mem_ty.primitiveBit();
                } else if (mem_ty.isBuiltinGroup()) {
                    prim_mask |= TypeGroupMask.forBuiltinGroup(mem_ty);
                } else if (self.pool.getUserGroupView(mem_ty)) |sub_view| {
                    prim_mask |= sub_view.prim_mask;
                    tilde_prim_mask |= sub_view.tilde_prim_mask;
                    try exact_members.appendSlice(self.allocator, sub_view.exact_members);
                    try tilde_members.appendSlice(self.allocator, sub_view.tilde_members);
                } else {
                    try exact_members.append(self.allocator, mem_ty.toU32());
                }
            }
            return self.pool.internUserGroup(
                sym_idx,
                prim_mask,
                tilde_prim_mask,
                exact_members.items,
                tilde_members.items,
            );
        }

        if (ast_node.lhs.tag != .node) return .err_ty;
        const target_ast_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const target_ast = self.ast_arena.getNode(target_ast_id);

        // [2] Nominal `distinct` newtype (`type Id = distinct u64;`):
        if (target_ast.tag == .mode_type) {
            const mode_lexeme = symbol_resolver.extractTokenSlice(
                self.source,
                self.token_buffer,
                target_ast.main_token,
            );
            if (std.mem.eql(u8, mode_lexeme, "distinct") and target_ast.lhs.tag == .node) {
                const base_ty = try self.resolveTypeAst(NodeIndex.fromInt(target_ast.lhs.payload));
                return self.pool.internDistinct(base_ty, sym_idx);
            }
        }

        const base_ty = try self.resolveTypeAst(target_ast_id);
        if (base_ty.isError()) return .err_ty;

        // [3] Range or pattern refinement (`type Port = u16 is 1024..=65535;`):
        if (ast_node.rhs.tag == .node) {
            const pat_node_id = NodeIndex.fromInt(ast_node.rhs.payload);
            if (self.extractPatternRangeBounds(pat_node_id)) |range| {
                // Verify refinement bounds fit within `base_ty`:
                const underlying_prim = self.pool.unwrapUnderlyingType(base_ty);
                if (getPrimitiveIntBounds(underlying_prim)) |prim_bounds| {
                    if (range.min_val > range.max_val or
                        range.min_val < prim_bounds.min_val or
                        range.max_val > prim_bounds.max_val)
                    {
                        try self.emitRangeRefinementError(
                            self.getAstNodeSpan(pat_node_id),
                            base_ty,
                            range.min_val,
                            prim_bounds.min_val,
                            prim_bounds.max_val,
                        );
                    }
                }
                return self.pool.internRefined(base_ty, sym_idx, range.min_val, range.max_val);
            }
        }

        return base_ty;
    }

    /// Resolves field types of a `struct`, `union`, or `bit_field` declaration and checks `bit_field` widths.
    fn resolveStructOrBitFieldFields(self: *TypeChecker, struct_sym_idx: SymbolIndex) !void {
        const struct_sym = self.sym_table.getSymbol(struct_sym_idx).*;
        if (struct_sym.target_scope.isNone() or struct_sym.ast_node.isNone()) return;

        const ast_node = self.ast_arena.getNode(struct_sym.ast_node);
        const field_members = try self.allocator.dupe(
            SymbolIndex,
            self.sym_table.getScopeMembers(struct_sym.target_scope),
        );
        defer self.allocator.free(field_members);

        if (struct_sym.kind == .bit_field_sym) {
            const bf_node = self.pool.getNode(self.pool.unwrapUnderlyingType(struct_sym.type_id));
            const raw_backing_ty = TypeId.fromInt(bf_node.lhs);
            const backing_ty = self.pool.unwrapUnderlyingType(raw_backing_ty);
            const backing_bits_opt = getTargetPrimitiveIntBits(backing_ty, self.target_layout);
            if (backing_bits_opt == null and !backing_ty.isError()) {
                try self.emitDiagnosticSimple(
                    .e0401_type_mismatch,
                    struct_sym.decl_span,
                    "`bit_field` backing type must be a primitive integer type",
                    "non-integer backing type here",
                );
            }
            const backing_bits: u32 = if (backing_bits_opt) |bits_val| bits_val else 64;
            var total_bits: u32 = 0;

            for (field_members) |f_sym_idx| {
                const f_sym = self.sym_table.getSymbol(f_sym_idx).*;
                if (f_sym.kind != .field_sym) continue;
                const field_ty = try self.resolveFieldTypeFromCst(f_sym.cst_node);
                self.sym_table.getSymbolMut(f_sym_idx).type_id = field_ty;
                const unwrapped_field_ty = self.pool.unwrapUnderlyingType(field_ty);
                const field_max_bits: u32 = if (getTargetPrimitiveIntBits(unwrapped_field_ty, self.target_layout)) |fb|
                    fb
                else if (unwrapped_field_ty == .bool_ty)
                    1
                else
                    backing_bits;
                if (f_sym.bit_width == 0 or f_sym.bit_width > field_max_bits) {
                    try self.emitDiagnosticSimple(
                        .e0406_range_refinement_violation,
                        f_sym.decl_span,
                        "`bit_field` member bit width is out of bounds for its field type",
                        "invalid field bit width here",
                    );
                }
                total_bits += f_sym.bit_width;
            }
            if (total_bits != backing_bits) {
                try self.emitDiagnosticSimple(
                    .e0406_range_refinement_violation,
                    struct_sym.decl_span,
                    "`bit_field` member bit widths do not match backing integer width",
                    "total bit width must equal backing integer bit width",
                );
            }
            return;
        }

        const type_ast_slice: []const u32 = if (ast_node.lhs.tag == .extra and ast_node.rhs.tag == .extra)
            self.ast_arena.getExtraSlice(ExtraIndex.fromInt(ast_node.lhs.payload), ast_node.rhs.payload)
        else
            &.{};

        var field_i: usize = 0;
        var has_all_copy_fields = true;
        for (field_members) |f_sym_idx| {
            const f_sym = self.sym_table.getSymbol(f_sym_idx).*;
            if (f_sym.kind != .field_sym) continue;
            const field_ty = if (field_i < type_ast_slice.len)
                try self.resolveTypeAst(NodeIndex.fromInt(type_ast_slice[field_i]))
            else
                try self.resolveFieldTypeFromCst(f_sym.cst_node);

            self.sym_table.getSymbolMut(f_sym_idx).type_id = field_ty;
            if (!self.pool.getFlags(field_ty).is_copy) has_all_copy_fields = false;
            field_i += 1;
        }
        if (has_all_copy_fields and struct_sym.type_id.toU32() < self.pool.nodes.len) {
            self.pool.nodes.items(.flags)[struct_sym.type_id.toU32()].is_copy = true;
        }
    }

    /// Resolves the type AST node inside a `.struct_field` CST subtree.
    fn resolveFieldTypeFromCst(self: *TypeChecker, field_cst: CstNodeIndex) !TypeId {
        if (field_cst.isNone() or field_cst.asInt() >= self.cst_arena.countNodes()) return .err_ty;
        const start_idx: usize = field_cst.asInt();
        const rec = self.cst_arena.getNode(field_cst);
        const end_idx: usize = @min(start_idx + @max(@as(usize, rec.subtree_size), 1), self.cst_arena.countNodes());
        const ty_ast = self.findFirstAstInCstRange(start_idx + 1, end_idx);
        if (!ty_ast.isNone()) return self.resolveTypeAst(ty_ast);
        return .err_ty;
    }

    /// Resolves tuple or struct payload types for all `.enum_variant` items inside an `enum`.
    fn resolveEnumVariantPayloads(self: *TypeChecker, enum_sym_idx: SymbolIndex) !void {
        const enum_sym = self.sym_table.getSymbol(enum_sym_idx).*;
        if (enum_sym.target_scope.isNone()) return;

        const variant_members = try self.allocator.dupe(
            SymbolIndex,
            self.sym_table.getScopeMembers(enum_sym.target_scope),
        );
        defer self.allocator.free(variant_members);

        for (variant_members) |var_sym_idx| {
            const var_sym = self.sym_table.getSymbol(var_sym_idx).*;
            if (var_sym.kind != .enum_variant_sym) continue;
            var payload_ty: TypeId = .unit_ty;
            if (!var_sym.cst_node.isNone() and var_sym.cst_node.asInt() < self.cst_arena.countNodes()) {
                const start_idx: usize = var_sym.cst_node.asInt();
                const rec = self.cst_arena.getNode(var_sym.cst_node);
                const end_idx: usize = @min(
                    start_idx + @max(@as(usize, rec.subtree_size), 1),
                    self.cst_arena.countNodes(),
                );
                const first_ty_ast = self.findFirstAstInCstRange(start_idx + 1, end_idx);
                if (!first_ty_ast.isNone()) {
                    const ast_tag = self.ast_arena.getNode(first_ty_ast).tag;
                    if (isTypeAstTag(ast_tag)) {
                        payload_ty = try self.resolveTypeAst(first_ty_ast);
                    }
                }
            }
            self.sym_table.getSymbolMut(var_sym_idx).type_id = payload_ty;
            if (var_sym.flags.is_from_error and payload_ty != .unit_ty and
                !payload_ty.isError() and !enum_sym.type_id.isError())
            {
                const src_err = if (self.pool.getTag(payload_ty) == .tuple_ty) blk: {
                    const tup_elems = self.pool.getTupleElements(payload_ty);
                    break :blk if (tup_elems.len == 1) TypeId.fromInt(tup_elems[0]) else payload_ty;
                } else payload_ty;
                try self.sym_table.from_error_pairs.put(
                    self.sym_table.allocator,
                    packFromErrorPair(src_err, enum_sym.type_id),
                    {},
                );
            }
        }
    }

    /// Resolves the parameter types, modes, return type, and `@from` registration of a `fn_sym`.
    pub fn resolveFnSignatureSymbol(self: *TypeChecker, fn_sym_idx: SymbolIndex) !void {
        const fn_sym = self.sym_table.getSymbol(fn_sym_idx).*;
        if (!fn_sym.type_id.isError() and self.pool.getTag(fn_sym.type_id) == .fn_ty) return;
        if (fn_sym.ast_node.isNone()) return;

        self.active_bind_once_vars.clearRetainingCapacity();
        const saved_scope = self.current_scope;
        const saved_in_sig = self.is_in_fn_signature;
        self.is_in_fn_signature = true;
        defer {
            self.current_scope = saved_scope;
            self.is_in_fn_signature = saved_in_sig;
        }

        const fn_scope = try self.sym_table.scope_arena.allocScope(
            .fn_scope,
            fn_sym.scope_id,
            fn_sym.def_id,
            self.file_id,
            .{},
        );
        self.sym_table.getSymbolMut(fn_sym_idx).target_scope = fn_scope;
        self.current_scope = fn_scope;

        var param_types: std.ArrayListUnmanaged(TypeId) = .empty;
        defer param_types.deinit(self.allocator);
        var param_modes: std.ArrayListUnmanaged(ParamMode) = .empty;
        defer param_modes.deinit(self.allocator);

        // [1] Walk `.type_params` and `.param_list` inside `fn_sym.cst_node`:
        if (!fn_sym.cst_node.isNone() and fn_sym.cst_node.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = fn_sym.cst_node.asInt();
            const root_rec = self.cst_arena.getNode(fn_sym.cst_node);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, root_rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );

            var cursor: usize = start_idx + 1;
            while (cursor < end_idx) {
                const cst_id = CstNodeIndex.fromInt(@intCast(cursor));
                const node = self.cst_arena.getNode(cst_id);
                if (node.kind == .block) break;

                if (node.kind == .type_param) {
                    const param_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), end_idx);
                    try self.registerGenericTypeParamFromCst(fn_scope, cursor, param_end);
                    cursor = param_end;
                    continue;
                }

                if (node.kind == .fn_param) {
                    const param_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), end_idx);
                    const param_info = try self.extractFnParamFromCst(
                        fn_sym_idx,
                        fn_scope,
                        cursor,
                        param_end,
                        @intCast(param_types.items.len),
                    );
                    try param_types.append(self.allocator, param_info.ty);
                    try param_modes.append(self.allocator, param_info.mode);
                    cursor = param_end;
                    continue;
                }
                cursor += 1;
            }
        }

        // [2] Resolve return type (`-> Type`; defaults to `.unit_ty`):
        const fn_ast = self.ast_arena.getNode(fn_sym.ast_node);
        var ret_ty: TypeId = .unit_ty;
        if (fn_ast.lhs.tag == .node) {
            self.is_in_return_type_pos = true;
            defer self.is_in_return_type_pos = false;
            ret_ty = try self.resolveTypeAst(NodeIndex.fromInt(fn_ast.lhs.payload));
        }

        const is_must_use = fn_sym.flags.is_must_use or self.pool.getFlags(ret_ty).is_must_use;
        if (is_must_use) {
            self.sym_table.getSymbolMut(fn_sym_idx).flags.is_must_use = true;
        }
        const fn_ty = try self.pool.internFn(
            .fn_ty,
            param_types.items,
            param_modes.items,
            ret_ty,
            is_must_use,
        );
        self.sym_table.getSymbolMut(fn_sym_idx).type_id = fn_ty;

        // [3] Register `@from` error conversion (`@from fn from_io(e: SrcErr) -> DstErr` or `Result[_, DstErr]`):
        if (fn_sym.flags.is_from_error and param_types.items.len == 1) {
            const src_err = param_types.items[0];
            const dst_err = if (self.pool.getTag(ret_ty) == .result_ty)
                TypeId.fromInt(self.pool.getNode(ret_ty).rhs)
            else
                ret_ty;
            if (!src_err.isError() and !dst_err.isError()) {
                const pair_key = packFromErrorPair(src_err, dst_err);
                try self.sym_table.from_error_pairs.put(
                    self.sym_table.allocator,
                    pair_key,
                    {},
                );
                if (!fn_sym.def_id.isNone()) {
                    try self.sym_table.from_error_fn_defs.put(
                        self.sym_table.allocator,
                        pair_key,
                        fn_sym.def_id,
                    );
                }
            }
        }
    }

    /// Registers a generic `[T: Bound]` or `[const N: usize]` parameter inside `fn_scope`.
    fn registerGenericTypeParamFromCst(
        self: *TypeChecker,
        fn_scope: ScopeId,
        cst_start: usize,
        cst_end: usize,
    ) !void {
        var is_const_param = false;
        var name_tok: TokenIndex = .none;

        var cur = cst_start + 1;
        while (cur < cst_end) : (cur += 1) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
            if (!is_leaf or sub.flags.is_missing_or_injected or sub.token.isNone()) continue;
            if (sub.token.asInt() >= self.token_buffer.countTokens()) continue;
            const kind = self.token_buffer.getToken(sub.token).kind;
            if (kind == .kw_const) {
                is_const_param = true;
            } else if (name_tok.isNone() and symbol_resolver.isIdentifierToken(kind)) {
                name_tok = sub.token;
                break;
            }
        }
        if (name_tok.isNone()) return;

        const name_str = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, name_tok);
        if (name_str.len == 0) return;
        const name_sym = try self.interner.intern(name_str);
        const bound_ast = self.findFirstAstInCstRange(cst_start + 1, cst_end);
        const bound_ty = if (!bound_ast.isNone() and isTypeAstTag(self.ast_arena.getNode(bound_ast).tag)) blk: {
            const saved_in_fn_sig = self.is_in_fn_signature;
            if (!is_const_param) self.is_in_fn_signature = false;
            defer self.is_in_fn_signature = saved_in_fn_sig;
            break :blk try self.resolveTypeAst(bound_ast);
        } else TypeId.group_copy;

        const param_ty = if (is_const_param)
            bound_ty
        else
            try self.pool.internTypeParam(bound_ty, name_sym);

        _ = try self.sym_table.defineSymbol(.{
            .name = name_sym,
            .name_text = self.interner.get(name_sym),
            .kind = if (is_const_param) .const_param_sym else .type_param_sym,
            .namespace = if (is_const_param) .const_ns else .type_ns,
            .visibility = .private,
            .flags = .{ .is_used = true },
            .scope_id = fn_scope,
            .decl_span = self.token_buffer.getTokenSpan(self.file_id, name_tok),
            .type_id = param_ty,
        }, self.diagnostic_sink);
    }

    /// Extracts a single `.fn_param` parameter binding and its resolved `TypeId` + `ParamMode`.
    fn extractFnParamFromCst(
        self: *TypeChecker,
        fn_sym_idx: SymbolIndex,
        fn_scope: ScopeId,
        cst_start: usize,
        cst_end: usize,
        ordinal: u16,
    ) !struct { ty: TypeId, mode: ParamMode } {
        var name_tok: TokenIndex = .none;
        var is_mut = false;
        var is_comptime_param = false;
        var has_amp = false;
        var is_self_param = false;
        var mode: ParamMode = .let_mode;
        var colon_pos: ?usize = null;

        var cur = cst_start + 1;
        while (cur < cst_end) : (cur += 1) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.kind == .attribute) {
                if (sub.subtree_size > 1) cur += @as(usize, sub.subtree_size) - 1;
                continue;
            }
            const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
            if (!is_leaf or sub.flags.is_missing_or_injected or sub.token.isNone()) continue;
            if (sub.token.asInt() >= self.token_buffer.countTokens()) continue;
            const tok_kind = self.token_buffer.getToken(sub.token).kind;
            if (tok_kind == .colon) {
                colon_pos = cur;
                break;
            }
            if (tok_kind == .kw_comptime) {
                is_comptime_param = true;
            } else if (tok_kind == .amp or tok_kind == .kw_ref) {
                has_amp = true;
            } else if (tok_kind == .kw_mut) {
                is_mut = true;
                if (!has_amp) mode = .inout_mode;
            } else if (tok_kind == .kw_own) {
                mode = .sink_mode;
            } else if (name_tok.isNone() and
                (symbol_resolver.isIdentifierToken(tok_kind) or
                    tok_kind == .kw_self_val or
                    tok_kind == .underscore))
            {
                name_tok = sub.token;
                if (tok_kind == .kw_self_val) is_self_param = true;
            }
        }

        if (is_comptime_param and ordinal < 64 and !fn_sym_idx.isNone()) {
            self.sym_table.getSymbolMut(fn_sym_idx).is_comptime_param_mask |= (@as(u64, 1) << @intCast(ordinal));
        }

        const ty_search_start = if (colon_pos) |c_pos| c_pos + 1 else cst_start + 1;
        const ty_ast = self.findFirstAstInCstRange(ty_search_start, cst_end);
        if (colon_pos) |c_pos| {
            const mode_scan_end = if (!ty_ast.isNone() and !self.ast_arena.getCstOrigin(ty_ast).isNone())
                @min(@as(usize, self.ast_arena.getCstOrigin(ty_ast).asInt()), cst_end)
            else
                cst_end;
            var mode_cur = c_pos + 1;
            while (mode_cur < mode_scan_end) : (mode_cur += 1) {
                const mode_sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(mode_cur)));
                if (mode_sub.subtree_size > 1 or mode_sub.flags.is_bracketed or
                    mode_sub.flags.is_missing_or_injected or mode_sub.token.isNone() or
                    mode_sub.token.asInt() >= self.token_buffer.countTokens())
                {
                    continue;
                }
                const m_kind = self.token_buffer.getToken(mode_sub.token).kind;
                const m_lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, mode_sub.token);
                if (m_kind == .kw_own or std.mem.eql(u8, m_lex, "sink")) {
                    mode = .sink_mode;
                } else if (std.mem.eql(u8, m_lex, "inout")) {
                    mode = .inout_mode;
                    is_mut = true;
                } else if (std.mem.eql(u8, m_lex, "set")) {
                    mode = .set_mode;
                    is_mut = true;
                } else if (m_kind == .kw_let) {
                    mode = .let_mode;
                }
            }
        }
        if (!ty_ast.isNone() and self.ast_arena.getNode(ty_ast).tag == .mode_type) {
            const m_tok = self.ast_arena.getNode(ty_ast).main_token;
            if (!m_tok.isNone() and m_tok.asInt() < self.token_buffer.countTokens()) {
                const m_kind = self.token_buffer.getToken(m_tok).kind;
                const m_lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, m_tok);
                if (m_kind == .kw_own or std.mem.eql(u8, m_lex, "sink")) {
                    mode = .sink_mode;
                } else if (std.mem.eql(u8, m_lex, "inout")) {
                    mode = .inout_mode;
                    is_mut = true;
                } else if (std.mem.eql(u8, m_lex, "set")) {
                    mode = .set_mode;
                    is_mut = true;
                }
            }
        }
        var param_ty: TypeId = .unit_ty;
        if (!ty_ast.isNone() and isTypeAstTag(self.ast_arena.getNode(ty_ast).tag)) {
            param_ty = try self.resolveTypeAst(ty_ast);
        } else if (is_self_param) {
            const self_type_sym = try self.interner.intern("Self");
            switch (self.sym_table.lookupLexical(fn_scope, self_type_sym, NamespaceMask.TYPE_ONLY)) {
                .found => |found_self_idx| {
                    const base_self_ty = self.sym_table.getSymbol(found_self_idx).type_id;
                    param_ty = if (has_amp and !base_self_ty.isError())
                        try self.pool.internRef(base_self_ty, is_mut)
                    else
                        base_self_ty;
                },
                else => {},
            }
        }

        if (!name_tok.isNone()) {
            const name_str = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, name_tok);
            if (name_str.len > 0 and !std.mem.eql(u8, name_str, "_")) {
                const name_sym = try self.interner.intern(name_str);
                const param_sym_idx = try self.sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = self.interner.get(name_sym),
                    .kind = .param_sym,
                    .namespace = .value_ns,
                    .visibility = .private,
                    .flags = .{ .is_mut = is_mut and !has_amp, .is_comptime = is_comptime_param },
                    .scope_id = fn_scope,
                    .cst_node = CstNodeIndex.fromInt(@intCast(cst_start)),
                    .decl_span = self.token_buffer.getTokenSpan(self.file_id, name_tok),
                    .type_id = param_ty,
                    .member_ordinal = ordinal,
                }, self.diagnostic_sink);
                const owner_def: DefId = if (!fn_sym_idx.isNone())
                    self.sym_table.getSymbol(fn_sym_idx).def_id
                else
                    .NONE;
                try self.validateSymbolAttributes(param_sym_idx, owner_def);
            }
        }
        return .{ .ty = param_ty, .mode = mode };
    }

    // -------------------- Type AST Resolution ---------------------

    /// Resolves a type expression AST node into its canonical `TypeId` in `self.pool`.
    pub fn resolveTypeAst(self: *TypeChecker, type_node_id: NodeIndex) anyerror!TypeId {
        if (type_node_id.isNone() or type_node_id.asInt() >= self.ast_arena.countNodes()) return .err_ty;
        if (self.recursion_depth >= MAX_TYPE_DEPTH) return self.recordNodeType(type_node_id, .err_ty);
        self.recursion_depth += 1;
        defer self.recursion_depth -= 1;

        const ast_node = self.ast_arena.getNode(type_node_id);

        const resolved: TypeId = switch (ast_node.tag) {
            .type_hole => .err_ty,
            .prim_type => blk: {
                const lexeme = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.token_buffer,
                    ast_node.main_token,
                );
                for (symbol_resolver.BUILTIN_TYPES_AND_GROUPS) |entry| {
                    if (!entry.is_group and std.mem.eql(u8, entry.name, lexeme)) {
                        break :blk entry.type_id;
                    }
                }
                break :blk .err_ty;
            },
            .optional_type => blk: {
                if (ast_node.lhs.tag != .node) break :blk .err_ty;
                const inner_ty = try self.resolveTypeAst(NodeIndex.fromInt(ast_node.lhs.payload));
                break :blk try self.pool.internOptional(inner_ty);
            },
            .ref_type => blk: {
                if (ast_node.lhs.tag != .node) break :blk .err_ty;
                const inner_ty = try self.resolveTypeAst(NodeIndex.fromInt(ast_node.lhs.payload));
                const is_mut = self.hasMutKeywordInCst(self.ast_arena.getCstOrigin(type_node_id));
                break :blk try self.pool.internRef(inner_ty, is_mut);
            },
            .ptr_type => blk: {
                if (ast_node.lhs.tag != .node) break :blk .err_ty;
                const inner_ty = try self.resolveTypeAst(NodeIndex.fromInt(ast_node.lhs.payload));
                const is_mut = self.hasMutKeywordInCst(self.ast_arena.getCstOrigin(type_node_id));
                break :blk try self.pool.internRawPtr(inner_ty, is_mut);
            },
            .slice_type => blk: {
                if (ast_node.lhs.tag != .node) break :blk .err_ty;
                const elem_ty = try self.resolveTypeAst(NodeIndex.fromInt(ast_node.lhs.payload));
                break :blk try self.pool.internSlice(elem_ty, false);
            },
            .array_type => blk: {
                if (ast_node.lhs.tag != .node) break :blk .err_ty;
                const elem_ty = try self.resolveTypeAst(NodeIndex.fromInt(ast_node.lhs.payload));
                if (ast_node.rhs.tag != .node) {
                    break :blk try self.pool.internArray(elem_ty, 0, false);
                }
                const len_expr_id = NodeIndex.fromInt(ast_node.rhs.payload);

                // Check for symbolic `[const N: usize]` generic array length (`[T; N]`):
                if (try self.findConstParamInExpr(len_expr_id, 0)) |const_param_sym_idx| {
                    self.pure_comptime_depth += 1;
                    defer self.pure_comptime_depth -= 1;
                    _ = try self.synthExpr(len_expr_id);
                    if (self.ast_arena.getNode(len_expr_id).tag != .ident_expr) {
                        try self.emitDiagnosticSimple(
                            .e0503_forbidden_comptime_operation,
                            self.getAstNodeSpan(len_expr_id),
                            "compound dependent array length expressions require a named `const` " ++
                                "binding; only direct `[T; N]` const parameters are supported",
                            "compound `const` parameter expression in array length",
                        );
                        break :blk .err_ty;
                    }
                    const const_param_name = self.sym_table.getSymbol(const_param_sym_idx).name;
                    break :blk try self.pool.internSymbolicArray(elem_ty, const_param_name, false);
                }

                const len_ty = check_len: {
                    self.pure_comptime_depth += 1;
                    defer self.pure_comptime_depth -= 1;
                    break :check_len try self.synthExpr(len_expr_id);
                };
                if (len_ty.isError()) break :blk .err_ty;
                const len_base = self.pool.unwrapRefinementBase(len_ty);
                if (len_base != .untyped_int_ty and !len_base.isIntegerPrimitive()) {
                    try self.emitTypeMismatch(self.getAstNodeSpan(len_expr_id), .usize_ty, len_ty);
                    break :blk .err_ty;
                }

                const eval_opt = try self.evalConstIntExpr(len_expr_id, true);
                const len_val = eval_opt orelse break :blk .err_ty;
                if (len_val < 0 or len_val > 0x7FFF_FFFF) {
                    try self.emitDiagnosticSimple(
                        .e0502_integer_constant_overflow,
                        self.getAstNodeSpan(len_expr_id),
                        "array length must be a non-negative integer fitting within `0..=2147483647`",
                        "invalid negative or overflowing array length",
                    );
                    break :blk .err_ty;
                }
                break :blk try self.pool.internArray(elem_ty, @intCast(len_val), false);
            },
            .tuple_type => blk: {
                if (ast_node.lhs.tag != .extra or ast_node.rhs.tag != .extra or ast_node.rhs.payload == 0) {
                    break :blk .unit_ty;
                }
                const elem_nodes = self.ast_arena.getExtraSlice(
                    ExtraIndex.fromInt(ast_node.lhs.payload),
                    ast_node.rhs.payload,
                );
                const elem_types = try self.allocator.alloc(TypeId, elem_nodes.len);
                defer self.allocator.free(elem_types);
                for (elem_nodes, 0..) |raw_elem, i| {
                    elem_types[i] = try self.resolveTypeAst(NodeIndex.fromInt(raw_elem));
                }
                break :blk try self.pool.internTuple(elem_types);
            },
            .fn_type => blk: {
                var ret_ty: TypeId = .unit_ty;
                if (ast_node.rhs.tag == .node) {
                    ret_ty = try self.resolveTypeAst(NodeIndex.fromInt(ast_node.rhs.payload));
                }
                var param_types: std.ArrayListUnmanaged(TypeId) = .empty;
                defer param_types.deinit(self.allocator);
                var param_modes: std.ArrayListUnmanaged(ParamMode) = .empty;
                defer param_modes.deinit(self.allocator);
                if (ast_node.lhs.tag == .extra) {
                    const start_extra: usize = ast_node.lhs.payload;
                    var cur_extra = start_extra;
                    while (cur_extra < self.ast_arena.extra_data.items.len) : (cur_extra += 1) {
                        const cand_node = self.ast_arena.extra_data.items[cur_extra];
                        if (cand_node >= type_node_id.asInt()) break;
                        const cand_id = NodeIndex.fromInt(cand_node);
                        var fn_param_mode: ParamMode = .let_mode;
                        if (self.ast_arena.getNode(cand_id).tag == .mode_type) {
                            const m_tok = self.ast_arena.getNode(cand_id).main_token;
                            if (!m_tok.isNone() and m_tok.asInt() < self.token_buffer.countTokens()) {
                                const m_kind = self.token_buffer.getToken(m_tok).kind;
                                const m_lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, m_tok);
                                if (m_kind == .kw_own or std.mem.eql(u8, m_lex, "sink")) {
                                    fn_param_mode = .sink_mode;
                                } else if (std.mem.eql(u8, m_lex, "inout")) {
                                    fn_param_mode = .inout_mode;
                                } else if (std.mem.eql(u8, m_lex, "set")) {
                                    fn_param_mode = .set_mode;
                                }
                            }
                        }
                        try param_types.append(self.allocator, try self.resolveTypeAst(cand_id));
                        try param_modes.append(self.allocator, fn_param_mode);
                    }
                }
                break :blk try self.pool.internFn(
                    .fn_ty,
                    param_types.items,
                    param_modes.items,
                    ret_ty,
                    false,
                );
            },
            .mode_type => blk: {
                if (ast_node.lhs.tag != .node) break :blk .err_ty;
                const inner_ast_id = NodeIndex.fromInt(ast_node.lhs.payload);
                const tok_kind = self.token_buffer.getToken(ast_node.main_token).kind;
                const mode_lexeme = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.token_buffer,
                    ast_node.main_token,
                );

                // [a] `~T` underlying-type approximation:
                if (tok_kind == .tilde) {
                    const inner_ty = try self.resolveNamedOrGroupTypeRaw(inner_ast_id);
                    const tilde_ty = try self.pool.internTildeApprox(inner_ty);
                    if (self.is_in_fn_signature) {
                        const tilde_key = tilde_ty.toU32() | 0x8000_0000;
                        if (self.active_bind_once_vars.get(tilde_key)) |existing_var| {
                            break :blk existing_var;
                        }
                        const inner_lex = symbol_resolver.extractTokenSlice(
                            self.source,
                            self.token_buffer,
                            self.ast_arena.getNode(inner_ast_id).main_token,
                        );
                        const grp_sym_id = try self.interner.intern(inner_lex);
                        const bind_once_var = try self.pool.internBindOnceVar(tilde_ty, grp_sym_id);
                        try self.active_bind_once_vars.put(self.allocator, tilde_key, bind_once_var);
                        break :blk bind_once_var;
                    }
                    break :blk tilde_ty;
                }

                // [b] `#soa [T]` / `#soa [T; N]`:
                if (tok_kind == .hash_soa) {
                    const inner_ty = try self.resolveTypeAst(inner_ast_id);
                    const inner_node = self.pool.getNode(inner_ty);
                    if (inner_node.tag == .slice_ty) {
                        break :blk try self.pool.internSlice(TypeId.fromInt(inner_node.lhs), true);
                    }
                    if (inner_node.tag == .array_ty) {
                        if ((inner_node.rhs & SYMBOLIC_ARRAY_LEN_FLAG) != 0) {
                            break :blk try self.pool.internSymbolicArray(
                                TypeId.fromInt(inner_node.lhs),
                                SymbolId.fromInt(inner_node.rhs & ~SYMBOLIC_ARRAY_LEN_FLAG),
                                true,
                            );
                        }
                        break :blk try self.pool.internArray(TypeId.fromInt(inner_node.lhs), inner_node.rhs, true);
                    }
                    break :blk inner_ty;
                }

                // [c] `any Group` Bind-Many parameter (or forbidden `-> any Group` return type, `DR-04` Section 1.3):
                if (std.mem.eql(u8, mode_lexeme, "any")) {
                    if (self.is_in_return_type_pos) {
                        try self.emitDiagnosticSimple(
                            .e0402_unsatisfied_trait_bound,
                            self.getAstNodeSpan(type_node_id),
                            "existential `any Group` is not permitted in function return position",
                            "`any` Type Group cannot be returned by value; use a bare Type Group name or concrete type",
                        );
                        break :blk .err_ty;
                    }
                    const inner_ast = self.ast_arena.getNode(inner_ast_id);
                    const inner_raw_ty = if (inner_ast.tag == .mode_type and
                        self.token_buffer.getToken(inner_ast.main_token).kind == .tilde and
                        inner_ast.lhs.tag == .node)
                        try self.pool.internTildeApprox(
                            try self.resolveNamedOrGroupTypeRaw(NodeIndex.fromInt(inner_ast.lhs.payload)),
                        )
                    else
                        try self.resolveNamedOrGroupTypeRaw(inner_ast_id);
                    if (inner_raw_ty.isError()) break :blk .err_ty;
                    const ord = self.next_any_ordinal;
                    self.next_any_ordinal += 1;
                    break :blk try self.pool.internBindManyVar(inner_raw_ty, ord);
                }

                // [d] `ref T` / `ref mut T`:
                if (tok_kind == .kw_ref) {
                    const inner_ty = try self.resolveTypeAst(inner_ast_id);
                    const is_mut = self.hasMutKeywordInCst(self.ast_arena.getCstOrigin(type_node_id));
                    break :blk try self.pool.internRef(inner_ty, is_mut);
                }

                break :blk try self.resolveTypeAst(inner_ast_id);
            },
            .named_type => blk: {
                const raw_ty = try self.resolveNamedOrGroupTypeRaw(type_node_id);
                if (raw_ty.isError()) break :blk .err_ty;

                // Bare Type Group in function signature -> Bind-Once group variable (`__G_Name`, `DR-04` Section 1.3):
                const raw_tag = self.pool.getTag(raw_ty);
                if (self.is_in_fn_signature and
                    (raw_ty.isBuiltinGroup() or raw_tag == .builtin_group or raw_tag == .user_group))
                {
                    const lexeme = symbol_resolver.extractTokenSlice(
                        self.source,
                        self.token_buffer,
                        ast_node.main_token,
                    );
                    const grp_sym_id = try self.interner.intern(lexeme);
                    if (self.active_bind_once_vars.get(grp_sym_id.asInt())) |existing_var| {
                        break :blk existing_var;
                    }
                    const bind_once_var = try self.pool.internBindOnceVar(raw_ty, grp_sym_id);
                    try self.active_bind_once_vars.put(self.allocator, grp_sym_id.asInt(), bind_once_var);
                    break :blk bind_once_var;
                }
                break :blk raw_ty;
            },
            .generic_type => blk: {
                const name_lexeme = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.token_buffer,
                    ast_node.main_token,
                );
                const arg_slice: []const u32 = if (ast_node.lhs.tag == .extra and ast_node.rhs.tag == .extra)
                    self.ast_arena.getExtraSlice(ExtraIndex.fromInt(ast_node.lhs.payload), ast_node.rhs.payload)
                else
                    &.{};

                if (std.mem.eql(u8, name_lexeme, "Result")) {
                    const ok_ty = if (arg_slice.len >= 1)
                        try self.resolveTypeAst(NodeIndex.fromInt(arg_slice[0]))
                    else
                        .unit_ty;
                    const err_ty_arg = if (arg_slice.len >= 2)
                        try self.resolveTypeAst(NodeIndex.fromInt(arg_slice[1]))
                    else
                        .err_ty;
                    break :blk try self.pool.internResult(ok_ty, err_ty_arg);
                }
                if (std.mem.eql(u8, name_lexeme, "Option")) {
                    const payload_ty = if (arg_slice.len >= 1)
                        try self.resolveTypeAst(NodeIndex.fromInt(arg_slice[0]))
                    else
                        .unit_ty;
                    break :blk try self.pool.internOptional(payload_ty);
                }
                break :blk try self.resolveNamedOrGroupTypeRaw(type_node_id);
            },
            else => .err_ty,
        };
        return self.recordNodeType(type_node_id, resolved);
    }

    /// Searches `expr_id` for a reference to a generic `.const_param_sym` or `comptime` `.param_sym`.
    fn findConstParamInExpr(
        self: *TypeChecker,
        expr_id: NodeIndex,
        depth: u32,
    ) anyerror!?SymbolIndex {
        if (expr_id.isNone() or expr_id.asInt() >= self.ast_arena.countNodes() or depth >= MAX_TYPE_DEPTH) {
            return null;
        }
        const node = self.ast_arena.getNode(expr_id);
        switch (node.tag) {
            .ident_expr => {
                if (!node.main_token.isNone() and
                    self.token_buffer.getToken(node.main_token).kind == .at) return null;
                const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, node.main_token);
                if (lex.len == 0) return null;
                const sym_id = try self.interner.intern(lex);
                switch (self.sym_table.lookupLexical(self.current_scope, sym_id, NamespaceMask.ALL)) {
                    .found => |sym_idx| {
                        const found_sym = self.sym_table.getSymbol(sym_idx);
                        if (found_sym.kind == .const_param_sym or
                            (found_sym.kind == .param_sym and found_sym.flags.is_comptime))
                        {
                            return sym_idx;
                        }
                    },
                    else => {},
                }
                return null;
            },
            .unary_expr => {
                if (node.lhs.tag == .node) {
                    return self.findConstParamInExpr(NodeIndex.fromInt(node.lhs.payload), depth + 1);
                }
                return null;
            },
            .binary_expr => {
                if (node.lhs.tag == .node) {
                    if (try self.findConstParamInExpr(NodeIndex.fromInt(node.lhs.payload), depth + 1)) |found| {
                        return found;
                    }
                }
                if (node.rhs.tag == .node) {
                    return self.findConstParamInExpr(NodeIndex.fromInt(node.rhs.payload), depth + 1);
                }
                return null;
            },
            else => return null,
        }
    }

    /// Evaluates a compile-time constant integer or boolean AST expression to `i128` (`E0502`/`E0503`/`E0507`/`E0509`).
    pub fn evalConstIntExpr(
        self: *TypeChecker,
        expr_id: NodeIndex,
        is_emitting_diags: bool,
    ) anyerror!?i128 {
        if (expr_id.isNone() or expr_id.asInt() >= self.ast_arena.countNodes()) return null;
        if (self.recursion_depth >= MAX_TYPE_DEPTH) return null;
        self.recursion_depth += 1;
        defer self.recursion_depth -= 1;

        const ast_node = self.ast_arena.getNode(expr_id);
        switch (ast_node.tag) {
            .bool_lit => {
                const is_true = !ast_node.main_token.isNone() and
                    self.token_buffer.getToken(ast_node.main_token).kind == .kw_true;
                return if (is_true) 1 else 0;
            },
            .char_lit => {
                const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, ast_node.main_token);
                if (extractCharLiteralCodepoint(lex)) |cp| return @as(i128, cp);
                return null;
            },
            .int_lit => {
                const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, ast_node.main_token);
                const parsed = extractIntLiteralValue(lex) orelse {
                    if (is_emitting_diags) {
                        try self.emitDiagnosticSimple(
                            .e0502_integer_constant_overflow,
                            self.getAstNodeSpan(expr_id),
                            "integer literal overflows 128-bit constant evaluator range",
                            "constant integer literal overflow",
                        );
                    }
                    return null;
                };
                if (parsed.is_above_i128_max) {
                    const is_checked_u128 = expr_id.asInt() < self.node_types.len and
                        self.node_types[expr_id.asInt()] == .u128_ty;
                    if (is_emitting_diags and !is_checked_u128) {
                        try self.emitDiagnosticSimple(
                            .e0502_integer_constant_overflow,
                            self.getAstNodeSpan(expr_id),
                            "constant integer exceeds signed 128-bit evaluator range",
                            "constant integer overflow",
                        );
                    }
                    return null;
                }
                return parsed.value;
            },
            .unary_expr => {
                if (ast_node.lhs.tag != .node) return null;
                const inner_id = NodeIndex.fromInt(ast_node.lhs.payload);
                const op_kind = self.token_buffer.getToken(ast_node.main_token).kind;
                if (op_kind == .kw_comptime) {
                    return self.evalConstIntExpr(inner_id, is_emitting_diags);
                }
                if (op_kind == .minus and self.ast_arena.getNode(inner_id).tag == .int_lit) {
                    const lex = symbol_resolver.extractTokenSlice(
                        self.source,
                        self.token_buffer,
                        self.ast_arena.getNode(inner_id).main_token,
                    );
                    if (extractIntLiteralValue(lex)) |parsed| {
                        const min_abs: u128 = @as(u128, @intCast(std.math.maxInt(i128))) + 1;
                        if (parsed.is_above_i128_max and parsed.magnitude == min_abs) {
                            return std.math.minInt(i128);
                        }
                        if (!parsed.is_above_i128_max) return -parsed.value;
                    }
                }
                const inner_val = (try self.evalConstIntExpr(inner_id, is_emitting_diags)) orelse return null;
                return switch (op_kind) {
                    .minus => std.math.negate(inner_val) catch {
                        if (is_emitting_diags) {
                            try self.emitDiagnosticSimple(
                                .e0502_integer_constant_overflow,
                                self.getAstNodeSpan(expr_id),
                                "compile-time negation overflowed",
                                "arithmetic overflow during constant evaluation",
                            );
                        }
                        return null;
                    },
                    .bang, .kw_not => if (self.ast_arena.getNode(inner_id).tag == .bool_lit or
                        (inner_id.asInt() < self.node_types.len and self.node_types[inner_id.asInt()] == .bool_ty))
                        (if (inner_val == 0) @as(i128, 1) else @as(i128, 0))
                    else
                        ~inner_val,
                    else => null,
                };
            },
            .binary_expr => {
                if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .node) return null;
                const lhs_id = NodeIndex.fromInt(ast_node.lhs.payload);
                const rhs_id = NodeIndex.fromInt(ast_node.rhs.payload);
                const op_kind = self.token_buffer.getToken(ast_node.main_token).kind;

                if (op_kind == .ampamp or op_kind == .kw_and) {
                    const lhs_val = (try self.evalConstIntExpr(lhs_id, is_emitting_diags)) orelse return null;
                    if (lhs_val == 0) return 0;
                    const rhs_val = (try self.evalConstIntExpr(rhs_id, is_emitting_diags)) orelse return null;
                    return if (rhs_val != 0) 1 else 0;
                }
                if (op_kind == .pipepipe or op_kind == .kw_or) {
                    const lhs_val = (try self.evalConstIntExpr(lhs_id, is_emitting_diags)) orelse return null;
                    if (lhs_val != 0) return 1;
                    const rhs_val = (try self.evalConstIntExpr(rhs_id, is_emitting_diags)) orelse return null;
                    return if (rhs_val != 0) 1 else 0;
                }

                // String literal equality (`attr.method == "GET"`):
                if ((op_kind == .eqeq or op_kind == .bang_eq) and
                    self.ast_arena.getNode(lhs_id).tag == .string_lit and
                    self.ast_arena.getNode(rhs_id).tag == .string_lit)
                {
                    const lhs_lex = symbol_resolver.extractTokenSlice(
                        self.source,
                        self.token_buffer,
                        self.ast_arena.getNode(lhs_id).main_token,
                    );
                    const rhs_lex = symbol_resolver.extractTokenSlice(
                        self.source,
                        self.token_buffer,
                        self.ast_arena.getNode(rhs_id).main_token,
                    );
                    const is_eq = std.mem.eql(u8, lhs_lex, rhs_lex);
                    return if (op_kind == .eqeq)
                        (if (is_eq) @as(i128, 1) else @as(i128, 0))
                    else
                        (if (!is_eq) @as(i128, 1) else @as(i128, 0));
                }

                const lhs_val = (try self.evalConstIntExpr(lhs_id, is_emitting_diags)) orelse return null;
                const rhs_val = (try self.evalConstIntExpr(rhs_id, is_emitting_diags)) orelse return null;

                return switch (op_kind) {
                    .plus => std.math.add(i128, lhs_val, rhs_val) catch {
                        if (is_emitting_diags) {
                            try self.emitDiagnosticSimple(
                                .e0502_integer_constant_overflow,
                                self.getAstNodeSpan(expr_id),
                                "compile-time addition overflowed",
                                "integer overflow in constant expression",
                            );
                        }
                        return null;
                    },
                    .plus_percent => lhs_val +% rhs_val,
                    .plus_pipe => lhs_val +| rhs_val,
                    .minus => std.math.sub(i128, lhs_val, rhs_val) catch {
                        if (is_emitting_diags) {
                            try self.emitDiagnosticSimple(
                                .e0502_integer_constant_overflow,
                                self.getAstNodeSpan(expr_id),
                                "compile-time subtraction overflowed",
                                "integer overflow in constant expression",
                            );
                        }
                        return null;
                    },
                    .minus_percent => lhs_val -% rhs_val,
                    .minus_pipe => lhs_val -| rhs_val,
                    .star => std.math.mul(i128, lhs_val, rhs_val) catch {
                        if (is_emitting_diags) {
                            try self.emitDiagnosticSimple(
                                .e0502_integer_constant_overflow,
                                self.getAstNodeSpan(expr_id),
                                "compile-time multiplication overflowed",
                                "integer overflow in constant expression",
                            );
                        }
                        return null;
                    },
                    .star_percent => lhs_val *% rhs_val,
                    .star_pipe => lhs_val *| rhs_val,
                    .slash => blk: {
                        if (rhs_val == 0) {
                            if (is_emitting_diags) {
                                try self.emitDiagnosticSimple(
                                    .e0507_comptime_arithmetic_trap,
                                    self.getAstNodeSpan(expr_id),
                                    "compile-time division by zero",
                                    "divisor evaluated to `0` at compile time",
                                );
                            }
                            break :blk null;
                        }
                        break :blk std.math.divTrunc(i128, lhs_val, rhs_val) catch {
                            if (is_emitting_diags) {
                                try self.emitDiagnosticSimple(
                                    .e0502_integer_constant_overflow,
                                    self.getAstNodeSpan(expr_id),
                                    "compile-time division overflowed",
                                    "signed division overflow in constant expression",
                                );
                            }
                            break :blk null;
                        };
                    },
                    .percent => blk: {
                        if (rhs_val == 0) {
                            if (is_emitting_diags) {
                                try self.emitDiagnosticSimple(
                                    .e0507_comptime_arithmetic_trap,
                                    self.getAstNodeSpan(expr_id),
                                    "compile-time remainder by zero",
                                    "modulus evaluated to `0` at compile time",
                                );
                            }
                            break :blk null;
                        }
                        break :blk std.math.rem(i128, lhs_val, rhs_val) catch null;
                    },
                    .shl => blk: {
                        if (rhs_val < 0 or rhs_val >= 128) {
                            if (is_emitting_diags) {
                                try self.emitDiagnosticSimple(
                                    .e0507_comptime_arithmetic_trap,
                                    self.getAstNodeSpan(expr_id),
                                    "compile-time shift count out of bounds (`0..127`)",
                                    "invalid shift count at compile time",
                                );
                            }
                            break :blk null;
                        }
                        break :blk std.math.shlExact(i128, lhs_val, @intCast(rhs_val)) catch {
                            if (is_emitting_diags) {
                                try self.emitDiagnosticSimple(
                                    .e0502_integer_constant_overflow,
                                    self.getAstNodeSpan(expr_id),
                                    "compile-time left shift overflowed",
                                    "shifted bits overflowed constant integer width",
                                );
                            }
                            break :blk null;
                        };
                    },
                    .shr => blk: {
                        if (rhs_val < 0 or rhs_val >= 128) {
                            if (is_emitting_diags) {
                                try self.emitDiagnosticSimple(
                                    .e0507_comptime_arithmetic_trap,
                                    self.getAstNodeSpan(expr_id),
                                    "compile-time shift count out of bounds (`0..127`)",
                                    "invalid shift count at compile time",
                                );
                            }
                            break :blk null;
                        }
                        break :blk lhs_val >> @intCast(rhs_val);
                    },
                    .amp => lhs_val & rhs_val,
                    .pipe => lhs_val | rhs_val,
                    .caret => lhs_val ^ rhs_val,
                    .eqeq => if (lhs_val == rhs_val) 1 else 0,
                    .bang_eq => if (lhs_val != rhs_val) 1 else 0,
                    .lt => if (lhs_val < rhs_val) 1 else 0,
                    .le => if (lhs_val <= rhs_val) 1 else 0,
                    .gt => if (lhs_val > rhs_val) 1 else 0,
                    .ge => if (lhs_val >= rhs_val) 1 else 0,
                    else => null,
                };
            },
            .ident_expr, .path_expr => {
                const resolved_sym_idx = try self.lookupExprSymbolQuiet(expr_id);
                if (resolved_sym_idx.isNone()) return null;
                const sym = self.sym_table.getSymbol(resolved_sym_idx).*;
                switch (sym.kind) {
                    .const_sym => {
                        for (self.active_const_eval[0..self.active_const_eval_len]) |active_sym| {
                            if (active_sym == resolved_sym_idx) {
                                if (is_emitting_diags) {
                                    try self.emitDiagnosticSimple(
                                        .e0509_comptime_evaluation_cycle,
                                        self.getAstNodeSpan(expr_id),
                                        "cyclic compile-time constant evaluation detected",
                                        "constant depends on itself in an evaluation cycle",
                                    );
                                }
                                return null;
                            }
                        }
                        if (self.active_const_eval_len >= self.active_const_eval.len) {
                            if (is_emitting_diags) {
                                try self.emitDiagnosticSimple(
                                    .e0508_comptime_resource_limit_exceeded,
                                    self.getAstNodeSpan(expr_id),
                                    "compile-time constant dependency depth exceeded `64`",
                                    "constant evaluation chain too deep",
                                );
                            }
                            return null;
                        }
                        if (sym.decl_span.file_id != self.file_id or sym.ast_node.isNone()) return null;
                        const c_node = self.ast_arena.getNode(sym.ast_node);
                        if (c_node.rhs.tag != .node) return null;

                        self.active_const_eval[self.active_const_eval_len] = resolved_sym_idx;
                        self.active_const_eval_len += 1;
                        defer self.active_const_eval_len -= 1;

                        const saved_scope = self.current_scope;
                        self.current_scope = sym.scope_id;
                        defer self.current_scope = saved_scope;

                        return self.evalConstIntExpr(NodeIndex.fromInt(c_node.rhs.payload), is_emitting_diags);
                    },
                    .const_param_sym => return null,
                    .param_sym, .local_let_sym, .local_var_sym => {
                        if (sym.flags.is_comptime) return null;
                        if (is_emitting_diags) {
                            try self.emitDiagnosticSimple(
                                .e0503_forbidden_comptime_operation,
                                self.getAstNodeSpan(expr_id),
                                "compile-time constant expression cannot read runtime variable",
                                "non-`comptime` binding referenced in compile-time expression",
                            );
                        }
                        return null;
                    },
                    else => return null,
                }
            },
            .call_expr, .generic_call => {
                if (ast_node.lhs.tag != .node) return null;
                const callee_node = self.ast_arena.getNode(NodeIndex.fromInt(ast_node.lhs.payload));
                if (callee_node.tag != .ident_expr or callee_node.main_token.isNone() or
                    self.token_buffer.getToken(callee_node.main_token).kind != .at or
                    callee_node.lhs.tag != .token)
                {
                    return null;
                }
                const intr_name = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.token_buffer,
                    TokenIndex.fromInt(callee_node.lhs.payload),
                );
                const intr_kind = INTRINSIC_NAME_MAP.get(intr_name) orelse return null;
                const raw_items = self.getNodeExtraSlice(expr_id, true);
                var type_args: [4]TypeId = undefined;
                var type_arg_count: usize = 0;
                var val_args: [4]NodeIndex = undefined;
                var val_arg_count: usize = 0;
                for (raw_items) |raw_item| {
                    const item_id = NodeIndex.fromInt(raw_item);
                    if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
                    if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) {
                        if (type_arg_count < type_args.len) {
                            type_args[type_arg_count] = try self.resolveTypeAst(item_id);
                            type_arg_count += 1;
                        }
                    } else if (val_arg_count < val_args.len) {
                        val_args[val_arg_count] = item_id;
                        val_arg_count += 1;
                    }
                }

                switch (intr_kind) {
                    .size_of => {
                        if (type_arg_count != 1 or type_args[0].isError() or
                            self.pool.getFlags(type_args[0]).has_type_vars) return null;
                        return @intCast(self.computeTypeLayout(type_args[0], self.target_layout).byte_size);
                    },
                    .align_of => {
                        if (type_arg_count != 1 or type_args[0].isError() or
                            self.pool.getFlags(type_args[0]).has_type_vars) return null;
                        return @intCast(self.computeTypeLayout(type_args[0], self.target_layout).align_bytes);
                    },
                    .implements => {
                        if (type_arg_count != 2 or type_args[0].isError() or type_args[1].isError() or
                            self.pool.getFlags(type_args[0]).has_type_vars) return null;
                        return if (try self.hasTraitImplementation(type_args[0], type_args[1], 0)) 1 else 0;
                    },
                    .has_field => {
                        if (type_arg_count != 1 or val_arg_count != 1 or type_args[0].isError() or
                            self.pool.getFlags(type_args[0]).has_type_vars) return null;
                        const name_node = self.ast_arena.getNode(val_args[0]);
                        if (name_node.tag != .string_lit) return null;
                        const raw_lit = symbol_resolver.extractTokenSlice(
                            self.source,
                            self.token_buffer,
                            name_node.main_token,
                        );
                        if (raw_lit.len < 2) return null;
                        const field_name = raw_lit[1 .. raw_lit.len - 1];
                        return if (try self.hasTypeMember(type_args[0], field_name)) 1 else 0;
                    },
                    else => return null,
                }
            },
            else => return null,
        }
    }

    /// Returns `true` if `target_ty` has an accessible field or method named `member_name`.
    fn hasTypeMember(self: *TypeChecker, target_ty: TypeId, member_name: []const u8) !bool {
        const unwrapped = self.unwrapRefType(target_ty);
        const node = self.pool.getNode(unwrapped);
        if ((node.tag == .slice_ty or node.tag == .array_ty or node.tag == .soa_slice_ty or
            node.tag == .soa_array_ty or unwrapped == .str_ty) and std.mem.eql(u8, member_name, "len"))
        {
            return true;
        }
        if (node.tag == .struct_ty or node.tag == .union_ty or node.tag == .bit_field_ty or
            node.tag == .enum_ty or node.tag == .trait_ty)
        {
            const nom_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
            if (!nom_sym.target_scope.isNone()) {
                const sym_id = try self.interner.intern(member_name);
                switch (self.sym_table.lookupInTargetScope(
                    nom_sym.target_scope,
                    self.current_scope,
                    sym_id,
                    NamespaceMask.VALUE_ONLY,
                )) {
                    .found => return true,
                    else => return false,
                }
            }
        }
        return false;
    }

    /// Quietly resolves `.ident_expr` or `.path_expr` to its `SymbolIndex` without emitting diagnostics.
    fn lookupExprSymbolQuiet(self: *TypeChecker, expr_id: NodeIndex) !SymbolIndex {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.tag == .ident_expr) {
            if (!ast_node.main_token.isNone() and
                self.token_buffer.getToken(ast_node.main_token).kind == .at) return .none;
            const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, ast_node.main_token);
            if (lex.len == 0) return .none;
            const sym_id = try self.interner.intern(lex);
            return switch (self.sym_table.lookupLexical(self.current_scope, sym_id, NamespaceMask.ALL)) {
                .found => |idx| idx,
                else => .none,
            };
        }
        if (ast_node.tag == .path_expr) {
            const raw_segs = self.getNodeExtraSlice(expr_id, false);
            if (raw_segs.len == 0) return .none;
            const seg_tokens = try self.allocator.alloc(TokenIndex, raw_segs.len);
            defer self.allocator.free(seg_tokens);
            for (raw_segs, 0..) |raw_tok, i| {
                seg_tokens[i] = TokenIndex.fromInt(raw_tok);
            }
            const target_scope = try symbol_resolver.resolveModulePathSegments(
                self.sym_table,
                self.interner,
                self.file_id,
                self.current_scope,
                self.current_scope,
                seg_tokens[0 .. seg_tokens.len - 1],
                self.source,
                self.token_buffer,
                null,
            );
            if (target_scope.isNone()) return .none;
            const last_lex = symbol_resolver.extractTokenSlice(
                self.source,
                self.token_buffer,
                seg_tokens[seg_tokens.len - 1],
            );
            const last_sym_id = try self.interner.intern(last_lex);
            return switch (self.sym_table.lookupInTargetScope(
                target_scope,
                self.current_scope,
                last_sym_id,
                NamespaceMask.ALL,
            )) {
                .found => |idx| idx,
                else => .none,
            };
        }
        return .none;
    }

    /// Lazily populates the 8 `std::meta` reflection mirror types, fields, variants, and methods (`DR-05` §3.3).
    pub fn ensureReflectionMirrorTypes(self: *TypeChecker) !void {
        if (self.has_reflection_mirrors and !self.mirror_type_info_ty.isError()) return;

        const meta_scope = try self.sym_table.ensureStdMetaScope(self.interner);
        const lookupMetaSym = struct {
            fn get(checker: *TypeChecker, scope: ScopeId, name: []const u8) !SymbolIndex {
                const sym_id = try checker.interner.intern(name);
                return checker.sym_table.lookupInScopeDirect(scope, sym_id, NamespaceMask.TYPE_ONLY);
            }
        }.get;

        const meta_id_sym = try lookupMetaSym(self, meta_scope, "MetaId");
        const prim_kind_sym = try lookupMetaSym(self, meta_scope, "PrimKind");
        const field_info_sym = try lookupMetaSym(self, meta_scope, "FieldInfo");
        const struct_info_sym = try lookupMetaSym(self, meta_scope, "StructInfo");
        const variant_info_sym = try lookupMetaSym(self, meta_scope, "VariantInfo");
        const enum_info_sym = try lookupMetaSym(self, meta_scope, "EnumInfo");
        const type_kind_sym = try lookupMetaSym(self, meta_scope, "TypeKind");
        const type_info_sym = try lookupMetaSym(self, meta_scope, "TypeInfo");

        // Reuse existing `InternPool` handles if another `TypeChecker` on the same `SymbolTable` populated them:
        if (!self.sym_table.getSymbol(type_info_sym).type_id.isError()) {
            self.mirror_meta_id_ty = self.sym_table.getSymbol(meta_id_sym).type_id;
            self.mirror_prim_kind_ty = self.sym_table.getSymbol(prim_kind_sym).type_id;
            self.mirror_field_info_ty = self.sym_table.getSymbol(field_info_sym).type_id;
            self.mirror_struct_info_ty = self.sym_table.getSymbol(struct_info_sym).type_id;
            self.mirror_variant_info_ty = self.sym_table.getSymbol(variant_info_sym).type_id;
            self.mirror_enum_info_ty = self.sym_table.getSymbol(enum_info_sym).type_id;
            self.mirror_type_kind_ty = self.sym_table.getSymbol(type_kind_sym).type_id;
            self.mirror_type_info_ty = self.sym_table.getSymbol(type_info_sym).type_id;
            self.has_reflection_mirrors = true;
            return;
        }

        const bindNominal = struct {
            fn run(checker: *TypeChecker, tag: TypeTag, sym_idx: SymbolIndex, ordinal_seed: u32) !TypeId {
                const tid = try checker.pool.internNominal(tag, 0xFFFF_0000 | ordinal_seed, sym_idx, true, false, false);
                checker.sym_table.getSymbolMut(sym_idx).type_id = tid;
                try checker.sym_table.type_to_symbol.put(checker.allocator, tid.toU32(), sym_idx);
                return tid;
            }
        }.run;

        const addField = struct {
            fn run(checker: *TypeChecker, scope: ScopeId, name: []const u8, ty: TypeId, ord: u16) !void {
                const field_id = try checker.interner.intern(name);
                _ = try checker.sym_table.defineSymbol(.{
                    .name = field_id,
                    .name_text = checker.interner.get(field_id),
                    .kind = .field_sym,
                    .namespace = .value_ns,
                    .visibility = .public,
                    .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                    .scope_id = scope,
                    .type_id = ty,
                    .member_ordinal = ord,
                }, null);
            }
        }.run;

        const addVariant = struct {
            fn run(checker: *TypeChecker, scope: ScopeId, name: []const u8, payload: TypeId, ord: u16) !void {
                const variant_id = try checker.interner.intern(name);
                _ = try checker.sym_table.defineSymbol(.{
                    .name = variant_id,
                    .name_text = checker.interner.get(variant_id),
                    .kind = .enum_variant_sym,
                    .namespace = .value_ns,
                    .visibility = .public,
                    .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                    .scope_id = scope,
                    .type_id = payload,
                    .member_ordinal = ord,
                }, null);
            }
        }.run;

        self.mirror_meta_id_ty = try bindNominal(self, .struct_ty, meta_id_sym, 1);
        self.mirror_prim_kind_ty = try bindNominal(self, .enum_ty, prim_kind_sym, 2);
        self.mirror_field_info_ty = try bindNominal(self, .struct_ty, field_info_sym, 3);
        self.mirror_struct_info_ty = try bindNominal(self, .struct_ty, struct_info_sym, 4);
        self.mirror_variant_info_ty = try bindNominal(self, .struct_ty, variant_info_sym, 5);
        self.mirror_enum_info_ty = try bindNominal(self, .struct_ty, enum_info_sym, 6);
        self.mirror_type_kind_ty = try bindNominal(self, .enum_ty, type_kind_sym, 7);
        self.mirror_type_info_ty = try bindNominal(self, .struct_ty, type_info_sym, 8);

        // `MetaId { raw_id: u32 }`:
        try addField(self, self.sym_table.getSymbol(meta_id_sym).target_scope, "raw_id", .u32_ty, 0);

        // `PrimKind` 19 variants (`DR-05` §3.3):
        const prim_variants = [_][]const u8{
            "Bool", "I8", "I16", "I32", "I64", "I128", "Isize",
            "U8", "U16", "U32", "U64", "U128", "Usize",
            "F32", "F64", "Char", "Str", "Unit", "Never",
        };
        const prim_scope = self.sym_table.getSymbol(prim_kind_sym).target_scope;
        for (prim_variants, 0..) |variant_name, i| {
            try addVariant(self, prim_scope, variant_name, .unit_ty, @intCast(i));
        }

        // `FieldInfo`:
        const field_info_scope = self.sym_table.getSymbol(field_info_sym).target_scope;
        try addField(self, field_info_scope, "index", .u32_ty, 0);
        try addField(self, field_info_scope, "name", .str_ty, 1);
        try addField(self, field_info_scope, "ty_id", self.mirror_meta_id_ty, 2);
        try addField(self, field_info_scope, "byte_offset", .usize_ty, 3);
        try addField(self, field_info_scope, "is_pub", .bool_ty, 4);
        try addField(self, field_info_scope, "has_default", .bool_ty, 5);

        // `FieldInfo.get_attr[A](&self) -> A?`:
        const get_attr_fn_scope = try self.sym_table.scope_arena.allocScope(
            .fn_scope,
            field_info_scope,
            .NONE,
            .none,
            .{ .is_comptime_context = true },
        );
        const attr_param_sym_id = try self.interner.intern("A");
        const attr_type_param = try self.pool.internTypeParam(.group_copy, attr_param_sym_id);
        _ = try self.sym_table.defineSymbol(.{
            .name = attr_param_sym_id,
            .name_text = self.interner.get(attr_param_sym_id),
            .kind = .type_param_sym,
            .namespace = .type_ns,
            .visibility = .private,
            .flags = .{ .is_used = true, .is_builtin = true },
            .scope_id = get_attr_fn_scope,
            .type_id = attr_type_param,
        }, null);
        const field_info_ref_ty = try self.pool.internRef(self.mirror_field_info_ty, false);
        const opt_attr_ty = try self.pool.internOptional(attr_type_param);
        const get_attr_fn_ty = try self.pool.internFn(
            .fn_ty,
            &[_]TypeId{field_info_ref_ty},
            &[_]ParamMode{.let_mode},
            opt_attr_ty,
            false,
        );
        const get_attr_id = try self.interner.intern("get_attr");
        _ = try self.sym_table.defineSymbol(.{
            .name = get_attr_id,
            .name_text = self.interner.get(get_attr_id),
            .kind = .fn_sym,
            .namespace = .value_ns,
            .visibility = .public,
            .flags = .{
                .is_pub = true,
                .is_used = true,
                .is_builtin = true,
                .is_prototype_only = true,
                .is_comptime = true,
            },
            .scope_id = field_info_scope,
            .target_scope = get_attr_fn_scope,
            .type_id = get_attr_fn_ty,
        }, null);

        // `StructInfo`:
        const field_slice_ty = try self.pool.internSlice(self.mirror_field_info_ty, false);
        const struct_info_scope = self.sym_table.getSymbol(struct_info_sym).target_scope;
        try addField(self, struct_info_scope, "fields", field_slice_ty, 0);
        try addField(self, struct_info_scope, "is_repr_c", .bool_ty, 1);
        try addField(self, struct_info_scope, "is_soa_compatible", .bool_ty, 2);

        // `VariantInfo`:
        const variant_info_scope = self.sym_table.getSymbol(variant_info_sym).target_scope;
        try addField(self, variant_info_scope, "index", .u32_ty, 0);
        try addField(self, variant_info_scope, "name", .str_ty, 1);
        try addField(self, variant_info_scope, "discriminant", .i128_ty, 2);
        try addField(self, variant_info_scope, "fields", field_slice_ty, 3);

        // `EnumInfo`:
        const variant_slice_ty = try self.pool.internSlice(self.mirror_variant_info_ty, false);
        const enum_info_scope = self.sym_table.getSymbol(enum_info_sym).target_scope;
        try addField(self, enum_info_scope, "tag_ty", self.mirror_prim_kind_ty, 0);
        try addField(self, enum_info_scope, "variants", variant_slice_ty, 1);
        try addField(self, enum_info_scope, "is_niche_optimized", .bool_ty, 2);

        // `TypeKind`:
        const type_kind_scope = self.sym_table.getSymbol(type_kind_sym).target_scope;
        const arr_tup_ty = try self.pool.internTuple(&[_]TypeId{ self.mirror_meta_id_ty, .usize_ty });
        const res_tup_ty = try self.pool.internTuple(&[_]TypeId{ self.mirror_meta_id_ty, self.mirror_meta_id_ty });
        const ptr_tup_ty = try self.pool.internTuple(&[_]TypeId{ self.mirror_meta_id_ty, .bool_ty });
        const bf_tup_ty = try self.pool.internTuple(&[_]TypeId{ self.mirror_meta_id_ty, .u16_ty });
        try addVariant(self, type_kind_scope, "Primitive", self.mirror_prim_kind_ty, 0);
        try addVariant(self, type_kind_scope, "Struct", self.mirror_struct_info_ty, 1);
        try addVariant(self, type_kind_scope, "Enum", self.mirror_enum_info_ty, 2);
        try addVariant(self, type_kind_scope, "Array", arr_tup_ty, 3);
        try addVariant(self, type_kind_scope, "Slice", self.mirror_meta_id_ty, 4);
        try addVariant(self, type_kind_scope, "Option", self.mirror_meta_id_ty, 5);
        try addVariant(self, type_kind_scope, "Result", res_tup_ty, 6);
        try addVariant(self, type_kind_scope, "Pointer", ptr_tup_ty, 7);
        try addVariant(self, type_kind_scope, "SoaSlice", self.mirror_meta_id_ty, 8);
        try addVariant(self, type_kind_scope, "BitField", bf_tup_ty, 9);

        // `TypeInfo` + `as_struct` / `as_enum`:
        const type_info_scope = self.sym_table.getSymbol(type_info_sym).target_scope;
        try addField(self, type_info_scope, "id", self.mirror_meta_id_ty, 0);
        try addField(self, type_info_scope, "name", .str_ty, 1);
        try addField(self, type_info_scope, "qualified_name", .str_ty, 2);
        try addField(self, type_info_scope, "size", .usize_ty, 3);
        try addField(self, type_info_scope, "alignment", .usize_ty, 4);
        try addField(self, type_info_scope, "kind", self.mirror_type_kind_ty, 5);

        const type_info_ref_ty = try self.pool.internRef(self.mirror_type_info_ty, false);
        const as_struct_ty = try self.pool.internFn(
            .fn_ty,
            &[_]TypeId{type_info_ref_ty},
            &[_]ParamMode{.let_mode},
            self.mirror_struct_info_ty,
            false,
        );
        const as_struct_id = try self.interner.intern("as_struct");
        _ = try self.sym_table.defineSymbol(.{
            .name = as_struct_id,
            .name_text = self.interner.get(as_struct_id),
            .kind = .fn_sym,
            .namespace = .value_ns,
            .visibility = .public,
            .flags = .{
                .is_pub = true,
                .is_used = true,
                .is_builtin = true,
                .is_prototype_only = true,
                .is_comptime = true,
            },
            .scope_id = type_info_scope,
            .type_id = as_struct_ty,
        }, null);

        const as_enum_ty = try self.pool.internFn(
            .fn_ty,
            &[_]TypeId{type_info_ref_ty},
            &[_]ParamMode{.let_mode},
            self.mirror_enum_info_ty,
            false,
        );
        const as_enum_id = try self.interner.intern("as_enum");
        _ = try self.sym_table.defineSymbol(.{
            .name = as_enum_id,
            .name_text = self.interner.get(as_enum_id),
            .kind = .fn_sym,
            .namespace = .value_ns,
            .visibility = .public,
            .flags = .{
                .is_pub = true,
                .is_used = true,
                .is_builtin = true,
                .is_prototype_only = true,
                .is_comptime = true,
            },
            .scope_id = type_info_scope,
            .type_id = as_enum_ty,
        }, null);

        self.has_reflection_mirrors = true;
    }

    /// Resolves a `.named_type` AST node to its underlying `SymbolRecord.type_id` without wrapping in `bind_once_group_var`.
    fn resolveNamedOrGroupTypeRaw(self: *TypeChecker, type_node_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(type_node_id);
        const type_cst = self.ast_arena.getCstOrigin(type_node_id);

        // Check if `type_cst` has leading `module::` path segments:
        var seg_tokens: std.ArrayListUnmanaged(TokenIndex) = .empty;
        defer seg_tokens.deinit(self.allocator);
        if (!type_cst.isNone() and type_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = type_cst.asInt();
            const rec = self.cst_arena.getNode(type_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var cur = start_idx + 1;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.kind == .type_args and sub.subtree_size > 1) break;
                const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
                if (is_leaf and !sub.flags.is_missing_or_injected and
                    !sub.token.isNone() and sub.token.asInt() < self.token_buffer.countTokens())
                {
                    const kind = self.token_buffer.getToken(sub.token).kind;
                    if (symbol_resolver.isIdentifierToken(kind) or kind == .kw_self_type or kind == .prim_type) {
                        try seg_tokens.append(self.allocator, sub.token);
                    }
                }
            }
        }
        const seg_count = seg_tokens.items.len;

        const target_tok = if (seg_count > 0) seg_tokens.items[seg_count - 1] else ast_node.main_token;
        const target_lexeme = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, target_tok);
        if (target_lexeme.len == 0) return .err_ty;

        for (symbol_resolver.BUILTIN_TYPES_AND_GROUPS) |entry| {
            if (seg_count <= 1 and std.mem.eql(u8, entry.name, target_lexeme)) {
                return entry.type_id;
            }
        }

        if (REFLECTION_MIRROR_NAME_MAP.has(target_lexeme)) {
            try self.ensureReflectionMirrorTypes();
        }

        const target_sym_id = try self.interner.intern(target_lexeme);
        const target_span = self.token_buffer.getTokenSpan(self.file_id, target_tok);

        const lookup_scope = if (seg_count > 1)
            try symbol_resolver.resolveModulePathSegments(
                self.sym_table,
                self.interner,
                self.file_id,
                self.current_scope,
                self.current_scope,
                seg_tokens.items[0 .. seg_count - 1],
                self.source,
                self.token_buffer,
                self.diagnostic_sink,
            )
        else
            self.current_scope;

        if (lookup_scope.isNone()) return .err_ty;

        const lookup_res = if (seg_count <= 1)
            self.sym_table.lookupLexical(lookup_scope, target_sym_id, NamespaceMask.TYPE_ONLY)
        else
            self.sym_table.lookupInTargetScope(
                lookup_scope,
                self.current_scope,
                target_sym_id,
                NamespaceMask.TYPE_ONLY,
            );

        switch (lookup_res) {
            .found => |sym_idx| {
                self.sym_table.markSymbolUsed(sym_idx);
                const sym = self.sym_table.getSymbol(sym_idx);
                if (sym.type_id.isError() and sym.kind == .trait_sym) {
                    return self.ensureTraitSymbolTypeId(sym_idx);
                }
                if (sym.type_id.isError() and
                    (sym.kind == .struct_sym or sym.kind == .enum_sym) and
                    sym.flags.is_builtin)
                {
                    try self.ensureReflectionMirrorTypes();
                    return self.sym_table.getSymbol(sym_idx).type_id;
                }
                if (sym.type_id.isError() and
                    (sym.kind == .type_alias_sym or sym.kind == .distinct_type_sym or
                        sym.kind == .refined_type_sym or sym.kind == .type_group_sym))
                {
                    const resolved_alias = try self.resolveTypeAliasSymbol(sym_idx);
                    self.sym_table.getSymbolMut(sym_idx).type_id = resolved_alias;
                    return resolved_alias;
                }
                return sym.type_id;
            },
            .private_error => |priv_idx| {
                if (self.diagnostic_sink) |sink| {
                    try symbol_resolver.emitPrivateAccessDiagnostic(
                        sink,
                        self.sym_table.getSymbol(priv_idx),
                        target_span,
                    );
                }
                return .err_ty;
            },
            .not_found => {
                // Allow unqualified `TypeInfo` / `FieldInfo` fallback into `std::meta` when not shadowed:
                if (seg_count <= 1 and REFLECTION_MIRROR_NAME_MAP.has(target_lexeme)) {
                    const meta_scope = try self.sym_table.ensureStdMetaScope(self.interner);
                    const meta_sym_idx = self.sym_table.lookupInScopeDirect(
                        meta_scope,
                        target_sym_id,
                        NamespaceMask.TYPE_ONLY,
                    );
                    if (!meta_sym_idx.isNone()) {
                        return self.sym_table.getSymbol(meta_sym_idx).type_id;
                    }
                }
                if (self.diagnostic_sink) |sink| {
                    const suggestion = if (seg_count <= 1)
                        self.sym_table.suggestClosestSymbol(
                            self.current_scope,
                            target_lexeme,
                            NamespaceMask.TYPE_ONLY,
                        )
                    else
                        self.sym_table.suggestClosestInScope(
                            lookup_scope,
                            target_lexeme,
                            NamespaceMask.TYPE_ONLY,
                        );
                    try symbol_resolver.emitUnresolvedSymbolDiagnostic(
                        sink,
                        self.interner,
                        target_lexeme,
                        target_span,
                        suggestion,
                    );
                }
                return .err_ty;
            },
        }
    }

    /// Returns `true` if `cst_id` contains a direct `.kw_mut` token leaf.
    fn hasMutKeywordInCst(self: *const TypeChecker, cst_id: CstNodeIndex) bool {
        if (cst_id.isNone() or cst_id.asInt() >= self.cst_arena.countNodes()) return false;
        const start_idx: usize = cst_id.asInt();
        const rec = self.cst_arena.getNode(cst_id);
        const end_idx: usize = @min(start_idx + @max(@as(usize, rec.subtree_size), 1), self.cst_arena.countNodes());
        var cur = start_idx + 1;
        while (cur < end_idx) : (cur += 1) {
            const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (sub.subtree_size <= 1 and !sub.token.isNone() and
                sub.token.asInt() < self.token_buffer.countTokens() and
                self.token_buffer.getToken(sub.token).kind == .kw_mut)
            {
                return true;
            }
        }
        return false;
    }

    /// Extracts inclusive `[min_val, max_val]` integer bounds from a range pattern AST node (`low..=high` or `low..high`).
    pub fn extractPatternRangeBounds(self: *const TypeChecker, pat_node_id: NodeIndex) ?Interval128 {
        if (pat_node_id.isNone() or pat_node_id.asInt() >= self.ast_arena.countNodes()) return null;
        const pat_node = self.ast_arena.getNode(pat_node_id);
        if (pat_node.tag != .lit_pat) return null;

        // Single literal pattern (`42` or `-5`):
        if (pat_node.lhs.tag == .none and pat_node.rhs.tag == .none) {
            const single_val = self.extractSignedPatternTokenValue(
                pat_node.main_token,
                self.ast_arena.getCstOrigin(pat_node_id),
            ) orelse return null;
            return .{ .min_val = single_val, .max_val = single_val };
        }

        // Range pattern (`lhs = .node(low_pat)`, `main_token = range_tok`, `rhs = .token(end_tok)`):
        if (pat_node.lhs.tag != .node or pat_node.rhs.tag != .token) return null;
        const low_pat_id = NodeIndex.fromInt(pat_node.lhs.payload);
        const low_pat = self.ast_arena.getNode(low_pat_id);
        const low_val = self.extractSignedPatternTokenValue(
            low_pat.main_token,
            self.ast_arena.getCstOrigin(low_pat_id),
        ) orelse return null;

        const end_tok = TokenIndex.fromInt(pat_node.rhs.payload);
        const high_raw = self.extractSignedEndTokenValue(
            end_tok,
            pat_node.main_token,
            self.ast_arena.getCstOrigin(pat_node_id),
        ) orelse return null;

        const range_kind = self.token_buffer.getToken(pat_node.main_token).kind;
        if (range_kind == .dotdot) {
            if (high_raw <= low_val) return .{ .min_val = 1, .max_val = 0 };
            return .{ .min_val = low_val, .max_val = high_raw - 1 };
        }
        return .{ .min_val = low_val, .max_val = high_raw };
    }

    /// Extracts order-preserving biased `i128` interval bounds (`val ^ (1 << 127)`) for `u128` match patterns (`CRIT-07`).
    fn extractBiasedU128PatternRangeBounds(self: *const TypeChecker, pat_node_id: NodeIndex) ?Interval128 {
        if (pat_node_id.isNone() or pat_node_id.asInt() >= self.ast_arena.countNodes()) return null;
        const pat_node = self.ast_arena.getNode(pat_node_id);
        if (pat_node.tag != .lit_pat) return null;
        const sign_bias: u128 = @as(u128, 1) << 127;

        if (pat_node.lhs.tag == .none and pat_node.rhs.tag == .none) {
            const single_u = self.extractUnsignedPatternTokenValue(pat_node.main_token) orelse return null;
            const biased: i128 = @bitCast(single_u ^ sign_bias);
            return .{ .min_val = biased, .max_val = biased };
        }

        if (pat_node.lhs.tag != .node or pat_node.rhs.tag != .token) return null;
        const low_pat_id = NodeIndex.fromInt(pat_node.lhs.payload);
        const low_pat = self.ast_arena.getNode(low_pat_id);
        const low_u = self.extractUnsignedPatternTokenValue(low_pat.main_token) orelse return null;
        const end_tok = TokenIndex.fromInt(pat_node.rhs.payload);
        const high_raw_u = self.extractUnsignedEndTokenValue(
            end_tok,
            pat_node.main_token,
            self.ast_arena.getCstOrigin(pat_node_id),
        ) orelse return null;

        const range_kind = self.token_buffer.getToken(pat_node.main_token).kind;
        const high_u = if (range_kind == .dotdot) blk: {
            if (high_raw_u <= low_u) return .{ .min_val = 1, .max_val = 0 };
            break :blk high_raw_u - 1;
        } else high_raw_u;
        if (low_u > high_u) return .{ .min_val = 1, .max_val = 0 };
        return .{
            .min_val = @bitCast(low_u ^ sign_bias),
            .max_val = @bitCast(high_u ^ sign_bias),
        };
    }

    /// Evaluates a non-negative pattern literal token (`int_lit` or `char_lit`) to `u128`.
    fn extractUnsignedPatternTokenValue(self: *const TypeChecker, tok_idx: TokenIndex) ?u128 {
        if (tok_idx.isNone() or tok_idx.asInt() >= self.token_buffer.countTokens()) return null;
        const kind = self.token_buffer.getToken(tok_idx).kind;
        if (kind == .int_lit) {
            const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, tok_idx);
            if (lex.len > 0 and lex[0] == '-') return null;
            const parsed = extractIntLiteralValue(lex) orelse return null;
            return parsed.magnitude;
        }
        if (kind == .char_lit) {
            const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, tok_idx);
            if (extractCharLiteralCodepoint(lex)) |cp| return @as(u128, cp);
        }
        return null;
    }

    /// Evaluates the upper-bound token of an unsigned `u128` range pattern, rejecting leading `-`.
    fn extractUnsignedEndTokenValue(
        self: *const TypeChecker,
        end_tok: TokenIndex,
        range_tok: TokenIndex,
        range_cst: CstNodeIndex,
    ) ?u128 {
        if (end_tok.isNone() or end_tok.asInt() >= self.token_buffer.countTokens()) return null;
        if (!range_cst.isNone() and range_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = range_cst.asInt();
            const rec = self.cst_arena.getNode(range_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var is_after_range = false;
            var cur = start_idx;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.subtree_size <= 1 and !sub.token.isNone() and
                    sub.token.asInt() < self.token_buffer.countTokens())
                {
                    if (sub.token == range_tok) {
                        is_after_range = true;
                    } else if (sub.token == end_tok) {
                        break;
                    } else if (is_after_range and self.token_buffer.getToken(sub.token).kind == .minus) {
                        return null;
                    }
                }
            }
        }
        return self.extractUnsignedPatternTokenValue(end_tok);
    }

    /// Evaluates a pattern literal token (with optional leading `-` inside `pat_cst`) to `i128` (`CRIT-07`).
    fn extractSignedPatternTokenValue(
        self: *const TypeChecker,
        tok_idx: TokenIndex,
        pat_cst: CstNodeIndex,
    ) ?i128 {
        if (tok_idx.isNone() or tok_idx.asInt() >= self.token_buffer.countTokens()) return null;
        const kind = self.token_buffer.getToken(tok_idx).kind;
        const min_abs: u128 = @as(u128, @intCast(std.math.maxInt(i128))) + 1;
        if (kind == .minus) {
            // Find the numeric token immediately following `-` inside `pat_cst` or `token_buffer`:
            if (!pat_cst.isNone() and pat_cst.asInt() < self.cst_arena.countNodes()) {
                const start_idx: usize = pat_cst.asInt();
                const rec = self.cst_arena.getNode(pat_cst);
                const end_idx: usize = @min(
                    start_idx + @max(@as(usize, rec.subtree_size), 1),
                    self.cst_arena.countNodes(),
                );
                var has_seen_minus = false;
                var cur = start_idx;
                while (cur < end_idx) : (cur += 1) {
                    const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                    if (sub.subtree_size <= 1 and !sub.token.isNone() and
                        sub.token.asInt() < self.token_buffer.countTokens())
                    {
                        if (sub.token == tok_idx) {
                            has_seen_minus = true;
                        } else if (has_seen_minus and self.token_buffer.getToken(sub.token).kind == .int_lit) {
                            const lex = symbol_resolver.extractTokenSlice(
                                self.source,
                                self.token_buffer,
                                sub.token,
                            );
                            const parsed = extractIntLiteralValue(lex) orelse return null;
                            if (parsed.magnitude > min_abs) return null;
                            if (parsed.magnitude == min_abs) return std.math.minInt(i128);
                            return -@as(i128, @intCast(parsed.magnitude));
                        }
                    }
                }
            }
            return null;
        }
        if (kind == .int_lit) {
            const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, tok_idx);
            const parsed = extractIntLiteralValue(lex) orelse return null;
            if (parsed.is_above_i128_max) return null;
            return parsed.value;
        }
        if (kind == .char_lit) {
            const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, tok_idx);
            if (extractCharLiteralCodepoint(lex)) |cp| return @as(i128, cp);
        }
        return null;
    }

    /// Evaluates the upper-bound token of a range pattern (checking for `-` between `range_tok` and `end_tok`).
    fn extractSignedEndTokenValue(
        self: *const TypeChecker,
        end_tok: TokenIndex,
        range_tok: TokenIndex,
        range_cst: CstNodeIndex,
    ) ?i128 {
        if (end_tok.isNone() or end_tok.asInt() >= self.token_buffer.countTokens()) return null;
        var is_neg = false;
        if (!range_cst.isNone() and range_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = range_cst.asInt();
            const rec = self.cst_arena.getNode(range_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var is_after_range = false;
            var cur = start_idx;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.subtree_size <= 1 and !sub.token.isNone() and
                    sub.token.asInt() < self.token_buffer.countTokens())
                {
                    if (sub.token == range_tok) {
                        is_after_range = true;
                    } else if (sub.token == end_tok) {
                        break;
                    } else if (is_after_range and self.token_buffer.getToken(sub.token).kind == .minus) {
                        is_neg = true;
                    }
                }
            }
        }
        const kind = self.token_buffer.getToken(end_tok).kind;
        if (kind == .int_lit) {
            const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, end_tok);
            const parsed = extractIntLiteralValue(lex) orelse return null;
            if (is_neg) {
                const min_abs: u128 = @as(u128, @intCast(std.math.maxInt(i128))) + 1;
                if (parsed.magnitude > min_abs) return null;
                if (parsed.magnitude == min_abs) return std.math.minInt(i128);
                return -@as(i128, @intCast(parsed.magnitude));
            }
            if (parsed.is_above_i128_max) return null;
            return parsed.value;
        }
        if (kind == .char_lit) {
            const lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, end_tok);
            if (extractCharLiteralCodepoint(lex)) |cp| return @as(i128, cp);
        }
        return null;
    }

    // -------- Pass 2: Spine-Local Bidirectional Body Check --------

    /// Type-checks all function, constant, and top-level `comptime { … }` bodies declared in `self.file_id`.
    pub fn checkFileBodies(self: *TypeChecker) !void {
        const sym_count = self.sym_table.countSymbols();
        var idx: u32 = 0;
        while (idx < sym_count) : (idx += 1) {
            const sym_idx = SymbolIndex.fromInt(idx);
            const sym = self.sym_table.getSymbol(sym_idx).*;
            if (sym.flags.is_builtin or sym.flags.is_imported) continue;
            if (!sym.decl_span.file_id.isNone() and sym.decl_span.file_id != self.file_id) continue;

            if (sym.kind == .fn_sym) {
                try self.checkFnDeclBody(sym_idx);
            } else if (sym.kind == .const_sym) {
                try self.checkConstInitializer(sym_idx);
            }
        }

        if (self.sym_table.file_module_scopes.get(self.file_id.asInt())) |mod_scope| {
            if (self.ast_arena.countNodes() > 0) {
                try self.checkModuleComptimeBlocks(.root, mod_scope);
            }
            try symbol_resolver.checkUnusedBindingsInScope(
                self.sym_table,
                mod_scope,
                self.interner,
                self.diagnostic_sink,
            );
        }
    }

    /// Recursively checks top-level `comptime { … }` blocks (`AstTag.block`) in `container_id` and inline `mod` items.
    fn checkModuleComptimeBlocks(
        self: *TypeChecker,
        container_id: NodeIndex,
        mod_scope: ScopeId,
    ) anyerror!void {
        if (container_id.isNone() or container_id.asInt() >= self.ast_arena.countNodes()) return;
        const container = self.ast_arena.getNode(container_id);
        const item_slice: []const u32 = if (container_id == .root) blk: {
            if (container.lhs.tag == .extra and container.rhs.tag == .extra and container.rhs.payload > 0) {
                break :blk self.ast_arena.getExtraSlice(
                    ExtraIndex.fromInt(container.lhs.payload),
                    container.rhs.payload,
                );
            }
            break :blk &.{};
        } else self.getNodeExtraSlice(container_id, true);

        for (item_slice) |raw_item_idx| {
            const item_idx = NodeIndex.fromInt(raw_item_idx);
            if (item_idx.asInt() >= self.ast_arena.countNodes()) continue;
            const item_node = self.ast_arena.getNode(item_idx);
            if (item_node.tag == .block) {
                try self.checkPureComptimeBlock(item_idx, mod_scope);
            } else if (item_node.tag == .mod_decl and item_node.rhs.tag == .extra) {
                for (self.sym_table.getScopeMembers(mod_scope)) |mem_idx| {
                    const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                    if (mem_sym.kind == .module_sym and mem_sym.ast_node == item_idx and
                        !mem_sym.target_scope.isNone())
                    {
                        try self.checkModuleComptimeBlocks(item_idx, mem_sym.target_scope);
                        break;
                    }
                }
            }
        }
    }

    /// Type-checks a module-level `comptime { … }` block in `mod_scope` under `pure_comptime_depth`.
    fn checkPureComptimeBlock(
        self: *TypeChecker,
        block_id: NodeIndex,
        mod_scope: ScopeId,
    ) !void {
        const saved_scope = self.current_scope;
        const prev_pure_depth = self.pure_comptime_depth;
        const prev_boundary = self.comptime_boundary_scope_depth;
        self.current_scope = mod_scope;
        if (prev_pure_depth == 0) {
            self.comptime_boundary_scope_depth = if (mod_scope.isNone())
                0
            else
                self.sym_table.scope_arena.getScope(mod_scope).depth;
        }
        self.pure_comptime_depth = prev_pure_depth + 1;
        defer {
            self.current_scope = saved_scope;
            self.pure_comptime_depth = prev_pure_depth;
            self.comptime_boundary_scope_depth = prev_boundary;
        }
        _ = try self.checkBlock(block_id, .unit_ty, false);
    }

    /// Type-checks the body of a single `DefId` in isolation (used by `CompilerDb.typecheckBody`).
    pub fn checkDefBody(self: *TypeChecker, def_id: DefId) !void {
        if (def_id.isNone()) return;
        var matched_top_ast: NodeIndex = .none;
        if (self.ast_arena.countNodes() > 0) {
            const root_node = self.ast_arena.getNode(.root);
            if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
                const item_slice = self.ast_arena.getExtraSlice(
                    ExtraIndex.fromInt(root_node.lhs.payload),
                    root_node.rhs.payload,
                );
                var top_ordinal: u12 = 0;
                for (item_slice) |raw_node_idx| {
                    const cand_node_idx = NodeIndex.fromInt(raw_node_idx);
                    if (cand_node_idx.asInt() >= self.ast_arena.countNodes()) continue;
                    if (self.ast_arena.getNode(cand_node_idx).tag == .item_hole) continue;
                    if (top_ordinal == def_id.itemIndex()) {
                        matched_top_ast = cand_node_idx;
                        break;
                    }
                    if (top_ordinal < std.math.maxInt(u12)) top_ordinal += 1;
                }
            }
        }

        if (self.sym_table.def_to_symbol.get(def_id.asInt())) |sym_idx| {
            // Refresh `ast_node` and `cst_node` from `self.ast_arena` in case preceding function bodies shifted:
            if (!matched_top_ast.isNone()) {
                const sym_mut = self.sym_table.getSymbolMut(sym_idx);
                sym_mut.ast_node = matched_top_ast;
                sym_mut.cst_node = self.ast_arena.getCstOrigin(matched_top_ast);
            }
            const sym = self.sym_table.getSymbol(sym_idx).*;
            if (sym.kind == .fn_sym) {
                if (!sym.target_scope.isNone()) {
                    for (self.sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                        if (self.sym_table.getSymbol(mem_idx).kind == .param_sym) {
                            self.sym_table.getSymbolMut(mem_idx).flags.is_used = false;
                        }
                    }
                }
                try self.checkFnDeclBody(sym_idx);
            } else if (sym.kind == .const_sym) {
                try self.checkConstInitializer(sym_idx);
            }
        } else if (!matched_top_ast.isNone()) {
            const top_tag = self.ast_arena.getNode(matched_top_ast).tag;
            if (top_tag == .block) {
                const mod_scope = self.sym_table.file_module_scopes.get(self.file_id.asInt()) orelse
                    self.sym_table.prelude_scope;
                try self.checkPureComptimeBlock(matched_top_ast, mod_scope);
            } else if (top_tag == .impl_decl) {
                const impl_members = symbol_resolver.extractImplMemberItems(self.ast_arena, matched_top_ast);
                var mem_cursor: usize = 0;
                var sym_raw: u32 = 0;
                while (sym_raw < self.sym_table.symbols.items.len) : (sym_raw += 1) {
                    const cand_sym_idx = SymbolIndex.fromInt(sym_raw);
                    const cand_sym = self.sym_table.getSymbol(cand_sym_idx).*;
                    if (cand_sym.owner_def_id != def_id) continue;
                    if (cand_sym.kind != .fn_sym and cand_sym.kind != .const_sym) continue;

                    while (mem_cursor < impl_members.len) {
                        const mem_ast_idx = NodeIndex.fromInt(impl_members[mem_cursor]);
                        mem_cursor += 1;
                        if (mem_ast_idx.asInt() >= self.ast_arena.countNodes()) continue;
                        const mem_ast = self.ast_arena.getNode(mem_ast_idx);
                        const is_kind_match = (cand_sym.kind == .fn_sym and mem_ast.tag == .fn_decl) or
                            (cand_sym.kind == .const_sym and mem_ast.tag == .const_decl);
                        if (!is_kind_match) continue;
                        const sym_mut = self.sym_table.getSymbolMut(cand_sym_idx);
                        sym_mut.ast_node = mem_ast_idx;
                        sym_mut.cst_node = self.ast_arena.getCstOrigin(mem_ast_idx);
                        break;
                    }

                    if (cand_sym.kind == .fn_sym) {
                        if (!cand_sym.target_scope.isNone()) {
                            for (self.sym_table.getScopeMembers(cand_sym.target_scope)) |param_idx| {
                                if (self.sym_table.getSymbol(param_idx).kind == .param_sym) {
                                    self.sym_table.getSymbolMut(param_idx).flags.is_used = false;
                                }
                            }
                        }
                        try self.checkFnDeclBody(cand_sym_idx);
                    } else if (cand_sym.kind == .const_sym) {
                        try self.checkConstInitializer(cand_sym_idx);
                    }
                }
            }
        }
    }

    /// Checks a `const` declaration's initializer expression against its explicit type under `pure_comptime_depth`.
    fn checkConstInitializer(self: *TypeChecker, const_sym_idx: SymbolIndex) !void {
        const sym = self.sym_table.getSymbol(const_sym_idx).*;
        if (sym.ast_node.isNone()) return;
        const c_node = self.ast_arena.getNode(sym.ast_node);
        if (c_node.rhs.tag != .node) return;

        const saved_scope = self.current_scope;
        const prev_pure_depth = self.pure_comptime_depth;
        const prev_boundary = self.comptime_boundary_scope_depth;
        self.current_scope = sym.scope_id;
        if (prev_pure_depth == 0) {
            self.comptime_boundary_scope_depth = if (sym.scope_id.isNone())
                0
            else
                self.sym_table.scope_arena.getScope(sym.scope_id).depth;
        }
        self.pure_comptime_depth = prev_pure_depth + 1;
        defer {
            self.current_scope = saved_scope;
            self.pure_comptime_depth = prev_pure_depth;
            self.comptime_boundary_scope_depth = prev_boundary;
        }

        const init_node_id = NodeIndex.fromInt(c_node.rhs.payload);
        if (!sym.type_id.isError()) {
            _ = try self.checkExpr(init_node_id, sym.type_id);
        } else {
            const inferred_ty = try self.synthExpr(init_node_id);
            self.sym_table.getSymbolMut(const_sym_idx).type_id = self.materializeUntypedType(inferred_ty);
        }

        const resolved_const_ty = self.sym_table.getSymbol(const_sym_idx).type_id;
        if ((resolved_const_ty.isIntegerPrimitive() or resolved_const_ty == .bool_ty) and
            self.active_const_eval_len < self.active_const_eval.len)
        {
            self.active_const_eval[self.active_const_eval_len] = const_sym_idx;
            self.active_const_eval_len += 1;
            defer self.active_const_eval_len -= 1;
            _ = try self.evalConstIntExpr(init_node_id, true);
        }
    }

    /// Type-checks a block-local `const NAME: T = EXPR;` declaration (`DR-05` Showcases A & B).
    fn checkLocalConstDecl(self: *TypeChecker, decl_id: NodeIndex) anyerror!TypeId {
        const decl_node = self.ast_arena.getNode(decl_id);
        const decl_cst = self.ast_arena.getCstOrigin(decl_id);

        var name_tok: TokenIndex = .none;
        if (!decl_cst.isNone() and decl_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = decl_cst.asInt();
            const rec = self.cst_arena.getNode(decl_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var cur = start_idx + 1;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.subtree_size <= 1 and !sub.token.isNone() and
                    sub.token.asInt() < self.token_buffer.countTokens())
                {
                    const tok_kind = self.token_buffer.getToken(sub.token).kind;
                    if (tok_kind == .colon or tok_kind == .eq) break;
                    if (symbol_resolver.isIdentifierToken(tok_kind)) {
                        name_tok = sub.token;
                        break;
                    }
                }
            }
        }

        const declared_ty: TypeId = if (decl_node.lhs.tag == .node)
            try self.resolveTypeAst(NodeIndex.fromInt(decl_node.lhs.payload))
        else
            .err_ty;

        var final_ty: TypeId = declared_ty;
        if (decl_node.rhs.tag == .node) {
            const prev_pure_depth = self.pure_comptime_depth;
            const prev_boundary = self.comptime_boundary_scope_depth;
            if (prev_pure_depth == 0) {
                self.comptime_boundary_scope_depth = if (self.current_scope.isNone())
                    0
                else
                    self.sym_table.scope_arena.getScope(self.current_scope).depth;
            }
            self.pure_comptime_depth = prev_pure_depth + 1;
            defer {
                self.pure_comptime_depth = prev_pure_depth;
                self.comptime_boundary_scope_depth = prev_boundary;
            }

            const init_id = NodeIndex.fromInt(decl_node.rhs.payload);
            if (!declared_ty.isError()) {
                final_ty = try self.checkExpr(init_id, declared_ty);
            } else {
                final_ty = self.materializeUntypedType(try self.synthExpr(init_id));
            }
        }

        if (!name_tok.isNone()) {
            const name_lex = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, name_tok);
            if (name_lex.len > 0) {
                const name_sym = try self.interner.intern(name_lex);
                const created_idx = try self.sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = self.interner.get(name_sym),
                    .kind = .const_sym,
                    .namespace = .const_ns,
                    .visibility = .private,
                    .flags = .{ .is_comptime = true },
                    .scope_id = self.current_scope,
                    .ast_node = decl_id,
                    .cst_node = decl_cst,
                    .decl_span = self.token_buffer.getTokenSpan(self.file_id, name_tok),
                    .type_id = final_ty,
                }, self.diagnostic_sink);
                self.recordNodeSymbol(decl_id, created_idx);
            }
        }
        return self.recordNodeType(decl_id, .unit_ty);
    }

    /// Type-checks the body block of a function or method symbol (`fn_sym_idx`).
    pub fn checkFnDeclBody(self: *TypeChecker, fn_sym_idx: SymbolIndex) !void {
        try self.resolveFnSignatureSymbol(fn_sym_idx);
        const fn_sym = self.sym_table.getSymbol(fn_sym_idx).*;
        if (fn_sym.ast_node.isNone()) return;

        const fn_ast = self.ast_arena.getNode(fn_sym.ast_node);
        if (fn_ast.rhs.tag != .node) return;
        const body_block_id = NodeIndex.fromInt(fn_ast.rhs.payload);
        if (body_block_id.isNone() or body_block_id.asInt() >= self.ast_arena.countNodes()) return;

        const sig_view = self.pool.getFnSignatureView(fn_sym.type_id) orelse return;
        const saved_scope = self.current_scope;
        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_defer_depth = self.defer_depth;
        const saved_defer_loop_depth = self.defer_inner_loop_depth;
        const prev_pure_depth = self.pure_comptime_depth;
        const prev_boundary = self.comptime_boundary_scope_depth;
        defer {
            self.current_scope = saved_scope;
            self.current_fn_ret_ty = saved_ret_ty;
            self.defer_depth = saved_defer_depth;
            self.defer_inner_loop_depth = saved_defer_loop_depth;
            self.pure_comptime_depth = prev_pure_depth;
            self.comptime_boundary_scope_depth = prev_boundary;
        }

        if (fn_sym.flags.is_comptime) {
            if (prev_pure_depth == 0) {
                self.comptime_boundary_scope_depth = if (fn_sym.scope_id.isNone())
                    0
                else
                    self.sym_table.scope_arena.getScope(fn_sym.scope_id).depth;
            }
            self.pure_comptime_depth = prev_pure_depth + 1;
        }
        self.defer_depth = 0;
        self.defer_inner_loop_depth = 0;
        self.current_scope = if (!fn_sym.target_scope.isNone()) fn_sym.target_scope else fn_sym.scope_id;
        self.current_fn_ret_ty = sig_view.ret_ty;

        const is_subscript = !fn_ast.main_token.isNone() and
            fn_ast.main_token.asInt() < self.token_buffer.countTokens() and
            std.mem.eql(
                u8,
                symbol_resolver.extractTokenSlice(self.source, self.token_buffer, fn_ast.main_token),
                "subscript",
            );
        const body_expected_ty = if (is_subscript and self.ast_arena.getNode(body_block_id).rhs.tag != .node)
            TypeId.unit_ty
        else
            sig_view.ret_ty;
        _ = try self.checkBlock(body_block_id, body_expected_ty, true);

        if (!fn_sym.target_scope.isNone()) {
            try symbol_resolver.checkUnusedBindingsInScope(
                self.sym_table,
                fn_sym.target_scope,
                self.interner,
                self.diagnostic_sink,
            );
        }
    }

    // ----------------- Block & Statement Checking -----------------

    /// Type-checks a `.block` AST node against `expected_ty` (`is_fn_body = true` for top-level function blocks).
    fn checkBlock(
        self: *TypeChecker,
        block_id: NodeIndex,
        expected_ty: TypeId,
        is_fn_body: bool,
    ) anyerror!TypeId {
        if (block_id.isNone() or block_id.asInt() >= self.ast_arena.countNodes()) return .err_ty;
        if (self.recursion_depth >= MAX_TYPE_DEPTH) return self.recordNodeType(block_id, .err_ty);
        self.recursion_depth += 1;
        defer self.recursion_depth -= 1;

        const block_node = self.ast_arena.getNode(block_id);
        if (block_node.tag == .expr_hole) return self.recordNodeType(block_id, .err_ty);
        if (block_node.tag != .block) {
            return if (expected_ty.isError())
                self.synthExpr(block_id)
            else
                self.checkExpr(block_id, expected_ty);
        }

        const saved_scope = self.current_scope;
        const block_scope = if (is_fn_body)
            self.current_scope
        else
            try self.sym_table.scope_arena.allocScope(
                .block_scope,
                self.current_scope,
                .NONE,
                self.file_id,
                .{},
            );
        self.current_scope = block_scope;
        defer self.current_scope = saved_scope;

        const stmt_slice = self.getNodeExtraSlice(block_id, false);
        var has_diverged = false;

        for (stmt_slice) |raw_stmt_id| {
            const stmt_id = NodeIndex.fromInt(raw_stmt_id);
            const stmt_ty = try self.checkStmt(stmt_id);
            if (stmt_ty == .never_ty) {
                has_diverged = true;
            }
        }

        var result_ty: TypeId = if (has_diverged) .never_ty else .unit_ty;
        if (block_node.rhs.tag == .node) {
            const tail_id = NodeIndex.fromInt(block_node.rhs.payload);
            if (!expected_ty.isError() and expected_ty != .unit_ty) {
                result_ty = try self.checkExpr(tail_id, expected_ty);
            } else if (expected_ty == .unit_ty) {
                const tail_ty = try self.synthExpr(tail_id);
                if (tail_ty == .never_ty) {
                    result_ty = .never_ty;
                } else if (!tail_ty.isError() and tail_ty != .unit_ty) {
                    if (self.isMustUseTypeOrCall(tail_id, tail_ty)) {
                        try self.emitUnhandledMustUseError(self.getAstNodeSpan(tail_id), tail_ty);
                    } else if (is_fn_body) {
                        try self.emitTypeMismatch(
                            self.getAstNodeSpan(tail_id),
                            .unit_ty,
                            self.materializeUntypedType(tail_ty),
                        );
                    } else {
                        result_ty = self.materializeUntypedType(tail_ty);
                    }
                }
            } else {
                const tail_ty = try self.synthExpr(tail_id);
                result_ty = self.materializeUntypedType(tail_ty);
            }
        } else if (!has_diverged and !expected_ty.isError() and expected_ty != .unit_ty) {
            try self.emitTypeMismatch(self.getAstNodeSpan(block_id), expected_ty, .unit_ty);
            result_ty = .err_ty;
        }

        if (!is_fn_body) {
            try symbol_resolver.checkUnusedBindingsInScope(
                self.sym_table,
                block_scope,
                self.interner,
                self.diagnostic_sink,
            );
        }
        return self.recordNodeType(block_id, result_ty);
    }

    /// Type-checks a single statement inside a block, returning `.never_ty` if the statement diverges.
    fn checkStmt(self: *TypeChecker, stmt_id: NodeIndex) anyerror!TypeId {
        if (stmt_id.isNone() or stmt_id.asInt() >= self.ast_arena.countNodes()) return .err_ty;
        if (self.recursion_depth >= MAX_TYPE_DEPTH) return self.recordNodeType(stmt_id, .err_ty);
        self.recursion_depth += 1;
        defer self.recursion_depth -= 1;

        const stmt_node = self.ast_arena.getNode(stmt_id);

        return switch (stmt_node.tag) {
            .stmt_hole, .expr_hole, .item_hole => self.recordNodeType(stmt_id, .err_ty),
            .local_var_decl => self.checkLocalVarDecl(stmt_id),
            .const_decl => self.checkLocalConstDecl(stmt_id),
            .fn_decl,
            .struct_decl,
            .enum_decl,
            .union_decl,
            .type_alias_decl,
            .trait_decl,
            .impl_decl,
            .use_decl,
            => self.recordNodeType(stmt_id, .unit_ty),
            .defer_stmt => self.checkDeferStmt(stmt_id),
            .return_stmt => self.checkReturnStmt(stmt_id),
            .break_stmt => self.checkBreakStmt(stmt_id),
            .continue_stmt => blk: {
                if (self.defer_depth > 0 and self.defer_inner_loop_depth == 0) {
                    try self.emitDiagnosticSimple(
                        .e0412_let_else_not_diverging,
                        self.getAstNodeSpan(stmt_id),
                        "`continue` cannot escape an enclosing `defer` or `errdefer` block",
                        "control-flow jump out of `defer` / `errdefer` is forbidden",
                    );
                }
                break :blk self.recordNodeType(stmt_id, .never_ty);
            },
            .for_stmt => self.checkForStmt(stmt_id),
            .while_stmt => self.checkWhileStmt(stmt_id),
            .assign_stmt => self.checkAssignStmt(stmt_id),
            else => blk: {
                const expr_ty = try self.synthExpr(stmt_id);
                const is_yield_stmt = stmt_node.tag == .unary_expr and
                    !stmt_node.main_token.isNone() and
                    stmt_node.main_token.asInt() < self.token_buffer.countTokens() and
                    std.mem.eql(
                        u8,
                        symbol_resolver.extractTokenSlice(self.source, self.token_buffer, stmt_node.main_token),
                        "yield",
                    );
                // Enforce `@must_use` / `Result[T, E]` handling on discarded expression statements (`E0413`, `DR-07` Section 2.4):
                if (!is_yield_stmt and !expr_ty.isError() and expr_ty != .unit_ty and expr_ty != .never_ty) {
                    if (self.isMustUseTypeOrCall(stmt_id, expr_ty)) {
                        try self.emitUnhandledMustUseError(self.getAstNodeSpan(stmt_id), expr_ty);
                    }
                }
                break :blk self.recordNodeType(stmt_id, expr_ty);
            },
        };
    }

    /// Type-checks `let`/`var` local declarations, including `: Type = Expr`, `let … else { … }` (`E0412`), and `let _ = result` (`E0414`).
    fn checkLocalVarDecl(self: *TypeChecker, decl_id: NodeIndex) anyerror!TypeId {
        const decl_node = self.ast_arena.getNode(decl_id);
        const decl_cst = self.ast_arena.getCstOrigin(decl_id);
        const pat_id = if (decl_node.lhs.tag == .node) NodeIndex.fromInt(decl_node.lhs.payload) else .none;
        const is_var = !decl_node.main_token.isNone() and
            self.token_buffer.getToken(decl_node.main_token).kind == .kw_var;
        const is_mut = is_var or self.hasMutKeywordInCst(decl_cst);

        // Locate optional explicit `: Type`, `= Expr`, and `else { … }` inside `decl_cst`:
        var explicit_ty_ast: NodeIndex = .none;
        var init_expr_ast: NodeIndex = .none;
        var else_block_ast: NodeIndex = .none;

        if (!decl_cst.isNone() and decl_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = decl_cst.asInt();
            const rec = self.cst_arena.getNode(decl_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var colon_cst_pos: ?usize = null;
            var eq_cst_pos: ?usize = null;
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

            var cur = pat_end_pos;
            while (cur < end_idx) {
                const sub_id = CstNodeIndex.fromInt(@intCast(cur));
                const sub = self.cst_arena.getNode(sub_id);
                if (sub.kind == .let_else_branch) {
                    const branch_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                    else_block_ast = self.findFirstAstInCstRange(cur + 1, branch_end);
                    cur = branch_end;
                    continue;
                }
                const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
                if (is_leaf and !sub.flags.is_missing_or_injected and
                    !sub.token.isNone() and sub.token.asInt() < self.token_buffer.countTokens())
                {
                    const kind = self.token_buffer.getToken(sub.token).kind;
                    if (kind == .colon and colon_cst_pos == null and eq_cst_pos == null) {
                        colon_cst_pos = cur;
                    } else if (kind == .eq and eq_cst_pos == null) {
                        eq_cst_pos = cur;
                    }
                }
                cur += 1;
            }

            if (colon_cst_pos) |c_pos| {
                const search_end = eq_cst_pos orelse end_idx;
                explicit_ty_ast = self.findFirstAstInCstRange(c_pos + 1, search_end);
            }
            if (eq_cst_pos != null and decl_node.rhs.tag == .node) {
                init_expr_ast = NodeIndex.fromInt(decl_node.rhs.payload);
            } else if (colon_cst_pos != null and eq_cst_pos == null and decl_node.rhs.tag == .node) {
                explicit_ty_ast = NodeIndex.fromInt(decl_node.rhs.payload);
            }
        } else if (decl_node.rhs.tag == .node) {
            const rhs_id = NodeIndex.fromInt(decl_node.rhs.payload);
            if (isTypeAstTag(self.ast_arena.getNode(rhs_id).tag)) {
                explicit_ty_ast = rhs_id;
            } else {
                init_expr_ast = rhs_id;
            }
        }

        var declared_ty: TypeId = .err_ty;
        if (!explicit_ty_ast.isNone()) {
            declared_ty = try self.resolveTypeAst(explicit_ty_ast);
        }

        var val_ty: TypeId = declared_ty;
        if (!init_expr_ast.isNone()) {
            if (!declared_ty.isError()) {
                val_ty = try self.checkExpr(init_expr_ast, declared_ty);
            } else {
                const raw_init_ty = try self.synthExpr(init_expr_ast);
                val_ty = self.materializeUntypedType(raw_init_ty);
            }
        }

        // [1] Reject bare `let _ = fallible_expr;` without `catch` (`E0414`, `DR-07` Section 2.4):
        if (!pat_id.isNone() and !init_expr_ast.isNone() and !val_ty.isError()) {
            const init_ast = self.ast_arena.getNode(init_expr_ast);
            const is_catch_handled = init_ast.tag == .binary_expr and
                !init_ast.main_token.isNone() and
                self.token_buffer.getToken(init_ast.main_token).kind == .kw_catch;
            if (self.hasWildcardDiscardOfResult(pat_id, val_ty) or
                (self.ast_arena.getNode(pat_id).tag == .wildcard_pat and
                    !is_catch_handled and
                    self.isMustUseTypeOrCall(init_expr_ast, val_ty)))
            {
                try self.emitDiagnosticSimple(
                    .e0414_bare_wildcard_result_discard,
                    self.getAstNodeSpan(decl_id),
                    "discarding `@must_use` or `Result[T, E]` with `let _ = …` is forbidden",
                    "handle the error explicitly with `let _ = expr catch {};` or propagate with `?`",
                );
            }
        }

        // [2] Verify `let Pat = Expr else { … };` diverging block (`E0412`, `DR-07` Section 2.2):
        if (!else_block_ast.isNone()) {
            const else_ty = try self.checkBlock(else_block_ast, .unit_ty, false);
            if (!else_ty.isError() and else_ty != .never_ty) {
                try self.emitDiagnosticSimple(
                    .e0412_let_else_not_diverging,
                    self.getAstNodeSpan(else_block_ast),
                    "`let … else` fallback block must diverge (`never`)",
                    "this `else` block falls through; add `return`, `break`, `continue`, or a diverging call",
                );
            }
        }

        // [3] Bind pattern variables in `self.current_scope` and validate any leading `@Schema` attributes:
        const sym_count_before = self.sym_table.countSymbols();
        if (!pat_id.isNone()) {
            try self.bindPattern(pat_id, val_ty, is_mut);
        }
        const sym_count_after = self.sym_table.countSymbols();
        if (sym_count_after > sym_count_before and !decl_cst.isNone() and
            decl_cst.asInt() < self.cst_arena.countNodes())
        {
            const first_bound_idx = SymbolIndex.fromInt(@intCast(sym_count_before));
            const start_idx: usize = decl_cst.asInt();
            const rec = self.cst_arena.getNode(decl_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var cur = start_idx + 1;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.subtree_size <= 1 and !sub.token.isNone() and
                    sub.token.asInt() < self.token_buffer.countTokens())
                {
                    const leaf_kind = self.token_buffer.getToken(sub.token).kind;
                    if (leaf_kind == .kw_let or leaf_kind == .kw_var) break;
                }
                if (sub.kind == .attribute) {
                    const attr_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                    try self.validateSingleAttributeCst(first_bound_idx, .NONE, cur, attr_end);
                    if (sub.subtree_size > 1) cur += @as(usize, sub.subtree_size) - 1;
                }
            }
        }
        return self.recordNodeType(decl_id, .unit_ty);
    }

    /// Returns `true` if `pat_id` discards a `Result[T, E]` via `_` (directly or nested inside a tuple pattern).
    fn hasWildcardDiscardOfResult(self: *const TypeChecker, pat_id: NodeIndex, val_ty: TypeId) bool {
        if (pat_id.isNone() or pat_id.asInt() >= self.ast_arena.countNodes() or val_ty.isError()) return false;
        const pat_node = self.ast_arena.getNode(pat_id);
        if (pat_node.tag == .wildcard_pat) {
            return self.pool.getTag(val_ty) == .result_ty;
        }
        if (pat_node.tag == .tuple_pat) {
            const sub_pats = self.getNodeExtraSlice(pat_id, false);
            if (sub_pats.len == 1 and !hasShallowCommaInTupleCst(
                self.cst_arena,
                self.token_buffer,
                self.ast_arena.getCstOrigin(pat_id),
            )) {
                return self.hasWildcardDiscardOfResult(NodeIndex.fromInt(sub_pats[0]), val_ty);
            }
            if (self.pool.getTag(val_ty) == .tuple_ty) {
                const elem_types = self.pool.getTupleElements(val_ty);
                for (sub_pats, 0..) |raw_sub, i| {
                    if (i < elem_types.len) {
                        if (self.hasWildcardDiscardOfResult(NodeIndex.fromInt(raw_sub), TypeId.fromInt(elem_types[i]))) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    /// Type-checks `defer` and `errdefer |err|` statements (`DR-07` Section 2.3 & `[CRITICAL-08]`).
    fn checkDeferStmt(self: *TypeChecker, stmt_id: NodeIndex) anyerror!TypeId {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const is_errdefer = !stmt_node.main_token.isNone() and
            self.token_buffer.getToken(stmt_node.main_token).kind == .kw_errdefer;

        const saved_scope = self.current_scope;
        const defer_scope = try self.sym_table.scope_arena.allocScope(
            .catch_or_errdefer_scope,
            self.current_scope,
            .NONE,
            self.file_id,
            .{},
        );
        self.current_scope = defer_scope;
        defer self.current_scope = saved_scope;

        if (is_errdefer) {
            const fn_ret_node = self.pool.getNode(self.pool.unwrapUnderlyingType(self.current_fn_ret_ty));
            const err_payload_ty: TypeId = if (fn_ret_node.tag == .result_ty)
                TypeId.fromInt(fn_ret_node.rhs)
            else if (fn_ret_node.tag == .optional_ty)
                .unit_ty
            else blk: {
                if (!self.current_fn_ret_ty.isError()) {
                    try self.emitDiagnosticSimple(
                        .e0410_try_outside_fallible_fn,
                        self.getAstNodeSpan(stmt_id),
                        "`errdefer` is only permitted inside functions returning `Result[T, E]` or `T?`",
                        "enclosing function does not return a fallible type",
                    );
                }
                break :blk .err_ty;
            };

            if (stmt_node.lhs.tag == .token) {
                const cap_tok = TokenIndex.fromInt(stmt_node.lhs.payload);
                const cap_str = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, cap_tok);
                if (cap_str.len > 0 and !std.mem.eql(u8, cap_str, "_")) {
                    const cap_sym = try self.interner.intern(cap_str);
                    _ = try self.sym_table.defineSymbol(.{
                        .name = cap_sym,
                        .name_text = self.interner.get(cap_sym),
                        .kind = .local_var_sym,
                        .namespace = .value_ns,
                        .visibility = .private,
                        .flags = .{},
                        .scope_id = defer_scope,
                        .decl_span = self.token_buffer.getTokenSpan(self.file_id, cap_tok),
                        .type_id = err_payload_ty,
                    }, self.diagnostic_sink);
                }
            }
        }

        if (stmt_node.rhs.tag == .node) {
            // Forbid `return`, uncaught `?`, and outer-loop `break`/`continue` inside `defer` / `errdefer` (`[CRITICAL-08]`):
            const saved_inner_loop_depth = self.defer_inner_loop_depth;
            self.defer_depth += 1;
            self.defer_inner_loop_depth = 0;
            defer {
                self.defer_depth -= 1;
                self.defer_inner_loop_depth = saved_inner_loop_depth;
            }

            const body_id = NodeIndex.fromInt(stmt_node.rhs.payload);
            if (self.ast_arena.getNode(body_id).tag == .block) {
                _ = try self.checkBlock(body_id, .unit_ty, true);
            } else {
                const expr_ty = try self.synthExpr(body_id);
                if (!expr_ty.isError() and expr_ty != .unit_ty and expr_ty != .never_ty) {
                    if (self.isMustUseTypeOrCall(body_id, expr_ty)) {
                        try self.emitUnhandledMustUseError(self.getAstNodeSpan(body_id), expr_ty);
                    }
                }
            }
        }
        try symbol_resolver.checkUnusedBindingsInScope(self.sym_table, defer_scope, self.interner, self.diagnostic_sink);
        return self.recordNodeType(stmt_id, .unit_ty);
    }

    /// Type-checks `return [expr];` against `self.current_fn_ret_ty`, rejecting `return` inside `defer` / `errdefer`.
    fn checkReturnStmt(self: *TypeChecker, stmt_id: NodeIndex) anyerror!TypeId {
        if (self.defer_depth > 0) {
            try self.emitDiagnosticSimple(
                .e0412_let_else_not_diverging,
                self.getAstNodeSpan(stmt_id),
                "`return` is forbidden inside `defer` and `errdefer` cleanup blocks",
                "cannot return from an enclosing function while inside `defer` / `errdefer`",
            );
        }
        const stmt_node = self.ast_arena.getNode(stmt_id);
        if (stmt_node.lhs.tag == .node) {
            _ = try self.checkExpr(NodeIndex.fromInt(stmt_node.lhs.payload), self.current_fn_ret_ty);
        } else if (!self.current_fn_ret_ty.isError() and self.current_fn_ret_ty != .unit_ty) {
            try self.emitTypeMismatch(self.getAstNodeSpan(stmt_id), self.current_fn_ret_ty, .unit_ty);
        }
        return self.recordNodeType(stmt_id, .never_ty);
    }

    /// Type-checks `break [expr];`, rejecting outer-loop `break` inside `defer` / `errdefer`.
    fn checkBreakStmt(self: *TypeChecker, stmt_id: NodeIndex) anyerror!TypeId {
        if (self.defer_depth > 0 and self.defer_inner_loop_depth == 0) {
            try self.emitDiagnosticSimple(
                .e0412_let_else_not_diverging,
                self.getAstNodeSpan(stmt_id),
                "`break` cannot escape an enclosing `defer` or `errdefer` block",
                "control-flow jump out of `defer` / `errdefer` is forbidden",
            );
        }
        const stmt_node = self.ast_arena.getNode(stmt_id);
        if (stmt_node.lhs.tag == .node) {
            const val_id = NodeIndex.fromInt(stmt_node.lhs.payload);
            if (!self.current_loop_break_ty.isError() and self.current_loop_break_ty != .unit_ty) {
                _ = try self.checkExpr(val_id, self.current_loop_break_ty);
            } else {
                const brk_ty = try self.synthExpr(val_id);
                self.current_loop_break_ty = self.materializeUntypedType(brk_ty);
            }
        } else if (self.current_loop_break_ty == .never_ty) {
            self.current_loop_break_ty = .unit_ty;
        }
        return self.recordNodeType(stmt_id, .never_ty);
    }

    /// Type-checks `for pat in iter_expr { … }` and `comptime for pat in iter_expr { … }` (`DR-05` §3.2).
    fn checkForStmt(self: *TypeChecker, stmt_id: NodeIndex) anyerror!TypeId {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const is_comptime_for = !stmt_node.main_token.isNone() and
            self.token_buffer.getToken(stmt_node.main_token).kind == .kw_comptime;
        const pair = self.getNodeExtraSlice(stmt_id, false);
        const pat_id = if (pair.len >= 1) NodeIndex.fromInt(pair[0]) else .none;
        const iter_id = if (pair.len >= 2) NodeIndex.fromInt(pair[1]) else .none;

        const saved_scope = self.current_scope;
        const loop_scope = try self.sym_table.scope_arena.allocScope(
            .loop_scope,
            self.current_scope,
            .NONE,
            self.file_id,
            .{},
        );
        self.current_scope = loop_scope;
        defer self.current_scope = saved_scope;

        if (self.defer_depth > 0) self.defer_inner_loop_depth += 1;
        defer if (self.defer_depth > 0) {
            self.defer_inner_loop_depth -= 1;
        };

        var elem_ty: TypeId = .err_ty;
        if (!iter_id.isNone()) {
            const iter_ty = if (is_comptime_for) eval_ct_iter: {
                const prev_pure_depth = self.pure_comptime_depth;
                const prev_boundary = self.comptime_boundary_scope_depth;
                if (prev_pure_depth == 0) {
                    self.comptime_boundary_scope_depth = if (saved_scope.isNone())
                        0
                    else
                        self.sym_table.scope_arena.getScope(saved_scope).depth;
                }
                self.pure_comptime_depth = prev_pure_depth + 1;
                defer {
                    self.pure_comptime_depth = prev_pure_depth;
                    self.comptime_boundary_scope_depth = prev_boundary;
                }
                break :eval_ct_iter try self.synthExpr(iter_id);
            } else try self.synthExpr(iter_id);

            const unwrapped_iter = self.unwrapRefType(iter_ty);
            const iter_node = self.pool.getNode(unwrapped_iter);
            elem_ty = switch (iter_node.tag) {
                .slice_ty, .soa_slice_ty, .array_ty, .soa_array_ty => TypeId.fromInt(iter_node.lhs),
                .tuple_ty => blk: {
                    const elems = self.pool.getTupleElements(unwrapped_iter);
                    break :blk if (elems.len > 0) TypeId.fromInt(elems[0]) else .unit_ty;
                },
                else => self.materializeUntypedType(unwrapped_iter),
            };
        }
        if (!pat_id.isNone()) {
            const prev_binding_ct = self.is_binding_comptime;
            if (is_comptime_for) self.is_binding_comptime = true;
            defer self.is_binding_comptime = prev_binding_ct;
            try self.bindPattern(pat_id, elem_ty, false);
        }
        if (stmt_node.rhs.tag == .node) {
            _ = try self.checkBlock(NodeIndex.fromInt(stmt_node.rhs.payload), .unit_ty, true);
        }
        try symbol_resolver.checkUnusedBindingsInScope(self.sym_table, loop_scope, self.interner, self.diagnostic_sink);
        return self.recordNodeType(stmt_id, .unit_ty);
    }

    /// Type-checks `while cond { … }` and `while let pat = expr { … }`.
    fn checkWhileStmt(self: *TypeChecker, stmt_id: NodeIndex) anyerror!TypeId {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const saved_scope = self.current_scope;
        const loop_scope = try self.sym_table.scope_arena.allocScope(
            .loop_scope,
            self.current_scope,
            .NONE,
            self.file_id,
            .{},
        );
        self.current_scope = loop_scope;
        defer self.current_scope = saved_scope;

        if (self.defer_depth > 0) self.defer_inner_loop_depth += 1;
        defer if (self.defer_depth > 0) {
            self.defer_inner_loop_depth -= 1;
        };

        if (stmt_node.lhs.tag == .node) {
            try self.checkConditionOrLetHeader(
                NodeIndex.fromInt(stmt_node.lhs.payload),
                self.ast_arena.getCstOrigin(stmt_id),
            );
        }
        if (stmt_node.rhs.tag == .node) {
            _ = try self.checkBlock(NodeIndex.fromInt(stmt_node.rhs.payload), .unit_ty, true);
        }
        try symbol_resolver.checkUnusedBindingsInScope(self.sym_table, loop_scope, self.interner, self.diagnostic_sink);
        return self.recordNodeType(stmt_id, .unit_ty);
    }

    /// Type-checks `lhs = rhs;` or compound assignment statements (`+=`, `-=`, etc.).
    fn checkAssignStmt(self: *TypeChecker, stmt_id: NodeIndex) anyerror!TypeId {
        const stmt_node = self.ast_arena.getNode(stmt_id);
        const lhs_id = if (stmt_node.lhs.tag == .node) NodeIndex.fromInt(stmt_node.lhs.payload) else .none;
        const rhs_id = if (stmt_node.rhs.tag == .node) NodeIndex.fromInt(stmt_node.rhs.payload) else .none;

        const lhs_ty = try self.synthExpr(lhs_id);
        if (!rhs_id.isNone()) {
            if (!lhs_ty.isError()) {
                _ = try self.checkExpr(rhs_id, lhs_ty);
            } else {
                _ = try self.synthExpr(rhs_id);
            }
        }
        return self.recordNodeType(stmt_id, .unit_ty);
    }

    /// Checks a boolean condition, `if let` / `while let` header, or `if opt_val |cap| {` payload capture.
    fn checkConditionOrLetHeader(
        self: *TypeChecker,
        cond_node_id: NodeIndex,
        enclosing_cst: CstNodeIndex,
    ) !void {
        if (cond_node_id.isNone() or cond_node_id.asInt() >= self.ast_arena.countNodes()) return;
        const cond_node = self.ast_arena.getNode(cond_node_id);

        // `if let pat = scrutinee` or `while let pat = scrutinee` (`cond_node.lhs.tag == .extra`):
        if (cond_node.tag == .binary_expr and cond_node.lhs.tag == .extra) {
            const pair = self.getNodeExtraSlice(cond_node_id, false);
            const pat_id = if (pair.len >= 1) NodeIndex.fromInt(pair[0]) else .none;
            const scrutinee_id = if (pair.len >= 2) NodeIndex.fromInt(pair[1]) else .none;
            const scrutinee_ty = self.materializeUntypedType(try self.synthExpr(scrutinee_id));
            if (!pat_id.isNone()) {
                try self.bindPattern(pat_id, scrutinee_ty, false);
            }
            return;
        }

        // Check for `if opt_val |capture| {` payload bar inside `enclosing_cst`:
        var capture_tok: TokenIndex = .none;
        var is_ref_capture = false;
        if (!enclosing_cst.isNone() and enclosing_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = enclosing_cst.asInt();
            const rec = self.cst_arena.getNode(enclosing_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var cur = start_idx + 1;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.kind == .block) break;
                if (sub.kind == .if_cond or sub.kind == .while_header) {
                    const hdr_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                    var h_cur = cur + 1;
                    var has_seen_open_pipe = false;
                    while (h_cur < hdr_end) : (h_cur += 1) {
                        const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(h_cur)));
                        if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                            leaf.token.asInt() < self.token_buffer.countTokens())
                        {
                            const kind = self.token_buffer.getToken(leaf.token).kind;
                            if (kind == .pipe) {
                                if (has_seen_open_pipe) break;
                                has_seen_open_pipe = true;
                            } else if (has_seen_open_pipe and kind == .amp) {
                                is_ref_capture = true;
                            } else if (has_seen_open_pipe and symbol_resolver.isIdentifierToken(kind)) {
                                capture_tok = leaf.token;
                            }
                        }
                    }
                    break;
                }
            }
        }

        if (!capture_tok.isNone()) {
            const cond_ty = try self.synthExpr(cond_node_id);
            const cond_ty_node = self.pool.getNode(cond_ty);
            var payload_ty: TypeId = switch (cond_ty_node.tag) {
                .optional_ty, .result_ty => TypeId.fromInt(cond_ty_node.lhs),
                else => .err_ty,
            };
            if (is_ref_capture and !payload_ty.isError()) {
                payload_ty = try self.pool.internRef(payload_ty, false);
            }
            const cap_str = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, capture_tok);
            if (cap_str.len > 0 and !std.mem.eql(u8, cap_str, "_")) {
                const cap_sym = try self.interner.intern(cap_str);
                _ = try self.sym_table.defineSymbol(.{
                    .name = cap_sym,
                    .name_text = self.interner.get(cap_sym),
                    .kind = .local_var_sym,
                    .namespace = .value_ns,
                    .visibility = .private,
                    .flags = .{},
                    .scope_id = self.current_scope,
                    .decl_span = self.token_buffer.getTokenSpan(self.file_id, capture_tok),
                    .type_id = payload_ty,
                }, self.diagnostic_sink);
            }
            return;
        }

        const prev_pos = self.is_direct_positive_cond;
        self.is_direct_positive_cond = true;
        defer self.is_direct_positive_cond = prev_pos;
        _ = try self.checkExpr(cond_node_id, .bool_ty);
    }

    // ---------------------- Pattern Binding -----------------------

    /// Validates a `.lit_pat` literal or range pattern against `scrutinee_ty` (`E0401`).
    fn validateLiteralPatternType(self: *TypeChecker, pat_id: NodeIndex, scrutinee_ty: TypeId) !void {
        const base_scr = self.pool.unwrapRefinementBase(self.unwrapRefType(scrutinee_ty));
        if (base_scr.isError()) return;
        const pat_node = self.ast_arena.getNode(pat_id);
        if (pat_node.main_token.isNone() or pat_node.main_token.asInt() >= self.token_buffer.countTokens()) return;

        const tok_kind = self.token_buffer.getToken(pat_node.main_token).kind;
        switch (tok_kind) {
            .kw_true, .kw_false => {
                if (base_scr != .bool_ty) {
                    try self.emitTypeMismatch(self.getAstNodeSpan(pat_id), base_scr, .bool_ty);
                }
            },
            .string_lit => {
                if (base_scr != .str_ty) {
                    try self.emitTypeMismatch(self.getAstNodeSpan(pat_id), base_scr, .str_ty);
                }
            },
            .char_lit => {
                if (base_scr != .char_ty) {
                    try self.emitTypeMismatch(self.getAstNodeSpan(pat_id), base_scr, .char_ty);
                }
            },
            .float_lit => {
                if (!base_scr.isFloatPrimitive() and base_scr != .untyped_float_ty) {
                    try self.emitTypeMismatch(self.getAstNodeSpan(pat_id), base_scr, .f64_ty);
                }
            },
            .int_lit, .minus => {
                if (!base_scr.isIntegerPrimitive() and base_scr != .untyped_int_ty and
                    !self.isIntegerBoundedVar(base_scr))
                {
                    try self.emitTypeMismatch(self.getAstNodeSpan(pat_id), base_scr, .i32_ty);
                }
            },
            else => {},
        }
    }

    /// Binds variables introduced by `pat_id` against `scrutinee_ty` in `self.current_scope`.
    fn bindPattern(
        self: *TypeChecker,
        pat_id: NodeIndex,
        scrutinee_ty: TypeId,
        is_decl_mut: bool,
    ) anyerror!void {
        if (pat_id.isNone() or pat_id.asInt() >= self.ast_arena.countNodes()) return;
        if (self.recursion_depth >= MAX_TYPE_DEPTH) return;
        self.recursion_depth += 1;
        defer self.recursion_depth -= 1;

        const pat_node = self.ast_arena.getNode(pat_id);
        _ = self.recordNodeType(pat_id, scrutinee_ty);

        switch (pat_node.tag) {
            .wildcard_pat, .pattern_hole => return,
            .lit_pat => {
                try self.validateLiteralPatternType(pat_id, scrutinee_ty);
                return;
            },
            .or_pat => {
                if (pat_node.lhs.tag == .node) {
                    try self.bindPattern(NodeIndex.fromInt(pat_node.lhs.payload), scrutinee_ty, is_decl_mut);
                }
                if (pat_node.rhs.tag == .node) {
                    try self.bindPattern(NodeIndex.fromInt(pat_node.rhs.payload), scrutinee_ty, is_decl_mut);
                }
            },
            .bind_pat => {
                const name_str = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.token_buffer,
                    pat_node.main_token,
                );
                if (name_str.len == 0 or std.mem.eql(u8, name_str, "_")) return;

                const pat_cst = self.ast_arena.getCstOrigin(pat_id);
                const is_mut = is_decl_mut or self.hasMutKeywordInCst(pat_cst);
                var bound_ty = self.materializeUntypedType(scrutinee_ty);
                if (!pat_cst.isNone() and pat_cst.asInt() < self.cst_arena.countNodes()) {
                    const start_idx: usize = pat_cst.asInt();
                    const rec = self.cst_arena.getNode(pat_cst);
                    const end_idx: usize = @min(
                        start_idx + @max(@as(usize, rec.subtree_size), 1),
                        self.cst_arena.countNodes(),
                    );
                    var cur = start_idx;
                    while (cur < end_idx) : (cur += 1) {
                        const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                        if (sub.subtree_size <= 1 and !sub.token.isNone() and
                            sub.token.asInt() < self.token_buffer.countTokens())
                        {
                            const tok_kind = self.token_buffer.getToken(sub.token).kind;
                            if (tok_kind == .kw_ref or tok_kind == .amp) {
                                bound_ty = try self.pool.internRef(bound_ty, is_mut);
                                break;
                            }
                        }
                    }
                }

                const name_sym = try self.interner.intern(name_str);
                const bound_idx = try self.sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = self.interner.get(name_sym),
                    .kind = .local_var_sym,
                    .namespace = .value_ns,
                    .visibility = .private,
                    .flags = .{
                        .is_mut = is_mut,
                        .is_comptime = self.is_binding_comptime or self.pure_comptime_depth > 0,
                    },
                    .scope_id = self.current_scope,
                    .decl_span = self.token_buffer.getTokenSpan(self.file_id, pat_node.main_token),
                    .ast_node = pat_id,
                    .cst_node = pat_cst,
                    .type_id = bound_ty,
                }, self.diagnostic_sink);
                self.recordNodeSymbol(pat_id, bound_idx);
            },
            .tuple_pat => {
                const sub_pats = self.getNodeExtraSlice(pat_id, false);
                if (sub_pats.len == 1 and !hasShallowCommaInTupleCst(
                    self.cst_arena,
                    self.token_buffer,
                    self.ast_arena.getCstOrigin(pat_id),
                )) {
                    try self.bindPattern(NodeIndex.fromInt(sub_pats[0]), scrutinee_ty, is_decl_mut);
                    return;
                }
                const unwrapped = self.unwrapRefType(scrutinee_ty);
                const elem_types = self.pool.getTupleElements(unwrapped);
                for (sub_pats, 0..) |raw_sub, i| {
                    const sub_ty = if (i < elem_types.len)
                        TypeId.fromInt(elem_types[i])
                    else
                        .err_ty;
                    try self.bindPattern(NodeIndex.fromInt(raw_sub), sub_ty, is_decl_mut);
                }
            },
            .variant_pat => {
                const sub_pats = self.getNodeExtraSlice(pat_id, false);
                const payload_ty = try self.resolveVariantPatPayloadType(pat_id, scrutinee_ty);
                if (sub_pats.len == 0) return;
                if (sub_pats.len == 1) {
                    try self.bindPattern(NodeIndex.fromInt(sub_pats[0]), payload_ty, is_decl_mut);
                } else {
                    const elem_types = self.pool.getTupleElements(payload_ty);
                    for (sub_pats, 0..) |raw_sub, i| {
                        const sub_ty = if (i < elem_types.len)
                            TypeId.fromInt(elem_types[i])
                        else
                            payload_ty;
                        try self.bindPattern(NodeIndex.fromInt(raw_sub), sub_ty, is_decl_mut);
                    }
                }
            },
            .struct_pat => {
                const sub_pats = self.getNodeExtraSlice(pat_id, false);
                const unwrapped = self.unwrapRefType(scrutinee_ty);
                const struct_node = self.pool.getNode(unwrapped);
                const struct_scope: ScopeId = if (struct_node.tag == .struct_ty) blk: {
                    const struct_sym_idx = SymbolIndex.fromInt(struct_node.rhs);
                    self.recordNodeSymbol(pat_id, struct_sym_idx);
                    break :blk self.sym_table.getSymbol(struct_sym_idx).target_scope;
                } else .none;

                for (sub_pats) |raw_sub| {
                    const sub_pat_id = NodeIndex.fromInt(raw_sub);
                    const sub_pat = self.ast_arena.getNode(sub_pat_id);
                    var field_ty: TypeId = .err_ty;
                    if (!struct_scope.isNone() and !sub_pat.main_token.isNone()) {
                        const field_name = symbol_resolver.extractTokenSlice(
                            self.source,
                            self.token_buffer,
                            sub_pat.main_token,
                        );
                        if (self.interner.lookup(field_name)) |field_sym_id| {
                            const f_sym_idx = self.sym_table.lookupInScopeDirect(
                                struct_scope,
                                field_sym_id,
                                NamespaceMask.VALUE_ONLY,
                            );
                            if (!f_sym_idx.isNone()) {
                                field_ty = self.sym_table.getSymbol(f_sym_idx).type_id;
                            }
                        }
                    }
                    try self.bindPattern(sub_pat_id, field_ty, is_decl_mut);
                }
            },
            else => {},
        }
    }

    /// Resolves the payload `TypeId` of a `.variant_pat` (`Some(x)`, `Ok(x)`, `Err(e)`, or `Enum::Variant(x)`).
    fn resolveVariantPatPayloadType(
        self: *TypeChecker,
        pat_id: NodeIndex,
        scrutinee_ty: TypeId,
    ) !TypeId {
        const unwrapped = self.unwrapRefType(scrutinee_ty);
        if (unwrapped.isError()) return .err_ty;
        const var_name = self.extractVariantPatName(pat_id);
        const scr_node = self.pool.getNode(unwrapped);

        switch (scr_node.tag) {
            .optional_ty => {
                if (std.mem.eql(u8, var_name, "Some")) return TypeId.fromInt(scr_node.lhs);
                if (std.mem.eql(u8, var_name, "None")) return .unit_ty;
            },
            .result_ty => {
                if (std.mem.eql(u8, var_name, "Ok")) return TypeId.fromInt(scr_node.lhs);
                if (std.mem.eql(u8, var_name, "Err")) return TypeId.fromInt(scr_node.rhs);
            },
            .enum_ty => {
                const enum_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(scr_node.rhs));
                if (!enum_sym.target_scope.isNone()) {
                    if (self.interner.lookup(var_name)) |var_sym_id| {
                        const v_idx = self.sym_table.lookupInScopeDirect(
                            enum_sym.target_scope,
                            var_sym_id,
                            NamespaceMask.VALUE_ONLY,
                        );
                        if (!v_idx.isNone()) {
                            self.sym_table.markSymbolUsed(v_idx);
                            self.recordNodeSymbol(pat_id, v_idx);
                            return self.sym_table.getSymbol(v_idx).type_id;
                        }
                    }
                }
            },
            else => {},
        }

        var expected_buf: [96]u8 = undefined;
        const expected_str = self.pool.formatType(unwrapped, self.sym_table, &expected_buf);
        var msg_buf: [192]u8 = undefined;
        const msg = std.fmt.bufPrint(
            &msg_buf,
            "variant pattern `.{s}` does not exist on scrutinee type `{s}`",
            .{ var_name, expected_str },
        ) catch "unresolved variant pattern on scrutinee type";
        try self.emitDiagnosticSimple(
            .e0407_invalid_contextual_variant,
            self.getAstNodeSpan(pat_id),
            msg,
            "variant not found on scrutinee type",
        );
        return .err_ty;
    }

    /// Extracts the variant identifier text from a `.variant_pat` AST node.
    fn extractVariantPatName(self: *const TypeChecker, pat_id: NodeIndex) []const u8 {
        const pat_node = self.ast_arena.getNode(pat_id);
        const pat_cst = self.ast_arena.getCstOrigin(pat_id);
        var last_ident_tok: TokenIndex = pat_node.main_token;

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
                const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
                if (is_leaf and !sub.flags.is_missing_or_injected and
                    !sub.token.isNone() and sub.token.asInt() < self.token_buffer.countTokens())
                {
                    const kind = self.token_buffer.getToken(sub.token).kind;
                    if (kind == .lparen or kind == .lbrace) break;
                    if (symbol_resolver.isIdentifierToken(kind)) {
                        last_ident_tok = sub.token;
                    }
                }
            }
        }
        return symbol_resolver.extractTokenSlice(self.source, self.token_buffer, last_ident_tok);
    }

    // ------- Bidirectional Expression Synthesis & Checking --------

    /// Checking mode ($\Gamma \vdash e \Leftarrow T$): verifies `expr_id` against `expected_ty`.
    pub fn checkExpr(self: *TypeChecker, expr_id: NodeIndex, expected_ty: TypeId) anyerror!TypeId {
        if (expr_id.isNone() or expr_id.asInt() >= self.ast_arena.countNodes()) return .err_ty;
        if (self.recursion_depth >= MAX_TYPE_DEPTH) return self.recordNodeType(expr_id, .err_ty);
        self.recursion_depth += 1;
        defer self.recursion_depth -= 1;

        if (expected_ty.isError()) {
            return self.synthExpr(expr_id);
        }

        const expr_node = self.ast_arena.getNode(expr_id);
        switch (expr_node.tag) {
            .expr_hole, .type_hole, .item_hole, .stmt_hole, .pattern_hole => {
                return self.recordNodeType(expr_id, .err_ty);
            },
            .contextual_variant => {
                return self.checkContextualVariant(expr_id, expected_ty);
            },
            .int_lit => {
                return self.checkIntLiteralAgainstExpected(expr_id, false, expected_ty);
            },
            .unary_expr => {
                if (!expr_node.main_token.isNone() and expr_node.lhs.tag == .node) {
                    const op_kind = self.token_buffer.getToken(expr_node.main_token).kind;
                    if (op_kind == .kw_comptime) {
                        return self.synthOrCheckComptimePrefixExpr(expr_id, expected_ty);
                    }
                    if (op_kind == .minus) {
                        const inner_id = NodeIndex.fromInt(expr_node.lhs.payload);
                        if (self.ast_arena.getNode(inner_id).tag == .int_lit) {
                            const res_ty = try self.checkIntLiteralAgainstExpected(inner_id, true, expected_ty);
                            return self.recordNodeType(expr_id, res_ty);
                        }
                    }
                    if (op_kind == .amp or op_kind == .kw_ref) {
                        const inner_id = NodeIndex.fromInt(expr_node.lhs.payload);
                        if (self.ast_arena.getNode(inner_id).tag == .array_lit) {
                            const is_mut = self.hasMutKeywordInCst(self.ast_arena.getCstOrigin(expr_id));
                            const exp_node = self.pool.getNode(expected_ty);
                            const slice_elem_opt: ?TypeId = if (exp_node.tag == .slice_ty)
                                TypeId.fromInt(exp_node.lhs)
                            else if (exp_node.tag == .ref_ty or (exp_node.tag == .mut_ref_ty and is_mut)) blk_ref: {
                                const inner_exp = self.pool.getNode(TypeId.fromInt(exp_node.lhs));
                                if (inner_exp.tag == .slice_ty) break :blk_ref TypeId.fromInt(inner_exp.lhs);
                                break :blk_ref null;
                            } else null;
                            if (slice_elem_opt) |slice_elem_ty| {
                                const arr_ty = try self.checkArrayLitWithElemType(inner_id, slice_elem_ty, null);
                                _ = try self.pool.internRef(arr_ty, is_mut);
                                return self.recordNodeType(expr_id, expected_ty);
                            }
                        }
                    }
                }
            },
            .block => {
                return self.checkBlock(expr_id, expected_ty, false);
            },
            .if_expr => {
                return self.synthOrCheckIfExpr(expr_id, expected_ty);
            },
            .match_expr => {
                return self.synthOrCheckMatchExpr(expr_id, expected_ty, false);
            },
            .tuple_lit => {
                if (self.pool.getTag(expected_ty) == .tuple_ty) {
                    const elem_nodes = self.getNodeExtraSlice(expr_id, false);
                    const expected_elems = self.pool.getTupleElements(expected_ty);
                    if (elem_nodes.len == expected_elems.len) {
                        for (elem_nodes, 0..) |raw_elem, i| {
                            _ = try self.checkExpr(
                                NodeIndex.fromInt(raw_elem),
                                TypeId.fromInt(expected_elems[i]),
                            );
                        }
                        return self.recordNodeType(expr_id, expected_ty);
                    }
                }
            },
            .array_lit => {
                const exp_node = self.pool.getNode(expected_ty);
                if (exp_node.tag == .array_ty) {
                    const elem_expected = TypeId.fromInt(exp_node.lhs);
                    const actual_arr_ty = try self.checkArrayLitWithElemType(
                        expr_id,
                        elem_expected,
                        exp_node.rhs,
                    );
                    if (actual_arr_ty.isError()) return self.recordNodeType(expr_id, .err_ty);
                    if (try self.checkTypeCompatibility(expr_id, actual_arr_ty, expected_ty)) {
                        return self.recordNodeType(expr_id, expected_ty);
                    }
                    return self.recordNodeType(expr_id, .err_ty);
                }
            },
            .binary_expr => {
                if (!expr_node.main_token.isNone() and
                    self.token_buffer.getToken(expr_node.main_token).kind == .kw_catch)
                {
                    return self.synthCatchExpr(expr_id, expected_ty);
                }
            },
            else => {},
        }

        // Subsumption rule ($\Rightarrow$ followed by compatibility/refinement check):
        const synth_ty = try self.synthExpr(expr_id);
        if (synth_ty.isError() or synth_ty == .never_ty) {
            return self.recordNodeType(expr_id, if (synth_ty == .never_ty) expected_ty else .err_ty);
        }

        if (try self.checkTypeCompatibility(expr_id, synth_ty, expected_ty)) {
            return self.recordNodeType(expr_id, expected_ty);
        }
        return self.recordNodeType(expr_id, .err_ty);
    }

    /// Synthesis mode ($\Gamma \vdash e \Rightarrow T$): infers the principal `TypeId` of `expr_id`.
    pub fn synthExpr(self: *TypeChecker, expr_id: NodeIndex) anyerror!TypeId {
        if (expr_id.isNone() or expr_id.asInt() >= self.ast_arena.countNodes()) return .err_ty;
        if (self.recursion_depth >= MAX_TYPE_DEPTH) return self.recordNodeType(expr_id, .err_ty);
        self.recursion_depth += 1;
        defer self.recursion_depth -= 1;

        const ast_node = self.ast_arena.getNode(expr_id);
        const prev_pos_cond = self.is_direct_positive_cond;
        if (ast_node.tag != .binary_expr) {
            self.is_direct_positive_cond = false;
        }
        defer self.is_direct_positive_cond = prev_pos_cond;

        const inferred: TypeId = switch (ast_node.tag) {
            .expr_hole, .type_hole, .item_hole, .stmt_hole, .pattern_hole, .incomplete_member_access => .err_ty,
            .bool_lit => .bool_ty,
            .char_lit => .char_ty,
            .string_lit => try self.synthStringLit(expr_id),
            .int_lit => try self.synthIntLiteral(expr_id, false),
            .float_lit => self.synthFloatLiteral(expr_id),
            .self_val => blk: {
                const self_sym = try self.interner.intern("self");
                switch (self.sym_table.lookupLexical(self.current_scope, self_sym, NamespaceMask.VALUE_ONLY)) {
                    .found => |sym_idx| {
                        self.sym_table.markSymbolUsed(sym_idx);
                        self.recordNodeSymbol(expr_id, sym_idx);
                        try self.checkComptimeSymbolAccess(expr_id, sym_idx);
                        break :blk self.sym_table.getSymbol(sym_idx).type_id;
                    },
                    else => break :blk .err_ty,
                }
            },
            .ident_expr, .path_expr => try self.synthIdentOrPathExpr(expr_id),
            .contextual_variant => blk: {
                const var_tok = if (ast_node.lhs.tag == .token)
                    TokenIndex.fromInt(ast_node.lhs.payload)
                else
                    ast_node.main_token;
                const var_name = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, var_tok);
                var msg_buf: [160]u8 = undefined;
                const msg = std.fmt.bufPrint(
                    &msg_buf,
                    "cannot infer contextual variant `.{s}` without an expected `enum`, `T?`, or `Result[T, E]` type",
                    .{var_name},
                ) catch "cannot infer contextual variant without an expected type";
                try self.emitDiagnosticSimple(
                    .e0407_invalid_contextual_variant,
                    self.getAstNodeSpan(expr_id),
                    msg,
                    "add an explicit type annotation or qualify the enum name",
                );
                break :blk .err_ty;
            },
            .tuple_lit => blk: {
                const elem_nodes = self.getNodeExtraSlice(expr_id, false);
                if (elem_nodes.len == 0) break :blk .unit_ty;
                const elem_types = try self.allocator.alloc(TypeId, elem_nodes.len);
                defer self.allocator.free(elem_types);
                for (elem_nodes, 0..) |raw_elem, i| {
                    const e_ty = try self.synthExpr(NodeIndex.fromInt(raw_elem));
                    elem_types[i] = self.materializeUntypedType(e_ty);
                }
                break :blk try self.pool.internTuple(elem_types);
            },
            .array_lit => try self.checkArrayLitWithElemType(expr_id, .err_ty, null),
            .struct_lit => try self.synthStructLit(expr_id),
            .unary_expr => try self.synthUnaryExpr(expr_id),
            .binary_expr => try self.synthBinaryExpr(expr_id),
            .pipe_expr => try self.synthPipeExpr(expr_id),
            .try_expr => try self.synthTryExpr(expr_id),
            .cast_expr => blk: {
                const dst_ty = if (ast_node.rhs.tag == .node)
                    try self.resolveTypeAst(NodeIndex.fromInt(ast_node.rhs.payload))
                else
                    .err_ty;
                const src_ty = if (ast_node.lhs.tag == .node) blk_src: {
                    const lhs_id = NodeIndex.fromInt(ast_node.lhs.payload);
                    if (!dst_ty.isError() and self.ast_arena.getNode(lhs_id).tag == .contextual_variant) {
                        break :blk_src try self.checkExpr(lhs_id, self.pool.unwrapUnderlyingType(dst_ty));
                    }
                    break :blk_src try self.synthExpr(lhs_id);
                } else .err_ty;
                if (self.pure_comptime_depth > 0 and !src_ty.isError() and !dst_ty.isError()) {
                    const src_node = self.pool.getNode(src_ty);
                    const dst_node = self.pool.getNode(dst_ty);
                    const is_src_ptr = src_node.tag == .raw_ptr_ty or src_node.tag == .ref_ty or
                        src_node.tag == .mut_ref_ty;
                    const is_dst_ptr = dst_node.tag == .raw_ptr_ty or dst_node.tag == .ref_ty or
                        dst_node.tag == .mut_ref_ty;
                    const is_src_int = src_ty.isIntegerPrimitive() or src_ty == .untyped_int_ty;
                    const is_dst_int = dst_ty.isIntegerPrimitive() or dst_ty == .untyped_int_ty;
                    if ((is_src_ptr and is_dst_int) or (is_src_int and is_dst_ptr) or
                        (is_src_ptr and is_dst_ptr and src_node.lhs != dst_node.lhs))
                    {
                        try self.emitDiagnosticSimple(
                            .e0503_forbidden_comptime_operation,
                            self.getAstNodeSpan(expr_id),
                            "pointer-to-integer or type-punning pointer cast is forbidden in `comptime` evaluation",
                            "unsafe pointer reinterpretation is disallowed at compile time",
                        );
                    }
                }
                break :blk dst_ty;
            },
            .field_access => try self.synthFieldAccess(expr_id),
            .index_expr => try self.synthIndexExpr(expr_id),
            .call_expr, .generic_call, .incomplete_call => try self.synthCallExpr(expr_id),
            .method_call => try self.synthMethodCallExpr(expr_id),
            .block => try self.checkBlock(expr_id, .err_ty, false),
            .if_expr => try self.synthOrCheckIfExpr(expr_id, .err_ty),
            .match_expr => try self.synthOrCheckMatchExpr(expr_id, .err_ty, false),
            .loop_expr => blk: {
                const saved_brk = self.current_loop_break_ty;
                self.current_loop_break_ty = .never_ty;
                defer self.current_loop_break_ty = saved_brk;

                if (self.defer_depth > 0) self.defer_inner_loop_depth += 1;
                defer if (self.defer_depth > 0) {
                    self.defer_inner_loop_depth -= 1;
                };

                if (ast_node.lhs.tag == .node) {
                    _ = try self.checkBlock(NodeIndex.fromInt(ast_node.lhs.payload), .unit_ty, false);
                }
                break :blk self.current_loop_break_ty;
            },
            .closure_expr => try self.synthClosureExpr(expr_id),
            .await_expr => blk: {
                if (ast_node.lhs.tag == .node) {
                    break :blk try self.synthExpr(NodeIndex.fromInt(ast_node.lhs.payload));
                }
                break :blk .err_ty;
            },
            else => .err_ty,
        };
        return self.recordNodeType(expr_id, inferred);
    }

    /// Synthesizes or checks `comptime { … }`, `comptime if …`, `comptime match …`, or `comptime expr` (`DR-05` §3.2).
    fn synthOrCheckComptimePrefixExpr(
        self: *TypeChecker,
        expr_id: NodeIndex,
        expected_ty: TypeId,
    ) anyerror!TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.lhs.tag != .node) return self.recordNodeType(expr_id, .err_ty);
        const inner_id = NodeIndex.fromInt(ast_node.lhs.payload);
        if (inner_id.isNone() or inner_id.asInt() >= self.ast_arena.countNodes()) {
            return self.recordNodeType(expr_id, .err_ty);
        }

        const inner_tag = self.ast_arena.getNode(inner_id).tag;
        if (inner_tag == .if_expr) {
            const branch_ty = try self.synthOrCheckComptimeIfNode(inner_id, expected_ty);
            return self.recordNodeType(expr_id, branch_ty);
        }
        if (inner_tag == .match_expr) {
            self.comptime_branch_guard_depth += 1;
            defer self.comptime_branch_guard_depth -= 1;
            const match_ty = try self.synthOrCheckMatchExpr(inner_id, expected_ty, true);
            return self.recordNodeType(expr_id, match_ty);
        }

        const prev_pure_depth = self.pure_comptime_depth;
        const prev_boundary = self.comptime_boundary_scope_depth;
        if (prev_pure_depth == 0) {
            self.comptime_boundary_scope_depth = if (self.current_scope.isNone())
                0
            else
                self.sym_table.scope_arena.getScope(self.current_scope).depth;
        }
        self.pure_comptime_depth = prev_pure_depth + 1;
        defer {
            self.pure_comptime_depth = prev_pure_depth;
            self.comptime_boundary_scope_depth = prev_boundary;
        }

        const res_ty = if (!expected_ty.isError())
            try self.checkExpr(inner_id, expected_ty)
        else
            try self.synthExpr(inner_id);
        return self.recordNodeType(expr_id, res_ty);
    }

    /// Evaluates a `comptime if` (and chained `else if`) condition at compile time, pruning statically dead branches.
    fn synthOrCheckComptimeIfNode(
        self: *TypeChecker,
        if_node_id: NodeIndex,
        expected_ty: TypeId,
    ) anyerror!TypeId {
        const ast_node = self.ast_arena.getNode(if_node_id);
        const saved_scope = self.current_scope;
        const if_scope = try self.sym_table.scope_arena.allocScope(
            .block_scope,
            self.current_scope,
            .NONE,
            self.file_id,
            .{},
        );
        self.current_scope = if_scope;
        defer self.current_scope = saved_scope;

        var folded_cond: ?i128 = null;
        if (ast_node.lhs.tag == .node) {
            const cond_id = NodeIndex.fromInt(ast_node.lhs.payload);
            const prev_pure_depth = self.pure_comptime_depth;
            const prev_boundary = self.comptime_boundary_scope_depth;
            if (prev_pure_depth == 0) {
                self.comptime_boundary_scope_depth = if (saved_scope.isNone())
                    0
                else
                    self.sym_table.scope_arena.getScope(saved_scope).depth;
            }
            self.pure_comptime_depth = prev_pure_depth + 1;
            defer {
                self.pure_comptime_depth = prev_pure_depth;
                self.comptime_boundary_scope_depth = prev_boundary;
            }

            try self.checkConditionOrLetHeader(cond_id, self.ast_arena.getCstOrigin(if_node_id));
            const cond_ast = self.ast_arena.getNode(cond_id);
            const is_let_header = cond_ast.tag == .binary_expr and cond_ast.lhs.tag == .extra;
            if (!is_let_header) {
                folded_cond = try self.evalConstIntExpr(cond_id, false);
            }
        }

        if (ast_node.rhs.tag == .node) {
            const then_id = NodeIndex.fromInt(ast_node.rhs.payload);
            if (folded_cond == null or folded_cond.? != 0) {
                if (folded_cond == null) self.comptime_branch_guard_depth += 1;
                defer if (folded_cond == null) {
                    self.comptime_branch_guard_depth -= 1;
                };
                _ = try self.checkBlock(then_id, .unit_ty, false);
                try symbol_resolver.checkUnusedBindingsInScope(
                    self.sym_table,
                    if_scope,
                    self.interner,
                    self.diagnostic_sink,
                );
            }
            return self.recordNodeType(if_node_id, .unit_ty);
        }

        const branches = self.getNodeExtraSlice(if_node_id, true);
        const then_id = if (branches.len >= 1) NodeIndex.fromInt(branches[0]) else .none;
        const else_id = if (branches.len >= 2) NodeIndex.fromInt(branches[1]) else .none;

        if (folded_cond) |const_flag| {
            if (const_flag != 0) {
                const taken_then_ty = if (!expected_ty.isError())
                    try self.checkBlock(then_id, expected_ty, false)
                else
                    try self.checkBlock(then_id, .err_ty, false);
                try symbol_resolver.checkUnusedBindingsInScope(
                    self.sym_table,
                    if_scope,
                    self.interner,
                    self.diagnostic_sink,
                );
                const mat_then = if (taken_then_ty == .never_ty)
                    (if (!expected_ty.isError()) expected_ty else .never_ty)
                else
                    self.materializeUntypedType(taken_then_ty);
                return self.recordNodeType(if_node_id, mat_then);
            }

            self.current_scope = saved_scope;
            if (else_id.isNone()) return self.recordNodeType(if_node_id, .unit_ty);
            const taken_else_ty = if (self.ast_arena.getNode(else_id).tag == .if_expr)
                try self.synthOrCheckComptimeIfNode(else_id, expected_ty)
            else
                try self.checkBlock(else_id, expected_ty, false);
            const mat_else = if (taken_else_ty == .never_ty)
                (if (!expected_ty.isError()) expected_ty else .never_ty)
            else
                self.materializeUntypedType(taken_else_ty);
            return self.recordNodeType(if_node_id, mat_else);
        }

        // Unfolded polymorphic `comptime if`: check both branches under `comptime_branch_guard_depth`:
        self.comptime_branch_guard_depth += 1;
        defer self.comptime_branch_guard_depth -= 1;

        const then_ty = if (!expected_ty.isError())
            try self.checkBlock(then_id, expected_ty, false)
        else
            try self.checkBlock(then_id, .err_ty, false);
        try symbol_resolver.checkUnusedBindingsInScope(
            self.sym_table,
            if_scope,
            self.interner,
            self.diagnostic_sink,
        );

        self.current_scope = saved_scope;
        const branch_expected = if (!expected_ty.isError())
            expected_ty
        else if (then_ty != .never_ty)
            self.materializeUntypedType(then_ty)
        else
            .err_ty;

        const else_ty = if (!else_id.isNone()) blk: {
            if (self.ast_arena.getNode(else_id).tag == .if_expr) {
                break :blk try self.synthOrCheckComptimeIfNode(else_id, branch_expected);
            }
            break :blk try self.checkBlock(else_id, branch_expected, false);
        } else .unit_ty;

        const final_ty = if (then_ty == .never_ty)
            else_ty
        else if (else_ty == .never_ty)
            then_ty
        else
            self.materializeUntypedType(then_ty);
        return self.recordNodeType(if_node_id, final_ty);
    }

    /// Synthesizes a closure expression (`|p1, p2| body`), binding parameters inside a dedicated `.fn_scope`.
    fn synthClosureExpr(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        const saved_scope = self.current_scope;
        const saved_ret_ty = self.current_fn_ret_ty;
        const saved_defer_depth = self.defer_depth;
        const saved_defer_loop_depth = self.defer_inner_loop_depth;
        const closure_scope = try self.sym_table.scope_arena.allocScope(
            .fn_scope,
            self.current_scope,
            .NONE,
            self.file_id,
            .{},
        );
        self.current_scope = closure_scope;
        self.current_fn_ret_ty = .err_ty;
        self.defer_depth = 0;
        self.defer_inner_loop_depth = 0;
        defer {
            self.current_scope = saved_scope;
            self.current_fn_ret_ty = saved_ret_ty;
            self.defer_depth = saved_defer_depth;
            self.defer_inner_loop_depth = saved_defer_loop_depth;
        }

        const param_tokens = self.getNodeExtraSlice(expr_id, false);
        const param_count = param_tokens.len;
        const param_types = try self.allocator.alloc(TypeId, param_count);
        defer if (param_types.len > 0) self.allocator.free(param_types);
        const param_modes = try self.allocator.alloc(ParamMode, param_count);
        defer if (param_modes.len > 0) self.allocator.free(param_modes);
        @memset(param_modes, .let_mode);
        for (param_tokens, 0..) |raw_tok, i| {
            const param_tok = TokenIndex.fromInt(raw_tok);
            param_types[i] = .err_ty;
            if (!param_tok.isNone() and param_tok.asInt() < self.token_buffer.countTokens()) {
                const param_name = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, param_tok);
                if (param_name.len > 0 and !std.mem.eql(u8, param_name, "_")) {
                    const param_sym = try self.interner.intern(param_name);
                    _ = try self.sym_table.defineSymbol(.{
                        .name = param_sym,
                        .name_text = self.interner.get(param_sym),
                        .kind = .param_sym,
                        .namespace = .value_ns,
                        .visibility = .private,
                        .flags = .{ .is_used = true },
                        .scope_id = closure_scope,
                        .decl_span = self.token_buffer.getTokenSpan(self.file_id, param_tok),
                        .type_id = .err_ty,
                        .member_ordinal = @intCast(i),
                    }, self.diagnostic_sink);
                }
            }
        }

        const body_ty: TypeId = if (ast_node.rhs.tag == .node)
            self.materializeUntypedType(try self.synthExpr(NodeIndex.fromInt(ast_node.rhs.payload)))
        else
            .unit_ty;

        try symbol_resolver.checkUnusedBindingsInScope(self.sym_table, closure_scope, self.interner, self.diagnostic_sink);
        return self.pool.internFn(.closure_ty, param_types, param_modes, body_ty, false);
    }

    /// Type-checks `[e_0, …, e_k]` or `[val; count]` array literals with optional expected element type and length.
    fn checkArrayLitWithElemType(
        self: *TypeChecker,
        expr_id: NodeIndex,
        expected_elem_ty: TypeId,
        expected_rhs_opt: ?u32,
    ) !TypeId {
        const elem_nodes = self.getNodeExtraSlice(expr_id, false);
        const has_expected_elem = !expected_elem_ty.isError();
        if (elem_nodes.len == 0) {
            const empty_elem = if (has_expected_elem) expected_elem_ty else .i32_ty;
            const arr_ty = try self.pool.internArray(empty_elem, 0, false);
            return self.recordNodeType(expr_id, arr_ty);
        }

        const arr_cst = self.ast_arena.getCstOrigin(expr_id);
        if (elem_nodes.len == 2 and hasShallowSemicolonInArrayCst(self.cst_arena, self.token_buffer, arr_cst)) {
            const val_id = NodeIndex.fromInt(elem_nodes[0]);
            const count_id = NodeIndex.fromInt(elem_nodes[1]);
            const resolved_elem_ty = if (has_expected_elem)
                try self.checkExpr(val_id, expected_elem_ty)
            else
                self.materializeUntypedType(try self.synthExpr(val_id));

            if (try self.findConstParamInExpr(count_id, 0)) |const_param_sym_idx| {
                self.pure_comptime_depth += 1;
                defer self.pure_comptime_depth -= 1;
                _ = try self.checkExpr(count_id, .usize_ty);
                if (self.ast_arena.getNode(count_id).tag != .ident_expr) {
                    try self.emitDiagnosticSimple(
                        .e0503_forbidden_comptime_operation,
                        self.getAstNodeSpan(count_id),
                        "compound dependent array repeat count requires a named `const` binding; only direct `[val; N]` is supported",
                        "compound `const` parameter expression in repeat count",
                    );
                    return self.recordNodeType(expr_id, .err_ty);
                }
                const sym_arr = try self.pool.internSymbolicArray(
                    if (has_expected_elem) expected_elem_ty else resolved_elem_ty,
                    self.sym_table.getSymbol(const_param_sym_idx).name,
                    false,
                );
                return self.recordNodeType(expr_id, sym_arr);
            }

            const count_ty = blk_cnt: {
                self.pure_comptime_depth += 1;
                defer self.pure_comptime_depth -= 1;
                break :blk_cnt try self.checkExpr(count_id, .usize_ty);
            };
            if (count_ty.isError()) return self.recordNodeType(expr_id, .err_ty);
            const count_val = (try self.evalConstIntExpr(count_id, true)) orelse {
                return self.recordNodeType(expr_id, .err_ty);
            };
            if (count_val < 0 or count_val > 0x7FFF_FFFF) {
                try self.emitDiagnosticSimple(
                    .e0502_integer_constant_overflow,
                    self.getAstNodeSpan(count_id),
                    "array repeat count must fit within `0..=2147483647`",
                    "invalid negative or overflowing repeat count",
                );
                return self.recordNodeType(expr_id, .err_ty);
            }
            _ = expected_rhs_opt;
            const elem_final = if (has_expected_elem) expected_elem_ty else resolved_elem_ty;
            const rep_ty = try self.pool.internArray(elem_final, @intCast(count_val), false);
            return self.recordNodeType(expr_id, rep_ty);
        }

        const elem_ty = if (has_expected_elem) blk_exp: {
            for (elem_nodes) |raw_elem| {
                _ = try self.checkExpr(NodeIndex.fromInt(raw_elem), expected_elem_ty);
            }
            break :blk_exp expected_elem_ty;
        } else blk_inf: {
            const first_ty = self.materializeUntypedType(
                try self.synthExpr(NodeIndex.fromInt(elem_nodes[0])),
            );
            for (elem_nodes[1..]) |raw_elem| {
                _ = try self.checkExpr(NodeIndex.fromInt(raw_elem), first_ty);
            }
            break :blk_inf first_ty;
        };
        const arr_ty = try self.pool.internArray(elem_ty, @intCast(elem_nodes.len), false);
        return self.recordNodeType(expr_id, arr_ty);
    }

    /// Type-checks any `{expr}` interpolation segments inside a non-raw `.string_lit` in `self.current_scope`.
    fn synthStringLit(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const str_node = self.ast_arena.getNode(expr_id);
        if (str_node.main_token.isNone() or str_node.main_token.asInt() >= self.token_buffer.countTokens()) {
            return .str_ty;
        }
        const tok_span = self.token_buffer.getTokenSpan(self.file_id, str_node.main_token);
        const lexeme = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, str_node.main_token);
        if (extractRawStringContent(lexeme) != null) return .str_ty;
        if (lexeme.len < 2 or lexeme[0] != '"' or lexeme[lexeme.len - 1] != '"') return .str_ty;

        const body = lexeme[1 .. lexeme.len - 1];
        var scan_pos: usize = 0;
        while (scanNextInterpolationSegment(body, scan_pos)) |seg| {
            scan_pos = seg.after_close;
            const expr_text = std.mem.trim(u8, body[seg.expr_start..seg.expr_end], " \t\r\n");
            if (expr_text.len == 0) continue;

            const wrapper_prefix = "fn __cx_interp__() {\n";
            const wrapper_suffix = "\n}\n";
            const wrapped_src = try std.mem.concat(
                self.allocator,
                u8,
                &[_][]const u8{ wrapper_prefix, body[seg.expr_start..seg.expr_end], wrapper_suffix },
            );
            defer self.allocator.free(wrapped_src);

            var sub_tokens = TokenBuffer.init(self.allocator);
            defer sub_tokens.deinit();
            var sub_cst = LosslessCstArena.init(self.allocator);
            defer sub_cst.deinit();
            var sub_ast = AstArena.init(self.allocator);
            defer sub_ast.deinit();
            var sub_diags = DiagnosticSink.init(self.allocator);
            defer sub_diags.deinit();

            _ = try parser.parseSource(
                wrapped_src,
                self.file_id,
                &sub_tokens,
                &sub_cst,
                &sub_ast,
                &sub_diags,
                self.interner,
            );

            if (sub_ast.countNodes() > 1) {
                var sub_checker = try TypeChecker.init(
                    self.allocator,
                    self.interner,
                    self.pool,
                    self.sym_table,
                    self.file_id,
                    wrapped_src,
                    &sub_tokens,
                    &sub_cst,
                    &sub_ast,
                    &sub_diags,
                );
                defer sub_checker.deinit();
                sub_checker.current_scope = self.current_scope;
                sub_checker.current_fn_ret_ty = self.current_fn_ret_ty;
                sub_checker.defer_depth = self.defer_depth;
                sub_checker.pure_comptime_depth = self.pure_comptime_depth;
                sub_checker.comptime_boundary_scope_depth = self.comptime_boundary_scope_depth;
                sub_checker.target_layout = self.target_layout;
                sub_checker.db = self.db;

                const root_node = sub_ast.getNode(.root);
                if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
                    const root_items = sub_ast.getExtraSlice(
                        ExtraIndex.fromInt(root_node.lhs.payload),
                        root_node.rhs.payload,
                    );
                    const fn_node = sub_ast.getNode(NodeIndex.fromInt(root_items[0]));
                    if (fn_node.rhs.tag == .node) {
                        _ = try sub_checker.checkBlock(NodeIndex.fromInt(fn_node.rhs.payload), .err_ty, false);
                    }
                }
            }

            if (self.diagnostic_sink) |main_sink| {
                const base_in_file: u32 = tok_span.start_byte + 1 + @as(u32, @intCast(seg.expr_start));
                const prefix_u32: u32 = @intCast(wrapper_prefix.len);
                for (sub_diags.asSlice()) |sub_diag| {
                    if (sub_diag.severity != .err) continue;
                    const rebased_start = if (sub_diag.primary_span.start_byte >= prefix_u32)
                        base_in_file + (sub_diag.primary_span.start_byte - prefix_u32)
                    else
                        tok_span.start_byte;
                    const span_len = sub_diag.primary_span.end_byte -| sub_diag.primary_span.start_byte;
                    const rebased_span = Span.init(
                        self.file_id,
                        @min(rebased_start, tok_span.end_byte),
                        @min(rebased_start + @max(span_len, 1), tok_span.end_byte),
                    );
                    const msg_copy = try main_sink.arena.asAllocator().dupe(u8, sub_diag.message);
                    const lbl_text = if (sub_diag.labels.len > 0)
                        try main_sink.arena.asAllocator().dupe(u8, sub_diag.labels[0].label)
                    else
                        "in interpolated string expression";
                    const labels = [1]LabeledSpan{
                        .{ .span = rebased_span, .label = lbl_text, .style = .primary },
                    };
                    _ = try main_sink.emit(.{
                        .code = sub_diag.code,
                        .severity = sub_diag.severity,
                        .primary_span = rebased_span,
                        .message = msg_copy,
                        .labels = &labels,
                    });
                }
            }
        }
        return .str_ty;
    }

    /// Synthesizes the `TypeId` of an integer literal (`int_lit`), verifying suffix bounds (`E0502`).
    fn synthIntLiteral(self: *TypeChecker, lit_id: NodeIndex, is_negated: bool) !TypeId {
        const lit_node = self.ast_arena.getNode(lit_id);
        if (!lit_node.main_token.isNone() and lit_node.main_token.asInt() < self.token_buffer.countTokens() and
            self.token_buffer.getToken(lit_node.main_token).flags.has_lexer_error)
        {
            return .err_ty;
        }
        const lexeme = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, lit_node.main_token);
        const parsed = extractIntLiteralValue(lexeme) orelse {
            try self.emitDiagnosticSimple(
                .e0502_integer_constant_overflow,
                self.getAstNodeSpan(lit_id),
                "integer literal overflows maximum representable width",
                "literal value exceeds 128-bit integer capacity",
            );
            return .err_ty;
        };

        const i128_min_abs: u128 = @as(u128, @intCast(std.math.maxInt(i128))) + 1;
        if (parsed.is_above_i128_max) {
            if (is_negated and parsed.magnitude == i128_min_abs) {
                if (parsed.suffix_ty) |suffix_ty| {
                    if (suffix_ty != .i128_ty) {
                        try self.emitDiagnosticSimple(
                            .e0502_integer_constant_overflow,
                            self.getAstNodeSpan(lit_id),
                            "integer literal out of range for explicit suffix type",
                            "literal value does not fit in target integer type",
                        );
                    }
                    return suffix_ty;
                }
                return .i128_ty;
            }
            if (!is_negated and parsed.suffix_ty == .u128_ty) {
                return .u128_ty;
            }
            try self.emitDiagnosticSimple(
                .e0502_integer_constant_overflow,
                self.getAstNodeSpan(lit_id),
                "integer literal overflows signed 128-bit integer range",
                "literal value exceeds signed 128-bit capacity",
            );
            return .err_ty;
        }

        const signed_val: i128 = if (is_negated) -parsed.value else parsed.value;
        if (parsed.suffix_ty) |suffix_ty| {
            if (getPrimitiveIntBounds(suffix_ty)) |bounds| {
                if (signed_val < bounds.min_val or signed_val > bounds.max_val) {
                    try self.emitDiagnosticSimple(
                        .e0502_integer_constant_overflow,
                        self.getAstNodeSpan(lit_id),
                        "integer literal out of range for explicit suffix type",
                        "literal value does not fit in target integer type",
                    );
                }
            }
            return suffix_ty;
        }
        return .untyped_int_ty;
    }

    /// Checks an integer literal (possibly negated) against `expected_ty` (`E0502` / `E0406`).
    fn checkIntLiteralAgainstExpected(
        self: *TypeChecker,
        lit_id: NodeIndex,
        is_negated: bool,
        expected_ty: TypeId,
    ) !TypeId {
        const lit_node = self.ast_arena.getNode(lit_id);
        if (!lit_node.main_token.isNone() and lit_node.main_token.asInt() < self.token_buffer.countTokens() and
            self.token_buffer.getToken(lit_node.main_token).flags.has_lexer_error)
        {
            return self.recordNodeType(lit_id, .err_ty);
        }
        const lexeme = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, lit_node.main_token);
        const parsed = extractIntLiteralValue(lexeme) orelse {
            try self.emitDiagnosticSimple(
                .e0502_integer_constant_overflow,
                self.getAstNodeSpan(lit_id),
                "integer literal overflows maximum representable width",
                "literal value exceeds integer capacity",
            );
            return self.recordNodeType(lit_id, .err_ty);
        };

        const exp_node = self.pool.getNode(expected_ty);
        const exp_base_ty = self.pool.unwrapRefinementBase(expected_ty);
        const i128_min_abs: u128 = @as(u128, @intCast(std.math.maxInt(i128))) + 1;

        if (parsed.is_above_i128_max) {
            if (!is_negated and exp_base_ty == .u128_ty and self.pool.getRefinementBounds(expected_ty) == null) {
                return self.recordNodeType(lit_id, expected_ty);
            }
            if (is_negated and parsed.magnitude == i128_min_abs and exp_base_ty == .i128_ty) {
                if (self.pool.getRefinementBounds(expected_ty)) |ref_bounds| {
                    if (std.math.minInt(i128) < ref_bounds.min_val) {
                        try self.emitRangeRefinementError(
                            self.getAstNodeSpan(lit_id),
                            expected_ty,
                            std.math.minInt(i128),
                            ref_bounds.min_val,
                            ref_bounds.max_val,
                        );
                        return self.recordNodeType(lit_id, .err_ty);
                    }
                }
                return self.recordNodeType(lit_id, expected_ty);
            }
            try self.emitDiagnosticSimple(
                .e0502_integer_constant_overflow,
                self.getAstNodeSpan(lit_id),
                "integer literal out of bounds for target integer type",
                "literal overflows target integer range",
            );
            return self.recordNodeType(lit_id, .err_ty);
        }

        const signed_val: i128 = if (is_negated) -parsed.value else parsed.value;
        if (parsed.suffix_ty) |suffix_ty| {
            const is_var = exp_node.tag == .bind_once_group_var or
                exp_node.tag == .bind_many_any_var or
                exp_node.tag == .type_param;
            if (!is_var and suffix_ty != expected_ty and suffix_ty != exp_base_ty) {
                try self.emitTypeMismatch(self.getAstNodeSpan(lit_id), expected_ty, suffix_ty);
                return self.recordNodeType(lit_id, .err_ty);
            }
        }

        // [1] Check `T is low..=high` range refinement (`E0406`, `DR-04` Section 1.5):
        if (self.pool.getRefinementBounds(expected_ty)) |ref_bounds| {
            if (signed_val < ref_bounds.min_val or signed_val > ref_bounds.max_val) {
                try self.emitRangeRefinementError(
                    self.getAstNodeSpan(lit_id),
                    expected_ty,
                    signed_val,
                    ref_bounds.min_val,
                    ref_bounds.max_val,
                );
                return self.recordNodeType(lit_id, .err_ty);
            }
            return self.recordNodeType(lit_id, expected_ty);
        }

        // [2] Reject implicit coercion into `distinct` newtype without constructor/cast (`E0405`):
        if (self.pool.getTag(expected_ty) == .distinct_ty) {
            try self.emitDistinctMixingError(
                self.getAstNodeSpan(lit_id),
                expected_ty,
                parsed.suffix_ty orelse .i32_ty,
            );
            return self.recordNodeType(lit_id, .err_ty);
        }

        // [3] Check primitive integer bounds (`E0502`):
        if (getPrimitiveIntBounds(expected_ty)) |prim_bounds| {
            if (signed_val < prim_bounds.min_val or signed_val > prim_bounds.max_val) {
                try self.emitDiagnosticSimple(
                    .e0502_integer_constant_overflow,
                    self.getAstNodeSpan(lit_id),
                    "integer literal out of bounds for target integer type",
                    "literal overflows target integer range",
                );
                return self.recordNodeType(lit_id, .err_ty);
            }
            return self.recordNodeType(lit_id, expected_ty);
        }

        // [4] Check satisfaction if `expected_ty` is a Type Group variable:
        if (exp_node.tag == .bind_once_group_var or
            exp_node.tag == .bind_many_any_var or
            exp_node.tag == .type_param)
        {
            const group_ty = TypeId.fromInt(exp_node.lhs);
            const check_cand = parsed.suffix_ty orelse .untyped_int_ty;
            if (checkGroupSatisfaction(self.pool, check_cand, group_ty) != .rejected) {
                return self.recordNodeType(lit_id, expected_ty);
            }
        }

        try self.emitTypeMismatch(
            self.getAstNodeSpan(lit_id),
            expected_ty,
            parsed.suffix_ty orelse .i32_ty,
        );
        return self.recordNodeType(lit_id, .err_ty);
    }

    /// Synthesizes the `TypeId` of a floating-point literal (`float_lit`).
    fn synthFloatLiteral(self: *const TypeChecker, lit_id: NodeIndex) TypeId {
        const lit_node = self.ast_arena.getNode(lit_id);
        const lexeme = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, lit_node.main_token);
        if (std.mem.endsWith(u8, lexeme, "f32")) return .f32_ty;
        if (std.mem.endsWith(u8, lexeme, "f64")) return .f64_ty;
        return .untyped_float_ty;
    }

    /// Rejects reading outer non-`comptime` runtime variables inside a pure `comptime` context (`E0503`).
    fn checkComptimeSymbolAccess(
        self: *TypeChecker,
        expr_id: NodeIndex,
        sym_idx: SymbolIndex,
    ) !void {
        if (self.pure_comptime_depth == 0 or sym_idx.isNone()) return;
        const sym = self.sym_table.getSymbol(sym_idx).*;
        if (sym.kind == .param_sym or sym.kind == .local_let_sym or sym.kind == .local_var_sym) {
            if (sym.flags.is_comptime) return;
            const sym_depth: u16 = if (sym.scope_id.isNone())
                0
            else
                self.sym_table.scope_arena.getScope(sym.scope_id).depth;
            if (sym_depth <= self.comptime_boundary_scope_depth) {
                try self.emitDiagnosticSimple(
                    .e0503_forbidden_comptime_operation,
                    self.getAstNodeSpan(expr_id),
                    "cannot read non-`comptime` runtime variable inside `comptime` evaluation",
                    "runtime variable referenced in `comptime` context",
                );
            }
        }
    }

    /// Resolves an `.ident_expr` or `.path_expr` in value/constant/enum namespace (`E0403` / `E0409`).
    fn synthIdentOrPathExpr(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.tag == .ident_expr) {
            if (!ast_node.main_token.isNone() and
                self.token_buffer.getToken(ast_node.main_token).kind == .at)
            {
                try self.emitDiagnosticSimple(
                    .e0401_type_mismatch,
                    self.getAstNodeSpan(expr_id),
                    "compiler intrinsic must be invoked as a call expression",
                    "add `(…)` or `[T](…)` to invoke this intrinsic",
                );
                return .err_ty;
            }
            const lexeme = symbol_resolver.extractTokenSlice(
                self.source,
                self.token_buffer,
                ast_node.main_token,
            );
            if (lexeme.len == 0) return .err_ty;
            const sym_id = try self.interner.intern(lexeme);
            const span = self.token_buffer.getTokenSpan(self.file_id, ast_node.main_token);

            switch (self.sym_table.lookupLexical(self.current_scope, sym_id, NamespaceMask.ALL)) {
                .found => |sym_idx| {
                    self.sym_table.markSymbolUsed(sym_idx);
                    self.recordNodeSymbol(expr_id, sym_idx);
                    try self.checkComptimeSymbolAccess(expr_id, sym_idx);
                    const sym = self.sym_table.getSymbol(sym_idx).*;
                    if (sym.kind == .fn_sym and sym.type_id.isError()) {
                        try self.resolveFnSignatureSymbol(sym_idx);
                    }
                    return self.sym_table.getSymbol(sym_idx).type_id;
                },
                .private_error => |priv_idx| {
                    if (self.diagnostic_sink) |sink| {
                        try symbol_resolver.emitPrivateAccessDiagnostic(
                            sink,
                            self.sym_table.getSymbol(priv_idx),
                            span,
                        );
                    }
                    return .err_ty;
                },
                .not_found => {
                    if (self.diagnostic_sink) |sink| {
                        const suggestion = self.sym_table.suggestClosestSymbol(
                            self.current_scope,
                            lexeme,
                            NamespaceMask.VALUE_OR_CONST,
                        );
                        try symbol_resolver.emitUnresolvedSymbolDiagnostic(
                            sink,
                            self.interner,
                            lexeme,
                            span,
                            suggestion,
                        );
                    }
                    return .err_ty;
                },
            }
        }

        // `.path_expr` (`mod::item` or `Enum::Variant`):
        const raw_segs = self.getNodeExtraSlice(expr_id, false);
        if (raw_segs.len == 0) return .err_ty;

        const seg_tokens = try self.allocator.alloc(TokenIndex, raw_segs.len);
        defer self.allocator.free(seg_tokens);
        for (raw_segs, 0..) |raw_tok, i| {
            seg_tokens[i] = TokenIndex.fromInt(raw_tok);
        }

        const last_tok = seg_tokens[seg_tokens.len - 1];
        const last_lexeme = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, last_tok);
        const last_span = self.token_buffer.getTokenSpan(self.file_id, last_tok);

        const target_scope = try symbol_resolver.resolveModulePathSegments(
            self.sym_table,
            self.interner,
            self.file_id,
            self.current_scope,
            self.current_scope,
            seg_tokens[0 .. seg_tokens.len - 1],
            self.source,
            self.token_buffer,
            self.diagnostic_sink,
        );
        if (target_scope.isNone()) return .err_ty;

        const last_sym_id = try self.interner.intern(last_lexeme);
        switch (self.sym_table.lookupInTargetScope(
            target_scope,
            self.current_scope,
            last_sym_id,
            NamespaceMask.ALL,
        )) {
            .found => |sym_idx| {
                self.sym_table.markSymbolUsed(sym_idx);
                self.recordNodeSymbol(expr_id, sym_idx);
                try self.checkComptimeSymbolAccess(expr_id, sym_idx);
                const sym = self.sym_table.getSymbol(sym_idx).*;
                if (sym.kind == .fn_sym and sym.type_id.isError()) {
                    try self.resolveFnSignatureSymbol(sym_idx);
                } else if (sym.kind == .enum_variant_sym) {
                    for (self.sym_table.symbols.items) |cand_sym| {
                        if (cand_sym.kind == .enum_sym and cand_sym.target_scope == target_scope) {
                            if (sym.type_id == .unit_ty) return cand_sym.type_id;
                            const param_tys = [_]TypeId{sym.type_id};
                            const param_modes = [_]ParamMode{.let_mode};
                            return self.pool.internFn(.fn_ty, &param_tys, &param_modes, cand_sym.type_id, false);
                        }
                    }
                }
                return self.sym_table.getSymbol(sym_idx).type_id;
            },
            .private_error => |priv_idx| {
                if (self.diagnostic_sink) |sink| {
                    try symbol_resolver.emitPrivateAccessDiagnostic(
                        sink,
                        self.sym_table.getSymbol(priv_idx),
                        last_span,
                    );
                }
                return .err_ty;
            },
            .not_found => {
                if (self.diagnostic_sink) |sink| {
                    const suggestion = self.sym_table.suggestClosestInScope(
                        target_scope,
                        last_lexeme,
                        NamespaceMask.ALL,
                    );
                    try symbol_resolver.emitUnresolvedSymbolDiagnostic(
                        sink,
                        self.interner,
                        last_lexeme,
                        last_span,
                        suggestion,
                    );
                }
                return .err_ty;
            },
        }
    }

    /// Checks a contextual `.Variant` or `.Variant(args)` expression against `expected_ty` (`E0407`, `DR-04` / `DR-07`).
    fn checkContextualVariant(
        self: *TypeChecker,
        expr_id: NodeIndex,
        expected_ty: TypeId,
    ) !TypeId {
        const expr_node = self.ast_arena.getNode(expr_id);
        const var_tok = if (expr_node.lhs.tag == .token)
            TokenIndex.fromInt(expr_node.lhs.payload)
        else
            expr_node.main_token;
        const var_name = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, var_tok);
        const arg_nodes = self.getNodeExtraSlice(expr_id, true);

        const exp_node = self.pool.getNode(expected_ty);
        switch (exp_node.tag) {
            .optional_ty => {
                const payload_ty = TypeId.fromInt(exp_node.lhs);
                if (std.mem.eql(u8, var_name, "None")) {
                    if (arg_nodes.len > 0) {
                        try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), .unit_ty, payload_ty);
                    }
                    return self.recordNodeType(expr_id, expected_ty);
                }
                if (std.mem.eql(u8, var_name, "Some")) {
                    if (arg_nodes.len == 1) {
                        _ = try self.checkExpr(NodeIndex.fromInt(arg_nodes[0]), payload_ty);
                    } else {
                        try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), payload_ty, .unit_ty);
                    }
                    return self.recordNodeType(expr_id, expected_ty);
                }
            },
            .result_ty => {
                const ok_ty = TypeId.fromInt(exp_node.lhs);
                const err_ty_arg = TypeId.fromInt(exp_node.rhs);
                if (std.mem.eql(u8, var_name, "Ok")) {
                    if (arg_nodes.len == 1 and ok_ty != .unit_ty) {
                        _ = try self.checkExpr(NodeIndex.fromInt(arg_nodes[0]), ok_ty);
                    } else if (arg_nodes.len == 1 and ok_ty == .unit_ty) {
                        const extra_ty = self.materializeUntypedType(
                            try self.synthExpr(NodeIndex.fromInt(arg_nodes[0])),
                        );
                        if (extra_ty != .unit_ty) {
                            try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), .unit_ty, extra_ty);
                        }
                    } else if (arg_nodes.len > 1) {
                        try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), ok_ty, .unit_ty);
                    } else if (ok_ty != .unit_ty) {
                        try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), ok_ty, .unit_ty);
                    }
                    return self.recordNodeType(expr_id, expected_ty);
                }
                if (std.mem.eql(u8, var_name, "Err")) {
                    if (arg_nodes.len == 1 and err_ty_arg != .unit_ty) {
                        _ = try self.checkExpr(NodeIndex.fromInt(arg_nodes[0]), err_ty_arg);
                    } else if (arg_nodes.len == 1 and err_ty_arg == .unit_ty) {
                        const extra_ty = self.materializeUntypedType(
                            try self.synthExpr(NodeIndex.fromInt(arg_nodes[0])),
                        );
                        if (extra_ty != .unit_ty) {
                            try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), .unit_ty, extra_ty);
                        }
                    } else if (arg_nodes.len > 1) {
                        try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), err_ty_arg, .unit_ty);
                    } else if (err_ty_arg != .unit_ty) {
                        try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), err_ty_arg, .unit_ty);
                    }
                    return self.recordNodeType(expr_id, expected_ty);
                }
            },
            .enum_ty => {
                const enum_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(exp_node.rhs)).*;
                if (!enum_sym.target_scope.isNone()) {
                    if (self.interner.lookup(var_name)) |var_sym_id| {
                        const v_idx = self.sym_table.lookupInScopeDirect(
                            enum_sym.target_scope,
                            var_sym_id,
                            NamespaceMask.VALUE_ONLY,
                        );
                        if (!v_idx.isNone()) {
                            self.sym_table.markSymbolUsed(v_idx);
                            self.recordNodeSymbol(expr_id, v_idx);
                            const v_sym = self.sym_table.getSymbol(v_idx).*;
                            if (v_sym.type_id == .unit_ty) {
                                if (arg_nodes.len > 0) {
                                    for (arg_nodes) |raw_arg| {
                                        _ = try self.synthExpr(NodeIndex.fromInt(raw_arg));
                                    }
                                    try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), .unit_ty, expected_ty);
                                }
                            } else if (self.pool.getTag(v_sym.type_id) == .tuple_ty) {
                                const tup_elems = self.pool.getTupleElements(v_sym.type_id);
                                if (arg_nodes.len != tup_elems.len) {
                                    try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), v_sym.type_id, .unit_ty);
                                }
                                for (arg_nodes, 0..) |raw_arg, i| {
                                    const exp_elem = if (i < tup_elems.len)
                                        TypeId.fromInt(tup_elems[i])
                                    else
                                        .err_ty;
                                    _ = try self.checkExpr(NodeIndex.fromInt(raw_arg), exp_elem);
                                }
                            } else if (arg_nodes.len == 1) {
                                _ = try self.checkExpr(NodeIndex.fromInt(arg_nodes[0]), v_sym.type_id);
                            } else {
                                for (arg_nodes) |raw_arg| {
                                    _ = try self.synthExpr(NodeIndex.fromInt(raw_arg));
                                }
                                if (!v_sym.type_id.isError()) {
                                    try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), v_sym.type_id, .unit_ty);
                                }
                            }
                            return self.recordNodeType(expr_id, expected_ty);
                        }
                    }
                }
            },
            else => {},
        }

        // Emit `E0407` unresolved contextual variant:
        var expected_buf: [96]u8 = undefined;
        const expected_str = self.pool.formatType(expected_ty, self.sym_table, &expected_buf);
        var msg_buf: [192]u8 = undefined;
        const msg = std.fmt.bufPrint(
            &msg_buf,
            "contextual variant `.{s}` does not exist on expected type `{s}`",
            .{ var_name, expected_str },
        ) catch "unresolved contextual variant for expected type";
        try self.emitDiagnosticSimple(
            .e0407_invalid_contextual_variant,
            self.getAstNodeSpan(expr_id),
            msg,
            "variant not found on expected type",
        );
        return self.recordNodeType(expr_id, .err_ty);
    }

    /// Synthesizes a `StructLiteral` expression (`Point { x: 1, y: 2 }`).
    fn synthStructLit(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.lhs.tag != .node) return .err_ty;
        const path_node_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const struct_ty = try self.resolveNamedOrGroupTypeRaw(path_node_id);
        if (struct_ty.isError()) return .err_ty;

        const struct_node = self.pool.getNode(self.pool.unwrapUnderlyingType(struct_ty));
        const target_scope: ScopeId = if (struct_node.tag == .struct_ty or
            struct_node.tag == .union_ty or struct_node.tag == .bit_field_ty)
            self.sym_table.getSymbol(SymbolIndex.fromInt(struct_node.rhs)).target_scope
        else
            .none;

        const field_exprs = self.getNodeExtraSlice(expr_id, true);
        const lit_cst = self.ast_arena.getCstOrigin(expr_id);

        // Extract `.field_init` field name tokens in order from `lit_cst`:
        var field_name_tokens: std.ArrayListUnmanaged(TokenIndex) = .empty;
        defer field_name_tokens.deinit(self.allocator);
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
                            leaf.token.asInt() < self.token_buffer.countTokens())
                        {
                            const tok_kind = self.token_buffer.getToken(leaf.token).kind;
                            if (symbol_resolver.isIdentifierToken(tok_kind)) {
                                try field_name_tokens.append(self.allocator, leaf.token);
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

        for (field_exprs, 0..) |raw_val_expr, i| {
            const val_expr_id = NodeIndex.fromInt(raw_val_expr);
            var expected_field_ty: TypeId = .err_ty;
            if (!target_scope.isNone() and i < field_name_tokens.items.len) {
                const f_tok = field_name_tokens.items[i];
                const f_name = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, f_tok);
                const f_sym_id = try self.interner.intern(f_name);
                const f_sym_idx = self.sym_table.lookupInScopeDirect(
                    target_scope,
                    f_sym_id,
                    NamespaceMask.VALUE_ONLY,
                );
                if (!f_sym_idx.isNone()) {
                    self.sym_table.markSymbolUsed(f_sym_idx);
                    expected_field_ty = self.sym_table.getSymbol(f_sym_idx).type_id;
                } else if (self.diagnostic_sink) |sink| {
                    const suggestion = self.sym_table.suggestClosestInScope(
                        target_scope,
                        f_name,
                        NamespaceMask.VALUE_ONLY,
                    );
                    try symbol_resolver.emitUnresolvedSymbolDiagnostic(
                        sink,
                        self.interner,
                        f_name,
                        self.token_buffer.getTokenSpan(self.file_id, f_tok),
                        suggestion,
                    );
                }
            }
            if (!expected_field_ty.isError()) {
                _ = try self.checkExpr(val_expr_id, expected_field_ty);
            } else {
                _ = try self.synthExpr(val_expr_id);
            }
        }
        return struct_ty;
    }

    /// Synthesizes a unary prefix expression (`-x`, `!b`, `not b`, `&x`, `&mut x`, `*p`, `comptime e`).
    fn synthUnaryExpr(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.lhs.tag != .node) return .err_ty;
        const inner_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const op_kind = self.token_buffer.getToken(ast_node.main_token).kind;

        switch (op_kind) {
            .kw_comptime => return self.synthOrCheckComptimePrefixExpr(expr_id, .err_ty),
            .minus => {
                if (self.ast_arena.getNode(inner_id).tag == .int_lit) {
                    return self.synthIntLiteral(inner_id, true);
                }
                const operand_ty = try self.synthExpr(inner_id);
                if (operand_ty.isError()) return .err_ty;
                const base_ty = self.pool.unwrapRefinementBase(operand_ty);
                if (base_ty == .untyped_int_ty or base_ty == .untyped_float_ty or
                    base_ty.isSignedIntPrimitive() or base_ty.isFloatPrimitive())
                {
                    return base_ty;
                }
                try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), .i32_ty, operand_ty);
                return .err_ty;
            },
            .kw_not => {
                const operand_ty = try self.checkExpr(inner_id, .bool_ty);
                return if (operand_ty.isError()) .err_ty else .bool_ty;
            },
            .bang => {
                const operand_ty = try self.synthExpr(inner_id);
                if (operand_ty.isError()) return .err_ty;
                if (operand_ty == .bool_ty or operand_ty.isIntegerPrimitive() or operand_ty == .untyped_int_ty) {
                    return operand_ty;
                }
                try self.emitTypeMismatch(self.getAstNodeSpan(expr_id), .bool_ty, operand_ty);
                return .err_ty;
            },
            .amp, .kw_ref => {
                const operand_ty = self.materializeUntypedType(try self.synthExpr(inner_id));
                const is_mut = self.hasMutKeywordInCst(self.ast_arena.getCstOrigin(expr_id));
                return self.pool.internRef(operand_ty, is_mut);
            },
            .star => {
                const operand_ty = try self.synthExpr(inner_id);
                if (operand_ty.isError()) return .err_ty;
                const op_node = self.pool.getNode(operand_ty);
                return switch (op_node.tag) {
                    .ref_ty, .mut_ref_ty, .raw_ptr_ty => TypeId.fromInt(op_node.lhs),
                    else => blk: {
                        try self.emitDiagnosticSimple(
                            .e0401_type_mismatch,
                            self.getAstNodeSpan(expr_id),
                            "cannot dereference non-pointer / non-reference value",
                            "expected `&T`, `&mut T`, `*const T`, or `*mut T`",
                        );
                        break :blk .err_ty;
                    },
                };
            },
            .ident => {
                const op_lex = symbol_resolver.extractTokenSlice(
                    self.source,
                    self.token_buffer,
                    ast_node.main_token,
                );
                if (std.mem.eql(u8, op_lex, "yield")) {
                    return self.checkExpr(inner_id, self.current_fn_ret_ty);
                }
                return self.synthExpr(inner_id);
            },
            else => return self.synthExpr(inner_id),
        }
    }

    /// Synthesizes a binary infix expression, enforcing `distinct` isolation (`E0405`), `expr is Pattern`, and `catch`.
    fn synthBinaryExpr(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        const op_kind = self.token_buffer.getToken(ast_node.main_token).kind;

        if (op_kind == .kw_catch) {
            const saved_pos = self.is_direct_positive_cond;
            self.is_direct_positive_cond = false;
            defer self.is_direct_positive_cond = saved_pos;
            return self.synthCatchExpr(expr_id, .err_ty);
        }

        const lhs_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;
        const rhs_id = if (ast_node.rhs.tag == .node) NodeIndex.fromInt(ast_node.rhs.payload) else .none;

        if (op_kind == .kw_is) {
            const is_positive_here = self.is_direct_positive_cond;
            const scrutinee_ty = eval_scrutinee: {
                const saved_pos = self.is_direct_positive_cond;
                self.is_direct_positive_cond = false;
                defer self.is_direct_positive_cond = saved_pos;
                break :eval_scrutinee self.materializeUntypedType(try self.synthExpr(lhs_id));
            };
            if (!rhs_id.isNone()) {
                if (is_positive_here) {
                    try self.bindPattern(rhs_id, scrutinee_ty, false);
                } else {
                    const saved_scope = self.current_scope;
                    const temp_scope = try self.sym_table.scope_arena.allocScope(
                        .match_arm_scope,
                        self.current_scope,
                        .NONE,
                        self.file_id,
                        .{},
                    );
                    self.current_scope = temp_scope;
                    defer self.current_scope = saved_scope;
                    try self.bindPattern(rhs_id, scrutinee_ty, false);
                }
            }
            return .bool_ty;
        }

        if (op_kind == .ampamp or op_kind == .kw_and) {
            _ = try self.checkExpr(lhs_id, .bool_ty);
            _ = try self.checkExpr(rhs_id, .bool_ty);
            return .bool_ty;
        }

        const saved_pos = self.is_direct_positive_cond;
        self.is_direct_positive_cond = false;
        defer self.is_direct_positive_cond = saved_pos;

        if (op_kind == .pipepipe or op_kind == .kw_or) {
            _ = try self.checkExpr(lhs_id, .bool_ty);
            _ = try self.checkExpr(rhs_id, .bool_ty);
            return .bool_ty;
        }

        const is_lhs_ctx_var = !lhs_id.isNone() and
            self.ast_arena.getNode(lhs_id).tag == .contextual_variant;
        const is_rhs_ctx_var = !rhs_id.isNone() and
            self.ast_arena.getNode(rhs_id).tag == .contextual_variant;

        var lhs_ty: TypeId = .err_ty;
        var rhs_ty: TypeId = .err_ty;
        if (is_lhs_ctx_var and !is_rhs_ctx_var) {
            rhs_ty = self.materializeUntypedType(try self.synthExpr(rhs_id));
            lhs_ty = if (!rhs_ty.isError())
                try self.checkExpr(lhs_id, rhs_ty)
            else
                try self.synthExpr(lhs_id);
        } else if (is_rhs_ctx_var and !is_lhs_ctx_var) {
            lhs_ty = self.materializeUntypedType(try self.synthExpr(lhs_id));
            rhs_ty = if (!lhs_ty.isError())
                try self.checkExpr(rhs_id, lhs_ty)
            else
                try self.synthExpr(rhs_id);
        } else {
            lhs_ty = try self.synthExpr(lhs_id);
            rhs_ty = try self.synthExpr(rhs_id);
        }
        if (lhs_ty.isError() or rhs_ty.isError()) return .err_ty;

        // [1] Reject mixing `distinct` newtype with its base type or another `distinct` type (`E0405`, `DR-04` Section 1.4):
        const is_lhs_distinct = self.pool.getTag(lhs_ty) == .distinct_ty;
        const is_rhs_distinct = self.pool.getTag(rhs_ty) == .distinct_ty;
        if ((is_lhs_distinct or is_rhs_distinct) and lhs_ty != rhs_ty) {
            try self.emitDistinctMixingError(self.getAstNodeSpan(expr_id), lhs_ty, rhs_ty);
            return .err_ty;
        }

        // [2] Unwrap zero-cost `is` range refinements (`T is low..=high` widens to `T` under arithmetic, `DR-04` Section 1.5):
        const lhs_base = self.pool.unwrapRefinementBase(lhs_ty);
        const rhs_base = self.pool.unwrapRefinementBase(rhs_ty);

        const unified_ty: TypeId = blk: {
            if (lhs_base == rhs_base) break :blk lhs_base;
            if (lhs_base == .untyped_int_ty and (rhs_base.isIntegerPrimitive() or
                self.isIntegerBoundedVar(rhs_base)))
            {
                _ = try self.checkExpr(lhs_id, rhs_base);
                break :blk rhs_base;
            }
            if (rhs_base == .untyped_int_ty and (lhs_base.isIntegerPrimitive() or
                self.isIntegerBoundedVar(lhs_base)))
            {
                _ = try self.checkExpr(rhs_id, lhs_base);
                break :blk lhs_base;
            }
            if (lhs_base == .untyped_float_ty and rhs_base.isFloatPrimitive()) break :blk rhs_base;
            if (rhs_base == .untyped_float_ty and lhs_base.isFloatPrimitive()) break :blk lhs_base;

            try self.emitTypeMismatch(
                self.getAstNodeSpan(rhs_id),
                self.materializeUntypedType(lhs_ty),
                self.materializeUntypedType(rhs_ty),
            );
            break :blk .err_ty;
        };

        if (unified_ty.isError()) return .err_ty;

        return switch (op_kind) {
            .eqeq, .bang_eq, .lt, .le, .gt, .ge => .bool_ty,
            .eq,
            .plus_eq,
            .minus_eq,
            .star_eq,
            .slash_eq,
            .percent_eq,
            .amp_eq,
            .pipe_eq,
            .caret_eq,
            .shl_eq,
            .shr_eq,
            => .unit_ty,
            else => unified_ty,
        };
    }

    /// Synthesizes postfix `expr?` (`try_expr`), enforcing `E0410` and `@from` `FromError` upcasting (`E0411`, `DR-07` Section 2.1).
    fn synthTryExpr(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.lhs.tag != .node) return .err_ty;
        const inner_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const operand_ty = try self.synthExpr(inner_id);
        if (operand_ty.isError()) return .err_ty;

        if (self.defer_depth > 0) {
            try self.emitDiagnosticSimple(
                .e0410_try_outside_fallible_fn,
                self.getAstNodeSpan(expr_id),
                "uncaught `?` operator cannot propagate out of a `defer` or `errdefer` block",
                "handle fallible operations locally inside `defer` / `errdefer` with `catch`",
            );
            const op_node_defer = self.pool.getNode(self.pool.unwrapUnderlyingType(operand_ty));
            return switch (op_node_defer.tag) {
                .optional_ty, .result_ty => TypeId.fromInt(op_node_defer.lhs),
                else => .err_ty,
            };
        }

        const op_node = self.pool.getNode(self.pool.unwrapUnderlyingType(operand_ty));
        const unwrapped_fn_ret_ty = self.pool.unwrapUnderlyingType(self.current_fn_ret_ty);
        const fn_ret_node = self.pool.getNode(unwrapped_fn_ret_ty);

        switch (op_node.tag) {
            .optional_ty => {
                const payload_ty = TypeId.fromInt(op_node.lhs);
                if (!unwrapped_fn_ret_ty.isError() and fn_ret_node.tag != .optional_ty) {
                    try self.emitDiagnosticSimple(
                        .e0410_try_outside_fallible_fn,
                        self.getAstNodeSpan(expr_id),
                        "`?` on optional `T?` requires enclosing function to return an optional `U?`",
                        "enclosing function does not return an optional type",
                    );
                } else {
                    try self.try_conversions.put(self.allocator, expr_id.asInt(), .NONE);
                }
                return payload_ty;
            },
            .result_ty => {
                const ok_ty = TypeId.fromInt(op_node.lhs);
                const inner_err_ty = TypeId.fromInt(op_node.rhs);

                if (!unwrapped_fn_ret_ty.isError() and fn_ret_node.tag != .result_ty) {
                    try self.emitDiagnosticSimple(
                        .e0410_try_outside_fallible_fn,
                        self.getAstNodeSpan(expr_id),
                        "`?` on `Result[T, E]` requires enclosing function to return `Result[U, F]`",
                        "enclosing function does not return `Result`",
                    );
                    return ok_ty;
                }

                var conv_def_id: DefId = .NONE;
                if (fn_ret_node.tag == .result_ty) {
                    const outer_err_ty = TypeId.fromInt(fn_ret_node.rhs);
                    if (!inner_err_ty.isError() and !outer_err_ty.isError() and inner_err_ty != outer_err_ty) {
                        const pair_key = packFromErrorPair(inner_err_ty, outer_err_ty);
                        if (self.sym_table.from_error_pairs.contains(pair_key)) {
                            conv_def_id = self.sym_table.from_error_fn_defs.get(pair_key) orelse .NONE;
                        } else {
                            var src_buf: [64]u8 = undefined;
                            var dst_buf: [64]u8 = undefined;
                            const src_name = self.pool.formatType(inner_err_ty, self.sym_table, &src_buf);
                            const dst_name = self.pool.formatType(outer_err_ty, self.sym_table, &dst_buf);
                            var msg_buf: [192]u8 = undefined;
                            const msg = std.fmt.bufPrint(
                                &msg_buf,
                                "cannot convert error `{s}` to `{s}` via `?`; missing `@from` conversion",
                                .{ src_name, dst_name },
                            ) catch "missing `@from` error conversion for `?` operator";
                            try self.emitDiagnosticSimple(
                                .e0411_missing_from_error_conversion,
                                self.getAstNodeSpan(expr_id),
                                msg,
                                "define an `@from fn from_err(e: SourceError) -> TargetError` conversion",
                            );
                        }
                    }
                }
                try self.try_conversions.put(self.allocator, expr_id.asInt(), conv_def_id);
                return ok_ty;
            },
            else => {
                try self.emitDiagnosticSimple(
                    .e0410_try_outside_fallible_fn,
                    self.getAstNodeSpan(expr_id),
                    "the `?` operator can only be applied to `Result[T, E]` or `T?` values",
                    "operand is not a fallible `Result` or optional type",
                );
                return .err_ty;
            },
        }
    }

    /// Synthesizes or checks `fallible_expr catch [|err|] fallback` (`DR-07` Section 2.2).
    fn synthCatchExpr(self: *TypeChecker, expr_id: NodeIndex, expected_ty: TypeId) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        const lhs_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;
        const rhs_id = if (ast_node.rhs.tag == .node) NodeIndex.fromInt(ast_node.rhs.payload) else .none;

        const lhs_ty = try self.synthExpr(lhs_id);
        const lhs_node = self.pool.getNode(lhs_ty);
        var ok_ty: TypeId = .err_ty;
        var err_payload_ty: TypeId = .err_ty;

        switch (lhs_node.tag) {
            .result_ty => {
                ok_ty = TypeId.fromInt(lhs_node.lhs);
                err_payload_ty = TypeId.fromInt(lhs_node.rhs);
            },
            .optional_ty => {
                ok_ty = TypeId.fromInt(lhs_node.lhs);
                err_payload_ty = .unit_ty;
            },
            else => {
                if (!lhs_ty.isError()) {
                    try self.emitDiagnosticSimple(
                        .e0410_try_outside_fallible_fn,
                        self.getAstNodeSpan(lhs_id),
                        "`catch` requires a `Result[T, E]` or `T?` left-hand operand",
                        "expression is not a `Result` or optional value",
                    );
                }
            },
        }

        const saved_scope = self.current_scope;
        const catch_scope = try self.sym_table.scope_arena.allocScope(
            .catch_or_errdefer_scope,
            self.current_scope,
            .NONE,
            self.file_id,
            .{},
        );
        self.current_scope = catch_scope;
        defer self.current_scope = saved_scope;

        // Bind optional `|err|` capture token inside `expr_id`'s CST:
        const catch_cst = self.ast_arena.getCstOrigin(expr_id);
        if (!catch_cst.isNone() and catch_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = catch_cst.asInt();
            const rec = self.cst_arena.getNode(catch_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var is_after_catch = false;
            var is_after_open_pipe = false;
            var cur = start_idx + 1;
            while (cur < end_idx) : (cur += 1) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.subtree_size <= 1 and !sub.token.isNone() and
                    sub.token.asInt() < self.token_buffer.countTokens())
                {
                    if (sub.token == ast_node.main_token) {
                        is_after_catch = true;
                    } else if (is_after_catch and self.token_buffer.getToken(sub.token).kind == .pipe) {
                        if (is_after_open_pipe) break;
                        is_after_open_pipe = true;
                    } else if (is_after_open_pipe and
                        symbol_resolver.isIdentifierToken(self.token_buffer.getToken(sub.token).kind))
                    {
                        const cap_name = symbol_resolver.extractTokenSlice(
                            self.source,
                            self.token_buffer,
                            sub.token,
                        );
                        if (cap_name.len > 0 and !std.mem.eql(u8, cap_name, "_")) {
                            const cap_sym = try self.interner.intern(cap_name);
                            _ = try self.sym_table.defineSymbol(.{
                                .name = cap_sym,
                                .name_text = self.interner.get(cap_sym),
                                .kind = .local_var_sym,
                                .namespace = .value_ns,
                                .visibility = .private,
                                .flags = .{},
                                .scope_id = catch_scope,
                                .decl_span = self.token_buffer.getTokenSpan(self.file_id, sub.token),
                                .type_id = err_payload_ty,
                            }, self.diagnostic_sink);
                        }
                        break;
                    }
                }
            }
        }

        const target_ty = if (!expected_ty.isError()) expected_ty else ok_ty;
        if (!rhs_id.isNone()) {
            const rhs_ty = if (!target_ty.isError())
                try self.checkExpr(rhs_id, target_ty)
            else
                try self.synthExpr(rhs_id);
            _ = rhs_ty;
        }
        try symbol_resolver.checkUnusedBindingsInScope(self.sym_table, catch_scope, self.interner, self.diagnostic_sink);
        return self.recordNodeType(expr_id, target_ty);
    }

    /// Synthesizes `.field_access` (`s.field`, `tup.0`, or `#soa [T]` column slice `soa.field -> [FieldType]`).
    fn synthFieldAccess(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .token) return .err_ty;
        const recv_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const member_tok = TokenIndex.fromInt(ast_node.rhs.payload);

        const raw_recv_ty = try self.synthExpr(recv_id);
        if (raw_recv_ty.isError()) return .err_ty;
        const recv_ty = self.unwrapRefType(raw_recv_ty);
        const recv_node = self.pool.getNode(recv_ty);
        const member_lexeme = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, member_tok);
        const member_span = self.token_buffer.getTokenSpan(self.file_id, member_tok);

        // [1] Tuple index access (`tup.0`, `tup.1`):
        if (recv_node.tag == .tuple_ty and self.token_buffer.getToken(member_tok).kind == .int_lit) {
            if (extractIntLiteralValue(member_lexeme)) |parsed| {
                const elems = self.pool.getTupleElements(recv_ty);
                if (parsed.value >= 0 and parsed.value < elems.len) {
                    return TypeId.fromInt(elems[@intCast(parsed.value)]);
                }
            }
            return .err_ty;
        }

        // [2] `#soa [S]` or `#soa [S; N]` column slice projection (`DR-04` Section 2.1):
        if (recv_node.tag == .soa_slice_ty or recv_node.tag == .soa_array_ty) {
            if (std.mem.eql(u8, member_lexeme, "len")) return .usize_ty;
            const elem_ty = TypeId.fromInt(recv_node.lhs);
            const elem_node = self.pool.getNode(elem_ty);
            if (elem_node.tag == .struct_ty) {
                const struct_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(elem_node.rhs)).*;
                if (!struct_sym.target_scope.isNone()) {
                    const f_sym_id = try self.interner.intern(member_lexeme);
                    const f_idx = self.sym_table.lookupInScopeDirect(
                        struct_sym.target_scope,
                        f_sym_id,
                        NamespaceMask.VALUE_ONLY,
                    );
                    if (!f_idx.isNone()) {
                        self.sym_table.markSymbolUsed(f_idx);
                        self.recordNodeSymbol(expr_id, f_idx);
                        const col_ty = self.sym_table.getSymbol(f_idx).type_id;
                        return self.pool.internSlice(col_ty, false);
                    }
                }
            }
        }

        // [3] Built-in `.len` property on slices, arrays, and `str`:
        if ((recv_node.tag == .slice_ty or recv_node.tag == .array_ty or recv_ty == .str_ty) and
            std.mem.eql(u8, member_lexeme, "len"))
        {
            return .usize_ty;
        }

        // [4] Nominal `struct`, `union`, or `bit_field` member access:
        if (recv_node.tag == .struct_ty or recv_node.tag == .union_ty or recv_node.tag == .bit_field_ty) {
            const type_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(recv_node.rhs)).*;
            if (!type_sym.target_scope.isNone()) {
                const member_sym_id = try self.interner.intern(member_lexeme);
                switch (self.sym_table.lookupInTargetScope(
                    type_sym.target_scope,
                    self.current_scope,
                    member_sym_id,
                    NamespaceMask.VALUE_ONLY,
                )) {
                    .found => |f_idx| {
                        self.sym_table.markSymbolUsed(f_idx);
                        self.recordNodeSymbol(expr_id, f_idx);
                        return self.sym_table.getSymbol(f_idx).type_id;
                    },
                    .private_error => |priv_idx| {
                        if (self.diagnostic_sink) |sink| {
                            try symbol_resolver.emitPrivateAccessDiagnostic(
                                sink,
                                self.sym_table.getSymbol(priv_idx),
                                member_span,
                            );
                        }
                        return .err_ty;
                    },
                    .not_found => {
                        if (self.diagnostic_sink) |sink| {
                            const suggestion = self.sym_table.suggestClosestInScope(
                                type_sym.target_scope,
                                member_lexeme,
                                NamespaceMask.VALUE_ONLY,
                            );
                            try symbol_resolver.emitUnresolvedSymbolDiagnostic(
                                sink,
                                self.interner,
                                member_lexeme,
                                member_span,
                                suggestion,
                            );
                        }
                        return .err_ty;
                    },
                }
            }
        }
        return .err_ty;
    }

    /// Synthesizes `base[index]` (`index_expr`).
    fn synthIndexExpr(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        const base_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;
        const idx_id = if (ast_node.rhs.tag == .node) NodeIndex.fromInt(ast_node.rhs.payload) else .none;

        const base_ty = self.unwrapRefType(try self.synthExpr(base_id));
        if (!idx_id.isNone()) {
            const idx_ty = try self.synthExpr(idx_id);
            const idx_base = self.pool.unwrapRefinementBase(idx_ty);
            if (!idx_base.isError() and idx_base != .untyped_int_ty and !idx_base.isIntegerPrimitive()) {
                try self.emitTypeMismatch(self.getAstNodeSpan(idx_id), .usize_ty, idx_ty);
            }
        }
        if (base_ty.isError()) return .err_ty;
        const base_node = self.pool.getNode(base_ty);
        return switch (base_node.tag) {
            .slice_ty, .soa_slice_ty, .array_ty, .soa_array_ty => TypeId.fromInt(base_node.lhs),
            else => .err_ty,
        };
    }

    /// Synthesizes `lhs |> rhs` pipeline calls (`lhs |> f`, `lhs |> f(a_1, …)`, and `lhs |> obj.m(a_1, …)`).
    fn synthPipeExpr(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.lhs.tag != .node or ast_node.rhs.tag != .node) return .err_ty;
        const lhs_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const rhs_id = NodeIndex.fromInt(ast_node.rhs.payload);
        const rhs_node = self.ast_arena.getNode(rhs_id);

        if (rhs_node.tag == .method_call) {
            if (rhs_node.lhs.tag != .node) return .err_ty;
            const recv_id = NodeIndex.fromInt(rhs_node.lhs.payload);
            const recv_ty = try self.synthExpr(recv_id);
            const raw_items = self.getNodeExtraSlice(rhs_id, true);
            if (raw_items.len == 0) return .err_ty;
            const member_tok = TokenIndex.fromInt(raw_items[0]);
            const member_name = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, member_tok);
            const member_span = self.token_buffer.getTokenSpan(self.file_id, member_tok);

            var type_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
            defer type_arg_nodes.deinit(self.allocator);
            var arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
            defer arg_nodes.deinit(self.allocator);
            try arg_nodes.append(self.allocator, lhs_id);
            for (raw_items[1..]) |raw_item| {
                const item_id = NodeIndex.fromInt(raw_item);
                if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
                if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) {
                    try type_arg_nodes.append(self.allocator, item_id);
                } else {
                    try arg_nodes.append(self.allocator, item_id);
                }
            }
            if (recv_ty.isError()) {
                for (type_arg_nodes.items) |type_node_id| _ = try self.resolveTypeAst(type_node_id);
                for (arg_nodes.items) |arg_id| _ = try self.synthExpr(arg_id);
                return .err_ty;
            }

            const unwrapped_recv = self.unwrapRefType(recv_ty);
            const recv_node = self.pool.getNode(unwrapped_recv);
            var lookup_owner_scope: ScopeId = .none;
            if (recv_node.tag == .struct_ty or recv_node.tag == .enum_ty or
                recv_node.tag == .union_ty or recv_node.tag == .trait_ty)
            {
                lookup_owner_scope = self.sym_table.getSymbol(SymbolIndex.fromInt(recv_node.rhs)).target_scope;
            } else if (recv_node.tag == .type_param or recv_node.tag == .bind_once_group_var or
                recv_node.tag == .bind_many_any_var)
            {
                const bound_node = self.pool.getNode(TypeId.fromInt(recv_node.lhs));
                if (bound_node.tag == .trait_ty) {
                    lookup_owner_scope = self.sym_table.getSymbol(SymbolIndex.fromInt(bound_node.rhs)).target_scope;
                }
            }
            if (!lookup_owner_scope.isNone()) {
                const method_sym_id = try self.interner.intern(member_name);
                switch (self.sym_table.lookupInTargetScope(
                    lookup_owner_scope,
                    self.current_scope,
                    method_sym_id,
                    NamespaceMask.VALUE_ONLY,
                )) {
                    .found => |m_idx| {
                        self.sym_table.markSymbolUsed(m_idx);
                        self.recordNodeSymbol(rhs_id, m_idx);
                        self.recordNodeSymbol(expr_id, m_idx);
                        try self.resolveFnSignatureSymbol(m_idx);
                        const m_ty = self.sym_table.getSymbol(m_idx).type_id;
                        const ret_ty = try self.checkCallArgumentsAgainstFn(
                            expr_id,
                            m_ty,
                            m_idx,
                            recv_id,
                            type_arg_nodes.items,
                            arg_nodes.items,
                        );
                        _ = self.recordNodeType(rhs_id, ret_ty);
                        return ret_ty;
                    },
                    .private_error => |priv_idx| {
                        if (self.diagnostic_sink) |sink| {
                            try symbol_resolver.emitPrivateAccessDiagnostic(
                                sink,
                                self.sym_table.getSymbol(priv_idx),
                                member_span,
                            );
                        }
                        return .err_ty;
                    },
                    .not_found => {},
                }
            }
            for (type_arg_nodes.items) |type_node_id| _ = try self.resolveTypeAst(type_node_id);
            for (arg_nodes.items) |arg_id| _ = try self.synthExpr(arg_id);
            return .err_ty;
        }

        var callee_id: NodeIndex = rhs_id;
        var type_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer type_arg_nodes.deinit(self.allocator);
        var arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer arg_nodes.deinit(self.allocator);
        try arg_nodes.append(self.allocator, lhs_id);

        if (rhs_node.tag == .call_expr or rhs_node.tag == .generic_call or rhs_node.tag == .incomplete_call) {
            if (rhs_node.lhs.tag == .node) callee_id = NodeIndex.fromInt(rhs_node.lhs.payload);
            const raw_items = self.getNodeExtraSlice(rhs_id, true);
            for (raw_items) |raw_item| {
                const item_id = NodeIndex.fromInt(raw_item);
                if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
                if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) {
                    try type_arg_nodes.append(self.allocator, item_id);
                } else {
                    try arg_nodes.append(self.allocator, item_id);
                }
            }
        }

        const callee_node = self.ast_arena.getNode(callee_id);
        if (callee_node.tag == .ident_expr and !callee_node.main_token.isNone() and
            self.token_buffer.getToken(callee_node.main_token).kind == .at)
        {
            return self.synthIntrinsicCall(expr_id, callee_id, type_arg_nodes.items, arg_nodes.items);
        }
        if (callee_node.tag == .ident_expr) {
            const name_str = symbol_resolver.extractTokenSlice(
                self.source,
                self.token_buffer,
                callee_node.main_token,
            );
            if (self.interner.lookup(name_str)) |sym_id| {
                switch (self.sym_table.lookupLexical(self.current_scope, sym_id, NamespaceMask.VALUE_ONLY)) {
                    .found => |found_idx| {
                        const found_sym = self.sym_table.getSymbol(found_idx).*;
                        if (found_sym.flags.is_overload) {
                            if (self.sym_table.getOverloadSet(found_sym.scope_id, sym_id)) |ov_set| {
                                if (ov_set.members.items.len > 1) {
                                    return self.resolveAndCheckOverloadCall(
                                        expr_id,
                                        ov_set.members.items,
                                        type_arg_nodes.items,
                                        arg_nodes.items,
                                    );
                                }
                            }
                        }
                    },
                    else => {},
                }
            }
        }

        const callee_ty = try self.synthExpr(callee_id);
        const callee_sym_idx = if (callee_id.asInt() < self.node_symbols.len)
            self.node_symbols[callee_id.asInt()]
        else
            SymbolIndex.none;
        if (!callee_sym_idx.isNone()) {
            self.recordNodeSymbol(expr_id, callee_sym_idx);
        }
        if (callee_ty.isError()) {
            for (type_arg_nodes.items) |type_node_id| _ = try self.resolveTypeAst(type_node_id);
            for (arg_nodes.items) |arg_id| _ = try self.synthExpr(arg_id);
            return .err_ty;
        }
        return self.checkCallArgumentsAgainstFn(
            expr_id,
            callee_ty,
            callee_sym_idx,
            null,
            type_arg_nodes.items,
            arg_nodes.items,
        );
    }

    /// Synthesizes a function, intrinsic, or generic function call (`call_expr`, `generic_call`, `incomplete_call`).
    fn synthCallExpr(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.lhs.tag != .node) return .err_ty;
        const callee_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const callee_node = self.ast_arena.getNode(callee_id);

        // Partition extra slice into explicit `[TypeArgs]` and `(CallArgs)`:
        const raw_items = self.getNodeExtraSlice(expr_id, true);
        var type_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer type_arg_nodes.deinit(self.allocator);
        var arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer arg_nodes.deinit(self.allocator);
        for (raw_items) |raw_item| {
            const item_id = NodeIndex.fromInt(raw_item);
            if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
            if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) {
                try type_arg_nodes.append(self.allocator, item_id);
                continue;
            }
            try arg_nodes.append(self.allocator, item_id);
        }
        const explicit_type_args = type_arg_nodes.items;
        const args = arg_nodes.items;

        // [1] Dispatch `@intrinsic` calls (`DR-05` §3.3):
        if (callee_node.tag == .ident_expr and !callee_node.main_token.isNone() and
            self.token_buffer.getToken(callee_node.main_token).kind == .at)
        {
            return self.synthIntrinsicCall(expr_id, callee_id, explicit_type_args, args);
        }

        // [2] Check if `callee_id` resolves to an `@overload` set in `self.sym_table`:
        if (callee_node.tag == .ident_expr) {
            const name_str = symbol_resolver.extractTokenSlice(
                self.source,
                self.token_buffer,
                callee_node.main_token,
            );
            if (self.interner.lookup(name_str)) |sym_id| {
                switch (self.sym_table.lookupLexical(
                    self.current_scope,
                    sym_id,
                    NamespaceMask.VALUE_ONLY,
                )) {
                    .found => |found_idx| {
                        const found_sym = self.sym_table.getSymbol(found_idx).*;
                        if (found_sym.flags.is_overload) {
                            if (self.sym_table.getOverloadSet(found_sym.scope_id, sym_id)) |ov_set| {
                                if (ov_set.members.items.len > 1) {
                                    return self.resolveAndCheckOverloadCall(
                                        expr_id,
                                        ov_set.members.items,
                                        explicit_type_args,
                                        args,
                                    );
                                }
                            }
                        }
                    },
                    else => {},
                }
            }
        }

        const callee_ty = try self.synthExpr(callee_id);
        const callee_sym_idx = if (callee_id.asInt() < self.node_symbols.len)
            self.node_symbols[callee_id.asInt()]
        else
            SymbolIndex.none;
        if (!callee_sym_idx.isNone()) {
            self.recordNodeSymbol(expr_id, callee_sym_idx);
        }
        if (callee_ty.isError()) {
            for (explicit_type_args) |type_node_id| {
                _ = try self.resolveTypeAst(type_node_id);
            }
            for (args) |arg_id| {
                _ = try self.synthExpr(arg_id);
            }
            return .err_ty;
        }

        return self.checkCallArgumentsAgainstFn(
            expr_id,
            callee_ty,
            callee_sym_idx,
            null,
            explicit_type_args,
            args,
        );
    }

    /// Type-checks all 12 Phase 5 `@intrinsic` calls (`DR-05` §3.3).
    fn synthIntrinsicCall(
        self: *TypeChecker,
        call_id: NodeIndex,
        callee_id: NodeIndex,
        type_arg_nodes: []const NodeIndex,
        val_args: []const NodeIndex,
    ) !TypeId {
        const callee_node = self.ast_arena.getNode(callee_id);
        const intr_tok = if (callee_node.lhs.tag == .token)
            TokenIndex.fromInt(callee_node.lhs.payload)
        else
            callee_node.main_token;
        const intr_name = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, intr_tok);

        const type_args = try self.allocator.alloc(TypeId, type_arg_nodes.len);
        defer if (type_args.len > 0) self.allocator.free(type_args);
        for (type_arg_nodes, 0..) |type_node_id, i| {
            type_args[i] = try self.resolveTypeAst(type_node_id);
        }
        if (type_arg_nodes.len > 0) {
            try self.recordCallInstantiation(call_id, type_args);
        }

        const intr_kind = INTRINSIC_NAME_MAP.get(intr_name) orelse {
            var msg_buf: [160]u8 = undefined;
            const msg = std.fmt.bufPrint(
                &msg_buf,
                "unknown compiler intrinsic `@{s}`",
                .{intr_name},
            ) catch "unknown compiler intrinsic";
            try self.emitDiagnosticSimple(
                .e0403_unresolved_symbol,
                self.getAstNodeSpan(callee_id),
                msg,
                "unrecognized `@intrinsic` name",
            );
            for (val_args) |arg_id| {
                _ = try self.synthExpr(arg_id);
            }
            return .err_ty;
        };

        switch (intr_kind) {
            .size_of, .align_of => {
                if (type_arg_nodes.len != 1 or val_args.len != 0) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "intrinsic expects exactly 1 type argument `[T]` and 0 value arguments `()`",
                        "expected `@size_of[T]()` / `@align_of[T]()`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                }
                return self.recordNodeType(callee_id, .usize_ty);
            },
            .type_name => {
                if (type_arg_nodes.len != 1 or val_args.len != 0) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "`@type_name` expects 1 type argument `[T]` and 0 value arguments `()`",
                        "expected `@type_name[T]()`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                }
                return self.recordNodeType(callee_id, .str_ty);
            },
            .default_init => {
                if (type_arg_nodes.len != 1 or val_args.len != 0) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "`@default_init` expects 1 type argument `[T]` and 0 value arguments `()`",
                        "expected `@default_init[T]()`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                    return .err_ty;
                }
                return self.recordNodeType(callee_id, type_args[0]);
            },
            .has_field => {
                if (type_arg_nodes.len != 1 or val_args.len != 1) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "`@has_field` expects 1 type argument `[T]` and 1 `comptime` `str` argument",
                        "expected `@has_field[T](\"field_name\")`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                    return .bool_ty;
                }
                const prev_pure = self.pure_comptime_depth;
                const prev_bound = self.comptime_boundary_scope_depth;
                if (prev_pure == 0) {
                    self.comptime_boundary_scope_depth = if (self.current_scope.isNone())
                        0
                    else
                        self.sym_table.scope_arena.getScope(self.current_scope).depth;
                }
                self.pure_comptime_depth = prev_pure + 1;
                defer {
                    self.pure_comptime_depth = prev_pure;
                    self.comptime_boundary_scope_depth = prev_bound;
                }
                _ = try self.checkExpr(val_args[0], .str_ty);
                return self.recordNodeType(callee_id, .bool_ty);
            },
            .implements => {
                if (type_arg_nodes.len != 2 or val_args.len != 0) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "`@implements` expects 2 type arguments `[T, Trait]` and 0 value arguments `()`",
                        "expected `@implements[T, Trait]()`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                    return .bool_ty;
                }
                if (!type_args[1].isError()) {
                    const bound_ty = self.pool.unwrapUnderlyingType(type_args[1]);
                    const trait_tag = self.pool.getTag(bound_ty);
                    if (trait_tag != .trait_ty and trait_tag != .builtin_group and trait_tag != .user_group) {
                        try self.emitDiagnosticSimple(
                            .e0401_type_mismatch,
                            self.getAstNodeSpan(type_arg_nodes[1]),
                            "second type argument to `@implements[T, Trait]()` must be a `trait` or Type Group",
                            "expected `trait` or Type Group here",
                        );
                    }
                }
                return self.recordNodeType(callee_id, .bool_ty);
            },
            .type_info => {
                if (type_arg_nodes.len != 1 or val_args.len != 0) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "`@type_info` expects 1 type argument `[T]` and 0 value arguments `()`",
                        "expected `@type_info[T]()`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                }
                try self.ensureReflectionMirrorTypes();
                return self.recordNodeType(callee_id, self.mirror_type_info_ty);
            },
            .field_attr_lookup => {
                try self.ensureReflectionMirrorTypes();
                if (type_arg_nodes.len != 1 or val_args.len != 2) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "`@field_attr_lookup` expects `[AttrSchema]` and `(owner_id: MetaId, index: u32)`",
                        "expected `@field_attr_lookup[A](id, idx)`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                    return if (type_arg_nodes.len >= 1)
                        try self.pool.internOptional(type_args[0])
                    else
                        .err_ty;
                }
                const schema_ty = type_args[0];
                if (!schema_ty.isError()) {
                    const schema_node = self.pool.getNode(schema_ty);
                    if (schema_node.tag == .struct_ty) {
                        const schema_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(schema_node.rhs)).*;
                        if (!schema_sym.flags.is_attribute_schema) {
                            try self.emitDiagnosticSimple(
                                .e0503_forbidden_comptime_operation,
                                self.getAstNodeSpan(type_arg_nodes[0]),
                                "type argument to `@field_attr_lookup[A]` must be an `@attribute_schema` struct",
                                "struct is missing `@attribute_schema`",
                            );
                        }
                    }
                }
                _ = try self.checkExpr(val_args[0], self.mirror_meta_id_ty);
                const idx_ty = try self.synthExpr(val_args[1]);
                const idx_base = self.pool.unwrapRefinementBase(idx_ty);
                if (!idx_base.isError() and idx_base != .u32_ty and idx_base != .usize_ty and
                    idx_base != .untyped_int_ty)
                {
                    try self.emitTypeMismatch(self.getAstNodeSpan(val_args[1]), .u32_ty, idx_ty);
                }
                const opt_attr_ty = try self.pool.internOptional(schema_ty);
                return self.recordNodeType(callee_id, opt_attr_ty);
            },
            .field => {
                if (type_arg_nodes.len != 0 or val_args.len != 2) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "`@field` expects 0 type arguments and 2 arguments `(target, field_name_or_info)`",
                        "expected `@field(target, field)`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                    return .err_ty;
                }
                const raw_target_ty = try self.synthExpr(val_args[0]);
                const spec_ty = eval_spec: {
                    const prev_pure = self.pure_comptime_depth;
                    const prev_bound = self.comptime_boundary_scope_depth;
                    if (prev_pure == 0) {
                        self.comptime_boundary_scope_depth = if (self.current_scope.isNone())
                            0
                        else
                            self.sym_table.scope_arena.getScope(self.current_scope).depth;
                    }
                    self.pure_comptime_depth = prev_pure + 1;
                    defer {
                        self.pure_comptime_depth = prev_pure;
                        self.comptime_boundary_scope_depth = prev_bound;
                    }
                    break :eval_spec try self.synthExpr(val_args[1]);
                };
                if (raw_target_ty.isError() or spec_ty.isError()) return .err_ty;

                const target_ty = self.unwrapRefType(raw_target_ty);
                const target_node = self.pool.getNode(target_ty);
                const spec_node = self.ast_arena.getNode(val_args[1]);

                if (spec_node.tag == .string_lit) {
                    const raw_lit = symbol_resolver.extractTokenSlice(
                        self.source,
                        self.token_buffer,
                        spec_node.main_token,
                    );
                    const field_name = if (raw_lit.len >= 2) raw_lit[1 .. raw_lit.len - 1] else "";
                    if ((target_node.tag == .slice_ty or target_node.tag == .array_ty or target_ty == .str_ty) and
                        std.mem.eql(u8, field_name, "len"))
                    {
                        return self.recordNodeType(callee_id, .usize_ty);
                    }
                    if (target_node.tag == .struct_ty or target_node.tag == .union_ty or
                        target_node.tag == .bit_field_ty)
                    {
                        const owner_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(target_node.rhs)).*;
                        if (!owner_sym.target_scope.isNone()) {
                            const field_sym_id = try self.interner.intern(field_name);
                            switch (self.sym_table.lookupInTargetScope(
                                owner_sym.target_scope,
                                self.current_scope,
                                field_sym_id,
                                NamespaceMask.VALUE_ONLY,
                            )) {
                                .found => |found_field_idx| {
                                    self.sym_table.markSymbolUsed(found_field_idx);
                                    self.recordNodeSymbol(call_id, found_field_idx);
                                    const projected_ty = self.sym_table.getSymbol(found_field_idx).type_id;
                                    return self.recordNodeType(callee_id, projected_ty);
                                },
                                .private_error => |priv_idx| {
                                    if (self.diagnostic_sink) |sink| {
                                        try symbol_resolver.emitPrivateAccessDiagnostic(
                                            sink,
                                            self.sym_table.getSymbol(priv_idx),
                                            self.getAstNodeSpan(val_args[1]),
                                        );
                                    }
                                    return .err_ty;
                                },
                                .not_found => {},
                            }
                        }
                    }
                    if (!self.pool.getFlags(target_ty).has_type_vars) {
                        if (self.diagnostic_sink) |sink| {
                            try symbol_resolver.emitUnresolvedSymbolDiagnostic(
                                sink,
                                self.interner,
                                field_name,
                                self.getAstNodeSpan(val_args[1]),
                                null,
                            );
                        }
                        return .err_ty;
                    }
                }

                const unwrapped_spec = self.unwrapRefType(spec_ty);
                const is_field_info = self.has_reflection_mirrors and unwrapped_spec == self.mirror_field_info_ty;
                if (unwrapped_spec != .str_ty and !is_field_info) {
                    try self.emitTypeMismatch(self.getAstNodeSpan(val_args[1]), .str_ty, spec_ty);
                    return .err_ty;
                }

                // Polymorphic or `comptime for` `FieldInfo` projection before unrolling:
                if (target_node.tag == .struct_ty) {
                    const owner_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(target_node.rhs)).*;
                    if (!owner_sym.target_scope.isNone()) {
                        var common_field_ty: TypeId = .err_ty;
                        var is_homogeneous = true;
                        for (self.sym_table.getScopeMembers(owner_sym.target_scope)) |mem_idx| {
                            const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                            if (mem_sym.kind != .field_sym) continue;
                            if (common_field_ty.isError()) {
                                common_field_ty = mem_sym.type_id;
                            } else if (common_field_ty != mem_sym.type_id) {
                                is_homogeneous = false;
                                break;
                            }
                        }
                        if (is_homogeneous and !common_field_ty.isError()) {
                            return self.recordNodeType(callee_id, common_field_ty);
                        }
                    }
                }
                const poly_ordinal = self.next_any_ordinal;
                self.next_any_ordinal += 1;
                const poly_proj_ty = try self.pool.internBindManyVar(.group_copy, poly_ordinal);
                return self.recordNodeType(callee_id, poly_proj_ty);
            },
            .embed_bytes => {
                const byte_slice_ty = try self.pool.internSlice(.u8_ty, false);
                const ref_bytes_ty = try self.pool.internRef(byte_slice_ty, false);
                if (type_arg_nodes.len != 0 or val_args.len != 1) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "`@embed_bytes` expects 0 type arguments and 1 `comptime` `str` path",
                        "expected `@embed_bytes(\"relative/path.bin\")`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                    return ref_bytes_ty;
                }
                {
                    const prev_pure = self.pure_comptime_depth;
                    const prev_bound = self.comptime_boundary_scope_depth;
                    if (prev_pure == 0) {
                        self.comptime_boundary_scope_depth = if (self.current_scope.isNone())
                            0
                        else
                            self.sym_table.scope_arena.getScope(self.current_scope).depth;
                    }
                    self.pure_comptime_depth = prev_pure + 1;
                    defer {
                        self.pure_comptime_depth = prev_pure;
                        self.comptime_boundary_scope_depth = prev_bound;
                    }
                    _ = try self.checkExpr(val_args[0], .str_ty);
                }
                const path_node = self.ast_arena.getNode(val_args[0]);
                if (path_node.tag == .string_lit) {
                    const raw_lit = symbol_resolver.extractTokenSlice(
                        self.source,
                        self.token_buffer,
                        path_node.main_token,
                    );
                    const rel_path = if (raw_lit.len >= 2) raw_lit[1 .. raw_lit.len - 1] else "";
                    const has_parent_escape = std.mem.indexOf(u8, rel_path, "..") != null;
                    const is_abs_path = (rel_path.len > 0 and (rel_path[0] == '/' or rel_path[0] == '\\')) or
                        (rel_path.len >= 2 and rel_path[1] == ':');
                    if (has_parent_escape or is_abs_path) {
                        try self.emitDiagnosticSimple(
                            .e0503_forbidden_comptime_operation,
                            self.getAstNodeSpan(val_args[0]),
                            "`@embed_bytes` path must be relative to the package root and cannot contain `..`",
                            "sandboxed `@embed_bytes` rejects parent traversal and absolute paths",
                        );
                    }
                }
                return self.recordNodeType(callee_id, ref_bytes_ty);
            },
            .compile_assert => {
                if (type_arg_nodes.len != 0 or val_args.len == 0 or val_args.len > 2) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "`@compile_assert` expects `(cond: bool)` or `(cond: bool, msg: str)`",
                        "expected `@compile_assert(cond, \"message\")`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                    return .unit_ty;
                }
                {
                    const prev_pure = self.pure_comptime_depth;
                    const prev_bound = self.comptime_boundary_scope_depth;
                    if (prev_pure == 0) {
                        self.comptime_boundary_scope_depth = if (self.current_scope.isNone())
                            0
                        else
                            self.sym_table.scope_arena.getScope(self.current_scope).depth;
                    }
                    self.pure_comptime_depth = prev_pure + 1;
                    defer {
                        self.pure_comptime_depth = prev_pure;
                        self.comptime_boundary_scope_depth = prev_bound;
                    }
                    _ = try self.checkExpr(val_args[0], .bool_ty);
                    if (val_args.len == 2) {
                        _ = try self.checkExpr(val_args[1], .str_ty);
                    }
                }
                if (self.comptime_branch_guard_depth == 0) {
                    if (try self.evalConstIntExpr(val_args[0], false)) |cond_val| {
                        if (cond_val == 0) {
                            var user_msg: []const u8 = "compile-time assertion failed";
                            if (val_args.len == 2 and self.ast_arena.getNode(val_args[1]).tag == .string_lit) {
                                const raw_msg = symbol_resolver.extractTokenSlice(
                                    self.source,
                                    self.token_buffer,
                                    self.ast_arena.getNode(val_args[1]).main_token,
                                );
                                if (raw_msg.len >= 2) user_msg = raw_msg[1 .. raw_msg.len - 1];
                            }
                            try self.emitDiagnosticSimple(
                                .e0510_compile_assertion_failed,
                                self.getAstNodeSpan(call_id),
                                user_msg,
                                "`@compile_assert` condition evaluated to `false`",
                            );
                        }
                    }
                }
                return self.recordNodeType(callee_id, .unit_ty);
            },
            .compile_error => {
                if (type_arg_nodes.len != 0 or val_args.len != 1) {
                    try self.emitDiagnosticSimple(
                        .e0401_type_mismatch,
                        self.getAstNodeSpan(call_id),
                        "`@compile_error` expects 0 type arguments and 1 `comptime` `str` message",
                        "expected `@compile_error(\"message\")`",
                    );
                    for (val_args) |arg_id| _ = try self.synthExpr(arg_id);
                    return .never_ty;
                }
                {
                    const prev_pure = self.pure_comptime_depth;
                    const prev_bound = self.comptime_boundary_scope_depth;
                    if (prev_pure == 0) {
                        self.comptime_boundary_scope_depth = if (self.current_scope.isNone())
                            0
                        else
                            self.sym_table.scope_arena.getScope(self.current_scope).depth;
                    }
                    self.pure_comptime_depth = prev_pure + 1;
                    defer {
                        self.pure_comptime_depth = prev_pure;
                        self.comptime_boundary_scope_depth = prev_bound;
                    }
                    _ = try self.checkExpr(val_args[0], .str_ty);
                }
                if (self.comptime_branch_guard_depth == 0) {
                    var user_msg: []const u8 = "explicit `@compile_error` triggered";
                    if (self.ast_arena.getNode(val_args[0]).tag == .string_lit) {
                        const raw_msg = symbol_resolver.extractTokenSlice(
                            self.source,
                            self.token_buffer,
                            self.ast_arena.getNode(val_args[0]).main_token,
                        );
                        if (raw_msg.len >= 2) user_msg = raw_msg[1 .. raw_msg.len - 1];
                    }
                    try self.emitDiagnosticSimple(
                        .e0510_compile_assertion_failed,
                        self.getAstNodeSpan(call_id),
                        user_msg,
                        "compile-time error triggered here",
                    );
                }
                return self.recordNodeType(callee_id, .never_ty);
            },
        }
    }

    /// Synthesizes `receiver.method(args)` (`method_call`).
    fn synthMethodCallExpr(self: *TypeChecker, expr_id: NodeIndex) !TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        if (ast_node.lhs.tag != .node) return .err_ty;
        const recv_id = NodeIndex.fromInt(ast_node.lhs.payload);
        const recv_ty = try self.synthExpr(recv_id);

        const raw_items = self.getNodeExtraSlice(expr_id, true);
        if (raw_items.len == 0) return .err_ty;
        const member_tok = TokenIndex.fromInt(raw_items[0]);
        const member_name = symbol_resolver.extractTokenSlice(self.source, self.token_buffer, member_tok);
        const member_span = self.token_buffer.getTokenSpan(self.file_id, member_tok);

        var type_arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer type_arg_nodes.deinit(self.allocator);
        var arg_nodes: std.ArrayListUnmanaged(NodeIndex) = .empty;
        defer arg_nodes.deinit(self.allocator);
        for (raw_items[1..]) |raw_item| {
            const item_id = NodeIndex.fromInt(raw_item);
            if (item_id.asInt() >= self.ast_arena.countNodes()) continue;
            if (isTypeAstTag(self.ast_arena.getNode(item_id).tag)) {
                try type_arg_nodes.append(self.allocator, item_id);
                continue;
            }
            try arg_nodes.append(self.allocator, item_id);
        }
        const explicit_type_args = type_arg_nodes.items;
        const args = arg_nodes.items;

        if (recv_ty.isError()) {
            for (explicit_type_args) |type_node_id| _ = try self.resolveTypeAst(type_node_id);
            for (args) |arg_id| {
                _ = try self.synthExpr(arg_id);
            }
            return .err_ty;
        }

        const unwrapped_recv = self.unwrapRefType(recv_ty);
        const recv_node = self.pool.getNode(unwrapped_recv);

        // Built-in `.len()` method on slices, arrays, `#soa` containers, and `str`:
        if ((recv_node.tag == .slice_ty or recv_node.tag == .array_ty or
            recv_node.tag == .soa_slice_ty or recv_node.tag == .soa_array_ty or
            unwrapped_recv == .str_ty) and
            std.mem.eql(u8, member_name, "len") and
            explicit_type_args.len == 0 and args.len == 0)
        {
            return .usize_ty;
        }

        var lookup_owner_scope: ScopeId = .none;
        if (recv_node.tag == .struct_ty or recv_node.tag == .enum_ty or
            recv_node.tag == .union_ty or recv_node.tag == .trait_ty)
        {
            lookup_owner_scope = self.sym_table.getSymbol(SymbolIndex.fromInt(recv_node.rhs)).target_scope;
        } else if (recv_node.tag == .type_param or recv_node.tag == .bind_once_group_var or
            recv_node.tag == .bind_many_any_var)
        {
            const bound_node = self.pool.getNode(TypeId.fromInt(recv_node.lhs));
            if (bound_node.tag == .trait_ty) {
                lookup_owner_scope = self.sym_table.getSymbol(SymbolIndex.fromInt(bound_node.rhs)).target_scope;
            }
        }

        if (!lookup_owner_scope.isNone()) {
            const method_sym_id = try self.interner.intern(member_name);
            switch (self.sym_table.lookupInTargetScope(
                lookup_owner_scope,
                self.current_scope,
                method_sym_id,
                NamespaceMask.VALUE_ONLY,
            )) {
                .found => |m_idx| {
                    self.sym_table.markSymbolUsed(m_idx);
                    self.recordNodeSymbol(expr_id, m_idx);
                    try self.resolveFnSignatureSymbol(m_idx);
                    const m_ty = self.sym_table.getSymbol(m_idx).type_id;
                    return self.checkCallArgumentsAgainstFn(
                        expr_id,
                        m_ty,
                        m_idx,
                        recv_id,
                        explicit_type_args,
                        args,
                    );
                },
                .private_error => |priv_idx| {
                    if (self.diagnostic_sink) |sink| {
                        try symbol_resolver.emitPrivateAccessDiagnostic(
                            sink,
                            self.sym_table.getSymbol(priv_idx),
                            member_span,
                        );
                    }
                    return .err_ty;
                },
                .not_found => {},
            }
        }

        for (explicit_type_args) |type_node_id| _ = try self.resolveTypeAst(type_node_id);
        for (args) |arg_id| {
            _ = try self.synthExpr(arg_id);
        }
        return .err_ty;
    }

    /// Resolves an `@overload` candidate set against `args`, emitting `E0400` on ambiguity (`DR-02` Section 1.2).
    fn resolveAndCheckOverloadCall(
        self: *TypeChecker,
        call_id: NodeIndex,
        candidates: []const SymbolIndex,
        explicit_type_args: []const NodeIndex,
        args: []const NodeIndex,
    ) !TypeId {
        const arg_types = try self.allocator.alloc(TypeId, args.len);
        defer if (arg_types.len > 0) self.allocator.free(arg_types);
        for (args, 0..) |arg_id, i| {
            arg_types[i] = try self.synthExpr(arg_id);
        }

        const MatchScore = enum(u8) {
            none = 0,
            group_or_tilde = 1,
            exact = 2,
        };

        var best_score: MatchScore = .none;
        var best_candidate: SymbolIndex = .none;
        var is_ambiguous = false;

        for (candidates) |cand_idx| {
            try self.resolveFnSignatureSymbol(cand_idx);
            const cand_ty = self.sym_table.getSymbol(cand_idx).type_id;
            const sig = self.pool.getFnSignatureView(cand_ty) orelse continue;
            if (sig.paramCount() != args.len) continue;

            var subst = SubstitutionMap{};
            defer subst.deinit(self.allocator);
            var cand_score: MatchScore = .exact;
            var has_all_matched = true;

            var p_i: usize = 0;
            while (p_i < sig.paramCount()) : (p_i += 1) {
                const param_ty = sig.getParamType(p_i);
                const arg_ty = self.materializeUntypedType(arg_types[p_i]);
                const p_node = self.pool.getNode(param_ty);

                if (param_ty == arg_ty) continue;
                if (p_node.tag == .bind_once_group_var or
                    p_node.tag == .bind_many_any_var or
                    p_node.tag == .type_param)
                {
                    const grp_ty = TypeId.fromInt(p_node.lhs);
                    if (checkGroupSatisfaction(self.pool, arg_ty, grp_ty) == .rejected or
                        checkGroupSatisfaction(self.pool, arg_ty, grp_ty) == .rejected_distinct_without_tilde)
                    {
                        has_all_matched = false;
                        break;
                    }
                    if (p_node.tag == .bind_once_group_var or p_node.tag == .type_param) {
                        if (subst.lookup(param_ty)) |prev_ty| {
                            if (prev_ty != arg_ty) {
                                has_all_matched = false;
                                break;
                            }
                        } else {
                            try subst.put(self.allocator, param_ty, arg_ty, self.getAstNodeSpan(args[p_i]));
                        }
                    }
                    cand_score = .group_or_tilde;
                } else if (self.pool.getFlags(param_ty).has_type_vars) {
                    if (!(try self.unifyParamTypeWithArg(
                        param_ty,
                        arg_ty,
                        self.getAstNodeSpan(args[p_i]),
                        &subst,
                        false,
                    ))) {
                        has_all_matched = false;
                        break;
                    }
                    cand_score = .group_or_tilde;
                } else {
                    has_all_matched = false;
                    break;
                }
            }

            if (!has_all_matched) continue;
            if (@intFromEnum(cand_score) > @intFromEnum(best_score)) {
                best_score = cand_score;
                best_candidate = cand_idx;
                is_ambiguous = false;
            } else if (cand_score == best_score) {
                is_ambiguous = true;
            }
        }

        if (is_ambiguous) {
            try self.emitDiagnosticSimple(
                .e0400_ambiguous_overload,
                self.getAstNodeSpan(call_id),
                "ambiguous call to `@overload` function group; multiple candidates match equally",
                "specify explicit type arguments or cast arguments to disambiguate",
            );
            return .err_ty;
        }
        if (best_candidate.isNone()) {
            try self.emitDiagnosticSimple(
                .e0401_type_mismatch,
                self.getAstNodeSpan(call_id),
                "no `@overload` candidate matches the supplied argument types",
                "no matching overload signature found",
            );
            return .err_ty;
        }

        self.sym_table.markSymbolUsed(best_candidate);
        self.recordNodeSymbol(call_id, best_candidate);
        const chosen_ty = self.sym_table.getSymbol(best_candidate).type_id;
        return self.checkCallArgumentsAgainstFn(
            call_id,
            chosen_ty,
            best_candidate,
            null,
            explicit_type_args,
            args,
        );
    }

    /// Two-Pass Spine-Local Argument, Generic `[T]`, & `comptime` Verification (`DR-02`, `DR-04`, `DR-05`):
    /// - Enforces `comptime fn` (`E0503` at runtime), `extern fn` (`E0503` at `comptime`), and `comptime` params (`E0503`),
    /// - Binds explicit `[TypeArgs]` and infers Bind-Once / Bind-Many Type Group parameters,
    /// - Records concrete instantiation tuples in `self.call_instantiations` (`[CRITICAL-11]`).
    fn checkCallArgumentsAgainstFn(
        self: *TypeChecker,
        call_id: NodeIndex,
        fn_ty: TypeId,
        callee_sym_idx: SymbolIndex,
        optional_self_recv: ?NodeIndex,
        explicit_type_args: []const NodeIndex,
        args: []const NodeIndex,
    ) !TypeId {
        var comptime_param_mask: u64 = 0;
        var declared_type_params: std.ArrayListUnmanaged(TypeId) = .empty;
        defer declared_type_params.deinit(self.allocator);

        if (!callee_sym_idx.isNone()) {
            const callee_sym = self.sym_table.getSymbol(callee_sym_idx).*;
            comptime_param_mask = callee_sym.is_comptime_param_mask;
            if (callee_sym.flags.is_comptime and self.pure_comptime_depth == 0) {
                try self.emitDiagnosticSimple(
                    .e0503_forbidden_comptime_operation,
                    self.getAstNodeSpan(call_id),
                    "`comptime fn` cannot be invoked at runtime; evaluate inside `comptime` or a `const` binding",
                    "compile-time-only function called in runtime context",
                );
            }
            if (callee_sym.flags.is_extern and self.pure_comptime_depth > 0) {
                try self.emitDiagnosticSimple(
                    .e0503_forbidden_comptime_operation,
                    self.getAstNodeSpan(call_id),
                    "cannot invoke `extern` FFI function during `comptime` evaluation",
                    "external FFI call is forbidden at compile time",
                );
            }
            if (!callee_sym.target_scope.isNone()) {
                for (self.sym_table.getScopeMembers(callee_sym.target_scope)) |mem_idx| {
                    const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                    if (mem_sym.kind == .type_param_sym and !mem_sym.type_id.isError()) {
                        try declared_type_params.append(self.allocator, mem_sym.type_id);
                    }
                }
            }
        }
        const declared_tp_count = declared_type_params.items.len;

        const sig = self.pool.getFnSignatureView(fn_ty) orelse {
            for (explicit_type_args) |type_node_id| _ = try self.resolveTypeAst(type_node_id);
            for (args) |arg_id| {
                _ = try self.synthExpr(arg_id);
            }
            return .err_ty;
        };

        var subst = SubstitutionMap{};
        defer subst.deinit(self.allocator);

        // Bind explicit `[TypeArgs]` if supplied at the call site:
        const resolved_explicit_tys = try self.allocator.alloc(TypeId, explicit_type_args.len);
        defer if (resolved_explicit_tys.len > 0) self.allocator.free(resolved_explicit_tys);
        for (explicit_type_args, 0..) |type_node_id, i| {
            const resolved_ty = try self.resolveTypeAst(type_node_id);
            resolved_explicit_tys[i] = resolved_ty;
            if (i < declared_tp_count and !resolved_ty.isError()) {
                const tp_id = declared_type_params.items[i];
                const tp_node = self.pool.getNode(tp_id);
                const grp_ty = TypeId.fromInt(tp_node.lhs);
                var sat = checkGroupSatisfaction(self.pool, resolved_ty, grp_ty);
                if (sat == .rejected and self.pool.getTag(grp_ty) == .trait_ty) {
                    if (try self.hasTraitImplementation(resolved_ty, grp_ty, 0)) {
                        sat = .matched_exact;
                    }
                }
                if (sat == .rejected or sat == .rejected_distinct_without_tilde) {
                    try self.emitGroupConstraintError(
                        self.getAstNodeSpan(type_node_id),
                        resolved_ty,
                        grp_ty,
                        sat == .rejected_distinct_without_tilde,
                    );
                }
                try subst.put(self.allocator, tp_id, resolved_ty, self.getAstNodeSpan(type_node_id));
            }
        }

        var param_offset: usize = 0;
        if (optional_self_recv != null and sig.paramCount() == args.len + 1) {
            param_offset = 1;
        }

        if (args.len + param_offset != sig.paramCount()) {
            try self.emitDiagnosticSimple(
                .e0401_type_mismatch,
                self.getAstNodeSpan(call_id),
                "function call argument count does not match parameter signature",
                "incorrect number of arguments passed to function",
            );
            for (args) |arg_id| {
                _ = try self.synthExpr(arg_id);
            }
            return subst.apply(self.pool, sig.ret_ty);
        }

        // Pass 1: Synthesize non-contextual arguments and populate `SubstitutionMap`:
        for (args, 0..) |arg_id, i| {
            const param_idx: usize = i + param_offset;
            const param_ty = sig.getParamType(param_idx);
            const arg_node = self.ast_arena.getNode(arg_id);
            if (arg_node.tag == .contextual_variant or arg_node.tag == .closure_expr) continue;

            const is_comptime_param = param_idx < 64 and
                (comptime_param_mask & (@as(u64, 1) << @intCast(param_idx))) != 0;
            const prev_pure = self.pure_comptime_depth;
            const prev_bound = self.comptime_boundary_scope_depth;
            if (is_comptime_param) {
                if (prev_pure == 0) {
                    self.comptime_boundary_scope_depth = if (self.current_scope.isNone())
                        0
                    else
                        self.sym_table.scope_arena.getScope(self.current_scope).depth;
                }
                self.pure_comptime_depth = prev_pure + 1;
            }
            defer if (is_comptime_param) {
                self.pure_comptime_depth = prev_pure;
                self.comptime_boundary_scope_depth = prev_bound;
            };

            if (self.pool.getFlags(param_ty).has_type_vars) {
                if (explicit_type_args.len > 0) {
                    const explicit_inst_param = try subst.apply(self.pool, param_ty);
                    if (!self.pool.getFlags(explicit_inst_param).has_type_vars) {
                        _ = try self.checkExpr(arg_id, explicit_inst_param);
                        continue;
                    }
                }
                const raw_arg_ty = try self.synthExpr(arg_id);
                if (raw_arg_ty.isError()) continue;
                const concrete_arg_ty = self.materializeUntypedType(raw_arg_ty);
                _ = try self.unifyParamTypeWithArg(
                    param_ty,
                    concrete_arg_ty,
                    self.getAstNodeSpan(arg_id),
                    &subst,
                    true,
                );
            } else {
                _ = try self.checkExpr(arg_id, param_ty);
            }
        }

        // Pass 2: Check contextual variants and closures against instantiated parameter types:
        for (args, 0..) |arg_id, i| {
            const arg_node = self.ast_arena.getNode(arg_id);
            if (arg_node.tag != .contextual_variant and arg_node.tag != .closure_expr) continue;
            const param_idx: usize = i + param_offset;
            const is_comptime_param = param_idx < 64 and
                (comptime_param_mask & (@as(u64, 1) << @intCast(param_idx))) != 0;
            const prev_pure = self.pure_comptime_depth;
            const prev_bound = self.comptime_boundary_scope_depth;
            if (is_comptime_param) {
                if (prev_pure == 0) {
                    self.comptime_boundary_scope_depth = if (self.current_scope.isNone())
                        0
                    else
                        self.sym_table.scope_arena.getScope(self.current_scope).depth;
                }
                self.pure_comptime_depth = prev_pure + 1;
            }
            defer if (is_comptime_param) {
                self.pure_comptime_depth = prev_pure;
                self.comptime_boundary_scope_depth = prev_bound;
            };

            const inst_param_ty = try subst.apply(self.pool, sig.getParamType(param_idx));
            _ = try self.checkExpr(arg_id, inst_param_ty);
        }

        // Record concrete instantiation tuple in `self.call_instantiations`:
        var inst_tys: std.ArrayListUnmanaged(TypeId) = .empty;
        defer inst_tys.deinit(self.allocator);
        if (declared_tp_count > 0) {
            for (declared_type_params.items) |tp_id| {
                try inst_tys.append(self.allocator, try subst.apply(self.pool, tp_id));
            }
        } else if (explicit_type_args.len > 0) {
            try inst_tys.appendSlice(self.allocator, resolved_explicit_tys);
        }
        for (subst.inline_entries[0..subst.inline_len]) |entry| {
            const var_tag = self.pool.getTag(entry.var_ty);
            if (var_tag == .bind_once_group_var or var_tag == .bind_many_any_var) {
                try inst_tys.append(self.allocator, entry.concrete_ty);
            }
        }
        for (subst.overflow_entries.items) |entry| {
            const var_tag = self.pool.getTag(entry.var_ty);
            if (var_tag == .bind_once_group_var or var_tag == .bind_many_any_var) {
                try inst_tys.append(self.allocator, entry.concrete_ty);
            }
        }
        if (inst_tys.items.len > 0) {
            try self.recordCallInstantiation(call_id, inst_tys.items);
        }

        return subst.apply(self.pool, sig.ret_ty);
    }

    /// Recursively unifies `param_ty` (which may be or contain `.bind_once_group_var`, `.bind_many_any_var`, or `.type_param`)
    /// against `arg_ty`, updating `subst` and optionally emitting `E0401`/`E0402`/`E0404`.
    fn unifyParamTypeWithArg(
        self: *TypeChecker,
        param_ty: TypeId,
        arg_ty: TypeId,
        arg_span: Span,
        subst: *SubstitutionMap,
        is_emitting_diags: bool,
    ) anyerror!bool {
        if (param_ty.isError() or arg_ty.isError()) return true;
        if (param_ty == arg_ty) return true;
        if (self.recursion_depth >= MAX_TYPE_DEPTH) return true;
        self.recursion_depth += 1;
        defer self.recursion_depth -= 1;

        const p_node = self.pool.getNode(param_ty);
        const a_node = self.pool.getNode(arg_ty);

        if (p_node.tag == .bind_once_group_var or
            p_node.tag == .bind_many_any_var or
            p_node.tag == .type_param)
        {
            const concrete_arg = self.materializeUntypedType(arg_ty);
            const group_ty = TypeId.fromInt(p_node.lhs);
            var sat = checkGroupSatisfaction(self.pool, concrete_arg, group_ty);
            if (sat == .rejected and self.pool.getTag(group_ty) == .trait_ty) {
                if (try self.hasTraitImplementation(concrete_arg, group_ty, 0)) {
                    sat = .matched_exact;
                }
            }
            if (sat == .rejected or sat == .rejected_distinct_without_tilde) {
                if (is_emitting_diags) {
                    try self.emitGroupConstraintError(
                        arg_span,
                        concrete_arg,
                        group_ty,
                        sat == .rejected_distinct_without_tilde,
                    );
                }
                return false;
            }

            if (p_node.tag == .bind_once_group_var or p_node.tag == .type_param) {
                if (subst.lookup(param_ty)) |bound_ty| {
                    if (bound_ty != concrete_arg) {
                        if (is_emitting_diags) {
                            try self.emitBindOnceConflict(
                                arg_span,
                                group_ty,
                                bound_ty,
                                concrete_arg,
                            );
                        }
                        return false;
                    }
                } else {
                    try subst.put(self.allocator, param_ty, concrete_arg, arg_span);
                }
            } else {
                // `bind_many_any_var`: each parameter ordinal binds independently:
                try subst.put(self.allocator, param_ty, concrete_arg, arg_span);
            }
            return true;
        }

        switch (p_node.tag) {
            .ref_ty => {
                if (a_node.tag == .ref_ty or a_node.tag == .mut_ref_ty) {
                    return self.unifyParamTypeWithArg(
                        TypeId.fromInt(p_node.lhs),
                        TypeId.fromInt(a_node.lhs),
                        arg_span,
                        subst,
                        is_emitting_diags,
                    );
                }
            },
            .mut_ref_ty => {
                if (a_node.tag == .mut_ref_ty) {
                    return self.unifyParamTypeWithArg(
                        TypeId.fromInt(p_node.lhs),
                        TypeId.fromInt(a_node.lhs),
                        arg_span,
                        subst,
                        is_emitting_diags,
                    );
                }
            },
            .slice_ty => {
                if (a_node.tag == .slice_ty) {
                    return self.unifyParamTypeWithArg(
                        TypeId.fromInt(p_node.lhs),
                        TypeId.fromInt(a_node.lhs),
                        arg_span,
                        subst,
                        is_emitting_diags,
                    );
                }
                if (a_node.tag == .ref_ty or a_node.tag == .mut_ref_ty) {
                    const inner_a = TypeId.fromInt(a_node.lhs);
                    const inner_a_node = self.pool.getNode(inner_a);
                    if (inner_a_node.tag == .slice_ty or inner_a_node.tag == .array_ty) {
                        return self.unifyParamTypeWithArg(
                            TypeId.fromInt(p_node.lhs),
                            TypeId.fromInt(inner_a_node.lhs),
                            arg_span,
                            subst,
                            is_emitting_diags,
                        );
                    }
                }
            },
            .soa_slice_ty => {
                if (a_node.tag == .soa_slice_ty) {
                    return self.unifyParamTypeWithArg(
                        TypeId.fromInt(p_node.lhs),
                        TypeId.fromInt(a_node.lhs),
                        arg_span,
                        subst,
                        is_emitting_diags,
                    );
                }
                if (a_node.tag == .ref_ty or a_node.tag == .mut_ref_ty) {
                    const inner_a = TypeId.fromInt(a_node.lhs);
                    const inner_a_node = self.pool.getNode(inner_a);
                    if (inner_a_node.tag == .soa_slice_ty or inner_a_node.tag == .soa_array_ty) {
                        return self.unifyParamTypeWithArg(
                            TypeId.fromInt(p_node.lhs),
                            TypeId.fromInt(inner_a_node.lhs),
                            arg_span,
                            subst,
                            is_emitting_diags,
                        );
                    }
                }
            },
            .array_ty, .soa_array_ty => {
                if (a_node.tag == p_node.tag) {
                    if (a_node.rhs == p_node.rhs) {
                        return self.unifyParamTypeWithArg(
                            TypeId.fromInt(p_node.lhs),
                            TypeId.fromInt(a_node.lhs),
                            arg_span,
                            subst,
                            is_emitting_diags,
                        );
                    }
                    if ((p_node.rhs & SYMBOLIC_ARRAY_LEN_FLAG) != 0 and
                        (a_node.rhs & SYMBOLIC_ARRAY_LEN_FLAG) == 0)
                    {
                        const const_sym = SymbolId.fromInt(p_node.rhs & ~SYMBOLIC_ARRAY_LEN_FLAG);
                        const len_key = try self.pool.internSymbolicArray(.unit_ty, const_sym, false);
                        const concrete_len_ty = try self.pool.internArray(.unit_ty, a_node.rhs, false);
                        if (subst.lookup(len_key)) |bound_len_ty| {
                            if (bound_len_ty != concrete_len_ty) {
                                if (is_emitting_diags) {
                                    const inst_param = try subst.apply(self.pool, param_ty);
                                    try self.emitTypeMismatch(
                                        arg_span,
                                        inst_param,
                                        self.materializeUntypedType(arg_ty),
                                    );
                                }
                                return false;
                            }
                        } else {
                            try subst.put(self.allocator, len_key, concrete_len_ty, arg_span);
                        }
                        return self.unifyParamTypeWithArg(
                            TypeId.fromInt(p_node.lhs),
                            TypeId.fromInt(a_node.lhs),
                            arg_span,
                            subst,
                            is_emitting_diags,
                        );
                    }
                }
            },
            .optional_ty => {
                if (a_node.tag == .optional_ty) {
                    return self.unifyParamTypeWithArg(
                        TypeId.fromInt(p_node.lhs),
                        TypeId.fromInt(a_node.lhs),
                        arg_span,
                        subst,
                        is_emitting_diags,
                    );
                }
            },
            .result_ty => {
                if (a_node.tag == .result_ty) {
                    const is_ok_match = try self.unifyParamTypeWithArg(
                        TypeId.fromInt(p_node.lhs),
                        TypeId.fromInt(a_node.lhs),
                        arg_span,
                        subst,
                        is_emitting_diags,
                    );
                    const is_err_match = try self.unifyParamTypeWithArg(
                        TypeId.fromInt(p_node.rhs),
                        TypeId.fromInt(a_node.rhs),
                        arg_span,
                        subst,
                        is_emitting_diags,
                    );
                    return is_ok_match and is_err_match;
                }
            },
            .tuple_ty => {
                if (a_node.tag == .tuple_ty and p_node.rhs == a_node.rhs) {
                    const p_elems = self.pool.getTupleElements(param_ty);
                    const a_elems = self.pool.getTupleElements(arg_ty);
                    var has_all_elems_matched = true;
                    for (p_elems, 0..) |raw_p, i| {
                        if (!(try self.unifyParamTypeWithArg(
                            TypeId.fromInt(raw_p),
                            TypeId.fromInt(a_elems[i]),
                            arg_span,
                            subst,
                            is_emitting_diags,
                        ))) {
                            has_all_elems_matched = false;
                        }
                    }
                    return has_all_elems_matched;
                }
            },
            else => {},
        }

        if (is_emitting_diags) {
            const inst_param = try subst.apply(self.pool, param_ty);
            try self.emitTypeMismatch(arg_span, inst_param, self.materializeUntypedType(arg_ty));
        }
        return false;
    }

    /// Synthesizes or checks an `if` / `else` expression (`if_expr`).
    fn synthOrCheckIfExpr(
        self: *TypeChecker,
        expr_id: NodeIndex,
        expected_ty: TypeId,
    ) anyerror!TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        const saved_scope = self.current_scope;
        const if_scope = try self.sym_table.scope_arena.allocScope(
            .block_scope,
            self.current_scope,
            .NONE,
            self.file_id,
            .{},
        );
        self.current_scope = if_scope;
        defer self.current_scope = saved_scope;

        if (ast_node.lhs.tag == .node) {
            try self.checkConditionOrLetHeader(
                NodeIndex.fromInt(ast_node.lhs.payload),
                self.ast_arena.getCstOrigin(expr_id),
            );
        }

        if (ast_node.rhs.tag == .node) {
            // `if` without `else` always evaluates to `()` (`.unit_ty`):
            _ = try self.checkBlock(NodeIndex.fromInt(ast_node.rhs.payload), .unit_ty, false);
            try symbol_resolver.checkUnusedBindingsInScope(self.sym_table, if_scope, self.interner, self.diagnostic_sink);
            return self.recordNodeType(expr_id, .unit_ty);
        }

        const branches = self.getNodeExtraSlice(expr_id, true);
        const then_id = if (branches.len >= 1) NodeIndex.fromInt(branches[0]) else .none;
        const else_id = if (branches.len >= 2) NodeIndex.fromInt(branches[1]) else .none;

        const then_ty = if (!expected_ty.isError())
            try self.checkBlock(then_id, expected_ty, false)
        else
            try self.checkBlock(then_id, .err_ty, false);

        try symbol_resolver.checkUnusedBindingsInScope(self.sym_table, if_scope, self.interner, self.diagnostic_sink);

        // `else` branch runs in the outer scope (not `if_scope` where `if let` bindings live):
        self.current_scope = saved_scope;
        const branch_expected = if (!expected_ty.isError())
            expected_ty
        else if (then_ty != .never_ty)
            self.materializeUntypedType(then_ty)
        else
            .err_ty;

        const else_ty = if (!else_id.isNone()) blk: {
            if (self.ast_arena.getNode(else_id).tag == .if_expr) {
                break :blk try self.synthOrCheckIfExpr(else_id, branch_expected);
            }
            break :blk try self.checkBlock(else_id, branch_expected, false);
        } else .unit_ty;

        const final_ty = if (then_ty == .never_ty)
            else_ty
        else if (else_ty == .never_ty)
            then_ty
        else
            self.materializeUntypedType(then_ty);

        return self.recordNodeType(expr_id, final_ty);
    }

    // ------ Maranget Match Exhaustiveness & Unreachable Arms ------

    /// Synthesizes or checks `match scrutinee { arms… }`, verifying exhaustiveness (`E0415`) and reachability (`W0401`).
    fn synthOrCheckMatchExpr(
        self: *TypeChecker,
        expr_id: NodeIndex,
        expected_ty: TypeId,
        is_comptime_match: bool,
    ) anyerror!TypeId {
        const ast_node = self.ast_arena.getNode(expr_id);
        const scrutinee_id = if (ast_node.lhs.tag == .node) NodeIndex.fromInt(ast_node.lhs.payload) else .none;
        const scrutinee_ty = if (is_comptime_match) blk: {
            const prev_comptime_depth = self.pure_comptime_depth;
            const prev_boundary_depth = self.comptime_boundary_scope_depth;
            if (prev_comptime_depth == 0) {
                self.comptime_boundary_scope_depth = if (self.current_scope.isNone())
                    0
                else
                    self.sym_table.scope_arena.getScope(self.current_scope).depth;
            }
            self.pure_comptime_depth += 1;
            defer {
                self.pure_comptime_depth = prev_comptime_depth;
                self.comptime_boundary_scope_depth = prev_boundary_depth;
            }
            break :blk self.materializeUntypedType(try self.synthExpr(scrutinee_id));
        } else self.materializeUntypedType(try self.synthExpr(scrutinee_id));

        const arm_entries = self.getNodeExtraSlice(expr_id, true);
        const arm_count = arm_entries.len / 2;

        // Detect guarded arms (`pat if cond => body`) from CST `.match_arm` subtrees:
        const arm_guards = try self.allocator.alloc(NodeIndex, arm_count);
        defer if (arm_guards.len > 0) self.allocator.free(arm_guards);
        @memset(arm_guards, .none);
        const match_cst = self.ast_arena.getCstOrigin(expr_id);
        if (!match_cst.isNone() and match_cst.asInt() < self.cst_arena.countNodes()) {
            const start_idx: usize = match_cst.asInt();
            const rec = self.cst_arena.getNode(match_cst);
            const end_idx: usize = @min(
                start_idx + @max(@as(usize, rec.subtree_size), 1),
                self.cst_arena.countNodes(),
            );
            var arm_ord: usize = 0;
            var cur = start_idx + 1;
            while (cur < end_idx and arm_ord < arm_guards.len) {
                const sub = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                if (sub.kind == .match_expr and sub.subtree_size > 1) {
                    cur = @min(cur + @as(usize, sub.subtree_size), end_idx);
                    continue;
                }
                if (sub.kind == .match_arm) {
                    const arm_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), end_idx);
                    var if_pos: ?usize = null;
                    var arrow_pos: ?usize = null;
                    var a_cur = cur + 1;
                    while (a_cur < arm_end) : (a_cur += 1) {
                        const leaf = self.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(a_cur)));
                        if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                            leaf.token.asInt() < self.token_buffer.countTokens())
                        {
                            const tok_kind = self.token_buffer.getToken(leaf.token).kind;
                            if (tok_kind == .kw_if and if_pos == null and arrow_pos == null) {
                                if_pos = a_cur;
                            } else if (tok_kind == .fat_arrow and arrow_pos == null) {
                                arrow_pos = a_cur;
                                break;
                            }
                        }
                    }
                    if (if_pos) |ip| {
                        const search_end = arrow_pos orelse arm_end;
                        arm_guards[arm_ord] = self.findFirstAstInCstRange(ip + 1, search_end);
                    }
                    arm_ord += 1;
                    cur = arm_end;
                    continue;
                }
                cur += 1;
            }
        }

        // Exhaustiveness state across `bool`, `T?`, `Result[T, E]`, nominal `enum`, and integer/refinement intervals:
        const unwrapped_scr = self.unwrapRefType(scrutinee_ty);
        const scr_node = self.pool.getNode(unwrapped_scr);
        var has_wildcard_cover = false;
        var has_seen_pattern_hole = false;
        var bool_covered_mask: u8 = 0; // bit 0 = false, bit 1 = true
        var variant_covered_mask: u64 = 0;
        const total_variants: usize = switch (scr_node.tag) {
            .optional_ty, .result_ty => 2,
            .enum_ty => blk: {
                const e_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(scr_node.rhs)).*;
                if (e_sym.target_scope.isNone()) break :blk 0;
                var variant_count: usize = 0;
                for (self.sym_table.getScopeMembers(e_sym.target_scope)) |member_idx| {
                    if (self.sym_table.getSymbol(member_idx).kind == .enum_variant_sym) {
                        variant_count += 1;
                    }
                }
                break :blk variant_count;
            },
            else => 0,
        };

        var uncovered_intervals: std.ArrayListUnmanaged(Interval128) = .empty;
        defer uncovered_intervals.deinit(self.allocator);
        var has_int_intervals = false;
        if (self.pool.getRefinementBounds(unwrapped_scr)) |ref_b| {
            try uncovered_intervals.append(self.allocator, .{ .min_val = ref_b.min_val, .max_val = ref_b.max_val });
            has_int_intervals = true;
        } else if (unwrapped_scr == .u128_ty) {
            try uncovered_intervals.append(
                self.allocator,
                .{ .min_val = std.math.minInt(i128), .max_val = std.math.maxInt(i128) },
            );
            has_int_intervals = true;
        } else if (getPrimitiveIntBounds(unwrapped_scr)) |prim_b| {
            try uncovered_intervals.append(self.allocator, .{ .min_val = prim_b.min_val, .max_val = prim_b.max_val });
            has_int_intervals = true;
        }

        var unified_body_ty: TypeId = expected_ty;
        var arm_idx: usize = 0;
        while (arm_idx < arm_count) : (arm_idx += 1) {
            const pat_id = NodeIndex.fromInt(arm_entries[arm_idx * 2]);
            const body_id = NodeIndex.fromInt(arm_entries[arm_idx * 2 + 1]);
            const guard_id = if (arm_idx < arm_guards.len) arm_guards[arm_idx] else .none;
            const is_unguarded = guard_id.isNone();

            // [1] Check arm usefulness & update coverage (`W0401`, `DR-04` Section 1.5 / `DR-07` Section 2.5):
            const is_already_fully_covered = has_wildcard_cover or
                (unwrapped_scr == .bool_ty and bool_covered_mask == 0b11) or
                (total_variants > 0 and total_variants <= 64 and
                    variant_covered_mask == (@as(u64, 1) << @intCast(total_variants)) - 1) or
                (has_int_intervals and uncovered_intervals.items.len == 0);

            const has_arm_added_coverage = try self.updateMatchArmCoverage(
                pat_id,
                unwrapped_scr,
                is_unguarded,
                &has_wildcard_cover,
                &has_seen_pattern_hole,
                &bool_covered_mask,
                &variant_covered_mask,
                &uncovered_intervals,
                has_int_intervals,
            );

            if (!unwrapped_scr.isError() and (is_already_fully_covered or (!has_arm_added_coverage and is_unguarded))) {
                try self.emitDiagnosticSimple(
                    .w0401_unreachable_pattern_arm,
                    self.getAstNodeSpan(pat_id),
                    "unreachable `match` arm; all values matched by this pattern are already covered",
                    "remove this redundant pattern arm",
                );
            }

            // [2] Type-check arm pattern, optional `if` guard, and body inside `.match_arm_scope`:
            const saved_scope = self.current_scope;
            const arm_scope = try self.sym_table.scope_arena.allocScope(
                .match_arm_scope,
                self.current_scope,
                .NONE,
                self.file_id,
                .{},
            );
            self.current_scope = arm_scope;
            defer self.current_scope = saved_scope;

            try self.bindPattern(pat_id, scrutinee_ty, false);
            if (!guard_id.isNone()) {
                _ = try self.checkExpr(guard_id, .bool_ty);
            }

            const body_ty = if (!unified_body_ty.isError())
                try self.checkExpr(body_id, unified_body_ty)
            else
                try self.synthExpr(body_id);

            if (unified_body_ty.isError() and !body_ty.isError() and body_ty != .never_ty) {
                unified_body_ty = self.materializeUntypedType(body_ty);
            }
            try symbol_resolver.checkUnusedBindingsInScope(self.sym_table, arm_scope, self.interner, self.diagnostic_sink);
        }

        // [3] Verify exhaustiveness (`E0415`, `DR-04` Section 1.5 / `DR-07` Section 2.5):
        if (!unwrapped_scr.isError() and !has_wildcard_cover and !has_seen_pattern_hole) {
            if (unwrapped_scr == .bool_ty and bool_covered_mask != 0b11) {
                const missing_lit = if ((bool_covered_mask & 1) == 0) "`false`" else "`true`";
                var msg_buf: [128]u8 = undefined;
                const msg = std.fmt.bufPrint(
                    &msg_buf,
                    "non-exhaustive `match` on `bool`; missing pattern {s}",
                    .{missing_lit},
                ) catch "non-exhaustive `match` on `bool`";
                try self.emitDiagnosticSimple(
                    .e0415_non_exhaustive_match,
                    self.getAstNodeSpan(expr_id),
                    msg,
                    "add missing boolean arm or `_` wildcard",
                );
            } else if (total_variants > 0 and total_variants <= 64) {
                const full_mask: u64 = (@as(u64, 1) << @intCast(total_variants)) - 1;
                if ((variant_covered_mask & full_mask) != full_mask) {
                    const missing_name = self.findFirstUncoveredVariantName(
                        unwrapped_scr,
                        variant_covered_mask,
                    );
                    var msg_buf: [160]u8 = undefined;
                    const msg = std.fmt.bufPrint(
                        &msg_buf,
                        "non-exhaustive `match`; variant `.{s}` is not covered",
                        .{missing_name},
                    ) catch "non-exhaustive `match`; not all variants are covered";
                    try self.emitDiagnosticSimple(
                        .e0415_non_exhaustive_match,
                        self.getAstNodeSpan(expr_id),
                        msg,
                        "handle all enum/Result/Option variants or add a `_` wildcard arm",
                    );
                }
            } else if (has_int_intervals and uncovered_intervals.items.len > 0) {
                const first_gap = uncovered_intervals.items[0];
                var msg_buf: [192]u8 = undefined;
                const msg = if (unwrapped_scr == .u128_ty) blk_u128_msg: {
                    const sign_bias: u128 = @as(u128, 1) << 127;
                    const gap_min_u: u128 = @as(u128, @bitCast(first_gap.min_val)) ^ sign_bias;
                    const gap_max_u: u128 = @as(u128, @bitCast(first_gap.max_val)) ^ sign_bias;
                    break :blk_u128_msg std.fmt.bufPrint(
                        &msg_buf,
                        "non-exhaustive `match`; integer range `{d}..={d}` is not covered",
                        .{ gap_min_u, gap_max_u },
                    ) catch "non-exhaustive `match` over integer range";
                } else std.fmt.bufPrint(
                    &msg_buf,
                    "non-exhaustive `match`; integer range `{d}..={d}` is not covered",
                    .{ first_gap.min_val, first_gap.max_val },
                ) catch "non-exhaustive `match` over integer range";
                try self.emitDiagnosticSimple(
                    .e0415_non_exhaustive_match,
                    self.getAstNodeSpan(expr_id),
                    msg,
                    "cover all remaining integer intervals or add a `_` wildcard arm",
                );
            }
        }

        const result_ty = if (unified_body_ty.isError()) .unit_ty else unified_body_ty;
        return self.recordNodeType(expr_id, result_ty);
    }

    /// Updates Maranget exhaustiveness coverage state for `pat_id`, returning `true` if new values were covered.
    fn updateMatchArmCoverage(
        self: *TypeChecker,
        pat_id: NodeIndex,
        scrutinee_ty: TypeId,
        is_unguarded: bool,
        has_wildcard_cover: *bool,
        has_seen_pattern_hole: *bool,
        bool_covered_mask: *u8,
        variant_covered_mask: *u64,
        uncovered_intervals: *std.ArrayListUnmanaged(Interval128),
        has_int_intervals: bool,
    ) anyerror!bool {
        if (pat_id.isNone() or pat_id.asInt() >= self.ast_arena.countNodes()) return true;
        if (self.recursion_depth >= MAX_TYPE_DEPTH) return true;
        self.recursion_depth += 1;
        defer self.recursion_depth -= 1;

        const pat_node = self.ast_arena.getNode(pat_id);

        switch (pat_node.tag) {
            .pattern_hole => {
                // Recovery hole suppresses `E0415` without marking subsequent arms unreachable (`W0401`):
                has_seen_pattern_hole.* = true;
                return true;
            },
            .wildcard_pat, .bind_pat => {
                const is_already_covered = has_wildcard_cover.*;
                if (is_unguarded) {
                    has_wildcard_cover.* = true;
                    uncovered_intervals.clearRetainingCapacity();
                }
                return !is_already_covered;
            },
            .tuple_pat, .struct_pat => {
                if (pat_node.tag == .tuple_pat) {
                    const sub_pats = self.getNodeExtraSlice(pat_id, false);
                    if (sub_pats.len == 1 and !hasShallowCommaInTupleCst(
                        self.cst_arena,
                        self.token_buffer,
                        self.ast_arena.getCstOrigin(pat_id),
                    )) {
                        return self.updateMatchArmCoverage(
                            NodeIndex.fromInt(sub_pats[0]),
                            scrutinee_ty,
                            is_unguarded,
                            has_wildcard_cover,
                            has_seen_pattern_hole,
                            bool_covered_mask,
                            variant_covered_mask,
                            uncovered_intervals,
                            has_int_intervals,
                        );
                    }
                }
                if (!self.isPatternIrrefutable(pat_id, 0)) return true;
                const is_already_covered = has_wildcard_cover.*;
                if (is_unguarded) {
                    has_wildcard_cover.* = true;
                    uncovered_intervals.clearRetainingCapacity();
                }
                return !is_already_covered;
            },
            .or_pat => {
                const is_lhs_useful = if (pat_node.lhs.tag == .node)
                    try self.updateMatchArmCoverage(
                        NodeIndex.fromInt(pat_node.lhs.payload),
                        scrutinee_ty,
                        is_unguarded,
                        has_wildcard_cover,
                        has_seen_pattern_hole,
                        bool_covered_mask,
                        variant_covered_mask,
                        uncovered_intervals,
                        has_int_intervals,
                    )
                else
                    false;
                const is_rhs_useful = if (pat_node.rhs.tag == .node)
                    try self.updateMatchArmCoverage(
                        NodeIndex.fromInt(pat_node.rhs.payload),
                        scrutinee_ty,
                        is_unguarded,
                        has_wildcard_cover,
                        has_seen_pattern_hole,
                        bool_covered_mask,
                        variant_covered_mask,
                        uncovered_intervals,
                        has_int_intervals,
                    )
                else
                    false;
                return is_lhs_useful or is_rhs_useful;
            },
            .lit_pat => {
                if (scrutinee_ty == .bool_ty and !pat_node.main_token.isNone()) {
                    const kind = self.token_buffer.getToken(pat_node.main_token).kind;
                    const bit: u8 = if (kind == .kw_false) 1 else if (kind == .kw_true) 2 else 0;
                    const is_new = (bool_covered_mask.* & bit) == 0;
                    if (is_unguarded) bool_covered_mask.* |= bit;
                    return is_new;
                }
                if (has_int_intervals) {
                    const arm_range_opt = if (scrutinee_ty == .u128_ty)
                        self.extractBiasedU128PatternRangeBounds(pat_id)
                    else
                        self.extractPatternRangeBounds(pat_id);
                    if (arm_range_opt) |arm_range| {
                        // Check if `arm_range` intersects any remaining uncovered interval:
                        var has_intersection = false;
                        if (arm_range.min_val <= arm_range.max_val) {
                            for (uncovered_intervals.items) |iv| {
                                if (arm_range.max_val >= iv.min_val and arm_range.min_val <= iv.max_val) {
                                    has_intersection = true;
                                    break;
                                }
                            }
                        }
                        if (is_unguarded and has_intersection) {
                            try subtractIntervalFromUncoveredList(
                                self.allocator,
                                uncovered_intervals,
                                arm_range,
                            );
                        }
                        return has_intersection;
                    }
                }
                return true;
            },
            .variant_pat => {
                const sub_pats = self.getNodeExtraSlice(pat_id, false);
                for (sub_pats) |raw_sub| {
                    if (!self.isPatternIrrefutable(NodeIndex.fromInt(raw_sub), 0)) return true;
                }
                const var_name = self.extractVariantPatName(pat_id);
                const scr_node = self.pool.getNode(scrutinee_ty);
                var var_ordinal: ?u6 = null;
                switch (scr_node.tag) {
                    .optional_ty => {
                        if (std.mem.eql(u8, var_name, "None")) var_ordinal = 0;
                        if (std.mem.eql(u8, var_name, "Some")) var_ordinal = 1;
                    },
                    .result_ty => {
                        if (std.mem.eql(u8, var_name, "Ok")) var_ordinal = 0;
                        if (std.mem.eql(u8, var_name, "Err")) var_ordinal = 1;
                    },
                    .enum_ty => {
                        const e_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(scr_node.rhs)).*;
                        if (!e_sym.target_scope.isNone()) {
                            if (self.interner.lookup(var_name)) |v_sym_id| {
                                const v_idx = self.sym_table.lookupInScopeDirect(
                                    e_sym.target_scope,
                                    v_sym_id,
                                    NamespaceMask.VALUE_ONLY,
                                );
                                if (!v_idx.isNone()) {
                                    self.sym_table.markSymbolUsed(v_idx);
                                    const ord = self.sym_table.getSymbol(v_idx).member_ordinal;
                                    if (ord < 64) var_ordinal = @intCast(ord);
                                }
                            }
                        }
                    },
                    else => {},
                }
                if (var_ordinal) |ord| {
                    const bit = @as(u64, 1) << ord;
                    const is_new = (variant_covered_mask.* & bit) == 0;
                    if (is_unguarded) variant_covered_mask.* |= bit;
                    return is_new;
                }
                return true;
            },
            else => return true,
        }
    }

    /// Returns `true` if `pat_id` is irrefutable (matches all values of its type without refutable sub-patterns).
    fn isPatternIrrefutable(self: *const TypeChecker, pat_id: NodeIndex, depth: u32) bool {
        if (depth >= MAX_TYPE_DEPTH) return true;
        if (pat_id.isNone() or pat_id.asInt() >= self.ast_arena.countNodes()) return true;
        const pat_node = self.ast_arena.getNode(pat_id);
        return switch (pat_node.tag) {
            .wildcard_pat, .bind_pat, .pattern_hole => true,
            .tuple_pat => blk: {
                for (self.getNodeExtraSlice(pat_id, false)) |raw_sub| {
                    if (!self.isPatternIrrefutable(NodeIndex.fromInt(raw_sub), depth + 1)) break :blk false;
                }
                break :blk true;
            },
            .struct_pat => blk: {
                for (self.getNodeExtraSlice(pat_id, false)) |raw_sub| {
                    if (!self.isPatternIrrefutable(NodeIndex.fromInt(raw_sub), depth + 1)) break :blk false;
                }
                break :blk true;
            },
            .or_pat => blk: {
                const is_lhs_irrefutable = pat_node.lhs.tag == .node and
                    self.isPatternIrrefutable(NodeIndex.fromInt(pat_node.lhs.payload), depth + 1);
                const is_rhs_irrefutable = pat_node.rhs.tag == .node and
                    self.isPatternIrrefutable(NodeIndex.fromInt(pat_node.rhs.payload), depth + 1);
                break :blk is_lhs_irrefutable or is_rhs_irrefutable;
            },
            else => false,
        };
    }

    /// Returns the name of the first uncovered variant in `scrutinee_ty` for `E0415`.
    fn findFirstUncoveredVariantName(
        self: *const TypeChecker,
        scrutinee_ty: TypeId,
        covered_mask: u64,
    ) []const u8 {
        const scr_node = self.pool.getNode(scrutinee_ty);
        switch (scr_node.tag) {
            .optional_ty => return if ((covered_mask & 1) == 0) "None" else "Some",
            .result_ty => return if ((covered_mask & 1) == 0) "Ok" else "Err",
            .enum_ty => {
                const e_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(scr_node.rhs)).*;
                if (!e_sym.target_scope.isNone()) {
                    for (self.sym_table.getScopeMembers(e_sym.target_scope)) |member_idx| {
                        const member_sym = self.sym_table.getSymbol(member_idx).*;
                        if (member_sym.kind != .enum_variant_sym) continue;
                        if (member_sym.member_ordinal < 64 and
                            (covered_mask & (@as(u64, 1) << @intCast(member_sym.member_ordinal))) == 0)
                        {
                            return member_sym.name_text;
                        }
                    }
                }
                return "_";
            },
            else => return "_",
        }
    }

    // ----------- Type Compatibility & Coercion Checking -----------

    /// Verifies whether `actual_ty` is assignable to `expected_ty` at `expr_id`, emitting diagnostics on failure.
    fn checkTypeCompatibility(
        self: *TypeChecker,
        expr_id: NodeIndex,
        actual_ty: TypeId,
        expected_ty: TypeId,
    ) !bool {
        if (actual_ty.isError() or expected_ty.isError()) return true;
        if (actual_ty == .never_ty) return true;
        if (actual_ty == expected_ty) return true;

        const act_node = self.pool.getNode(actual_ty);
        const exp_node = self.pool.getNode(expected_ty);

        // [1] Constrained Type Group, `.tilde_approx`, or generic parameter satisfaction (`DR-04` Section 1.4):
        if (exp_node.tag == .bind_once_group_var or
            exp_node.tag == .bind_many_any_var or
            exp_node.tag == .type_param or
            exp_node.tag == .tilde_approx or
            exp_node.tag == .user_group or
            exp_node.tag == .builtin_group)
        {
            const grp_ty = if (exp_node.tag == .bind_once_group_var or
                exp_node.tag == .bind_many_any_var or
                exp_node.tag == .type_param)
                TypeId.fromInt(exp_node.lhs)
            else
                expected_ty;
            var sat = checkGroupSatisfaction(self.pool, actual_ty, grp_ty);
            if (sat == .rejected and self.pool.getTag(grp_ty) == .trait_ty) {
                if (try self.hasTraitImplementation(self.materializeUntypedType(actual_ty), grp_ty, 0)) {
                    sat = .matched_exact;
                }
            }
            if (sat == .matched_exact or sat == .matched_via_tilde) {
                return true;
            }
            if (sat == .rejected_distinct_without_tilde) {
                try self.emitGroupConstraintError(
                    self.getAstNodeSpan(expr_id),
                    self.materializeUntypedType(actual_ty),
                    grp_ty,
                    true,
                );
                return false;
            }
        }

        // [2] `distinct` newtype isolation (`E0405`, `DR-04` Section 1.4):
        const is_actual_distinct = act_node.tag == .distinct_ty;
        const is_expected_distinct = exp_node.tag == .distinct_ty;
        if (is_actual_distinct or is_expected_distinct) {
            try self.emitDistinctMixingError(
                self.getAstNodeSpan(expr_id),
                expected_ty,
                self.materializeUntypedType(actual_ty),
            );
            return false;
        }

        // [3] Zero-cost `T is low..=high` range refinement (`DR-04` Section 1.5):
        // - Widening `Refined -> Base` or `Refined[A..=B] -> Refined[C..=D]` (where `A >= C` and `B <= D`) is implicit:
        if (act_node.tag == .refined_ty) {
            if (self.pool.unwrapRefinementBase(actual_ty) == expected_ty) {
                return true;
            }
            if (exp_node.tag == .refined_ty and
                self.pool.unwrapRefinementBase(actual_ty) == self.pool.unwrapRefinementBase(expected_ty))
            {
                if (self.pool.getRefinementBounds(actual_ty)) |act_b| {
                    if (self.pool.getRefinementBounds(expected_ty)) |exp_b| {
                        if (act_b.min_val >= exp_b.min_val and act_b.max_val <= exp_b.max_val) {
                            return true;
                        }
                    }
                }
            }
        }
        if (self.pool.getRefinementBounds(expected_ty)) |ref_bounds| {
            try self.emitRangeRefinementError(
                self.getAstNodeSpan(expr_id),
                expected_ty,
                ref_bounds.min_val,
                ref_bounds.min_val,
                ref_bounds.max_val,
            );
            return false;
        }

        // [4] Untyped literal materialization (`untyped_int_ty` / `untyped_float_ty`):
        if (actual_ty == .untyped_int_ty and
            (expected_ty.isIntegerPrimitive() or self.isIntegerBoundedVar(expected_ty)))
        {
            return true;
        }
        if (actual_ty == .untyped_float_ty and expected_ty.isFloatPrimitive()) {
            return true;
        }

        // [5] Reference, symbolic-array, & array-to-slice coercions (`&mut T -> &T`, `&[T; N] -> [T]`):
        if (act_node.tag == .mut_ref_ty and exp_node.tag == .ref_ty and act_node.lhs == exp_node.lhs) {
            return true;
        }
        if ((act_node.tag == .array_ty or act_node.tag == .soa_array_ty) and
            act_node.tag == exp_node.tag and act_node.lhs == exp_node.lhs and
            act_node.rhs == exp_node.rhs)
        {
            return true;
        }
        if (exp_node.tag == .slice_ty) {
            if (act_node.tag == .ref_ty or act_node.tag == .mut_ref_ty) {
                const inner_act = self.pool.getNode(TypeId.fromInt(act_node.lhs));
                if ((inner_act.tag == .array_ty or inner_act.tag == .slice_ty) and
                    inner_act.lhs == exp_node.lhs)
                {
                    return true;
                }
            }
        }
        if (exp_node.tag == .soa_slice_ty) {
            if (act_node.tag == .ref_ty or act_node.tag == .mut_ref_ty) {
                const inner_act = self.pool.getNode(TypeId.fromInt(act_node.lhs));
                if ((inner_act.tag == .soa_array_ty or inner_act.tag == .soa_slice_ty) and
                    inner_act.lhs == exp_node.lhs)
                {
                    return true;
                }
            }
        }
        if ((exp_node.tag == .ref_ty and (act_node.tag == .ref_ty or act_node.tag == .mut_ref_ty)) or
            (exp_node.tag == .mut_ref_ty and act_node.tag == .mut_ref_ty))
        {
            const inner_exp = self.pool.getNode(TypeId.fromInt(exp_node.lhs));
            const inner_act = self.pool.getNode(TypeId.fromInt(act_node.lhs));
            if (inner_exp.tag == .slice_ty and inner_act.tag == .array_ty and inner_act.lhs == inner_exp.lhs) {
                return true;
            }
            if (inner_exp.tag == .soa_slice_ty and inner_act.tag == .soa_array_ty and inner_act.lhs == inner_exp.lhs) {
                return true;
            }
        }

        try self.emitTypeMismatch(
            self.getAstNodeSpan(expr_id),
            expected_ty,
            self.materializeUntypedType(actual_ty),
        );
        return false;
    }

    /// Materializes `.untyped_int_ty` to `.i32_ty` and `.untyped_float_ty` to `.f64_ty`.
    pub inline fn materializeUntypedType(self: *const TypeChecker, ty: TypeId) TypeId {
        _ = self;
        if (ty == .untyped_int_ty) return .i32_ty;
        if (ty == .untyped_float_ty) return .f64_ty;
        return ty;
    }

    /// Unwraps one or more `.ref_ty` / `.mut_ref_ty` layers for auto-dereferencing member/method access.
    fn unwrapRefType(self: *const TypeChecker, ty: TypeId) TypeId {
        var cur = ty;
        var guard: u32 = 0;
        while (guard < 16) : (guard += 1) {
            const node = self.pool.getNode(cur);
            if (node.tag == .ref_ty or node.tag == .mut_ref_ty) {
                cur = TypeId.fromInt(node.lhs);
            } else {
                break;
            }
        }
        return cur;
    }

    /// Returns `true` if `ty` is a type variable whose constraining Type Group admits integer literals.
    fn isIntegerBoundedVar(self: *const TypeChecker, ty: TypeId) bool {
        const node = self.pool.getNode(ty);
        if (node.tag == .bind_once_group_var or
            node.tag == .bind_many_any_var or
            node.tag == .type_param)
        {
            const grp_ty = TypeId.fromInt(node.lhs);
            return checkGroupSatisfaction(self.pool, .untyped_int_ty, grp_ty) != .rejected;
        }
        return false;
    }

    /// Returns `true` if `expr_id` produces a `@must_use` value (`Result[T, E]`, `@must_use` nominal type, or `@must_use` fn).
    fn isMustUseTypeOrCall(self: *const TypeChecker, expr_id: NodeIndex, expr_ty: TypeId) bool {
        if (self.pool.getFlags(expr_ty).is_must_use) return true;
        if (expr_id.isNone() or expr_id.asInt() >= self.ast_arena.countNodes()) return false;
        const ast_node = self.ast_arena.getNode(expr_id);
        if ((ast_node.tag == .call_expr or ast_node.tag == .generic_call) and ast_node.lhs.tag == .node) {
            const callee_id = NodeIndex.fromInt(ast_node.lhs.payload);
            if (callee_id.asInt() < self.node_types.len) {
                const callee_ty = self.node_types[callee_id.asInt()];
                if (self.pool.getFlags(callee_ty).is_must_use) return true;
            }
        } else if (ast_node.tag == .method_call and ast_node.lhs.tag == .node) {
            const recv_id = NodeIndex.fromInt(ast_node.lhs.payload);
            if (recv_id.asInt() < self.node_types.len) {
                const recv_ty = self.unwrapRefType(self.node_types[recv_id.asInt()]);
                const recv_node = self.pool.getNode(recv_ty);
                if (recv_node.tag == .struct_ty or recv_node.tag == .enum_ty or
                    recv_node.tag == .union_ty or recv_node.tag == .trait_ty)
                {
                    const owner_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(recv_node.rhs)).*;
                    const raw_items = self.getNodeExtraSlice(expr_id, true);
                    if (!owner_sym.target_scope.isNone() and raw_items.len > 0) {
                        const member_tok = TokenIndex.fromInt(raw_items[0]);
                        const member_name = symbol_resolver.extractTokenSlice(
                            self.source,
                            self.token_buffer,
                            member_tok,
                        );
                        if (self.interner.lookup(member_name)) |m_sym_id| {
                            const m_idx = self.sym_table.lookupInScopeDirect(
                                owner_sym.target_scope,
                                m_sym_id,
                                NamespaceMask.VALUE_ONLY,
                            );
                            if (!m_idx.isNone() and self.sym_table.getSymbol(m_idx).flags.is_must_use) {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    // ------------------- Diagnostic Formatters --------------------

    /// Emits `E0401` (`type_mismatch`) with formatted expected and actual type names.
    fn emitTypeMismatch(
        self: *TypeChecker,
        span: Span,
        expected_ty: TypeId,
        actual_ty: TypeId,
    ) !void {
        if (self.diagnostic_sink == null) return;
        var exp_buf: [96]u8 = undefined;
        var act_buf: [96]u8 = undefined;
        const exp_str = self.pool.formatType(expected_ty, self.sym_table, &exp_buf);
        const act_str = self.pool.formatType(actual_ty, self.sym_table, &act_buf);

        var msg_buf: [220]u8 = undefined;
        const msg = std.fmt.bufPrint(
            &msg_buf,
            "mismatched types: expected `{s}`, found `{s}`",
            .{ exp_str, act_str },
        ) catch "mismatched types";

        var lbl_buf: [160]u8 = undefined;
        const lbl = std.fmt.bufPrint(
            &lbl_buf,
            "expected `{s}`, found `{s}`",
            .{ exp_str, act_str },
        ) catch "type mismatch here";

        try self.emitDiagnosticSimple(.e0401_type_mismatch, span, msg, lbl);
    }

    /// Emits `E0402` (`unsatisfied_trait_bound`) when a type fails a Constrained Type Group check.
    fn emitGroupConstraintError(
        self: *TypeChecker,
        span: Span,
        candidate_ty: TypeId,
        group_ty: TypeId,
        is_distinct_without_tilde: bool,
    ) !void {
        if (self.diagnostic_sink == null) return;
        var cand_buf: [96]u8 = undefined;
        var grp_buf: [96]u8 = undefined;
        const cand_str = self.pool.formatType(candidate_ty, self.sym_table, &cand_buf);
        const grp_str = self.pool.formatType(group_ty, self.sym_table, &grp_buf);

        var msg_buf: [240]u8 = undefined;
        const msg = if (is_distinct_without_tilde)
            std.fmt.bufPrint(
                &msg_buf,
                "`distinct` type `{s}` does not satisfy Type Group `{s}` without `~` underlying-type approximation",
                .{ cand_str, grp_str },
            ) catch "`distinct` type does not satisfy Type Group without `~`"
        else
            std.fmt.bufPrint(
                &msg_buf,
                "type `{s}` does not satisfy Constrained Type Group `{s}`",
                .{ cand_str, grp_str },
            ) catch "type does not satisfy Constrained Type Group";

        try self.emitDiagnosticSimple(
            .e0402_unsatisfied_trait_bound,
            span,
            msg,
            "unsatisfied Type Group constraint",
        );
    }

    /// Emits `E0404` (`bind_once_type_group_conflict`) when a bare Type Group binds to two different types.
    fn emitBindOnceConflict(
        self: *TypeChecker,
        span: Span,
        group_ty: TypeId,
        first_ty: TypeId,
        second_ty: TypeId,
    ) !void {
        if (self.diagnostic_sink == null) return;
        var grp_buf: [64]u8 = undefined;
        var first_buf: [64]u8 = undefined;
        var second_buf: [64]u8 = undefined;
        const grp_str = self.pool.formatType(group_ty, self.sym_table, &grp_buf);
        const first_str = self.pool.formatType(first_ty, self.sym_table, &first_buf);
        const second_str = self.pool.formatType(second_ty, self.sym_table, &second_buf);

        var msg_buf: [240]u8 = undefined;
        const msg = std.fmt.bufPrint(
            &msg_buf,
            "Bind-Once Type Group `{s}` bound to conflicting types `{s}` and `{s}` (use `any {s}` for independent parameters)",
            .{ grp_str, first_str, second_str, grp_str },
        ) catch "Bind-Once Type Group bound to conflicting concrete types";

        try self.emitDiagnosticSimple(
            .e0404_bind_once_group_conflict,
            span,
            msg,
            "expected same concrete type as previous Bind-Once parameter",
        );
    }

    /// Emits `E0405` (`distinct_type_mismatch`) when mixing a `distinct` newtype with its base type.
    fn emitDistinctMixingError(
        self: *TypeChecker,
        span: Span,
        lhs_ty: TypeId,
        rhs_ty: TypeId,
    ) !void {
        if (self.diagnostic_sink == null) return;
        var lhs_buf: [64]u8 = undefined;
        var rhs_buf: [64]u8 = undefined;
        const lhs_str = self.pool.formatType(lhs_ty, self.sym_table, &lhs_buf);
        const rhs_str = self.pool.formatType(rhs_ty, self.sym_table, &rhs_buf);

        var msg_buf: [220]u8 = undefined;
        const msg = std.fmt.bufPrint(
            &msg_buf,
            "cannot mix `distinct` type `{s}` with `{s}` without an explicit `as` cast",
            .{ lhs_str, rhs_str },
        ) catch "cannot mix `distinct` type with underlying type without explicit `as` cast";

        try self.emitDiagnosticSimple(
            .e0405_distinct_type_mixing,
            span,
            msg,
            "`distinct` newtypes do not implicitly convert to or from their underlying type",
        );
    }

    /// Emits `E0406` (`range_refinement_violation`) when a value violates a `T is low..=high` refinement.
    fn emitRangeRefinementError(
        self: *TypeChecker,
        span: Span,
        refined_ty: TypeId,
        actual_val: i128,
        min_val: i128,
        max_val: i128,
    ) !void {
        if (self.diagnostic_sink == null) return;
        var ty_buf: [64]u8 = undefined;
        const ty_str = self.pool.formatType(refined_ty, self.sym_table, &ty_buf);

        var msg_buf: [220]u8 = undefined;
        const msg = std.fmt.bufPrint(
            &msg_buf,
            "value `{d}` violates refinement type `{s}` (expected `{d}..={d}`)",
            .{ actual_val, ty_str, min_val, max_val },
        ) catch "value violates `is` range refinement bounds";

        try self.emitDiagnosticSimple(
            .e0406_range_refinement_violation,
            span,
            msg,
            "value outside refined range `low..=high`",
        );
    }

    /// Emits `E0413` (`unhandled_must_use_result`) when a `Result[T, E]` or `@must_use` value is discarded.
    fn emitUnhandledMustUseError(self: *TypeChecker, span: Span, expr_ty: TypeId) !void {
        if (self.diagnostic_sink == null) return;
        var ty_buf: [96]u8 = undefined;
        const ty_str = self.pool.formatType(expr_ty, self.sym_table, &ty_buf);

        var msg_buf: [220]u8 = undefined;
        const msg = std.fmt.bufPrint(
            &msg_buf,
            "unhandled `@must_use` or `Result` value of type `{s}`; propagate with `?` or handle with `catch`",
            .{ty_str},
        ) catch "unhandled `@must_use` or `Result` value";

        try self.emitDiagnosticSimple(
            .e0413_unhandled_must_use_or_result,
            span,
            msg,
            "unused `@must_use` / `Result` value must be handled",
        );
    }

    /// Emits a diagnostic code with message and primary label into `self.diagnostic_sink`.
    fn emitDiagnosticSimple(
        self: *TypeChecker,
        code: DiagnosticCode,
        span: Span,
        message: []const u8,
        label: []const u8,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const sev: Severity = code.defaultSeverity();
        const labels = [1]LabeledSpan{.{
            .span = span,
            .label = label,
            .style = .primary,
        }};
        try sink.emit(.{
            .code = code,
            .severity = sev,
            .primary_span = span,
            .message = message,
            .labels = &labels,
        });
    }
};

// ------------- Single-File Typecheck Entry Point --------------

/// Bundles the arenas and tables produced by standalone single-file type checking (`typecheckSource`).
pub const TypecheckResult = struct {
    /// Backing allocator.
    allocator: std.mem.Allocator,
    /// String interner.
    interner: StringInterner,
    /// Token buffer.
    token_buffer: TokenBuffer,
    /// Lossless CST arena.
    cst_arena: LosslessCstArena,
    /// Lowered AST arena.
    ast_arena: AstArena,
    /// Canonical `InternPool` (`TypeArena`).
    type_pool: InternPool,
    /// Resolved `SymbolTable` and `ScopeArena`.
    symbol_table: SymbolTable,
    /// Emitted lexical, syntax, name-resolution, and type diagnostics.
    diagnostics: DiagnosticSink,

    /// Releases all owned buffers, arenas, and pools.
    pub fn deinit(self: *TypecheckResult) void {
        self.diagnostics.deinit();
        self.symbol_table.deinit();
        self.type_pool.deinit();
        self.ast_arena.deinit();
        self.cst_arena.deinit();
        self.token_buffer.deinit();
        self.interner.deinit();
        self.* = undefined;
    }
};

/// Tokenizes, parses, resolves names/imports, and type-checks `source` for `file_id`.
pub fn typecheckSource(
    allocator: std.mem.Allocator,
    file_id: FileId,
    source: []const u8,
) !TypecheckResult {
    var interner = try StringInterner.init(allocator);
    errdefer interner.deinit();

    var token_buffer = TokenBuffer.init(allocator);
    errdefer token_buffer.deinit();

    var cst_arena = LosslessCstArena.init(allocator);
    errdefer cst_arena.deinit();

    var ast_arena = AstArena.init(allocator);
    errdefer ast_arena.deinit();

    var diagnostics = DiagnosticSink.init(allocator);
    errdefer diagnostics.deinit();

    _ = try parser.parseSource(
        source,
        file_id,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
        &interner,
    );

    var type_pool = try InternPool.init(allocator);
    errdefer type_pool.deinit();

    var symbol_table = try SymbolTable.init(allocator, &interner);
    errdefer symbol_table.deinit();

    _ = try symbol_resolver.collectFileModuleItems(
        &symbol_table,
        &interner,
        file_id,
        source,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    try symbol_resolver.resolveFileUseImports(
        &symbol_table,
        &interner,
        file_id,
        source,
        &token_buffer,
        &cst_arena,
        &diagnostics,
    );

    var checker = try TypeChecker.init(
        allocator,
        &interner,
        &type_pool,
        &symbol_table,
        file_id,
        source,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    defer checker.deinit();

    try checker.resolveModuleSignatures();
    try checker.checkFileBodies();

    return .{
        .allocator = allocator,
        .interner = interner,
        .token_buffer = token_buffer,
        .cst_arena = cst_arena,
        .ast_arena = ast_arena,
        .type_pool = type_pool,
        .symbol_table = symbol_table,
        .diagnostics = diagnostics,
    };
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_type_node_14_byte_layout_and_intern_pool_static_slots" {
    const soa_bytes = @sizeOf(TypeTag) + @sizeOf(TypeFlags) + @sizeOf(u32) * 3;
    try std.testing.expectEqual(@as(usize, 14), soa_bytes);
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(TypeFlags));

    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    try std.testing.expectEqual(@as(usize, 64), pool.countTypes());
    try std.testing.expectEqual(TypeTag.primitive, pool.getTag(.i32_ty));
    try std.testing.expectEqual(TypeTag.builtin_group, pool.getTag(.group_integer));
    try std.testing.expect(TypeGroupMask.containsPrimitive(TypeGroupMask.INTEGER, .i32_ty));
    try std.testing.expect(!TypeGroupMask.containsPrimitive(TypeGroupMask.INTEGER, .f64_ty));
    try std.testing.expect(TypeGroupMask.isSubsetOf(TypeGroupMask.SIGNED, TypeGroupMask.INTEGER));
    try std.testing.expect(TypeGroupMask.isSubsetOf(TypeGroupMask.INTEGER, TypeGroupMask.NUMERIC));

    // Structural deduplication:
    const opt_i32_a = try pool.internOptional(.i32_ty);
    const opt_i32_b = try pool.internOptional(.i32_ty);
    try std.testing.expectEqual(opt_i32_a, opt_i32_b);

    const res_a = try pool.internResult(.u64_ty, .i32_ty);
    const res_b = try pool.internResult(.u64_ty, .i32_ty);
    try std.testing.expectEqual(res_a, res_b);
    try std.testing.expect(pool.getFlags(res_a).is_must_use);
}

test "test_bind_once_vs_bind_many_and_distinct_refinement_typing" {
    const source =
        \\type UserId = distinct u64;
        \\type Port = u16 is 1024..=65535;
        \\type IntLike = ~Integer;
        \\
        \\pub fn add_same(first_val: Integer, second_val: Integer) -> Integer {
        \\    return first_val + second_val;
        \\}
        \\
        \\pub fn accept_any(first_val: any Integer, second_val: any Integer) -> i32 {
        \\    let _ = first_val;
        \\    let _ = second_val;
        \\    return 0;
        \\}
        \\
        \\pub fn test_calls() -> i32 {
        \\    let arg_a: i32 = 10;
        \\    let arg_b: i32 = 20;
        \\    let sum_ok: i32 = add_same(arg_a, arg_b);
        \\    let small_val: i8 = 10;
        \\    let big_val: i64 = 20;
        \\    let mix_ok = accept_any(small_val, big_val);
        \\    let valid_port: Port = 8080;
        \\    let widened_u16: u16 = valid_port;
        \\    let _ = widened_u16;
        \\    return sum_ok + mix_ok;
        \\}
    ;
    var res = try typecheckSource(std.testing.allocator, FileId.fromInt(1), source);
    defer res.deinit();

    try std.testing.expectEqual(@as(usize, 0), res.diagnostics.countDiagnostics());
}

/// Returns `true` if `sink` contains at least one diagnostic with `target_code`.
fn hasDiagnosticCode(sink: *const DiagnosticSink, target_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == target_code) return true;
    }
    return false;
}

test "test_phase5_all_reflection_intrinsics_and_compile_assert" {
    const valid_source =
        \\@attribute_schema
        \\pub struct ColumnAttr {
        \\    pub name: str,
        \\}
        \\
        \\@derive(Eq)
        \\pub struct Point {
        \\    @ColumnAttr(name = "coord_x")
        \\    pub x: i32,
        \\    pub y: i32,
        \\}
        \\
        \\pub fn inspect_point() -> usize {
        \\    @compile_assert(@size_of[Point]() == 8, "Point must be 8 bytes");
        \\    @compile_assert(@align_of[Point]() == 4, "Point must be 4-byte aligned");
        \\    @compile_assert(@has_field[Point]("x"), "Point must have field x");
        \\    @compile_assert(@implements[Point, Eq](), "Point must implement Eq");
        \\    comptime if false {
        \\        @compile_error("statically pruned dead branch");
        \\    }
        \\    let zero_pt: Point = @default_init[Point]();
        \\    let x_copy: i32 = @field(zero_pt, "x");
        \\    let ty_label: str = @type_name[Point]();
        \\    let embedded: &[u8] = @embed_bytes("assets/header.bin");
        \\    let info = @type_info[Point]();
        \\    let col_opt: ColumnAttr? = @field_attr_lookup[ColumnAttr](info.id, 0);
        \\    let _ = x_copy;
        \\    let _ = ty_label;
        \\    let _ = embedded;
        \\    let _ = col_opt;
        \\    return @size_of[Point]();
        \\}
    ;
    var ok_res = try typecheckSource(std.testing.allocator, FileId.fromInt(2), valid_source);
    defer ok_res.deinit();
    try std.testing.expectEqual(@as(usize, 0), ok_res.diagnostics.countDiagnostics());

    const fail_assert_source =
        \\pub fn bad_assert() -> i32 {
        \\    @compile_assert(2 + 2 == 5, "math invariant violated");
        \\    return 0;
        \\}
    ;
    var fail_res = try typecheckSource(std.testing.allocator, FileId.fromInt(3), fail_assert_source);
    defer fail_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&fail_res.diagnostics, .e0510_compile_assertion_failed));
}

test "test_phase5_comptime_fn_params_for_and_forbidden_ops_e0503" {
    const valid_source =
        \\pub comptime fn compute_magic(base_val: i32) -> i32 {
        \\    return base_val * 4;
        \\}
        \\
        \\pub fn with_comptime_param(comptime tag_name: str, runtime_val: i32) -> i32 {
        \\    let _ = tag_name;
        \\    let folded: i32 = comptime compute_magic(8);
        \\    comptime for step_idx in 0..3 {
        \\        let _ = step_idx;
        \\    }
        \\    return runtime_val + folded;
        \\}
        \\
        \\pub fn caller() -> i32 {
        \\    return with_comptime_param("alpha", 10);
        \\}
    ;
    var ok_res = try typecheckSource(std.testing.allocator, FileId.fromInt(4), valid_source);
    defer ok_res.deinit();
    try std.testing.expectEqual(@as(usize, 0), ok_res.diagnostics.countDiagnostics());

    // [1] Capturing runtime variable inside `comptime` emits `E0503`:
    const capture_err_src =
        \\pub fn bad_capture(runtime_arg: i32) -> i32 {
        \\    return comptime (runtime_arg + 1);
        \\}
    ;
    var cap_res = try typecheckSource(std.testing.allocator, FileId.fromInt(5), capture_err_src);
    defer cap_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&cap_res.diagnostics, .e0503_forbidden_comptime_operation));

    // [2] Calling `comptime fn` in a runtime expression emits `E0503`:
    const runtime_call_src =
        \\comptime fn only_ct() -> i32 { return 7; }
        \\pub fn bad_runtime_call() -> i32 { return only_ct(); }
    ;
    var rt_res = try typecheckSource(std.testing.allocator, FileId.fromInt(6), runtime_call_src);
    defer rt_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&rt_res.diagnostics, .e0503_forbidden_comptime_operation));

    // [3] Calling `extern fn` inside `comptime` emits `E0503`:
    const extern_ct_src =
        \\extern fn os_clock() -> u64;
        \\const BAD_TICK: u64 = os_clock();
    ;
    var ext_res = try typecheckSource(std.testing.allocator, FileId.fromInt(7), extern_ct_src);
    defer ext_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&ext_res.diagnostics, .e0503_forbidden_comptime_operation));

    // [4] Pointer-to-integer `as` cast inside `comptime` emits `E0503`:
    const ptr_cast_src =
        \\pub fn bad_ptr_cast() -> usize {
        \\    return comptime {
        \\        let local_num: i32 = 1;
        \\        let raw_ptr: *i32 = &local_num as *i32;
        \\        raw_ptr as usize
        \\    };
        \\}
    ;
    var ptr_res = try typecheckSource(std.testing.allocator, FileId.fromInt(8), ptr_cast_src);
    defer ptr_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&ptr_res.diagnostics, .e0503_forbidden_comptime_operation));
}

test "test_phase5_is_pattern_expr_scoping_and_negation" {
    const valid_source =
        \\pub enum Status {
        \\    Ready,
        \\    Pending(i32),
        \\}
        \\
        \\pub fn check_status(status: Status, opt_num: i32?) -> i32 {
        \\    if status is .Ready {
        \\        return 1;
        \\    }
        \\    if opt_num is .Some(bound_val) and bound_val > 0 {
        \\        return bound_val;
        \\    }
        \\    if !(status is .Pending(ignored_code)) {
        \\        return 0;
        \\    }
        \\    return 2;
        \\}
    ;
    var ok_res = try typecheckSource(std.testing.allocator, FileId.fromInt(9), valid_source);
    defer ok_res.deinit();
    try std.testing.expectEqual(@as(usize, 0), ok_res.diagnostics.countDiagnostics());

    // Negated `!(opt is .Some(leaked))` must NOT expose `leaked` inside the `then` branch (`E0403`):
    const leak_source =
        \\pub fn negated_leak(opt_num: i32?) -> i32 {
        \\    if !(opt_num is .Some(leaked_val)) {
        \\        return leaked_val;
        \\    }
        \\    return 0;
        \\}
    ;
    var leak_res = try typecheckSource(std.testing.allocator, FileId.fromInt(10), leak_source);
    defer leak_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&leak_res.diagnostics, .e0403_unresolved_symbol));
}

test "test_phase5_attribute_schema_and_two_phase_derive" {
    const valid_source =
        \\@attribute_schema(targets = [.Struct, .StructField])
        \\pub struct ArgAttr {
        \\    pub short: char = 'x',
        \\    pub help: str,
        \\}
        \\
        \\@derive(Eq, Hash, Debug, Clone)
        \\@ArgAttr(help = "pair record")
        \\pub struct Pair {
        \\    @arg(short = 'a', help = "first value")
        \\    pub first: i32,
        \\    pub second: i32,
        \\}
        \\
        \\pub fn same_pair[T: Eq](lhs: &T, rhs: &T) -> bool {
        \\    let _ = lhs;
        \\    let _ = rhs;
        \\    return true;
        \\}
        \\
        \\pub fn exercise_derived(item_a: Pair, item_b: Pair) -> u64 {
        \\    let cloned_a: Pair = item_a.clone();
        \\    let is_same: bool = cloned_a.eq(&item_b);
        \\    let is_generic_eq: bool = same_pair(&cloned_a, &item_b);
        \\    let dbg_text: str = cloned_a.debug();
        \\    let _ = is_same;
        \\    let _ = is_generic_eq;
        \\    let _ = dbg_text;
        \\    return cloned_a.hash();
        \\}
    ;
    var ok_res = try typecheckSource(std.testing.allocator, FileId.fromInt(11), valid_source);
    defer ok_res.deinit();
    try std.testing.expectEqual(@as(usize, 0), ok_res.diagnostics.countDiagnostics());

    // `@derive(Eq)` on a struct containing a non-`Eq` field must emit `E0402`:
    const bad_derive_src =
        \\pub struct OpaqueHandle {
        \\    pub raw_fd: i32,
        \\}
        \\@derive(Eq)
        \\pub struct Wrapper {
        \\    pub handle: OpaqueHandle,
        \\}
    ;
    var bad_derive = try typecheckSource(std.testing.allocator, FileId.fromInt(12), bad_derive_src);
    defer bad_derive.deinit();
    try std.testing.expect(hasDiagnosticCode(&bad_derive.diagnostics, .e0402_unsatisfied_trait_bound));
}

test "test_phase5_defer_errdefer_control_flow_guards_and_const_array_lengths" {
    const valid_source =
        \\const HEADER_WORDS: usize = 4;
        \\
        \\pub fn select_first[T, const N: usize](lhs: [T; N], rhs: [T; N]) -> [T; N] {
        \\    let _ = rhs;
        \\    return lhs;
        \\}
        \\
        \\pub fn compute_buf() -> usize {
        \\    defer {
        \\        for inner_idx in 0..2 {
        \\            if inner_idx == 1 {
        \\                break;
        \\            }
        \\        }
        \\    }
        \\    let packet: [u8; HEADER_WORDS * @size_of[u64]()] = [0; 32];
        \\    let same_pkt: [u8; 32] = select_first(packet, packet);
        \\    return same_pkt.len();
        \\}
    ;
    var ok_res = try typecheckSource(std.testing.allocator, FileId.fromInt(13), valid_source);
    defer ok_res.deinit();
    try std.testing.expectEqual(@as(usize, 0), ok_res.diagnostics.countDiagnostics());

    // `return` inside `defer` emits `E0412`:
    const defer_ret_src =
        \\pub fn bad_defer_ret() -> i32 {
        \\    defer { return 1; }
        \\    return 0;
        \\}
    ;
    var defer_ret = try typecheckSource(std.testing.allocator, FileId.fromInt(14), defer_ret_src);
    defer defer_ret.deinit();
    try std.testing.expect(hasDiagnosticCode(&defer_ret.diagnostics, .e0412_let_else_not_diverging));

    // Division by zero in array length emits `E0507`, and `const` cycle emits `E0509`:
    const cycle_and_div_src =
        \\const CYCLE_A: usize = CYCLE_B;
        \\const CYCLE_B: usize = CYCLE_A;
        \\pub fn bad_arr(buf: [u8; 8 / 0]) -> usize {
        \\    return buf.len();
        \\}
    ;
    var cycle_res = try typecheckSource(std.testing.allocator, FileId.fromInt(15), cycle_and_div_src);
    defer cycle_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&cycle_res.diagnostics, .e0509_comptime_evaluation_cycle));
    try std.testing.expect(hasDiagnosticCode(&cycle_res.diagnostics, .e0507_comptime_arithmetic_trap));
}

test "test_phase5_target_layout_and_body_semantic_side_tables" {
    const source =
        \\@attribute_schema
        \\pub struct TagAttr {
        \\    pub code: i32,
        \\}
        \\
        \\@TagAttr(code = 42)
        \\pub struct Padded {
        \\    pub flag: u8,
        \\    pub word: u64,
        \\}
        \\
        \\pub fn identity_val[T](input_val: T) -> T {
        \\    return input_val;
        \\}
        \\
        \\pub fn caller_body() -> i32 {
        \\    return identity_val(99);
        \\}
    ;

    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var token_buffer = TokenBuffer.init(std.testing.allocator);
    defer token_buffer.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var diagnostics = DiagnosticSink.init(std.testing.allocator);
    defer diagnostics.deinit();

    const file_id = FileId.fromInt(16);
    _ = try parser.parseSource(
        source,
        file_id,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
        &interner,
    );

    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(std.testing.allocator, &interner);
    defer sym_table.deinit();

    _ = try symbol_resolver.collectFileModuleItems(
        &sym_table,
        &interner,
        file_id,
        source,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    try symbol_resolver.resolveFileUseImports(
        &sym_table,
        &interner,
        file_id,
        source,
        &token_buffer,
        &cst_arena,
        &diagnostics,
    );

    var checker = try TypeChecker.init(
        std.testing.allocator,
        &interner,
        &pool,
        &sym_table,
        file_id,
        source,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    defer checker.deinit();

    try checker.resolveModuleSignatures();
    try checker.checkFileBodies();
    try std.testing.expectEqual(@as(usize, 0), diagnostics.countDiagnostics());

    // [1] Verify `TargetLayout.NATIVE_64` vs `TargetLayout.WASM32`:
    try std.testing.expectEqual(@as(u64, 16), checker.computeTypeLayout(.str_ty, TargetLayout.NATIVE_64).byte_size);
    try std.testing.expectEqual(@as(u64, 8), checker.computeTypeLayout(.str_ty, TargetLayout.WASM32).byte_size);
    try std.testing.expectEqual(@as(u64, 8), checker.computeTypeLayout(.usize_ty, TargetLayout.NATIVE_64).byte_size);
    try std.testing.expectEqual(@as(u64, 4), checker.computeTypeLayout(.usize_ty, TargetLayout.WASM32).byte_size);

    const padded_sym_id = try interner.intern("Padded");
    const mod_scope = sym_table.file_module_scopes.get(file_id.asInt()).?;
    const padded_sym_idx = sym_table.lookupInScopeDirect(mod_scope, padded_sym_id, NamespaceMask.TYPE_ONLY);
    const padded_ty = sym_table.getSymbol(padded_sym_idx).type_id;
    try std.testing.expectEqual(@as(u64, 16), checker.computeTypeLayout(padded_ty, TargetLayout.NATIVE_64).byte_size);
    try std.testing.expectEqual(
        @as(?u64, 8),
        computeStructFieldOffset(&pool, &sym_table, padded_ty, 1, TargetLayout.NATIVE_64),
    );

    // [2] Verify window-scoped `BodySemanticSideTables` extraction & `rebaseWindow`:
    var file_tables = try checker.extractFileSemanticSideTables(std.testing.allocator);
    defer file_tables.deinit();
    try std.testing.expectEqual(@as(usize, 1), file_tables.attr_instances.len);
    try std.testing.expectEqual(@as(i128, 42), file_tables.attr_instances[0].fields[0].value.int_val);

    const caller_sym_id = try interner.intern("caller_body");
    const caller_sym_idx = sym_table.lookupInScopeDirect(mod_scope, caller_sym_id, NamespaceMask.VALUE_ONLY);
    const caller_def_id = sym_table.getSymbol(caller_sym_idx).def_id;
    var body_tables = try checker.extractBodySemanticSideTables(std.testing.allocator, caller_def_id);
    defer body_tables.deinit();

    try std.testing.expect(body_tables.ast_start < body_tables.ast_end);
    try std.testing.expectEqual(@as(u32, 1), body_tables.call_instantiations.count());
    const old_len = body_tables.ast_end - body_tables.ast_start;
    body_tables.rebaseWindow(500);
    try std.testing.expectEqual(@as(u32, 500), body_tables.ast_start);
    try std.testing.expectEqual(500 + old_len, body_tables.ast_end);
}

test "test_redteam_3a_const_arrays_slice_coercion_and_attribute_schema_targets" {
    // [1] `MIN-03`: misspelled `AttributeTarget` variant & wrong named param emit `E0403` and do not fall back to `ALL`:
    const bad_schema_src =
        \\@attribute_schema(targets = [.Strcut])
        \\pub struct BadTargetAttr {
        \\    pub tag: i32,
        \\}
        \\
        \\@BadTargetAttr(tag = 1)
        \\pub fn disallowed_fn() -> i32 {
        \\    return 0;
        \\}
    ;
    var bad_schema_res = try typecheckSource(std.testing.allocator, FileId.fromInt(20), bad_schema_src);
    defer bad_schema_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&bad_schema_res.diagnostics, .e0403_unresolved_symbol));
    try std.testing.expect(hasDiagnosticCode(&bad_schema_res.diagnostics, .e0401_type_mismatch));

    // [2] `CRIT-12`: compound `[T; N * 4]` emits `E0503`; `[T; N] -> [T; M]` / `[T; 1024]` and bare `[T; N] -> [T]` emit `E0401`:
    const compound_len_src =
        \\pub fn bad_dep[const N: usize](buf: [u8; N * 4]) -> usize {
        \\    return buf.len();
        \\}
    ;
    var compound_res = try typecheckSource(std.testing.allocator, FileId.fromInt(21), compound_len_src);
    defer compound_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&compound_res.diagnostics, .e0503_forbidden_comptime_operation));

    const sym_mismatch_src =
        \\pub fn bad_sym_coerce[const N: usize, const M: usize](lhs: [i32; N]) -> [i32; M] {
        \\    return lhs;
        \\}
    ;
    var sym_mismatch_res = try typecheckSource(std.testing.allocator, FileId.fromInt(22), sym_mismatch_src);
    defer sym_mismatch_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&sym_mismatch_res.diagnostics, .e0401_type_mismatch));

    const bare_slice_src =
        \\pub fn sum_slice(items: [i32]) -> usize {
        \\    return items.len();
        \\}
        \\pub fn caller_bare() -> usize {
        \\    let arr: [i32; 3] = [1, 2, 3];
        \\    return sum_slice(arr);
        \\}
    ;
    var bare_slice_res = try typecheckSource(std.testing.allocator, FileId.fromInt(23), bare_slice_src);
    defer bare_slice_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&bare_slice_res.diagnostics, .e0401_type_mismatch));

    const borrowed_slice_src =
        \\pub fn sum_slice(items: [u8]) -> usize {
        \\    return items.len();
        \\}
        \\pub fn caller_borrowed() -> usize {
        \\    let arr: [u8; 3] = [1, 2, 3];
        \\    return sum_slice(&arr) + sum_slice(&[4, 5, 6]);
        \\}
    ;
    var borrowed_slice_res = try typecheckSource(std.testing.allocator, FileId.fromInt(24), borrowed_slice_src);
    defer borrowed_slice_res.deinit();
    try std.testing.expectEqual(@as(usize, 0), borrowed_slice_res.diagnostics.countDiagnostics());
}

test "test_redteam_3a_attr_escapes_enum_ordinals_string_interp_and_large_arity" {
    // [1] `MAJ-08`: `\xNN`, `\u{…}`, raw strings `r"…"`, and enum `.Variant` ordinals in `@attribute_schema`:
    const attr_src =
        \\pub enum LogMode {
        \\    Quiet,
        \\    Normal,
        \\    Verbose,
        \\}
        \\
        \\@attribute_schema(targets = [.Function])
        \\pub struct TraceAttr {
        \\    pub marker: char,
        \\    pub unicode_ch: char,
        \\    pub decoded_text: str,
        \\    pub raw_text: str,
        \\    pub mode: LogMode,
        \\}
        \\
        \\@TraceAttr(marker = '\x41', unicode_ch = '\u{03B1}', decoded_text = "hi\x21", raw_text = r"a\nb{x}", mode = .Verbose)
        \\pub fn traced_fn(used_val: i32) -> str {
        \\    return "value={used_val + 1}";
        \\}
    ;
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var token_buffer = TokenBuffer.init(std.testing.allocator);
    defer token_buffer.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var diagnostics = DiagnosticSink.init(std.testing.allocator);
    defer diagnostics.deinit();
    const attr_file_id = FileId.fromInt(25);
    _ = try parser.parseSource(
        attr_src,
        attr_file_id,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
        &interner,
    );
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(std.testing.allocator, &interner);
    defer sym_table.deinit();
    _ = try symbol_resolver.collectFileModuleItems(
        &sym_table,
        &interner,
        attr_file_id,
        attr_src,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    var attr_checker = try TypeChecker.init(
        std.testing.allocator,
        &interner,
        &pool,
        &sym_table,
        attr_file_id,
        attr_src,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    defer attr_checker.deinit();
    try attr_checker.resolveModuleSignatures();
    try attr_checker.checkFileBodies();
    try std.testing.expectEqual(@as(usize, 0), diagnostics.countDiagnostics());
    try std.testing.expectEqual(@as(usize, 1), attr_checker.attr_instances.items.len);
    const fields = attr_checker.attr_instances.items[0].fields;
    try std.testing.expectEqual(@as(u21, 0x41), fields[0].value.char_val);
    try std.testing.expectEqual(@as(u21, 0x03B1), fields[1].value.char_val);
    try std.testing.expectEqualStrings("hi!", interner.get(fields[2].value.str_val));
    try std.testing.expectEqualStrings("a\\nb{x}", interner.get(fields[3].value.str_val));
    try std.testing.expectEqual(@as(u16, 2), fields[4].value.enum_tag);

    // [2] `MAJ-08`: unresolved identifier inside `"{missing_ident}"` interpolation emits `E0403`:
    const bad_interp_src =
        \\pub fn broken_interp() -> str {
        \\    return "hello {missing_ident}";
        \\}
    ;
    var bad_interp_res = try typecheckSource(std.testing.allocator, FileId.fromInt(26), bad_interp_src);
    defer bad_interp_res.deinit();
    try std.testing.expect(hasDiagnosticCode(&bad_interp_res.diagnostics, .e0403_unresolved_symbol));

    // [3] `CRIT-11`: >64 guarded `match` arms and >32 `@overload` call arguments without silent truncation:
    var dyn_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer dyn_buf.deinit(std.testing.allocator);
    var line_buf: [96]u8 = undefined;
    try dyn_buf.appendSlice(std.testing.allocator, "@overload\npub fn many_args(");
    var i: usize = 0;
    while (i < 36) : (i += 1) {
        if (i > 0) try dyn_buf.appendSlice(std.testing.allocator, ", ");
        if (i == 0 or i == 35) {
            try dyn_buf.appendSlice(std.testing.allocator, try std.fmt.bufPrint(&line_buf, "p_{d}: i32", .{i}));
        } else {
            try dyn_buf.appendSlice(std.testing.allocator, try std.fmt.bufPrint(&line_buf, "_p_{d}: i32", .{i}));
        }
    }
    try dyn_buf.appendSlice(std.testing.allocator, ") -> i32 { return p_0 + p_35; }\n");
    try dyn_buf.appendSlice(std.testing.allocator, "@overload\npub fn many_args(");
    i = 0;
    while (i < 36) : (i += 1) {
        if (i > 0) try dyn_buf.appendSlice(std.testing.allocator, ", ");
        if (i == 0) {
            try dyn_buf.appendSlice(std.testing.allocator, try std.fmt.bufPrint(&line_buf, "p_{d}: bool", .{i}));
        } else {
            try dyn_buf.appendSlice(std.testing.allocator, try std.fmt.bufPrint(&line_buf, "_p_{d}: bool", .{i}));
        }
    }
    try dyn_buf.appendSlice(std.testing.allocator, ") -> i32 { if p_0 { return 1; } return 0; }\n");
    try dyn_buf.appendSlice(std.testing.allocator, "pub fn many_match(val: i32, flag: bool) -> i32 {\n    let sum = many_args(");
    i = 0;
    while (i < 36) : (i += 1) {
        if (i > 0) try dyn_buf.appendSlice(std.testing.allocator, ", ");
        try dyn_buf.appendSlice(std.testing.allocator, try std.fmt.bufPrint(&line_buf, "{d}", .{i}));
    }
    try dyn_buf.appendSlice(std.testing.allocator, ");\n    return match val {\n");
    i = 0;
    while (i < 70) : (i += 1) {
        try dyn_buf.appendSlice(
            std.testing.allocator,
            try std.fmt.bufPrint(&line_buf, "        _ if flag and val == {d} => {d},\n", .{ i, i }),
        );
    }
    try dyn_buf.appendSlice(std.testing.allocator, "        _ => sum,\n    };\n}\n");

    var large_res = try typecheckSource(std.testing.allocator, FileId.fromInt(27), dyn_buf.items);
    defer large_res.deinit();
    try std.testing.expectEqual(@as(usize, 0), large_res.diagnostics.countDiagnostics());
}

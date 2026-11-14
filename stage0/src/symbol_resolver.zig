//! Module & Lexical Scope Name Resolution, Visibility Hygiene & Overload Grouping
//!
//! Implements Phase 4 (`PLAN.md` Section 2.1, `DR-02` Deliverable 2, `DR-03` Section 3, and
//! `DR-04`) lexical and module-level symbol resolution for CoreX:
//! - `ScopeArena` (`ScopeId`) with bounded lexical depth (`MAX_SCOPE_DEPTH = 512`) and parent chains,
//! - Disjoint `Namespace` (`type_ns`, `value_ns`, `const_ns`) $O(1)$ hash-table lookup,
//! - Module item collection (`mod` inline and file modules, `use` path/glob/group/alias imports),
//! - Module boundary `pub` visibility enforcement (`E0409`) and duplicate symbol detection (`E0408`),
//! - Explicit `@overload` function set grouping (`DR-02` Section 1.4),
//! - Unused local binding and parameter warnings (`W0402`) with `_` prefix autofixes, and
//! - Stack-bounded Levenshtein + Jaro-Winkler prefix-boosted "did you mean?" typo suggestions (`E0403`).

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const lexer = @import("lexer.zig");
const diagnostic = @import("diag/diagnostic.zig");
const query_db = @import("query_db.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const NodeIndex = mem_foundation.NodeIndex;
const ExtraIndex = mem_foundation.ExtraIndex;
pub const ScopeId = mem_foundation.ScopeId;
const TypeId = mem_foundation.TypeId;
const DefId = query_db.DefId;
const TokenKind = syntax_arenas.TokenKind;
const CstNodeKind = syntax_arenas.CstNodeKind;
const AstTag = syntax_arenas.AstTag;
const TokenBuffer = syntax_arenas.TokenBuffer;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstArena = syntax_arenas.AstArena;
const DiagnosticSink = diagnostic.DiagnosticSink;
const LabeledSpan = diagnostic.LabeledSpan;
const SuggestedFix = diagnostic.SuggestedFix;
const TextEdit = diagnostic.TextEdit;

// ---------------------------------------- TYPES ----------------------------------------

// -------------------- Namespaces & Scopes ---------------------

/// Disjoint CoreX identifier namespaces (`DR-03` Section 3.1).
pub const Namespace = enum(u2) {
    /// `PascalCase` types, traits, constrained type groups, and type parameters (`0`).
    type_ns = 0,
    /// `snake_case` functions, local bindings, parameters, fields, and modules (`1`).
    value_ns = 1,
    /// `SCREAMING_SNAKE_CASE` compile-time constants and const generic parameters (`2`).
    const_ns = 2,

    /// Converts `self` into a single-bit `NamespaceMask`.
    pub inline fn toMask(self: Namespace) NamespaceMask {
        return switch (self) {
            .type_ns => NamespaceMask.TYPE_ONLY,
            .value_ns => NamespaceMask.VALUE_ONLY,
            .const_ns => NamespaceMask.CONST_ONLY,
        };
    }
};

/// Bitmask of `Namespace` categories used for multi-namespace lookups and imports.
pub const NamespaceMask = packed struct(u8) {
    /// `true` if `Namespace.type_ns` is included.
    is_type: bool = false,
    /// `true` if `Namespace.value_ns` is included.
    is_value: bool = false,
    /// `true` if `Namespace.const_ns` is included.
    is_const: bool = false,
    /// Reserved zero padding (`0`).
    reserved: u5 = 0,

    /// Mask matching only `Namespace.type_ns`.
    pub const TYPE_ONLY: NamespaceMask = .{ .is_type = true };
    /// Mask matching only `Namespace.value_ns`.
    pub const VALUE_ONLY: NamespaceMask = .{ .is_value = true };
    /// Mask matching only `Namespace.const_ns`.
    pub const CONST_ONLY: NamespaceMask = .{ .is_const = true };
    /// Mask matching `Namespace.value_ns` or `Namespace.const_ns` (expression position).
    pub const VALUE_OR_CONST: NamespaceMask = .{ .is_value = true, .is_const = true };
    /// Mask matching `Namespace.type_ns` or `Namespace.value_ns` (module/type path prefixes).
    pub const TYPE_OR_VALUE: NamespaceMask = .{ .is_type = true, .is_value = true };
    /// Mask matching all three namespaces (`use` aliases and typo suggestions).
    pub const ALL: NamespaceMask = .{ .is_type = true, .is_value = true, .is_const = true };

    /// Returns `true` if `self` includes `namespace`.
    pub inline fn contains(self: NamespaceMask, namespace: Namespace) bool {
        return switch (namespace) {
            .type_ns => self.is_type,
            .value_ns => self.is_value,
            .const_ns => self.is_const,
        };
    }
};

/// Classification of lexical and module scopes in `ScopeArena`.
pub const ScopeKind = enum(u8) {
    /// Root built-in prelude scope (`ScopeId` `0`).
    global_prelude = 0,
    /// File or inline `mod { … }` module scope.
    module_scope = 1,
    /// Nominal `struct`, `union`, `bit_field`, or `enum` member/variant container scope.
    nominal_type_scope = 2,
    /// `trait { … }` declaration scope.
    trait_scope = 3,
    /// `impl … { … }` declaration scope.
    impl_scope = 4,
    /// Function or subscript signature and parameter scope.
    fn_scope = 5,
    /// Lexical `{ … }` statement block scope.
    block_scope = 6,
    /// `for`, `while`, or `loop` body scope (`break` / `continue` target).
    loop_scope = 7,
    /// `match` arm pattern + guard + body scope.
    match_arm_scope = 8,
    /// `catch |err|` or `errdefer |err|` error payload capture scope.
    catch_or_errdefer_scope = 9,
};

/// 1-byte bit-packed semantic context flags inherited down lexical scope chains.
pub const ScopeFlags = packed struct(u8) {
    /// `true` inside an `unsafe` function, block, or `impl`.
    is_unsafe_context: bool = false,
    /// `true` inside an `async` function or block.
    is_async_context: bool = false,
    /// `true` inside a `comptime` function, block, or constant initializer.
    is_comptime_context: bool = false,
    /// `true` inside a `for`, `while`, or `loop` body.
    is_inside_loop: bool = false,
    /// `true` inside a function returning `Result[T, E]` or `T?`.
    is_inside_fallible_fn: bool = false,
    /// Reserved zero bits (`0`).
    reserved: u3 = 0,
};

/// Lexical or module scope record stored in `ScopeArena`.
pub const ScopeRecord = struct {
    /// Category of this scope.
    kind: ScopeKind,
    /// Inherited context flags (`unsafe`, `async`, `comptime`, loop, fallible).
    flags: ScopeFlags = .{},
    /// Enclosing parent `ScopeId` (`.none` for `.global_prelude`).
    parent: ScopeId = .none,
    /// Nearest enclosing `.module_scope` `ScopeId` for $O(1)$ `pub` visibility checks.
    enclosing_module: ScopeId = .none,
    /// Owning top-level `DefId` (`.NONE` for prelude/file root).
    owner_def_id: DefId = .NONE,
    /// Source file handle where this scope resides.
    file_id: FileId = .none,
    /// Nesting depth from `.global_prelude` (`0..MAX_SCOPE_DEPTH`).
    depth: u16 = 0,
};

/// Strongly typed 32-bit index into `SymbolTable.symbols`.
pub const SymbolIndex = enum(u32) {
    /// Sentinel representing an unresolved or absent symbol (`0xFFFF_FFFF`).
    none = std.math.maxInt(u32),
    _,

    /// Wraps a raw 32-bit unsigned integer into a `SymbolIndex`.
    pub inline fn fromInt(raw_value: u32) SymbolIndex {
        return @fromBackingInt(@intCast(raw_value));
    }

    /// Extracts the underlying 32-bit unsigned integer of `self`.
    pub inline fn asInt(self: SymbolIndex) u32 {
        return @backingInt(self);
    }

    /// Returns `true` if `self` is `.none`.
    pub inline fn isNone(self: SymbolIndex) bool {
        return self == .none;
    }
};

/// Visibility level of a declaration (`private` to its defining module vs. `pub` exported).
pub const Visibility = enum(u1) {
    /// Visible only within the defining module and its descendant inline submodules.
    private = 0,
    /// Exported via `pub` and accessible across module boundaries.
    public = 1,
};

/// Semantic classification of a resolved symbol in `SymbolTable`.
pub const SymbolKind = enum(u8) {
    /// Inline or external `mod` declaration (`0`).
    module_sym = 0,
    /// Imported `use` alias or binding (`1`).
    use_alias_sym = 1,
    /// `struct` nominal type declaration (`2`).
    struct_sym = 2,
    /// `enum` nominal type declaration (`3`).
    enum_sym = 3,
    /// `union` nominal type declaration (`4`).
    union_sym = 4,
    /// `bit_field` packed integer type declaration (`5`).
    bit_field_sym = 5,
    /// `trait` interface declaration (`6`).
    trait_sym = 6,
    /// Transparent `type Alias = Target;` declaration (`7`).
    type_alias_sym = 7,
    /// User-defined or built-in Constrained Type Group (`type G = A | ~B;`) (`8`).
    type_group_sym = 8,
    /// Nominal `type New = distinct Base;` declaration (`9`).
    distinct_type_sym = 9,
    /// Range or pattern refinement `type R = Base is low..=high;` declaration (`10`).
    refined_type_sym = 10,
    /// Generic type parameter (`[T: Bound]`) (`11`).
    type_param_sym = 11,
    /// Standalone function, method, or subscript declaration (`12`).
    fn_sym = 12,
    /// Explicit `@overload` function group entry (`DR-02` Section 1.4) (`13`).
    overload_group_sym = 13,
    /// Compile-time `const` declaration (`14`).
    const_sym = 14,
    /// Compile-time `const N: usize` generic parameter (`15`).
    const_param_sym = 15,
    /// Function, method, or closure value parameter (`16`).
    param_sym = 16,
    /// Immutable local `let` binding (`17`).
    local_let_sym = 17,
    /// Mutable local `var` or `let mut` binding (`18`).
    local_var_sym = 18,
    /// Variant inside an `enum` declaration (`19`).
    enum_variant_sym = 19,
    /// Field inside a `struct`, `union`, or `bit_field` declaration (`20`).
    field_sym = 20,
};

/// 1-byte bit-packed mask of compiler-synthesized `@derive(…)` traits (`DR-05` Section 2.3).
pub const DeriveMask = packed struct(u8) {
    /// `@derive(Eq)` (`fn eq(&self, other: &Self) -> bool`).
    has_eq: bool = false,
    /// `@derive(Hash)` (`fn hash(&self) -> u64`).
    has_hash: bool = false,
    /// `@derive(Debug)` (`fn debug(&self) -> str`).
    has_debug: bool = false,
    /// `@derive(Clone)` (`fn clone(&self) -> Self`).
    has_clone: bool = false,
    /// Reserved padding bits (`0`).
    reserved: u4 = 0,

    /// Returns `true` if at least one built-in `@derive` trait is requested.
    pub inline fn hasAny(self: DeriveMask) bool {
        return self.has_eq or self.has_hash or self.has_debug or self.has_clone;
    }
};

/// 1-byte bit-packed mask of valid declaration targets for an `@attribute_schema` struct (`DR-05` Section 2.2).
pub const AttrTargetMask = packed struct(u8) {
    /// Allowed on `struct` declarations (`.Struct`).
    has_struct_target: bool = false,
    /// Allowed on `enum` declarations (`.Enum`).
    has_enum_target: bool = false,
    /// Allowed on `struct`/`union`/`bit_field` fields (`.StructField` / `.Field`).
    has_field_target: bool = false,
    /// Allowed on `fn` declarations and methods (`.Fn` / `.Function`).
    has_fn_target: bool = false,
    /// Allowed on `enum` variants (`.EnumVariant` / `.Variant`).
    has_variant_target: bool = false,
    /// Allowed on function parameters (`.Param`).
    has_param_target: bool = false,
    /// Allowed on local `let` / `var` bindings (`.Local`).
    has_local_target: bool = false,
    /// Allowed on `union` declarations (`.Union`).
    has_union_target: bool = false,

    /// Unrestricted target mask used when `@attribute_schema` omits an explicit `targets` filter.
    pub const ALL: AttrTargetMask = .{
        .has_struct_target = true,
        .has_enum_target = true,
        .has_field_target = true,
        .has_fn_target = true,
        .has_variant_target = true,
        .has_param_target = true,
        .has_local_target = true,
        .has_union_target = true,
    };

    /// Returns `true` if no target bit is enabled.
    pub inline fn isEmpty(self: AttrTargetMask) bool {
        return @as(u8, @bitCast(self)) == 0;
    }
};

/// 2-byte bit-packed semantic and attribute flags attached to each `SymbolRecord`.
pub const SymbolFlags = packed struct(u16) {
    /// `true` if declared with `pub`.
    is_pub: bool = false,
    /// `true` if declared with `mut` or `var`.
    is_mut: bool = false,
    /// `true` if referenced at least once after declaration (suppresses `W0402`).
    is_used: bool = false,
    /// `true` if annotated with `@overload` (`DR-02` Section 1.4).
    is_overload: bool = false,
    /// `true` if annotated with `@must_use` or returning `Result[T, E]` (`DR-07` Section 2.7).
    is_must_use: bool = false,
    /// `true` if annotated with `@from` for `FromError` upcasting (`DR-07` Section 2.2).
    is_from_error: bool = false,
    /// `true` if annotated with `#soa` or `@soa`.
    is_soa_annotated: bool = false,
    /// `true` if pre-populated in `.global_prelude`.
    is_builtin: bool = false,
    /// `true` if introduced via a `use` import.
    is_imported: bool = false,
    /// `true` if this type alias is a `distinct` newtype.
    is_distinct: bool = false,
    /// `true` if this type alias carries an `is` range/pattern refinement.
    is_refined: bool = false,
    /// `true` if this symbol represents a built-in or user Constrained Type Group.
    is_type_group: bool = false,
    /// `true` if this function is an `extern` or trait prototype without a body block.
    is_prototype_only: bool = false,
    /// `true` if declared with `comptime` (`comptime fn` or `comptime` parameter, `DR-05` Section 3.1).
    is_comptime: bool = false,
    /// `true` if annotated with `@attribute_schema` (`DR-05` Section 2.2).
    is_attribute_schema: bool = false,
    /// `true` if declared with `extern` or `@extern` (`DR-05` Section 3.1).
    is_extern: bool = false,
};

/// 2-byte bit-packed Phase 6 contract, safety, and FFI attributes attached to `SymbolRecord` (`DR-17`, `DR-20`).
pub const DeclContractFlags = packed struct(u16) {
    /// `true` if annotated with `@no_alloc` (`DR-17` §2.2).
    is_no_alloc: bool = false,
    /// `true` if annotated with `@no_panic` (`DR-17` §2.2).
    is_no_panic: bool = false,
    /// `true` if annotated with `@no_block` (`DR-17` §2.2).
    is_no_block: bool = false,
    /// `true` if annotated with `@linear` (`DR-06` §1.2 Tier 3).
    is_linear: bool = false,
    /// `true` if annotated with `@zero_pad` (`DR-20` `D-01`).
    is_zero_pad: bool = false,
    /// `true` if annotated with `@secret` (`DR-20` `D-02`, Seam #1).
    is_secret: bool = false,
    /// `true` if annotated with `@std_cap_boundary` (`DR-17` §2.3).
    is_std_cap_boundary: bool = false,
    /// `true` if annotated with `@export`.
    is_export: bool = false,
    /// `true` if annotated with `@link_name(…)`.
    has_link_name: bool = false,
    /// `true` if annotated with `@link_section(…)`.
    has_link_section: bool = false,
    /// `true` if annotated with `@max_stack(…)` (`DR-17` §3.2).
    has_max_stack: bool = false,
    /// `true` if annotated with `@local` (`DR-06` §1.2 non-escaping borrow).
    is_local_only: bool = false,
    /// `true` if annotated with `@ifunc` (`DR-17` §4.2 Gate C indirect resolver).
    is_ifunc: bool = false,
    /// `true` if annotated with `@repr(C)` or `@repr(c)`.
    is_repr_c: bool = false,
    /// `true` if annotated with `@packed` or `@repr(packed)`.
    is_packed: bool = false,
    /// `true` if annotated with `@cache_aligned` (`DR-20` `D-10A`).
    is_cache_aligned: bool = false,

    comptime {
        std.debug.assert(@sizeOf(DeclContractFlags) == 2);
    }
};

/// Canonical 12-bit inferred capability/effect bits (`DR-17` §2.1) for `@std_cap_boundary` masks.
pub const CapabilityBits = struct {
    /// Filesystem I/O capability (`bit 0`).
    pub const FS: u16 = 1 << 0;
    /// Network socket I/O capability (`bit 1`).
    pub const NET: u16 = 1 << 1;
    /// Environment variable, `argv`, or host metadata capability (`bit 2`).
    pub const ENV: u16 = 1 << 2;
    /// Child process, signal, or OS thread spawn capability (`bit 3`).
    pub const PROCESS: u16 = 1 << 3;
    /// Foreign function interface or linker symbol capability (`bit 4`).
    pub const FFI: u16 = 1 << 4;
    /// Raw pointer dereference, pointer offset, `union`, or `asm` capability (`bit 5`).
    pub const UNSAFE_OP: u16 = 1 << 5;
    /// Dynamic heap allocation capability (`bit 6`; `@no_alloc` forbids this bit).
    pub const ALLOC: u16 = 1 << 6;
    /// Unrecoverable trap / panic capability (`bit 7`; `@no_panic` forbids this bit).
    pub const MAY_PANIC: u16 = 1 << 7;
    /// Direct host clock capability (`bit 8`).
    pub const CLOCK: u16 = 1 << 8;
    /// Direct host OS entropy / CSPRNG capability (`bit 9`).
    pub const ENTROPY: u16 = 1 << 9;
    /// Blocking synchronization or sleep capability (`bit 10`; `@no_block` forbids blocking bits).
    pub const BLOCKING_SYNC: u16 = 1 << 10;
    /// Unconstrained dynamic `fn(…)` or `dyn Trait` dispatch capability (`bit 11`).
    pub const INDIRECT_OPAQUE: u16 = 1 << 11;
    /// Alias for `ALLOC` (`1 << 6`).
    pub const HEAP_ALLOC: u16 = ALLOC;
    /// Alias for `BLOCKING_SYNC` (`1 << 10`).
    pub const IO_ASYNC: u16 = BLOCKING_SYNC;
    /// Alias for `FS` (`1 << 0`).
    pub const IO_FS: u16 = FS;
    /// Alias for `NET` (`1 << 1`).
    pub const IO_NET: u16 = NET;
    /// Alias for `PROCESS` (`1 << 3`).
    pub const THREAD_SPAWN: u16 = PROCESS;
    /// Composite mask for `FFI | UNSAFE_OP` (`0x0030`).
    pub const FFI_UNSAFE: u16 = FFI | UNSAFE_OP;
    /// Composite mask for `CLOCK | ENTROPY` (`0x0300`).
    pub const CLOCK_ENTROPY: u16 = CLOCK | ENTROPY;
};

/// Complete metadata record for a symbol registered in `SymbolTable`.
pub const SymbolRecord = struct {
    /// Interned identifier handle (`SymbolId`).
    name: SymbolId,
    /// Borrowed UTF-8 slice for `name` from `StringInterner`.
    name_text: []const u8,
    /// Semantic kind of this symbol.
    kind: SymbolKind,
    /// Disjoint namespace (`type_ns`, `value_ns`, `const_ns`) owning this symbol.
    namespace: Namespace,
    /// Module visibility (`private` vs. `public`).
    visibility: Visibility,
    /// Bit-packed attribute and usage flags.
    flags: SymbolFlags = .{},
    /// Enclosing `ScopeId` where this symbol is registered.
    scope_id: ScopeId,
    /// Associated top-level `DefId` (`.NONE` for locals, nested methods, and built-ins).
    def_id: DefId = .NONE,
    /// Enclosing top-level `DefId` owning a `@derive` or `impl` member symbol (`.NONE` otherwise).
    owner_def_id: DefId = .NONE,
    /// AST node index of the declaration (`.none` for built-ins).
    ast_node: NodeIndex = .none,
    /// CST node index of the declaration (`.none` for built-ins).
    cst_node: CstNodeIndex = .none,
    /// Exact source span of the symbol's identifier token.
    decl_span: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 },
    /// Canonical `TypeId` assigned to this symbol (`TypeId.err_ty` until resolved).
    type_id: TypeId = .err_ty,
    /// Target `SymbolIndex` (for `use_alias_sym`) or overload set index (for `overload_group_sym`).
    target_symbol: SymbolIndex = .none,
    /// Member/child `ScopeId` owned by this symbol (for `module_sym`, `struct_sym`, `enum_sym`, `trait_sym`).
    target_scope: ScopeId = .none,
    /// Ordinal index of a field, variant, or parameter within its parent container (`0`-based).
    member_ordinal: u16 = 0,
    /// Bit width for `bit_field` members (`0` for standard fields).
    bit_width: u16 = 0,
    /// Bitmask of `comptime`-qualified value parameters (`bit i == 1` when parameter `i` is `comptime`).
    is_comptime_param_mask: u64 = 0,
    /// Parsed `@derive(Eq, Hash, Debug, Clone)` bitmask on nominal `struct` / `enum` / `union` items.
    derive_mask: DeriveMask = .{},
    /// Allowed declaration target bitmask when `flags.is_attribute_schema` is `true`.
    attr_target_mask: AttrTargetMask = .{},
    /// Phase 6 contract, ownership, secret, zero-pad, and FFI flags (`DR-17`, `DR-20`).
    contract_flags: DeclContractFlags = .{},
    /// Explicit stack frame budget in bytes when `contract_flags.has_max_stack` is `true` (`@max_stack(N)`).
    max_stack_bytes: u32 = 0,
    /// Capability bits explicitly emitted at an `@std_cap_boundary` (`DR-17` §2.3).
    cap_emits_mask: u16 = 0,
    /// Capability bits explicitly cleared/trusted at an `@std_cap_boundary` (`DR-17` §2.3).
    cap_clears_mask: u16 = 0,
    /// Interned section name when `contract_flags.has_link_section` is `true` (`@link_section("…")`).
    link_section_name: []const u8 = "",
    /// Interned external symbol name when `contract_flags.has_link_name` is `true` (`@link_name("…")`).
    link_name_text: []const u8 = "",
    /// Explicit discriminant width in bits on `@repr(u8/u16/u32/u64)` `enum` declarations (`0` = default).
    repr_tag_bits: u8 = 0,
    /// Explicit power-of-two alignment encoded as `log2(align) + 1` (`0` = default).
    explicit_align_log2_plus1: u8 = 0,
};

/// Explicit `@overload` function group tracking all member `fn_sym` symbols in a scope (`DR-02`).
pub const OverloadSet = struct {
    /// Shared function identifier (`SymbolId`).
    name: SymbolId,
    /// Defining `ScopeId`.
    scope_id: ScopeId,
    /// Contiguous list of overloaded `fn_sym` `SymbolIndex` handles in declaration order.
    members: std.ArrayListUnmanaged(SymbolIndex) = .empty,

    /// Releases the member list back to `allocator`.
    pub fn deinit(self: *OverloadSet, allocator: std.mem.Allocator) void {
        self.members.deinit(allocator);
        self.* = undefined;
    }
};

/// Unresolved deferred `use` import item queued during Pass 1 for Pass 2 resolution.
pub const PendingUseImport = struct {
    /// Enclosing module `ScopeId` where `use` appeared.
    module_scope: ScopeId,
    /// Source file handle containing the `use` declaration.
    file_id: FileId,
    /// Top-level `DefId` of the `use` declaration.
    def_id: DefId,
    /// `true` if `pub use` re-exports the imported symbol(s).
    is_pub: bool,
    /// AST node index of the `use_decl`.
    ast_node: NodeIndex,
    /// CST node index of the `use_item`.
    cst_node: CstNodeIndex,
};

/// Result of looking up a symbol with visibility verification.
pub const LookupResult = union(enum) {
    /// Symbol was found and is accessible from the caller's scope.
    found: SymbolIndex,
    /// Symbol exists but is private (`!is_pub`) and accessed from outside its defining module (`E0409`).
    private_error: SymbolIndex,
    /// No matching symbol exists in the requested namespace(s).
    not_found,
};

/// Recognized built-in declaration header attribute selector for `extractItemHeaderMetadataValidated`.
const HeaderAttrKind = enum(u8) {
    /// `@align(N)` explicit power-of-two byte alignment attribute.
    align_attr,
    /// `@attribute_schema` target-constrained schema struct attribute.
    attribute_schema,
    /// `@cache_aligned` target L1/L2 cache-line alignment attribute (`DR-20` `D-10A`).
    cache_aligned,
    /// `@derive(Eq, Hash, Debug, Clone)` trait synthesis attribute.
    derive,
    /// `@export` symbol export attribute.
    export_attr,
    /// `@extern` foreign symbol linkage attribute.
    extern_attr,
    /// `@from` `FromError` upcasting constructor attribute.
    from,
    /// `@ifunc` forbidden indirect function resolver attribute (`E0327`).
    ifunc,
    /// `@linear` Tier 3 must-consume ownership attribute (`DR-06`).
    linear,
    /// `@link_name(…)` custom linker symbol name attribute.
    link_name,
    /// `@link_section(…)` custom object section attribute (`E0327` checked).
    link_section,
    /// `@local` non-escaping borrow attribute (`DR-06`).
    local,
    /// `@max_stack(N)` static stack frame byte budget attribute (`DR-17`).
    max_stack,
    /// `@must_use` unused-result warning attribute (`DR-07`).
    must_use,
    /// `@no_alloc` heap-allocation-free effect contract (`DR-17`).
    no_alloc,
    /// `@no_block` non-blocking effect contract (`DR-17`).
    no_block,
    /// `@no_panic` panic-free effect contract (`DR-17`).
    no_panic,
    /// `@overload` explicit function overload group attribute (`DR-02`).
    overload,
    /// `@packed` 1-byte field alignment attribute.
    packed_attr,
    /// `@repr(…)` explicit layout and discriminant width attribute.
    repr,
    /// `@secret` constant-time / wire-redacted taint attribute (`DR-20`).
    secret,
    /// `@soa` Structure-of-Arrays layout attribute.
    soa,
    /// `@std_cap_boundary(…)` stdlib capability boundary attribute (`DR-17`).
    std_cap_boundary,
    /// `@zero_pad` deterministic padding zeroing attribute (`DR-20`).
    zero_pad,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum lexical scope nesting depth (`512`, matching `syntax_arenas.MAX_PARSE_DEPTH`).
pub const MAX_SCOPE_DEPTH: usize = 512;

/// Maximum identifier byte length evaluated by the stack-allocated Levenshtein matrix (`64`).
pub const MAX_EDIT_DISTANCE_LEN: usize = 64;

/// Built-in trait names pre-populated in `.global_prelude` (`DR-02`, `DR-04` & `DR-06`).
pub const BUILTIN_TRAIT_NAMES = [_][]const u8{
    "AutoDrop",
    "Clone",
    "Copy",
    "Debug",
    "Default",
    "Display",
    "Drop",
    "Eq",
    "FromError",
    "Hash",
    "Iterator",
    "Ord",
    "Send",
    "Sync",
};

/// Built-in primitive and Constrained Type Group mappings pre-populated in `.global_prelude` (`DR-04`).
pub const BuiltinTypeEntry = struct {
    /// Surface identifier in `.cx` source code.
    name: []const u8,
    /// Pre-assigned static `TypeId` (`0..44`).
    type_id: TypeId,
    /// `true` if this entry is one of the 13 Constrained Type Groups (`32..44`).
    is_group: bool,
};

/// Canonical table of 19 primitive types and 13 Constrained Type Groups (`DR-04` Section 1.1 & `DR-20` `D-01`).
pub const BUILTIN_TYPES_AND_GROUPS = [_]BuiltinTypeEntry{
    .{ .name = "i8", .type_id = .i8_ty, .is_group = false },
    .{ .name = "i16", .type_id = .i16_ty, .is_group = false },
    .{ .name = "i32", .type_id = .i32_ty, .is_group = false },
    .{ .name = "i64", .type_id = .i64_ty, .is_group = false },
    .{ .name = "i128", .type_id = .i128_ty, .is_group = false },
    .{ .name = "isize", .type_id = .isize_ty, .is_group = false },
    .{ .name = "u8", .type_id = .u8_ty, .is_group = false },
    .{ .name = "u16", .type_id = .u16_ty, .is_group = false },
    .{ .name = "u32", .type_id = .u32_ty, .is_group = false },
    .{ .name = "u64", .type_id = .u64_ty, .is_group = false },
    .{ .name = "u128", .type_id = .u128_ty, .is_group = false },
    .{ .name = "usize", .type_id = .usize_ty, .is_group = false },
    .{ .name = "f32", .type_id = .f32_ty, .is_group = false },
    .{ .name = "f64", .type_id = .f64_ty, .is_group = false },
    .{ .name = "bool", .type_id = .bool_ty, .is_group = false },
    .{ .name = "char", .type_id = .char_ty, .is_group = false },
    .{ .name = "str", .type_id = .str_ty, .is_group = false },
    .{ .name = "never", .type_id = .never_ty, .is_group = false },
    .{ .name = "unit", .type_id = .unit_ty, .is_group = false },
    .{ .name = "Signed", .type_id = .group_signed, .is_group = true },
    .{ .name = "Unsigned", .type_id = .group_unsigned, .is_group = true },
    .{ .name = "Integer", .type_id = .group_integer, .is_group = true },
    .{ .name = "Float", .type_id = .group_float, .is_group = true },
    .{ .name = "Number", .type_id = .group_number, .is_group = true },
    .{ .name = "Numeric", .type_id = .group_numeric, .is_group = true },
    .{ .name = "Comparable", .type_id = .group_comparable, .is_group = true },
    .{ .name = "Equatable", .type_id = .group_equatable, .is_group = true },
    .{ .name = "Bytes", .type_id = .group_bytes, .is_group = true },
    .{ .name = "Scalar", .type_id = .group_scalar, .is_group = true },
    .{ .name = "Copy", .type_id = .group_copy, .is_group = true },
    .{ .name = "FromBytes", .type_id = .group_from_bytes, .is_group = true },
    .{ .name = "IntoBytes", .type_id = .group_into_bytes, .is_group = true },
};

/// $O(1)$ static lookup map from `@std_cap_boundary` capability names to `CapabilityBits` (`DR-17` §2.1–2.3).
pub const CAPABILITY_NAME_MAP = std.StaticStringMap(u16).initComptime(.{
    .{ "Alloc", CapabilityBits.ALLOC },
    .{ "BlockingSync", CapabilityBits.BLOCKING_SYNC },
    .{ "Clock", CapabilityBits.CLOCK },
    .{ "ClockEntropy", CapabilityBits.CLOCK_ENTROPY },
    .{ "Entropy", CapabilityBits.ENTROPY },
    .{ "Env", CapabilityBits.ENV },
    .{ "Ffi", CapabilityBits.FFI },
    .{ "FfiUnsafe", CapabilityBits.FFI_UNSAFE },
    .{ "Fs", CapabilityBits.FS },
    .{ "HeapAlloc", CapabilityBits.HEAP_ALLOC },
    .{ "IndirectOpaque", CapabilityBits.INDIRECT_OPAQUE },
    .{ "IoAsync", CapabilityBits.IO_ASYNC },
    .{ "IoFs", CapabilityBits.IO_FS },
    .{ "IoNet", CapabilityBits.IO_NET },
    .{ "MayPanic", CapabilityBits.MAY_PANIC },
    .{ "Net", CapabilityBits.NET },
    .{ "Process", CapabilityBits.PROCESS },
    .{ "ThreadSpawn", CapabilityBits.THREAD_SPAWN },
    .{ "UnsafeOp", CapabilityBits.UNSAFE_OP },
    .{ "alloc", CapabilityBits.ALLOC },
    .{ "block", CapabilityBits.BLOCKING_SYNC },
    .{ "blocking_sync", CapabilityBits.BLOCKING_SYNC },
    .{ "clock", CapabilityBits.CLOCK },
    .{ "clock_entropy", CapabilityBits.CLOCK_ENTROPY },
    .{ "entropy", CapabilityBits.ENTROPY },
    .{ "env", CapabilityBits.ENV },
    .{ "ffi", CapabilityBits.FFI },
    .{ "ffi_unsafe", CapabilityBits.FFI_UNSAFE },
    .{ "fs", CapabilityBits.FS },
    .{ "heap_alloc", CapabilityBits.HEAP_ALLOC },
    .{ "indirect_opaque", CapabilityBits.INDIRECT_OPAQUE },
    .{ "io_async", CapabilityBits.IO_ASYNC },
    .{ "io_fs", CapabilityBits.IO_FS },
    .{ "io_net", CapabilityBits.IO_NET },
    .{ "may_panic", CapabilityBits.MAY_PANIC },
    .{ "net", CapabilityBits.NET },
    .{ "panic", CapabilityBits.MAY_PANIC },
    .{ "process", CapabilityBits.PROCESS },
    .{ "thread_spawn", CapabilityBits.THREAD_SPAWN },
    .{ "unsafe_op", CapabilityBits.UNSAFE_OP },
});

/// Canonical `AttributeTarget` variant names for `@attribute_schema(targets = […])` typo suggestions.
const ATTRIBUTE_TARGET_NAMES = [_][]const u8{
    "Enum",
    "EnumVariant",
    "Field",
    "Fn",
    "Function",
    "Local",
    "Param",
    "Struct",
    "StructField",
    "Union",
    "Variant",
};

/// $O(1)$ static lookup map from `AttributeTarget` variant names to `AttrTargetMask` bits.
const ATTRIBUTE_TARGET_MAP = std.StaticStringMap(AttrTargetMask).initComptime(.{
    .{ "Enum", AttrTargetMask{ .has_enum_target = true } },
    .{ "EnumVariant", AttrTargetMask{ .has_variant_target = true } },
    .{ "Field", AttrTargetMask{ .has_field_target = true } },
    .{ "Fn", AttrTargetMask{ .has_fn_target = true } },
    .{ "Function", AttrTargetMask{ .has_fn_target = true } },
    .{ "Local", AttrTargetMask{ .has_local_target = true } },
    .{ "LocalVar", AttrTargetMask{ .has_local_target = true } },
    .{ "Param", AttrTargetMask{ .has_param_target = true } },
    .{ "Struct", AttrTargetMask{ .has_struct_target = true } },
    .{ "StructField", AttrTargetMask{ .has_field_target = true } },
    .{ "Union", AttrTargetMask{ .has_union_target = true } },
    .{ "Variant", AttrTargetMask{ .has_variant_target = true } },
});

/// $O(1)$ static lookup map from `@repr(…)` integer/ABI argument names to discriminant bit widths.
const REPR_TAG_BITS_MAP = std.StaticStringMap(u8).initComptime(.{
    .{ "C", 32 },
    .{ "i16", 16 },
    .{ "i32", 32 },
    .{ "i64", 64 },
    .{ "i8", 8 },
    .{ "u16", 16 },
    .{ "u32", 32 },
    .{ "u64", 64 },
    .{ "u8", 8 },
});

/// $O(1)$ static lookup map from declaration `@attr` identifiers to `HeaderAttrKind`.
const HEADER_ATTR_MAP = std.StaticStringMap(HeaderAttrKind).initComptime(.{
    .{ "align", .align_attr },
    .{ "attribute_schema", .attribute_schema },
    .{ "cache_aligned", .cache_aligned },
    .{ "derive", .derive },
    .{ "export", .export_attr },
    .{ "extern", .extern_attr },
    .{ "from", .from },
    .{ "ifunc", .ifunc },
    .{ "linear", .linear },
    .{ "link_name", .link_name },
    .{ "link_section", .link_section },
    .{ "local", .local },
    .{ "max_stack", .max_stack },
    .{ "must_use", .must_use },
    .{ "no_alloc", .no_alloc },
    .{ "no_block", .no_block },
    .{ "no_panic", .no_panic },
    .{ "overload", .overload },
    .{ "packed", .packed_attr },
    .{ "repr", .repr },
    .{ "secret", .secret },
    .{ "soa", .soa },
    .{ "std_cap_boundary", .std_cap_boundary },
    .{ "zero_pad", .zero_pad },
});

/// $O(1)$ static lookup map from built-in `@derive` trait identifiers to `DeriveMask` bits.
const DERIVE_TRAIT_MAP = std.StaticStringMap(DeriveMask).initComptime(.{
    .{ "Clone", DeriveMask{ .has_clone = true } },
    .{ "Debug", DeriveMask{ .has_debug = true } },
    .{ "Eq", DeriveMask{ .has_eq = true } },
    .{ "Hash", DeriveMask{ .has_hash = true } },
});

// -------------------------------------- INTERNALS --------------------------------------

// -------------- Scoped Hash Key & Lexeme Helpers --------------

/// Packs `(scope_id, symbol_id, namespace)` into a collision-free 64-bit lookup key.
inline fn packScopedSymbolKey(scope_id: ScopeId, name: SymbolId, namespace: Namespace) u64 {
    const scope_part: u64 = @as(u64, scope_id.asInt() & 0x3FFF_FFFF);
    const ns_part: u64 = @as(u64, @backingInt(namespace)) << 30;
    const sym_part: u64 = @as(u64, name.asInt()) << 32;
    return sym_part | ns_part | scope_part;
}

/// Packs `(target_ty, trait_sym_idx)` into a collision-free 64-bit key for `SymbolTable.trait_impl_pairs`.
pub inline fn packTraitImplKey(target_ty: TypeId, trait_sym_idx: SymbolIndex) u64 {
    return (@as(u64, target_ty.toU32()) << 32) | @as(u64, trait_sym_idx.asInt());
}

/// Returns the UTF-8 source slice of `token_id`, or `""` for synthesized/out-of-bounds tokens.
pub inline fn extractTokenSlice(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    token_id: TokenIndex,
) []const u8 {
    if (token_id.isNone() or token_id.asInt() >= token_buffer.countTokens()) return "";
    const record = token_buffer.getToken(token_id);
    if (record.flags.is_synthesized or record.byte_len == 0) return "";
    const start_off: usize = record.byte_offset;
    const end_off: usize = @min(start_off + @as(usize, record.byte_len), source.len);
    if (start_off >= end_off) return "";
    return source[start_off..end_off];
}

/// Returns `true` if `kind` is an identifier token (`.ident`, `.type_ident`, or `.const_ident`).
pub inline fn isIdentifierToken(kind: TokenKind) bool {
    return kind == .ident or kind == .type_ident or kind == .const_ident;
}

/// Classifies the canonical `Namespace` of an identifier token kind.
pub inline fn classifyTokenNamespace(kind: TokenKind) Namespace {
    return switch (kind) {
        .type_ident, .prim_type, .kw_self_type => .type_ns,
        .const_ident => .const_ns,
        else => .value_ns,
    };
}

// ------- Bounded Levenshtein & Jaro-Winkler Typo Engine -------

/// Computes the Damerau-Levenshtein edit distance between `query` and `candidate` using a 130-byte stack row.
pub fn computeEditDistance(query: []const u8, candidate: []const u8) u16 {
    if (std.mem.eql(u8, query, candidate)) return 0;
    const query_len = @min(query.len, MAX_EDIT_DISTANCE_LEN);
    const cand_len = @min(candidate.len, MAX_EDIT_DISTANCE_LEN);
    if (query_len == 0) return @intCast(cand_len);
    if (cand_len == 0) return @intCast(query_len);

    // Case-only mismatch (e.g., ` my_var` vs `MyVar` or `MAX_VAL` vs `max_val`) gets distance 1:
    if (query_len == cand_len and std.ascii.eqlIgnoreCase(query[0..query_len], candidate[0..cand_len])) {
        return 1;
    }

    var prev_prev_row: [MAX_EDIT_DISTANCE_LEN + 1]u16 = @splat(0);
    var prev_row: [MAX_EDIT_DISTANCE_LEN + 1]u16 = undefined;
    var curr_row: [MAX_EDIT_DISTANCE_LEN + 1]u16 = undefined;

    var j: usize = 0;
    while (j <= cand_len) : (j += 1) {
        prev_row[j] = @intCast(j);
    }

    var i: usize = 1;
    while (i <= query_len) : (i += 1) {
        curr_row[0] = @intCast(i);
        j = 1;
        while (j <= cand_len) : (j += 1) {
            const subst_cost: u16 = if (query[i - 1] == candidate[j - 1]) 0 else 1;
            const deletion = prev_row[j] + 1;
            const insertion = curr_row[j - 1] + 1;
            const substitution = prev_row[j - 1] + subst_cost;
            var best = @min(deletion, @min(insertion, substitution));

            // Adjacent transposition check (`ab` <-> `ba`):
            if (i > 1 and j > 1 and
                query[i - 1] == candidate[j - 2] and
                query[i - 2] == candidate[j - 1])
            {
                best = @min(best, prev_prev_row[j - 2] + 1);
            }
            curr_row[j] = best;
        }
        prev_prev_row = prev_row;
        prev_row = curr_row;
    }
    return prev_row[cand_len];
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------------------ Scope Arena -------------------------

/// Contiguous Structure-of-Arrays lexical and module scope arena indexed by `ScopeId`.
pub const ScopeArena = struct {
    /// Backing allocator for the SoA scope columns.
    allocator: std.mem.Allocator,
    /// SoA storage of `ScopeRecord` items.
    scopes: std.MultiArrayList(ScopeRecord) = .empty,

    /// Initializes an empty `ScopeArena` bound to `allocator`.
    pub fn init(allocator: std.mem.Allocator) ScopeArena {
        return .{ .allocator = allocator };
    }

    /// Releases all scope storage.
    pub fn deinit(self: *ScopeArena) void {
        self.scopes.deinit(self.allocator);
        self.* = undefined;
    }

    /// Clears all scopes while retaining allocated capacity.
    pub fn resetRetainingCapacity(self: *ScopeArena) void {
        self.scopes.shrinkRetainingCapacity(0);
    }

    /// Allocates a new `ScopeRecord` and returns its `ScopeId`, inheriting flags and `enclosing_module`.
    pub fn allocScope(
        self: *ScopeArena,
        kind: ScopeKind,
        parent: ScopeId,
        owner_def_id: DefId,
        file_id: FileId,
        extra_flags: ScopeFlags,
    ) !ScopeId {
        var merged_flags = extra_flags;
        var enclosing_mod: ScopeId = .none;
        var depth: u16 = 0;

        if (!parent.isNone() and parent.asInt() < self.scopes.len) {
            const parent_rec = self.scopes.get(parent.asInt());
            if (parent_rec.depth >= MAX_SCOPE_DEPTH) return error.ScopeDepthExceeded;
            depth = parent_rec.depth + 1;
            merged_flags.is_unsafe_context = merged_flags.is_unsafe_context or parent_rec.flags.is_unsafe_context;
            merged_flags.is_async_context = merged_flags.is_async_context or parent_rec.flags.is_async_context;
            merged_flags.is_comptime_context = merged_flags.is_comptime_context or parent_rec.flags.is_comptime_context;
            merged_flags.is_inside_loop = merged_flags.is_inside_loop or
                parent_rec.flags.is_inside_loop or
                (kind == .loop_scope);
            merged_flags.is_inside_fallible_fn = merged_flags.is_inside_fallible_fn or
                parent_rec.flags.is_inside_fallible_fn;
            enclosing_mod = if (kind == .module_scope)
                ScopeId.fromInt(@intCast(self.scopes.len))
            else
                parent_rec.enclosing_module;
        } else if (kind == .module_scope) {
            enclosing_mod = ScopeId.fromInt(@intCast(self.scopes.len));
        }

        const new_id = ScopeId.fromInt(@intCast(self.scopes.len));
        try self.scopes.append(self.allocator, .{
            .kind = kind,
            .flags = merged_flags,
            .parent = parent,
            .enclosing_module = enclosing_mod,
            .owner_def_id = owner_def_id,
            .file_id = file_id,
            .depth = depth,
        });
        return new_id;
    }

    /// Retrieves the `ScopeRecord` for `scope_id` in $O(1)$ time.
    pub inline fn getScope(self: *const ScopeArena, scope_id: ScopeId) ScopeRecord {
        std.debug.assert(!scope_id.isNone() and scope_id.asInt() < self.scopes.len);
        return self.scopes.get(scope_id.asInt());
    }

    /// Returns `true` if `inner_scope` is located inside (or is identical to) `target_module_scope`.
    pub fn isWithinModule(
        self: *const ScopeArena,
        inner_scope: ScopeId,
        target_module_scope: ScopeId,
    ) bool {
        if (target_module_scope.isNone() or target_module_scope.asInt() == 0) return true;
        var cursor = inner_scope;
        var steps: usize = 0;
        while (!cursor.isNone() and cursor.asInt() < self.scopes.len and steps <= MAX_SCOPE_DEPTH) : (steps += 1) {
            if (cursor == target_module_scope) return true;
            const rec = self.scopes.get(cursor.asInt());
            if (rec.enclosing_module == target_module_scope) return true;
            cursor = rec.parent;
        }
        return false;
    }

    /// Returns the total number of allocated scopes.
    pub inline fn countScopes(self: *const ScopeArena) usize {
        return self.scopes.len;
    }
};

// ------------------------ Symbol Table ------------------------

/// Unified symbol table owning `ScopeArena`, `SymbolRecord` storage, `OverloadSet`s, and module maps.
pub const SymbolTable = struct {
    /// Backing allocator for symbol records, scope maps, and overload sets.
    allocator: std.mem.Allocator,
    /// Lexical and module scope hierarchy arena.
    scope_arena: ScopeArena,
    /// Flat array of all resolved `SymbolRecord` items indexed by `SymbolIndex`.
    symbols: std.ArrayListUnmanaged(SymbolRecord) = .empty,
    /// $O(1)$ lookup map from `packScopedSymbolKey(scope_id, name, namespace)` to `SymbolIndex`.
    scoped_map: std.AutoHashMapUnmanaged(u64, SymbolIndex) = .empty,
    /// Per-scope symbol lists for deterministic iteration, glob `use *`, and unused-binding checks.
    scope_members: std.AutoHashMapUnmanaged(u32, std.ArrayListUnmanaged(SymbolIndex)) = .empty,
    /// Explicit `@overload` function groups indexed by `SymbolRecord.target_symbol.asInt()`.
    overload_sets: std.ArrayListUnmanaged(OverloadSet) = .empty,
    /// Maps `FileId.asInt()` to its root `.module_scope` `ScopeId`.
    file_module_scopes: std.AutoHashMapUnmanaged(u32, ScopeId) = .empty,
    /// Maps module `SymbolId.asInt()` to its root `.module_scope` `ScopeId` for cross-file `mod` / `use`.
    named_module_scopes: std.AutoHashMapUnmanaged(u32, ScopeId) = .empty,
    /// Maps `(file_id << 32) | mod_name_sym` to the bound external file's root `.module_scope` `ScopeId`.
    external_module_scopes: std.AutoHashMapUnmanaged(u64, ScopeId) = .empty,
    /// Maps `DefId.asInt()` to its primary `SymbolIndex`.
    def_to_symbol: std.AutoHashMapUnmanaged(u32, SymbolIndex) = .empty,
    /// Maps nominal `TypeId.toU32()` to its defining `SymbolIndex` for field/variant/method lookup.
    type_to_symbol: std.AutoHashMapUnmanaged(u32, SymbolIndex) = .empty,
    /// Registered `@from` (`FromError`) `(source_err_ty, target_err_ty)` pairs for `?` upcasting (`DR-07`).
    from_error_pairs: std.AutoHashMapUnmanaged(u64, void) = .empty,
    /// Maps `(source_err_ty, target_err_ty)` to the conversion `fn` `DefId` when backed by an `@from fn`.
    from_error_fn_defs: std.AutoHashMapUnmanaged(u64, DefId) = .empty,
    /// Registered `(target_ty, trait_sym_idx)` pairs from `impl Trait for Type` and `@derive(Trait)`.
    trait_impl_pairs: std.AutoHashMapUnmanaged(u64, void) = .empty,
    /// Maps an `impl Trait for Type` method `SymbolIndex.asInt()` to its implemented `trait_sym` `SymbolIndex`.
    impl_method_trait: std.AutoHashMapUnmanaged(u32, SymbolIndex) = .empty,
    /// Deferred `use` imports queued during Pass 1 for Pass 2 cross-module resolution.
    pending_imports: std.ArrayListUnmanaged(PendingUseImport) = .empty,
    /// Global prelude `ScopeId` (`ScopeId.fromInt(0)`).
    prelude_scope: ScopeId = .none,
    /// Lazily populated `std::meta` module `ScopeId` (`DR-05` §3.3).
    std_meta_scope: ScopeId = .none,

    /// Initializes a new `SymbolTable` and pre-populates the global prelude scope (`ScopeId` `0`).
    pub fn init(allocator: std.mem.Allocator, interner: *StringInterner) !SymbolTable {
        var self = SymbolTable{
            .allocator = allocator,
            .scope_arena = ScopeArena.init(allocator),
        };
        errdefer self.deinit();
        try self.populateGlobalPrelude(interner);
        return self;
    }

    /// Releases all owned symbol tables, overload sets, and scope arenas.
    pub fn deinit(self: *SymbolTable) void {
        for (self.overload_sets.items) |*ov_set| {
            ov_set.deinit(self.allocator);
        }
        self.overload_sets.deinit(self.allocator);

        var member_iter = self.scope_members.valueIterator();
        while (member_iter.next()) |list_ptr| {
            list_ptr.deinit(self.allocator);
        }
        self.scope_members.deinit(self.allocator);

        self.symbols.deinit(self.allocator);
        self.scoped_map.deinit(self.allocator);
        self.file_module_scopes.deinit(self.allocator);
        self.named_module_scopes.deinit(self.allocator);
        self.external_module_scopes.deinit(self.allocator);
        self.def_to_symbol.deinit(self.allocator);
        self.type_to_symbol.deinit(self.allocator);
        self.from_error_pairs.deinit(self.allocator);
        self.from_error_fn_defs.deinit(self.allocator);
        self.trait_impl_pairs.deinit(self.allocator);
        self.impl_method_trait.deinit(self.allocator);
        self.pending_imports.deinit(self.allocator);
        self.scope_arena.deinit();
        self.* = undefined;
    }

    /// Resets the symbol table and re-initializes the global prelude while retaining allocated capacity.
    pub fn reset(self: *SymbolTable, interner: *StringInterner) !void {
        for (self.overload_sets.items) |*ov_set| {
            ov_set.deinit(self.allocator);
        }
        self.overload_sets.clearRetainingCapacity();

        var member_iter = self.scope_members.valueIterator();
        while (member_iter.next()) |list_ptr| {
            list_ptr.clearRetainingCapacity();
        }

        self.symbols.clearRetainingCapacity();
        self.scoped_map.clearRetainingCapacity();
        self.file_module_scopes.clearRetainingCapacity();
        self.named_module_scopes.clearRetainingCapacity();
        self.external_module_scopes.clearRetainingCapacity();
        self.def_to_symbol.clearRetainingCapacity();
        self.type_to_symbol.clearRetainingCapacity();
        self.from_error_pairs.clearRetainingCapacity();
        self.from_error_fn_defs.clearRetainingCapacity();
        self.trait_impl_pairs.clearRetainingCapacity();
        self.impl_method_trait.clearRetainingCapacity();
        self.pending_imports.clearRetainingCapacity();
        self.scope_arena.resetRetainingCapacity();
        self.std_meta_scope = .none;
        try self.populateGlobalPrelude(interner);
    }

    /// Binds an external `mod <name>;` declaration in `parent_file_id` to `target_scope`.
    pub fn bindExternalModuleScope(
        self: *SymbolTable,
        parent_file_id: FileId,
        mod_name: SymbolId,
        target_scope: ScopeId,
    ) !void {
        const key: u64 = (@as(u64, parent_file_id.asInt()) << 32) | @as(u64, mod_name.asInt());
        try self.external_module_scopes.put(self.allocator, key, target_scope);
    }

    /// Looks up a bound external `.module_scope` `ScopeId` for `mod <name>;` in `parent_file_id`.
    pub fn getExternalModuleScope(
        self: *const SymbolTable,
        parent_file_id: FileId,
        mod_name: SymbolId,
    ) ScopeId {
        const key: u64 = (@as(u64, parent_file_id.asInt()) << 32) | @as(u64, mod_name.asInt());
        if (self.external_module_scopes.get(key)) |bound_scope| {
            if (!bound_scope.isNone()) return bound_scope;
        }
        return .none;
    }

    /// Lazily populates `std::meta` and its 8 value-based reflection mirror stubs (`DR-05` §3.3).
    pub fn ensureStdMetaScope(self: *SymbolTable, interner: *StringInterner) !ScopeId {
        if (!self.std_meta_scope.isNone()) return self.std_meta_scope;

        const std_sym_id = try interner.intern("std");
        const existing_std = self.lookupInScopeDirect(
            self.prelude_scope,
            std_sym_id,
            NamespaceMask.VALUE_ONLY,
        );
        const std_scope = if (!existing_std.isNone() and
            !self.getSymbol(existing_std).target_scope.isNone())
            self.getSymbol(existing_std).target_scope
        else blk: {
            const new_std_scope = try self.scope_arena.allocScope(
                .module_scope,
                self.prelude_scope,
                .NONE,
                .none,
                .{},
            );
            _ = try self.defineSymbol(.{
                .name = std_sym_id,
                .name_text = interner.get(std_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = self.prelude_scope,
                .target_scope = new_std_scope,
            }, null);
            break :blk new_std_scope;
        };

        const meta_sym_id = try interner.intern("meta");
        const meta_scope = try self.scope_arena.allocScope(
            .module_scope,
            std_scope,
            .NONE,
            .none,
            .{},
        );
        _ = try self.defineSymbol(.{
            .name = meta_sym_id,
            .name_text = interner.get(meta_sym_id),
            .kind = .module_sym,
            .namespace = .value_ns,
            .visibility = .public,
            .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
            .scope_id = std_scope,
            .target_scope = meta_scope,
        }, null);

        const MirrorStub = struct { name: []const u8, kind: SymbolKind };
        const stubs = [8]MirrorStub{
            .{ .name = "EnumInfo", .kind = .struct_sym },
            .{ .name = "FieldInfo", .kind = .struct_sym },
            .{ .name = "MetaId", .kind = .struct_sym },
            .{ .name = "PrimKind", .kind = .enum_sym },
            .{ .name = "StructInfo", .kind = .struct_sym },
            .{ .name = "TypeInfo", .kind = .struct_sym },
            .{ .name = "TypeKind", .kind = .enum_sym },
            .{ .name = "VariantInfo", .kind = .struct_sym },
        };
        for (stubs) |stub| {
            const stub_sym_id = try interner.intern(stub.name);
            const member_scope = try self.scope_arena.allocScope(
                .nominal_type_scope,
                meta_scope,
                .NONE,
                .none,
                .{},
            );
            _ = try self.defineSymbol(.{
                .name = stub_sym_id,
                .name_text = interner.get(stub_sym_id),
                .kind = stub.kind,
                .namespace = .type_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = meta_scope,
                .target_scope = member_scope,
                .type_id = .err_ty,
            }, null);
        }

        self.std_meta_scope = meta_scope;
        return meta_scope;
    }

    /// Populates `ScopeId` `0` (`.global_prelude`) with the 19 primitives, 11 Type Groups, and built-in traits.
    fn populateGlobalPrelude(self: *SymbolTable, interner: *StringInterner) !void {
        self.prelude_scope = try self.scope_arena.allocScope(
            .global_prelude,
            .none,
            .NONE,
            .none,
            .{},
        );

        // [1] Register the 19 primitive types and 11 Constrained Type Groups (`DR-04` Section 1.1):
        for (BUILTIN_TYPES_AND_GROUPS) |entry| {
            const sym_name = try interner.intern(entry.name);
            const sym_idx = try self.appendSymbol(.{
                .name = sym_name,
                .name_text = interner.get(sym_name),
                .kind = if (entry.is_group) .type_group_sym else .type_alias_sym,
                .namespace = .type_ns,
                .visibility = .public,
                .flags = .{
                    .is_pub = true,
                    .is_used = true,
                    .is_builtin = true,
                    .is_type_group = entry.is_group,
                },
                .scope_id = self.prelude_scope,
                .type_id = entry.type_id,
            });
            try self.scoped_map.put(
                self.allocator,
                packScopedSymbolKey(self.prelude_scope, sym_name, .type_ns),
                sym_idx,
            );
            try self.type_to_symbol.put(self.allocator, entry.type_id.toU32(), sym_idx);
        }

        // [2] Register built-in generic `Result` and `Option` type constructors:
        for ([_][]const u8{ "Result", "Option" }) |adt_name| {
            const sym_name = try interner.intern(adt_name);
            const sym_idx = try self.appendSymbol(.{
                .name = sym_name,
                .name_text = interner.get(sym_name),
                .kind = .enum_sym,
                .namespace = .type_ns,
                .visibility = .public,
                .flags = .{
                    .is_pub = true,
                    .is_used = true,
                    .is_builtin = true,
                    .is_must_use = std.mem.eql(u8, adt_name, "Result"),
                },
                .scope_id = self.prelude_scope,
                .type_id = .err_ty,
            });
            try self.scoped_map.put(
                self.allocator,
                packScopedSymbolKey(self.prelude_scope, sym_name, .type_ns),
                sym_idx,
            );
        }

        // [3] Register built-in traits (`Clone`, `Debug`, `Display`, `Eq`, `FromError`, `Ord`, etc.):
        for (BUILTIN_TRAIT_NAMES) |trait_name| {
            const sym_name = try interner.intern(trait_name);
            const key = packScopedSymbolKey(self.prelude_scope, sym_name, .type_ns);
            if (self.scoped_map.contains(key)) continue;
            const sym_idx = try self.appendSymbol(.{
                .name = sym_name,
                .name_text = interner.get(sym_name),
                .kind = .trait_sym,
                .namespace = .type_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = self.prelude_scope,
                .type_id = .err_ty,
            });
            try self.scoped_map.put(self.allocator, key, sym_idx);
        }
    }

    /// Appends `record` to `self.symbols` and records it in `scope_members[record.scope_id]`.
    pub fn appendSymbol(self: *SymbolTable, record: SymbolRecord) !SymbolIndex {
        const sym_idx = SymbolIndex.fromInt(@intCast(self.symbols.items.len));
        try self.symbols.append(self.allocator, record);

        const gop = try self.scope_members.getOrPut(self.allocator, record.scope_id.asInt());
        if (!gop.found_existing) {
            gop.value_ptr.* = .empty;
        }
        try gop.value_ptr.append(self.allocator, sym_idx);
        return sym_idx;
    }

    /// Retrieves a read-only pointer to the `SymbolRecord` at `sym_idx`.
    pub inline fn getSymbol(self: *const SymbolTable, sym_idx: SymbolIndex) *const SymbolRecord {
        std.debug.assert(!sym_idx.isNone() and sym_idx.asInt() < self.symbols.items.len);
        return &self.symbols.items[sym_idx.asInt()];
    }

    /// Retrieves a mutable pointer to the `SymbolRecord` at `sym_idx`.
    pub inline fn getSymbolMut(self: *SymbolTable, sym_idx: SymbolIndex) *SymbolRecord {
        std.debug.assert(!sym_idx.isNone() and sym_idx.asInt() < self.symbols.items.len);
        return &self.symbols.items[sym_idx.asInt()];
    }

    /// Marks `sym_idx` (and its underlying target symbol if imported via `use`) as referenced.
    pub inline fn markSymbolUsed(self: *SymbolTable, sym_idx: SymbolIndex) void {
        if (sym_idx.isNone() or sym_idx.asInt() >= self.symbols.items.len) return;
        self.symbols.items[sym_idx.asInt()].flags.is_used = true;
        const target = self.symbols.items[sym_idx.asInt()].target_symbol;
        if (self.symbols.items[sym_idx.asInt()].kind == .use_alias_sym and
            !target.isNone() and target.asInt() < self.symbols.items.len)
        {
            self.symbols.items[target.asInt()].flags.is_used = true;
        }
    }

    /// Returns the slice of `SymbolIndex` members declared directly inside `scope_id`.
    pub fn getScopeMembers(self: *const SymbolTable, scope_id: ScopeId) []const SymbolIndex {
        if (self.scope_members.getPtr(scope_id.asInt())) |list_ptr| {
            return list_ptr.items;
        }
        return &.{};
    }

    /// Returns the total number of symbols in `self.symbols`.
    pub inline fn countSymbols(self: *const SymbolTable) u32 {
        return @intCast(self.symbols.items.len);
    }

    /// Returns the `OverloadSet` for `(scope_id, name)` if one is registered.
    pub fn getOverloadSet(
        self: *const SymbolTable,
        scope_id: ScopeId,
        name: SymbolId,
    ) ?*const OverloadSet {
        const sym_idx = self.lookupInScopeDirect(scope_id, name, NamespaceMask.VALUE_ONLY);
        if (sym_idx.isNone()) return null;
        const sym = self.getSymbol(sym_idx);
        if (sym.kind == .overload_group_sym and !sym.target_symbol.isNone() and
            sym.target_symbol.asInt() < self.overload_sets.items.len)
        {
            return &self.overload_sets.items[sym.target_symbol.asInt()];
        }
        return null;
    }

    /// Registers a symbol in `(record.scope_id, record.name, record.namespace)`, enforcing `E0408` and `@overload`.
    pub fn defineSymbol(
        self: *SymbolTable,
        record: SymbolRecord,
        diagnostic_sink: ?*DiagnosticSink,
    ) !SymbolIndex {
        const key = packScopedSymbolKey(record.scope_id, record.name, record.namespace);
        if (self.scoped_map.get(key)) |existing_idx| {
            const existing = self.getSymbol(existing_idx);

            // [1] Explicit `@overload` function group handling (`DR-02` Section 1.4):
            if (record.namespace == .value_ns and record.kind == .fn_sym and
                (existing.kind == .fn_sym or existing.kind == .overload_group_sym))
            {
                if (record.flags.is_overload and existing.flags.is_overload) {
                    const new_fn_idx = try self.appendSymbol(record);
                    if (!record.def_id.isNone()) {
                        try self.def_to_symbol.put(self.allocator, record.def_id.asInt(), new_fn_idx);
                    }
                    if (existing.kind == .overload_group_sym) {
                        const ov_idx = existing.target_symbol.asInt();
                        try self.overload_sets.items[ov_idx].members.append(self.allocator, new_fn_idx);
                        if (record.flags.is_pub) {
                            self.getSymbolMut(existing_idx).flags.is_pub = true;
                            self.getSymbolMut(existing_idx).visibility = .public;
                        }
                        return new_fn_idx;
                    }

                    // Upgrade the first `fn_sym` and the new `fn_sym` into an `OverloadSet`:
                    const ov_set_idx: u32 = @intCast(self.overload_sets.items.len);
                    var new_ov_set = OverloadSet{
                        .name = record.name,
                        .scope_id = record.scope_id,
                    };
                    try new_ov_set.members.append(self.allocator, existing_idx);
                    try new_ov_set.members.append(self.allocator, new_fn_idx);
                    try self.overload_sets.append(self.allocator, new_ov_set);

                    const group_sym_idx = try self.appendSymbol(.{
                        .name = record.name,
                        .name_text = record.name_text,
                        .kind = .overload_group_sym,
                        .namespace = .value_ns,
                        .visibility = if (existing.flags.is_pub or record.flags.is_pub) .public else .private,
                        .flags = .{
                            .is_pub = existing.flags.is_pub or record.flags.is_pub,
                            .is_overload = true,
                        },
                        .scope_id = record.scope_id,
                        .decl_span = existing.decl_span,
                        .target_symbol = SymbolIndex.fromInt(ov_set_idx),
                    });
                    try self.scoped_map.put(self.allocator, key, group_sym_idx);
                    return new_fn_idx;
                }

                // Missing `@overload` on one or both functions in the same scope -> emit `E0408`:
                if (diagnostic_sink) |sink| {
                    try emitDuplicateDefinitionDiagnostic(
                        sink,
                        record.name_text,
                        record.decl_span,
                        existing.decl_span,
                        true,
                    );
                }
                const dup_fn_idx = try self.appendSymbol(record);
                if (!record.def_id.isNone()) {
                    try self.def_to_symbol.put(self.allocator, record.def_id.asInt(), dup_fn_idx);
                }
                return dup_fn_idx;
            }

            // [2] Local variable shadowing inside `.block_scope` / `.match_arm_scope` is permitted across nested blocks,
            //     and within the same block `let x = …; let x = …;` rebinds `x` cleanly in CoreX/Rust style:
            const scope_kind = self.scope_arena.getScope(record.scope_id).kind;
            if (scope_kind == .block_scope or scope_kind == .match_arm_scope or scope_kind == .loop_scope) {
                if (record.kind == .local_let_sym or record.kind == .local_var_sym) {
                    const shadowed_idx = try self.appendSymbol(record);
                    try self.scoped_map.put(self.allocator, key, shadowed_idx);
                    return shadowed_idx;
                }
            }

            // [3] Duplicate top-level or parameter definition in the same scope and namespace -> emit `E0408`:
            if (diagnostic_sink) |sink| {
                if (!existing.flags.is_imported or !record.flags.is_imported) {
                    try emitDuplicateDefinitionDiagnostic(
                        sink,
                        record.name_text,
                        record.decl_span,
                        existing.decl_span,
                        false,
                    );
                }
            }
            const fallback_idx = try self.appendSymbol(record);
            if (!record.def_id.isNone()) {
                try self.def_to_symbol.put(self.allocator, record.def_id.asInt(), fallback_idx);
            }
            return fallback_idx;
        }

        const sym_idx = try self.appendSymbol(record);
        try self.scoped_map.put(self.allocator, key, sym_idx);
        if (!record.def_id.isNone()) {
            try self.def_to_symbol.put(self.allocator, record.def_id.asInt(), sym_idx);
        }
        return sym_idx;
    }

    /// Looks up `name` in `scope_id` (without walking parents) across the namespaces in `mask`.
    pub fn lookupInScopeDirect(
        self: *const SymbolTable,
        scope_id: ScopeId,
        name: SymbolId,
        mask: NamespaceMask,
    ) SymbolIndex {
        if (scope_id.isNone() or name.isNone()) return .none;
        if (mask.is_value) {
            if (self.scoped_map.get(packScopedSymbolKey(scope_id, name, .value_ns))) |idx| return idx;
        }
        if (mask.is_const) {
            if (self.scoped_map.get(packScopedSymbolKey(scope_id, name, .const_ns))) |idx| return idx;
        }
        if (mask.is_type) {
            if (self.scoped_map.get(packScopedSymbolKey(scope_id, name, .type_ns))) |idx| return idx;
        }
        return .none;
    }

    /// Walks up the lexical parent chain from `start_scope` to `.global_prelude` looking up `name` in `mask`.
    pub fn lookupLexical(
        self: *const SymbolTable,
        start_scope: ScopeId,
        name: SymbolId,
        mask: NamespaceMask,
    ) LookupResult {
        if (name.isNone()) return .not_found;
        var cursor = start_scope;
        var steps: usize = 0;
        while (!cursor.isNone() and cursor.asInt() < self.scope_arena.countScopes() and steps <= MAX_SCOPE_DEPTH) : (steps += 1) {
            const sym_idx = self.lookupInScopeDirect(cursor, name, mask);
            if (!sym_idx.isNone()) {
                return self.checkSymbolVisibility(sym_idx, start_scope);
            }
            cursor = self.scope_arena.getScope(cursor).parent;
        }
        return .not_found;
    }

    /// Looks up `name` inside `target_scope` from `caller_scope`, enforcing `pub` module boundary rules (`E0409`).
    pub fn lookupInTargetScope(
        self: *const SymbolTable,
        target_scope: ScopeId,
        caller_scope: ScopeId,
        name: SymbolId,
        mask: NamespaceMask,
    ) LookupResult {
        const sym_idx = self.lookupInScopeDirect(target_scope, name, mask);
        if (sym_idx.isNone()) return .not_found;
        return self.checkSymbolVisibility(sym_idx, caller_scope);
    }

    /// Verifies whether `sym_idx` is visible from `caller_scope`, unwrapping `use_alias_sym` targets.
    pub fn checkSymbolVisibility(
        self: *const SymbolTable,
        sym_idx: SymbolIndex,
        caller_scope: ScopeId,
    ) LookupResult {
        const sym = self.getSymbol(sym_idx);
        const resolved_idx = if (sym.kind == .use_alias_sym and !sym.target_symbol.isNone())
            sym.target_symbol
        else
            sym_idx;

        if (sym.flags.is_pub or sym.flags.is_builtin) {
            return .{ .found = resolved_idx };
        }
        const decl_scope = self.scope_arena.getScope(sym.scope_id);
        if (decl_scope.enclosing_module.isNone() or
            self.scope_arena.isWithinModule(caller_scope, decl_scope.enclosing_module))
        {
            return .{ .found = resolved_idx };
        }
        return .{ .private_error = resolved_idx };
    }

    /// Finds the closest visible candidate identifier to `query_text` using bounded Damerau-Levenshtein distance.
    pub fn suggestClosestSymbol(
        self: *const SymbolTable,
        start_scope: ScopeId,
        query_text: []const u8,
        mask: NamespaceMask,
    ) ?[]const u8 {
        if (query_text.len < 2 or query_text.len > MAX_EDIT_DISTANCE_LEN) return null;
        const max_allowed_dist: u16 = if (query_text.len <= 4) 1 else if (query_text.len <= 8) 2 else 3;

        var best_candidate: ?[]const u8 = null;
        var best_distance: u16 = max_allowed_dist + 1;

        var cursor = start_scope;
        var steps: usize = 0;
        while (!cursor.isNone() and cursor.asInt() < self.scope_arena.countScopes() and steps <= MAX_SCOPE_DEPTH) : (steps += 1) {
            for (self.getScopeMembers(cursor)) |sym_idx| {
                const sym = self.getSymbol(sym_idx);
                if (!mask.contains(sym.namespace)) continue;
                if (sym.name_text.len == 0 or sym.name_text.len > MAX_EDIT_DISTANCE_LEN) continue;
                if (std.mem.startsWith(u8, sym.name_text, "_")) continue;

                // Skip candidates whose length difference alone exceeds `max_allowed_dist`:
                const len_diff = if (query_text.len > sym.name_text.len)
                    query_text.len - sym.name_text.len
                else
                    sym.name_text.len - query_text.len;
                if (len_diff > max_allowed_dist) continue;

                const dist = computeEditDistance(query_text, sym.name_text);
                if (dist > 0 and dist <= max_allowed_dist) {
                    if (dist < best_distance or
                        (dist == best_distance and best_candidate != null and
                            std.mem.order(u8, sym.name_text, best_candidate.?) == .lt))
                    {
                        best_distance = dist;
                        best_candidate = sym.name_text;
                    }
                }
            }
            cursor = self.scope_arena.getScope(cursor).parent;
        }
        return best_candidate;
    }

    /// Finds the closest member/field/variant in `target_scope` for `query_text`.
    pub fn suggestClosestInScope(
        self: *const SymbolTable,
        target_scope: ScopeId,
        query_text: []const u8,
        mask: NamespaceMask,
    ) ?[]const u8 {
        if (target_scope.isNone() or query_text.len < 2 or query_text.len > MAX_EDIT_DISTANCE_LEN) return null;
        const max_allowed_dist: u16 = if (query_text.len <= 4) 1 else if (query_text.len <= 8) 2 else 3;

        var best_candidate: ?[]const u8 = null;
        var best_distance: u16 = max_allowed_dist + 1;

        for (self.getScopeMembers(target_scope)) |sym_idx| {
            const sym = self.getSymbol(sym_idx);
            if (!mask.contains(sym.namespace)) continue;
            if (sym.name_text.len == 0 or sym.name_text.len > MAX_EDIT_DISTANCE_LEN) continue;
            const dist = computeEditDistance(query_text, sym.name_text);
            if (dist > 0 and dist <= max_allowed_dist) {
                if (dist < best_distance or
                    (dist == best_distance and best_candidate != null and
                        std.mem.order(u8, sym.name_text, best_candidate.?) == .lt))
                {
                    best_distance = dist;
                    best_candidate = sym.name_text;
                }
            }
        }
        return best_candidate;
    }

    /// Emits `W0402` (`w0402_unused_binding`) for any unreferenced local bindings/parameters in `scope_id`.
    pub fn checkUnusedBindingsInScope(
        self: *const SymbolTable,
        scope_id: ScopeId,
        interner: *StringInterner,
        diagnostic_sink: *DiagnosticSink,
    ) !void {
        for (self.getScopeMembers(scope_id)) |sym_idx| {
            const sym = self.getSymbol(sym_idx);
            if (sym.kind != .local_let_sym and sym.kind != .local_var_sym and sym.kind != .param_sym) {
                continue;
            }
            if (sym.flags.is_used or sym.flags.is_builtin) continue;
            if (sym.name_text.len == 0 or
                std.mem.startsWith(u8, sym.name_text, "_") or
                std.mem.eql(u8, sym.name_text, "self"))
            {
                continue;
            }
            if (sym.decl_span.file_id.isNone()) continue;

            const prefixed_name = try std.fmt.allocPrint(
                diagnostic_sink.arena.asAllocator(),
                "_{s}",
                .{sym.name_text},
            );
            const replacement_id = try interner.intern(prefixed_name);
            const edit = [1]TextEdit{.{
                .file_id = sym.decl_span.file_id,
                .start_byte = sym.decl_span.start_byte,
                .end_byte = sym.decl_span.end_byte,
                .replacement_id = replacement_id,
            }};
            const fix = [1]SuggestedFix{.{
                .message = "prefix the unused binding with `_` to silence this warning",
                .applicability = .machine_applicable,
                .priority = .lint_idiom,
                .edits = &edit,
            }};
            const label_msg = try std.fmt.allocPrint(
                diagnostic_sink.arena.asAllocator(),
                "unused binding `{s}` is never read",
                .{sym.name_text},
            );
            const labels = [1]LabeledSpan{.{
                .span = sym.decl_span,
                .label = label_msg,
                .style = .primary,
            }};
            const main_msg = try std.fmt.allocPrint(
                diagnostic_sink.arena.asAllocator(),
                "unused variable or parameter `{s}`",
                .{sym.name_text},
            );
            const notes = [1][]const u8{
                "help: prefix intentional unused bindings with an underscore (`_name`)",
            };
            try diagnostic_sink.emit(.{
                .code = .w0402_unused_binding,
                .severity = .warning,
                .primary_span = sym.decl_span,
                .message = main_msg,
                .labels = &labels,
                .notes = &notes,
                .suggestions = &fix,
            });
        }
    }
};

// ---------------- Diagnostic Emission Helpers -----------------

/// Emits `W0402` (`w0402_unused_binding`) for any unreferenced local bindings/parameters in `scope_id`.
pub fn checkUnusedBindingsInScope(
    sym_table: *const SymbolTable,
    scope_id: ScopeId,
    interner: *StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
) !void {
    const sink = diagnostic_sink orelse return;
    try sym_table.checkUnusedBindingsInScope(scope_id, interner, sink);
}

/// Emits `E0408` (`e0408_duplicate_definition`) with primary and secondary labels.
pub fn emitDuplicateDefinitionDiagnostic(
    sink: *DiagnosticSink,
    name_text: []const u8,
    dup_span: Span,
    first_span: Span,
    is_missing_overload_attr: bool,
) !void {
    const arena_alloc = sink.arena.asAllocator();
    const main_msg = try std.fmt.allocPrint(
        arena_alloc,
        "duplicate definition of `{s}` in the same scope",
        .{name_text},
    );
    const primary_label = try std.fmt.allocPrint(
        arena_alloc,
        "`{s}` redefined here",
        .{name_text},
    );
    const secondary_label = try std.fmt.allocPrint(
        arena_alloc,
        "previous definition of `{s}` was here",
        .{name_text},
    );

    if (!first_span.file_id.isNone()) {
        const labels = [2]LabeledSpan{
            .{ .span = dup_span, .label = primary_label, .style = .primary },
            .{ .span = first_span, .label = secondary_label, .style = .secondary },
        };
        const help_note = if (is_missing_overload_attr)
            "help: annotate all overloaded functions in an overload family with `@overload`"
        else
            "help: rename one of the declarations so each symbol in the scope is unique";
        const notes = [1][]const u8{help_note};
        _ = try sink.emit(.{
            .code = .e0408_duplicate_definition,
            .severity = .err,
            .primary_span = dup_span,
            .message = main_msg,
            .labels = &labels,
            .notes = &notes,
        });
    } else {
        const labels = [1]LabeledSpan{
            .{ .span = dup_span, .label = primary_label, .style = .primary },
        };
        _ = try sink.emit(.{
            .code = .e0408_duplicate_definition,
            .severity = .err,
            .primary_span = dup_span,
            .message = main_msg,
            .labels = &labels,
        });
    }
}

/// Emits `E0403` (`e0403_unresolved_symbol`) with an optional Levenshtein "did you mean?" hint.
pub fn emitUnresolvedSymbolDiagnostic(
    sink: *DiagnosticSink,
    interner: *StringInterner,
    name_text: []const u8,
    use_span: Span,
    suggestion_opt: ?[]const u8,
) !void {
    const arena_alloc = sink.arena.asAllocator();
    const main_msg = try std.fmt.allocPrint(
        arena_alloc,
        "unresolved symbol `{s}` in this scope",
        .{name_text},
    );
    const primary_label = if (suggestion_opt) |sug|
        try std.fmt.allocPrint(arena_alloc, "not found in this scope; did you mean `{s}`?", .{sug})
    else
        try std.fmt.allocPrint(arena_alloc, "cannot find `{s}` in this scope", .{name_text});

    const labels = [1]LabeledSpan{
        .{ .span = use_span, .label = primary_label, .style = .primary },
    };

    if (suggestion_opt) |sug| {
        const rep_id = try interner.intern(sug);
        const edit = [1]TextEdit{.{
            .file_id = use_span.file_id,
            .start_byte = use_span.start_byte,
            .end_byte = use_span.end_byte,
            .replacement_id = rep_id,
        }};
        const fix_msg = try std.fmt.allocPrint(arena_alloc, "replace with `{s}`", .{sug});
        const fix = [1]SuggestedFix{.{
            .message = fix_msg,
            .applicability = .maybe_incorrect,
            .priority = .type_migration,
            .edits = &edit,
        }};
        _ = try sink.emit(.{
            .code = .e0403_unresolved_symbol,
            .severity = .err,
            .primary_span = use_span,
            .message = main_msg,
            .labels = &labels,
            .suggestions = &fix,
        });
    } else {
        _ = try sink.emit(.{
            .code = .e0403_unresolved_symbol,
            .severity = .err,
            .primary_span = use_span,
            .message = main_msg,
            .labels = &labels,
        });
    }
}

/// Emits `E0409` (`e0409_private_symbol_access`) pointing to both the access site and private declaration.
pub fn emitPrivateAccessDiagnostic(
    sink: *DiagnosticSink,
    sym: *const SymbolRecord,
    access_span: Span,
) !void {
    const arena_alloc = sink.arena.asAllocator();
    const main_msg = try std.fmt.allocPrint(
        arena_alloc,
        "symbol `{s}` is private and cannot be accessed outside its defining module",
        .{sym.name_text},
    );
    const primary_label = try std.fmt.allocPrint(
        arena_alloc,
        "`{s}` is private here",
        .{sym.name_text},
    );
    const secondary_label = try std.fmt.allocPrint(
        arena_alloc,
        "`{s}` is declared without `pub` here",
        .{sym.name_text},
    );

    if (!sym.decl_span.file_id.isNone()) {
        const labels = [2]LabeledSpan{
            .{ .span = access_span, .label = primary_label, .style = .primary },
            .{ .span = sym.decl_span, .label = secondary_label, .style = .secondary },
        };
        const notes = [1][]const u8{
            "help: mark the declaration with `pub` to export it across module boundaries",
        };
        _ = try sink.emit(.{
            .code = .e0409_private_symbol_access,
            .severity = .err,
            .primary_span = access_span,
            .message = main_msg,
            .labels = &labels,
            .notes = &notes,
        });
    } else {
        const labels = [1]LabeledSpan{
            .{ .span = access_span, .label = primary_label, .style = .primary },
        };
        _ = try sink.emit(.{
            .code = .e0409_private_symbol_access,
            .severity = .err,
            .primary_span = access_span,
            .message = main_msg,
            .labels = &labels,
        });
    }
}

// --------- Module Item Collection & `use` Resolution ----------

/// Combined item modifier, `@derive`, `@attribute_schema`, and Phase 6 contract metadata extracted from CST headers.
pub const ItemHeaderMetadata = struct {
    /// Extracted item visibility, modifier, and attribute flags.
    flags: SymbolFlags = .{},
    /// Parsed `@derive(Eq, Hash, Debug, Clone)` bitmask.
    derive_mask: DeriveMask = .{},
    /// Parsed `@attribute_schema(targets = …)` target bitmask.
    attr_target_mask: AttrTargetMask = .{},
    /// Phase 6 contract, ownership, secret, zero-pad, and FFI attribute flags (`DR-17`, `DR-20`).
    contract_flags: DeclContractFlags = .{},
    /// Explicit stack frame budget in bytes when `contract_flags.has_max_stack` is `true` (`@max_stack(N)`).
    max_stack_bytes: u32 = 0,
    /// Capability bits explicitly emitted at an `@std_cap_boundary` (`DR-17` §2.3).
    cap_emits_mask: u16 = 0,
    /// Capability bits explicitly cleared/trusted at an `@std_cap_boundary` (`DR-17` §2.3).
    cap_clears_mask: u16 = 0,
    /// Inline decoded section name buffer when `contract_flags.has_link_section` is `true`.
    link_section_buf: [256]u8 = undefined,
    /// Valid byte length inside `link_section_buf`.
    link_section_len: u16 = 0,
    /// Inline decoded external symbol name buffer when `contract_flags.has_link_name` is `true`.
    link_name_buf: [256]u8 = undefined,
    /// Valid byte length inside `link_name_buf`.
    link_name_len: u16 = 0,
    /// Explicit discriminant width in bits on `@repr(…)` items (`0` = default).
    repr_tag_bits: u8 = 0,
    /// Explicit power-of-two alignment encoded as `log2(align) + 1` (`0` = default).
    explicit_align_log2_plus1: u8 = 0,

    /// Returns the decoded `@link_section` byte slice.
    pub inline fn asLinkSectionSlice(self: *const ItemHeaderMetadata) []const u8 {
        return self.link_section_buf[0..self.link_section_len];
    }

    /// Returns the decoded `@link_name` byte slice.
    pub inline fn asLinkNameSlice(self: *const ItemHeaderMetadata) []const u8 {
        return self.link_name_buf[0..self.link_name_len];
    }
};

/// Returns `true` if `section_name` targets a forbidden constructor/destructor/TLS/interpose section (`E0327`).
pub fn isForbiddenExecutableSection(section_name: []const u8) bool {
    const trimmed_full = std.mem.trim(u8, section_name, " \t\r\n");
    if (trimmed_full.len == 0) return false;

    var seg_iter = std.mem.splitScalar(u8, trimmed_full, ',');
    while (seg_iter.next()) |raw_seg| {
        const seg_trimmed = std.mem.trim(u8, raw_seg, " \t\r\n");
        if (seg_trimmed.len == 0) continue;

        var lower_buf: [128]u8 = undefined;
        const copy_len = @min(seg_trimmed.len, lower_buf.len);
        for (seg_trimmed[0..copy_len], 0..) |byte_val, i| {
            lower_buf[i] = std.ascii.toLower(byte_val);
        }
        const seg = lower_buf[0..copy_len];

        if (std.mem.eql(u8, seg, ".init") or
            std.mem.startsWith(u8, seg, ".init.") or
            std.mem.startsWith(u8, seg, ".init_array") or
            std.mem.eql(u8, seg, ".fini") or
            std.mem.startsWith(u8, seg, ".fini.") or
            std.mem.startsWith(u8, seg, ".fini_array") or
            std.mem.startsWith(u8, seg, ".preinit_array") or
            std.mem.startsWith(u8, seg, ".ctors") or
            std.mem.startsWith(u8, seg, ".dtors") or
            std.mem.startsWith(u8, seg, ".crt$xc") or
            std.mem.startsWith(u8, seg, ".crt$xi") or
            std.mem.startsWith(u8, seg, ".crt$xl") or
            std.mem.startsWith(u8, seg, ".crt$xp") or
            std.mem.startsWith(u8, seg, ".crt$xt") or
            std.mem.eql(u8, seg, ".tls") or
            std.mem.startsWith(u8, seg, ".tls.") or
            std.mem.startsWith(u8, seg, ".tls$") or
            std.mem.startsWith(u8, seg, "__mod_init_func") or
            std.mem.startsWith(u8, seg, "__mod_term_func") or
            std.mem.startsWith(u8, seg, "__interpose") or
            std.mem.startsWith(u8, seg, "__kmod_init") or
            std.mem.startsWith(u8, seg, "__kmod_term") or
            std.mem.startsWith(u8, seg, "__wasm_call_ctors"))
        {
            return true;
        }
    }
    return false;
}

/// Strips outer quotes (`"…"` or `r#"…"#`) and decodes standard `\xNN` / `\u{…}` escapes into `out_buf`.
fn unquoteAttrStringLexeme(lexeme: []const u8, out_buf: *[256]u8) []const u8 {
    if (std.mem.startsWith(u8, lexeme, "r")) {
        var hash_count: usize = 0;
        var idx: usize = 1;
        while (idx < lexeme.len and lexeme[idx] == '#') : (idx += 1) {
            hash_count += 1;
        }
        if (idx < lexeme.len and lexeme[idx] == '"' and lexeme.len >= idx + 2 + hash_count) {
            return lexeme[idx + 1 .. lexeme.len - 1 - hash_count];
        }
    }
    const inner = if (lexeme.len >= 2 and lexeme[0] == '"' and lexeme[lexeme.len - 1] == '"')
        lexeme[1 .. lexeme.len - 1]
    else
        lexeme;
    if (std.mem.indexOfScalar(u8, inner, '\\') == null) return inner;

    var out_len: usize = 0;
    var i: usize = 0;
    while (i < inner.len and out_len < out_buf.len) {
        if (inner[i] != '\\' or i + 1 >= inner.len) {
            out_buf[out_len] = inner[i];
            out_len += 1;
            i += 1;
            continue;
        }
        const esc_ch = inner[i + 1];
        i += 2;
        switch (esc_ch) {
            'n' => {
                out_buf[out_len] = '\n';
                out_len += 1;
            },
            'r' => {
                out_buf[out_len] = '\r';
                out_len += 1;
            },
            't' => {
                out_buf[out_len] = '\t';
                out_len += 1;
            },
            '0' => {
                out_buf[out_len] = 0;
                out_len += 1;
            },
            '\\', '"', '\'' => {
                out_buf[out_len] = esc_ch;
                out_len += 1;
            },
            'x' => {
                if (i + 2 <= inner.len) {
                    const hi_nibble = std.fmt.charToDigit(inner[i], 16) catch null;
                    const lo_nibble = std.fmt.charToDigit(inner[i + 1], 16) catch null;
                    if (hi_nibble != null and lo_nibble != null) {
                        out_buf[out_len] = (@as(u8, hi_nibble.?) << 4) | @as(u8, lo_nibble.?);
                        out_len += 1;
                        i += 2;
                        continue;
                    }
                }
                out_buf[out_len] = 'x';
                out_len += 1;
            },
            'u' => {
                if (i < inner.len and inner[i] == '{') {
                    if (std.mem.indexOfScalarPos(u8, inner, i + 1, '}')) |close_brace| {
                        const hex_digits = inner[i + 1 .. close_brace];
                        if (std.fmt.parseInt(u21, hex_digits, 16)) |codepoint| {
                            if (std.unicode.utf8ValidCodepoint(codepoint) and out_len + 4 <= out_buf.len) {
                                const encoded_len = std.unicode.utf8Encode(
                                    codepoint,
                                    out_buf[out_len .. out_len + 4],
                                ) catch 0;
                                out_len += encoded_len;
                                i = close_brace + 1;
                                continue;
                            }
                        } else |_| {}
                    }
                }
                out_buf[out_len] = 'u';
                out_len += 1;
            },
            else => {
                out_buf[out_len] = esc_ch;
                out_len += 1;
            },
        }
    }
    return out_buf[0..out_len];
}

/// Extracts an unsigned 32-bit integer value from a literal lexeme (allowing `_` separators and `0x`/`0b`/`0o` prefixes).
fn extractAttrUint32Lexeme(lexeme: []const u8) ?u32 {
    var clean_buf: [64]u8 = undefined;
    var clean_len: usize = 0;
    for (lexeme) |byte_val| {
        if (byte_val == '_') continue;
        if (clean_len >= clean_buf.len) return null;
        clean_buf[clean_len] = byte_val;
        clean_len += 1;
    }
    return std.fmt.parseInt(u32, clean_buf[0..clean_len], 0) catch null;
}

/// Extracts `emits` and `clears` capability bitmasks from `@std_cap_boundary(…)` inside `[arg_start .. attr_end)`.
fn extractStdCapBoundaryMasks(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    arg_start: usize,
    attr_end: usize,
    emits_out: *u16,
    clears_out: *u16,
) void {
    var active_mode: enum { emits_mode, clears_mode } = .clears_mode;
    var arg_cur = arg_start;
    while (arg_cur < attr_end) : (arg_cur += 1) {
        const arg_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(arg_cur)));
        if (arg_leaf.subtree_size > 1 or arg_leaf.token.isNone() or
            arg_leaf.token.asInt() >= token_buffer.countTokens())
        {
            continue;
        }
        const arg_kind = token_buffer.getToken(arg_leaf.token).kind;
        if (!isIdentifierToken(arg_kind) and arg_kind != .string_lit) continue;
        const raw_lex = extractTokenSlice(source, token_buffer, arg_leaf.token);
        var unquote_buf: [256]u8 = undefined;
        const ident_lex = if (arg_kind == .string_lit)
            unquoteAttrStringLexeme(raw_lex, &unquote_buf)
        else
            raw_lex;

        const next_tok = peekNextAttrLeafToken(token_buffer, cst_arena, arg_cur + 1, attr_end);
        const next_kind: TokenKind = if (!next_tok.isNone())
            token_buffer.getToken(next_tok).kind
        else
            .eof;
        if (next_kind == .eq or next_kind == .colon) {
            if (std.mem.eql(u8, ident_lex, "emits")) {
                active_mode = .emits_mode;
            } else if (std.mem.eql(u8, ident_lex, "clears")) {
                active_mode = .clears_mode;
            }
            continue;
        }
        if (CAPABILITY_NAME_MAP.get(ident_lex)) |cap_bit| {
            switch (active_mode) {
                .emits_mode => emits_out.* |= cap_bit,
                .clears_mode => clears_out.* |= cap_bit,
            }
        }
    }
}

/// Extracts `@repr(C | c | packed | align = N | u8..u64 | i8..i64)` metadata inside `[arg_start .. attr_end)`.
fn extractReprAttr(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    arg_start: usize,
    attr_end: usize,
    meta: *ItemHeaderMetadata,
) void {
    var is_expecting_align = false;
    var arg_cur = arg_start;
    while (arg_cur < attr_end) : (arg_cur += 1) {
        const arg_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(arg_cur)));
        if (arg_leaf.subtree_size > 1 or arg_leaf.token.isNone() or
            arg_leaf.token.asInt() >= token_buffer.countTokens())
        {
            continue;
        }
        const arg_kind = token_buffer.getToken(arg_leaf.token).kind;
        if (arg_kind == .int_lit and is_expecting_align) {
            const align_lex = extractTokenSlice(source, token_buffer, arg_leaf.token);
            if (extractAttrUint32Lexeme(align_lex)) |align_bytes| {
                if (align_bytes > 0 and std.math.isPowerOfTwo(align_bytes) and align_bytes <= (@as(u32, 1) << 29)) {
                    const log2_plus1: u8 = @as(u8, @intCast(std.math.log2_int(u32, align_bytes))) + 1;
                    meta.explicit_align_log2_plus1 = @max(meta.explicit_align_log2_plus1, log2_plus1);
                }
            }
            is_expecting_align = false;
            continue;
        }
        if (arg_kind == .eq or arg_kind == .lparen or arg_kind == .rparen) continue;
        if (arg_kind == .comma) {
            is_expecting_align = false;
            continue;
        }
        if (arg_kind != .prim_type and !isIdentifierToken(arg_kind)) continue;
        const repr_lex = extractTokenSlice(source, token_buffer, arg_leaf.token);
        if (std.mem.eql(u8, repr_lex, "C") or std.mem.eql(u8, repr_lex, "c")) {
            meta.contract_flags.is_repr_c = true;
            if (meta.repr_tag_bits == 0) meta.repr_tag_bits = 32;
        } else if (std.mem.eql(u8, repr_lex, "packed")) {
            meta.contract_flags.is_packed = true;
        } else if (std.mem.eql(u8, repr_lex, "align")) {
            is_expecting_align = true;
        } else if (REPR_TAG_BITS_MAP.get(repr_lex)) |tag_bits| {
            meta.repr_tag_bits = tag_bits;
        }
    }
}

/// Extracts `@align(N)` power-of-two alignment inside `[arg_start .. attr_end)`.
fn extractAlignAttr(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    arg_start: usize,
    attr_end: usize,
    meta: *ItemHeaderMetadata,
) void {
    var arg_cur = arg_start;
    while (arg_cur < attr_end) : (arg_cur += 1) {
        const arg_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(arg_cur)));
        if (arg_leaf.subtree_size > 1 or arg_leaf.token.isNone() or
            arg_leaf.token.asInt() >= token_buffer.countTokens())
        {
            continue;
        }
        if (token_buffer.getToken(arg_leaf.token).kind == .int_lit) {
            const align_lex = extractTokenSlice(source, token_buffer, arg_leaf.token);
            if (extractAttrUint32Lexeme(align_lex)) |align_bytes| {
                if (align_bytes > 0 and std.math.isPowerOfTwo(align_bytes) and align_bytes <= (@as(u32, 1) << 29)) {
                    const log2_plus1: u8 = @as(u8, @intCast(std.math.log2_int(u32, align_bytes))) + 1;
                    meta.explicit_align_log2_plus1 = @max(meta.explicit_align_log2_plus1, log2_plus1);
                }
            }
            break;
        }
    }
}

/// Extracts `@link_name("…")` external symbol name inside `[arg_start .. attr_end)`.
fn extractLinkNameAttr(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    arg_start: usize,
    attr_end: usize,
    meta: *ItemHeaderMetadata,
) void {
    var name_cur = arg_start;
    while (name_cur < attr_end) : (name_cur += 1) {
        const name_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(name_cur)));
        if (name_leaf.subtree_size <= 1 and !name_leaf.token.isNone() and
            name_leaf.token.asInt() < token_buffer.countTokens())
        {
            if (token_buffer.getToken(name_leaf.token).kind == .string_lit) {
                const name_raw = extractTokenSlice(source, token_buffer, name_leaf.token);
                var unesc_buf: [256]u8 = undefined;
                const sym_name = unquoteAttrStringLexeme(name_raw, &unesc_buf);
                var has_ctrl_byte = false;
                for (sym_name) |byte_val| {
                    if (byte_val == 0 or byte_val == '\n' or byte_val == '\r' or (byte_val < 0x20 and byte_val != 0x01)) {
                        has_ctrl_byte = true;
                        break;
                    }
                }
                if (!has_ctrl_byte and sym_name.len > 0) {
                    const copy_len = @min(sym_name.len, meta.link_name_buf.len);
                    @memcpy(meta.link_name_buf[0..copy_len], sym_name[0..copy_len]);
                    meta.link_name_len = @intCast(copy_len);
                    meta.contract_flags.has_link_name = true;
                }
                break;
            }
        }
    }
}

/// Returns the next leaf `TokenIndex` inside `[start_cursor .. attr_end)`, or `.none` if exhausted.
fn peekNextAttrLeafToken(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    start_cursor: usize,
    attr_end: usize,
) TokenIndex {
    var scan_idx = start_cursor;
    while (scan_idx < attr_end) : (scan_idx += 1) {
        const cand = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(scan_idx)));
        if (cand.subtree_size <= 1 and !cand.token.isNone() and
            cand.token.asInt() < token_buffer.countTokens())
        {
            return cand.token;
        }
    }
    return .none;
}

/// Emits `E0403` for an unknown `@attribute_schema` parameter or misspelled `AttributeTarget` variant.
fn emitInvalidAttributeSchemaToken(
    sink: *DiagnosticSink,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    bad_tok: TokenIndex,
    bad_lexeme: []const u8,
    is_named_param: bool,
) !void {
    const span = token_buffer.getTokenSpan(file_id, bad_tok);
    const arena_alloc = sink.arena.asAllocator();
    const message = if (is_named_param)
        try std.fmt.allocPrint(
            arena_alloc,
            "unknown `@attribute_schema` parameter `{s}`; expected `targets`",
            .{bad_lexeme},
        )
    else
        try std.fmt.allocPrint(
            arena_alloc,
            "unknown `AttributeTarget` variant `{s}` in `@attribute_schema`",
            .{bad_lexeme},
        );
    const label_text = if (is_named_param)
        "unknown `@attribute_schema` parameter"
    else
        "invalid `AttributeTarget` variant here";

    var best_suggestion: ?[]const u8 = if (is_named_param) "targets" else null;
    if (!is_named_param and bad_lexeme.len > 0) {
        var best_dist: u16 = 3;
        for (ATTRIBUTE_TARGET_NAMES) |cand_name| {
            const dist = computeEditDistance(bad_lexeme, cand_name);
            if (dist < best_dist) {
                best_dist = dist;
                best_suggestion = cand_name;
            }
        }
    }

    const labels = [1]LabeledSpan{
        .{ .span = span, .label = label_text, .style = .primary },
    };
    if (best_suggestion) |suggested| {
        const help_note = try std.fmt.allocPrint(
            arena_alloc,
            "help: did you mean `{s}`?",
            .{suggested},
        );
        const notes = [1][]const u8{help_note};
        _ = try sink.emit(.{
            .code = .e0403_unresolved_symbol,
            .severity = .err,
            .primary_span = span,
            .message = message,
            .labels = &labels,
            .notes = &notes,
        });
    } else {
        _ = try sink.emit(.{
            .code = .e0403_unresolved_symbol,
            .severity = .err,
            .primary_span = span,
            .message = message,
            .labels = &labels,
        });
    }
}

/// Extracts and validates `@attribute_schema(…)` target arguments inside `[arg_start .. attr_end)`.
fn extractAttributeSchemaTargets(
    source: []const u8,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    arg_start: usize,
    attr_end: usize,
    diagnostic_sink: ?*DiagnosticSink,
) !AttrTargetMask {
    const first_tok = peekNextAttrLeafToken(token_buffer, cst_arena, arg_start, attr_end);
    if (first_tok.isNone() or token_buffer.getToken(first_tok).kind != .lparen) {
        return AttrTargetMask.ALL;
    }

    var parsed_mask = AttrTargetMask{};
    var arg_cur = arg_start;
    while (arg_cur < attr_end) : (arg_cur += 1) {
        const arg_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(arg_cur)));
        if (arg_leaf.subtree_size > 1 or arg_leaf.token.isNone() or
            arg_leaf.token.asInt() >= token_buffer.countTokens())
        {
            continue;
        }
        const arg_kind = token_buffer.getToken(arg_leaf.token).kind;
        switch (arg_kind) {
            .lparen,
            .rparen,
            .lbracket,
            .rbracket,
            .comma,
            .dot,
            .coloncolon,
            .pipe,
            .eq,
            .colon,
            => continue,
            else => {},
        }

        const token_lex = extractTokenSlice(source, token_buffer, arg_leaf.token);
        if (isIdentifierToken(arg_kind)) {
            const next_tok = peekNextAttrLeafToken(token_buffer, cst_arena, arg_cur + 1, attr_end);
            const next_kind: TokenKind = if (!next_tok.isNone())
                token_buffer.getToken(next_tok).kind
            else
                .eof;
            if (next_kind == .eq or next_kind == .colon) {
                if (!std.mem.eql(u8, token_lex, "targets")) {
                    if (diagnostic_sink) |sink| {
                        try emitInvalidAttributeSchemaToken(
                            sink,
                            file_id,
                            token_buffer,
                            arg_leaf.token,
                            token_lex,
                            true,
                        );
                    }
                }
                continue;
            }
            if ((next_kind == .coloncolon or next_kind == .dot) and
                std.mem.eql(u8, token_lex, "AttributeTarget"))
            {
                continue;
            }
            if (ATTRIBUTE_TARGET_MAP.get(token_lex)) |bit_val| {
                parsed_mask = @bitCast(@as(u8, @bitCast(parsed_mask)) | @as(u8, @bitCast(bit_val)));
            } else if (diagnostic_sink) |sink| {
                try emitInvalidAttributeSchemaToken(
                    sink,
                    file_id,
                    token_buffer,
                    arg_leaf.token,
                    token_lex,
                    false,
                );
            }
        } else if (diagnostic_sink) |sink| {
            try emitInvalidAttributeSchemaToken(
                sink,
                file_id,
                token_buffer,
                arg_leaf.token,
                token_lex,
                false,
            );
        }
    }
    return parsed_mask;
}

/// Extracts `@link_section(…)` section bytes inside `[arg_start .. attr_end)` and enforces `E0327`.
fn extractLinkSectionAttr(
    source: []const u8,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    arg_start: usize,
    attr_end: usize,
    meta: *ItemHeaderMetadata,
    diagnostic_sink: ?*DiagnosticSink,
) !void {
    meta.contract_flags.has_link_section = true;
    var sec_cur = arg_start;
    while (sec_cur < attr_end) : (sec_cur += 1) {
        const sec_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sec_cur)));
        if (sec_leaf.subtree_size <= 1 and !sec_leaf.token.isNone() and
            sec_leaf.token.asInt() < token_buffer.countTokens())
        {
            if (token_buffer.getToken(sec_leaf.token).kind == .string_lit) {
                const sec_raw = extractTokenSlice(source, token_buffer, sec_leaf.token);
                var unesc_buf: [256]u8 = undefined;
                const sec_name = unquoteAttrStringLexeme(sec_raw, &unesc_buf);
                const copy_len = @min(sec_name.len, meta.link_section_buf.len);
                @memcpy(meta.link_section_buf[0..copy_len], sec_name[0..copy_len]);
                meta.link_section_len = @intCast(copy_len);
                if (isForbiddenExecutableSection(sec_name)) {
                    if (diagnostic_sink) |sink| {
                        const sec_span = token_buffer.getTokenSpan(file_id, sec_leaf.token);
                        const msg = try std.fmt.allocPrint(
                            sink.arena.asAllocator(),
                            "forbidden executable/constructor section `{s}` in `@link_section`",
                            .{sec_name},
                        );
                        const labels = [1]LabeledSpan{
                            .{
                                .span = sec_span,
                                .label = "constructor/destructor/TLS section bypasses `main(ctx)` capability root",
                                .style = .primary,
                            },
                        };
                        _ = try sink.emit(.{
                            .code = .e0327_forbidden_sandbox_bypass_attribute,
                            .severity = .err,
                            .primary_span = sec_span,
                            .message = msg,
                            .labels = &labels,
                        });
                    }
                }
                break;
            }
        }
    }
}

/// Extracts `@max_stack(…)` byte budget inside `[arg_start .. attr_end)` and validates 32-bit bounds.
fn extractMaxStackAttr(
    source: []const u8,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    attr_token: TokenIndex,
    arg_start: usize,
    attr_end: usize,
    meta: *ItemHeaderMetadata,
    diagnostic_sink: ?*DiagnosticSink,
) !void {
    meta.contract_flags.has_max_stack = true;
    var has_minus = false;
    var has_parsed_limit = false;
    var has_overflow = false;
    var diag_tok: TokenIndex = attr_token;
    var stk_cur = arg_start;
    while (stk_cur < attr_end) : (stk_cur += 1) {
        const stk_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(stk_cur)));
        if (stk_leaf.subtree_size <= 1 and !stk_leaf.token.isNone() and
            stk_leaf.token.asInt() < token_buffer.countTokens())
        {
            const stk_kind = token_buffer.getToken(stk_leaf.token).kind;
            if (stk_kind == .lparen or stk_kind == .rparen) continue;
            if (stk_kind == .minus) {
                has_minus = true;
                diag_tok = stk_leaf.token;
                continue;
            }
            diag_tok = stk_leaf.token;
            if (stk_kind == .int_lit and !has_minus) {
                const stk_lex = extractTokenSlice(source, token_buffer, stk_leaf.token);
                if (extractAttrUint32Lexeme(stk_lex)) |parsed_bytes| {
                    meta.max_stack_bytes = parsed_bytes;
                    has_parsed_limit = true;
                } else {
                    has_overflow = true;
                }
            }
            break;
        }
    }
    if (!has_parsed_limit) {
        if (diagnostic_sink) |sink| {
            const bad_span = token_buffer.getTokenSpan(file_id, diag_tok);
            const err_code: diagnostic.DiagnosticCode = if (has_overflow)
                .e0103_invalid_numeric_literal
            else
                .e0406_range_refinement_violation;
            const err_msg: []const u8 = if (has_minus)
                "`@max_stack` byte budget cannot be negative"
            else if (has_overflow)
                "`@max_stack` byte budget overflows maximum 32-bit frame limit"
            else
                "`@max_stack` requires a non-negative 32-bit integer byte limit";
            const labels = [1]LabeledSpan{
                .{
                    .span = bad_span,
                    .label = "invalid `@max_stack` byte budget here",
                    .style = .primary,
                },
            };
            _ = try sink.emit(.{
                .code = err_code,
                .severity = .err,
                .primary_span = bad_span,
                .message = err_msg,
                .labels = &labels,
            });
        }
    }
}

/// Extracts item flags, `comptime` modifier, `@derive(…)`, and `@attribute_schema(…)` metadata from `item_cst`.
pub fn extractItemHeaderMetadata(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst: CstNodeIndex,
    main_token: TokenIndex,
) ItemHeaderMetadata {
    return extractItemHeaderMetadataValidated(
        source,
        .none,
        token_buffer,
        cst_arena,
        item_cst,
        main_token,
        null,
    ) catch ItemHeaderMetadata{};
}

/// Extracts item header metadata while validating `@attribute_schema(…)` targets into `diagnostic_sink`.
pub fn extractItemHeaderMetadataValidated(
    source: []const u8,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst: CstNodeIndex,
    main_token: TokenIndex,
    diagnostic_sink: ?*DiagnosticSink,
) !ItemHeaderMetadata {
    var meta = ItemHeaderMetadata{};
    if (item_cst.isNone() or item_cst.asInt() >= cst_arena.countNodes()) return meta;

    const start_idx: usize = item_cst.asInt();
    const root_rec = cst_arena.getNode(item_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (!node.token.isNone() and !main_token.isNone() and node.token.asInt() >= main_token.asInt()) {
            break;
        }
        if (node.kind == .visibility_modifier) {
            meta.flags.is_pub = true;
            continue;
        }
        if (node.subtree_size <= 1 and !node.flags.is_bracketed and !node.token.isNone() and
            node.token.asInt() < token_buffer.countTokens())
        {
            const tok_kind_pre = token_buffer.getToken(node.token).kind;
            if (tok_kind_pre == .kw_comptime) {
                meta.flags.is_comptime = true;
                continue;
            }
            if (tok_kind_pre == .kw_extern) {
                meta.flags.is_extern = true;
                continue;
            }
        }
        if (node.kind == .attribute) {
            const attr_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), end_idx);
            var attr_cur = cursor + 1;
            while (attr_cur < attr_end) : (attr_cur += 1) {
                const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(attr_cur)));
                if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                    leaf.token.asInt() < token_buffer.countTokens())
                {
                    const tok_kind = token_buffer.getToken(leaf.token).kind;
                    if (isIdentifierToken(tok_kind) or tok_kind == .kw_pub) {
                        const attr_name = extractTokenSlice(source, token_buffer, leaf.token);
                        if (HEADER_ATTR_MAP.get(attr_name)) |attr_kind| {
                            switch (attr_kind) {
                                .overload => meta.flags.is_overload = true,
                                .must_use => meta.flags.is_must_use = true,
                                .from => meta.flags.is_from_error = true,
                                .soa => meta.flags.is_soa_annotated = true,
                                .extern_attr => meta.flags.is_extern = true,
                                .no_alloc => meta.contract_flags.is_no_alloc = true,
                                .no_panic => meta.contract_flags.is_no_panic = true,
                                .no_block => meta.contract_flags.is_no_block = true,
                                .linear => meta.contract_flags.is_linear = true,
                                .zero_pad => meta.contract_flags.is_zero_pad = true,
                                .secret => meta.contract_flags.is_secret = true,
                                .export_attr => meta.contract_flags.is_export = true,
                                .local => meta.contract_flags.is_local_only = true,
                                .cache_aligned => meta.contract_flags.is_cache_aligned = true,
                                .packed_attr => meta.contract_flags.is_packed = true,
                                .align_attr => extractAlignAttr(
                                    source,
                                    token_buffer,
                                    cst_arena,
                                    attr_cur + 1,
                                    attr_end,
                                    &meta,
                                ),
                                .link_name => extractLinkNameAttr(
                                    source,
                                    token_buffer,
                                    cst_arena,
                                    attr_cur + 1,
                                    attr_end,
                                    &meta,
                                ),
                                .ifunc => {
                                    meta.contract_flags.is_ifunc = true;
                                    if (diagnostic_sink) |sink| {
                                        const ifunc_span = token_buffer.getTokenSpan(file_id, leaf.token);
                                        const labels = [1]LabeledSpan{
                                            .{
                                                .span = ifunc_span,
                                                .label = "dynamic loader resolver bypasses `main(ctx)` capability root",
                                                .style = .primary,
                                            },
                                        };
                                        _ = try sink.emit(.{
                                            .code = .e0327_forbidden_sandbox_bypass_attribute,
                                            .severity = .err,
                                            .primary_span = ifunc_span,
                                            .message = "forbidden `@ifunc` indirect function resolver attribute",
                                            .labels = &labels,
                                        });
                                    }
                                },
                                .link_section => try extractLinkSectionAttr(
                                    source,
                                    file_id,
                                    token_buffer,
                                    cst_arena,
                                    attr_cur + 1,
                                    attr_end,
                                    &meta,
                                    diagnostic_sink,
                                ),
                                .max_stack => try extractMaxStackAttr(
                                    source,
                                    file_id,
                                    token_buffer,
                                    cst_arena,
                                    leaf.token,
                                    attr_cur + 1,
                                    attr_end,
                                    &meta,
                                    diagnostic_sink,
                                ),
                                .std_cap_boundary => {
                                    meta.contract_flags.is_std_cap_boundary = true;
                                    extractStdCapBoundaryMasks(
                                        source,
                                        token_buffer,
                                        cst_arena,
                                        attr_cur + 1,
                                        attr_end,
                                        &meta.cap_emits_mask,
                                        &meta.cap_clears_mask,
                                    );
                                },
                                .repr => extractReprAttr(
                                    source,
                                    token_buffer,
                                    cst_arena,
                                    attr_cur + 1,
                                    attr_end,
                                    &meta,
                                ),
                                .derive => {
                                    var arg_cur = attr_cur + 1;
                                    while (arg_cur < attr_end) : (arg_cur += 1) {
                                        const arg_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(arg_cur)));
                                        if (arg_leaf.subtree_size <= 1 and !arg_leaf.token.isNone() and
                                            arg_leaf.token.asInt() < token_buffer.countTokens())
                                        {
                                            const arg_kind = token_buffer.getToken(arg_leaf.token).kind;
                                            if (isIdentifierToken(arg_kind)) {
                                                const trait_lex = extractTokenSlice(source, token_buffer, arg_leaf.token);
                                                if (DERIVE_TRAIT_MAP.get(trait_lex)) |trait_bit| {
                                                    meta.derive_mask = @bitCast(
                                                        @as(u8, @bitCast(meta.derive_mask)) |
                                                            @as(u8, @bitCast(trait_bit)),
                                                    );
                                                }
                                            }
                                        }
                                    }
                                },
                                .attribute_schema => {
                                    meta.flags.is_attribute_schema = true;
                                    meta.attr_target_mask = try extractAttributeSchemaTargets(
                                        source,
                                        file_id,
                                        token_buffer,
                                        cst_arena,
                                        attr_cur + 1,
                                        attr_end,
                                        diagnostic_sink,
                                    );
                                },
                            }
                        }
                        break;
                    }
                }
            }
            if (node.subtree_size > 1) {
                cursor += @as(usize, node.subtree_size) - 1;
            }
        }
    }
    return meta;
}

/// Extracts `@overload`, `@must_use`, `@from`, and `#soa` flags from CST `.attribute` nodes inside `item_cst`.
pub fn extractItemAttributesAndVisibility(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst: CstNodeIndex,
    main_token: TokenIndex,
) SymbolFlags {
    return extractItemHeaderMetadata(source, token_buffer, cst_arena, item_cst, main_token).flags;
}

/// Returns `true` if `item_cst` contains a direct leaf token of `target_kind`.
fn hasKeywordInCst(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst: CstNodeIndex,
    target_kind: TokenKind,
) bool {
    if (item_cst.isNone() or item_cst.asInt() >= cst_arena.countNodes()) return false;
    const start_idx: usize = item_cst.asInt();
    const root_rec = cst_arena.getNode(item_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );
    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
        if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
        if (node.token.asInt() >= token_buffer.countTokens()) continue;
        if (token_buffer.getToken(node.token).kind == target_kind) return true;
    }
    return false;
}

/// Finds the primary declaration identifier token inside `item_cst` right after `main_token`.
pub fn findItemNameToken(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst: CstNodeIndex,
    main_token: TokenIndex,
) TokenIndex {
    if (item_cst.isNone() or item_cst.asInt() >= cst_arena.countNodes()) return main_token;
    const start_idx: usize = item_cst.asInt();
    const root_rec = cst_arena.getNode(item_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
        if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
        if (!main_token.isNone() and node.token.asInt() <= main_token.asInt()) continue;
        if (node.token.asInt() >= token_buffer.countTokens()) continue;

        const tok_kind = token_buffer.getToken(node.token).kind;
        if (tok_kind == .lbrace or tok_kind == .semi or tok_kind == .eq or tok_kind == .colon or tok_kind == .lparen) {
            break;
        }
        if (isIdentifierToken(tok_kind)) {
            return node.token;
        }
    }
    return main_token;
}

/// Collects all top-level items inside `file_id` (and nested inline `mod` blocks) into `sym_table`.
pub fn collectFileModuleItems(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    diagnostic_sink: ?*DiagnosticSink,
) !ScopeId {
    const file_scope = try sym_table.scope_arena.allocScope(
        .module_scope,
        sym_table.prelude_scope,
        .NONE,
        file_id,
        .{},
    );
    try sym_table.file_module_scopes.put(sym_table.allocator, file_id.asInt(), file_scope);

    if (ast_arena.countNodes() == 0) return file_scope;
    const root_node = ast_arena.getNode(.root);
    if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
        const item_slice = ast_arena.getExtraSlice(
            ExtraIndex.fromInt(root_node.lhs.payload),
            root_node.rhs.payload,
        );
        try collectItemSliceInScope(
            sym_table,
            interner,
            file_id,
            file_scope,
            true,
            .NONE,
            item_slice,
            source,
            token_buffer,
            cst_arena,
            ast_arena,
            diagnostic_sink,
        );
    }
    return file_scope;
}

/// Collects a slice of AST item indices into `enclosing_scope`.
fn collectItemSliceInScope(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    enclosing_scope: ScopeId,
    is_file_top_level: bool,
    enclosing_owner_def: DefId,
    item_slice: []const u32,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!void {
    var top_item_ordinal: u12 = 0;
    for (item_slice) |raw_node_idx| {
        const item_node_idx = NodeIndex.fromInt(raw_node_idx);
        if (item_node_idx.asInt() >= ast_arena.countNodes()) continue;
        const ast_node = ast_arena.getNode(item_node_idx);
        if (ast_node.tag == .item_hole) continue;

        const def_id: DefId = if (is_file_top_level) blk: {
            const current_def = DefId.init(file_id, top_item_ordinal);
            if (top_item_ordinal < std.math.maxInt(u12)) top_item_ordinal += 1;
            break :blk current_def;
        } else .NONE;

        const item_cst = ast_arena.getCstOrigin(item_node_idx);
        const header_meta = try extractItemHeaderMetadataValidated(
            source,
            file_id,
            token_buffer,
            cst_arena,
            item_cst,
            ast_node.main_token,
            diagnostic_sink,
        );
        var flags = header_meta.flags;
        const visibility: Visibility = if (flags.is_pub) .public else .private;
        const link_sec_slice = header_meta.asLinkSectionSlice();
        const interned_link_sec: []const u8 = if (link_sec_slice.len > 0)
            interner.get(try interner.intern(link_sec_slice))
        else
            "";
        const link_name_slice = header_meta.asLinkNameSlice();
        const interned_link_name: []const u8 = if (link_name_slice.len > 0)
            interner.get(try interner.intern(link_name_slice))
        else
            "";

        switch (ast_node.tag) {
            .mod_decl => {
                const name_tok = if (ast_node.lhs.tag == .token)
                    TokenIndex.fromInt(ast_node.lhs.payload)
                else
                    findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                const name_str = extractTokenSlice(source, token_buffer, name_tok);
                if (name_str.len == 0) continue;
                const name_sym = try interner.intern(name_str);
                const name_span = token_buffer.getTokenSpan(file_id, name_tok);

                const bound_ext_scope: ScopeId = if (ast_node.rhs.tag != .extra) blk: {
                    const direct_ext = sym_table.getExternalModuleScope(file_id, name_sym);
                    if (!direct_ext.isNone()) break :blk direct_ext;
                    break :blk sym_table.named_module_scopes.get(name_sym.asInt()) orelse .none;
                } else .none;
                const mod_scope = if (!bound_ext_scope.isNone())
                    bound_ext_scope
                else blk: {
                    const fresh_scope = try sym_table.scope_arena.allocScope(
                        .module_scope,
                        enclosing_scope,
                        def_id,
                        file_id,
                        .{},
                    );
                    try sym_table.named_module_scopes.put(sym_table.allocator, name_sym.asInt(), fresh_scope);
                    break :blk fresh_scope;
                };

                _ = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = .module_sym,
                    .namespace = .value_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = name_span,
                    .target_scope = mod_scope,
                }, diagnostic_sink);

                // Collect inline `mod foo { … }` sub-items:
                if (ast_node.rhs.tag == .extra) {
                    const inner_items = extractModInnerItems(ast_arena, item_node_idx);
                    try collectItemSliceInScope(
                        sym_table,
                        interner,
                        file_id,
                        mod_scope,
                        false,
                        .NONE,
                        inner_items,
                        source,
                        token_buffer,
                        cst_arena,
                        ast_arena,
                        diagnostic_sink,
                    );
                }
            },
            .use_decl => {
                try sym_table.pending_imports.append(sym_table.allocator, .{
                    .module_scope = enclosing_scope,
                    .file_id = file_id,
                    .def_id = def_id,
                    .is_pub = flags.is_pub,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                });
            },
            .struct_decl, .union_decl => {
                const is_bit_field = !ast_node.main_token.isNone() and
                    ast_node.main_token.asInt() < token_buffer.countTokens() and
                    token_buffer.getToken(ast_node.main_token).kind == .kw_bit_field;
                const name_tok = findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                const name_str = extractTokenSlice(source, token_buffer, name_tok);
                if (name_str.len == 0) continue;
                const name_sym = try interner.intern(name_str);
                const name_span = token_buffer.getTokenSpan(file_id, name_tok);

                const member_scope = try sym_table.scope_arena.allocScope(
                    .nominal_type_scope,
                    enclosing_scope,
                    def_id,
                    file_id,
                    .{},
                );
                const sym_kind: SymbolKind = if (is_bit_field)
                    .bit_field_sym
                else if (ast_node.tag == .union_decl)
                    .union_sym
                else
                    .struct_sym;

                _ = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = sym_kind,
                    .namespace = .type_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = name_span,
                    .target_scope = member_scope,
                    .derive_mask = header_meta.derive_mask,
                    .attr_target_mask = header_meta.attr_target_mask,
                    .contract_flags = header_meta.contract_flags,
                    .max_stack_bytes = header_meta.max_stack_bytes,
                    .cap_emits_mask = header_meta.cap_emits_mask,
                    .cap_clears_mask = header_meta.cap_clears_mask,
                    .link_section_name = interned_link_sec,
                    .link_name_text = interned_link_name,
                    .repr_tag_bits = header_meta.repr_tag_bits,
                    .explicit_align_log2_plus1 = header_meta.explicit_align_log2_plus1,
                }, diagnostic_sink);

                try collectStructOrBitFieldMembers(
                    sym_table,
                    interner,
                    file_id,
                    member_scope,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                    diagnostic_sink,
                );
            },
            .enum_decl => {
                const name_tok = findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                const name_str = extractTokenSlice(source, token_buffer, name_tok);
                if (name_str.len == 0) continue;
                const name_sym = try interner.intern(name_str);
                const name_span = token_buffer.getTokenSpan(file_id, name_tok);

                const variant_scope = try sym_table.scope_arena.allocScope(
                    .nominal_type_scope,
                    enclosing_scope,
                    def_id,
                    file_id,
                    .{},
                );
                _ = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = .enum_sym,
                    .namespace = .type_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = name_span,
                    .target_scope = variant_scope,
                    .derive_mask = header_meta.derive_mask,
                    .attr_target_mask = header_meta.attr_target_mask,
                    .contract_flags = header_meta.contract_flags,
                    .max_stack_bytes = header_meta.max_stack_bytes,
                    .cap_emits_mask = header_meta.cap_emits_mask,
                    .cap_clears_mask = header_meta.cap_clears_mask,
                    .link_section_name = interned_link_sec,
                    .link_name_text = interned_link_name,
                    .repr_tag_bits = header_meta.repr_tag_bits,
                    .explicit_align_log2_plus1 = header_meta.explicit_align_log2_plus1,
                }, diagnostic_sink);

                try collectEnumVariants(
                    sym_table,
                    interner,
                    file_id,
                    variant_scope,
                    flags.is_pub,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                    diagnostic_sink,
                );
            },
            .trait_decl => {
                const name_tok = findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                const name_str = extractTokenSlice(source, token_buffer, name_tok);
                if (name_str.len == 0) continue;
                const name_sym = try interner.intern(name_str);
                const name_span = token_buffer.getTokenSpan(file_id, name_tok);

                const trait_scope = try sym_table.scope_arena.allocScope(
                    .trait_scope,
                    enclosing_scope,
                    def_id,
                    file_id,
                    .{},
                );
                _ = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = .trait_sym,
                    .namespace = .type_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = name_span,
                    .target_scope = trait_scope,
                    .contract_flags = header_meta.contract_flags,
                }, diagnostic_sink);

                if (ast_node.lhs.tag == .extra and ast_node.rhs.tag == .extra and ast_node.rhs.payload > 0) {
                    const member_slice = ast_arena.getExtraSlice(
                        ExtraIndex.fromInt(ast_node.lhs.payload),
                        ast_node.rhs.payload,
                    );
                    try collectItemSliceInScope(
                        sym_table,
                        interner,
                        file_id,
                        trait_scope,
                        false,
                        .NONE,
                        member_slice,
                        source,
                        token_buffer,
                        cst_arena,
                        ast_arena,
                        diagnostic_sink,
                    );
                }
            },
            .type_alias_decl => {
                const name_tok = findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                const name_str = extractTokenSlice(source, token_buffer, name_tok);
                if (name_str.len == 0) continue;
                const name_sym = try interner.intern(name_str);
                const name_span = token_buffer.getTokenSpan(file_id, name_tok);

                // Classify whether this `type` item is a `bit_field`, union Type Group (`|`), `is` refinement, or `distinct`:
                var alias_kind: SymbolKind = .type_alias_sym;
                var bf_member_scope: ScopeId = .none;
                if (hasKeywordInCst(token_buffer, cst_arena, item_cst, .kw_bit_field)) {
                    alias_kind = .bit_field_sym;
                    bf_member_scope = try sym_table.scope_arena.allocScope(
                        .nominal_type_scope,
                        enclosing_scope,
                        def_id,
                        file_id,
                        .{},
                    );
                } else if (ast_node.lhs.tag == .extra and ast_node.rhs.tag == .extra) {
                    alias_kind = .type_group_sym;
                    flags.is_type_group = true;
                } else if (ast_node.rhs.tag == .node) {
                    alias_kind = .refined_type_sym;
                    flags.is_refined = true;
                } else if (ast_node.lhs.tag == .node) {
                    const target_ast = ast_arena.getNode(NodeIndex.fromInt(ast_node.lhs.payload));
                    if (target_ast.tag == .mode_type) {
                        const mode_lexeme = extractTokenSlice(source, token_buffer, target_ast.main_token);
                        if (std.mem.eql(u8, mode_lexeme, "distinct")) {
                            alias_kind = .distinct_type_sym;
                            flags.is_distinct = true;
                        }
                    }
                }

                _ = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = alias_kind,
                    .namespace = .type_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = name_span,
                    .target_scope = bf_member_scope,
                    .contract_flags = header_meta.contract_flags,
                    .link_section_name = interned_link_sec,
                    .link_name_text = interned_link_name,
                    .repr_tag_bits = header_meta.repr_tag_bits,
                    .explicit_align_log2_plus1 = header_meta.explicit_align_log2_plus1,
                }, diagnostic_sink);

                if (alias_kind == .bit_field_sym and !bf_member_scope.isNone()) {
                    try collectStructOrBitFieldMembers(
                        sym_table,
                        interner,
                        file_id,
                        bf_member_scope,
                        item_cst,
                        source,
                        token_buffer,
                        cst_arena,
                        diagnostic_sink,
                    );
                }
            },
            .const_decl => {
                const name_tok = findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                const name_str = extractTokenSlice(source, token_buffer, name_tok);
                if (name_str.len == 0) continue;
                const name_sym = try interner.intern(name_str);
                const name_span = token_buffer.getTokenSpan(file_id, name_tok);

                _ = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = .const_sym,
                    .namespace = .const_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .owner_def_id = enclosing_owner_def,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = name_span,
                    .contract_flags = header_meta.contract_flags,
                    .link_section_name = interned_link_sec,
                    .link_name_text = interned_link_name,
                    .explicit_align_log2_plus1 = header_meta.explicit_align_log2_plus1,
                }, diagnostic_sink);
            },
            .fn_decl => {
                const name_tok = findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                const name_str = extractTokenSlice(source, token_buffer, name_tok);
                if (name_str.len == 0) continue;
                const name_sym = try interner.intern(name_str);
                const name_span = token_buffer.getTokenSpan(file_id, name_tok);
                flags.is_prototype_only = (ast_node.rhs.tag == .none);

                _ = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = .fn_sym,
                    .namespace = .value_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .owner_def_id = enclosing_owner_def,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = name_span,
                    .contract_flags = header_meta.contract_flags,
                    .max_stack_bytes = header_meta.max_stack_bytes,
                    .cap_emits_mask = header_meta.cap_emits_mask,
                    .cap_clears_mask = header_meta.cap_clears_mask,
                    .link_section_name = interned_link_sec,
                    .link_name_text = interned_link_name,
                    .explicit_align_log2_plus1 = header_meta.explicit_align_log2_plus1,
                }, diagnostic_sink);
            },
            .impl_decl => {
                // Collect methods inside `impl [Trait for] TargetType { … }` into `TargetType`'s member scope:
                const impl_target = try resolveImplTargetScope(
                    sym_table,
                    interner,
                    file_id,
                    enclosing_scope,
                    def_id,
                    item_cst,
                    ast_node,
                    source,
                    token_buffer,
                    cst_arena,
                    ast_arena,
                );
                const member_items = extractImplMemberItems(ast_arena, item_node_idx);
                const pre_sym_len = sym_table.symbols.items.len;
                try collectItemSliceInScope(
                    sym_table,
                    interner,
                    file_id,
                    impl_target.target_scope,
                    false,
                    def_id,
                    member_items,
                    source,
                    token_buffer,
                    cst_arena,
                    ast_arena,
                    diagnostic_sink,
                );
                if (!impl_target.trait_sym_idx.isNone()) {
                    var sym_i = pre_sym_len;
                    while (sym_i < sym_table.symbols.items.len) : (sym_i += 1) {
                        const added_sym = sym_table.symbols.items[sym_i];
                        if (added_sym.kind == .fn_sym and added_sym.scope_id == impl_target.target_scope) {
                            try sym_table.impl_method_trait.put(
                                sym_table.allocator,
                                @intCast(sym_i),
                                impl_target.trait_sym_idx,
                            );
                        }
                    }
                }
            },
            else => {},
        }
    }
}

/// Extracts the slice of inner item AST indices from an inline `mod foo { … }` node.
fn extractModInnerItems(ast_arena: *const AstArena, mod_node_idx: NodeIndex) []const u32 {
    const mod_node = ast_arena.getNode(mod_node_idx);
    if (mod_node.rhs.tag != .extra) return &.{};
    const start_extra: usize = mod_node.rhs.payload;
    if (start_extra >= ast_arena.extra_data.items.len) return &.{};
    // Any nodes in `extra_data[start_extra..]` that were appended as the trailing slice of `mod_node`
    // precede `mod_node_idx` in `ast_arena.nodes`:
    var end_extra: usize = start_extra;
    while (end_extra < ast_arena.extra_data.items.len) : (end_extra += 1) {
        const cand_node = ast_arena.extra_data.items[end_extra];
        if (cand_node >= mod_node_idx.asInt()) break;
    }
    return ast_arena.extra_data.items[start_extra..end_extra];
}

/// Extracts the slice of member AST node indices from an `impl_decl` node.
pub fn extractImplMemberItems(ast_arena: *const AstArena, impl_node_idx: NodeIndex) []const u32 {
    const impl_node = ast_arena.getNode(impl_node_idx);
    if (impl_node.rhs.tag != .extra) return &.{};
    const start_extra: usize = impl_node.rhs.payload;
    if (start_extra >= ast_arena.extra_data.items.len) return &.{};
    var end_extra: usize = start_extra;
    while (end_extra < ast_arena.extra_data.items.len) : (end_extra += 1) {
        const cand_node = ast_arena.extra_data.items[end_extra];
        if (cand_node >= impl_node_idx.asInt()) break;
    }
    return ast_arena.extra_data.items[start_extra..end_extra];
}

/// Target member scope and optional implemented `trait_sym` resolved for an `impl` header.
const ImplTargetResolution = struct {
    /// Member scope receiving `impl` methods.
    target_scope: ScopeId,
    /// Implemented `.trait_sym` when `impl Trait for Type` is resolved (`SymbolIndex.none` for inherent `impl Type`).
    trait_sym_idx: SymbolIndex,
};

/// Finds or creates the member `ScopeId` and implemented `trait_sym` for an `impl` block.
fn resolveImplTargetScope(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    enclosing_scope: ScopeId,
    def_id: DefId,
    item_cst: CstNodeIndex,
    ast_node: syntax_arenas.AstNode,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
) !ImplTargetResolution {
    _ = ast_arena;
    var trait_sym_idx: SymbolIndex = .none;
    if (!item_cst.isNone() and item_cst.asInt() < cst_arena.countNodes()) {
        const start_idx: usize = item_cst.asInt();
        const root_rec = cst_arena.getNode(item_cst);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, root_rec.subtree_size), 1),
            cst_arena.countNodes(),
        );

        var first_type_name: []const u8 = "";
        var after_for_type_name: []const u8 = "";
        var has_seen_for = false;

        var cursor: usize = start_idx + 1;
        while (cursor < end_idx) : (cursor += 1) {
            const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
            if ((node.kind == .type_params or node.kind == .type_args or node.kind == .where_clause) and
                node.subtree_size > 1)
            {
                cursor += @as(usize, node.subtree_size) - 1;
                continue;
            }
            const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
            if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
            if (!ast_node.main_token.isNone() and node.token.asInt() <= ast_node.main_token.asInt()) continue;
            if (node.token.asInt() >= token_buffer.countTokens()) continue;

            const tok_kind = token_buffer.getToken(node.token).kind;
            if (tok_kind == .lbrace or tok_kind == .kw_where or tok_kind == .semi) break;
            if (tok_kind == .kw_for) {
                has_seen_for = true;
                continue;
            }
            if (isIdentifierToken(tok_kind) or tok_kind == .prim_type) {
                const lex = extractTokenSlice(source, token_buffer, node.token);
                if (!has_seen_for) {
                    if (first_type_name.len == 0) first_type_name = lex;
                } else {
                    if (after_for_type_name.len == 0) after_for_type_name = lex;
                }
            }
        }

        if (has_seen_for and first_type_name.len > 0) {
            const trait_id = try interner.intern(first_type_name);
            switch (sym_table.lookupLexical(enclosing_scope, trait_id, NamespaceMask.TYPE_ONLY)) {
                .found => |found_trait| {
                    if (sym_table.getSymbol(found_trait).kind == .trait_sym) {
                        trait_sym_idx = found_trait;
                    }
                },
                else => {},
            }
        }

        const target_type_name = if (has_seen_for and after_for_type_name.len > 0)
            after_for_type_name
        else
            first_type_name;

        if (target_type_name.len > 0) {
            const target_sym_id = try interner.intern(target_type_name);
            const lookup = sym_table.lookupLexical(enclosing_scope, target_sym_id, NamespaceMask.TYPE_ONLY);
            switch (lookup) {
                .found => |sym_idx| {
                    const sym = sym_table.getSymbol(sym_idx);
                    if (!sym.target_scope.isNone()) {
                        return .{
                            .target_scope = sym.target_scope,
                            .trait_sym_idx = trait_sym_idx,
                        };
                    }
                    const created_scope = try sym_table.scope_arena.allocScope(
                        .nominal_type_scope,
                        enclosing_scope,
                        def_id,
                        file_id,
                        .{},
                    );
                    sym_table.getSymbolMut(sym_idx).target_scope = created_scope;
                    return .{
                        .target_scope = created_scope,
                        .trait_sym_idx = trait_sym_idx,
                    };
                },
                else => {},
            }
        }
    }

    return .{
        .target_scope = try sym_table.scope_arena.allocScope(
            .impl_scope,
            enclosing_scope,
            def_id,
            file_id,
            .{},
        ),
        .trait_sym_idx = trait_sym_idx,
    };
}

/// Collects `.struct_field` CST nodes inside a `struct`, `union`, or `bit_field` declaration into `member_scope`.
fn collectStructOrBitFieldMembers(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    member_scope: ScopeId,
    item_cst: CstNodeIndex,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    diagnostic_sink: ?*DiagnosticSink,
) !void {
    if (item_cst.isNone() or item_cst.asInt() >= cst_arena.countNodes()) return;
    const start_idx: usize = item_cst.asInt();
    const root_rec = cst_arena.getNode(item_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var ordinal: u16 = 0;
    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) {
        const cst_id = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(cst_id);
        if (node.kind == .struct_field) {
            const field_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), end_idx);
            var is_pub = false;
            var field_tok: TokenIndex = .none;
            var bit_width: u16 = 0;
            var has_seen_pipe = false;

            var inner_cur = cursor + 1;
            while (inner_cur < field_end) : (inner_cur += 1) {
                const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(inner_cur)));
                if (sub.kind == .attribute and sub.subtree_size > 1) {
                    inner_cur += @as(usize, sub.subtree_size) - 1;
                    continue;
                }
                if (sub.kind == .visibility_modifier) {
                    is_pub = true;
                    continue;
                }
                const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
                if (!is_leaf or sub.flags.is_missing_or_injected or sub.token.isNone()) continue;
                if (sub.token.asInt() >= token_buffer.countTokens()) continue;

                const tok_kind = token_buffer.getToken(sub.token).kind;
                if (field_tok.isNone() and isIdentifierToken(tok_kind)) {
                    field_tok = sub.token;
                } else if (tok_kind == .pipe) {
                    has_seen_pipe = true;
                } else if (has_seen_pipe and tok_kind == .int_lit) {
                    const width_str = extractTokenSlice(source, token_buffer, sub.token);
                    var acc_width: u32 = 0;
                    var has_digit = false;
                    for (width_str) |ch| {
                        if (ch == '_') continue;
                        if (ch >= '0' and ch <= '9') {
                            has_digit = true;
                            acc_width = @min(acc_width *| 10 +| @as(u32, ch - '0'), @as(u32, std.math.maxInt(u16)));
                        } else {
                            break;
                        }
                    }
                    bit_width = if (has_digit) @intCast(acc_width) else std.math.maxInt(u16);
                    has_seen_pipe = false;
                }
            }

            if (!field_tok.isNone()) {
                const field_name = extractTokenSlice(source, token_buffer, field_tok);
                if (field_name.len > 0) {
                    const field_sym = try interner.intern(field_name);
                    _ = try sym_table.defineSymbol(.{
                        .name = field_sym,
                        .name_text = interner.get(field_sym),
                        .kind = .field_sym,
                        .namespace = .value_ns,
                        .visibility = if (is_pub) .public else .private,
                        .flags = .{ .is_pub = is_pub },
                        .scope_id = member_scope,
                        .cst_node = cst_id,
                        .decl_span = token_buffer.getTokenSpan(file_id, field_tok),
                        .member_ordinal = ordinal,
                        .bit_width = bit_width,
                    }, diagnostic_sink);
                    ordinal +|= 1;
                }
            }
            cursor = field_end;
            continue;
        }
        cursor += 1;
    }
}

/// Collects `.enum_variant` CST nodes inside an `enum` declaration into `variant_scope`.
fn collectEnumVariants(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    variant_scope: ScopeId,
    is_enum_pub: bool,
    item_cst: CstNodeIndex,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    diagnostic_sink: ?*DiagnosticSink,
) !void {
    if (item_cst.isNone() or item_cst.asInt() >= cst_arena.countNodes()) return;
    const start_idx: usize = item_cst.asInt();
    const root_rec = cst_arena.getNode(item_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var ordinal: u16 = 0;
    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) {
        const cst_id = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(cst_id);
        if (node.kind == .enum_variant) {
            const var_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), end_idx);
            var var_tok: TokenIndex = .none;
            var is_var_from_error = false;

            var inner_cur = cursor + 1;
            while (inner_cur < var_end) : (inner_cur += 1) {
                const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(inner_cur)));
                if (sub.kind == .attribute) {
                    const attr_end = @min(inner_cur + @max(@as(usize, sub.subtree_size), 1), var_end);
                    var attr_cur = inner_cur + 1;
                    while (attr_cur < attr_end) : (attr_cur += 1) {
                        const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(attr_cur)));
                        if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                            leaf.token.asInt() < token_buffer.countTokens())
                        {
                            const attr_tok_kind = token_buffer.getToken(leaf.token).kind;
                            if (isIdentifierToken(attr_tok_kind)) {
                                if (std.mem.eql(u8, extractTokenSlice(source, token_buffer, leaf.token), "from")) {
                                    is_var_from_error = true;
                                }
                                break;
                            }
                        }
                    }
                    if (sub.subtree_size > 1) {
                        inner_cur += @as(usize, sub.subtree_size) - 1;
                    }
                    continue;
                }
                const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
                if (!is_leaf or sub.flags.is_missing_or_injected or sub.token.isNone()) continue;
                if (sub.token.asInt() >= token_buffer.countTokens()) continue;

                const tok_kind = token_buffer.getToken(sub.token).kind;
                if (isIdentifierToken(tok_kind)) {
                    var_tok = sub.token;
                    break;
                }
            }

            if (!var_tok.isNone()) {
                const var_name = extractTokenSlice(source, token_buffer, var_tok);
                if (var_name.len > 0) {
                    const var_sym = try interner.intern(var_name);
                    _ = try sym_table.defineSymbol(.{
                        .name = var_sym,
                        .name_text = interner.get(var_sym),
                        .kind = .enum_variant_sym,
                        .namespace = .value_ns,
                        .visibility = if (is_enum_pub) .public else .private,
                        .flags = .{
                            .is_pub = is_enum_pub,
                            .is_from_error = is_var_from_error,
                        },
                        .scope_id = variant_scope,
                        .cst_node = cst_id,
                        .decl_span = token_buffer.getTokenSpan(file_id, var_tok),
                        .member_ordinal = ordinal,
                    }, diagnostic_sink);
                    ordinal +|= 1;
                }
            }
            cursor = var_end;
            continue;
        }
        cursor += 1;
    }
}

/// Resolves all queued `PendingUseImport` entries in `sym_table` for `file_id`.
pub fn resolveFileUseImports(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    diagnostic_sink: ?*DiagnosticSink,
) !void {
    var i: usize = 0;
    while (i < sym_table.pending_imports.items.len) : (i += 1) {
        const pending = sym_table.pending_imports.items[i];
        if (pending.file_id != file_id) continue;
        if (pending.cst_node.isNone() or pending.cst_node.asInt() >= cst_arena.countNodes()) continue;

        const root_idx: usize = pending.cst_node.asInt();
        const root_rec = cst_arena.getNode(pending.cst_node);
        const end_idx: usize = @min(
            root_idx + @max(@as(usize, root_rec.subtree_size), 1),
            cst_arena.countNodes(),
        );

        // Locate the top-level `.use_tree` child inside `use_item`:
        var cursor: usize = root_idx + 1;
        while (cursor < end_idx) : (cursor += 1) {
            const node_id = CstNodeIndex.fromInt(@intCast(cursor));
            if (cst_arena.getNode(node_id).kind == .use_tree) {
                try resolveUseTreeCst(
                    sym_table,
                    interner,
                    pending.file_id,
                    pending.module_scope,
                    pending.module_scope,
                    pending.def_id,
                    pending.is_pub,
                    node_id,
                    source,
                    token_buffer,
                    cst_arena,
                    diagnostic_sink,
                );
                break;
            }
        }
    }
}

/// Recursively resolves a `.use_tree` CST subtree (`path::to::{a, b as c}` or `path::*`).
fn resolveUseTreeCst(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    dest_module_scope: ScopeId,
    current_lookup_scope: ScopeId,
    def_id: DefId,
    is_pub: bool,
    tree_cst: CstNodeIndex,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!void {
    const start_idx: usize = tree_cst.asInt();
    const tree_rec = cst_arena.getNode(tree_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, tree_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var segments: [32]TokenIndex = undefined;
    var seg_count: usize = 0;
    var is_glob = false;
    var has_seen_as = false;
    var alias_tok: TokenIndex = .none;
    var has_nested_trees = false;

    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) {
        const sub_id = CstNodeIndex.fromInt(@intCast(cursor));
        const sub = cst_arena.getNode(sub_id);

        if (sub.kind == .use_tree) {
            has_nested_trees = true;
            // First resolve prefix `segments[0..seg_count]` to a target module/type scope:
            const prefix_scope = try resolveModulePathSegments(
                sym_table,
                interner,
                file_id,
                dest_module_scope,
                current_lookup_scope,
                segments[0..seg_count],
                source,
                token_buffer,
                diagnostic_sink,
            );
            if (!prefix_scope.isNone()) {
                try resolveUseTreeCst(
                    sym_table,
                    interner,
                    file_id,
                    dest_module_scope,
                    prefix_scope,
                    def_id,
                    is_pub,
                    sub_id,
                    source,
                    token_buffer,
                    cst_arena,
                    diagnostic_sink,
                );
            }
            cursor += @max(@as(usize, sub.subtree_size), 1);
            continue;
        }

        const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
        if (is_leaf and !sub.flags.is_missing_or_injected and
            !sub.token.isNone() and sub.token.asInt() < token_buffer.countTokens())
        {
            const tok_kind = token_buffer.getToken(sub.token).kind;
            if (tok_kind == .star) {
                is_glob = true;
            } else if (tok_kind == .kw_as) {
                has_seen_as = true;
            } else if (has_seen_as and (isIdentifierToken(tok_kind) or tok_kind == .underscore)) {
                alias_tok = sub.token;
            } else if (!has_seen_as and
                (isIdentifierToken(tok_kind) or tok_kind == .kw_self_val or tok_kind == .kw_self_type))
            {
                if (seg_count < segments.len) {
                    segments[seg_count] = sub.token;
                    seg_count += 1;
                }
            }
        }
        cursor += 1;
    }

    if (has_nested_trees or seg_count == 0) return;

    // [1] Glob import (`use prefix::*;`):
    if (is_glob) {
        const target_scope = try resolveModulePathSegments(
            sym_table,
            interner,
            file_id,
            dest_module_scope,
            current_lookup_scope,
            segments[0..seg_count],
            source,
            token_buffer,
            diagnostic_sink,
        );
        if (target_scope.isNone()) return;

        const members_snapshot = try sym_table.allocator.dupe(
            SymbolIndex,
            sym_table.getScopeMembers(target_scope),
        );
        defer sym_table.allocator.free(members_snapshot);

        for (members_snapshot) |member_idx| {
            const member = sym_table.getSymbol(member_idx).*;
            const vis_check = sym_table.checkSymbolVisibility(member_idx, dest_module_scope);
            if (vis_check != .found) continue;

            _ = try sym_table.defineSymbol(.{
                .name = member.name,
                .name_text = member.name_text,
                .kind = .use_alias_sym,
                .namespace = member.namespace,
                .visibility = if (is_pub) .public else .private,
                .flags = .{
                    .is_pub = is_pub,
                    .is_used = true,
                    .is_imported = true,
                },
                .scope_id = dest_module_scope,
                .def_id = def_id,
                .decl_span = member.decl_span,
                .type_id = member.type_id,
                .target_symbol = vis_check.found,
                .target_scope = member.target_scope,
            }, null);
        }
        return;
    }

    // [2] Single path import (`use prefix::Item [as Alias];`):
    const prefix_scope = if (seg_count > 1)
        try resolveModulePathSegments(
            sym_table,
            interner,
            file_id,
            dest_module_scope,
            current_lookup_scope,
            segments[0 .. seg_count - 1],
            source,
            token_buffer,
            diagnostic_sink,
        )
    else
        current_lookup_scope;

    if (prefix_scope.isNone()) return;

    const final_tok = segments[seg_count - 1];
    const final_lexeme = extractTokenSlice(source, token_buffer, final_tok);
    if (final_lexeme.len == 0) return;
    const final_sym_id = try interner.intern(final_lexeme);
    const final_span = token_buffer.getTokenSpan(file_id, final_tok);

    const lookup_res = if (seg_count == 1 and prefix_scope == dest_module_scope)
        sym_table.lookupLexical(prefix_scope, final_sym_id, NamespaceMask.ALL)
    else
        sym_table.lookupInTargetScope(prefix_scope, dest_module_scope, final_sym_id, NamespaceMask.ALL);

    switch (lookup_res) {
        .found => |resolved_idx| {
            sym_table.markSymbolUsed(resolved_idx);
            const target_rec = sym_table.getSymbol(resolved_idx).*;
            const bind_tok = if (!alias_tok.isNone()) alias_tok else final_tok;
            const bind_lexeme = extractTokenSlice(source, token_buffer, bind_tok);
            if (bind_lexeme.len == 0 or std.mem.eql(u8, bind_lexeme, "_")) return;

            const bind_sym_id = try interner.intern(bind_lexeme);
            const bind_span = token_buffer.getTokenSpan(file_id, bind_tok);
            _ = try sym_table.defineSymbol(.{
                .name = bind_sym_id,
                .name_text = interner.get(bind_sym_id),
                .kind = .use_alias_sym,
                .namespace = target_rec.namespace,
                .visibility = if (is_pub) .public else .private,
                .flags = .{
                    .is_pub = is_pub,
                    .is_used = true,
                    .is_imported = true,
                },
                .scope_id = dest_module_scope,
                .def_id = def_id,
                .decl_span = bind_span,
                .type_id = target_rec.type_id,
                .target_symbol = resolved_idx,
                .target_scope = target_rec.target_scope,
            }, diagnostic_sink);
        },
        .private_error => |priv_idx| {
            if (diagnostic_sink) |sink| {
                try emitPrivateAccessDiagnostic(sink, sym_table.getSymbol(priv_idx), final_span);
            }
        },
        .not_found => {
            // Check if `final_sym_id` is a registered cross-file module:
            if (sym_table.named_module_scopes.get(final_sym_id.asInt())) |ext_mod_scope| {
                const bind_tok = if (!alias_tok.isNone()) alias_tok else final_tok;
                const bind_lexeme = extractTokenSlice(source, token_buffer, bind_tok);
                if (bind_lexeme.len == 0 or std.mem.eql(u8, bind_lexeme, "_")) return;
                const bind_sym_id = try interner.intern(bind_lexeme);
                _ = try sym_table.defineSymbol(.{
                    .name = bind_sym_id,
                    .name_text = interner.get(bind_sym_id),
                    .kind = .module_sym,
                    .namespace = .value_ns,
                    .visibility = if (is_pub) .public else .private,
                    .flags = .{ .is_pub = is_pub, .is_used = true, .is_imported = true },
                    .scope_id = dest_module_scope,
                    .def_id = def_id,
                    .decl_span = token_buffer.getTokenSpan(file_id, bind_tok),
                    .target_scope = ext_mod_scope,
                }, diagnostic_sink);
                return;
            }
            if (diagnostic_sink) |sink| {
                const suggestion = if (seg_count == 1 and prefix_scope == dest_module_scope)
                    sym_table.suggestClosestSymbol(prefix_scope, final_lexeme, NamespaceMask.ALL)
                else
                    sym_table.suggestClosestInScope(prefix_scope, final_lexeme, NamespaceMask.ALL);
                try emitUnresolvedSymbolDiagnostic(
                    sink,
                    interner,
                    final_lexeme,
                    final_span,
                    suggestion,
                );
            }
        },
    }
}

/// Resolves a sequence of `module::submodule` path tokens to their target `ScopeId`.
pub fn resolveModulePathSegments(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    caller_scope: ScopeId,
    initial_scope: ScopeId,
    segments: []const TokenIndex,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    diagnostic_sink: ?*DiagnosticSink,
) !ScopeId {
    var cur_scope = initial_scope;
    for (segments, 0..) |seg_tok, i| {
        const seg_lexeme = extractTokenSlice(source, token_buffer, seg_tok);
        if (seg_lexeme.len == 0) return .none;
        if (std.mem.eql(u8, seg_lexeme, "self")) continue;

        const seg_sym_id = try interner.intern(seg_lexeme);
        const seg_span = token_buffer.getTokenSpan(file_id, seg_tok);
        if (i == 0 and std.mem.eql(u8, seg_lexeme, "std")) {
            _ = try sym_table.ensureStdMetaScope(interner);
        }
        const lookup_res = if (i == 0 and cur_scope == caller_scope)
            sym_table.lookupLexical(cur_scope, seg_sym_id, NamespaceMask.TYPE_OR_VALUE)
        else
            sym_table.lookupInTargetScope(cur_scope, caller_scope, seg_sym_id, NamespaceMask.TYPE_OR_VALUE);

        switch (lookup_res) {
            .found => |sym_idx| {
                sym_table.markSymbolUsed(sym_idx);
                const sym = sym_table.getSymbol(sym_idx);
                if (!sym.target_scope.isNone()) {
                    cur_scope = sym.target_scope;
                    continue;
                }
                if (sym_table.named_module_scopes.get(seg_sym_id.asInt())) |ext_scope| {
                    cur_scope = ext_scope;
                    continue;
                }
                return .none;
            },
            .private_error => |priv_idx| {
                if (diagnostic_sink) |sink| {
                    try emitPrivateAccessDiagnostic(sink, sym_table.getSymbol(priv_idx), seg_span);
                }
                return .none;
            },
            .not_found => {
                if (sym_table.named_module_scopes.get(seg_sym_id.asInt())) |ext_scope| {
                    cur_scope = ext_scope;
                    continue;
                }
                // Built-in virtual root prefixes (`std`, `core`, `pkg`) resolve to `caller_scope` when not shadowed:
                if (i == 0 and (std.mem.eql(u8, seg_lexeme, "std") or
                    std.mem.eql(u8, seg_lexeme, "core") or
                    std.mem.eql(u8, seg_lexeme, "pkg")))
                {
                    continue;
                }
                if (diagnostic_sink) |sink| {
                    const suggestion = if (i == 0 and cur_scope == caller_scope)
                        sym_table.suggestClosestSymbol(cur_scope, seg_lexeme, NamespaceMask.TYPE_OR_VALUE)
                    else
                        sym_table.suggestClosestInScope(cur_scope, seg_lexeme, NamespaceMask.TYPE_OR_VALUE);
                    try emitUnresolvedSymbolDiagnostic(
                        sink,
                        interner,
                        seg_lexeme,
                        seg_span,
                        suggestion,
                    );
                }
                return .none;
            },
        }
    }
    return cur_scope;
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_edit_distance_and_symbol_table_overload_and_visibility" {
    try std.testing.expectEqual(@as(u16, 0), computeEditDistance("counter", "counter"));
    try std.testing.expectEqual(@as(u16, 1), computeEditDistance("counter", "countr"));
    try std.testing.expectEqual(@as(u16, 1), computeEditDistance("counter", "conuter"));
    try std.testing.expectEqual(@as(u16, 1), computeEditDistance("MyType", "mytype"));

    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    var sym_table = try SymbolTable.init(std.testing.allocator, &interner);
    defer sym_table.deinit();

    // Verify built-in prelude types and groups (`i32`, `Number`, `Result`) are registered:
    const i32_name = try interner.intern("i32");
    const num_name = try interner.intern("Number");
    const i32_lookup = sym_table.lookupLexical(sym_table.prelude_scope, i32_name, NamespaceMask.TYPE_ONLY);
    const num_lookup = sym_table.lookupLexical(sym_table.prelude_scope, num_name, NamespaceMask.TYPE_ONLY);
    try std.testing.expect(i32_lookup == .found);
    try std.testing.expect(num_lookup == .found);
    try std.testing.expectEqual(TypeId.i32_ty, sym_table.getSymbol(i32_lookup.found).type_id);
    try std.testing.expectEqual(TypeId.group_number, sym_table.getSymbol(num_lookup.found).type_id);

    // Verify typo suggestion finds `"Number"` for `"Numbr"`:
    const suggestion = sym_table.suggestClosestSymbol(
        sym_table.prelude_scope,
        "Numbr",
        NamespaceMask.TYPE_ONLY,
    );
    try std.testing.expect(suggestion != null);
    try std.testing.expectEqualStrings("Number", suggestion.?);
}

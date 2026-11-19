//! Module & Lexical Scope Name Resolution, Visibility Hygiene & Overload Grouping
//!
//! Implements Phase 4 and Phase 7.6 (`PLAN.md` §2.1, `DR-02` Deliverable 2, `DR-03` §3, `DR-04`,
//! and `DR-22` `ADR-22D`/`ADR-22E`) lexical and module-level symbol resolution for CoreX:
//! - `ScopeArena` (`ScopeId`) with bounded lexical depth (`MAX_SCOPE_DEPTH = 512`) and parent chains,
//! - Disjoint `Namespace` (`type_ns`, `value_ns`, `const_ns`) $O(1)$ hash-table lookup,
//! - Module item collection (`mod`, `use`, `subscript`, `test`, `bench`, `bit_field`, `enum`),
//! - 4-tier visibility (`private` < `pub(super)` < `pub(pkg)` < `pub`, `E0409`/`E0433`) and `E0408`,
//! - Explicit `@overload` function and `subscript` set grouping (`DR-02` §1.4 & `DR-22` `SE-21`),
//! - Unused local binding and parameter warnings (`W0402`) with `_` prefix autofixes, and
//! - Stack-bounded Levenshtein + Jaro-Winkler prefix-boosted "did you mean?" typo suggestions (`E0403`).

const std = @import("std");
const builtin = @import("builtin");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const diagnostic = @import("diag/diagnostic.zig");
const query_db = @import("query_db.zig");
const codegen_abi = @import("codegen_abi.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const NodeIndex = mem_foundation.NodeIndex;
const ExtraIndex = mem_foundation.ExtraIndex;
pub const ScopeId = mem_foundation.ScopeId;
pub const PackageId = vfs_sourcemap.PackageId;
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
    /// Positive `if`/`while` `is` and `:=` condition-binding scope (`DR-21` `SE-01`/`SE-02`).
    condition_scope = 10,
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
    /// `true` inside a function returning `T!E` (`Result[T, E]`) or `T?`.
    is_inside_fallible_fn: bool = false,
    /// `true` inside a `subscript` `let { … }` or `inout { … }` accessor arm (`SE-21`).
    is_inside_subscript: bool = false,
    /// Reserved zero bits (`0`).
    reserved: u2 = 0,
};

/// Lexical or module scope record stored in `ScopeArena`.
pub const ScopeRecord = struct {
    /// Category of this scope.
    kind: ScopeKind,
    /// Inherited context flags (`unsafe`, `async`, `comptime`, loop, fallible, subscript).
    flags: ScopeFlags = .{},
    /// Enclosing parent `ScopeId` (`.none` for `.global_prelude`).
    parent: ScopeId = .none,
    /// Nearest enclosing `.module_scope` `ScopeId` for $O(1)$ visibility checks.
    enclosing_module: ScopeId = .none,
    /// Immediate parent `.module_scope` `ScopeId` across both inline `mod { … }` and external `mod foo;`.
    parent_module: ScopeId = .none,
    /// Owning compilation package (`PackageId`) for `pub(pkg)` visibility enforcement (`ADR-22E`).
    pkg_id: PackageId = .root,
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

/// Four-tier ordered visibility level of a declaration (`ADR-22E`: `private` < `pub(super)` < `pub(pkg)` < `pub`).
pub const Visibility = enum(u2) {
    /// Visible only within the defining module and its descendant submodules (`0`).
    private = 0,
    /// Visible within the immediate parent module and all of its descendant scopes (`pub(super)`, `1`).
    pub_super = 1,
    /// Visible anywhere inside the defining `PackageId` (`pub(pkg)`, `2`); excluded from `.cxi` exports.
    pub_pkg = 2,
    /// Exported publicly across packages and included in `.cxi` interface digests (`pub`, `3`).
    public = 3,

    /// Returns `true` only for unrestricted external `pub` (`Visibility.public`).
    pub inline fn isPublicOutsidePkg(self: Visibility) bool {
        return self == .public;
    }

    /// Returns `true` if `self` carries any `pub` modifier (`pub(super)`, `pub(pkg)`, or `pub`).
    pub inline fn isAnyPub(self: Visibility) bool {
        return self != .private;
    }

    /// Returns the canonical CoreX syntax spelling for `self`.
    pub inline fn asKeywordSlice(self: Visibility) []const u8 {
        return switch (self) {
            .private => "private",
            .pub_super => "pub(super)",
            .pub_pkg => "pub(pkg)",
            .public => "pub",
        };
    }

    /// Evaluates whether an item declared in `(def_mod_scope, def_pkg_id)` is accessible from `(caller_scope, caller_pkg_id)`.
    pub fn isVisibleFrom(
        self: Visibility,
        def_mod_scope: ScopeId,
        def_pkg_id: PackageId,
        caller_scope: ScopeId,
        caller_pkg_id: PackageId,
        scope_arena: *const ScopeArena,
    ) bool {
        return switch (self) {
            .public => true,
            .pub_pkg => {
                if (def_pkg_id == caller_pkg_id) return true;
                return def_mod_scope.isNone() or scope_arena.isWithinModule(caller_scope, def_mod_scope);
            },
            .pub_super => {
                if (def_pkg_id != caller_pkg_id) return false;
                if (def_mod_scope.isNone()) return true;
                const parent_mod = scope_arena.findImmediateParentModule(def_mod_scope);
                const boundary_mod = if (!parent_mod.isNone()) parent_mod else def_mod_scope;
                return scope_arena.isWithinModule(caller_scope, boundary_mod);
            },
            .private => {
                if (def_pkg_id != caller_pkg_id) return false;
                return def_mod_scope.isNone() or scope_arena.isWithinModule(caller_scope, def_mod_scope);
            },
        };
    }
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
    /// Explicit `@overload` function or `subscript` group entry (`DR-02` §1.4 & `SE-21`) (`13`).
    overload_group_sym = 13,
    /// Compile-time `const` declaration (`14`).
    const_sym = 14,
    /// Compile-time `const N: usize` generic parameter (`15`).
    const_param_sym = 15,
    /// Function, method, or closure value parameter (`16`).
    param_sym = 16,
    /// Immutable local `let` binding (`17`).
    local_let_sym = 17,
    /// Mutable local `var` binding (`18`).
    local_var_sym = 18,
    /// Variant inside an `enum` declaration (`19`).
    enum_variant_sym = 19,
    /// Field inside a `struct`, `union`, or `bit_field` declaration (`20`).
    field_sym = 20,
    /// Foreign linker `extern static [mut]` variable declaration (`21`).
    extern_static_sym = 21,
};

/// 1-byte bit-packed mask of compiler-synthesized `@derive(…)` traits (`DR-05` §2.3 & `DR-22` `SE-10B`).
pub const DeriveMask = packed struct(u8) {
    /// `@derive(Eq)` (`fn eq(&self, other: &Self) -> bool`).
    has_eq: bool = false,
    /// `@derive(Hash)` (`fn hash(&self) -> u64`).
    has_hash: bool = false,
    /// `@derive(Debug)` (`fn debug(&self) -> str`).
    has_debug: bool = false,
    /// `@derive(Clone)` (`fn clone(&self) -> Self`).
    has_clone: bool = false,
    /// `@derive(From)` single-field enum variant error/payload upcasting synthesis (`SE-10B`).
    has_from: bool = false,
    /// `@derive(Copy)` bitwise copy marker synthesis.
    has_copy: bool = false,
    /// Reserved padding bits (`0`).
    reserved: u2 = 0,

    comptime {
        std.debug.assert(@sizeOf(DeriveMask) == 1);
    }

    /// Returns `true` if at least one built-in `@derive` trait is requested.
    pub inline fn hasAny(self: DeriveMask) bool {
        return self.has_eq or self.has_hash or self.has_debug or self.has_clone or self.has_from or self.has_copy;
    }
};

/// 2-byte bit-packed Phase 7.6 & Phase 8 declaration attributes and item kind discriminators (`DR-22`, `DR-08`).
pub const DeclExtraFlags = packed struct(u16) {
    /// `true` if annotated with `@constructor` (`SE-22` constructor delegation).
    is_constructor: bool = false,
    /// `true` if annotated with `@builder` (`SE-22` declarative builder parameter/closure).
    is_builder: bool = false,
    /// `true` if annotated with `@builder_item` (`SE-22` builder-scoped call guard, `E0436`).
    is_builder_item: bool = false,
    /// `true` if an explicit integer argument was written in `@repr(u8..u128 / i8..i128)` (`ADR-22D`).
    has_repr_int: bool = false,
    /// `true` if declared via `subscript(…) -> T { … }` (`SE-21`).
    is_subscript: bool = false,
    /// `true` if declared via `test "…" { … }` (`SE-16`).
    is_test: bool = false,
    /// `true` if declared via `bench "…" (b: &var Bencher) { … }` (`SE-16`).
    is_bench: bool = false,
    /// `true` if the parameter list ends with C FFI variadic `...` (`ADR-22F`).
    is_variadic: bool = false,
    /// `true` if annotated with `@not_send` (`DR-08` cross-thread `!Send` marker).
    is_not_send: bool = false,
    /// `true` if annotated with `@not_sync` (`DR-08` shared-reference `!Sync` marker).
    is_not_sync: bool = false,
    /// `true` if annotated with `@thread_local` (`DR-08` / `DR-10` thread-local storage marker).
    is_thread_local: bool = false,
    /// `true` if annotated with `@trusted` (`DR-10` §2.3 safe FFI contract).
    is_trusted_ffi: bool = false,
    /// Reserved zero padding bits (`0`).
    reserved: u4 = 0,

    comptime {
        std.debug.assert(@sizeOf(DeclExtraFlags) == 2);
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
    /// `true` if declared with `var` (`&var` or `var` local/parameter).
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
    /// Canonical 8-capability supply-chain/OS mask recorded in `corex.lock` (`0x033F`).
    pub const LOCKFILE_CAP_BITS: u16 = FS | NET | ENV | PROCESS | FFI | UNSAFE_OP | CLOCK | ENTROPY;
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
    /// Four-tier visibility (`private`, `pub_super`, `pub_pkg`, `public`).
    visibility: Visibility,
    /// Bit-packed attribute and usage flags.
    flags: SymbolFlags = .{},
    /// Phase 7.6 `@constructor`, `@builder`, `@builder_item`, `subscript`/`test`/`bench`, and variadic flags.
    extra_flags: DeclExtraFlags = .{},
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
    /// Parsed `@derive(Eq, Hash, Debug, Clone, From, Copy)` bitmask on nominal `struct` / `enum` / `union` items.
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
    /// Explicit discriminant width in bits on `@repr(C)` or integer-backed `enum` declarations (`0` = default).
    repr_tag_bits: u8 = 0,
    /// Explicit power-of-two alignment encoded as `log2(align) + 1` (`0` = default).
    explicit_align_log2_plus1: u8 = 0,
    /// `true` if the declaration (or an enclosing `impl`) carries at least one `@cfg(…)` attribute (`SE-18`).
    has_cfg_attr: bool = false,
    /// Optional enclosing `impl` CST node carrying `@cfg(…)` (`CstNodeIndex.none` when absent).
    enclosing_cfg_cst: CstNodeIndex = .none,
};

/// Target operating-system selector evaluated inside `@cfg(target.os == .Linux)` (`SE-18`).
pub const CfgOs = enum(u8) {
    /// Linux (`ELF64`).
    linux = 0,
    /// Apple macOS (`Mach-O`).
    macos = 1,
    /// Microsoft Windows (`PE/COFF`).
    windows = 2,
    /// WebAssembly System Interface (`WASI`).
    wasi = 3,
    /// Bare-metal freestanding target (`no_os`).
    freestanding = 4,
};

/// Target CPU architecture selector evaluated inside `@cfg(target.arch == .X86_64)` (`SE-18`).
pub const CfgArch = enum(u8) {
    /// 64-bit x86 (`AMD64` / `Intel 64`).
    x86_64 = 0,
    /// 64-bit ARM (`ARMv8-A` / Apple Silicon).
    aarch64 = 1,
    /// 32-bit WebAssembly (`wasm32`).
    wasm32 = 2,
    /// 64-bit RISC-V (`riscv64`).
    riscv64 = 3,
};

/// Target ABI environment selector evaluated inside `@cfg(target.abi == .Gnu)` (`SE-18`).
pub const CfgAbi = enum(u8) {
    /// System V / GNU C ABI (`gnu`).
    gnu = 0,
    /// Microsoft Visual C++ x64 / ARM64 ABI (`msvc`).
    msvc = 1,
    /// Static `musl` C ABI (`musl`).
    musl = 2,
    /// Apple Darwin ABI (`apple`).
    apple = 3,
    /// WebAssembly WASI Preview 1 ABI (`wasi`).
    wasi = 4,
    /// Bare-metal freestanding ABI (`none`).
    none = 5,
};

/// Target byte-order selector evaluated inside `@cfg(target.endian == .Little)` (`SE-18`).
pub const CfgEndian = enum(u8) {
    /// Little-endian byte order (`x86_64`, `aarch64`, `wasm32`).
    little = 0,
    /// Big-endian byte order.
    big = 1,
};

/// Compile-time `@cfg(expr)` target and build-mode evaluation context (`DR-22` `SE-18`).
pub const CfgEnv = struct {
    /// Active target operating system.
    os: CfgOs = defaultHostOs(),
    /// Active target CPU architecture.
    arch: CfgArch = defaultHostArch(),
    /// Active target C ABI flavor.
    abi: CfgAbi = defaultHostAbi(),
    /// Active target byte endianness.
    endian: CfgEndian = .little,
    /// Active target pointer bit width (`64` or `32`).
    ptr_width: u16 = 64,
    /// `true` in debug / development builds (`cfg.debug`).
    is_debug: bool = true,
    /// `true` when compiling `test` / `bench` blocks (`cfg.test_mode`).
    is_test_mode: bool = true,
    /// `true` in deterministic simulation mode (`cfg.sim_mode`).
    is_sim_mode: bool = false,
    /// `true` under coverage-guided fuzzing (`cfg.fuzz_mode`).
    is_fuzz_mode: bool = false,
    /// Enabled package feature names (`cfg.feature.<name>`).
    enabled_features: []const []const u8 = &.{},
    /// Optional declared package feature allowlist from `corex.toml`; undeclared names emit `E0435` when set.
    declared_features: ?[]const []const u8 = null,
    /// Additional enabled CPU feature strings queried by `target.cpu_has("…")`.
    enabled_cpu_features: []const []const u8 = &.{},
    /// Owning `PackageId` when bound to a multi-package `SymbolTable` (`PackageId.root` by default).
    owner_pkg_id: PackageId = .root,
    /// Optional read-only `SymbolTable` supplying per-`PackageId` declared/enabled feature sets (`E0435`).
    sym_table_features: ?*const SymbolTable = null,

    /// Returns the host `CfgOs` inferred at Stage 0 compile time.
    pub fn defaultHostOs() CfgOs {
        return switch (builtin.os.tag) {
            .linux => .linux,
            .macos => .macos,
            .windows => .windows,
            .wasi => .wasi,
            .freestanding => .freestanding,
            else => .linux,
        };
    }

    /// Returns the host `CfgArch` inferred at Stage 0 compile time.
    pub fn defaultHostArch() CfgArch {
        return switch (builtin.cpu.arch) {
            .x86_64 => .x86_64,
            .aarch64 => .aarch64,
            .wasm32 => .wasm32,
            else => .x86_64,
        };
    }

    /// Returns the default `CfgAbi` matching `defaultHostOs()`.
    pub fn defaultHostAbi() CfgAbi {
        return switch (builtin.os.tag) {
            .windows => .msvc,
            .macos => .apple,
            .wasi => .wasi,
            .freestanding => .none,
            else => .gnu,
        };
    }

    /// Constructs a `CfgEnv` synchronized with `spec` and `is_including_tests`.
    pub fn fromTargetSpec(spec: codegen_abi.TargetSpec, is_including_tests: bool) CfgEnv {
        return .{
            .os = switch (spec.os) {
                .linux => .linux,
                .macos => .macos,
                .windows => .windows,
                .wasi => .wasi,
                .freestanding => .freestanding,
            },
            .arch = switch (spec.arch) {
                .x86_64 => .x86_64,
                .aarch64 => .aarch64,
                .wasm32 => .wasm32,
            },
            .abi = switch (spec.abi) {
                .gnu => .gnu,
                .msvc => .msvc,
                .musl => .musl,
                .apple => .apple,
                .wasi => .wasi,
                .none => .none,
            },
            .endian = .little,
            .ptr_width = @as(u16, spec.ptrBytes()) * 8,
            .is_test_mode = is_including_tests,
        };
    }
};

/// Bit-packed 32-bit FFI boundary SAST contract for a single `extern` function parameter (`DR-10` §2.3).
pub const FfiParamContract = packed struct(u32) {
    /// `true` if annotated with `@slice_len(param_ident)` (`len * sizeof(T)` spatial bound).
    has_slice_len: bool = false,
    /// `true` if annotated with `@byte_len(param_ident)` (raw byte-length spatial bound).
    has_byte_len: bool = false,
    /// Zero-based ordinal of the paired integer length parameter when `has_slice_len` or `has_byte_len` is `true`.
    len_param_ordinal: u8 = 0,
    /// `true` if annotated with `@null_terminated` (`E0308` NUL-termination proof required).
    is_null_terminated: bool = false,
    /// `true` if annotated with `@consumes` (transfers linear ownership / frees pointer, `E0310` / `E0301`).
    is_consumes: bool = false,
    /// `true` if annotated with `@escapes` (forbids stack/local-region pointers, `E0306`).
    is_escapes: bool = false,
    /// `true` if annotated with `@borrowed` (non-escaping foreign borrow).
    is_borrowed: bool = false,
    /// `true` if annotated with `@out_param` (permits `&raw mut uninit` and marks initialized on return).
    is_out_param: bool = false,
    /// `true` if annotated with `@may_be_null` (permits nullable pointer arguments; formal param starts `maybe_null`).
    is_may_be_null: bool = false,
    /// `true` if annotated with `@non_null` (explicitly forbids `maybe_null` pointers, `E0311`).
    is_non_null: bool = false,
    /// Reserved zero padding (`0`).
    reserved: u15 = 0,

    comptime {
        std.debug.assert(@sizeOf(FfiParamContract) == 4);
    }
};

/// Sparse FFI linkage and SAST contract metadata stored in `SymbolTable.ffi_contracts` (`0` overhead on pure `.cx`).
pub const FfiFnContract = struct {
    /// `true` if annotated with `@trusted` (safe to call/read outside `unsafe { … }`, still emits `.ffi`).
    is_trusted: bool = false,
    /// `true` if annotated with `@thread_local` on an `extern static` variable.
    is_thread_local: bool = false,
    /// `true` if declared inside `unsafe extern { … }` or with explicit `unsafe`.
    is_unsafe_extern: bool = false,
    /// `true` if return value is annotated with `@owned_by_caller` (linear leak obligation, `E0304`).
    is_ret_owned_by_caller: bool = false,
    /// `true` if return pointer is annotated with `@may_be_null` (unchecked deref/use emits `E0311`).
    is_ret_may_be_null: bool = false,
    /// `true` if return pointer is annotated with `@non_null`.
    is_ret_non_null: bool = false,
    /// `true` if return pointer is annotated with `@null_terminated` (satisfies downstream `E0308`).
    is_ret_null_terminated: bool = false,
    /// Expected `@consumes` deallocator `SymbolIndex` resolved from `@free_with(fn_ident)` (`.none` when unconstrained).
    ret_free_with_sym: SymbolIndex = .none,
    /// Interned ABI string literal (e.g., `"C"`, `"system"`, `"C-unwind"`, `"wasm"`, `.empty` for default `"C"`).
    abi_name: SymbolId = .empty,
    /// Interned Wasm host import module name from `@wasm_import("mod", "name")` (`.empty` when absent).
    wasm_import_module: SymbolId = .empty,
    /// Interned Wasm host import symbol name from `@wasm_import("mod", "name")` (`.empty` when absent).
    wasm_import_name: SymbolId = .empty,
    /// Interned Wasm export name from `@wasm_export("name")` (`.empty` when absent).
    wasm_export_name: SymbolId = .empty,
    /// Interned native library link directive from `@link_lib("name")` (`.empty` when absent).
    link_lib_name: SymbolId = .empty,
    /// Owned per-parameter FFI contract slice indexed by fixed parameter ordinal (`&.{}` when none).
    param_contracts: []FfiParamContract = &.{},
};

/// Strongly typed callback invoked when `@c_import("header.h")` is evaluated on an uncached header path.
pub const CImportModuleLoader = *const fn (
    sym_table: *SymbolTable,
    interner: *StringInterner,
    caller_file_id: FileId,
    header_path: []const u8,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!SymbolIndex;

/// Per-parameter metadata stored on `SymbolTable` for parameter zones, defaults, and builders (`SE-07`, `SE-11`, `SE-22`).
pub const FnParamSpec = struct {
    /// Interned parameter identifier (`SymbolId.empty` for unnamed or variadic parameters).
    name: SymbolId = .empty,
    /// Borrowed UTF-8 slice for `name` from `StringInterner`.
    name_text: []const u8 = "",
    /// `true` when this parameter declares `= DefaultExpr`.
    has_default: bool = false,
    /// AST node index of `DefaultExpr` inside `decl_file_id`'s `AstArena` (`.none` when `!has_default`).
    default_ast_node: NodeIndex = .none,
    /// Owning source file `FileId` containing `default_ast_node`.
    decl_file_id: FileId = .none,
    /// Enclosing top-level `DefId` owning this function or method declaration.
    owner_def_id: DefId = .NONE,
    /// Principal `TypeId` synthesized for `default_ast_node` (`TypeId.err_ty` until checked).
    default_type_id: TypeId = .err_ty,
    /// `true` when referenced by a subsequent parameter's `default_ast_node` (`SE-07`, suppresses `W0402`).
    is_used_by_default: bool = false,
    /// `true` when declared before PEP 570 `/` positional-only separator (`SE-11`, `E0428`).
    is_positional_only: bool = false,
    /// `true` when declared after PEP 3102 `*` keyword-only separator (`SE-11`, `E0429`).
    is_keyword_only: bool = false,
    /// `true` when this entry represents a trailing C variadic `...` parameter (`ADR-22F`).
    is_variadic: bool = false,
    /// `true` when declared with `var x: T` local-rebindable value parameter mutability (`ADR-22B`).
    is_local_var: bool = false,
    /// `true` when annotated with `@builder` (`SE-22` declarative closure builder parameter).
    is_builder: bool = false,
    /// `true` when default expression is `@caller_location()` (`SE-18`).
    is_caller_location_default: bool = false,
};

/// Result of extracting CST parameter-zone, mutability, builder, and variadic metadata from an item signature.
pub const ExtractedFnParams = struct {
    /// Heap-allocated `FnParamSpec` slice owned by caller.
    specs: []FnParamSpec,
    /// `true` when the parameter list ends with C variadic `...` (`ADR-22F`).
    is_variadic: bool = false,
};

/// Per-generic-parameter metadata stored on `SymbolTable` for generic defaults (`SE-10`).
pub const GenericParamSpec = struct {
    /// Interned generic parameter identifier (`T` or `N`).
    name: SymbolId = .empty,
    /// Borrowed UTF-8 slice for `name` from `StringInterner`.
    name_text: []const u8 = "",
    /// `true` when declared with `const` (`const N: usize = 8`).
    is_const: bool = false,
    /// `true` when this generic parameter declares `= DefaultType` or `= DefaultExpr`.
    has_default: bool = false,
    /// `true` when this generic parameter declares an explicit `: ConstraintExpr` or `: Type` bound.
    has_explicit_bound: bool = false,
    /// Resolved default `TypeId` for type parameters (`TypeId.err_ty` until resolved).
    default_type_id: TypeId = .err_ty,
    /// Interned trailing type identifier of `= DefaultType` when syntactically named (`SymbolId.empty` otherwise).
    default_type_sym: SymbolId = .empty,
    /// AST node index of the default type or const expression inside `decl_file_id` (`.none` when `!has_default`).
    default_ast_node: NodeIndex = .none,
    /// Deterministic structural hash of the raw default CST tokens (`0` when `!has_default`).
    default_syntax_hash: u64 = 0,
};

/// Explicit `@overload` function or `subscript` group tracking all member `fn_sym` symbols in a scope (`DR-02`).
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
    /// Four-tier re-export visibility (`private`, `pub(super)`, `pub(pkg)`, `pub`) on `use`.
    visibility: Visibility = .private,
    /// AST node index of the `use_decl`.
    ast_node: NodeIndex,
    /// CST node index of the `use_item`.
    cst_node: CstNodeIndex,
};

/// Result of looking up a symbol with visibility verification.
pub const LookupResult = union(enum) {
    /// Symbol was found and is accessible from the caller's scope.
    found: SymbolIndex,
    /// Symbol exists but violates module/package visibility from the caller's scope (`E0409`/`E0433`).
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
    /// `@builder` declarative builder closure/parameter attribute (`SE-22`).
    builder,
    /// `@builder_item` builder-scoped call guard attribute (`SE-22`, `E0436`).
    builder_item,
    /// `@cache_aligned` target L1/L2 cache-line alignment attribute (`DR-20` `D-10A`).
    cache_aligned,
    /// `@constructor` primary/secondary constructor attribute (`SE-22`).
    constructor,
    /// `@derive(Eq, Hash, Debug, Clone, From, Copy)` trait synthesis attribute.
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
    /// `@link_lib("…")` native library link directive attribute (`DR-10`).
    link_lib,
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
    /// Retired `@noalloc` spelling emitting `E0225` with `@no_alloc` fix (`ADR-22D`).
    noalloc,
    /// `@not_send` negative concurrency marker (`DR-08` `!Send`).
    not_send,
    /// `@not_sync` negative concurrency marker (`DR-08` `!Sync`).
    not_sync,
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
    /// `@thread_local` foreign thread-local static storage attribute (`DR-10`).
    thread_local,
    /// `@trusted` safe-callable FFI contract attribute (`DR-10` §2.3).
    trusted,
    /// `@wasm_export("name")` WebAssembly module export attribute (`DR-10`).
    wasm_export,
    /// `@wasm_import("mod", "name")` WebAssembly host import attribute (`DR-10`).
    wasm_import,
    /// `@zero_pad` deterministic padding zeroing attribute (`DR-20`).
    zero_pad,
};

/// Descriptor for a built-in `cx.meta` reflection mirror type stub (`DR-05` §3.3 & `DR-21`).
const CxMetaMirrorStub = struct {
    /// Canonical `PascalCase` reflection mirror type name.
    name: []const u8,
    /// Nominal symbol kind (`.struct_sym` or `.enum_sym`).
    kind: SymbolKind,
};

/// Paired AST/CST node handles for a function-like item (`.fn_decl`, `.subscript_decl`, `.test_decl`, `.bench_decl`).
pub const FnDeclSyntaxHandle = struct {
    /// Lowered AST node index.
    ast_node: NodeIndex,
    /// Lossless CST node index.
    cst_node: CstNodeIndex,
};

/// Zero-padding 8-byte key binding `(caller_pkg, alias_sym)` in `SymbolTable.package_dep_scopes`.
pub const PkgDepKey = extern struct {
    /// Importing caller package handle.
    caller_pkg: PackageId,
    /// Explicit zero padding guaranteeing unique C-ABI byte representation (`std.AutoHashMapUnmanaged`-safe).
    _pad: u16 = 0,
    /// Interned `snake_case` dependency alias identifier.
    alias_sym: SymbolId,

    comptime {
        std.debug.assert(@sizeOf(PkgDepKey) == 8);
        std.debug.assert(std.meta.hasUniqueRepresentation(PkgDepKey));
    }
};

/// Zero-padding 8-byte key binding `(pkg_id, feature_sym)` in `SymbolTable.package_declared_features`.
pub const PkgFeatureKey = extern struct {
    /// Owning package handle.
    pkg_id: PackageId,
    /// Explicit zero padding guaranteeing unique C-ABI byte representation (`std.AutoHashMapUnmanaged`-safe).
    _pad: u16 = 0,
    /// Interned feature flag name (`SymbolId`).
    feature_sym: SymbolId,

    comptime {
        std.debug.assert(@sizeOf(PkgFeatureKey) == 8);
        std.debug.assert(std.meta.hasUniqueRepresentation(PkgFeatureKey));
    }
};

/// Per-`PackageId` identity and SemVer origin record for `E0012` diagnostics and multi-package mangling.
pub const PackageIdentityMeta = struct {
    /// Assigned `PackageId`.
    pkg_id: PackageId,
    /// Canonical `kebab-case` package name (`SymbolId`, e.g., `"corex-http"`).
    canonical_name_sym: SymbolId,
    /// Borrowed canonical package name (`"corex-http"`).
    canonical_name: []const u8,
    /// Borrowed formatted SemVer text (`"1.8.0"`, interned in `StringInterner`).
    version_text: []const u8,
    /// Default `snake_case` display alias (`"corex_http"`).
    display_alias: []const u8 = "",
    /// Root `FileId` (`src/root.cx` or `src/main.cx`) of this package.
    root_file_id: FileId = .none,
};

/// Extracted metadata for a single `@cfg`-active `use "<spec>" as <snake_alias>;` item (`DR-11` §2.1).
pub const InlineUseImport = struct {
    /// Source file containing the inline import.
    file_id: FileId,
    /// Unquoted `<url_or_registry_spec>` slice allocated in caller's allocator.
    spec_text: []const u8,
    /// Interned `<snake_alias>` `SymbolId`.
    alias_sym: SymbolId,
    /// Borrowed `<snake_alias>` slice from `interner`.
    alias_text: []const u8,
    /// Re-export visibility (`private`, `pub_super`, `pub_pkg`, `public`).
    visibility: Visibility,
    /// Byte span of the string literal token.
    spec_span: Span,
    /// Byte span of the full `use` item.
    decl_span: Span,
    /// `true` if the enclosing item carries any `@cfg(…)` attribute.
    is_cfg_conditional: bool = false,
};

/// Dormant capability scan result over `@cfg`-disabled CST subtrees in a file (`DR-17` §3.1).
pub const InactiveCfgCapScan = struct {
    /// Raw 12-bit capability mask (`CapabilityBits`) found inside any `@cfg`-disabled subtree.
    all_inactive_caps_bits: u16 = 0,
    /// Raw 12-bit capability mask (`CapabilityBits`) found inside `@cfg`-disabled `pub` items/impls/bodies.
    pub_inactive_caps_bits: u16 = 0,
    /// Raw 12-bit capability mask (`CapabilityBits`) found on `@cfg`-disabled exported/linked items.
    link_ambient_inactive_caps_bits: u16 = 0,
    /// Span of the first capability-bearing token inside an inactive `@cfg` branch.
    first_inactive_cap_span: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 },
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum lexical scope nesting depth (`512`, matching `syntax_arenas.MAX_PARSE_DEPTH`).
pub const MAX_SCOPE_DEPTH: usize = 512;

/// Maximum identifier byte length evaluated by the stack-allocated Levenshtein matrix (`64`).
pub const MAX_EDIT_DISTANCE_LEN: usize = 64;

/// Built-in trait names pre-populated in `.global_prelude` (`DR-02`, `DR-04`, `DR-06` & `DR-22` `SE-10B`).
pub const BUILTIN_TRAIT_NAMES = [_][]const u8{
    "AutoDrop",
    "Clone",
    "Copy",
    "Debug",
    "Default",
    "Display",
    "Drop",
    "Eq",
    "From",
    "FromError",
    "Hash",
    "Iterator",
    "Ord",
    "Send",
    "Sync",
};

/// Canonical table of 8 value-based reflection mirror stubs in `cx.meta` (`DR-05` §3.3 & `DR-21`).
const CX_META_MIRROR_STUBS = [8]CxMetaMirrorStub{
    .{ .name = "EnumInfo", .kind = .struct_sym },
    .{ .name = "FieldInfo", .kind = .struct_sym },
    .{ .name = "MetaId", .kind = .struct_sym },
    .{ .name = "PrimKind", .kind = .enum_sym },
    .{ .name = "StructInfo", .kind = .struct_sym },
    .{ .name = "TypeInfo", .kind = .struct_sym },
    .{ .name = "TypeKind", .kind = .enum_sym },
    .{ .name = "VariantInfo", .kind = .struct_sym },
};

/// Built-in primitive, runtime nominal, and Constrained Type Group mappings in `.global_prelude` (`DR-04`, `DR-22`).
pub const BuiltinTypeEntry = struct {
    /// Surface identifier in `.cx` source code.
    name: []const u8,
    /// Pre-assigned static `TypeId` (`0..50`).
    type_id: TypeId,
    /// `true` if this entry is one of the 12 Constrained Type Groups (`32..36`, `38..44`).
    is_group: bool,
};

/// Canonical table of 20 primitive types, 6 built-in runtime types, and 12 Constrained Type Groups (`DR-22`).
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
    .{ .name = "opaque", .type_id = .opaque_ty, .is_group = false },
    .{ .name = "Signed", .type_id = .group_signed, .is_group = true },
    .{ .name = "Unsigned", .type_id = .group_unsigned, .is_group = true },
    .{ .name = "Integer", .type_id = .group_integer, .is_group = true },
    .{ .name = "Float", .type_id = .group_float, .is_group = true },
    .{ .name = "Number", .type_id = .group_number, .is_group = true },
    .{ .name = "Comparable", .type_id = .group_comparable, .is_group = true },
    .{ .name = "Equatable", .type_id = .group_equatable, .is_group = true },
    .{ .name = "Bytes", .type_id = .group_bytes, .is_group = true },
    .{ .name = "Scalar", .type_id = .group_scalar, .is_group = true },
    .{ .name = "Copy", .type_id = .group_copy, .is_group = true },
    .{ .name = "FromBytes", .type_id = .group_from_bytes, .is_group = true },
    .{ .name = "IntoBytes", .type_id = .group_into_bytes, .is_group = true },
    .{ .name = "SourceLoc", .type_id = .source_loc_ty, .is_group = false },
    .{ .name = "FmtSpec", .type_id = .fmt_spec_ty, .is_group = false },
    .{ .name = "FmtArgs", .type_id = .fmt_args_ty, .is_group = false },
    .{ .name = "Bencher", .type_id = .bencher_ty, .is_group = false },
    .{ .name = "TaskGroup", .type_id = .task_group_base_ty, .is_group = false },
    .{ .name = "TaskHandle", .type_id = .task_handle_base_ty, .is_group = false },
};

/// $O(1)$ static lookup map from built-in primitive, runtime, and Constrained Type Group names to `TypeId`.
pub const BUILTIN_TYPE_AND_GROUP_MAP = std.StaticStringMap(TypeId).initComptime(.{
    .{ "Bencher", .bencher_ty },
    .{ "Bytes", .group_bytes },
    .{ "Comparable", .group_comparable },
    .{ "Copy", .group_copy },
    .{ "Equatable", .group_equatable },
    .{ "Float", .group_float },
    .{ "FmtArgs", .fmt_args_ty },
    .{ "FmtSpec", .fmt_spec_ty },
    .{ "FromBytes", .group_from_bytes },
    .{ "Integer", .group_integer },
    .{ "IntoBytes", .group_into_bytes },
    .{ "Number", .group_number },
    .{ "Scalar", .group_scalar },
    .{ "Signed", .group_signed },
    .{ "SourceLoc", .source_loc_ty },
    .{ "TaskGroup", .task_group_base_ty },
    .{ "TaskHandle", .task_handle_base_ty },
    .{ "Unsigned", .group_unsigned },
    .{ "bool", .bool_ty },
    .{ "char", .char_ty },
    .{ "f32", .f32_ty },
    .{ "f64", .f64_ty },
    .{ "i128", .i128_ty },
    .{ "i16", .i16_ty },
    .{ "i32", .i32_ty },
    .{ "i64", .i64_ty },
    .{ "i8", .i8_ty },
    .{ "isize", .isize_ty },
    .{ "never", .never_ty },
    .{ "opaque", .opaque_ty },
    .{ "str", .str_ty },
    .{ "u128", .u128_ty },
    .{ "u16", .u16_ty },
    .{ "u32", .u32_ty },
    .{ "u64", .u64_ty },
    .{ "u8", .u8_ty },
    .{ "unit", .unit_ty },
    .{ "usize", .usize_ty },
});

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
    .{ "i128", 128 },
    .{ "i16", 16 },
    .{ "i32", 32 },
    .{ "i64", 64 },
    .{ "i8", 8 },
    .{ "isize", 64 },
    .{ "u128", 128 },
    .{ "u16", 16 },
    .{ "u32", 32 },
    .{ "u64", 64 },
    .{ "u8", 8 },
    .{ "usize", 64 },
});

/// $O(1)$ static lookup map of the 13 canonical C primitive type aliases exempt from `W0201` `PascalCase` checks.
pub const C_PRIMITIVE_TYPE_ALIAS_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "c_char", {} },
    .{ "c_int", {} },
    .{ "c_long", {} },
    .{ "c_longdouble", {} },
    .{ "c_longlong", {} },
    .{ "c_schar", {} },
    .{ "c_short", {} },
    .{ "c_uchar", {} },
    .{ "c_uint", {} },
    .{ "c_ulong", {} },
    .{ "c_ulonglong", {} },
    .{ "c_ushort", {} },
    .{ "c_void", {} },
});

/// $O(1)$ static lookup map from declaration `@attr` identifiers to `HeaderAttrKind`.
const HEADER_ATTR_MAP = std.StaticStringMap(HeaderAttrKind).initComptime(.{
    .{ "align", .align_attr },
    .{ "attribute_schema", .attribute_schema },
    .{ "builder", .builder },
    .{ "builder_item", .builder_item },
    .{ "cache_aligned", .cache_aligned },
    .{ "constructor", .constructor },
    .{ "derive", .derive },
    .{ "export", .export_attr },
    .{ "extern", .extern_attr },
    .{ "from", .from },
    .{ "ifunc", .ifunc },
    .{ "linear", .linear },
    .{ "link_lib", .link_lib },
    .{ "link_name", .link_name },
    .{ "link_section", .link_section },
    .{ "local", .local },
    .{ "max_stack", .max_stack },
    .{ "must_use", .must_use },
    .{ "no_alloc", .no_alloc },
    .{ "no_block", .no_block },
    .{ "no_panic", .no_panic },
    .{ "noalloc", .noalloc },
    .{ "not_send", .not_send },
    .{ "not_sync", .not_sync },
    .{ "overload", .overload },
    .{ "packed", .packed_attr },
    .{ "repr", .repr },
    .{ "secret", .secret },
    .{ "soa", .soa },
    .{ "std_cap_boundary", .std_cap_boundary },
    .{ "thread_local", .thread_local },
    .{ "trusted", .trusted },
    .{ "wasm_export", .wasm_export },
    .{ "wasm_import", .wasm_import },
    .{ "zero_pad", .zero_pad },
});

/// $O(1)$ static lookup map from built-in `@derive` trait identifiers to `DeriveMask` bits.
const DERIVE_TRAIT_MAP = std.StaticStringMap(DeriveMask).initComptime(.{
    .{ "Clone", DeriveMask{ .has_clone = true } },
    .{ "Copy", DeriveMask{ .has_copy = true } },
    .{ "Debug", DeriveMask{ .has_debug = true } },
    .{ "Eq", DeriveMask{ .has_eq = true } },
    .{ "From", DeriveMask{ .has_from = true } },
    .{ "Hash", DeriveMask{ .has_hash = true } },
});

/// Sandbox-bypass attributes strictly forbidden inside external packages (`PackageId >= 2`, `E0327`).
const FORBIDDEN_EXTERNAL_PKG_ATTR_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "allow_unsafe_in_safe", {} },
    .{ "export_section", {} },
    .{ "ifunc", {} },
    .{ "link_section", {} },
    .{ "naked", {} },
    .{ "std_cap_boundary", {} },
    .{ "trusted", {} },
    .{ "used", {} },
});

/// $O(1)$ static lookup map from `cx.<domain>` / `core.<domain>` submodules to `CapabilityBits` (`DR-17`).
const CX_DOMAIN_CAP_MAP = std.StaticStringMap(u16).initComptime(.{
    .{ "clock", CapabilityBits.CLOCK },
    .{ "crypto", CapabilityBits.ENTROPY },
    .{ "env", CapabilityBits.ENV },
    .{ "ffi", CapabilityBits.FFI },
    .{ "fs", CapabilityBits.FS },
    .{ "http", CapabilityBits.NET },
    .{ "net", CapabilityBits.NET },
    .{ "os", CapabilityBits.PROCESS },
    .{ "process", CapabilityBits.PROCESS },
    .{ "rand", CapabilityBits.ENTROPY },
    .{ "random", CapabilityBits.ENTROPY },
    .{ "sys", CapabilityBits.LOCKFILE_CAP_BITS },
    .{ "time", CapabilityBits.CLOCK },
    .{ "tls", CapabilityBits.NET },
});

// -------------------------------------- INTERNALS --------------------------------------

// -------------- Scoped Hash Key & Lexeme Helpers --------------

/// Packs `(caller_pkg_id, alias_sym_id)` into a collision-free 64-bit lookup key.
pub inline fn packPackageDepKey(caller_pkg_id: PackageId, alias_sym_id: SymbolId) u64 {
    return (@as(u64, caller_pkg_id.asInt()) << 32) | @as(u64, alias_sym_id.asInt());
}

/// Computes target-ABI `c_char`, `c_long`, and `c_ulong` `TypeId`s from `cfg_env` (`DR-10` §2.1).
fn computeTargetCFfiTypes(cfg_env: CfgEnv) struct {
    c_char_ty: TypeId,
    c_long_ty: TypeId,
    c_ulong_ty: TypeId,
} {
    const c_char_ty: TypeId = if (cfg_env.arch == .aarch64 and
        cfg_env.os != .macos and cfg_env.os != .windows)
        .u8_ty
    else
        .i8_ty;
    const c_long_ty: TypeId = if (cfg_env.os == .windows or cfg_env.ptr_width == 32)
        .i32_ty
    else
        .i64_ty;
    const c_ulong_ty: TypeId = if (cfg_env.os == .windows or cfg_env.ptr_width == 32)
        .u32_ty
    else
        .u64_ty;
    return .{
        .c_char_ty = c_char_ty,
        .c_long_ty = c_long_ty,
        .c_ulong_ty = c_ulong_ty,
    };
}

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

/// Returns the primary string description lexeme for a `.test_decl` or `.bench_decl` node.
pub fn extractTestOrBenchDescriptionSlice(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst: CstNodeIndex,
    main_token: TokenIndex,
) []const u8 {
    if (!main_token.isNone() and main_token.asInt() < token_buffer.countTokens() and
        token_buffer.getToken(main_token).kind == .string_lit)
    {
        return extractTokenSlice(source, token_buffer, main_token);
    }
    if (!item_cst.isNone() and item_cst.asInt() < cst_arena.countNodes()) {
        const start_idx: usize = item_cst.asInt();
        const root_rec = cst_arena.getNode(item_cst);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, root_rec.subtree_size), 1),
            cst_arena.countNodes(),
        );
        var cursor: usize = start_idx + 1;
        while (cursor < end_idx) : (cursor += 1) {
            const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
            if (node.kind == .attribute and node.subtree_size > 1) {
                cursor += @as(usize, node.subtree_size) - 1;
                continue;
            }
            if (node.kind == .block or node.kind == .param_list) break;
            const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
            if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
            if (node.token.asInt() >= token_buffer.countTokens()) continue;
            const tok_kind = token_buffer.getToken(node.token).kind;
            if (tok_kind == .lbrace or tok_kind == .lparen or tok_kind == .arrow) break;
            if (tok_kind == .string_lit) return extractTokenSlice(source, token_buffer, node.token);
        }
    }
    return "";
}

/// Appends function-like AST/CST handles from `item_slice` in exact `collectItemSliceInScope` DFS order.
fn collectFnDeclHandlesInSlice(
    allocator: std.mem.Allocator,
    item_slice: []const u32,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    extra_ends: []const u32,
    is_including_tests: bool,
    out_handles: *std.ArrayListUnmanaged(FnDeclSyntaxHandle),
    depth: u32,
) std.mem.Allocator.Error!void {
    if (depth >= MAX_SCOPE_DEPTH) return;
    for (item_slice) |raw_node_idx| {
        const item_node_idx = NodeIndex.fromInt(raw_node_idx);
        if (item_node_idx.asInt() >= ast_arena.countNodes()) continue;
        const ast_node = ast_arena.getNode(item_node_idx);
        if (ast_node.tag == .item_hole) continue;
        const item_cst = ast_arena.getCstOrigin(item_node_idx);
        switch (ast_node.tag) {
            .fn_decl => {
                const name_tok = findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                if (extractTokenSlice(source, token_buffer, name_tok).len == 0) continue;
                try out_handles.append(allocator, .{ .ast_node = item_node_idx, .cst_node = item_cst });
            },
            .subscript_decl => {
                try out_handles.append(allocator, .{ .ast_node = item_node_idx, .cst_node = item_cst });
            },
            .test_decl, .bench_decl => {
                if (!is_including_tests) continue;
                if (extractTestOrBenchDescriptionSlice(source, token_buffer, cst_arena, item_cst, ast_node.main_token).len == 0) {
                    continue;
                }
                try out_handles.append(allocator, .{ .ast_node = item_node_idx, .cst_node = item_cst });
            },
            .mod_decl => {
                const name_tok = if (ast_node.lhs.tag == .token)
                    TokenIndex.fromInt(ast_node.lhs.payload)
                else
                    findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                if (extractTokenSlice(source, token_buffer, name_tok).len == 0) continue;
                if (ast_node.rhs.tag == .extra) {
                    try collectFnDeclHandlesInSlice(
                        allocator,
                        computeRhsExtraSliceWithEnds(ast_arena, item_node_idx, extra_ends),
                        source,
                        token_buffer,
                        cst_arena,
                        ast_arena,
                        extra_ends,
                        is_including_tests,
                        out_handles,
                        depth + 1,
                    );
                }
            },
            .trait_decl => {
                const name_tok = findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                if (extractTokenSlice(source, token_buffer, name_tok).len == 0) continue;
                if (ast_node.lhs.tag == .extra and ast_node.rhs.tag == .extra and ast_node.rhs.payload > 0) {
                    try collectFnDeclHandlesInSlice(
                        allocator,
                        ast_arena.getExtraSlice(ExtraIndex.fromInt(ast_node.lhs.payload), ast_node.rhs.payload),
                        source,
                        token_buffer,
                        cst_arena,
                        ast_arena,
                        extra_ends,
                        is_including_tests,
                        out_handles,
                        depth + 1,
                    );
                }
            },
            .impl_decl => {
                try collectFnDeclHandlesInSlice(
                    allocator,
                    computeRhsExtraSliceWithEnds(ast_arena, item_node_idx, extra_ends),
                    source,
                    token_buffer,
                    cst_arena,
                    ast_arena,
                    extra_ends,
                    is_including_tests,
                    out_handles,
                    depth + 1,
                );
            },
            .extern_block_decl => {
                try collectFnDeclHandlesInSlice(
                    allocator,
                    ast_arena.getExternBlockItems(item_node_idx),
                    source,
                    token_buffer,
                    cst_arena,
                    ast_arena,
                    extra_ends,
                    is_including_tests,
                    out_handles,
                    depth + 1,
                );
            },
            else => {},
        }
    }
}

/// Returns `true` if `cst_start .. cst_end` contains an `@builder` attribute node (`SE-22`).
fn hasBuilderAttributeInCstRange(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    cst_start: usize,
    cst_end: usize,
) bool {
    var cursor = cst_start;
    while (cursor < cst_end) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (node.kind == .attribute) {
            const attr_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), cst_end);
            var attr_cur = cursor + 1;
            while (attr_cur < attr_end) : (attr_cur += 1) {
                const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(attr_cur)));
                if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                    leaf.token.asInt() < token_buffer.countTokens())
                {
                    const tok_kind = token_buffer.getToken(leaf.token).kind;
                    if (isIdentifierToken(tok_kind)) {
                        if (std.mem.eql(u8, extractTokenSlice(source, token_buffer, leaf.token), "builder")) {
                            return true;
                        }
                        break;
                    }
                }
            }
            if (node.subtree_size > 1) cursor += @as(usize, node.subtree_size) - 1;
        }
    }
    return false;
}

/// Extracts a single string literal argument inside `[arg_start .. attr_end)` into `dest_buf` and `dest_len`.
fn extractSingleStringAttrIntoBuf(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    arg_start: usize,
    attr_end: usize,
    dest_buf: *[256]u8,
    dest_len: *u16,
) void {
    var arg_cur = arg_start;
    while (arg_cur < attr_end) : (arg_cur += 1) {
        const arg_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(arg_cur)));
        if (arg_leaf.subtree_size <= 1 and !arg_leaf.token.isNone() and
            arg_leaf.token.asInt() < token_buffer.countTokens())
        {
            const arg_kind = token_buffer.getToken(arg_leaf.token).kind;
            if (arg_kind == .string_lit or arg_kind == .byte_string_lit) {
                var unesc_buf: [256]u8 = undefined;
                const unquoted = unquoteAttrStringLexeme(
                    extractTokenSlice(source, token_buffer, arg_leaf.token),
                    &unesc_buf,
                );
                const copy_len = @min(unquoted.len, dest_buf.len);
                @memcpy(dest_buf[0..copy_len], unquoted[0..copy_len]);
                dest_len.* = @intCast(copy_len);
                break;
            }
        }
    }
}

/// Extracts `@wasm_import("mod", "name")` string literal arguments inside `[arg_start .. attr_end)`.
fn extractWasmImportAttr(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    arg_start: usize,
    attr_end: usize,
    meta: *ItemHeaderMetadata,
) void {
    var seen_strings: u8 = 0;
    var arg_cur = arg_start;
    while (arg_cur < attr_end and seen_strings < 2) : (arg_cur += 1) {
        const arg_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(arg_cur)));
        if (arg_leaf.subtree_size <= 1 and !arg_leaf.token.isNone() and
            arg_leaf.token.asInt() < token_buffer.countTokens())
        {
            const arg_kind = token_buffer.getToken(arg_leaf.token).kind;
            if (arg_kind == .string_lit or arg_kind == .byte_string_lit) {
                var unesc_buf: [256]u8 = undefined;
                const unquoted = unquoteAttrStringLexeme(
                    extractTokenSlice(source, token_buffer, arg_leaf.token),
                    &unesc_buf,
                );
                if (seen_strings == 0) {
                    const copy_len = @min(unquoted.len, meta.wasm_import_mod_buf.len);
                    @memcpy(meta.wasm_import_mod_buf[0..copy_len], unquoted[0..copy_len]);
                    meta.wasm_import_mod_len = @intCast(copy_len);
                } else {
                    const copy_len = @min(unquoted.len, meta.wasm_import_name_buf.len);
                    @memcpy(meta.wasm_import_name_buf[0..copy_len], unquoted[0..copy_len]);
                    meta.wasm_import_name_len = @intCast(copy_len);
                }
                seen_strings += 1;
            }
        }
    }
}

/// Evaluates `@cfg` predicates on symbols in `scope_id` against `sym_table.cfg_env` to keep `scoped_map` synchronized
/// for cross-file `use` resolution before `TypeChecker` runs (`core/ffi.cx` `@cfg` `c_char` twins).
fn pruneScopeMapWithCfgEnvQuiet(
    sym_table: *SymbolTable,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    scope_id: ScopeId,
    depth: u32,
) !void {
    if (scope_id.isNone() or depth >= MAX_SCOPE_DEPTH) return;
    const effective_cfg = sym_table.effectiveCfgEnvForFile(file_id);
    const members_copy = try sym_table.allocator.dupe(
        SymbolIndex,
        sym_table.getScopeMembers(scope_id),
    );
    defer sym_table.allocator.free(members_copy);

    for (members_copy) |sym_idx| {
        const sym = sym_table.getSymbol(sym_idx).*;
        if (sym.flags.is_builtin or sym.flags.is_imported) continue;
        if (sym.kind == .overload_group_sym) continue;

        if (sym.has_cfg_attr) {
            const is_own_enabled = if (!sym.cst_node.isNone())
                (evaluateCstNodeCfgWithEnv(
                    &effective_cfg,
                    file_id,
                    source,
                    token_buffer,
                    cst_arena,
                    sym.cst_node,
                    null,
                ) catch true)
            else
                true;
            const is_enc_enabled = if (!sym.enclosing_cfg_cst.isNone())
                (evaluateCstNodeCfgWithEnv(
                    &effective_cfg,
                    file_id,
                    source,
                    token_buffer,
                    cst_arena,
                    sym.enclosing_cfg_cst,
                    null,
                ) catch true)
            else
                true;
            const key = packScopedSymbolKey(scope_id, sym.name, sym.namespace);
            if (!(is_own_enabled and is_enc_enabled)) {
                if (sym_table.scoped_map.get(key)) |mapped_idx| {
                    if (mapped_idx == sym_idx) {
                        _ = sym_table.scoped_map.remove(key);
                    }
                }
                continue;
            }
            if (sym_table.scoped_map.get(key) == null) {
                try sym_table.scoped_map.put(sym_table.allocator, key, sym_idx);
            }
        }

        if (!sym.target_scope.isNone() and
            sym_table.scope_arena.getScope(sym.target_scope).file_id == file_id)
        {
            try pruneScopeMapWithCfgEnvQuiet(
                sym_table,
                file_id,
                source,
                token_buffer,
                cst_arena,
                sym.target_scope,
                depth + 1,
            );
        }
    }
}

/// Extracts any explicit `extern "ABI"` string and `unsafe` prefix before `main_token` in `item_cst`.
fn extractItemExternAbiAndUnsafe(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst: CstNodeIndex,
    main_token: TokenIndex,
    abi_out_buf: *[256]u8,
) struct { abi_slice: []const u8, is_unsafe: bool } {
    var abi_slice: []const u8 = "";
    var is_unsafe = false;
    if (item_cst.isNone() or item_cst.asInt() >= cst_arena.countNodes()) {
        return .{ .abi_slice = abi_slice, .is_unsafe = is_unsafe };
    }
    const start_idx: usize = item_cst.asInt();
    const root_rec = cst_arena.getNode(item_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );
    var has_seen_extern = false;
    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (node.kind == .attribute or node.kind == .visibility_modifier) {
            if (node.subtree_size > 1) cursor += @as(usize, node.subtree_size) - 1;
            continue;
        }
        if (!node.token.isNone() and !main_token.isNone() and node.token.asInt() >= main_token.asInt()) {
            break;
        }
        if (node.subtree_size <= 1 and !node.flags.is_bracketed and !node.token.isNone() and
            node.token.asInt() < token_buffer.countTokens())
        {
            const tok_kind = token_buffer.getToken(node.token).kind;
            if (tok_kind == .kw_unsafe) {
                is_unsafe = true;
                has_seen_extern = false;
            } else if (tok_kind == .kw_extern) {
                has_seen_extern = true;
            } else if (has_seen_extern and tok_kind == .string_lit) {
                abi_slice = unquoteAttrStringLexeme(
                    extractTokenSlice(source, token_buffer, node.token),
                    abi_out_buf,
                );
                has_seen_extern = false;
            } else {
                has_seen_extern = false;
            }
        }
    }
    return .{ .abi_slice = abi_slice, .is_unsafe = is_unsafe };
}

/// Populates or updates initial linkage/trust `FfiFnContract` metadata on `sym_idx` when FFI attributes are present.
fn recordHeaderFfiContractIfPresent(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    sym_idx: SymbolIndex,
    is_extern: bool,
    is_unsafe_extern: bool,
    abi_slice: []const u8,
    header_meta: *const ItemHeaderMetadata,
) !void {
    const link_lib_slice = header_meta.asLinkLibSlice();
    const wasm_mod_slice = header_meta.asWasmImportModSlice();
    const wasm_name_slice = header_meta.asWasmImportNameSlice();
    const wasm_exp_slice = header_meta.asWasmExportSlice();
    const has_any = header_meta.is_trusted or
        header_meta.is_thread_local or
        is_unsafe_extern or
        abi_slice.len > 0 or
        link_lib_slice.len > 0 or
        wasm_mod_slice.len > 0 or
        wasm_name_slice.len > 0 or
        wasm_exp_slice.len > 0;
    if (!has_any and !is_extern) return;
    if (!has_any) return;

    const abi_id: SymbolId = if (abi_slice.len > 0) try interner.intern(abi_slice) else .empty;
    const link_lib_id: SymbolId = if (link_lib_slice.len > 0) try interner.intern(link_lib_slice) else .empty;
    const wasm_mod_id: SymbolId = if (wasm_mod_slice.len > 0) try interner.intern(wasm_mod_slice) else .empty;
    const wasm_name_id: SymbolId = if (wasm_name_slice.len > 0) try interner.intern(wasm_name_slice) else .empty;
    const wasm_exp_id: SymbolId = if (wasm_exp_slice.len > 0) try interner.intern(wasm_exp_slice) else .empty;

    try sym_table.setFfiContract(sym_idx, .{
        .is_trusted = header_meta.is_trusted,
        .is_thread_local = header_meta.is_thread_local,
        .is_unsafe_extern = is_unsafe_extern,
        .abi_name = abi_id,
        .wasm_import_module = wasm_mod_id,
        .wasm_import_name = wasm_name_id,
        .wasm_export_name = wasm_exp_id,
        .link_lib_name = link_lib_id,
    }, &.{});
}

/// Collects AST items into `enclosing_scope`, advancing `top_ordinal_ptr` across flattened top-level `extern` blocks.
fn collectItemSliceInScopeWithOrdinal(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    enclosing_scope: ScopeId,
    top_ordinal_ptr: ?*u12,
    enclosing_owner_def: DefId,
    item_slice: []const u32,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    extra_ends: []const u32,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!void {
    const ForwardImplRebind = struct {
        /// Temporary `.impl_scope` created before the target nominal type was seen.
        old_scope: ScopeId,
        /// Assigned `DefId` of the `.impl_decl`.
        def_id: DefId,
        /// AST node index of the `.impl_decl`.
        item_node_idx: NodeIndex,
        /// CST node index of the `.impl_item`.
        item_cst: CstNodeIndex,
        /// Inclusive symbol table start index of this `impl`'s members.
        sym_start: usize,
        /// Exclusive symbol table end index of this `impl`'s members.
        sym_end: usize,
    };

    const file_pkg_id = sym_table.getFilePackageId(file_id);
    const is_external_pkg = file_pkg_id.asInt() >= 2;
    const is_file_including_tests = sym_table.is_including_tests and (file_pkg_id == .root);
    var forward_impls: std.ArrayListUnmanaged(ForwardImplRebind) = .empty;
    defer forward_impls.deinit(sym_table.allocator);
    for (item_slice) |raw_node_idx| {
        const item_node_idx = NodeIndex.fromInt(raw_node_idx);
        if (item_node_idx.asInt() >= ast_arena.countNodes()) continue;
        const ast_node = ast_arena.getNode(item_node_idx);
        if (ast_node.tag == .item_hole) continue;
        if (!is_file_including_tests and (ast_node.tag == .test_decl or ast_node.tag == .bench_decl)) {
            continue;
        }

        const def_id: DefId = if (ast_node.tag != .extern_block_decl) blk: {
            if (top_ordinal_ptr) |ord_ptr| {
                const current_def = DefId.init(file_id, ord_ptr.*);
                if (ord_ptr.* < std.math.maxInt(u12)) ord_ptr.* += 1;
                break :blk current_def;
            }
            break :blk .NONE;
        } else .NONE;

        const item_cst = ast_arena.getCstOrigin(item_node_idx);
        var header_meta = try extractItemHeaderMetadataWithInterner(
            source,
            file_id,
            token_buffer,
            cst_arena,
            item_cst,
            ast_node.main_token,
            interner,
            diagnostic_sink,
        );
        if (is_external_pkg) {
            header_meta.contract_flags.is_std_cap_boundary = false;
            header_meta.cap_emits_mask = 0;
            header_meta.cap_clears_mask = 0;
            header_meta.is_trusted = false;
            header_meta.extra_flags.is_trusted_ffi = false;
            header_meta.contract_flags.has_link_section = false;
            header_meta.link_section_len = 0;
        }
        const visibility = header_meta.visibility;
        var flags = header_meta.flags;
        flags.is_pub = (visibility == .public);
        var extra_flags = header_meta.extra_flags;
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

                const is_flat_mod_allowed = !sym_table.is_flat_named_module_scopes_suppressed and
                    !sym_table.configured_pkg_deps.contains(file_pkg_id);
                const bound_ext_scope: ScopeId = if (ast_node.rhs.tag != .extra) blk: {
                    const direct_ext = sym_table.getExternalModuleScope(file_id, name_sym);
                    if (!direct_ext.isNone()) break :blk direct_ext;
                    if (is_flat_mod_allowed) {
                        break :blk sym_table.named_module_scopes.get(name_sym.asInt()) orelse .none;
                    }
                    break :blk .none;
                } else .none;
                const mod_scope = if (!bound_ext_scope.isNone()) blk: {
                    const parent_mod = sym_table.scope_arena.getScope(enclosing_scope).enclosing_module;
                    if (!parent_mod.isNone()) {
                        sym_table.scope_arena.setParentModule(bound_ext_scope, parent_mod);
                    }
                    break :blk bound_ext_scope;
                } else blk: {
                    const fresh_scope = try sym_table.scope_arena.allocScope(
                        .module_scope,
                        enclosing_scope,
                        def_id,
                        file_id,
                        .{},
                    );
                    if (!sym_table.is_flat_named_module_scopes_suppressed) {
                        try sym_table.named_module_scopes.put(sym_table.allocator, name_sym.asInt(), fresh_scope);
                    }
                    break :blk fresh_scope;
                };

                _ = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = .module_sym,
                    .namespace = .value_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .extra_flags = extra_flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = name_span,
                    .target_scope = mod_scope,
                    .has_cfg_attr = header_meta.has_cfg_attr,
                }, diagnostic_sink);

                // Collect inline `mod foo { … }` sub-items:
                if (ast_node.rhs.tag == .extra) {
                    const inner_items = computeRhsExtraSliceWithEnds(ast_arena, item_node_idx, extra_ends);
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
                        extra_ends,
                        diagnostic_sink,
                    );
                }
            },
            .use_decl => {
                try sym_table.pending_imports.append(sym_table.allocator, .{
                    .module_scope = enclosing_scope,
                    .file_id = file_id,
                    .def_id = def_id,
                    .visibility = visibility,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                });
            },
            .struct_decl, .union_decl, .bit_field_decl => {
                const is_bit_field = ast_node.tag == .bit_field_decl or
                    (!ast_node.main_token.isNone() and
                        ast_node.main_token.asInt() < token_buffer.countTokens() and
                        token_buffer.getToken(ast_node.main_token).kind == .kw_bit_field);
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

                const defined_sym_idx = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = sym_kind,
                    .namespace = .type_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .extra_flags = extra_flags,
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
                    .has_cfg_attr = header_meta.has_cfg_attr,
                }, diagnostic_sink);

                const gen_specs = try extractGenericParamSpecsFromItemCst(
                    sym_table.allocator,
                    interner,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                );
                defer sym_table.allocator.free(gen_specs);
                if (gen_specs.len > 0) {
                    try sym_table.setGenericParamSpecs(defined_sym_idx, gen_specs);
                }

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

                if (extra_flags.has_repr_int) {
                    if (diagnostic_sink) |sink| {
                        try emitRetiredEnumReprIntDiagnostic(
                            sink,
                            file_id,
                            source,
                            token_buffer,
                            name_str,
                            header_meta.repr_int_token,
                        );
                    }
                }

                const variant_scope = try sym_table.scope_arena.allocScope(
                    .nominal_type_scope,
                    enclosing_scope,
                    def_id,
                    file_id,
                    .{},
                );
                const defined_sym_idx = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = .enum_sym,
                    .namespace = .type_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .extra_flags = extra_flags,
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
                    .has_cfg_attr = header_meta.has_cfg_attr,
                }, diagnostic_sink);

                const gen_specs = try extractGenericParamSpecsFromItemCst(
                    sym_table.allocator,
                    interner,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                );
                defer sym_table.allocator.free(gen_specs);
                if (gen_specs.len > 0) {
                    try sym_table.setGenericParamSpecs(defined_sym_idx, gen_specs);
                }

                try collectEnumVariants(
                    sym_table,
                    interner,
                    file_id,
                    variant_scope,
                    visibility,
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
                const defined_sym_idx = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = .trait_sym,
                    .namespace = .type_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .extra_flags = extra_flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = name_span,
                    .target_scope = trait_scope,
                    .contract_flags = header_meta.contract_flags,
                    .has_cfg_attr = header_meta.has_cfg_attr,
                }, diagnostic_sink);

                const gen_specs = try extractGenericParamSpecsFromItemCst(
                    sym_table.allocator,
                    interner,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                );
                defer sym_table.allocator.free(gen_specs);
                if (gen_specs.len > 0) {
                    try sym_table.setGenericParamSpecs(defined_sym_idx, gen_specs);
                }

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
                        extra_ends,
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

                const gen_specs = try extractGenericParamSpecsFromItemCst(
                    sym_table.allocator,
                    interner,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                );
                defer sym_table.allocator.free(gen_specs);

                // Classify whether this `type` item is a `bit_field`, Type Group (`|`/`+`), `is` refinement, or `distinct`:
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
                    if (target_ast.tag == .union_bound_type or target_ast.tag == .intersect_bound_type) {
                        alias_kind = .type_group_sym;
                        flags.is_type_group = true;
                    } else if (target_ast.tag == .mode_type) {
                        const mode_lexeme = extractTokenSlice(source, token_buffer, target_ast.main_token);
                        if (std.mem.eql(u8, mode_lexeme, "distinct")) {
                            alias_kind = .distinct_type_sym;
                            flags.is_distinct = true;
                        }
                    }
                }
                if (bf_member_scope.isNone() and gen_specs.len > 0) {
                    bf_member_scope = try sym_table.scope_arena.allocScope(
                        .nominal_type_scope,
                        enclosing_scope,
                        def_id,
                        file_id,
                        .{},
                    );
                }

                const defined_sym_idx = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = alias_kind,
                    .namespace = .type_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .extra_flags = extra_flags,
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
                    .has_cfg_attr = header_meta.has_cfg_attr,
                }, diagnostic_sink);

                if (gen_specs.len > 0) {
                    try sym_table.setGenericParamSpecs(defined_sym_idx, gen_specs);
                }

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
                    .extra_flags = extra_flags,
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
                    .has_cfg_attr = header_meta.has_cfg_attr,
                }, diagnostic_sink);
            },
            .fn_decl => {
                const name_tok = findItemNameToken(token_buffer, cst_arena, item_cst, ast_node.main_token);
                const name_str = extractTokenSlice(source, token_buffer, name_tok);
                if (name_str.len == 0) continue;
                const name_sym = try interner.intern(name_str);
                const name_span = token_buffer.getTokenSpan(file_id, name_tok);
                flags.is_prototype_only = (ast_node.rhs.tag == .none);

                const effective_owner_def = if (!def_id.isNone()) def_id else enclosing_owner_def;
                const extracted_params = try extractFnParamSpecsFromItemCst(
                    sym_table.allocator,
                    interner,
                    file_id,
                    effective_owner_def,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                );
                defer sym_table.allocator.free(extracted_params.specs);
                extra_flags.is_variadic = extracted_params.is_variadic;

                const defined_sym_idx = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = .fn_sym,
                    .namespace = .value_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .extra_flags = extra_flags,
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
                    .has_cfg_attr = header_meta.has_cfg_attr,
                }, diagnostic_sink);

                if (extracted_params.specs.len > 0) {
                    try sym_table.setFnParamSpecs(defined_sym_idx, extracted_params.specs);
                }
                const gen_specs = try extractGenericParamSpecsFromItemCst(
                    sym_table.allocator,
                    interner,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                );
                defer sym_table.allocator.free(gen_specs);
                if (gen_specs.len > 0) {
                    try sym_table.setGenericParamSpecs(defined_sym_idx, gen_specs);
                }
                var fn_abi_buf: [256]u8 = undefined;
                const fn_ext_info = extractItemExternAbiAndUnsafe(
                    source,
                    token_buffer,
                    cst_arena,
                    item_cst,
                    ast_node.main_token,
                    &fn_abi_buf,
                );
                try recordHeaderFfiContractIfPresent(
                    sym_table,
                    interner,
                    defined_sym_idx,
                    flags.is_extern,
                    fn_ext_info.is_unsafe,
                    fn_ext_info.abi_slice,
                    &header_meta,
                );
            },
            .extern_static_decl => {
                const static_extra = ast_arena.getExternStaticExtra(item_node_idx);
                const name_tok = ast_node.main_token;
                const name_str = extractTokenSlice(source, token_buffer, name_tok);
                if (name_str.len == 0) continue;
                const name_sym = try interner.intern(name_str);
                const name_span = token_buffer.getTokenSpan(file_id, name_tok);

                const static_vis: Visibility = if (visibility != .private)
                    visibility
                else
                    @fromBackingInt(@backingInt(static_extra.flags.visibility));
                flags.is_pub = (static_vis == .public);
                flags.is_extern = static_extra.flags.has_extern;
                flags.is_mut = static_extra.flags.is_mut;

                const defined_sym_idx = try sym_table.defineSymbol(.{
                    .name = name_sym,
                    .name_text = interner.get(name_sym),
                    .kind = .extern_static_sym,
                    .namespace = .value_ns,
                    .visibility = static_vis,
                    .flags = flags,
                    .extra_flags = extra_flags,
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
                    .has_cfg_attr = header_meta.has_cfg_attr,
                }, diagnostic_sink);

                var static_abi_buf: [256]u8 = undefined;
                const static_abi_slice: []const u8 = if (!static_extra.abi_tok.isNone())
                    unquoteAttrStringLexeme(
                        extractTokenSlice(source, token_buffer, static_extra.abi_tok),
                        &static_abi_buf,
                    )
                else
                    "";
                try recordHeaderFfiContractIfPresent(
                    sym_table,
                    interner,
                    defined_sym_idx,
                    flags.is_extern,
                    static_extra.flags.is_unsafe,
                    static_abi_slice,
                    &header_meta,
                );
            },
            .extern_block_decl => {
                const block_hdr = ast_arena.getExternBlockHeader(item_node_idx);
                const member_items = ast_arena.getExternBlockItems(item_node_idx);
                const outer_vis: Visibility = if (visibility != .private)
                    visibility
                else
                    @fromBackingInt(@backingInt(block_hdr.flags.visibility));

                var block_abi_buf: [256]u8 = undefined;
                const block_abi_slice: []const u8 = if (!block_hdr.abi_tok.isNone())
                    unquoteAttrStringLexeme(
                        extractTokenSlice(source, token_buffer, block_hdr.abi_tok),
                        &block_abi_buf,
                    )
                else
                    "C";
                const block_abi_id: SymbolId = if (block_abi_slice.len > 0)
                    try interner.intern(block_abi_slice)
                else
                    .empty;
                const block_link_lib = header_meta.asLinkLibSlice();
                const block_link_lib_id: SymbolId = if (block_link_lib.len > 0)
                    try interner.intern(block_link_lib)
                else
                    .empty;
                const block_wasm_mod = header_meta.asWasmImportModSlice();
                const block_wasm_mod_id: SymbolId = if (block_wasm_mod.len > 0)
                    try interner.intern(block_wasm_mod)
                else
                    .empty;
                const block_wasm_name = header_meta.asWasmImportNameSlice();
                const block_wasm_name_id: SymbolId = if (block_wasm_name.len > 0)
                    try interner.intern(block_wasm_name)
                else
                    .empty;

                const effective_owner_def = if (!def_id.isNone()) def_id else enclosing_owner_def;
                const pre_sym_len = sym_table.symbols.items.len;
                try collectItemSliceInScopeWithOrdinal(
                    sym_table,
                    interner,
                    file_id,
                    enclosing_scope,
                    top_ordinal_ptr,
                    effective_owner_def,
                    member_items,
                    source,
                    token_buffer,
                    cst_arena,
                    ast_arena,
                    extra_ends,
                    diagnostic_sink,
                );

                var sym_i = pre_sym_len;
                while (sym_i < sym_table.symbols.items.len) : (sym_i += 1) {
                    const added_idx = SymbolIndex.fromInt(@intCast(sym_i));
                    const added_sym = &sym_table.symbols.items[sym_i];
                    if (added_sym.scope_id != enclosing_scope) continue;
                    if (added_sym.kind == .overload_group_sym) continue;

                    if (outer_vis != .private and added_sym.visibility == .private) {
                        added_sym.visibility = outer_vis;
                        added_sym.flags.is_pub = (outer_vis == .public);
                    }
                    if (header_meta.has_cfg_attr) {
                        added_sym.has_cfg_attr = true;
                        if (added_sym.enclosing_cfg_cst.isNone()) {
                            added_sym.enclosing_cfg_cst = item_cst;
                        }
                    }
                    if (added_sym.kind == .fn_sym or added_sym.kind == .extern_static_sym) {
                        added_sym.flags.is_extern = true;
                        const existing_contract = if (sym_table.getFfiContract(added_idx)) |ptr|
                            ptr.*
                        else
                            FfiFnContract{};
                        const has_inherited = header_meta.is_trusted or
                            header_meta.is_thread_local or
                            block_hdr.flags.is_unsafe or
                            block_abi_id != .empty or
                            block_link_lib_id != .empty or
                            block_wasm_mod_id != .empty or
                            block_wasm_name_id != .empty;
                        if (header_meta.is_trusted) {
                            added_sym.extra_flags.is_trusted_ffi = true;
                        }
                        if (header_meta.is_thread_local) {
                            added_sym.extra_flags.is_thread_local = true;
                        }
                        if (has_inherited or sym_table.getFfiContract(added_idx) != null) {
                            var merged = existing_contract;
                            if (header_meta.is_trusted) merged.is_trusted = true;
                            if (header_meta.is_thread_local) merged.is_thread_local = true;
                            if (block_hdr.flags.is_unsafe) merged.is_unsafe_extern = true;
                            if (merged.abi_name == .empty) merged.abi_name = block_abi_id;
                            if (merged.link_lib_name == .empty) merged.link_lib_name = block_link_lib_id;
                            if (merged.wasm_import_module == .empty) merged.wasm_import_module = block_wasm_mod_id;
                            if (merged.wasm_import_name == .empty) merged.wasm_import_name = block_wasm_name_id;
                            try sym_table.setFfiContract(added_idx, merged, existing_contract.param_contracts);
                        }
                    }
                }
            },
            .subscript_decl => {
                const sub_sym = try interner.intern("subscript");
                const sub_span = token_buffer.getTokenSpan(file_id, ast_node.main_token);
                flags.is_prototype_only = (ast_node.rhs.tag == .none);
                extra_flags.is_subscript = true;

                const effective_owner_def = if (!def_id.isNone()) def_id else enclosing_owner_def;
                const extracted_params = try extractFnParamSpecsFromItemCst(
                    sym_table.allocator,
                    interner,
                    file_id,
                    effective_owner_def,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                );
                defer sym_table.allocator.free(extracted_params.specs);
                extra_flags.is_variadic = extracted_params.is_variadic;

                const defined_sym_idx = try sym_table.defineSymbol(.{
                    .name = sub_sym,
                    .name_text = interner.get(sub_sym),
                    .kind = .fn_sym,
                    .namespace = .value_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .extra_flags = extra_flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .owner_def_id = enclosing_owner_def,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = sub_span,
                    .contract_flags = header_meta.contract_flags,
                    .max_stack_bytes = header_meta.max_stack_bytes,
                    .cap_emits_mask = header_meta.cap_emits_mask,
                    .cap_clears_mask = header_meta.cap_clears_mask,
                    .link_section_name = interned_link_sec,
                    .link_name_text = interned_link_name,
                    .explicit_align_log2_plus1 = header_meta.explicit_align_log2_plus1,
                    .has_cfg_attr = header_meta.has_cfg_attr,
                }, diagnostic_sink);

                if (extracted_params.specs.len > 0) {
                    try sym_table.setFnParamSpecs(defined_sym_idx, extracted_params.specs);
                }
                const gen_specs = try extractGenericParamSpecsFromItemCst(
                    sym_table.allocator,
                    interner,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                );
                defer sym_table.allocator.free(gen_specs);
                if (gen_specs.len > 0) {
                    try sym_table.setGenericParamSpecs(defined_sym_idx, gen_specs);
                }
            },
            .test_decl, .bench_decl => {
                const desc_slice = extractTestOrBenchDescriptionSlice(
                    source,
                    token_buffer,
                    cst_arena,
                    item_cst,
                    ast_node.main_token,
                );
                if (desc_slice.len == 0) continue;
                const desc_sym = try interner.intern(desc_slice);
                const desc_span = token_buffer.getTokenSpan(file_id, ast_node.main_token);
                flags.is_used = true;
                extra_flags.is_test = (ast_node.tag == .test_decl);
                extra_flags.is_bench = (ast_node.tag == .bench_decl);

                const effective_owner_def = if (!def_id.isNone()) def_id else enclosing_owner_def;
                const extracted_params = try extractFnParamSpecsFromItemCst(
                    sym_table.allocator,
                    interner,
                    file_id,
                    effective_owner_def,
                    item_cst,
                    source,
                    token_buffer,
                    cst_arena,
                );
                defer sym_table.allocator.free(extracted_params.specs);

                const defined_sym_idx = try sym_table.defineSymbol(.{
                    .name = desc_sym,
                    .name_text = interner.get(desc_sym),
                    .kind = .fn_sym,
                    .namespace = .value_ns,
                    .visibility = visibility,
                    .flags = flags,
                    .extra_flags = extra_flags,
                    .scope_id = enclosing_scope,
                    .def_id = def_id,
                    .owner_def_id = enclosing_owner_def,
                    .ast_node = item_node_idx,
                    .cst_node = item_cst,
                    .decl_span = desc_span,
                    .contract_flags = header_meta.contract_flags,
                    .max_stack_bytes = header_meta.max_stack_bytes,
                    .has_cfg_attr = header_meta.has_cfg_attr,
                }, diagnostic_sink);

                if (extracted_params.specs.len > 0) {
                    try sym_table.setFnParamSpecs(defined_sym_idx, extracted_params.specs);
                }
            },
            .impl_decl => {
                // Collect methods inside `impl [Trait for] TargetType { … }` in exact AST source order:
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
                const member_items = computeRhsExtraSliceWithEnds(ast_arena, item_node_idx, extra_ends);
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
                    extra_ends,
                    diagnostic_sink,
                );
                const post_sym_len = sym_table.symbols.items.len;
                if (header_meta.has_cfg_attr or !impl_target.trait_sym_idx.isNone()) {
                    var sym_i = pre_sym_len;
                    while (sym_i < post_sym_len) : (sym_i += 1) {
                        const added_sym = &sym_table.symbols.items[sym_i];
                        if (added_sym.scope_id == impl_target.target_scope) {
                            if (header_meta.has_cfg_attr) {
                                added_sym.has_cfg_attr = true;
                                added_sym.enclosing_cfg_cst = item_cst;
                            }
                            if (!impl_target.trait_sym_idx.isNone() and added_sym.kind == .fn_sym) {
                                try sym_table.impl_method_trait.put(
                                    sym_table.allocator,
                                    @intCast(sym_i),
                                    impl_target.trait_sym_idx,
                                );
                            }
                        }
                    }
                }
                const is_unresolved_scope = !impl_target.target_scope.isNone() and
                    impl_target.target_scope.asInt() < sym_table.scope_arena.scopes.len and
                    sym_table.scope_arena.scopes.get(impl_target.target_scope.asInt()).kind == .impl_scope;
                if (is_unresolved_scope or impl_target.trait_sym_idx.isNone()) {
                    try forward_impls.append(sym_table.allocator, .{
                        .old_scope = impl_target.target_scope,
                        .def_id = def_id,
                        .item_node_idx = item_node_idx,
                        .item_cst = item_cst,
                        .sym_start = pre_sym_len,
                        .sym_end = post_sym_len,
                    });
                }
            },
            else => {},
        }
    }

    // Rebind any forward `impl` blocks whose nominal target type or trait was declared later in `enclosing_scope`:
    for (forward_impls.items) |fwd_impl| {
        const impl_ast = ast_arena.getNode(fwd_impl.item_node_idx);
        const rebound = try resolveImplTargetScope(
            sym_table,
            interner,
            file_id,
            enclosing_scope,
            fwd_impl.def_id,
            fwd_impl.item_cst,
            impl_ast,
            source,
            token_buffer,
            cst_arena,
            ast_arena,
        );
        const has_rebound_scope = rebound.target_scope != fwd_impl.old_scope and
            !rebound.target_scope.isNone() and
            rebound.target_scope.asInt() < sym_table.scope_arena.scopes.len and
            sym_table.scope_arena.scopes.get(rebound.target_scope.asInt()).kind == .nominal_type_scope;
        if (!has_rebound_scope and rebound.trait_sym_idx.isNone()) continue;

        var sym_i = fwd_impl.sym_start;
        while (sym_i < fwd_impl.sym_end) : (sym_i += 1) {
            const sym_idx = SymbolIndex.fromInt(@intCast(sym_i));
            const sym_mut = &sym_table.symbols.items[sym_i];
            if (sym_mut.scope_id != fwd_impl.old_scope) continue;
            if (has_rebound_scope) {
                sym_mut.scope_id = rebound.target_scope;
                const mem_gop = try sym_table.scope_members.getOrPut(
                    sym_table.allocator,
                    rebound.target_scope.asInt(),
                );
                if (!mem_gop.found_existing) mem_gop.value_ptr.* = .empty;
                try mem_gop.value_ptr.append(sym_table.allocator, sym_idx);
                const new_key = packScopedSymbolKey(rebound.target_scope, sym_mut.name, sym_mut.namespace);
                if (!sym_table.scoped_map.contains(new_key)) {
                    try sym_table.scoped_map.put(sym_table.allocator, new_key, sym_idx);
                }
            }
            if (!rebound.trait_sym_idx.isNone() and sym_mut.kind == .fn_sym) {
                try sym_table.impl_method_trait.put(
                    sym_table.allocator,
                    @intCast(sym_i),
                    rebound.trait_sym_idx,
                );
            }
        }
    }
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

    /// Allocates a new `ScopeRecord` and returns its `ScopeId`, inheriting flags, `pkg_id`, and module links.
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
        var parent_mod: ScopeId = .none;
        var inherited_pkg: PackageId = .root;
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
            merged_flags.is_inside_subscript = merged_flags.is_inside_subscript or
                parent_rec.flags.is_inside_subscript;
            if (parent_rec.kind != .global_prelude) {
                inherited_pkg = parent_rec.pkg_id;
            }
            if (kind == .module_scope) {
                enclosing_mod = ScopeId.fromInt(@intCast(self.scopes.len));
                if (!parent_rec.enclosing_module.isNone() and parent_rec.kind != .global_prelude) {
                    parent_mod = parent_rec.enclosing_module;
                }
            } else {
                enclosing_mod = parent_rec.enclosing_module;
                parent_mod = parent_rec.parent_module;
            }
        } else if (kind == .module_scope) {
            enclosing_mod = ScopeId.fromInt(@intCast(self.scopes.len));
        }

        const new_id = ScopeId.fromInt(@intCast(self.scopes.len));
        try self.scopes.append(self.allocator, .{
            .kind = kind,
            .flags = merged_flags,
            .parent = parent,
            .enclosing_module = enclosing_mod,
            .parent_module = parent_mod,
            .pkg_id = inherited_pkg,
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

    /// Updates `parent_module` on `mod_scope` when binding an external `mod child;` file scope.
    pub fn setParentModule(self: *ScopeArena, mod_scope: ScopeId, parent_mod_scope: ScopeId) void {
        if (mod_scope.isNone() or mod_scope.asInt() >= self.scopes.len) return;
        if (mod_scope == parent_mod_scope) return;
        self.scopes.items(.parent_module)[mod_scope.asInt()] = parent_mod_scope;
    }

    /// Updates `pkg_id` on `scope_id` and any scopes already allocated in the same `file_id`.
    pub fn setScopePackageId(self: *ScopeArena, scope_id: ScopeId, pkg_id: PackageId) void {
        if (scope_id.isNone() or scope_id.asInt() >= self.scopes.len) return;
        const target_file = self.scopes.items(.file_id)[scope_id.asInt()];
        self.scopes.items(.pkg_id)[scope_id.asInt()] = pkg_id;
        if (!target_file.isNone()) {
            const file_col = self.scopes.items(.file_id);
            const pkg_col = self.scopes.items(.pkg_id);
            var i: usize = 1;
            while (i < self.scopes.len) : (i += 1) {
                if (file_col[i] == target_file) pkg_col[i] = pkg_id;
            }
        }
    }

    /// Resolves the immediate parent `.module_scope` of `mod_scope` (`.none` at a package root).
    pub fn findImmediateParentModule(self: *const ScopeArena, mod_scope: ScopeId) ScopeId {
        if (mod_scope.isNone() or mod_scope.asInt() >= self.scopes.len) return .none;
        const rec = self.scopes.get(mod_scope.asInt());
        if (!rec.parent_module.isNone() and rec.parent_module.asInt() != 0) {
            return rec.parent_module;
        }
        if (!rec.parent.isNone() and rec.parent.asInt() < self.scopes.len) {
            const parent_rec = self.scopes.get(rec.parent.asInt());
            if (parent_rec.kind != .global_prelude and !parent_rec.enclosing_module.isNone() and
                parent_rec.enclosing_module != mod_scope)
            {
                return parent_rec.enclosing_module;
            }
        }
        return .none;
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
            if (rec.kind == .module_scope and
                (rec.parent.isNone() or rec.parent.asInt() == 0) and
                !rec.parent_module.isNone() and
                rec.parent_module != cursor)
            {
                cursor = rec.parent_module;
            } else {
                cursor = rec.parent;
            }
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
    /// Explicit `@overload` function and `subscript` groups indexed by `SymbolRecord.target_symbol.asInt()`.
    overload_sets: std.ArrayListUnmanaged(OverloadSet) = .empty,
    /// Maps `FileId.asInt()` to its root `.module_scope` `ScopeId`.
    file_module_scopes: std.AutoHashMapUnmanaged(u32, ScopeId) = .empty,
    /// Maps `FileId.asInt()` to its owning `PackageId` (`PackageId.root` by default).
    file_package_ids: std.AutoHashMapUnmanaged(u32, PackageId) = .empty,
    /// Maps `PackageId` to its root `.module_scope` `ScopeId` (`src/root.cx` or `src/main.cx`).
    package_root_scopes: std.AutoHashMapUnmanaged(PackageId, ScopeId) = .empty,
    /// Maps `(caller_pkg, alias_sym)` (`PkgDepKey`) to the declared dependency's root `.module_scope`.
    package_dep_scopes: std.AutoHashMapUnmanaged(PkgDepKey, ScopeId) = .empty,
    /// Set of `PackageId`s whose dependency tables are explicitly configured (disables flat `named_module_scopes`).
    configured_pkg_deps: std.AutoHashMapUnmanaged(PackageId, void) = .empty,
    /// `true` when a multi-package graph is mounted, preventing sibling `mod` items from clobbering `named_module_scopes`.
    is_flat_named_module_scopes_suppressed: bool = false,
    /// Set of `(pkg_id, feature_sym)` entries declared in `[features]` of each package's `corex.toml` (`E0435`).
    package_declared_features: std.AutoHashMapUnmanaged(PkgFeatureKey, void) = .empty,
    /// Set of `(pkg_id, feature_sym)` entries enabled by unified MVS/PubGrub feature resolution.
    package_enabled_features: std.AutoHashMapUnmanaged(PkgFeatureKey, void) = .empty,
    /// Set of `PackageId`s that registered an explicit `[features]` manifest table (enables per-pkg `E0435`).
    has_package_feature_manifest: std.AutoHashMapUnmanaged(PackageId, void) = .empty,
    /// Maps `PackageId` to its canonical `kebab-case` package name `SymbolId` (`E0012`).
    package_canonical_names: std.AutoHashMapUnmanaged(PackageId, SymbolId) = .empty,
    /// Maps `PackageId` to its interned SemVer label `StringId` (`E0012` & multi-pkg mangling).
    package_version_labels: std.AutoHashMapUnmanaged(PackageId, mem_foundation.StringId) = .empty,
    /// Full per-`PackageId` identity metadata (`canonical_name`, `version_text`, `display_alias`, `root_file_id`).
    package_metas: std.AutoHashMapUnmanaged(PackageId, PackageIdentityMeta) = .empty,
    /// Borrowed reference to the session `StringInterner` for $O(1)$ read-only feature/package lookups.
    interner_ref: ?*const StringInterner = null,
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
    /// Maps a function `SymbolIndex.asInt()` to its owned slice of `FnParamSpec` metadata (`SE-07`, `SE-11`).
    fn_param_specs: std.AutoHashMapUnmanaged(u32, []FnParamSpec) = .empty,
    /// Maps a generic item `SymbolIndex.asInt()` to its owned slice of `GenericParamSpec` metadata (`SE-10`).
    generic_param_specs: std.AutoHashMapUnmanaged(u32, []GenericParamSpec) = .empty,
    /// Sparse map of `extern` function/static FFI linkage and SAST contract metadata (`DR-10` §2.3).
    ffi_contracts: std.AutoHashMapUnmanaged(SymbolIndex, FfiFnContract) = .empty,
    /// Pre-registered or cached `@c_import("header.h")` synthetic module `SymbolIndex` handles.
    c_import_modules: std.StringHashMapUnmanaged(SymbolIndex) = .empty,
    /// Optional on-demand loader invoked when `@c_import("header.h")` misses `c_import_modules`.
    c_import_loader: ?CImportModuleLoader = null,
    /// Deferred `use` imports queued during Pass 1 for Pass 2 cross-module resolution.
    pending_imports: std.ArrayListUnmanaged(PendingUseImport) = .empty,
    /// Global prelude `ScopeId` (`ScopeId.fromInt(0)`).
    prelude_scope: ScopeId = .none,
    /// Lazily populated `cx.meta` reflection module `ScopeId` (`DR-05` §3.3 & `DR-21` `ADR-21B`).
    cx_meta_scope: ScopeId = .none,
    /// Lazily resolved or synthesized `cx` unified standard library root `ScopeId` (`DR-21` `ADR-21B`).
    cx_root_scope: ScopeId = .none,
    /// Lazily resolved or synthesized `cx.sync.atomic` / `cx.atomic` module `ScopeId`.
    cx_atomic_scope: ScopeId = .none,
    /// `true` when compiling internal `core/` sources (`--internal-core` or `Durability.high`), suppressing `E0218`.
    is_internal_core: bool = false,
    /// `true` when `test "…"` and `bench "…"` items are active (`SE-16`); `false` skips them in $O(1)$.
    is_including_tests: bool = true,
    /// Active `@cfg(expr)` target and build-mode evaluation context for `use` imports (`SE-18`).
    cfg_env: CfgEnv = .{},

    /// Initializes a new `SymbolTable` and pre-populates the global prelude scope (`ScopeId` `0`).
    pub fn init(allocator: std.mem.Allocator, interner: *StringInterner) !SymbolTable {
        var self = SymbolTable{
            .allocator = allocator,
            .scope_arena = ScopeArena.init(allocator),
            .interner_ref = interner,
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

        var param_spec_iter = self.fn_param_specs.valueIterator();
        while (param_spec_iter.next()) |spec_slice_ptr| {
            self.allocator.free(spec_slice_ptr.*);
        }
        self.fn_param_specs.deinit(self.allocator);

        var generic_spec_iter = self.generic_param_specs.valueIterator();
        while (generic_spec_iter.next()) |spec_slice_ptr| {
            self.allocator.free(spec_slice_ptr.*);
        }
        self.generic_param_specs.deinit(self.allocator);

        var ffi_contract_iter = self.ffi_contracts.valueIterator();
        while (ffi_contract_iter.next()) |contract_ptr| {
            if (contract_ptr.param_contracts.len > 0) {
                self.allocator.free(contract_ptr.param_contracts);
            }
        }
        self.ffi_contracts.deinit(self.allocator);
        self.c_import_modules.deinit(self.allocator);

        self.symbols.deinit(self.allocator);
        self.scoped_map.deinit(self.allocator);
        self.file_module_scopes.deinit(self.allocator);
        self.file_package_ids.deinit(self.allocator);
        self.package_root_scopes.deinit(self.allocator);
        self.package_dep_scopes.deinit(self.allocator);
        self.configured_pkg_deps.deinit(self.allocator);
        self.package_declared_features.deinit(self.allocator);
        self.package_enabled_features.deinit(self.allocator);
        self.has_package_feature_manifest.deinit(self.allocator);
        self.package_canonical_names.deinit(self.allocator);
        self.package_version_labels.deinit(self.allocator);
        self.package_metas.deinit(self.allocator);
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

        var param_spec_iter = self.fn_param_specs.valueIterator();
        while (param_spec_iter.next()) |spec_slice_ptr| {
            self.allocator.free(spec_slice_ptr.*);
        }
        self.fn_param_specs.clearRetainingCapacity();

        var generic_spec_iter = self.generic_param_specs.valueIterator();
        while (generic_spec_iter.next()) |spec_slice_ptr| {
            self.allocator.free(spec_slice_ptr.*);
        }
        self.generic_param_specs.clearRetainingCapacity();

        var ffi_reset_iter = self.ffi_contracts.valueIterator();
        while (ffi_reset_iter.next()) |contract_ptr| {
            if (contract_ptr.param_contracts.len > 0) {
                self.allocator.free(contract_ptr.param_contracts);
            }
        }
        self.ffi_contracts.clearRetainingCapacity();
        self.c_import_modules.clearRetainingCapacity();
        self.c_import_loader = null;

        self.symbols.clearRetainingCapacity();
        self.scoped_map.clearRetainingCapacity();
        self.file_module_scopes.clearRetainingCapacity();
        self.file_package_ids.clearRetainingCapacity();
        self.package_root_scopes.clearRetainingCapacity();
        self.package_dep_scopes.clearRetainingCapacity();
        self.configured_pkg_deps.clearRetainingCapacity();
        self.is_flat_named_module_scopes_suppressed = false;
        self.package_declared_features.clearRetainingCapacity();
        self.package_enabled_features.clearRetainingCapacity();
        self.has_package_feature_manifest.clearRetainingCapacity();
        self.package_canonical_names.clearRetainingCapacity();
        self.package_version_labels.clearRetainingCapacity();
        self.package_metas.clearRetainingCapacity();
        self.interner_ref = interner;
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
        self.cx_meta_scope = .none;
        self.cx_root_scope = .none;
        self.cx_atomic_scope = .none;
        self.is_internal_core = false;
        self.is_including_tests = true;
        self.cfg_env = .{};
        try self.populateGlobalPrelude(interner);
    }

    /// Associates `file_id` with `pkg_id` for `pub(pkg)` visibility verification (`ADR-22E`).
    pub fn setFilePackageId(self: *SymbolTable, file_id: FileId, pkg_id: PackageId) !void {
        if (file_id.isNone()) return;
        try self.file_package_ids.put(self.allocator, file_id.asInt(), pkg_id);
        if (self.file_module_scopes.get(file_id.asInt())) |mod_scope| {
            self.scope_arena.setScopePackageId(mod_scope, pkg_id);
        }
    }

    /// Returns the `PackageId` assigned to `file_id` (`.root` when unassigned).
    pub fn getFilePackageId(self: *const SymbolTable, file_id: FileId) PackageId {
        if (file_id.isNone()) return .root;
        return self.file_package_ids.get(file_id.asInt()) orelse .root;
    }

    /// Returns `true` if `file_id` is permitted to import `core.*` directly (`false` for all `PackageId >= 2`).
    pub fn isCoreAllowedForFile(self: *const SymbolTable, file_id: FileId) bool {
        const pkg_id = self.getFilePackageId(file_id);
        if (pkg_id == .std_core) return true;
        if (pkg_id != .root) return false;
        return self.is_internal_core;
    }

    /// Registers `root_scope` as the package-root `.module_scope` for `pkg_id` (`use pkg.…`).
    pub fn setPackageRootScope(self: *SymbolTable, pkg_id: PackageId, root_scope: ScopeId) !void {
        if (root_scope.isNone()) return;
        try self.package_root_scopes.put(self.allocator, pkg_id, root_scope);
        self.scope_arena.setScopePackageId(root_scope, pkg_id);
    }

    /// Returns the registered package-root `ScopeId` for `pkg_id`, or `null` when unregistered.
    pub fn lookupPackageRootScope(self: *const SymbolTable, pkg_id: PackageId) ?ScopeId {
        if (self.package_root_scopes.get(pkg_id)) |root_scope| {
            if (!root_scope.isNone()) return root_scope;
        }
        return null;
    }

    /// Resolves the package-root `ScopeId` for `caller_file_id` (falling back to `file_module_scopes` or `fallback_scope`).
    pub fn resolveCallerPackageRootScope(
        self: *const SymbolTable,
        caller_file_id: FileId,
        fallback_scope: ScopeId,
    ) ScopeId {
        const caller_pkg = self.getFilePackageId(caller_file_id);
        if (self.lookupPackageRootScope(caller_pkg)) |pkg_root| {
            return pkg_root;
        }
        if (!caller_file_id.isNone()) {
            if (self.file_module_scopes.get(caller_file_id.asInt())) |file_scope| {
                if (!file_scope.isNone()) return file_scope;
            }
        }
        return fallback_scope;
    }

    /// Binds `(caller_pkg_id, alias_sym)` to `target_root_scope` and marks `caller_pkg_id` dependency-isolated.
    pub fn bindPackageDepScope(
        self: *SymbolTable,
        caller_pkg_id: PackageId,
        alias_sym: SymbolId,
        target_root_scope: ScopeId,
    ) !void {
        try self.configured_pkg_deps.put(self.allocator, caller_pkg_id, {});
        if (!target_root_scope.isNone()) {
            try self.package_dep_scopes.put(
                self.allocator,
                .{ .caller_pkg = caller_pkg_id, .alias_sym = alias_sym },
                target_root_scope,
            );
        }
    }

    /// Marks `caller_pkg_id` as having an explicit dependency table (even when empty, disabling `named_module_scopes`).
    pub fn markPackageDepsConfigured(self: *SymbolTable, caller_pkg_id: PackageId) !void {
        try self.configured_pkg_deps.put(self.allocator, caller_pkg_id, {});
    }

    /// Looks up a declared external dependency root `ScopeId` for `(caller_file_id, alias_sym)`.
    pub fn lookupExternalPackageScope(
        self: *const SymbolTable,
        caller_file_id: FileId,
        alias_sym: SymbolId,
    ) ?ScopeId {
        const caller_pkg = self.getFilePackageId(caller_file_id);
        if (self.package_dep_scopes.get(.{ .caller_pkg = caller_pkg, .alias_sym = alias_sym })) |dep_scope| {
            if (!dep_scope.isNone()) return dep_scope;
        }
        if (self.configured_pkg_deps.contains(caller_pkg) or self.is_flat_named_module_scopes_suppressed) {
            return null;
        }
        if (self.named_module_scopes.get(alias_sym.asInt())) |legacy_scope| {
            if (!legacy_scope.isNone()) return legacy_scope;
        }
        return null;
    }

    /// Registers canonical package name and version label handles for `pkg_id` (`E0012` & mangling).
    pub fn setPackageOriginMetadata(
        self: *SymbolTable,
        interner: *const StringInterner,
        pkg_id: PackageId,
        canonical_name_sym: SymbolId,
        version_label_id: mem_foundation.StringId,
    ) !void {
        self.interner_ref = interner;
        try self.package_canonical_names.put(self.allocator, pkg_id, canonical_name_sym);
        try self.package_version_labels.put(self.allocator, pkg_id, version_label_id);
        const canon_slice = interner.get(canonical_name_sym);
        const ver_slice = interner.get(version_label_id);
        if (self.package_metas.getPtr(pkg_id)) |existing_meta| {
            existing_meta.canonical_name_sym = canonical_name_sym;
            existing_meta.canonical_name = canon_slice;
            existing_meta.version_text = ver_slice;
        } else {
            try self.package_metas.put(self.allocator, pkg_id, .{
                .pkg_id = pkg_id,
                .canonical_name_sym = canonical_name_sym,
                .canonical_name = canon_slice,
                .version_text = ver_slice,
            });
        }
    }

    /// Registers complete `PackageIdentityMeta` for `pkg_id`, synchronizing `package_canonical_names` and `package_version_labels`.
    pub fn setPackageIdentityMeta(
        self: *SymbolTable,
        interner: *StringInterner,
        pkg_id: PackageId,
        canonical_name: []const u8,
        version_text: []const u8,
        display_alias: []const u8,
        root_file_id: FileId,
    ) !void {
        self.interner_ref = interner;
        const canon_sym = try interner.intern(canonical_name);
        const ver_id = try interner.intern(version_text);
        const alias_id = if (display_alias.len > 0) try interner.intern(display_alias) else .empty;
        try self.package_canonical_names.put(self.allocator, pkg_id, canon_sym);
        try self.package_version_labels.put(self.allocator, pkg_id, ver_id);
        try self.package_metas.put(self.allocator, pkg_id, .{
            .pkg_id = pkg_id,
            .canonical_name_sym = canon_sym,
            .canonical_name = interner.get(canon_sym),
            .version_text = interner.get(ver_id),
            .display_alias = if (alias_id != .empty) interner.get(alias_id) else "",
            .root_file_id = root_file_id,
        });
    }

    /// Marks `pkg_id` as owning an explicit `[features]` manifest table so undeclared `@cfg` features emit `E0435`.
    pub fn registerPackageFeatureManifest(self: *SymbolTable, pkg_id: PackageId) !void {
        try self.has_package_feature_manifest.put(self.allocator, pkg_id, {});
    }

    /// Declares a valid `[features]` key `feature_sym` on `pkg_id` (and marks `has_package_feature_manifest`).
    pub fn declarePackageFeature(
        self: *SymbolTable,
        pkg_id: PackageId,
        feature_sym: SymbolId,
    ) !void {
        try self.has_package_feature_manifest.put(self.allocator, pkg_id, {});
        try self.package_declared_features.put(
            self.allocator,
            .{ .pkg_id = pkg_id, .feature_sym = feature_sym },
            {},
        );
    }

    /// Activates `feature_sym` on `pkg_id` for `@cfg(cfg.feature.<name>)` evaluation.
    pub fn enablePackageFeature(
        self: *SymbolTable,
        pkg_id: PackageId,
        feature_sym: SymbolId,
    ) !void {
        try self.package_enabled_features.put(
            self.allocator,
            .{ .pkg_id = pkg_id, .feature_sym = feature_sym },
            {},
        );
    }

    /// Returns `true` if `feat_name` is declared in `pkg_id`'s `[features]` table (`O(1)` read-only lookup).
    pub fn isPackageFeatureDeclared(
        self: *const SymbolTable,
        pkg_id: PackageId,
        feat_name: []const u8,
    ) bool {
        const str_interner = self.interner_ref orelse return false;
        const feat_sym = str_interner.lookup(feat_name) orelse return false;
        return self.package_declared_features.contains(.{ .pkg_id = pkg_id, .feature_sym = feat_sym });
    }

    /// Returns `true` if `feat_name` is enabled on `pkg_id` (`O(1)` read-only lookup).
    pub fn isPackageFeatureEnabled(
        self: *const SymbolTable,
        pkg_id: PackageId,
        feat_name: []const u8,
    ) bool {
        const str_interner = self.interner_ref orelse return false;
        const feat_sym = str_interner.lookup(feat_name) orelse return false;
        return self.package_enabled_features.contains(.{ .pkg_id = pkg_id, .feature_sym = feat_sym });
    }

    /// Returns a `CfgEnv` scoped to `file_id`'s `PackageId` (pruning `test` mode on `PackageId >= 2`).
    pub fn effectiveCfgEnvForFile(self: *const SymbolTable, file_id: FileId) CfgEnv {
        var file_cfg = self.cfg_env;
        const pkg_id = self.getFilePackageId(file_id);
        file_cfg.owner_pkg_id = pkg_id;
        file_cfg.sym_table_features = self;
        if (pkg_id != .root) {
            file_cfg.is_test_mode = false;
        }
        return file_cfg;
    }

    /// Stores a duplicated `FnParamSpec` slice for `fn_sym_idx`, preserving CST zone flags across re-binds.
    pub fn setFnParamSpecs(
        self: *SymbolTable,
        fn_sym_idx: SymbolIndex,
        specs: []const FnParamSpec,
    ) !void {
        if (fn_sym_idx.isNone()) return;
        const prev_opt = self.fn_param_specs.get(fn_sym_idx.asInt());
        const has_trailing_variadic = if (prev_opt) |prev|
            (prev.len == specs.len + 1 and prev[specs.len].is_variadic)
        else
            false;
        const alloc_len = if (has_trailing_variadic) specs.len + 1 else specs.len;
        const owned = try self.allocator.alloc(FnParamSpec, alloc_len);
        errdefer self.allocator.free(owned);
        @memcpy(owned[0..specs.len], specs);
        if (prev_opt) |prev| {
            if (prev.len == specs.len or has_trailing_variadic) {
                var i: usize = 0;
                while (i < specs.len) : (i += 1) {
                    if (owned[i].name == prev[i].name) {
                        owned[i].is_positional_only = owned[i].is_positional_only or prev[i].is_positional_only;
                        owned[i].is_keyword_only = owned[i].is_keyword_only or prev[i].is_keyword_only;
                        owned[i].is_variadic = owned[i].is_variadic or prev[i].is_variadic;
                        owned[i].is_local_var = owned[i].is_local_var or prev[i].is_local_var;
                        owned[i].is_builder = owned[i].is_builder or prev[i].is_builder;
                        owned[i].is_caller_location_default = owned[i].is_caller_location_default or
                            prev[i].is_caller_location_default;
                    }
                }
            }
            if (has_trailing_variadic) {
                owned[specs.len] = prev[specs.len];
            }
        }
        if (try self.fn_param_specs.fetchPut(self.allocator, fn_sym_idx.asInt(), owned)) |prev_kv| {
            self.allocator.free(prev_kv.value);
        }
    }

    /// Retrieves the `FnParamSpec` slice recorded for `fn_sym_idx`, or `&.{}` if none is registered.
    pub fn getFnParamSpecs(self: *const SymbolTable, fn_sym_idx: SymbolIndex) []const FnParamSpec {
        if (fn_sym_idx.isNone()) return &.{};
        return self.fn_param_specs.get(fn_sym_idx.asInt()) orelse &.{};
    }

    /// Retrieves the mutable `FnParamSpec` slice recorded for `fn_sym_idx`, or `&.{}` if none is registered.
    pub fn getFnParamSpecsMut(self: *SymbolTable, fn_sym_idx: SymbolIndex) []FnParamSpec {
        if (fn_sym_idx.isNone()) return &.{};
        return self.fn_param_specs.get(fn_sym_idx.asInt()) orelse &.{};
    }

    /// Stores a duplicated `GenericParamSpec` slice for `sym_idx` (`SE-10` generic parameter defaults).
    pub fn setGenericParamSpecs(
        self: *SymbolTable,
        sym_idx: SymbolIndex,
        specs: []const GenericParamSpec,
    ) !void {
        if (sym_idx.isNone()) return;
        const owned = try self.allocator.dupe(GenericParamSpec, specs);
        errdefer self.allocator.free(owned);
        if (try self.generic_param_specs.fetchPut(self.allocator, sym_idx.asInt(), owned)) |prev_kv| {
            self.allocator.free(prev_kv.value);
        }
    }

    /// Retrieves the `GenericParamSpec` slice recorded for `sym_idx`, or `&.{}` if none is registered.
    pub fn getGenericParamSpecs(self: *const SymbolTable, sym_idx: SymbolIndex) []const GenericParamSpec {
        if (sym_idx.isNone()) return &.{};
        return self.generic_param_specs.get(sym_idx.asInt()) orelse &.{};
    }

    /// Retrieves the mutable `GenericParamSpec` slice recorded for `sym_idx`, or `&.{}` if none is registered.
    pub fn getGenericParamSpecsMut(self: *SymbolTable, sym_idx: SymbolIndex) []GenericParamSpec {
        if (sym_idx.isNone()) return &.{};
        return self.generic_param_specs.get(sym_idx.asInt()) orelse &.{};
    }

    /// Stores `contract` (duplicating `param_contracts` when non-empty) in `ffi_contracts` for `sym_idx`.
    pub fn setFfiContract(
        self: *SymbolTable,
        sym_idx: SymbolIndex,
        contract: FfiFnContract,
        param_contracts: []const FfiParamContract,
    ) !void {
        if (sym_idx.isNone()) return;
        const owned_params: []FfiParamContract = if (param_contracts.len > 0)
            try self.allocator.dupe(FfiParamContract, param_contracts)
        else
            &.{};
        errdefer if (owned_params.len > 0) self.allocator.free(owned_params);
        var stored_contract = contract;
        stored_contract.param_contracts = owned_params;
        if (try self.ffi_contracts.fetchPut(self.allocator, sym_idx, stored_contract)) |prev_kv| {
            if (prev_kv.value.param_contracts.len > 0) {
                self.allocator.free(prev_kv.value.param_contracts);
            }
        }
    }

    /// Returns a read-only pointer to the `FfiFnContract` registered for `sym_idx`, or `null` if none exists.
    pub fn getFfiContract(self: *const SymbolTable, sym_idx: SymbolIndex) ?*const FfiFnContract {
        if (sym_idx.isNone()) return null;
        return self.ffi_contracts.getPtr(sym_idx);
    }

    /// Registers a translated `@c_import("header.h")` synthetic module `mod_sym_idx` under `header_path`.
    pub fn registerCImportModule(
        self: *SymbolTable,
        interner: *StringInterner,
        header_path: []const u8,
        mod_sym_idx: SymbolIndex,
    ) !void {
        const interned_id = try interner.intern(header_path);
        try self.c_import_modules.put(self.allocator, interner.get(interned_id), mod_sym_idx);
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
        if (self.file_module_scopes.get(parent_file_id.asInt())) |parent_mod_scope| {
            self.scope_arena.setParentModule(target_scope, parent_mod_scope);
            const mod_sym_idx = self.lookupInScopeDirect(
                parent_mod_scope,
                mod_name,
                NamespaceMask.VALUE_ONLY,
            );
            if (!mod_sym_idx.isNone() and self.getSymbol(mod_sym_idx).kind == .module_sym) {
                self.getSymbolMut(mod_sym_idx).target_scope = target_scope;
            }
        }
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

    /// Lazily populates `cx.meta` and its 8 value-based reflection mirror stubs (`DR-05` §3.3 & `DR-21`).
    pub fn ensureCxMetaScope(self: *SymbolTable, interner: *StringInterner) anyerror!ScopeId {
        if (!self.cx_meta_scope.isNone()) return self.cx_meta_scope;

        const root_scope = if (!self.cx_root_scope.isNone())
            self.cx_root_scope
        else
            try self.ensureCxRootScope(interner);
        if (!self.cx_meta_scope.isNone()) return self.cx_meta_scope;

        const meta_sym_id = try interner.intern("meta");
        const existing_meta = self.lookupInScopeDirect(
            root_scope,
            meta_sym_id,
            NamespaceMask.VALUE_ONLY,
        );
        const meta_scope = if (!existing_meta.isNone() and
            !self.getSymbol(existing_meta).target_scope.isNone())
            self.getSymbol(existing_meta).target_scope
        else blk: {
            const fresh_meta_scope = try self.scope_arena.allocScope(
                .module_scope,
                root_scope,
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
                .scope_id = root_scope,
                .target_scope = fresh_meta_scope,
            }, null);
            break :blk fresh_meta_scope;
        };

        for (CX_META_MIRROR_STUBS) |stub| {
            const stub_sym_id = try interner.intern(stub.name);
            if (!self.lookupInScopeDirect(meta_scope, stub_sym_id, NamespaceMask.TYPE_ONLY).isNone()) {
                continue;
            }
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

        self.cx_meta_scope = meta_scope;
        return meta_scope;
    }

    /// Lazily resolves or synthesizes the unified `cx` standard library root scope and built-in submodule bridges (`DR-21`).
    pub fn ensureCxRootScope(self: *SymbolTable, interner: *StringInterner) anyerror!ScopeId {
        const core_sym_id = try interner.intern("core");
        const cx_sym_id = try interner.intern("cx");

        const registered_root = self.named_module_scopes.get(core_sym_id.asInt()) orelse
            self.named_module_scopes.get(cx_sym_id.asInt()) orelse
            ScopeId.none;
        const root_scope = if (!registered_root.isNone())
            registered_root
        else if (!self.cx_root_scope.isNone())
            self.cx_root_scope
        else
            try self.scope_arena.allocScope(.module_scope, self.prelude_scope, .NONE, .none, .{});

        self.cx_root_scope = root_scope;
        try self.named_module_scopes.put(self.allocator, cx_sym_id.asInt(), root_scope);
        const existing_cx = self.lookupInScopeDirect(self.prelude_scope, cx_sym_id, NamespaceMask.VALUE_ONLY);
        if (existing_cx.isNone()) {
            _ = try self.defineSymbol(.{
                .name = cx_sym_id,
                .name_text = interner.get(cx_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = self.prelude_scope,
                .target_scope = root_scope,
            }, null);
        } else {
            self.getSymbolMut(existing_cx).target_scope = root_scope;
        }

        // [1] Ensure `cx.meta` and its reflection mirror types (`TypeInfo`, `FieldInfo`, etc.) exist under `cx`:
        _ = try self.ensureCxMetaScope(interner);

        // [2] Bridge `cx.sync.atomic` -> `core/atomic.cx` when loaded, or synthesize standalone `atomic` stubs (`[P0-A]`):
        const atomic_sym_id = try interner.intern("atomic");
        const existing_atomic = self.lookupInScopeDirect(root_scope, atomic_sym_id, NamespaceMask.VALUE_ONLY);
        const atomic_scope = if (!existing_atomic.isNone() and !self.getSymbol(existing_atomic).target_scope.isNone())
            self.getSymbol(existing_atomic).target_scope
        else blk: {
            const fresh_atomic_scope = try self.scope_arena.allocScope(.module_scope, root_scope, .NONE, .none, .{});
            _ = try self.defineSymbol(.{
                .name = atomic_sym_id,
                .name_text = interner.get(atomic_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = root_scope,
                .target_scope = fresh_atomic_scope,
            }, null);
            break :blk fresh_atomic_scope;
        };
        const atomic_order_variants = [_][]const u8{
            "Relaxed",
            "Consume",
            "Acquire",
            "Release",
            "AcqRel",
            "SeqCst",
        };
        try self.populateStandaloneEnumStubWithRepr(interner, atomic_scope, "MemoryOrder", &atomic_order_variants, 8);
        try self.populateStandaloneEnumStubWithRepr(interner, atomic_scope, "Ordering", &atomic_order_variants, 8);
        self.cx_atomic_scope = atomic_scope;

        const sync_sym_id = try interner.intern("sync");
        const existing_sync = self.lookupInScopeDirect(root_scope, sync_sym_id, NamespaceMask.VALUE_ONLY);
        const sync_scope = if (!existing_sync.isNone() and !self.getSymbol(existing_sync).target_scope.isNone())
            self.getSymbol(existing_sync).target_scope
        else blk: {
            const fresh_sync_scope = try self.scope_arena.allocScope(.module_scope, root_scope, .NONE, .none, .{});
            _ = try self.defineSymbol(.{
                .name = sync_sym_id,
                .name_text = interner.get(sync_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = root_scope,
                .target_scope = fresh_sync_scope,
            }, null);
            break :blk fresh_sync_scope;
        };
        if (self.lookupInScopeDirect(sync_scope, atomic_sym_id, NamespaceMask.VALUE_ONLY).isNone()) {
            _ = try self.defineSymbol(.{
                .name = atomic_sym_id,
                .name_text = interner.get(atomic_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = sync_scope,
                .target_scope = atomic_scope,
            }, null);
        }

        // [3] Synthesize standalone `cx.cmp`, `cx.io`, `cx.fs`, `cx.mem`, `cx.fmt`, `cx.testing`, `cx.async`, `cx.ffi`:
        const cmp_sym_id = try interner.intern("cmp");
        if (self.lookupInScopeDirect(root_scope, cmp_sym_id, NamespaceMask.VALUE_ONLY).isNone()) {
            const cmp_scope = try self.scope_arena.allocScope(.module_scope, root_scope, .NONE, .none, .{});
            _ = try self.defineSymbol(.{
                .name = cmp_sym_id,
                .name_text = interner.get(cmp_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = root_scope,
                .target_scope = cmp_scope,
            }, null);
            try self.populateStandaloneEnumStub(interner, cmp_scope, "Ordering", &.{ "Less", "Equal", "Greater" });
        }

        const io_sym_id = try interner.intern("io");
        if (self.lookupInScopeDirect(root_scope, io_sym_id, NamespaceMask.VALUE_ONLY).isNone()) {
            const io_scope = try self.scope_arena.allocScope(.module_scope, root_scope, .NONE, .none, .{});
            _ = try self.defineSymbol(.{
                .name = io_sym_id,
                .name_text = interner.get(io_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = root_scope,
                .target_scope = io_scope,
            }, null);
            for ([_][]const u8{ "Read", "Write" }) |trait_stub| {
                const trait_id = try interner.intern(trait_stub);
                const trait_scope = try self.scope_arena.allocScope(.trait_scope, io_scope, .NONE, .none, .{});
                _ = try self.defineSymbol(.{
                    .name = trait_id,
                    .name_text = interner.get(trait_id),
                    .kind = .trait_sym,
                    .namespace = .type_ns,
                    .visibility = .public,
                    .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                    .scope_id = io_scope,
                    .target_scope = trait_scope,
                }, null);
            }
        }

        const fs_sym_id = try interner.intern("fs");
        if (self.lookupInScopeDirect(root_scope, fs_sym_id, NamespaceMask.VALUE_ONLY).isNone()) {
            const fs_scope = try self.scope_arena.allocScope(.module_scope, root_scope, .NONE, .none, .{});
            _ = try self.defineSymbol(.{
                .name = fs_sym_id,
                .name_text = interner.get(fs_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = root_scope,
                .target_scope = fs_scope,
            }, null);
            const file_ty_id = try interner.intern("File");
            const file_member_scope = try self.scope_arena.allocScope(.nominal_type_scope, fs_scope, .NONE, .none, .{});
            _ = try self.defineSymbol(.{
                .name = file_ty_id,
                .name_text = interner.get(file_ty_id),
                .kind = .struct_sym,
                .namespace = .type_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = fs_scope,
                .target_scope = file_member_scope,
            }, null);
        }

        const mem_sym_id = try interner.intern("mem");
        if (self.lookupInScopeDirect(root_scope, mem_sym_id, NamespaceMask.VALUE_ONLY).isNone()) {
            const mem_scope = try self.scope_arena.allocScope(.module_scope, root_scope, .NONE, .none, .{});
            _ = try self.defineSymbol(.{
                .name = mem_sym_id,
                .name_text = interner.get(mem_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = root_scope,
                .target_scope = mem_scope,
            }, null);
            const alloc_trait_id = try interner.intern("Allocator");
            const alloc_trait_scope = try self.scope_arena.allocScope(.trait_scope, mem_scope, .NONE, .none, .{});
            _ = try self.defineSymbol(.{
                .name = alloc_trait_id,
                .name_text = interner.get(alloc_trait_id),
                .kind = .trait_sym,
                .namespace = .type_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = mem_scope,
                .target_scope = alloc_trait_scope,
            }, null);
        }

        try self.populateStandaloneTypeSubmoduleStub(interner, root_scope, "fmt", &.{
            .{ .name = "FmtSpec", .type_id = .fmt_spec_ty },
            .{ .name = "FmtArgs", .type_id = .fmt_args_ty },
        });
        try self.populateStandaloneTypeSubmoduleStub(interner, root_scope, "testing", &.{
            .{ .name = "Bencher", .type_id = .bencher_ty },
        });
        try self.populateStandaloneTypeSubmoduleStub(interner, root_scope, "async", &.{
            .{ .name = "TaskGroup", .type_id = .task_group_base_ty },
            .{ .name = "TaskHandle", .type_id = .task_handle_base_ty },
        });
        const async_mod_id = try interner.intern("async");
        const async_mod_idx = self.lookupInScopeDirect(root_scope, async_mod_id, NamespaceMask.VALUE_ONLY);
        if (!async_mod_idx.isNone() and !self.getSymbol(async_mod_idx).target_scope.isNone()) {
            const async_sub_scope = self.getSymbol(async_mod_idx).target_scope;
            for ([_][]const u8{ "block_on", "task_group", "yield_now" }) |async_fn_name| {
                const fn_sym_id = try interner.intern(async_fn_name);
                if (self.lookupInScopeDirect(async_sub_scope, fn_sym_id, NamespaceMask.VALUE_ONLY).isNone()) {
                    _ = try self.defineSymbol(.{
                        .name = fn_sym_id,
                        .name_text = interner.get(fn_sym_id),
                        .kind = .fn_sym,
                        .namespace = .value_ns,
                        .visibility = .public,
                        .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                        .scope_id = async_sub_scope,
                        .type_id = .err_ty,
                    }, null);
                }
            }
        }
        const target_c_tys = computeTargetCFfiTypes(self.cfg_env);
        try self.populateStandaloneTypeSubmoduleStub(interner, root_scope, "ffi", &.{
            .{ .name = "c_char", .type_id = target_c_tys.c_char_ty },
            .{ .name = "c_schar", .type_id = .i8_ty },
            .{ .name = "c_uchar", .type_id = .u8_ty },
            .{ .name = "c_short", .type_id = .i16_ty },
            .{ .name = "c_ushort", .type_id = .u16_ty },
            .{ .name = "c_int", .type_id = .i32_ty },
            .{ .name = "c_uint", .type_id = .u32_ty },
            .{ .name = "c_long", .type_id = target_c_tys.c_long_ty },
            .{ .name = "c_ulong", .type_id = target_c_tys.c_ulong_ty },
            .{ .name = "c_longlong", .type_id = .i64_ty },
            .{ .name = "c_ulonglong", .type_id = .u64_ty },
            .{ .name = "c_longdouble", .type_id = .f64_ty },
            .{ .name = "c_void", .type_id = .opaque_ty },
        });

        return root_scope;
    }

    /// Refreshes target-dependent `cx.ffi` built-in type aliases (`c_char`, `c_long`, `c_ulong`) in-place from `self.cfg_env`.
    pub fn refreshCxFfiTargetAliases(self: *SymbolTable, interner: *const StringInterner) void {
        if (self.cx_root_scope.isNone()) return;
        const ffi_sym_id = interner.lookup("ffi") orelse return;
        const ffi_mod_idx = self.lookupInScopeDirect(self.cx_root_scope, ffi_sym_id, NamespaceMask.VALUE_ONLY);
        if (ffi_mod_idx.isNone()) return;
        const ffi_scope = self.getSymbol(ffi_mod_idx).target_scope;
        if (ffi_scope.isNone()) return;

        const target_c_tys = computeTargetCFfiTypes(self.cfg_env);
        const target_updates = [3]struct { name: []const u8, ty: TypeId }{
            .{ .name = "c_char", .ty = target_c_tys.c_char_ty },
            .{ .name = "c_long", .ty = target_c_tys.c_long_ty },
            .{ .name = "c_ulong", .ty = target_c_tys.c_ulong_ty },
        };
        var updated_syms: [3]SymbolIndex = @splat(.none);
        var prev_targets: [3]SymbolIndex = @splat(.none);
        var next_targets: [3]SymbolIndex = @splat(.none);
        for (target_updates, 0..) |upd, i| {
            const name_id = interner.lookup(upd.name) orelse continue;
            const sym_idx = self.lookupInScopeDirect(ffi_scope, name_id, NamespaceMask.TYPE_ONLY);
            if (!sym_idx.isNone() and self.getSymbol(sym_idx).flags.is_builtin) {
                const target_prelude = self.type_to_symbol.get(upd.ty.toU32()) orelse SymbolIndex.none;
                const target_member_scope = if (!target_prelude.isNone())
                    self.getSymbol(target_prelude).target_scope
                else
                    ScopeId.none;
                const sym_mut = self.getSymbolMut(sym_idx);
                prev_targets[i] = sym_mut.target_symbol;
                next_targets[i] = target_prelude;
                sym_mut.type_id = upd.ty;
                sym_mut.target_symbol = target_prelude;
                sym_mut.target_scope = target_member_scope;
                updated_syms[i] = sym_idx;
            }
        }
        for (self.symbols.items) |*sym_rec| {
            if (sym_rec.kind == .use_alias_sym and !sym_rec.target_symbol.isNone()) {
                for (updated_syms, prev_targets, next_targets, target_updates) |upd_sym, prev_tgt, next_tgt, upd| {
                    if (upd_sym.isNone()) continue;
                    const is_direct_alias = (sym_rec.target_symbol == upd_sym);
                    const is_unwrapped_ffi_alias = (!prev_tgt.isNone() and
                        sym_rec.target_symbol == prev_tgt and
                        std.mem.eql(u8, sym_rec.name_text, upd.name));
                    if (is_direct_alias or is_unwrapped_ffi_alias) {
                        sym_rec.type_id = upd.ty;
                        if (is_unwrapped_ffi_alias and !next_tgt.isNone()) {
                            sym_rec.target_symbol = next_tgt;
                        }
                        break;
                    }
                }
            }
        }
    }

    /// Populates a built-in unit-variant `enum` stub inside `parent_scope` when `core/` sources are absent.
    fn populateStandaloneEnumStub(
        self: *SymbolTable,
        interner: *StringInterner,
        parent_scope: ScopeId,
        enum_name: []const u8,
        variant_names: []const []const u8,
    ) !void {
        return self.populateStandaloneEnumStubWithRepr(interner, parent_scope, enum_name, variant_names, 0);
    }

    /// Populates a built-in unit-variant `enum` stub with explicit `repr_tag_bits` inside `parent_scope`.
    fn populateStandaloneEnumStubWithRepr(
        self: *SymbolTable,
        interner: *StringInterner,
        parent_scope: ScopeId,
        enum_name: []const u8,
        variant_names: []const []const u8,
        repr_tag_bits: u8,
    ) !void {
        const enum_sym_id = try interner.intern(enum_name);
        if (!self.lookupInScopeDirect(parent_scope, enum_sym_id, NamespaceMask.TYPE_ONLY).isNone()) return;
        const var_scope = try self.scope_arena.allocScope(.nominal_type_scope, parent_scope, .NONE, .none, .{});
        _ = try self.defineSymbol(.{
            .name = enum_sym_id,
            .name_text = interner.get(enum_sym_id),
            .kind = .enum_sym,
            .namespace = .type_ns,
            .visibility = .public,
            .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
            .scope_id = parent_scope,
            .target_scope = var_scope,
            .derive_mask = .{ .has_eq = true, .has_hash = true, .has_debug = true, .has_clone = true, .has_copy = true },
            .repr_tag_bits = repr_tag_bits,
        }, null);
        for (variant_names, 0..) |var_name, ord| {
            const var_id = try interner.intern(var_name);
            _ = try self.defineSymbol(.{
                .name = var_id,
                .name_text = interner.get(var_id),
                .kind = .enum_variant_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = var_scope,
                .type_id = .unit_ty,
                .member_ordinal = @intCast(ord),
            }, null);
        }
    }

    /// Populates a standalone `cx.<submodule>` stub exposing pre-wired built-in `TypeId` entries.
    fn populateStandaloneTypeSubmoduleStub(
        self: *SymbolTable,
        interner: *StringInterner,
        root_scope: ScopeId,
        submod_name: []const u8,
        entries: []const struct { name: []const u8, type_id: TypeId },
    ) !void {
        const sub_sym_id = try interner.intern(submod_name);
        const existing_sub = self.lookupInScopeDirect(root_scope, sub_sym_id, NamespaceMask.VALUE_ONLY);
        const sub_scope = if (!existing_sub.isNone() and !self.getSymbol(existing_sub).target_scope.isNone())
            self.getSymbol(existing_sub).target_scope
        else blk: {
            const fresh_scope = try self.scope_arena.allocScope(.module_scope, root_scope, .NONE, .none, .{});
            _ = try self.defineSymbol(.{
                .name = sub_sym_id,
                .name_text = interner.get(sub_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true },
                .scope_id = root_scope,
                .target_scope = fresh_scope,
            }, null);
            break :blk fresh_scope;
        };
        for (entries) |entry| {
            const ty_sym_id = try interner.intern(entry.name);
            const target_prelude = self.type_to_symbol.get(entry.type_id.toU32()) orelse SymbolIndex.none;
            const target_member_scope = if (!target_prelude.isNone())
                self.getSymbol(target_prelude).target_scope
            else
                ScopeId.none;
            const existing_idx = self.lookupInScopeDirect(sub_scope, ty_sym_id, NamespaceMask.TYPE_ONLY);
            if (!existing_idx.isNone()) {
                const sym_mut = self.getSymbolMut(existing_idx);
                if (sym_mut.flags.is_builtin) {
                    sym_mut.kind = if (!target_prelude.isNone()) .use_alias_sym else .type_alias_sym;
                    sym_mut.flags.is_imported = !target_prelude.isNone();
                    sym_mut.type_id = entry.type_id;
                    sym_mut.target_symbol = target_prelude;
                    sym_mut.target_scope = target_member_scope;
                }
                continue;
            }
            _ = try self.defineSymbol(.{
                .name = ty_sym_id,
                .name_text = interner.get(ty_sym_id),
                .kind = if (!target_prelude.isNone()) .use_alias_sym else .type_alias_sym,
                .namespace = .type_ns,
                .visibility = .public,
                .flags = .{ .is_pub = true, .is_used = true, .is_builtin = true, .is_imported = !target_prelude.isNone() },
                .scope_id = sub_scope,
                .type_id = entry.type_id,
                .target_symbol = target_prelude,
                .target_scope = target_member_scope,
            }, null);
        }
    }

    /// Resolves root namespace prefixes (`cx`, `core`), enforcing `E0218` on `core` when `!is_internal_core`.
    pub fn resolveRootNamespaceScope(
        self: *SymbolTable,
        interner: *StringInterner,
        caller_scope: ScopeId,
        root_lexeme: []const u8,
        root_span: Span,
        diagnostic_sink: ?*DiagnosticSink,
    ) !ScopeId {
        if (std.mem.eql(u8, root_lexeme, "cx")) {
            const cx_id = try interner.intern("cx");
            switch (self.lookupLexical(caller_scope, cx_id, NamespaceMask.VALUE_ONLY)) {
                .found => |sym_idx| {
                    const sym = self.getSymbol(sym_idx);
                    if (sym.scope_id != self.prelude_scope and !sym.flags.is_builtin and !sym.target_scope.isNone()) {
                        self.markSymbolUsed(sym_idx);
                        return sym.target_scope;
                    }
                },
                else => {},
            }
            return self.ensureCxRootScope(interner);
        } else if (std.mem.eql(u8, root_lexeme, "core")) {
            const core_id = try interner.intern("core");
            switch (self.lookupLexical(caller_scope, core_id, NamespaceMask.VALUE_ONLY)) {
                .found => |sym_idx| {
                    const sym = self.getSymbol(sym_idx);
                    if (sym.scope_id != self.prelude_scope and !sym.flags.is_builtin and !sym.target_scope.isNone()) {
                        self.markSymbolUsed(sym_idx);
                        return sym.target_scope;
                    }
                },
                else => {},
            }
            const cx_scope = try self.ensureCxRootScope(interner);
            if (!self.isCoreAllowedForFile(root_span.file_id)) {
                if (diagnostic_sink) |sink| {
                    try emitDirectCoreImportDiagnostic(sink, interner, root_span);
                }
                return .none;
            }
            return self.named_module_scopes.get(core_id.asInt()) orelse cx_scope;
        }
        return .none;
    }

    /// Populates `ScopeId` `0` (`.global_prelude`) with the 20 primitives, 6 runtime types, 12 Type Groups, and traits.
    fn populateGlobalPrelude(self: *SymbolTable, interner: *StringInterner) !void {
        self.prelude_scope = try self.scope_arena.allocScope(
            .global_prelude,
            .none,
            .NONE,
            .none,
            .{},
        );

        // [1] Register the 20 primitive types, 6 runtime structs, and 12 Constrained Type Groups (`DR-04`, `DR-22`):
        for (BUILTIN_TYPES_AND_GROUPS) |entry| {
            const sym_name = try interner.intern(entry.name);
            const is_runtime_struct = switch (entry.type_id) {
                .source_loc_ty,
                .fmt_spec_ty,
                .fmt_args_ty,
                .bencher_ty,
                .task_group_base_ty,
                .task_handle_base_ty,
                => true,
                else => false,
            };
            const is_linear_runtime = entry.type_id == .task_group_base_ty or entry.type_id == .task_handle_base_ty;
            const member_scope = if (is_runtime_struct)
                try self.scope_arena.allocScope(.nominal_type_scope, self.prelude_scope, .NONE, .none, .{})
            else
                ScopeId.none;
            const sym_idx = try self.appendSymbol(.{
                .name = sym_name,
                .name_text = interner.get(sym_name),
                .kind = if (entry.is_group)
                    .type_group_sym
                else if (is_runtime_struct)
                    .struct_sym
                else
                    .type_alias_sym,
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
                .target_scope = member_scope,
                .contract_flags = .{ .is_linear = is_linear_runtime },
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

        // [3] Register built-in traits (`Clone`, `Debug`, `Display`, `Eq`, `From`, `FromError`, `Ord`, etc.):
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
            const existing = self.getSymbol(existing_idx).*;

            // [1] Explicit `@overload` function and multi-arity `subscript` group handling (`DR-02` §1.4 & `SE-21`):
            if (record.namespace == .value_ns and record.kind == .fn_sym and
                (existing.kind == .fn_sym or existing.kind == .overload_group_sym))
            {
                const is_overload_family = (record.flags.is_overload and existing.flags.is_overload) or
                    (record.extra_flags.is_subscript and existing.extra_flags.is_subscript);
                if (is_overload_family) {
                    const new_fn_idx = try self.appendSymbol(record);
                    if (!record.def_id.isNone()) {
                        try self.def_to_symbol.put(self.allocator, record.def_id.asInt(), new_fn_idx);
                    }
                    const merged_vis: Visibility = @fromBackingInt(
                        @max(@backingInt(existing.visibility), @backingInt(record.visibility)),
                    );
                    if (existing.kind == .overload_group_sym) {
                        const ov_idx = existing.target_symbol.asInt();
                        try self.overload_sets.items[ov_idx].members.append(self.allocator, new_fn_idx);
                        self.getSymbolMut(existing_idx).visibility = merged_vis;
                        self.getSymbolMut(existing_idx).flags.is_pub = (merged_vis == .public);
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
                        .visibility = merged_vis,
                        .flags = .{
                            .is_pub = (merged_vis == .public),
                            .is_overload = true,
                        },
                        .extra_flags = .{
                            .is_subscript = record.extra_flags.is_subscript,
                        },
                        .scope_id = record.scope_id,
                        .decl_span = existing.decl_span,
                        .target_symbol = SymbolIndex.fromInt(ov_set_idx),
                    });
                    try self.scoped_map.put(self.allocator, key, group_sym_idx);
                    return new_fn_idx;
                }

                // Defer duplicate `E0408` until `@cfg` evaluation when either candidate carries `@cfg` (`SE-18`):
                if (existing.has_cfg_attr or record.has_cfg_attr) {
                    const cfg_fn_idx = try self.appendSymbol(record);
                    if (!record.def_id.isNone()) {
                        try self.def_to_symbol.put(self.allocator, record.def_id.asInt(), cfg_fn_idx);
                    }
                    return cfg_fn_idx;
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

            // [2.5] Distinct `test "…"` and `bench "…"` items sharing a description string do not collide:
            if ((record.extra_flags.is_test or record.extra_flags.is_bench) and
                (existing.extra_flags.is_test != record.extra_flags.is_test or
                    existing.extra_flags.is_bench != record.extra_flags.is_bench))
            {
                const distinct_tb_idx = try self.appendSymbol(record);
                if (!record.def_id.isNone()) {
                    try self.def_to_symbol.put(self.allocator, record.def_id.asInt(), distinct_tb_idx);
                }
                return distinct_tb_idx;
            }

            // [2.8] Defer duplicate `E0408` until `@cfg` pruning when either declaration carries `@cfg` (`SE-18`):
            if (existing.has_cfg_attr or record.has_cfg_attr) {
                const cfg_sym_idx = try self.appendSymbol(record);
                if (!record.def_id.isNone()) {
                    try self.def_to_symbol.put(self.allocator, record.def_id.asInt(), cfg_sym_idx);
                }
                return cfg_sym_idx;
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

    /// Looks up `name` inside `target_scope` from `caller_scope`, enforcing 4-tier visibility (`E0409`/`E0433`).
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

    /// Verifies whether `sym_idx` is visible from `caller_scope` under `ADR-22E`, unwrapping `use_alias_sym` targets.
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

        if (sym.flags.is_builtin) {
            return .{ .found = resolved_idx };
        }
        const decl_scope = self.scope_arena.getScope(sym.scope_id);
        const caller_pkg_id: PackageId = if (!caller_scope.isNone() and
            caller_scope.asInt() < self.scope_arena.countScopes())
            self.scope_arena.getScope(caller_scope).pkg_id
        else
            decl_scope.pkg_id;
        const is_alias_visible = sym.visibility == .public or sym.visibility.isVisibleFrom(
            decl_scope.enclosing_module,
            decl_scope.pkg_id,
            caller_scope,
            caller_pkg_id,
            &self.scope_arena,
        );
        if (!is_alias_visible) {
            return .{ .private_error = if (sym.kind == .use_alias_sym) sym_idx else resolved_idx };
        }
        if (resolved_idx != sym_idx) {
            const target_sym = self.getSymbol(resolved_idx);
            if (!target_sym.flags.is_builtin and @backingInt(sym.visibility) > @backingInt(target_sym.visibility)) {
                const target_decl_scope = self.scope_arena.getScope(target_sym.scope_id);
                if (!target_sym.visibility.isVisibleFrom(
                    target_decl_scope.enclosing_module,
                    target_decl_scope.pkg_id,
                    caller_scope,
                    caller_pkg_id,
                    &self.scope_arena,
                )) {
                    return .{ .private_error = resolved_idx };
                }
            }
        }
        return .{ .found = resolved_idx };
    }

    /// Finds the closest visible candidate identifier to `query_text` using bounded Damerau-Levenshtein distance.
    pub fn suggestClosestSymbol(
        self: *const SymbolTable,
        start_scope: ScopeId,
        query_text: []const u8,
        mask: NamespaceMask,
    ) ?[]const u8 {
        if (query_text.len < 2 or query_text.len > MAX_EDIT_DISTANCE_LEN) return null;
        if (mask.is_type and std.mem.eql(u8, query_text, "Numeric")) {
            return "Number";
        }
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
    const is_retired_numeric = std.mem.eql(u8, name_text, "Numeric");
    const effective_suggestion: ?[]const u8 = if (is_retired_numeric)
        (suggestion_opt orelse "Number")
    else
        suggestion_opt;

    const main_msg = if (is_retired_numeric)
        "the `Numeric` type group was retired in favor of `Number` (or `Integer` / `Float`)"
    else
        try std.fmt.allocPrint(
            arena_alloc,
            "unresolved symbol `{s}` in this scope",
            .{name_text},
        );
    const primary_label = if (is_retired_numeric)
        "retired type group `Numeric`; did you mean `Number`?"
    else if (effective_suggestion) |sug|
        try std.fmt.allocPrint(arena_alloc, "not found in this scope; did you mean `{s}`?", .{sug})
    else
        try std.fmt.allocPrint(arena_alloc, "cannot find `{s}` in this scope", .{name_text});

    const labels = [1]LabeledSpan{
        .{ .span = use_span, .label = primary_label, .style = .primary },
    };

    if (effective_suggestion) |sug| {
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
        if (is_retired_numeric) {
            const notes = [1][]const u8{
                "help: constrain generic numeric code with `Number`, `Integer`, `Signed`, `Unsigned`, or `Float`",
            };
            _ = try sink.emit(.{
                .code = .e0403_unresolved_symbol,
                .severity = .err,
                .primary_span = use_span,
                .message = main_msg,
                .labels = &labels,
                .notes = &notes,
                .suggestions = &fix,
            });
        } else {
            _ = try sink.emit(.{
                .code = .e0403_unresolved_symbol,
                .severity = .err,
                .primary_span = use_span,
                .message = main_msg,
                .labels = &labels,
                .suggestions = &fix,
            });
        }
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

/// Emits `E0409` (private) or `E0433` (`pub(super)` / `pub(pkg)`) pointing to the access site and declaration.
pub fn emitPrivateAccessDiagnostic(
    sink: *DiagnosticSink,
    sym: *const SymbolRecord,
    access_span: Span,
) !void {
    const arena_alloc = sink.arena.asAllocator();
    const diag_code: diagnostic.DiagnosticCode = switch (sym.visibility) {
        .private => .e0409_private_symbol_access,
        .pub_super, .pub_pkg, .public => .e0433_inaccessible_field_or_visibility,
    };
    const main_msg = switch (sym.visibility) {
        .private => try std.fmt.allocPrint(
            arena_alloc,
            "symbol `{s}` is private and cannot be accessed outside its defining module",
            .{sym.name_text},
        ),
        .pub_super => try std.fmt.allocPrint(
            arena_alloc,
            "symbol `{s}` is `pub(super)` and cannot be accessed outside its parent module hierarchy",
            .{sym.name_text},
        ),
        .pub_pkg => try std.fmt.allocPrint(
            arena_alloc,
            "symbol `{s}` is `pub(pkg)` and cannot be accessed outside its defining package",
            .{sym.name_text},
        ),
        .public => try std.fmt.allocPrint(
            arena_alloc,
            "symbol `{s}` is inaccessible from this scope",
            .{sym.name_text},
        ),
    };
    const primary_label = switch (sym.visibility) {
        .private => try std.fmt.allocPrint(arena_alloc, "`{s}` is private here", .{sym.name_text}),
        .pub_super => try std.fmt.allocPrint(arena_alloc, "`{s}` is `pub(super)` here", .{sym.name_text}),
        .pub_pkg => try std.fmt.allocPrint(arena_alloc, "`{s}` is `pub(pkg)` here", .{sym.name_text}),
        .public => try std.fmt.allocPrint(arena_alloc, "`{s}` is inaccessible here", .{sym.name_text}),
    };
    const secondary_label = switch (sym.visibility) {
        .private => try std.fmt.allocPrint(arena_alloc, "`{s}` is declared without `pub` here", .{sym.name_text}),
        .pub_super => try std.fmt.allocPrint(arena_alloc, "`{s}` is declared `pub(super)` here", .{sym.name_text}),
        .pub_pkg => try std.fmt.allocPrint(arena_alloc, "`{s}` is declared `pub(pkg)` here", .{sym.name_text}),
        .public => try std.fmt.allocPrint(arena_alloc, "`{s}` is declared here", .{sym.name_text}),
    };
    const help_note = switch (sym.visibility) {
        .private => "help: mark the declaration with `pub`, `pub(pkg)`, or `pub(super)` to widen its visibility",
        .pub_super => "help: widen visibility to `pub(pkg)` or `pub` to export across broader module boundaries",
        .pub_pkg, .public => "help: mark the declaration with `pub` to export it across package boundaries",
    };

    if (!sym.decl_span.file_id.isNone()) {
        const labels = [2]LabeledSpan{
            .{ .span = access_span, .label = primary_label, .style = .primary },
            .{ .span = sym.decl_span, .label = secondary_label, .style = .secondary },
        };
        const notes = [1][]const u8{help_note};
        _ = try sink.emit(.{
            .code = diag_code,
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
            .code = diag_code,
            .severity = .err,
            .primary_span = access_span,
            .message = main_msg,
            .labels = &labels,
        });
    }
}

/// Emits `E0433` (`e0433_inaccessible_field_or_visibility`) for inaccessible struct field construction or spread (`ADR-22E`).
pub fn emitFieldVisibilityDiagnostic(
    sink: *DiagnosticSink,
    sym: *const SymbolRecord,
    access_span: Span,
) !void {
    const arena_alloc = sink.arena.asAllocator();
    const vis_kw = sym.visibility.asKeywordSlice();
    const main_msg = try std.fmt.allocPrint(
        arena_alloc,
        "field `{s}` is `{s}` and cannot be initialized or accessed from this scope",
        .{ sym.name_text, vis_kw },
    );
    const primary_label = try std.fmt.allocPrint(
        arena_alloc,
        "inaccessible `{s}` field `{s}`",
        .{ vis_kw, sym.name_text },
    );
    if (!sym.decl_span.file_id.isNone()) {
        const secondary_label = try std.fmt.allocPrint(
            arena_alloc,
            "field `{s}` declared `{s}` here",
            .{ sym.name_text, vis_kw },
        );
        const labels = [2]LabeledSpan{
            .{ .span = access_span, .label = primary_label, .style = .primary },
            .{ .span = sym.decl_span, .label = secondary_label, .style = .secondary },
        };
        const notes = [1][]const u8{
            "help: construct this type through a `@constructor` / `init` function or widen the field visibility",
        };
        _ = try sink.emit(.{
            .code = .e0433_inaccessible_field_or_visibility,
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
            .code = .e0433_inaccessible_field_or_visibility,
            .severity = .err,
            .primary_span = access_span,
            .message = main_msg,
            .labels = &labels,
        });
    }
}

/// Emits `E0433` (`e0433_inaccessible_field_or_visibility`) when a `use` re-export escalates visibility (`ADR-22E`).
fn emitUseVisibilityEscalationDiagnostic(
    sink: *DiagnosticSink,
    sym: *const SymbolRecord,
    requested_vis: Visibility,
    allowed_vis: Visibility,
    reexport_span: Span,
) !void {
    const arena_alloc = sink.arena.asAllocator();
    const req_kw = requested_vis.asKeywordSlice();
    const allowed_kw = allowed_vis.asKeywordSlice();
    const main_msg = try std.fmt.allocPrint(
        arena_alloc,
        "cannot re-export `{s}` item `{s}` with wider visibility `{s}`",
        .{ allowed_kw, sym.name_text, req_kw },
    );
    const primary_label = try std.fmt.allocPrint(
        arena_alloc,
        "`{s} use` escalates visibility beyond `{s}`",
        .{ req_kw, allowed_kw },
    );
    if (!sym.decl_span.file_id.isNone()) {
        const secondary_label = try std.fmt.allocPrint(
            arena_alloc,
            "`{s}` declared `{s}` here",
            .{ sym.name_text, allowed_kw },
        );
        const labels = [2]LabeledSpan{
            .{ .span = reexport_span, .label = primary_label, .style = .primary },
            .{ .span = sym.decl_span, .label = secondary_label, .style = .secondary },
        };
        _ = try sink.emit(.{
            .code = .e0433_inaccessible_field_or_visibility,
            .severity = .err,
            .primary_span = reexport_span,
            .message = main_msg,
            .labels = &labels,
        });
    } else {
        const labels = [1]LabeledSpan{
            .{ .span = reexport_span, .label = primary_label, .style = .primary },
        };
        _ = try sink.emit(.{
            .code = .e0433_inaccessible_field_or_visibility,
            .severity = .err,
            .primary_span = reexport_span,
            .message = main_msg,
            .labels = &labels,
        });
    }
}

/// Emits `E0218` (`e0218_direct_core_import_forbidden`) with a machine-applicable `"cx"` replacement fix.
pub fn emitDirectCoreImportDiagnostic(
    sink: *DiagnosticSink,
    interner: *StringInterner,
    core_span: Span,
) !void {
    const cx_id = try interner.intern("cx");
    const edit = [1]TextEdit{.{
        .file_id = core_span.file_id,
        .start_byte = core_span.start_byte,
        .end_byte = core_span.end_byte,
        .replacement_id = cx_id,
    }};
    const fix = [1]SuggestedFix{.{
        .message = "replace `core` with the unified `cx` standard library root",
        .applicability = .machine_applicable,
        .priority = .syntax_canonicalization,
        .edits = &edit,
    }};
    const labels = [1]LabeledSpan{.{
        .span = core_span,
        .label = "direct `core` root access is reserved for `--internal-core`",
        .style = .primary,
    }};
    const notes = [1][]const u8{
        "help: import standard library and kernel facilities through `cx.*` instead of `core.*`",
    };
    _ = try sink.emit(.{
        .code = .e0218_direct_core_import_forbidden,
        .severity = .err,
        .primary_span = core_span,
        .message = "direct access to internal `core` root is forbidden outside `--internal-core`",
        .labels = &labels,
        .notes = &notes,
        .suggestions = &fix,
    });
}

// --------- Module Item Collection & `use` Resolution ----------

/// Combined item modifier, `@derive`, `@attribute_schema`, and Phase 6/7.6 contract metadata extracted from CST headers.
pub const ItemHeaderMetadata = struct {
    /// Four-tier visibility (`private`, `pub(super)`, `pub(pkg)`, `pub`) extracted from `.visibility_modifier`.
    visibility: Visibility = .private,
    /// Extracted item visibility, modifier, and attribute flags.
    flags: SymbolFlags = .{},
    /// Phase 7.6 `@constructor`, `@builder`, `@builder_item`, `has_repr_int`, and item kind flags (`DR-22`).
    extra_flags: DeclExtraFlags = .{},
    /// Parsed `@derive(Eq, Hash, Debug, Clone, From, Copy)` bitmask.
    derive_mask: DeriveMask = .{},
    /// Parsed `@attribute_schema(targets: …)` target bitmask.
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
    /// Token of an explicit integer argument inside `@repr(Int)` (`TokenIndex.none` if absent).
    repr_int_token: TokenIndex = .none,
    /// `true` if `@cfg(…)` appears on this item header (`SE-18`).
    has_cfg_attr: bool = false,
    /// `true` if `@trusted` appears on this item or `extern` block header (`DR-10` §2.3).
    is_trusted: bool = false,
    /// `true` if `@thread_local` appears on this `extern static` item header (`DR-10`).
    is_thread_local: bool = false,
    /// Inline decoded library name buffer when `@link_lib("…")` is present.
    link_lib_buf: [256]u8 = undefined,
    /// Valid byte length inside `link_lib_buf`.
    link_lib_len: u16 = 0,
    /// Inline decoded Wasm import module buffer when `@wasm_import("mod", "name")` is present.
    wasm_import_mod_buf: [256]u8 = undefined,
    /// Valid byte length inside `wasm_import_mod_buf`.
    wasm_import_mod_len: u16 = 0,
    /// Inline decoded Wasm import symbol buffer when `@wasm_import("mod", "name")` is present.
    wasm_import_name_buf: [256]u8 = undefined,
    /// Valid byte length inside `wasm_import_name_buf`.
    wasm_import_name_len: u16 = 0,
    /// Inline decoded Wasm export symbol buffer when `@wasm_export("name")` is present.
    wasm_export_buf: [256]u8 = undefined,
    /// Valid byte length inside `wasm_export_buf`.
    wasm_export_len: u16 = 0,

    /// Returns the decoded `@link_section` byte slice.
    pub inline fn asLinkSectionSlice(self: *const ItemHeaderMetadata) []const u8 {
        return self.link_section_buf[0..self.link_section_len];
    }

    /// Returns the decoded `@link_name` byte slice.
    pub inline fn asLinkNameSlice(self: *const ItemHeaderMetadata) []const u8 {
        return self.link_name_buf[0..self.link_name_len];
    }

    /// Returns the decoded `@link_lib` byte slice.
    pub inline fn asLinkLibSlice(self: *const ItemHeaderMetadata) []const u8 {
        return self.link_lib_buf[0..self.link_lib_len];
    }

    /// Returns the decoded `@wasm_import` module name byte slice.
    pub inline fn asWasmImportModSlice(self: *const ItemHeaderMetadata) []const u8 {
        return self.wasm_import_mod_buf[0..self.wasm_import_mod_len];
    }

    /// Returns the decoded `@wasm_import` symbol name byte slice.
    pub inline fn asWasmImportNameSlice(self: *const ItemHeaderMetadata) []const u8 {
        return self.wasm_import_name_buf[0..self.wasm_import_name_len];
    }

    /// Returns the decoded `@wasm_export` symbol name byte slice.
    pub inline fn asWasmExportSlice(self: *const ItemHeaderMetadata) []const u8 {
        return self.wasm_export_buf[0..self.wasm_export_len];
    }
};

/// Extracts 4-tier `Visibility` (`pub`, `pub(pkg)`, `pub(super)`) from a `.visibility_modifier` CST node (`ADR-22E`).
pub fn extractVisibilityFromCst(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    vis_cst: CstNodeIndex,
) Visibility {
    if (vis_cst.isNone() or vis_cst.asInt() >= cst_arena.countNodes()) return .private;
    const root_idx: usize = vis_cst.asInt();
    const root_node = cst_arena.getNode(vis_cst);
    if (root_node.subtree_size <= 1) return .public;
    const end_idx: usize = @min(
        root_idx + @as(usize, root_node.subtree_size),
        cst_arena.countNodes(),
    );
    var cur: usize = root_idx + 1;
    while (cur < end_idx) : (cur += 1) {
        const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
        if (leaf.subtree_size > 1 or leaf.token.isNone() or leaf.token.asInt() >= token_buffer.countTokens()) {
            continue;
        }
        const lexeme = extractTokenSlice(source, token_buffer, leaf.token);
        if (std.mem.eql(u8, lexeme, "pkg")) return .pub_pkg;
        if (std.mem.eql(u8, lexeme, "super")) return .pub_super;
    }
    return .public;
}

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
            std.mem.startsWith(u8, seg, ".iplt") or
            std.mem.startsWith(u8, seg, ".rela.iplt") or
            std.mem.startsWith(u8, seg, ".got") or
            std.mem.startsWith(u8, seg, ".plt") or
            std.mem.eql(u8, seg, "start") or
            std.mem.indexOf(u8, seg, "__la_symbol_ptr") != null or
            std.mem.indexOf(u8, seg, "__nl_symbol_ptr") != null or
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

/// Strips outer quotes (`"…"`, `b"…"`, or `r#"…"#`) and decodes standard `\xNN` / `\u{…}` escapes into `out_buf`.
fn unquoteAttrStringLexeme(lexeme: []const u8, out_buf: *[256]u8) []const u8 {
    if (std.mem.startsWith(u8, lexeme, "br") or std.mem.startsWith(u8, lexeme, "r")) {
        var hash_count: usize = 0;
        var idx: usize = if (std.mem.startsWith(u8, lexeme, "br")) 2 else 1;
        while (idx < lexeme.len and lexeme[idx] == '#') : (idx += 1) {
            hash_count += 1;
        }
        if (idx < lexeme.len and lexeme[idx] == '"' and lexeme.len >= idx + 2 + hash_count) {
            return lexeme[idx + 1 .. lexeme.len - 1 - hash_count];
        }
    }
    const inner = if (lexeme.len >= 3 and lexeme[0] == 'b' and lexeme[1] == '"' and lexeme[lexeme.len - 1] == '"')
        lexeme[2 .. lexeme.len - 1]
    else if (lexeme.len >= 2 and lexeme[0] == '"' and lexeme[lexeme.len - 1] == '"')
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
        if (!isIdentifierToken(arg_kind) and arg_kind != .string_lit and arg_kind != .byte_string_lit) continue;
        const raw_lex = extractTokenSlice(source, token_buffer, arg_leaf.token);
        var unquote_buf: [256]u8 = undefined;
        const ident_lex = if (arg_kind == .string_lit or arg_kind == .byte_string_lit)
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

/// Extracts `@repr(C | c | packed | align: N)` metadata inside `[arg_start .. attr_end)`.
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
        if (arg_kind == .eq or arg_kind == .colon or arg_kind == .lparen or arg_kind == .rparen) continue;
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
            meta.extra_flags.has_repr_int = true;
            if (meta.repr_int_token.isNone()) meta.repr_int_token = arg_leaf.token;
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
            const name_kind = token_buffer.getToken(name_leaf.token).kind;
            if (name_kind == .string_lit or name_kind == .byte_string_lit) {
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
            if (next_kind == .dot and
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
            const sec_kind = token_buffer.getToken(sec_leaf.token).kind;
            if (sec_kind == .string_lit or sec_kind == .byte_string_lit) {
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

/// Emits `E0225` (`e0225_retired_noalloc_attribute`) with a machine-applicable `@no_alloc` fix if not yet emitted.
fn emitRetiredNoallocAttrDiagnostic(
    sink: *DiagnosticSink,
    interner: ?*StringInterner,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    at_token: TokenIndex,
    name_token: TokenIndex,
) !void {
    const name_span = token_buffer.getTokenSpan(file_id, name_token);
    const full_span: Span = if (!at_token.isNone() and at_token.asInt() < token_buffer.countTokens()) blk: {
        const at_span = token_buffer.getTokenSpan(file_id, at_token);
        if (at_span.file_id == name_span.file_id and at_span.start_byte <= name_span.start_byte) {
            break :blk .{
                .file_id = name_span.file_id,
                .start_byte = at_span.start_byte,
                .end_byte = name_span.end_byte,
            };
        }
        break :blk name_span;
    } else name_span;

    for (sink.asSlice()) |existing_diag| {
        if (existing_diag.code == .e0225_retired_noalloc_attribute and
            existing_diag.primary_span.file_id == full_span.file_id and
            existing_diag.primary_span.start_byte <= full_span.end_byte and
            full_span.start_byte <= existing_diag.primary_span.end_byte)
        {
            return;
        }
    }

    const labels = [1]LabeledSpan{
        .{
            .span = full_span,
            .label = "retired `@noalloc` spelling; write `@no_alloc`",
            .style = .primary,
        },
    };
    if (interner) |str_interner| {
        const replacement_str = if (full_span.start_byte < name_span.start_byte) "@no_alloc" else "no_alloc";
        const rep_id = try str_interner.intern(replacement_str);
        const edits = [1]TextEdit{.{
            .file_id = full_span.file_id,
            .start_byte = full_span.start_byte,
            .end_byte = full_span.end_byte,
            .replacement_id = rep_id,
        }};
        const fixes = [1]SuggestedFix{.{
            .message = "replace with canonical `@no_alloc`",
            .applicability = .machine_applicable,
            .priority = .syntax_canonicalization,
            .edits = &edits,
        }};
        _ = try sink.emit(.{
            .code = .e0225_retired_noalloc_attribute,
            .severity = .err,
            .primary_span = full_span,
            .message = "attribute `@noalloc` has been retired in favor of `@no_alloc`",
            .labels = &labels,
            .suggestions = &fixes,
        });
    } else {
        _ = try sink.emit(.{
            .code = .e0225_retired_noalloc_attribute,
            .severity = .err,
            .primary_span = full_span,
            .message = "attribute `@noalloc` has been retired in favor of `@no_alloc`",
            .labels = &labels,
        });
    }
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
    return extractItemHeaderMetadataWithInterner(
        source,
        file_id,
        token_buffer,
        cst_arena,
        item_cst,
        main_token,
        null,
        diagnostic_sink,
    );
}

/// Extracts item header metadata with optional `StringInterner` for machine-applicable attribute migration fixes.
fn extractItemHeaderMetadataWithInterner(
    source: []const u8,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst: CstNodeIndex,
    main_token: TokenIndex,
    interner: ?*StringInterner,
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
            meta.visibility = extractVisibilityFromCst(
                source,
                token_buffer,
                cst_arena,
                CstNodeIndex.fromInt(@intCast(cursor)),
            );
            meta.flags.is_pub = (meta.visibility == .public);
            if (node.subtree_size > 1) {
                cursor += @as(usize, node.subtree_size) - 1;
            }
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
            var at_tok: TokenIndex = .none;
            var attr_cur = cursor + 1;
            while (attr_cur < attr_end) : (attr_cur += 1) {
                const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(attr_cur)));
                if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                    leaf.token.asInt() < token_buffer.countTokens())
                {
                    const tok_kind = token_buffer.getToken(leaf.token).kind;
                    if (tok_kind == .at and at_tok.isNone()) {
                        at_tok = leaf.token;
                        continue;
                    }
                    if (isIdentifierToken(tok_kind) or tok_kind == .kw_pub) {
                        const attr_name = extractTokenSlice(source, token_buffer, leaf.token);
                        if (std.mem.eql(u8, attr_name, "cfg")) {
                            meta.has_cfg_attr = true;
                        }
                        if (HEADER_ATTR_MAP.get(attr_name)) |attr_kind| {
                            switch (attr_kind) {
                                .overload => meta.flags.is_overload = true,
                                .must_use => meta.flags.is_must_use = true,
                                .from => meta.flags.is_from_error = true,
                                .soa => meta.flags.is_soa_annotated = true,
                                .extern_attr => meta.flags.is_extern = true,
                                .builder => meta.extra_flags.is_builder = true,
                                .builder_item => meta.extra_flags.is_builder_item = true,
                                .constructor => meta.extra_flags.is_constructor = true,
                                .no_alloc => meta.contract_flags.is_no_alloc = true,
                                .noalloc => {
                                    meta.contract_flags.is_no_alloc = true;
                                    if (diagnostic_sink) |sink| {
                                        try emitRetiredNoallocAttrDiagnostic(
                                            sink,
                                            interner,
                                            file_id,
                                            token_buffer,
                                            at_tok,
                                            leaf.token,
                                        );
                                    }
                                },
                                .no_panic => meta.contract_flags.is_no_panic = true,
                                .no_block => meta.contract_flags.is_no_block = true,
                                .not_send => meta.extra_flags.is_not_send = true,
                                .not_sync => meta.extra_flags.is_not_sync = true,
                                .linear => meta.contract_flags.is_linear = true,
                                .zero_pad => meta.contract_flags.is_zero_pad = true,
                                .secret => meta.contract_flags.is_secret = true,
                                .export_attr => meta.contract_flags.is_export = true,
                                .local => meta.contract_flags.is_local_only = true,
                                .cache_aligned => meta.contract_flags.is_cache_aligned = true,
                                .packed_attr => meta.contract_flags.is_packed = true,
                                .trusted => {
                                    meta.is_trusted = true;
                                    meta.extra_flags.is_trusted_ffi = true;
                                },
                                .thread_local => {
                                    meta.is_thread_local = true;
                                    meta.extra_flags.is_thread_local = true;
                                },
                                .link_lib => extractSingleStringAttrIntoBuf(
                                    source,
                                    token_buffer,
                                    cst_arena,
                                    attr_cur + 1,
                                    attr_end,
                                    &meta.link_lib_buf,
                                    &meta.link_lib_len,
                                ),
                                .wasm_export => extractSingleStringAttrIntoBuf(
                                    source,
                                    token_buffer,
                                    cst_arena,
                                    attr_cur + 1,
                                    attr_end,
                                    &meta.wasm_export_buf,
                                    &meta.wasm_export_len,
                                ),
                                .wasm_import => extractWasmImportAttr(
                                    source,
                                    token_buffer,
                                    cst_arena,
                                    attr_cur + 1,
                                    attr_end,
                                    &meta,
                                ),
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
    if (!main_token.isNone() and main_token.asInt() < token_buffer.countTokens()) {
        const main_kind = token_buffer.getToken(main_token).kind;
        if (main_kind == .kw_subscript or main_kind == .string_lit) return main_token;
    }
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
        if ((node.kind == .visibility_modifier or node.kind == .attribute or node.kind == .type_params) and
            node.subtree_size > 1)
        {
            cursor += @as(usize, node.subtree_size) - 1;
            continue;
        }
        const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
        if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
        if (!main_token.isNone() and node.token.asInt() <= main_token.asInt()) continue;
        if (node.token.asInt() >= token_buffer.countTokens()) continue;

        const tok_kind = token_buffer.getToken(node.token).kind;
        if (tok_kind == .lbrace or tok_kind == .semi or tok_kind == .eq or
            tok_kind == .colon or tok_kind == .lparen or tok_kind == .lbracket)
        {
            break;
        }
        if (isIdentifierToken(tok_kind) or
            (tok_kind == .kw_async and !main_token.isNone() and
                main_token.asInt() < token_buffer.countTokens() and
                token_buffer.getToken(main_token).kind == .kw_mod))
        {
            return node.token;
        }
    }
    return main_token;
}

/// Extracts `FnParamSpec` zone (`/`, `*`), `var`, `@builder`, `@caller_location()`, and `...` metadata from `item_cst`.
pub fn extractFnParamSpecsFromItemCst(
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    file_id: FileId,
    owner_def_id: DefId,
    item_cst: CstNodeIndex,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
) !ExtractedFnParams {
    var specs: std.ArrayListUnmanaged(FnParamSpec) = .empty;
    errdefer specs.deinit(allocator);
    var is_variadic = false;

    if (item_cst.isNone() or item_cst.asInt() >= cst_arena.countNodes()) {
        return .{ .specs = try specs.toOwnedSlice(allocator), .is_variadic = false };
    }
    const start_idx: usize = item_cst.asInt();
    const root_rec = cst_arena.getNode(item_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (node.kind == .block or node.kind == .fn_expr_body or
            node.kind == .where_clause or node.kind == .subscript_arm)
        {
            break;
        }
        if ((node.kind == .attribute or node.kind == .type_params or node.kind == .visibility_modifier) and
            node.subtree_size > 1)
        {
            cursor += @as(usize, node.subtree_size) - 1;
            continue;
        }
        if (node.kind != .param_list) continue;

        const plist_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), end_idx);
        var is_in_keyword_only_zone = false;
        var child_cur: usize = cursor + 1;
        while (child_cur < plist_end) {
            const child = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_cur)));
            const child_end = @min(child_cur + @max(@as(usize, child.subtree_size), 1), plist_end);

            if (child.kind == .param_zone_sep) {
                var sep_cur = child_cur;
                while (sep_cur < child_end) : (sep_cur += 1) {
                    const sep_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sep_cur)));
                    if (sep_leaf.subtree_size > 1 or sep_leaf.token.isNone() or
                        sep_leaf.token.asInt() >= token_buffer.countTokens())
                    {
                        continue;
                    }
                    const sep_kind = token_buffer.getToken(sep_leaf.token).kind;
                    if (sep_kind == .slash) {
                        for (specs.items) |*prev_spec| {
                            if (!std.mem.eql(u8, prev_spec.name_text, "self")) {
                                prev_spec.is_positional_only = true;
                            }
                        }
                    } else if (sep_kind == .star) {
                        is_in_keyword_only_zone = true;
                    }
                }
                child_cur = child_end;
                continue;
            }

            const is_direct_dotdotdot = child.subtree_size <= 1 and !child.token.isNone() and
                child.token.asInt() < token_buffer.countTokens() and
                token_buffer.getToken(child.token).kind == .dotdotdot;
            if (child.kind == .variadic_param or is_direct_dotdotdot) {
                is_variadic = true;
                try specs.append(allocator, .{
                    .decl_file_id = file_id,
                    .owner_def_id = owner_def_id,
                    .is_variadic = true,
                });
                child_cur = child_end;
                continue;
            }

            if (child.kind == .fn_param) {
                var name_tok: TokenIndex = .none;
                var is_self_param = false;
                var is_local_var = false;
                var is_builder_param = false;
                var colon_pos: ?usize = null;

                var param_cur = child_cur + 1;
                while (param_cur < child_end) : (param_cur += 1) {
                    const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(param_cur)));
                    if (sub.kind == .attribute) {
                        const attr_end = @min(param_cur + @max(@as(usize, sub.subtree_size), 1), child_end);
                        if (hasBuilderAttributeInCstRange(source, token_buffer, cst_arena, param_cur, attr_end)) {
                            is_builder_param = true;
                        }
                        if (sub.subtree_size > 1) param_cur += @as(usize, sub.subtree_size) - 1;
                        continue;
                    }
                    const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
                    if (!is_leaf or sub.flags.is_missing_or_injected or sub.token.isNone() or
                        sub.token.asInt() >= token_buffer.countTokens())
                    {
                        continue;
                    }
                    const tok_kind = token_buffer.getToken(sub.token).kind;
                    if (tok_kind == .colon) {
                        colon_pos = param_cur;
                        break;
                    }
                    if (tok_kind == .kw_var) {
                        is_local_var = true;
                    } else if (name_tok.isNone() and
                        (isIdentifierToken(tok_kind) or tok_kind == .kw_self_val or tok_kind == .underscore))
                    {
                        name_tok = sub.token;
                        if (tok_kind == .kw_self_val) is_self_param = true;
                    }
                }

                var eq_pos: ?usize = null;
                var eq_scan = if (colon_pos) |col_idx| col_idx + 1 else child_cur + 1;
                while (eq_scan < child_end) {
                    const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(eq_scan)));
                    const step: usize = @max(@as(usize, sub.subtree_size), 1);
                    if (sub.kind == .closure_type) {
                        if (hasBuilderAttributeInCstRange(source, token_buffer, cst_arena, eq_scan, eq_scan + step)) {
                            is_builder_param = true;
                        }
                    } else if (step == 1 and !sub.flags.is_bracketed and !sub.flags.is_missing_or_injected and
                        !sub.token.isNone() and sub.token.asInt() < token_buffer.countTokens() and
                        token_buffer.getToken(sub.token).kind == .eq)
                    {
                        eq_pos = eq_scan;
                        break;
                    }
                    eq_scan += step;
                }

                var is_caller_location_default = false;
                if (eq_pos) |eq_idx| {
                    var has_seen_at = false;
                    var def_cur = eq_idx + 1;
                    while (def_cur < child_end) : (def_cur += 1) {
                        const def_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(def_cur)));
                        if (def_leaf.subtree_size > 1 or def_leaf.token.isNone() or
                            def_leaf.token.asInt() >= token_buffer.countTokens())
                        {
                            continue;
                        }
                        const def_kind = token_buffer.getToken(def_leaf.token).kind;
                        if (def_kind == .at) {
                            has_seen_at = true;
                        } else if (has_seen_at and isIdentifierToken(def_kind)) {
                            if (std.mem.eql(u8, extractTokenSlice(source, token_buffer, def_leaf.token), "caller_location")) {
                                is_caller_location_default = true;
                            }
                            break;
                        } else {
                            has_seen_at = false;
                        }
                    }
                }

                const param_lex = if (!name_tok.isNone())
                    extractTokenSlice(source, token_buffer, name_tok)
                else
                    "";
                const param_sym: SymbolId = if (param_lex.len > 0)
                    try interner.intern(param_lex)
                else
                    .empty;

                try specs.append(allocator, .{
                    .name = param_sym,
                    .name_text = if (param_sym != .empty) interner.get(param_sym) else "",
                    .has_default = (eq_pos != null),
                    .decl_file_id = file_id,
                    .owner_def_id = owner_def_id,
                    .is_keyword_only = (!is_self_param and is_in_keyword_only_zone),
                    .is_local_var = is_local_var,
                    .is_builder = is_builder_param,
                    .is_caller_location_default = is_caller_location_default,
                });
                child_cur = child_end;
                continue;
            }
            child_cur += 1;
        }
        break;
    }

    return .{
        .specs = try specs.toOwnedSlice(allocator),
        .is_variadic = is_variadic,
    };
}

/// Extracts `GenericParamSpec` entries (including `SE-10` generic defaults) from `.type_params` inside `item_cst`.
pub fn extractGenericParamSpecsFromItemCst(
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    item_cst: CstNodeIndex,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
) ![]GenericParamSpec {
    var specs: std.ArrayListUnmanaged(GenericParamSpec) = .empty;
    errdefer specs.deinit(allocator);

    if (item_cst.isNone() or item_cst.asInt() >= cst_arena.countNodes()) {
        return specs.toOwnedSlice(allocator);
    }
    const start_idx: usize = item_cst.asInt();
    const root_rec = cst_arena.getNode(item_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (node.kind == .param_list or node.kind == .where_clause or
            node.kind == .block or node.kind == .fn_expr_body or node.kind == .subscript_arm)
        {
            break;
        }
        if ((node.kind == .attribute or node.kind == .visibility_modifier) and node.subtree_size > 1) {
            cursor += @max(@as(usize, node.subtree_size), 1);
            continue;
        }
        if (node.kind == .type_param) {
            const tp_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), end_idx);
            var is_const_param = false;
            var name_tok: TokenIndex = .none;
            var has_default = false;
            var has_explicit_bound = false;
            var bracket_depth: u32 = 0;
            var paren_depth: u32 = 0;
            var default_hasher = std.hash.Wyhash.init(0x5345_3130_4445_4654);
            var default_leaf_count: u32 = 0;
            var single_default_tok: TokenIndex = .none;

            var tp_cur = cursor + 1;
            while (tp_cur < tp_end) : (tp_cur += 1) {
                const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(tp_cur)));
                const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
                if (!is_leaf or sub.flags.is_missing_or_injected or sub.token.isNone() or
                    sub.token.asInt() >= token_buffer.countTokens())
                {
                    continue;
                }
                const tok_kind = token_buffer.getToken(sub.token).kind;
                if (!has_default) {
                    if (tok_kind == .lbracket) {
                        bracket_depth += 1;
                    } else if (tok_kind == .rbracket) {
                        bracket_depth -|= 1;
                    } else if (tok_kind == .lparen) {
                        paren_depth += 1;
                    } else if (tok_kind == .rparen) {
                        paren_depth -|= 1;
                    } else if (tok_kind == .eq and bracket_depth == 0 and paren_depth == 0) {
                        has_default = true;
                        continue;
                    } else if (bracket_depth == 0 and paren_depth == 0) {
                        if (tok_kind == .kw_const) {
                            is_const_param = true;
                        } else if (tok_kind == .colon) {
                            has_explicit_bound = true;
                        } else if (name_tok.isNone() and isIdentifierToken(tok_kind)) {
                            name_tok = sub.token;
                        }
                    }
                } else {
                    const kind_tag: u8 = @backingInt(tok_kind);
                    default_hasher.update(&.{kind_tag});
                    const def_lex = extractTokenSlice(source, token_buffer, sub.token);
                    default_hasher.update(def_lex);
                    default_hasher.update(&.{0xFF});
                    default_leaf_count += 1;
                    if (default_leaf_count == 1) single_default_tok = sub.token;
                }
            }

            if (!name_tok.isNone()) {
                const name_lex = extractTokenSlice(source, token_buffer, name_tok);
                if (name_lex.len > 0) {
                    const name_sym = try interner.intern(name_lex);
                    var default_ty: TypeId = .err_ty;
                    var default_ty_sym: SymbolId = .empty;
                    if (has_default and !is_const_param and default_leaf_count == 1 and !single_default_tok.isNone()) {
                        const single_lex = extractTokenSlice(source, token_buffer, single_default_tok);
                        const single_kind = token_buffer.getToken(single_default_tok).kind;
                        if (BUILTIN_TYPE_AND_GROUP_MAP.get(single_lex)) |builtin_ty| {
                            default_ty = builtin_ty;
                        } else if (isIdentifierToken(single_kind)) {
                            default_ty_sym = try interner.intern(single_lex);
                        }
                    }
                    try specs.append(allocator, .{
                        .name = name_sym,
                        .name_text = interner.get(name_sym),
                        .is_const = is_const_param,
                        .has_default = has_default,
                        .has_explicit_bound = has_explicit_bound,
                        .default_type_id = default_ty,
                        .default_type_sym = default_ty_sym,
                        .default_syntax_hash = if (has_default) default_hasher.final() else 0,
                    });
                }
            }
            cursor = tp_end;
            continue;
        }
        cursor += 1;
    }

    return specs.toOwnedSlice(allocator);
}

/// Parses a `@cfg` unsigned integer literal (`32`, `64`, `16_u16`) without heap allocation.
fn extractCfgUnsignedInt(lexeme: []const u8) ?u64 {
    if (lexeme.len == 0) return null;
    var accum: u64 = 0;
    var has_digit = false;
    var i: usize = 0;
    while (i < lexeme.len) : (i += 1) {
        const byte_ch = lexeme[i];
        if (byte_ch == '_') continue;
        if (byte_ch == 'u' or byte_ch == 'i') break;
        if (byte_ch < '0' or byte_ch > '9') return null;
        has_digit = true;
        accum = std.math.mul(u64, accum, 10) catch return null;
        accum = std.math.add(u64, accum, byte_ch - '0') catch return null;
    }
    return if (has_digit) accum else null;
}

/// Emits an `E0435` (`e0435_invalid_cfg_predicate`) diagnostic when `diagnostic_sink` is active.
fn emitCfgPredicateDiagnostic(
    diagnostic_sink: ?*DiagnosticSink,
    span: Span,
    message: []const u8,
    primary_label: []const u8,
) !void {
    const sink = diagnostic_sink orelse return;
    const arena_alloc = sink.arena.asAllocator();
    const msg_owned = try arena_alloc.dupe(u8, message);
    const label_owned = try arena_alloc.dupe(u8, primary_label);
    const labels = [1]LabeledSpan{
        .{ .span = span, .label = label_owned, .style = .primary },
    };
    _ = try sink.emit(.{
        .code = .e0435_invalid_cfg_predicate,
        .severity = .err,
        .primary_span = span,
        .message = msg_owned,
        .labels = &labels,
    });
}

/// Validates `feat_name` against declared package features (`E0435`) and returns whether it is enabled.
fn evaluateCfgFeatureFlag(
    cfg_env: *const CfgEnv,
    feat_name: []const u8,
    span: Span,
    has_err: *bool,
    diagnostic_sink: ?*DiagnosticSink,
) !bool {
    var is_enabled = false;
    for (cfg_env.enabled_features) |enabled_feat| {
        if (std.mem.eql(u8, enabled_feat, feat_name)) {
            is_enabled = true;
            break;
        }
    }
    if (!is_enabled) {
        if (cfg_env.sym_table_features) |st_features| {
            if (st_features.isPackageFeatureEnabled(cfg_env.owner_pkg_id, feat_name)) {
                is_enabled = true;
            }
        }
    }

    var has_manifest = false;
    var is_declared = false;
    if (cfg_env.declared_features) |declared_list| {
        has_manifest = true;
        for (declared_list) |decl_feat| {
            if (std.mem.eql(u8, decl_feat, feat_name)) {
                is_declared = true;
                break;
            }
        }
    } else if (cfg_env.sym_table_features) |st_features| {
        if (st_features.has_package_feature_manifest.contains(cfg_env.owner_pkg_id)) {
            has_manifest = true;
            is_declared = st_features.isPackageFeatureDeclared(cfg_env.owner_pkg_id, feat_name);
        }
    }

    if (has_manifest and !is_declared and !has_err.*) {
        has_err.* = true;
        if (diagnostic_sink) |sink| {
            const arena_alloc = sink.arena.asAllocator();
            const msg_owned = try std.fmt.allocPrint(
                arena_alloc,
                "undeclared feature `{s}` in `@cfg(…)` predicate",
                .{feat_name},
            );
            const labels = [1]LabeledSpan{
                .{
                    .span = span,
                    .label = "feature is not declared in package `[features]`",
                    .style = .primary,
                },
            };
            _ = try sink.emit(.{
                .code = DiagnosticCode.e0435_unknown_cfg_feature,
                .severity = .err,
                .primary_span = span,
                .message = msg_owned,
                .labels = &labels,
            });
        }
    }
    return is_enabled;
}

/// Evaluates a single `.attribute` CST range `[attr_start .. attr_end)` if it is `@cfg(…)`.
fn evaluateSingleCfgAttrRangeWithEnv(
    cfg_env: *const CfgEnv,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    attr_start: usize,
    attr_end: usize,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!bool {
    var tokens: [128]TokenIndex = undefined;
    var tok_count: usize = 0;
    var attr_name_tok: TokenIndex = .none;
    var has_seen_lparen = false;
    var paren_depth: u32 = 0;

    var cur = attr_start + 1;
    while (cur < attr_end) : (cur += 1) {
        const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
        if (leaf.subtree_size > 1 or leaf.flags.is_missing_or_injected or
            leaf.token.isNone() or leaf.token.asInt() >= token_buffer.countTokens())
        {
            continue;
        }
        const tok = leaf.token;
        const kind = token_buffer.getToken(tok).kind;
        if (kind == .at) continue;
        if (attr_name_tok.isNone()) {
            attr_name_tok = tok;
            if (!std.mem.eql(u8, extractTokenSlice(source, token_buffer, tok), "cfg")) return true;
            continue;
        }
        if (!has_seen_lparen) {
            if (kind == .lparen) {
                has_seen_lparen = true;
                paren_depth = 1;
            }
            continue;
        }
        if (kind == .lparen) {
            paren_depth += 1;
        } else if (kind == .rparen) {
            if (paren_depth == 1) {
                paren_depth = 0;
                break;
            }
            if (paren_depth > 0) paren_depth -= 1;
        }
        if (tok_count < tokens.len) {
            tokens[tok_count] = tok;
            tok_count += 1;
        }
    }

    const attr_span = if (!attr_name_tok.isNone())
        token_buffer.getTokenSpan(file_id, attr_name_tok)
    else
        Span.init(file_id, 0, 0);

    if (!has_seen_lparen or tok_count == 0) {
        try emitCfgPredicateDiagnostic(
            diagnostic_sink,
            attr_span,
            "`@cfg(…)` requires a non-empty boolean target or feature predicate",
            "expected `@cfg(…)` boolean predicate",
        );
        return true;
    }

    var pos: usize = 0;
    var has_cfg_err = false;
    const result = try parseCfgOrExprWithEnv(
        cfg_env,
        file_id,
        source,
        token_buffer,
        tokens[0..tok_count],
        &pos,
        &has_cfg_err,
        diagnostic_sink,
    );
    if (!has_cfg_err and pos < tok_count) {
        try emitCfgPredicateDiagnostic(
            diagnostic_sink,
            token_buffer.getTokenSpan(file_id, tokens[pos]),
            "unexpected trailing token in `@cfg(…)` predicate",
            "invalid token in `@cfg` expression",
        );
        return true;
    }
    return if (has_cfg_err) true else result;
}

/// Parses `OrExpr = AndExpr { "or" AndExpr }` inside `@cfg(…)` (`SE-18`).
fn parseCfgOrExprWithEnv(
    cfg_env: *const CfgEnv,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    tokens: []const TokenIndex,
    pos: *usize,
    has_err: *bool,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!bool {
    var lhs = try parseCfgAndExprWithEnv(
        cfg_env,
        file_id,
        source,
        token_buffer,
        tokens,
        pos,
        has_err,
        diagnostic_sink,
    );
    while (pos.* < tokens.len) {
        const tok = tokens[pos.*];
        const kind = token_buffer.getToken(tok).kind;
        if (kind == .kw_or) {
            pos.* += 1;
            const rhs = try parseCfgAndExprWithEnv(
                cfg_env,
                file_id,
                source,
                token_buffer,
                tokens,
                pos,
                has_err,
                diagnostic_sink,
            );
            lhs = lhs or rhs;
        } else if (kind == .pipepipe) {
            if (!has_err.*) {
                has_err.* = true;
                try emitCfgPredicateDiagnostic(
                    diagnostic_sink,
                    token_buffer.getTokenSpan(file_id, tok),
                    "`||` is retired in `@cfg(…)`; write `or` instead",
                    "use `or` in `@cfg` predicate",
                );
            }
            pos.* += 1;
            const rhs = try parseCfgAndExprWithEnv(
                cfg_env,
                file_id,
                source,
                token_buffer,
                tokens,
                pos,
                has_err,
                diagnostic_sink,
            );
            lhs = lhs or rhs;
        } else {
            break;
        }
    }
    return lhs;
}

/// Parses `AndExpr = UnaryExpr { "and" UnaryExpr }` inside `@cfg(…)` (`SE-18`).
fn parseCfgAndExprWithEnv(
    cfg_env: *const CfgEnv,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    tokens: []const TokenIndex,
    pos: *usize,
    has_err: *bool,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!bool {
    var lhs = try parseCfgUnaryExprWithEnv(
        cfg_env,
        file_id,
        source,
        token_buffer,
        tokens,
        pos,
        has_err,
        diagnostic_sink,
    );
    while (pos.* < tokens.len) {
        const tok = tokens[pos.*];
        const kind = token_buffer.getToken(tok).kind;
        if (kind == .kw_and) {
            pos.* += 1;
            const rhs = try parseCfgUnaryExprWithEnv(
                cfg_env,
                file_id,
                source,
                token_buffer,
                tokens,
                pos,
                has_err,
                diagnostic_sink,
            );
            lhs = lhs and rhs;
        } else if (kind == .amp and pos.* + 1 < tokens.len and
            token_buffer.getToken(tokens[pos.* + 1]).kind == .amp)
        {
            if (!has_err.*) {
                has_err.* = true;
                try emitCfgPredicateDiagnostic(
                    diagnostic_sink,
                    token_buffer.getTokenSpan(file_id, tok),
                    "`&&` is retired in `@cfg(…)`; write `and` instead",
                    "use `and` in `@cfg` predicate",
                );
            }
            pos.* += 2;
            const rhs = try parseCfgUnaryExprWithEnv(
                cfg_env,
                file_id,
                source,
                token_buffer,
                tokens,
                pos,
                has_err,
                diagnostic_sink,
            );
            lhs = lhs and rhs;
        } else {
            break;
        }
    }
    return lhs;
}

/// Parses `UnaryExpr = "not" UnaryExpr | AtomExpr` inside `@cfg(…)` (`SE-18`).
fn parseCfgUnaryExprWithEnv(
    cfg_env: *const CfgEnv,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    tokens: []const TokenIndex,
    pos: *usize,
    has_err: *bool,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!bool {
    if (pos.* >= tokens.len) {
        has_err.* = true;
        return true;
    }
    const tok = tokens[pos.*];
    const kind = token_buffer.getToken(tok).kind;
    if (kind == .kw_not) {
        pos.* += 1;
        return !(try parseCfgUnaryExprWithEnv(
            cfg_env,
            file_id,
            source,
            token_buffer,
            tokens,
            pos,
            has_err,
            diagnostic_sink,
        ));
    }
    if (kind == .bang) {
        if (!has_err.*) {
            has_err.* = true;
            try emitCfgPredicateDiagnostic(
                diagnostic_sink,
                token_buffer.getTokenSpan(file_id, tok),
                "`!` negation is retired in `@cfg(…)`; write `not` instead",
                "use `not` in `@cfg` predicate",
            );
        }
        pos.* += 1;
        return !(try parseCfgUnaryExprWithEnv(
            cfg_env,
            file_id,
            source,
            token_buffer,
            tokens,
            pos,
            has_err,
            diagnostic_sink,
        ));
    }
    return parseCfgAtomExprWithEnv(
        cfg_env,
        file_id,
        source,
        token_buffer,
        tokens,
        pos,
        has_err,
        diagnostic_sink,
    );
}

/// Parses a primary `@cfg` predicate (`target.os == …`, `target.os is (…)`, `cfg.feature.<name>`, `debug`, `test`).
fn parseCfgAtomExprWithEnv(
    cfg_env: *const CfgEnv,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    tokens: []const TokenIndex,
    pos: *usize,
    has_err: *bool,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!bool {
    if (pos.* >= tokens.len) {
        has_err.* = true;
        return true;
    }
    const start_tok = tokens[pos.*];
    const start_kind = token_buffer.getToken(start_tok).kind;
    const start_span = token_buffer.getTokenSpan(file_id, start_tok);

    if (start_kind == .lparen) {
        pos.* += 1;
        const inner = try parseCfgOrExprWithEnv(
            cfg_env,
            file_id,
            source,
            token_buffer,
            tokens,
            pos,
            has_err,
            diagnostic_sink,
        );
        if (pos.* < tokens.len and token_buffer.getToken(tokens[pos.*]).kind == .rparen) {
            pos.* += 1;
        } else if (!has_err.*) {
            has_err.* = true;
            try emitCfgPredicateDiagnostic(
                diagnostic_sink,
                start_span,
                "unclosed `(` in `@cfg(…)` predicate",
                "missing `)` in `@cfg` predicate",
            );
        }
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
    var seg_spans: [4]Span = undefined;
    var seg_count: usize = 0;
    if (isIdentifierToken(start_kind) or start_kind == .kw_pub or start_kind == .prim_type) {
        segs[0] = extractTokenSlice(source, token_buffer, start_tok);
        seg_spans[0] = start_span;
        seg_count = 1;
        pos.* += 1;
        while (seg_count < segs.len and pos.* + 1 < tokens.len and
            token_buffer.getToken(tokens[pos.*]).kind == .dot)
        {
            const next_tok = tokens[pos.* + 1];
            const next_kind = token_buffer.getToken(next_tok).kind;
            if (!isIdentifierToken(next_kind)) break;
            segs[seg_count] = extractTokenSlice(source, token_buffer, next_tok);
            seg_spans[seg_count] = token_buffer.getTokenSpan(file_id, next_tok);
            seg_count += 1;
            pos.* += 2;
        }
    } else {
        if (!has_err.*) {
            has_err.* = true;
            try emitCfgPredicateDiagnostic(
                diagnostic_sink,
                start_span,
                "invalid expression in `@cfg(…)` predicate",
                "expected `@cfg` key (`os`, `arch`, `abi`, `endian`, `ptr_width`, `debug`, `test`, or `feature`)",
            );
        }
        pos.* += 1;
        return true;
    }

    var eff_segs: []const []const u8 = segs[0..seg_count];
    var eff_spans: []const Span = seg_spans[0..seg_count];
    if (eff_segs.len >= 2 and std.mem.eql(u8, eff_segs[0], "core")) {
        eff_segs = eff_segs[1..];
        eff_spans = eff_spans[1..];
    }
    if (eff_segs.len >= 2 and (std.mem.eql(u8, eff_segs[0], "target") or std.mem.eql(u8, eff_segs[0], "cfg"))) {
        eff_segs = eff_segs[1..];
        eff_spans = eff_spans[1..];
    }

    if (eff_segs.len == 2 and std.mem.eql(u8, eff_segs[0], "feature")) {
        return evaluateCfgFeatureFlag(cfg_env, eff_segs[1], eff_spans[1], has_err, diagnostic_sink);
    }
    if (eff_segs.len != 1) {
        if (!has_err.*) {
            has_err.* = true;
            try emitCfgPredicateDiagnostic(
                diagnostic_sink,
                start_span,
                "unknown target or configuration path in `@cfg(…)` predicate",
                "unknown `@cfg` path",
            );
        }
        return true;
    }

    const key = eff_segs[0];

    if (std.mem.eql(u8, key, "feature")) {
        if (pos.* + 2 < tokens.len and
            token_buffer.getToken(tokens[pos.*]).kind == .lparen and
            token_buffer.getToken(tokens[pos.* + 1]).kind == .string_lit and
            token_buffer.getToken(tokens[pos.* + 2]).kind == .rparen)
        {
            const lit_tok = tokens[pos.* + 1];
            const raw_lit = extractTokenSlice(source, token_buffer, lit_tok);
            pos.* += 3;
            const feat_name = if (raw_lit.len >= 2) raw_lit[1 .. raw_lit.len - 1] else "";
            return evaluateCfgFeatureFlag(
                cfg_env,
                feat_name,
                token_buffer.getTokenSpan(file_id, lit_tok),
                has_err,
                diagnostic_sink,
            );
        }
        if (!has_err.*) {
            has_err.* = true;
            try emitCfgPredicateDiagnostic(
                diagnostic_sink,
                start_span,
                "`feature(…)` in `@cfg` requires a single string literal argument (`feature(\"name\")`)",
                "invalid `feature(…)` syntax in `@cfg`",
            );
        }
        return true;
    }
    if (std.mem.eql(u8, key, "cpu_has")) {
        if (pos.* + 2 < tokens.len and
            token_buffer.getToken(tokens[pos.*]).kind == .lparen and
            token_buffer.getToken(tokens[pos.* + 1]).kind == .string_lit and
            token_buffer.getToken(tokens[pos.* + 2]).kind == .rparen)
        {
            const raw_cpu_lit = extractTokenSlice(source, token_buffer, tokens[pos.* + 1]);
            pos.* += 3;
            const cpu_feat = if (raw_cpu_lit.len >= 2) raw_cpu_lit[1 .. raw_cpu_lit.len - 1] else "";
            for (cfg_env.enabled_cpu_features) |enabled_cpu| {
                if (std.mem.eql(u8, enabled_cpu, cpu_feat)) return true;
            }
            return false;
        }
        if (pos.* < tokens.len and token_buffer.getToken(tokens[pos.*]).kind == .lparen) {
            var depth: u32 = 1;
            pos.* += 1;
            while (pos.* < tokens.len and depth > 0) : (pos.* += 1) {
                const tok_kind = token_buffer.getToken(tokens[pos.*]).kind;
                if (tok_kind == .lparen) {
                    depth += 1;
                } else if (tok_kind == .rparen) {
                    depth -= 1;
                }
            }
            return false;
        }
    }

    if (std.mem.eql(u8, key, "debug") or std.mem.eql(u8, key, "test") or
        std.mem.eql(u8, key, "test_mode") or std.mem.eql(u8, key, "sim_mode") or
        std.mem.eql(u8, key, "fuzz_mode"))
    {
        const flag_val = if (std.mem.eql(u8, key, "debug"))
            cfg_env.is_debug
        else if (std.mem.eql(u8, key, "test") or std.mem.eql(u8, key, "test_mode"))
            cfg_env.is_test_mode
        else if (std.mem.eql(u8, key, "sim_mode"))
            cfg_env.is_sim_mode
        else if (std.mem.eql(u8, key, "fuzz_mode"))
            cfg_env.is_fuzz_mode
        else
            false;

        if (pos.* < tokens.len) {
            const op_kind = token_buffer.getToken(tokens[pos.*]).kind;
            if (op_kind == .eqeq or op_kind == .bang_eq) {
                pos.* += 1;
                if (pos.* < tokens.len) {
                    const rhs_kind = token_buffer.getToken(tokens[pos.*]).kind;
                    if (rhs_kind == .kw_true or rhs_kind == .kw_false) {
                        pos.* += 1;
                        const rhs_bool = (rhs_kind == .kw_true);
                        return if (op_kind == .eqeq) flag_val == rhs_bool else flag_val != rhs_bool;
                    }
                }
                if (!has_err.*) {
                    has_err.* = true;
                    try emitCfgPredicateDiagnostic(
                        diagnostic_sink,
                        start_span,
                        "boolean `@cfg` flag can only be compared against `true` or `false`",
                        "expected `true` or `false`",
                    );
                }
                return true;
            }
        }
        return flag_val;
    }

    if (std.mem.eql(u8, key, "ptr_width")) {
        if (pos.* + 1 < tokens.len) {
            const op_kind = token_buffer.getToken(tokens[pos.*]).kind;
            const val_tok = tokens[pos.* + 1];
            if ((op_kind == .eqeq or op_kind == .bang_eq) and
                token_buffer.getToken(val_tok).kind == .int_lit)
            {
                const lex = extractTokenSlice(source, token_buffer, val_tok);
                pos.* += 2;
                if (extractCfgUnsignedInt(lex)) |parsed_val| {
                    const is_eq = (parsed_val == @as(u64, cfg_env.ptr_width));
                    return if (op_kind == .eqeq) is_eq else !is_eq;
                }
            }
        }
        if (!has_err.*) {
            has_err.* = true;
            try emitCfgPredicateDiagnostic(
                diagnostic_sink,
                start_span,
                "`ptr_width` in `@cfg` requires `==` or `!=` with an integer literal (`32` or `64`)",
                "expected `ptr_width == 64` or `ptr_width == 32`",
            );
        }
        return true;
    }

    if (std.mem.eql(u8, key, "os") or std.mem.eql(u8, key, "arch") or
        std.mem.eql(u8, key, "abi") or std.mem.eql(u8, key, "endian"))
    {
        if (pos.* < tokens.len) {
            const op_kind = token_buffer.getToken(tokens[pos.*]).kind;
            if (op_kind == .eqeq or op_kind == .bang_eq) {
                pos.* += 1;
                const matched = try matchCfgSingleTargetValueWithEnv(
                    cfg_env,
                    file_id,
                    source,
                    token_buffer,
                    key,
                    tokens,
                    pos,
                    has_err,
                    start_span,
                    diagnostic_sink,
                );
                return if (op_kind == .eqeq) matched else !matched;
            }
            if (op_kind == .kw_is) {
                pos.* += 1;
                var is_negated = false;
                if (pos.* < tokens.len and token_buffer.getToken(tokens[pos.*]).kind == .kw_not) {
                    is_negated = true;
                    pos.* += 1;
                }
                const has_paren = pos.* < tokens.len and token_buffer.getToken(tokens[pos.*]).kind == .lparen;
                if (has_paren) pos.* += 1;
                var has_any_matched = false;
                while (pos.* < tokens.len) {
                    if (try matchCfgSingleTargetValueWithEnv(
                        cfg_env,
                        file_id,
                        source,
                        token_buffer,
                        key,
                        tokens,
                        pos,
                        has_err,
                        start_span,
                        diagnostic_sink,
                    )) {
                        has_any_matched = true;
                    }
                    if (pos.* < tokens.len and token_buffer.getToken(tokens[pos.*]).kind == .pipe) {
                        pos.* += 1;
                    } else {
                        break;
                    }
                }
                if (has_paren and pos.* < tokens.len and
                    token_buffer.getToken(tokens[pos.*]).kind == .rparen)
                {
                    pos.* += 1;
                }
                return if (is_negated) !has_any_matched else has_any_matched;
            }
        }
        if (!has_err.*) {
            has_err.* = true;
            try emitCfgPredicateDiagnostic(
                diagnostic_sink,
                start_span,
                "`@cfg` target property requires `==`, `!=`, or `is` comparison",
                "expected `==`, `!=`, or `is` after target property",
            );
        }
        return true;
    }

    if (!has_err.*) {
        has_err.* = true;
        var msg_buf: [160]u8 = undefined;
        const msg = std.fmt.bufPrint(
            &msg_buf,
            "unknown `@cfg` predicate key `{s}`",
            .{key},
        ) catch "unknown `@cfg` predicate key";
        try emitCfgPredicateDiagnostic(
            diagnostic_sink,
            start_span,
            msg,
            "unknown `@cfg` key; expected `os`, `arch`, `abi`, `endian`, `ptr_width`, `debug`, `test`, or `feature`",
        );
    }
    return true;
}

/// Matches one string literal (`"linux"`) or contextual variant (`.Linux`) against `cfg_env` for `key`.
fn matchCfgSingleTargetValueWithEnv(
    cfg_env: *const CfgEnv,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    key: []const u8,
    tokens: []const TokenIndex,
    pos: *usize,
    has_err: *bool,
    fallback_span: Span,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!bool {
    if (pos.* >= tokens.len) {
        if (!has_err.*) {
            has_err.* = true;
            try emitCfgPredicateDiagnostic(
                diagnostic_sink,
                fallback_span,
                "missing target value in `@cfg` comparison",
                "expected string literal or enum variant",
            );
        }
        return false;
    }
    var raw_val: []const u8 = "";
    const tok = tokens[pos.*];
    const kind = token_buffer.getToken(tok).kind;
    const val_span = token_buffer.getTokenSpan(file_id, tok);
    if (kind == .string_lit) {
        const lit = extractTokenSlice(source, token_buffer, tok);
        raw_val = if (lit.len >= 2) lit[1 .. lit.len - 1] else "";
        pos.* += 1;
    } else if (kind == .dot and pos.* + 1 < tokens.len and
        isIdentifierToken(token_buffer.getToken(tokens[pos.* + 1]).kind))
    {
        raw_val = extractTokenSlice(source, token_buffer, tokens[pos.* + 1]);
        pos.* += 2;
    } else {
        if (!has_err.*) {
            has_err.* = true;
            try emitCfgPredicateDiagnostic(
                diagnostic_sink,
                val_span,
                "`@cfg` target comparison requires a string literal or `.Variant`",
                "invalid `@cfg` target value",
            );
        }
        pos.* += 1;
        return false;
    }

    if (std.mem.eql(u8, key, "os")) {
        if (std.ascii.eqlIgnoreCase(raw_val, "linux")) return cfg_env.os == .linux;
        if (std.ascii.eqlIgnoreCase(raw_val, "windows")) return cfg_env.os == .windows;
        if (std.ascii.eqlIgnoreCase(raw_val, "macos")) return cfg_env.os == .macos;
        if (std.ascii.eqlIgnoreCase(raw_val, "wasi")) return cfg_env.os == .wasi;
        if (std.ascii.eqlIgnoreCase(raw_val, "freestanding")) return cfg_env.os == .freestanding;
    } else if (std.mem.eql(u8, key, "arch")) {
        if (std.ascii.eqlIgnoreCase(raw_val, "x86_64")) return cfg_env.arch == .x86_64;
        if (std.ascii.eqlIgnoreCase(raw_val, "aarch64")) return cfg_env.arch == .aarch64;
        if (std.ascii.eqlIgnoreCase(raw_val, "riscv64")) return cfg_env.arch == .riscv64;
        if (std.ascii.eqlIgnoreCase(raw_val, "wasm32")) return cfg_env.arch == .wasm32;
    } else if (std.mem.eql(u8, key, "abi")) {
        if (std.ascii.eqlIgnoreCase(raw_val, "gnu")) return cfg_env.abi == .gnu;
        if (std.ascii.eqlIgnoreCase(raw_val, "musl")) return cfg_env.abi == .musl;
        if (std.ascii.eqlIgnoreCase(raw_val, "msvc")) return cfg_env.abi == .msvc;
        if (std.ascii.eqlIgnoreCase(raw_val, "apple")) return cfg_env.abi == .apple;
        if (std.ascii.eqlIgnoreCase(raw_val, "wasi")) return cfg_env.abi == .wasi;
        if (std.ascii.eqlIgnoreCase(raw_val, "none")) return cfg_env.abi == .none;
    } else if (std.mem.eql(u8, key, "endian")) {
        if (std.ascii.eqlIgnoreCase(raw_val, "little")) return cfg_env.endian == .little;
        if (std.ascii.eqlIgnoreCase(raw_val, "big")) return cfg_env.endian == .big;
    }

    if (!has_err.*) {
        has_err.* = true;
        var msg_buf: [160]u8 = undefined;
        const msg = std.fmt.bufPrint(
            &msg_buf,
            "unknown `{s}` target value `{s}` in `@cfg(…)`",
            .{ key, raw_val },
        ) catch "unknown target value in `@cfg(…)`";
        try emitCfgPredicateDiagnostic(
            diagnostic_sink,
            val_span,
            msg,
            "unrecognized target value for `@cfg` key",
        );
    }
    return false;
}

/// Emits `E0423` (`e0423_invalid_bitfield_or_enum_cast`) when retired `@repr(Int)` is written on an `enum` (`ADR-22D`).
fn emitRetiredEnumReprIntDiagnostic(
    sink: *DiagnosticSink,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    enum_name: []const u8,
    repr_int_token: TokenIndex,
) !void {
    if (repr_int_token.isNone() or repr_int_token.asInt() >= token_buffer.countTokens()) return;
    const repr_span = token_buffer.getTokenSpan(file_id, repr_int_token);
    const int_lex = extractTokenSlice(source, token_buffer, repr_int_token);
    const arena_alloc = sink.arena.asAllocator();
    const main_msg = try std.fmt.allocPrint(
        arena_alloc,
        "`@repr({s})` on `enum {s}` has been retired; specify the backing integer inline as `enum {s}: {s}`",
        .{ int_lex, enum_name, enum_name, int_lex },
    );
    const label_msg = try std.fmt.allocPrint(
        arena_alloc,
        "retired `@repr({s})` on `enum`; write `enum {s}: {s}` instead",
        .{ int_lex, enum_name, int_lex },
    );
    const labels = [1]LabeledSpan{
        .{ .span = repr_span, .label = label_msg, .style = .primary },
    };
    const notes = [1][]const u8{
        "help: integer-backed enums declare `: Int` on the header (`@repr(C)` remains valid for C ABI enums)",
    };
    _ = try sink.emit(.{
        .code = .e0423_invalid_bitfield_or_enum_cast,
        .severity = .err,
        .primary_span = repr_span,
        .message = main_msg,
        .labels = &labels,
        .notes = &notes,
    });
}

/// Removes parser `W0201` `PascalCase` warnings on the 13 canonical C primitive type aliases (`c_char`..`c_void`).
pub fn suppressCPrimitiveTypeCasingWarnings(
    diagnostic_sink: ?*DiagnosticSink,
    file_id: FileId,
    source: []const u8,
) void {
    const sink = diagnostic_sink orelse return;
    if (file_id.isNone()) return;
    var write_idx: usize = 0;
    for (sink.diagnostics.items) |diag_item| {
        var is_exempt_c_alias = false;
        if (diag_item.code == .w0201_non_canonical_identifier_case and
            diag_item.primary_span.file_id == file_id and
            diag_item.primary_span.start_byte < diag_item.primary_span.end_byte and
            diag_item.primary_span.end_byte <= source.len)
        {
            const is_pascal_expectation = if (diag_item.labels.len > 0)
                std.mem.indexOf(u8, diag_item.labels[0].label, "PascalCase") != null
            else
                true;
            if (is_pascal_expectation) {
                const span_lexeme = source[diag_item.primary_span.start_byte..diag_item.primary_span.end_byte];
                is_exempt_c_alias = C_PRIMITIVE_TYPE_ALIAS_MAP.has(span_lexeme);
            }
        }
        if (is_exempt_c_alias) {
            if (diag_item.severity == .warning) {
                sink.warning_count -|= 1;
            } else if (diag_item.severity == .err) {
                sink.error_count -|= 1;
                if (sink.error_count < sink.max_errors) {
                    sink.has_reached_limit = false;
                }
            }
        } else {
            sink.diagnostics.items[write_idx] = diag_item;
            write_idx += 1;
        }
    }
    sink.diagnostics.items.len = write_idx;
}

/// Enforces `DR-17` pre-`@cfg` external-package hygiene (`E0327`, `E0218`, `E0013`) across all CST nodes.
pub fn enforceExternalPackageCstHygiene(
    sym_table: *const SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    diagnostic_sink: ?*DiagnosticSink,
) !void {
    if (sym_table.getFilePackageId(file_id).asInt() < 2) return;
    const sink = diagnostic_sink orelse return;
    const file_cfg = sym_table.effectiveCfgEnvForFile(file_id);
    const total_nodes = cst_arena.countNodes();
    const total_tokens = token_buffer.countTokens();

    var cursor: usize = 0;
    while (cursor < total_nodes) : (cursor += 1) {
        const node_idx = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(node_idx);

        if (node.kind == .attribute) {
            const attr_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), total_nodes);
            var attr_cur = cursor + 1;
            while (attr_cur < attr_end) : (attr_cur += 1) {
                const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(attr_cur)));
                if (leaf.subtree_size > 1 or leaf.flags.is_missing_or_injected or
                    leaf.token.isNone() or leaf.token.asInt() >= total_tokens)
                {
                    continue;
                }
                const tok_kind = token_buffer.getToken(leaf.token).kind;
                if (tok_kind == .at) continue;
                if (isIdentifierToken(tok_kind)) {
                    const attr_name = extractTokenSlice(source, token_buffer, leaf.token);
                    if (FORBIDDEN_EXTERNAL_PKG_ATTR_MAP.has(attr_name)) {
                        const attr_span = token_buffer.getTokenSpan(file_id, leaf.token);
                        if (!hasDiagnosticAtSpan(sink, .e0327_forbidden_sandbox_bypass_attribute, attr_span)) {
                            const arena_alloc = sink.arena.asAllocator();
                            const msg = try std.fmt.allocPrint(
                                arena_alloc,
                                "forbidden sandbox-bypass attribute `@{s}` inside external package",
                                .{attr_name},
                            );
                            const labels = [1]LabeledSpan{.{
                                .span = attr_span,
                                .label = "privileged capability/linker attribute is forbidden in external dependencies",
                                .style = .primary,
                            }};
                            _ = try sink.emit(.{
                                .code = .e0327_forbidden_sandbox_bypass_attribute,
                                .severity = .err,
                                .primary_span = attr_span,
                                .message = msg,
                                .labels = &labels,
                            });
                        }
                    }
                }
                break;
            }
            continue;
        }

        if (node.kind == .use_item) {
            if (parser.extractInlineUseDeclView(source, file_id, token_buffer, cst_arena, node_idx, .none)) |inline_view| {
                if (!hasDiagnosticAtSpan(sink, .e0013_invalid_manifest_or_pkg_name, inline_view.spec_span)) {
                    const labels = [1]LabeledSpan{.{
                        .span = inline_view.spec_span,
                        .label = "inline package imports are only permitted in the root workspace or scripts",
                        .style = .primary,
                    }};
                    _ = try sink.emit(.{
                        .code = .e0013_invalid_manifest_or_pkg_name,
                        .severity = .err,
                        .primary_span = inline_view.spec_span,
                        .message = "external package cannot use inline string `use \"…\" as …;` imports; declare dependencies in `corex.toml`",
                        .labels = &labels,
                    });
                }
                continue;
            }

            const item_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), total_nodes);
            var item_cur = cursor + 1;
            while (item_cur < item_end) : (item_cur += 1) {
                const sub_idx = CstNodeIndex.fromInt(@intCast(item_cur));
                if (cst_arena.getNode(sub_idx).kind == .use_tree) {
                    try checkExternalUseTreeCoreImports(
                        interner,
                        file_id,
                        source,
                        token_buffer,
                        cst_arena,
                        sub_idx,
                        true,
                        sink,
                    );
                    break;
                }
            }
            continue;
        }

        // Also enforce `E0218` on qualified `core.<ident>` path roots inside `@cfg`-disabled subtrees:
        if (hasFalseLeadingCfgOnCstNode(&file_cfg, file_id, source, token_buffer, cst_arena, node_idx)) {
            const subtree_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), total_nodes);
            var scan_cur = cursor + 1;
            while (scan_cur < subtree_end) {
                const sub_rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(scan_cur)));
                if (sub_rec.kind == .attribute or sub_rec.kind == .use_item) {
                    scan_cur += @max(@as(usize, sub_rec.subtree_size), 1);
                    continue;
                }
                if (sub_rec.subtree_size <= 1 and !sub_rec.flags.is_bracketed and
                    !sub_rec.flags.is_missing_or_injected and !sub_rec.token.isNone() and
                    sub_rec.token.asInt() < total_tokens)
                {
                    const tok_idx = sub_rec.token;
                    const tok_rec = token_buffer.getToken(tok_idx);
                    if (!tok_rec.flags.is_synthesized and tok_rec.kind == .ident and
                        std.mem.eql(u8, extractTokenSlice(source, token_buffer, tok_idx), "core"))
                    {
                        var prev_kind: TokenKind = .eof;
                        var back_i = tok_idx.asInt();
                        while (back_i > 0) {
                            back_i -= 1;
                            const prev_rec = token_buffer.getToken(TokenIndex.fromInt(back_i));
                            if (!prev_rec.flags.is_synthesized) {
                                prev_kind = prev_rec.kind;
                                break;
                            }
                        }
                        if (prev_kind != .dot and prev_kind != .kw_mod and prev_kind != .kw_use) {
                            var fwd_i = tok_idx.asInt() + 1;
                            while (fwd_i < total_tokens and token_buffer.getToken(TokenIndex.fromInt(fwd_i)).flags.is_synthesized) {
                                fwd_i += 1;
                            }
                            if (fwd_i < total_tokens and token_buffer.getToken(TokenIndex.fromInt(fwd_i)).kind == .dot) {
                                var seg_i = fwd_i + 1;
                                while (seg_i < total_tokens and token_buffer.getToken(TokenIndex.fromInt(seg_i)).flags.is_synthesized) {
                                    seg_i += 1;
                                }
                                if (seg_i < total_tokens) {
                                    const seg_kind = token_buffer.getToken(TokenIndex.fromInt(seg_i)).kind;
                                    if (isIdentifierToken(seg_kind) or seg_kind == .kw_async) {
                                        const core_span = token_buffer.getTokenSpan(file_id, tok_idx);
                                        if (!hasDiagnosticAtSpan(sink, .e0218_direct_core_import_forbidden, core_span)) {
                                            try emitDirectCoreImportDiagnostic(sink, interner, core_span);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                scan_cur += 1;
            }
        }
    }
}

/// Returns `true` if `sink` already contains a diagnostic with `code` overlapping `span`.
fn hasDiagnosticAtSpan(sink: *const DiagnosticSink, code: DiagnosticCode, span: Span) bool {
    for (sink.asSlice()) |existing| {
        if (existing.code == code and
            existing.primary_span.file_id == span.file_id and
            existing.primary_span.start_byte <= span.end_byte and
            span.start_byte <= existing.primary_span.end_byte)
        {
            return true;
        }
    }
    return false;
}

/// Recursively checks `.use_tree` root segments in an external package (`PackageId >= 2`) for `core` (`E0218`).
fn checkExternalUseTreeCoreImports(
    interner: *StringInterner,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    tree_cst: CstNodeIndex,
    is_at_root_segment: bool,
    sink: *DiagnosticSink,
) !void {
    const start_idx: usize = tree_cst.asInt();
    const tree_rec = cst_arena.getNode(tree_cst);
    const end_idx = @min(start_idx + @max(@as(usize, tree_rec.subtree_size), 1), cst_arena.countNodes());
    var has_consumed_segment = false;

    var cur = start_idx + 1;
    while (cur < end_idx) {
        const sub_idx = CstNodeIndex.fromInt(@intCast(cur));
        const sub = cst_arena.getNode(sub_idx);
        if (sub.kind == .use_tree) {
            try checkExternalUseTreeCoreImports(
                interner,
                file_id,
                source,
                token_buffer,
                cst_arena,
                sub_idx,
                is_at_root_segment and !has_consumed_segment,
                sink,
            );
            cur += @max(@as(usize, sub.subtree_size), 1);
            continue;
        }
        if (sub.subtree_size <= 1 and !sub.flags.is_bracketed and !sub.flags.is_missing_or_injected and
            !sub.token.isNone() and sub.token.asInt() < token_buffer.countTokens())
        {
            const tok_kind = token_buffer.getToken(sub.token).kind;
            if (isIdentifierToken(tok_kind)) {
                if (is_at_root_segment and !has_consumed_segment) {
                    const lex = extractTokenSlice(source, token_buffer, sub.token);
                    if (std.mem.eql(u8, lex, "core")) {
                        const core_span = token_buffer.getTokenSpan(file_id, sub.token);
                        if (!hasDiagnosticAtSpan(sink, .e0218_direct_core_import_forbidden, core_span)) {
                            try emitDirectCoreImportDiagnostic(sink, interner, core_span);
                        }
                    }
                }
                has_consumed_segment = true;
            }
        }
        cur += 1;
    }
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
    suppressCPrimitiveTypeCasingWarnings(diagnostic_sink, file_id, source);
    try enforceExternalPackageCstHygiene(
        sym_table,
        interner,
        file_id,
        source,
        token_buffer,
        cst_arena,
        diagnostic_sink,
    );

    var write_idx: usize = 0;
    for (sym_table.pending_imports.items) |pending_imp| {
        if (pending_imp.file_id != file_id) {
            sym_table.pending_imports.items[write_idx] = pending_imp;
            write_idx += 1;
        }
    }
    sym_table.pending_imports.items.len = write_idx;

    var stale_def_keys: std.ArrayListUnmanaged(u32) = .empty;
    defer stale_def_keys.deinit(sym_table.allocator);
    var def_key_iter = sym_table.def_to_symbol.keyIterator();
    while (def_key_iter.next()) |raw_def_ptr| {
        if (DefId.fromInt(raw_def_ptr.*).fileId() == file_id) {
            try stale_def_keys.append(sym_table.allocator, raw_def_ptr.*);
        }
    }
    for (stale_def_keys.items) |stale_def_raw| {
        _ = sym_table.def_to_symbol.remove(stale_def_raw);
    }

    var stale_from_keys: std.ArrayListUnmanaged(u64) = .empty;
    defer stale_from_keys.deinit(sym_table.allocator);
    var from_iter = sym_table.from_error_fn_defs.iterator();
    while (from_iter.next()) |from_entry| {
        if (from_entry.value_ptr.fileId() == file_id) {
            try stale_from_keys.append(sym_table.allocator, from_entry.key_ptr.*);
        }
    }
    for (stale_from_keys.items) |stale_pair_key| {
        _ = sym_table.from_error_fn_defs.remove(stale_pair_key);
        _ = sym_table.from_error_pairs.remove(stale_pair_key);
    }

    const file_scope = try sym_table.scope_arena.allocScope(
        .module_scope,
        sym_table.prelude_scope,
        .NONE,
        file_id,
        .{},
    );
    sym_table.scope_arena.setScopePackageId(file_scope, sym_table.getFilePackageId(file_id));
    try sym_table.file_module_scopes.put(sym_table.allocator, file_id.asInt(), file_scope);

    if (ast_arena.countNodes() == 0) return file_scope;
    const extra_ends = try syntax_arenas.computeAstNodeExtraEnds(sym_table.allocator, ast_arena);
    defer sym_table.allocator.free(extra_ends);
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
            extra_ends,
            diagnostic_sink,
        );
        try pruneScopeMapWithCfgEnvQuiet(
            sym_table,
            file_id,
            source,
            token_buffer,
            cst_arena,
            file_scope,
            0,
        );
    }
    return file_scope;
}

/// Extracts all function-like AST/CST handles in `ast_arena` (including tests/benches) in `collectFileModuleItems` DFS order.
pub fn collectFileFnDeclHandles(
    allocator: std.mem.Allocator,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
) std.mem.Allocator.Error![]FnDeclSyntaxHandle {
    return collectFileFnDeclHandlesWithOptions(
        allocator,
        source,
        token_buffer,
        cst_arena,
        ast_arena,
        true,
    );
}

/// Extracts function-like AST/CST handles in `ast_arena` with explicit `is_including_tests` filtering (`SE-16`).
pub fn collectFileFnDeclHandlesWithOptions(
    allocator: std.mem.Allocator,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    is_including_tests: bool,
) std.mem.Allocator.Error![]FnDeclSyntaxHandle {
    var handles: std.ArrayListUnmanaged(FnDeclSyntaxHandle) = .empty;
    errdefer handles.deinit(allocator);
    if (ast_arena.countNodes() > 0) {
        const extra_ends = try syntax_arenas.computeAstNodeExtraEnds(allocator, ast_arena);
        defer allocator.free(extra_ends);
        const root_node = ast_arena.getNode(.root);
        if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and root_node.rhs.payload > 0) {
            try collectFnDeclHandlesInSlice(
                allocator,
                ast_arena.getExtraSlice(ExtraIndex.fromInt(root_node.lhs.payload), root_node.rhs.payload),
                source,
                token_buffer,
                cst_arena,
                ast_arena,
                extra_ends,
                is_including_tests,
                &handles,
                0,
            );
        }
    }
    return handles.toOwnedSlice(allocator);
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
    extra_ends: []const u32,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!void {
    var root_top_ordinal: u12 = 0;
    return collectItemSliceInScopeWithOrdinal(
        sym_table,
        interner,
        file_id,
        enclosing_scope,
        if (is_file_top_level) &root_top_ordinal else null,
        enclosing_owner_def,
        item_slice,
        source,
        token_buffer,
        cst_arena,
        ast_arena,
        extra_ends,
        diagnostic_sink,
    );
}

/// Returns the exact `rhs` `extra_data` slice of `node_idx` matching `computeAstNodeExtraEnds` without overrunning.
fn computeRhsExtraSliceWithEnds(
    ast_arena: *const AstArena,
    node_idx: NodeIndex,
    extra_ends_opt: ?[]const u32,
) []const u32 {
    if (node_idx.isNone() or node_idx.asInt() >= ast_arena.countNodes()) return &.{};
    const ast_node = ast_arena.getNode(node_idx);
    if (ast_node.rhs.tag != .extra) return &.{};
    const extra_len = ast_arena.extra_data.items.len;
    const start_extra: usize = ast_node.rhs.payload;
    if (start_extra >= extra_len) return &.{};
    if (extra_ends_opt) |extra_ends| {
        if (node_idx.asInt() < extra_ends.len) {
            const end_extra = @min(@as(usize, extra_ends[node_idx.asInt()]), extra_len);
            if (start_extra >= end_extra) return &.{};
            return ast_arena.extra_data.items[start_extra..end_extra];
        }
    }
    var best_end: usize = extra_len;
    const node_count = ast_arena.countNodes();
    for (0..node_count) |cand_idx| {
        const cand_node = ast_arena.getNode(NodeIndex.fromInt(@intCast(cand_idx)));
        if (cand_node.lhs.tag == .extra and cand_node.rhs.tag == .extra) {
            const start_pos: usize = cand_node.lhs.payload;
            const end_pos: usize = start_pos +| @as(usize, cand_node.rhs.payload);
            if (cand_node.rhs.payload > 0 and start_pos > start_extra and start_pos < best_end) {
                best_end = start_pos;
            }
            if (end_pos > start_extra and end_pos < best_end) {
                best_end = end_pos;
            }
        } else if (cand_node.lhs.tag == .extra) {
            const start_pos: usize = cand_node.lhs.payload;
            if (start_pos > start_extra and start_pos < best_end) {
                best_end = start_pos;
            }
        } else if (cand_node.rhs.tag == .extra) {
            const start_pos: usize = cand_node.rhs.payload;
            if (start_pos > start_extra and start_pos < best_end) {
                best_end = start_pos;
            }
        }
    }
    return ast_arena.extra_data.items[start_extra..best_end];
}

/// Extracts the slice of inner item AST indices from an inline `mod foo { … }` node.
pub fn extractModInnerItems(ast_arena: *const AstArena, mod_node_idx: NodeIndex) []const u32 {
    return computeRhsExtraSliceWithEnds(ast_arena, mod_node_idx, null);
}

/// Extracts the slice of member AST node indices from an `impl_decl` node.
pub fn extractImplMemberItems(ast_arena: *const AstArena, impl_node_idx: NodeIndex) []const u32 {
    return computeRhsExtraSliceWithEnds(ast_arena, impl_node_idx, null);
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

        var before_for_toks: [16]TokenIndex = undefined;
        var before_for_len: usize = 0;
        var after_for_toks: [16]TokenIndex = undefined;
        var after_for_len: usize = 0;
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
            if (isIdentifierToken(tok_kind) or tok_kind == .prim_type or tok_kind == .kw_async) {
                if (!has_seen_for) {
                    if (before_for_len < before_for_toks.len) {
                        before_for_toks[before_for_len] = node.token;
                        before_for_len += 1;
                    }
                } else {
                    if (after_for_len < after_for_toks.len) {
                        after_for_toks[after_for_len] = node.token;
                        after_for_len += 1;
                    }
                }
            }
        }

        if (has_seen_for and before_for_len > 0) {
            const trait_tok = before_for_toks[before_for_len - 1];
            const trait_lex = extractTokenSlice(source, token_buffer, trait_tok);
            if (trait_lex.len > 0) {
                const trait_id = try interner.intern(trait_lex);
                const trait_lookup: LookupResult = if (before_for_len > 1) blk: {
                    const mod_scope = try resolveModulePathSegments(
                        sym_table,
                        interner,
                        file_id,
                        enclosing_scope,
                        enclosing_scope,
                        before_for_toks[0 .. before_for_len - 1],
                        source,
                        token_buffer,
                        null,
                    );
                    if (mod_scope.isNone()) break :blk .not_found;
                    break :blk sym_table.lookupInTargetScope(
                        mod_scope,
                        enclosing_scope,
                        trait_id,
                        NamespaceMask.TYPE_ONLY,
                    );
                } else sym_table.lookupLexical(enclosing_scope, trait_id, NamespaceMask.TYPE_ONLY);
                switch (trait_lookup) {
                    .found => |found_trait| {
                        if (sym_table.getSymbol(found_trait).kind == .trait_sym) {
                            trait_sym_idx = found_trait;
                        }
                    },
                    else => {},
                }
            }
        }

        const target_toks = if (has_seen_for and after_for_len > 0)
            after_for_toks[0..after_for_len]
        else
            before_for_toks[0..before_for_len];

        if (target_toks.len > 0) {
            const target_tok = target_toks[target_toks.len - 1];
            const target_type_name = extractTokenSlice(source, token_buffer, target_tok);
            if (target_type_name.len > 0) {
                const target_sym_id = try interner.intern(target_type_name);
                const lookup: LookupResult = if (target_toks.len > 1) blk: {
                    const mod_scope = try resolveModulePathSegments(
                        sym_table,
                        interner,
                        file_id,
                        enclosing_scope,
                        enclosing_scope,
                        target_toks[0 .. target_toks.len - 1],
                        source,
                        token_buffer,
                        null,
                    );
                    if (mod_scope.isNone()) break :blk .not_found;
                    break :blk sym_table.lookupInTargetScope(
                        mod_scope,
                        enclosing_scope,
                        target_sym_id,
                        NamespaceMask.TYPE_ONLY,
                    );
                } else sym_table.lookupLexical(enclosing_scope, target_sym_id, NamespaceMask.TYPE_ONLY);
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
                            if (!sym.def_id.isNone()) sym.def_id else def_id,
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

/// Collects `.struct_field` / `.bit_field_member` CST nodes inside `struct`, `union`, or `bit_field` into `member_scope`.
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
        if (node.kind == .struct_field or node.kind == .bit_field_member) {
            const field_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), end_idx);
            var field_vis: Visibility = .private;
            var field_tok: TokenIndex = .none;
            var bit_width: u16 = 0;
            var has_seen_pipe = false;
            var has_field_cfg = false;

            var inner_cur = cursor + 1;
            while (inner_cur < field_end) : (inner_cur += 1) {
                const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(inner_cur)));
                if (sub.kind == .attribute) {
                    const attr_end = @min(inner_cur + @max(@as(usize, sub.subtree_size), 1), field_end);
                    var attr_cur = inner_cur + 1;
                    while (attr_cur < attr_end) : (attr_cur += 1) {
                        const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(attr_cur)));
                        if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                            leaf.token.asInt() < token_buffer.countTokens() and
                            isIdentifierToken(token_buffer.getToken(leaf.token).kind))
                        {
                            if (std.mem.eql(u8, extractTokenSlice(source, token_buffer, leaf.token), "cfg")) {
                                has_field_cfg = true;
                            }
                            break;
                        }
                    }
                    if (sub.subtree_size > 1) {
                        inner_cur += @as(usize, sub.subtree_size) - 1;
                    }
                    continue;
                }
                if (sub.kind == .visibility_modifier) {
                    field_vis = extractVisibilityFromCst(
                        source,
                        token_buffer,
                        cst_arena,
                        CstNodeIndex.fromInt(@intCast(inner_cur)),
                    );
                    if (sub.subtree_size > 1) {
                        inner_cur += @as(usize, sub.subtree_size) - 1;
                    }
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
                        .visibility = field_vis,
                        .flags = .{ .is_pub = (field_vis == .public) },
                        .scope_id = member_scope,
                        .cst_node = cst_id,
                        .decl_span = token_buffer.getTokenSpan(file_id, field_tok),
                        .member_ordinal = ordinal,
                        .bit_width = bit_width,
                        .has_cfg_attr = has_field_cfg,
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
    enum_visibility: Visibility,
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
            var has_var_cfg = false;

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
                                const attr_lex = extractTokenSlice(source, token_buffer, leaf.token);
                                if (std.mem.eql(u8, attr_lex, "from")) {
                                    is_var_from_error = true;
                                } else if (std.mem.eql(u8, attr_lex, "cfg")) {
                                    has_var_cfg = true;
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
                        .visibility = enum_visibility,
                        .flags = .{
                            .is_pub = (enum_visibility == .public),
                            .is_from_error = is_var_from_error,
                        },
                        .scope_id = variant_scope,
                        .cst_node = cst_id,
                        .decl_span = token_buffer.getTokenSpan(file_id, var_tok),
                        .member_ordinal = ordinal,
                        .has_cfg_attr = has_var_cfg,
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

/// Evaluates all leading `@cfg(…)` attributes on `cst_node` against `cfg_env` (`DR-22` `SE-18`).
pub fn evaluateCstNodeCfgWithEnv(
    cfg_env: *const CfgEnv,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    cst_node: CstNodeIndex,
    diagnostic_sink: ?*DiagnosticSink,
) anyerror!bool {
    if (cst_node.isNone() or cst_node.asInt() >= cst_arena.countNodes()) return true;
    const start_idx: usize = cst_node.asInt();
    const root_rec = cst_arena.getNode(cst_node);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var is_all_enabled = true;
    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (sub.kind == .block or sub.kind == .fn_expr_body or sub.kind == .param_list or
            sub.kind == .type_params or sub.kind == .struct_introducer or
            sub.kind == .enum_introducer or sub.kind == .union_introducer or
            sub.kind == .use_tree)
        {
            break;
        }
        if (sub.subtree_size <= 1 and !sub.token.isNone() and
            sub.token.asInt() < token_buffer.countTokens() and
            token_buffer.getToken(sub.token).kind == .lbrace)
        {
            break;
        }
        if (sub.kind == .attribute) {
            const attr_end = @min(cursor + @max(@as(usize, sub.subtree_size), 1), end_idx);
            const attr_enabled = try evaluateSingleCfgAttrRangeWithEnv(
                cfg_env,
                file_id,
                source,
                token_buffer,
                cst_arena,
                cursor,
                attr_end,
                diagnostic_sink,
            );
            if (!attr_enabled) is_all_enabled = false;
            if (sub.subtree_size > 1) cursor += @as(usize, sub.subtree_size) - 1;
        }
    }
    return is_all_enabled;
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
    const effective_cfg = sym_table.effectiveCfgEnvForFile(file_id);
    var i: usize = 0;
    while (i < sym_table.pending_imports.items.len) : (i += 1) {
        const pending = sym_table.pending_imports.items[i];
        if (pending.file_id != file_id) continue;
        if (pending.cst_node.isNone() or pending.cst_node.asInt() >= cst_arena.countNodes()) continue;

        const has_use_cfg = extractItemHeaderMetadata(
            source,
            token_buffer,
            cst_arena,
            pending.cst_node,
            .none,
        ).has_cfg_attr;
        if (has_use_cfg) {
            const is_use_enabled = try evaluateCstNodeCfgWithEnv(
                &effective_cfg,
                pending.file_id,
                source,
                token_buffer,
                cst_arena,
                pending.cst_node,
                diagnostic_sink,
            );
            if (!is_use_enabled) continue;
        }

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
                    .none,
                    pending.def_id,
                    pending.visibility,
                    pending.cst_node,
                    has_use_cfg,
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

/// Recursively resolves a `.use_tree` CST subtree (`path.to.{self, a, b as c}` or `path.*`).
fn resolveUseTreeCst(
    sym_table: *SymbolTable,
    interner: *StringInterner,
    file_id: FileId,
    dest_module_scope: ScopeId,
    current_lookup_scope: ScopeId,
    parent_mod_tok: TokenIndex,
    def_id: DefId,
    visibility: Visibility,
    use_item_cst: CstNodeIndex,
    has_use_cfg: bool,
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

    if (current_lookup_scope == dest_module_scope) {
        if (parser.extractInlineUseDeclView(
            source,
            file_id,
            token_buffer,
            cst_arena,
            use_item_cst,
            .none,
        )) |inline_view| {
            if (sym_table.getFilePackageId(file_id).asInt() >= 2) {
                if (diagnostic_sink) |sink| {
                    if (!hasDiagnosticAtSpan(sink, .e0013_invalid_manifest_or_pkg_name, inline_view.spec_span)) {
                        const labels = [1]LabeledSpan{.{
                            .span = inline_view.spec_span,
                            .label = "inline package imports are only permitted in the root workspace or scripts",
                            .style = .primary,
                        }};
                        _ = try sink.emit(.{
                            .code = .e0013_invalid_manifest_or_pkg_name,
                            .severity = .err,
                            .primary_span = inline_view.spec_span,
                            .message = "external package cannot use inline string `use \"…\" as …;` imports; " ++
                                "declare dependencies in `corex.toml`",
                            .labels = &labels,
                        });
                    }
                }
                return;
            }
            if (inline_view.alias_slice.len == 0 or
                parser.RESERVED_INLINE_USE_ALIAS_MAP.has(inline_view.alias_slice))
            {
                return;
            }
            const alias_sym_id = try interner.intern(inline_view.alias_slice);
            const is_pub_inline = (visibility == .public);
            if (sym_table.lookupExternalPackageScope(file_id, alias_sym_id)) |dep_scope| {
                _ = try sym_table.defineSymbol(.{
                    .name = alias_sym_id,
                    .name_text = interner.get(alias_sym_id),
                    .kind = .module_sym,
                    .namespace = .value_ns,
                    .visibility = visibility,
                    .flags = .{ .is_pub = is_pub_inline, .is_used = true, .is_imported = true },
                    .scope_id = dest_module_scope,
                    .def_id = def_id,
                    .cst_node = use_item_cst,
                    .decl_span = inline_view.alias_span,
                    .target_scope = dep_scope,
                    .has_cfg_attr = has_use_cfg,
                }, diagnostic_sink);
                return;
            }
            if (diagnostic_sink) |sink| {
                try emitUnresolvedSymbolDiagnostic(
                    sink,
                    interner,
                    inline_view.alias_slice,
                    inline_view.alias_span,
                    null,
                );
            }
            return;
        }
    }

    var segments: [32]TokenIndex = undefined;
    var seg_count: usize = 0;
    var is_glob = false;
    var has_seen_as = false;
    var alias_tok: TokenIndex = .none;
    var has_nested_trees = false;
    var cached_prefix_scope: ?ScopeId = null;
    const is_pub_export = (visibility == .public);

    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) {
        const sub_id = CstNodeIndex.fromInt(@intCast(cursor));
        const sub = cst_arena.getNode(sub_id);

        if (sub.kind == .use_tree) {
            has_nested_trees = true;
            // Resolve prefix `segments[0..seg_count]` once across all braced group children:
            const prefix_scope = if (cached_prefix_scope) |cached_scope|
                cached_scope
            else blk: {
                const resolved_scope = try resolveModulePathSegments(
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
                cached_prefix_scope = resolved_scope;
                break :blk resolved_scope;
            };
            const next_parent_tok = if (seg_count > 0) segments[seg_count - 1] else parent_mod_tok;
            if (!prefix_scope.isNone()) {
                try resolveUseTreeCst(
                    sym_table,
                    interner,
                    file_id,
                    dest_module_scope,
                    prefix_scope,
                    next_parent_tok,
                    def_id,
                    visibility,
                    use_item_cst,
                    has_use_cfg,
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
                (isIdentifierToken(tok_kind) or tok_kind == .kw_self_val or
                    tok_kind == .kw_self_type or tok_kind == .kw_async))
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

    // [1] Glob import (`use prefix.*;`):
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
            if (member.has_cfg_attr) {
                const scoped_key = packScopedSymbolKey(target_scope, member.name, member.namespace);
                if (sym_table.scoped_map.get(scoped_key)) |active_idx| {
                    if (active_idx != member_idx and
                        sym_table.getSymbol(active_idx).kind != .overload_group_sym)
                    {
                        continue;
                    }
                } else {
                    continue;
                }
            }
            const vis_check = sym_table.checkSymbolVisibility(member_idx, dest_module_scope);
            if (vis_check != .found) continue;

            const resolved_member = sym_table.getSymbol(vis_check.found).*;
            var max_member_vis_raw: u2 = if (member.flags.is_builtin)
                @backingInt(Visibility.public)
            else
                @backingInt(member.visibility);
            if (!resolved_member.flags.is_builtin) {
                max_member_vis_raw = @min(max_member_vis_raw, @backingInt(resolved_member.visibility));
            }
            if (max_member_vis_raw == @backingInt(Visibility.pub_super)) {
                const member_mod = sym_table.scope_arena.getScope(member.scope_id).enclosing_module;
                const dest_mod = sym_table.scope_arena.getScope(dest_module_scope).enclosing_module;
                if (!member_mod.isNone() and
                    sym_table.scope_arena.findImmediateParentModule(member_mod) == dest_mod)
                {
                    max_member_vis_raw = @backingInt(Visibility.private);
                }
            }
            const clamped_vis: Visibility = @fromBackingInt(@min(@backingInt(visibility), max_member_vis_raw));

            _ = try sym_table.defineSymbol(.{
                .name = member.name,
                .name_text = member.name_text,
                .kind = .use_alias_sym,
                .namespace = member.namespace,
                .visibility = clamped_vis,
                .flags = .{
                    .is_pub = clamped_vis == .public,
                    .is_used = true,
                    .is_imported = true,
                },
                .scope_id = dest_module_scope,
                .def_id = def_id,
                .cst_node = use_item_cst,
                .decl_span = member.decl_span,
                .type_id = member.type_id,
                .target_symbol = vis_check.found,
                .target_scope = member.target_scope,
                .has_cfg_attr = has_use_cfg,
            }, null);
        }
        return;
    }

    // [2] Group `self` import (`use cx.fs.{self, File};` or `use cx.fs.{self as fs_alias};`):
    const final_tok = segments[seg_count - 1];
    const final_lexeme = extractTokenSlice(source, token_buffer, final_tok);
    if (final_lexeme.len == 0) return;

    if (seg_count == 1 and std.mem.eql(u8, final_lexeme, "self") and current_lookup_scope != dest_module_scope) {
        const bind_name_tok = if (!alias_tok.isNone()) alias_tok else parent_mod_tok;
        if (bind_name_tok.isNone()) return;
        const bind_lexeme = extractTokenSlice(source, token_buffer, bind_name_tok);
        if (bind_lexeme.len == 0 or std.mem.eql(u8, bind_lexeme, "_")) return;
        const bind_sym_id = try interner.intern(bind_lexeme);
        const decl_tok = if (!alias_tok.isNone()) alias_tok else final_tok;
        const decl_span = token_buffer.getTokenSpan(file_id, decl_tok);
        var self_mod_vis = visibility;
        if (visibility != .private and !parent_mod_tok.isNone()) {
            const parent_mod_lex = extractTokenSlice(source, token_buffer, parent_mod_tok);
            if (interner.lookup(parent_mod_lex)) |parent_sym_id| {
                const mod_parent_scope = sym_table.scope_arena.getScope(current_lookup_scope).parent;
                if (!mod_parent_scope.isNone()) {
                    const mod_sym_idx = sym_table.lookupInScopeDirect(
                        mod_parent_scope,
                        parent_sym_id,
                        NamespaceMask.VALUE_ONLY,
                    );
                    if (!mod_sym_idx.isNone()) {
                        const mod_sym = sym_table.getSymbol(mod_sym_idx).*;
                        if (!mod_sym.flags.is_builtin and @backingInt(visibility) > @backingInt(mod_sym.visibility)) {
                            if (diagnostic_sink) |sink| {
                                try emitUseVisibilityEscalationDiagnostic(
                                    sink,
                                    &mod_sym,
                                    visibility,
                                    mod_sym.visibility,
                                    decl_span,
                                );
                            }
                            self_mod_vis = mod_sym.visibility;
                        }
                    }
                }
            }
        }
        _ = try sym_table.defineSymbol(.{
            .name = bind_sym_id,
            .name_text = interner.get(bind_sym_id),
            .kind = .module_sym,
            .namespace = .value_ns,
            .visibility = self_mod_vis,
            .flags = .{ .is_pub = self_mod_vis == .public, .is_used = true, .is_imported = true },
            .scope_id = dest_module_scope,
            .def_id = def_id,
            .cst_node = use_item_cst,
            .decl_span = decl_span,
            .target_scope = current_lookup_scope,
            .has_cfg_attr = has_use_cfg,
        }, diagnostic_sink);
        return;
    }

    // [3] Single-segment root namespace import (`use pkg as root;`, `use cx;`, `use core;` -> `E0218`):
    const final_span = token_buffer.getTokenSpan(file_id, final_tok);
    if (seg_count == 1 and current_lookup_scope == dest_module_scope and std.mem.eql(u8, final_lexeme, "pkg")) {
        const pkg_root_scope = sym_table.resolveCallerPackageRootScope(file_id, dest_module_scope);
        const bind_tok = if (!alias_tok.isNone()) alias_tok else final_tok;
        const bind_lexeme = extractTokenSlice(source, token_buffer, bind_tok);
        if (bind_lexeme.len == 0 or std.mem.eql(u8, bind_lexeme, "_") or std.mem.eql(u8, bind_lexeme, "pkg")) return;
        const bind_sym_id = try interner.intern(bind_lexeme);
        _ = try sym_table.defineSymbol(.{
            .name = bind_sym_id,
            .name_text = interner.get(bind_sym_id),
            .kind = .module_sym,
            .namespace = .value_ns,
            .visibility = visibility,
            .flags = .{ .is_pub = is_pub_export, .is_used = true, .is_imported = true },
            .scope_id = dest_module_scope,
            .def_id = def_id,
            .cst_node = use_item_cst,
            .decl_span = token_buffer.getTokenSpan(file_id, bind_tok),
            .target_scope = pkg_root_scope,
            .has_cfg_attr = has_use_cfg,
        }, diagnostic_sink);
        return;
    }
    if (seg_count == 1 and current_lookup_scope == dest_module_scope and
        (std.mem.eql(u8, final_lexeme, "cx") or
            std.mem.eql(u8, final_lexeme, "core")))
    {
        const root_mod_scope = try sym_table.resolveRootNamespaceScope(
            interner,
            dest_module_scope,
            final_lexeme,
            final_span,
            diagnostic_sink,
        );
        if (!root_mod_scope.isNone()) {
            const bind_tok = if (!alias_tok.isNone()) alias_tok else final_tok;
            const bind_lexeme = extractTokenSlice(source, token_buffer, bind_tok);
            if (bind_lexeme.len == 0 or std.mem.eql(u8, bind_lexeme, "_")) return;
            const bind_sym_id = try interner.intern(bind_lexeme);
            _ = try sym_table.defineSymbol(.{
                .name = bind_sym_id,
                .name_text = interner.get(bind_sym_id),
                .kind = .module_sym,
                .namespace = .value_ns,
                .visibility = visibility,
                .flags = .{ .is_pub = is_pub_export, .is_used = true, .is_imported = true },
                .scope_id = dest_module_scope,
                .def_id = def_id,
                .cst_node = use_item_cst,
                .decl_span = token_buffer.getTokenSpan(file_id, bind_tok),
                .target_scope = root_mod_scope,
                .has_cfg_attr = has_use_cfg,
            }, diagnostic_sink);
            return;
        }
        if (std.mem.eql(u8, final_lexeme, "core") and !sym_table.isCoreAllowedForFile(file_id)) {
            return;
        }
    }

    // [4] Single path import (`use prefix.Item [as Alias];`):
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

    const final_sym_id = try interner.intern(final_lexeme);

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

            const direct_idx = sym_table.lookupInScopeDirect(prefix_scope, final_sym_id, NamespaceMask.ALL);
            const direct_vis_raw: u2 = if (!direct_idx.isNone() and !sym_table.getSymbol(direct_idx).flags.is_builtin)
                @backingInt(sym_table.getSymbol(direct_idx).visibility)
            else
                @backingInt(Visibility.public);
            const target_vis_raw: u2 = if (target_rec.flags.is_builtin)
                @backingInt(Visibility.public)
            else
                @backingInt(target_rec.visibility);
            const max_allowed_vis: Visibility = @fromBackingInt(@min(direct_vis_raw, target_vis_raw));

            const bind_sym_id = try interner.intern(bind_lexeme);
            const bind_span = token_buffer.getTokenSpan(file_id, bind_tok);
            var effective_alias_vis = visibility;
            if (visibility != .private and @backingInt(visibility) > @backingInt(max_allowed_vis)) {
                if (diagnostic_sink) |sink| {
                    try emitUseVisibilityEscalationDiagnostic(
                        sink,
                        &target_rec,
                        visibility,
                        max_allowed_vis,
                        bind_span,
                    );
                }
                effective_alias_vis = max_allowed_vis;
            }
            _ = try sym_table.defineSymbol(.{
                .name = bind_sym_id,
                .name_text = interner.get(bind_sym_id),
                .kind = .use_alias_sym,
                .namespace = target_rec.namespace,
                .visibility = effective_alias_vis,
                .flags = .{
                    .is_pub = effective_alias_vis == .public,
                    .is_used = true,
                    .is_imported = true,
                },
                .scope_id = dest_module_scope,
                .def_id = def_id,
                .cst_node = use_item_cst,
                .decl_span = bind_span,
                .type_id = target_rec.type_id,
                .target_symbol = resolved_idx,
                .target_scope = target_rec.target_scope,
                .has_cfg_attr = has_use_cfg,
            }, diagnostic_sink);
        },
        .private_error => |priv_idx| {
            if (diagnostic_sink) |sink| {
                try emitPrivateAccessDiagnostic(sink, sym_table.getSymbol(priv_idx), final_span);
            }
        },
        .not_found => {
            if (prefix_scope == dest_module_scope and
                std.mem.eql(u8, final_lexeme, "core") and
                !sym_table.isCoreAllowedForFile(file_id))
            {
                if (diagnostic_sink) |sink| {
                    if (!hasDiagnosticAtSpan(sink, .e0218_direct_core_import_forbidden, final_span)) {
                        try emitDirectCoreImportDiagnostic(sink, interner, final_span);
                    }
                }
                return;
            }
            // Check if `final_sym_id` is a declared dependency or root cross-file module strictly at segment 0:
            if (seg_count == 1 and prefix_scope == dest_module_scope and
                (!std.mem.eql(u8, final_lexeme, "core") or sym_table.isCoreAllowedForFile(file_id)))
            {
                if (sym_table.lookupExternalPackageScope(file_id, final_sym_id)) |ext_mod_scope| {
                    const bind_tok = if (!alias_tok.isNone()) alias_tok else final_tok;
                    const bind_lexeme = extractTokenSlice(source, token_buffer, bind_tok);
                    if (bind_lexeme.len == 0 or std.mem.eql(u8, bind_lexeme, "_")) return;
                    const bind_sym_id = try interner.intern(bind_lexeme);
                    _ = try sym_table.defineSymbol(.{
                        .name = bind_sym_id,
                        .name_text = interner.get(bind_sym_id),
                        .kind = .module_sym,
                        .namespace = .value_ns,
                        .visibility = visibility,
                        .flags = .{ .is_pub = is_pub_export, .is_used = true, .is_imported = true },
                        .scope_id = dest_module_scope,
                        .def_id = def_id,
                        .decl_span = token_buffer.getTokenSpan(file_id, bind_tok),
                        .target_scope = ext_mod_scope,
                    }, diagnostic_sink);
                    return;
                }
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

/// Resolves a sequence of `module.submodule` path tokens to their target `ScopeId`.
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

        if (i == 0 and cur_scope == caller_scope and std.mem.eql(u8, seg_lexeme, "pkg")) {
            cur_scope = sym_table.resolveCallerPackageRootScope(file_id, caller_scope);
            continue;
        }

        const seg_sym_id = try interner.intern(seg_lexeme);
        const seg_span = token_buffer.getTokenSpan(file_id, seg_tok);
        if (i == 0 and cur_scope == caller_scope and
            (std.mem.eql(u8, seg_lexeme, "cx") or
                std.mem.eql(u8, seg_lexeme, "core")))
        {
            const root_ns_scope = try sym_table.resolveRootNamespaceScope(
                interner,
                caller_scope,
                seg_lexeme,
                seg_span,
                diagnostic_sink,
            );
            if (!root_ns_scope.isNone()) {
                cur_scope = root_ns_scope;
                continue;
            }
            if (std.mem.eql(u8, seg_lexeme, "core") and !sym_table.isCoreAllowedForFile(file_id)) {
                return .none;
            }
        }
        const lookup_res = if (i == 0 and cur_scope == caller_scope)
            sym_table.lookupLexical(cur_scope, seg_sym_id, NamespaceMask.ALL)
        else
            sym_table.lookupInTargetScope(cur_scope, caller_scope, seg_sym_id, NamespaceMask.ALL);

        switch (lookup_res) {
            .found => |sym_idx| {
                sym_table.markSymbolUsed(sym_idx);
                const sym = sym_table.getSymbol(sym_idx);
                if (!sym.target_scope.isNone()) {
                    cur_scope = sym.target_scope;
                    continue;
                }
                if (i == 0 and cur_scope == caller_scope and sym.kind == .module_sym) {
                    if (sym_table.lookupExternalPackageScope(file_id, seg_sym_id)) |ext_scope| {
                        cur_scope = ext_scope;
                        continue;
                    }
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
                if (cur_scope == caller_scope and
                    std.mem.eql(u8, seg_lexeme, "core") and
                    !sym_table.isCoreAllowedForFile(file_id))
                {
                    if (diagnostic_sink) |sink| {
                        if (!hasDiagnosticAtSpan(sink, .e0218_direct_core_import_forbidden, seg_span)) {
                            try emitDirectCoreImportDiagnostic(sink, interner, seg_span);
                        }
                    }
                    return .none;
                }
                if (i == 0 and cur_scope == caller_scope and
                    (!std.mem.eql(u8, seg_lexeme, "core") or sym_table.isCoreAllowedForFile(file_id)))
                {
                    if (sym_table.lookupExternalPackageScope(file_id, seg_sym_id)) |ext_scope| {
                        cur_scope = ext_scope;
                        continue;
                    }
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

// --------------- Inactive @cfg Capability Scan ----------------

/// Validates syntactic well-formedness of an unquoted inline `use "<spec>"` package specifier (`E0013` on failure).
pub fn isValidInlineImportSpec(raw_spec: []const u8) bool {
    return parser.isValidInlineUseSpec(raw_spec);
}

/// Extracts all `@cfg`-active `InlineUseImport` records from `file_id`'s lossless CST in source order.
pub fn extractActiveInlineUseImports(
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    cfg_env: *const CfgEnv,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    diagnostic_sink: ?*DiagnosticSink,
) ![]InlineUseImport {
    var imports: std.ArrayListUnmanaged(InlineUseImport) = .empty;
    errdefer {
        for (imports.items) |entry| allocator.free(entry.spec_text);
        imports.deinit(allocator);
    }

    var active_mod_ends: [64]usize = undefined;
    var active_mod_depth: usize = 0;
    const total_nodes = cst_arena.countNodes();

    var cursor: usize = 0;
    while (cursor < total_nodes) {
        while (active_mod_depth > 0 and cursor >= active_mod_ends[active_mod_depth - 1]) {
            active_mod_depth -= 1;
        }
        const node_idx = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(node_idx);

        if (node.kind == .mod_item) {
            const mod_meta = extractItemHeaderMetadata(source, token_buffer, cst_arena, node_idx, .none);
            if (mod_meta.has_cfg_attr) {
                const is_mod_active = try evaluateCstNodeCfgWithEnv(
                    cfg_env,
                    file_id,
                    source,
                    token_buffer,
                    cst_arena,
                    node_idx,
                    diagnostic_sink,
                );
                if (!is_mod_active) {
                    cursor += @max(@as(usize, node.subtree_size), 1);
                    continue;
                }
                if (active_mod_depth < active_mod_ends.len) {
                    active_mod_ends[active_mod_depth] = cursor + @max(@as(usize, node.subtree_size), 1);
                    active_mod_depth += 1;
                }
            }
            cursor += 1;
            continue;
        }

        if (node.kind == .use_item) {
            if (parser.extractInlineUseDeclView(source, file_id, token_buffer, cst_arena, node_idx, .none)) |view| {
                const use_meta = extractItemHeaderMetadata(source, token_buffer, cst_arena, node_idx, .none);
                if (use_meta.has_cfg_attr) {
                    const is_active = try evaluateCstNodeCfgWithEnv(
                        cfg_env,
                        file_id,
                        source,
                        token_buffer,
                        cst_arena,
                        node_idx,
                        diagnostic_sink,
                    );
                    if (!is_active) {
                        cursor += @max(@as(usize, node.subtree_size), 1);
                        continue;
                    }
                }
                if (view.unquoted_spec.len > 0 and view.alias_slice.len > 0 and
                    isValidInlineImportSpec(view.unquoted_spec) and
                    !parser.RESERVED_INLINE_USE_ALIAS_MAP.has(view.alias_slice))
                {
                    const alias_sym = try interner.intern(view.alias_slice);
                    const spec_copy = try allocator.dupe(u8, view.unquoted_spec);
                    try imports.append(allocator, .{
                        .file_id = file_id,
                        .spec_text = spec_copy,
                        .alias_sym = alias_sym,
                        .alias_text = interner.get(alias_sym),
                        .visibility = use_meta.visibility,
                        .spec_span = view.spec_span,
                        .decl_span = view.decl_span,
                        .is_cfg_conditional = use_meta.has_cfg_attr or active_mod_depth > 0,
                    });
                }
                cursor += @max(@as(usize, node.subtree_size), 1);
                continue;
            }
        }
        cursor += 1;
    }

    return imports.toOwnedSlice(allocator);
}

/// Stack-allocated imported `cx.<domain>` alias binding used during `scanFileInactiveCfgCapabilities`.
const ImportedCapBinding = struct {
    /// Borrowed identifier lexeme bound by `use cx.<domain>…`.
    alias_name: []const u8,
    /// `CapabilityBits` mask (`0` when `is_cx_root_alias` is `true`).
    cap_bits: u16 = 0,
    /// `true` when this binding aliases the root `cx` namespace itself (`use cx as std_cx;`).
    is_cx_root_alias: bool = false,
};

/// Collects `use cx…` capability alias bindings recursively from `.use_tree` into `bindings[0..binding_count]`.
fn collectUseTreeCapBindings(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    tree_cst: CstNodeIndex,
    is_prefix_cx_root: bool,
    prefix_cap_bits: u16,
    parent_seg_lex: []const u8,
    bindings: *[256]ImportedCapBinding,
    binding_count: *usize,
) void {
    const start_idx: usize = tree_cst.asInt();
    const tree_rec = cst_arena.getNode(tree_cst);
    const end_idx = @min(start_idx + @max(@as(usize, tree_rec.subtree_size), 1), cst_arena.countNodes());

    var seg_slices: [16][]const u8 = undefined;
    var seg_count: usize = 0;
    var has_seen_as = false;
    var alias_slice: []const u8 = "";
    var has_nested = false;

    var cur = start_idx + 1;
    while (cur < end_idx) {
        const sub_idx = CstNodeIndex.fromInt(@intCast(cur));
        const sub = cst_arena.getNode(sub_idx);
        if (sub.kind == .use_tree) {
            has_nested = true;
            var is_next_cx = is_prefix_cx_root;
            var next_cap = prefix_cap_bits;
            for (seg_slices[0..seg_count], 0..) |seg_str, seg_i| {
                if (!is_next_cx and next_cap == 0 and seg_i == 0 and
                    (std.mem.eql(u8, seg_str, "cx") or std.mem.eql(u8, seg_str, "core")))
                {
                    is_next_cx = true;
                } else if (is_next_cx and next_cap == 0) {
                    next_cap = CX_DOMAIN_CAP_MAP.get(seg_str) orelse 0;
                    is_next_cx = false;
                }
            }
            const next_parent_seg = if (seg_count > 0) seg_slices[seg_count - 1] else parent_seg_lex;
            collectUseTreeCapBindings(
                source,
                token_buffer,
                cst_arena,
                sub_idx,
                is_next_cx,
                next_cap,
                next_parent_seg,
                bindings,
                binding_count,
            );
            cur += @max(@as(usize, sub.subtree_size), 1);
            continue;
        }
        if (sub.subtree_size <= 1 and !sub.flags.is_bracketed and !sub.flags.is_missing_or_injected and
            !sub.token.isNone() and sub.token.asInt() < token_buffer.countTokens())
        {
            const tok_kind = token_buffer.getToken(sub.token).kind;
            if (tok_kind == .kw_as) {
                has_seen_as = true;
            } else if (has_seen_as and isIdentifierToken(tok_kind)) {
                alias_slice = extractTokenSlice(source, token_buffer, sub.token);
            } else if (!has_seen_as and
                (isIdentifierToken(tok_kind) or tok_kind == .kw_self_val or tok_kind == .kw_async))
            {
                if (seg_count < seg_slices.len) {
                    seg_slices[seg_count] = extractTokenSlice(source, token_buffer, sub.token);
                    seg_count += 1;
                }
            }
        }
        cur += 1;
    }

    if (has_nested or seg_count == 0 or binding_count.* >= bindings.len) return;

    var is_cur_cx = is_prefix_cx_root;
    var cur_cap = prefix_cap_bits;
    for (seg_slices[0..seg_count], 0..) |seg_str, seg_i| {
        if (std.mem.eql(u8, seg_str, "self")) continue;
        if (!is_cur_cx and cur_cap == 0 and seg_i == 0 and
            (std.mem.eql(u8, seg_str, "cx") or std.mem.eql(u8, seg_str, "core")))
        {
            is_cur_cx = true;
        } else if (is_cur_cx and cur_cap == 0) {
            cur_cap = CX_DOMAIN_CAP_MAP.get(seg_str) orelse 0;
            is_cur_cx = false;
        }
    }

    const last_seg = seg_slices[seg_count - 1];
    const bound_name = if (alias_slice.len > 0)
        alias_slice
    else if (std.mem.eql(u8, last_seg, "self"))
        parent_seg_lex
    else
        last_seg;
    if (bound_name.len == 0 or std.mem.eql(u8, bound_name, "_")) return;

    if (is_cur_cx and cur_cap == 0) {
        bindings[binding_count.*] = .{
            .alias_name = bound_name,
            .cap_bits = 0,
            .is_cx_root_alias = true,
        };
        binding_count.* += 1;
    } else if (cur_cap != 0) {
        bindings[binding_count.*] = .{
            .alias_name = bound_name,
            .cap_bits = cur_cap,
            .is_cx_root_alias = false,
        };
        binding_count.* += 1;
    }
}

/// Evaluates whether `cst_node` carries a leading `@cfg(…)` attribute evaluating to `false` under `cfg_env`.
fn hasFalseLeadingCfgOnCstNode(
    cfg_env: *const CfgEnv,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    cst_node: CstNodeIndex,
) bool {
    const start_idx: usize = cst_node.asInt();
    const root_rec = cst_arena.getNode(cst_node);
    if (root_rec.subtree_size <= 1 or root_rec.kind == .file_end or root_rec.kind == .attribute) {
        return false;
    }
    const end_idx = @min(start_idx + @as(usize, root_rec.subtree_size), cst_arena.countNodes());
    var cursor = start_idx + 1;
    while (cursor < end_idx) {
        const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (sub.kind == .attribute) {
            const attr_end = @min(cursor + @max(@as(usize, sub.subtree_size), 1), end_idx);
            var attr_cur = cursor + 1;
            while (attr_cur < attr_end) : (attr_cur += 1) {
                const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(attr_cur)));
                if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                    leaf.token.asInt() < token_buffer.countTokens())
                {
                    const lk = token_buffer.getToken(leaf.token).kind;
                    if (lk == .at) continue;
                    if (isIdentifierToken(lk) and
                        std.mem.eql(u8, extractTokenSlice(source, token_buffer, leaf.token), "cfg"))
                    {
                        const is_true = evaluateSingleCfgAttrRangeWithEnv(
                            cfg_env,
                            file_id,
                            source,
                            token_buffer,
                            cst_arena,
                            cursor,
                            attr_end,
                            null,
                        ) catch true;
                        if (!is_true) return true;
                    }
                    break;
                }
            }
            cursor = attr_end;
            continue;
        }
        if (sub.kind == .visibility_modifier) {
            cursor += @max(@as(usize, sub.subtree_size), 1);
            continue;
        }
        break;
    }
    return false;
}

/// Scans `@cfg`-disabled CST items and intra-body statements/blocks for dormant capabilities (`DR-17` §3.1).
pub fn scanFileInactiveCfgCapabilities(
    cfg_env: *const CfgEnv,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
) InactiveCfgCapScan {
    var result = InactiveCfgCapScan{};
    const total_nodes = cst_arena.countNodes();
    if (total_nodes == 0) return result;

    // [1] Pre-collect file-level `use cx.<domain>…` capability aliases into a bounded stack table:
    var bindings: [256]ImportedCapBinding = undefined;
    var binding_count: usize = 0;
    var pre_cur: usize = 0;
    while (pre_cur < total_nodes) : (pre_cur += 1) {
        const pre_idx = CstNodeIndex.fromInt(@intCast(pre_cur));
        const pre_node = cst_arena.getNode(pre_idx);
        if (pre_node.kind == .use_item) {
            const item_end = @min(pre_cur + @max(@as(usize, pre_node.subtree_size), 1), total_nodes);
            var sub_cur = pre_cur + 1;
            while (sub_cur < item_end) : (sub_cur += 1) {
                const sub_idx = CstNodeIndex.fromInt(@intCast(sub_cur));
                if (cst_arena.getNode(sub_idx).kind == .use_tree) {
                    collectUseTreeCapBindings(
                        source,
                        token_buffer,
                        cst_arena,
                        sub_idx,
                        false,
                        0,
                        "",
                        &bindings,
                        &binding_count,
                    );
                    break;
                }
            }
        }
    }

    // [2] Walk CST in pre-order, tracking enclosing `pub` / body ranges and scanning `@cfg`-false subtrees:
    var pub_scope_ends: [64]usize = undefined;
    var pub_scope_depth: usize = 0;
    var body_scope_ends: [64]usize = undefined;
    var body_scope_depth: usize = 0;

    var cursor: usize = 0;
    while (cursor < total_nodes) {
        while (pub_scope_depth > 0 and cursor >= pub_scope_ends[pub_scope_depth - 1]) {
            pub_scope_depth -= 1;
        }
        while (body_scope_depth > 0 and cursor >= body_scope_ends[body_scope_depth - 1]) {
            body_scope_depth -= 1;
        }
        const node_idx = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(node_idx);
        const subtree_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), total_nodes);

        const is_body_container = switch (node.kind) {
            .fn_item,
            .impl_item,
            .trait_item,
            .subscript_item,
            .const_item,
            .test_item,
            .bench_item,
            => true,
            else => false,
        };
        const is_own_pub = switch (node.kind) {
            .impl_item, .trait_item => true,
            .use_item,
            .mod_item,
            .const_item,
            .type_alias_item,
            .struct_item,
            .union_item,
            .enum_item,
            .extern_block_item,
            .extern_static_item,
            .fn_item,
            .trait_member,
            .impl_member,
            .subscript_item,
            => extractItemHeaderMetadata(source, token_buffer, cst_arena, node_idx, .none).visibility == .public,
            else => false,
        };

        if (hasFalseLeadingCfgOnCstNode(cfg_env, file_id, source, token_buffer, cst_arena, node_idx)) {
            const is_in_pub_context = is_own_pub or pub_scope_depth > 0;
            const is_outer_in_body = is_body_container or body_scope_depth > 0;
            var subtree_caps: u16 = 0;
            var has_link_export = false;
            var prev_tok_kind: TokenKind = .eof;
            var is_prev_cx_root = false;
            var is_prev_at = false;
            var is_inside_cfg_attr = false;
            var cfg_attr_end: usize = 0;
            var nested_body_end: usize = 0;

            var scan_cur = cursor + 1;
            while (scan_cur < subtree_end) : (scan_cur += 1) {
                if (is_inside_cfg_attr and scan_cur >= cfg_attr_end) {
                    is_inside_cfg_attr = false;
                }
                if (nested_body_end > 0 and scan_cur >= nested_body_end) {
                    nested_body_end = 0;
                }
                const sub_node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(scan_cur)));
                if (nested_body_end == 0) {
                    switch (sub_node.kind) {
                        .fn_item,
                        .impl_item,
                        .trait_item,
                        .subscript_item,
                        .const_item,
                        .test_item,
                        .bench_item,
                        => {
                            nested_body_end = @min(scan_cur + @max(@as(usize, sub_node.subtree_size), 1), subtree_end);
                        },
                        else => {},
                    }
                }
                if (sub_node.kind == .attribute and !is_inside_cfg_attr) {
                    const attr_end = @min(scan_cur + @max(@as(usize, sub_node.subtree_size), 1), subtree_end);
                    var attr_check = scan_cur + 1;
                    while (attr_check < attr_end) : (attr_check += 1) {
                        const attr_leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(attr_check)));
                        if (attr_leaf.subtree_size <= 1 and !attr_leaf.token.isNone() and
                            attr_leaf.token.asInt() < token_buffer.countTokens())
                        {
                            const attr_kind = token_buffer.getToken(attr_leaf.token).kind;
                            if (attr_kind == .at) continue;
                            if (isIdentifierToken(attr_kind) and
                                std.mem.eql(u8, extractTokenSlice(source, token_buffer, attr_leaf.token), "cfg"))
                            {
                                is_inside_cfg_attr = true;
                                cfg_attr_end = attr_end;
                            }
                            break;
                        }
                    }
                }
                if (is_inside_cfg_attr) continue;
                if (sub_node.subtree_size > 1 or sub_node.flags.is_bracketed or
                    sub_node.flags.is_missing_or_injected or sub_node.token.isNone() or
                    sub_node.token.asInt() >= token_buffer.countTokens())
                {
                    continue;
                }

                const tok = sub_node.token;
                const tok_rec = token_buffer.getToken(tok);
                if (tok_rec.flags.is_synthesized) continue;
                const tok_kind = tok_rec.kind;
                const lexeme = extractTokenSlice(source, token_buffer, tok);
                var token_caps: u16 = 0;

                if (tok_kind == .kw_extern) {
                    token_caps |= CapabilityBits.FFI_UNSAFE;
                } else if (tok_kind == .kw_unsafe) {
                    token_caps |= CapabilityBits.UNSAFE_OP;
                } else if (is_prev_at and (isIdentifierToken(tok_kind) or tok_kind == .kw_extern)) {
                    if (std.mem.eql(u8, lexeme, "extern")) {
                        token_caps |= CapabilityBits.FFI_UNSAFE;
                    } else if (std.mem.eql(u8, lexeme, "c_import") or
                        std.mem.eql(u8, lexeme, "wasm_import") or
                        std.mem.eql(u8, lexeme, "link_lib"))
                    {
                        token_caps |= CapabilityBits.FFI;
                    } else if (std.mem.eql(u8, lexeme, "export") or
                        std.mem.eql(u8, lexeme, "wasm_export") or
                        std.mem.eql(u8, lexeme, "link_name") or
                        std.mem.eql(u8, lexeme, "link_section"))
                    {
                        token_caps |= CapabilityBits.FFI_UNSAFE;
                        has_link_export = true;
                    }
                } else if (is_prev_cx_root and tok_kind == .dot) {
                    // Keep `is_prev_cx_root` across `.` so the following `<domain>` segment matches:
                    prev_tok_kind = .dot;
                    is_prev_at = false;
                    continue;
                } else if (is_prev_cx_root and prev_tok_kind == .dot and
                    (isIdentifierToken(tok_kind) or tok_kind == .kw_async))
                {
                    token_caps |= CX_DOMAIN_CAP_MAP.get(lexeme) orelse 0;
                } else if (prev_tok_kind != .dot and isIdentifierToken(tok_kind)) {
                    if (tok_kind == .ident and std.mem.eql(u8, lexeme, "asm")) {
                        const next_tok = peekNextAttrLeafToken(token_buffer, cst_arena, scan_cur + 1, subtree_end);
                        if (!next_tok.isNone()) {
                            const next_kind = token_buffer.getToken(next_tok).kind;
                            if (next_kind == .lparen or next_kind == .lbrace or next_kind == .string_lit) {
                                token_caps |= CapabilityBits.FFI_UNSAFE;
                                if (!is_outer_in_body and nested_body_end == 0) {
                                    has_link_export = true;
                                }
                            }
                        }
                    } else if (std.mem.eql(u8, lexeme, "cx") or std.mem.eql(u8, lexeme, "core")) {
                        is_prev_cx_root = true;
                        prev_tok_kind = tok_kind;
                        is_prev_at = false;
                        continue;
                    } else {
                        for (bindings[0..binding_count]) |binding| {
                            if (std.mem.eql(u8, binding.alias_name, lexeme)) {
                                if (binding.is_cx_root_alias) {
                                    is_prev_cx_root = true;
                                } else {
                                    token_caps |= binding.cap_bits;
                                }
                            }
                        }
                        if (is_prev_cx_root) {
                            prev_tok_kind = tok_kind;
                            is_prev_at = false;
                            continue;
                        }
                    }
                }

                if (token_caps != 0) {
                    subtree_caps |= token_caps;
                    if (result.first_inactive_cap_span.file_id.isNone()) {
                        result.first_inactive_cap_span = token_buffer.getTokenSpan(file_id, tok);
                    }
                }
                is_prev_cx_root = false;
                is_prev_at = (tok_kind == .at);
                prev_tok_kind = tok_kind;
            }

            result.all_inactive_caps_bits |= subtree_caps;
            if (is_in_pub_context) {
                result.pub_inactive_caps_bits |= subtree_caps;
            }
            if (has_link_export) {
                result.link_ambient_inactive_caps_bits |= (subtree_caps | CapabilityBits.FFI | CapabilityBits.UNSAFE_OP);
            }
            cursor = subtree_end;
            continue;
        }

        if (is_own_pub and pub_scope_depth < pub_scope_ends.len) {
            pub_scope_ends[pub_scope_depth] = subtree_end;
            pub_scope_depth += 1;
        }
        if (is_body_container and body_scope_depth < body_scope_ends.len) {
            body_scope_ends[body_scope_depth] = subtree_end;
            body_scope_depth += 1;
        }
        cursor += 1;
    }

    return result;
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

    // Verify built-in prelude types and groups (`i32`, `opaque`, `Number`, `SourceLoc`, `FmtSpec`, `Bencher`):
    const i32_name = try interner.intern("i32");
    const opaque_name = try interner.intern("opaque");
    const num_name = try interner.intern("Number");
    const numeric_name = try interner.intern("Numeric");
    const src_loc_name = try interner.intern("SourceLoc");
    const fmt_spec_name = try interner.intern("FmtSpec");
    const fmt_args_name = try interner.intern("FmtArgs");
    const bencher_name = try interner.intern("Bencher");
    const task_group_name = try interner.intern("TaskGroup");
    const task_handle_name = try interner.intern("TaskHandle");

    const i32_lookup = sym_table.lookupLexical(sym_table.prelude_scope, i32_name, NamespaceMask.TYPE_ONLY);
    const opaque_lookup = sym_table.lookupLexical(sym_table.prelude_scope, opaque_name, NamespaceMask.TYPE_ONLY);
    const num_lookup = sym_table.lookupLexical(sym_table.prelude_scope, num_name, NamespaceMask.TYPE_ONLY);
    const numeric_lookup = sym_table.lookupLexical(sym_table.prelude_scope, numeric_name, NamespaceMask.TYPE_ONLY);
    const src_loc_lookup = sym_table.lookupLexical(sym_table.prelude_scope, src_loc_name, NamespaceMask.TYPE_ONLY);
    const fmt_spec_lookup = sym_table.lookupLexical(sym_table.prelude_scope, fmt_spec_name, NamespaceMask.TYPE_ONLY);
    const fmt_args_lookup = sym_table.lookupLexical(sym_table.prelude_scope, fmt_args_name, NamespaceMask.TYPE_ONLY);
    const bencher_lookup = sym_table.lookupLexical(sym_table.prelude_scope, bencher_name, NamespaceMask.TYPE_ONLY);
    const tg_lookup = sym_table.lookupLexical(sym_table.prelude_scope, task_group_name, NamespaceMask.TYPE_ONLY);
    const th_lookup = sym_table.lookupLexical(sym_table.prelude_scope, task_handle_name, NamespaceMask.TYPE_ONLY);

    try std.testing.expect(i32_lookup == .found);
    try std.testing.expect(opaque_lookup == .found);
    try std.testing.expect(num_lookup == .found);
    try std.testing.expect(numeric_lookup == .not_found);
    try std.testing.expect(src_loc_lookup == .found);
    try std.testing.expect(fmt_spec_lookup == .found);
    try std.testing.expect(fmt_args_lookup == .found);
    try std.testing.expect(bencher_lookup == .found);
    try std.testing.expect(tg_lookup == .found);
    try std.testing.expect(th_lookup == .found);

    try std.testing.expectEqual(TypeId.i32_ty, sym_table.getSymbol(i32_lookup.found).type_id);
    try std.testing.expectEqual(TypeId.opaque_ty, sym_table.getSymbol(opaque_lookup.found).type_id);
    try std.testing.expectEqual(TypeId.group_number, sym_table.getSymbol(num_lookup.found).type_id);
    try std.testing.expectEqual(TypeId.source_loc_ty, sym_table.getSymbol(src_loc_lookup.found).type_id);
    try std.testing.expectEqual(TypeId.fmt_spec_ty, sym_table.getSymbol(fmt_spec_lookup.found).type_id);
    try std.testing.expectEqual(TypeId.fmt_args_ty, sym_table.getSymbol(fmt_args_lookup.found).type_id);
    try std.testing.expectEqual(TypeId.bencher_ty, sym_table.getSymbol(bencher_lookup.found).type_id);
    try std.testing.expectEqual(TypeId.task_group_base_ty, sym_table.getSymbol(tg_lookup.found).type_id);
    try std.testing.expectEqual(TypeId.task_handle_base_ty, sym_table.getSymbol(th_lookup.found).type_id);

    // Verify typo and retired-group suggestions map `"Numbr"` and `"Numeric"` to `"Number"`:
    const suggestion = sym_table.suggestClosestSymbol(
        sym_table.prelude_scope,
        "Numbr",
        NamespaceMask.TYPE_ONLY,
    );
    try std.testing.expect(suggestion != null);
    try std.testing.expectEqualStrings("Number", suggestion.?);

    const numeric_sug = sym_table.suggestClosestSymbol(
        sym_table.prelude_scope,
        "Numeric",
        NamespaceMask.TYPE_ONLY,
    );
    try std.testing.expect(numeric_sug != null);
    try std.testing.expectEqualStrings("Number", numeric_sug.?);

    // Verify `[P0-A]` `cx.sync.atomic.MemoryOrder` and `Ordering` discriminant order `0..5`:
    const cx_root = try sym_table.ensureCxRootScope(&interner);
    const sync_sym = sym_table.lookupInScopeDirect(cx_root, try interner.intern("sync"), NamespaceMask.VALUE_ONLY);
    const sync_scope = sym_table.getSymbol(sync_sym).target_scope;
    const atomic_sym = sym_table.lookupInScopeDirect(sync_scope, try interner.intern("atomic"), NamespaceMask.VALUE_ONLY);
    const atomic_scope = sym_table.getSymbol(atomic_sym).target_scope;

    const expected_orders = [_][]const u8{ "Relaxed", "Consume", "Acquire", "Release", "AcqRel", "SeqCst" };
    for ([_][]const u8{ "MemoryOrder", "Ordering" }) |enum_name| {
        const enum_idx = sym_table.lookupInScopeDirect(atomic_scope, try interner.intern(enum_name), NamespaceMask.TYPE_ONLY);
        try std.testing.expect(!enum_idx.isNone());
        const var_scope = sym_table.getSymbol(enum_idx).target_scope;
        for (expected_orders, 0..) |variant_name, expected_ord| {
            const var_idx = sym_table.lookupInScopeDirect(var_scope, try interner.intern(variant_name), NamespaceMask.VALUE_ONLY);
            try std.testing.expect(!var_idx.isNone());
            try std.testing.expectEqual(@as(u16, @intCast(expected_ord)), sym_table.getSymbol(var_idx).member_ordinal);
        }
    }

    // Verify 4-tier `Visibility.isVisibleFrom` (`private` < `pub(super)` < `pub(pkg)` < `pub`):
    const pkg_a = PackageId.fromInt(1);
    const pkg_b = PackageId.fromInt(2);
    const root_mod = try sym_table.scope_arena.allocScope(.module_scope, sym_table.prelude_scope, .NONE, .none, .{});
    sym_table.scope_arena.setScopePackageId(root_mod, pkg_a);
    const parent_mod = try sym_table.scope_arena.allocScope(.module_scope, root_mod, .NONE, .none, .{});
    const child_mod = try sym_table.scope_arena.allocScope(.module_scope, parent_mod, .NONE, .none, .{});
    const sibling_mod = try sym_table.scope_arena.allocScope(.module_scope, parent_mod, .NONE, .none, .{});
    const cousin_mod = try sym_table.scope_arena.allocScope(.module_scope, root_mod, .NONE, .none, .{});
    const external_mod = try sym_table.scope_arena.allocScope(.module_scope, sym_table.prelude_scope, .NONE, .none, .{});
    sym_table.scope_arena.setScopePackageId(external_mod, pkg_b);

    try std.testing.expect(Visibility.private.isVisibleFrom(child_mod, pkg_a, child_mod, pkg_a, &sym_table.scope_arena));
    try std.testing.expect(!Visibility.private.isVisibleFrom(child_mod, pkg_a, sibling_mod, pkg_a, &sym_table.scope_arena));
    try std.testing.expect(Visibility.pub_super.isVisibleFrom(child_mod, pkg_a, parent_mod, pkg_a, &sym_table.scope_arena));
    try std.testing.expect(Visibility.pub_super.isVisibleFrom(child_mod, pkg_a, sibling_mod, pkg_a, &sym_table.scope_arena));
    try std.testing.expect(!Visibility.pub_super.isVisibleFrom(child_mod, pkg_a, cousin_mod, pkg_a, &sym_table.scope_arena));
    try std.testing.expect(Visibility.pub_pkg.isVisibleFrom(child_mod, pkg_a, cousin_mod, pkg_a, &sym_table.scope_arena));
    try std.testing.expect(!Visibility.pub_pkg.isVisibleFrom(child_mod, pkg_a, external_mod, pkg_b, &sym_table.scope_arena));
    try std.testing.expect(Visibility.public.isVisibleFrom(child_mod, pkg_a, external_mod, pkg_b, &sym_table.scope_arena));
}

test "test_stage4_trailing_mod_impl_extra_bounds_and_use_visibility_escalation" {
    const parser_mod = @import("parser.zig");
    const allocator = std.testing.allocator;

    // [1] Trailing `mod` / `impl` after top-level items must not overrun into `root` `extra_data`:
    const trailing_src =
        \\pub fn outer_alpha() -> i32 { return 1; }
        \\pub struct Counter { pub val: i32 }
        \\impl Counter {
        \\    pub fn bump(&mut self) { self.val += 1; }
        \\}
        \\pub mod sub_mod {
        \\    pub fn sub_only() -> i32 { return 2; }
        \\}
    ;
    var tok_buf = TokenBuffer.init(allocator);
    defer tok_buf.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    _ = try parser_mod.parseSource(
        trailing_src,
        FileId.fromInt(90),
        &tok_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        null,
    );
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);

    const fn_handles = try collectFileFnDeclHandles(allocator, trailing_src, &tok_buf, &cst_arena, &ast_arena);
    defer allocator.free(fn_handles);
    try std.testing.expectEqual(@as(usize, 3), fn_handles.len);

    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();

    const file_scope = try collectFileModuleItems(
        &sym_table,
        &interner,
        FileId.fromInt(90),
        trailing_src,
        &tok_buf,
        &cst_arena,
        &ast_arena,
        &sink,
    );
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    const sub_mod_sym = sym_table.lookupInScopeDirect(file_scope, try interner.intern("sub_mod"), NamespaceMask.VALUE_ONLY);
    try std.testing.expect(!sub_mod_sym.isNone());
    const sub_scope = sym_table.getSymbol(sub_mod_sym).target_scope;
    try std.testing.expect(
        sym_table.lookupInScopeDirect(sub_scope, try interner.intern("outer_alpha"), NamespaceMask.VALUE_ONLY).isNone(),
    );

    // [2] `pub use` of `pub(pkg)` item emits `E0433`, while `pub use sub.*` clamps visibility:
    const vis_src =
        \\mod inner {
        \\    pub(pkg) fn pkg_fn() -> i32 { return 1; }
        \\    pub fn pub_fn() -> i32 { return 2; }
        \\}
        \\pub mod glob_reexport {
        \\    pub use inner.*;
        \\}
        \\pub use inner.pkg_fn as bad_reexport;
    ;
    var vis_tok = TokenBuffer.init(allocator);
    defer vis_tok.deinit();
    var vis_cst = LosslessCstArena.init(allocator);
    defer vis_cst.deinit();
    var vis_ast = AstArena.init(allocator);
    defer vis_ast.deinit();
    var vis_sink = DiagnosticSink.init(allocator);
    defer vis_sink.deinit();

    _ = try parser_mod.parseSource(
        vis_src,
        FileId.fromInt(91),
        &vis_tok,
        &vis_cst,
        &vis_ast,
        &vis_sink,
        null,
    );
    const vis_scope = try collectFileModuleItems(
        &sym_table,
        &interner,
        FileId.fromInt(91),
        vis_src,
        &vis_tok,
        &vis_cst,
        &vis_ast,
        &vis_sink,
    );
    try resolveFileUseImports(
        &sym_table,
        &interner,
        FileId.fromInt(91),
        vis_src,
        &vis_tok,
        &vis_cst,
        &vis_sink,
    );

    var has_e0433 = false;
    for (vis_sink.diagnostics.items) |diag_item| {
        if (diag_item.code == .e0433_inaccessible_field_or_visibility) has_e0433 = true;
    }
    try std.testing.expect(has_e0433);

    const glob_mod_idx = sym_table.lookupInScopeDirect(vis_scope, try interner.intern("glob_reexport"), NamespaceMask.VALUE_ONLY);
    const glob_scope = sym_table.getSymbol(glob_mod_idx).target_scope;
    const clamped_pkg_idx = sym_table.lookupInScopeDirect(glob_scope, try interner.intern("pkg_fn"), NamespaceMask.VALUE_ONLY);
    const kept_pub_idx = sym_table.lookupInScopeDirect(glob_scope, try interner.intern("pub_fn"), NamespaceMask.VALUE_ONLY);
    try std.testing.expectEqual(Visibility.pub_pkg, sym_table.getSymbol(clamped_pkg_idx).visibility);
    try std.testing.expectEqual(Visibility.public, sym_table.getSymbol(kept_pub_idx).visibility);
}

test "test_phase8_cfg_11_target_sync_extern_blocks_kw_async_and_c_casing" {
    const parser_mod = @import("parser.zig");
    const allocator = std.testing.allocator;

    // [1] Verify `CfgEnv.fromTargetSpec` across `musl`, `freestanding`, `none`, `wasi`, `apple`, `msvc`, and `gnu`:
    const musl_env = CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_MUSL, false);
    try std.testing.expectEqual(CfgOs.linux, musl_env.os);
    try std.testing.expectEqual(CfgAbi.musl, musl_env.abi);

    const free_env = CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.WASM32_UNKNOWN_FREESTANDING, false);
    try std.testing.expectEqual(CfgOs.freestanding, free_env.os);
    try std.testing.expectEqual(CfgAbi.none, free_env.abi);
    try std.testing.expectEqual(@as(u16, 32), free_env.ptr_width);

    const wasi_env = CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.WASM32_UNKNOWN_WASI, false);
    try std.testing.expectEqual(CfgOs.wasi, wasi_env.os);
    try std.testing.expectEqual(CfgAbi.wasi, wasi_env.abi);

    const apple_env = CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.AARCH64_APPLE_DARWIN, false);
    try std.testing.expectEqual(CfgAbi.apple, apple_env.abi);

    // [2] Verify `@cfg(target.abi == "musl")` / `freestanding` / `none`, `c_*` casing exemption, `.kw_async`, & `extern` blocks:
    const ffi_src =
        \\@cfg(target.abi == "musl")
        \\pub fn only_on_musl() -> i32 { return 11; }
        \\@cfg(target.os == "freestanding" and target.abi == "none")
        \\pub fn only_on_freestanding() -> i32 { return 22; }
        \\
        \\@cfg(target.arch == "aarch64")
        \\pub type c_char = u8;
        \\@cfg(not (target.arch == "aarch64"))
        \\pub type c_char = i8;
        \\pub type c_schar = i8;
        \\pub type c_uchar = u8;
        \\pub type c_short = i16;
        \\pub type c_ushort = u16;
        \\pub type c_int = i32;
        \\pub type c_uint = u32;
        \\pub type c_long = i64;
        \\pub type c_ulong = u64;
        \\pub type c_longlong = i64;
        \\pub type c_ulonglong = u64;
        \\pub type c_longdouble = f64;
        \\pub type c_void = opaque;
        \\
        \\pub mod async {
        \\    pub fn task_group() -> i32 { return 7; }
        \\}
        \\use async.{ task_group };
        \\
        \\@link_lib("z")
        \\@trusted
        \\extern "C" {
        \\    pub fn zlib_version() -> *c_char;
        \\    @thread_local
        \\    pub static mut ERRNO_TLS: c_int;
        \\    pub static ZLIB_MAGIC: c_uint;
        \\    pub const Z_OK: c_int = 0;
        \\}
        \\@trusted
        \\pub extern "C" static TOP_EXTERN_VAL: c_int;
    ;

    var tok_buf = TokenBuffer.init(allocator);
    defer tok_buf.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();

    _ = try parser_mod.parseSource(ffi_src, FileId.fromInt(95), &tok_buf, &cst_arena, &ast_arena, &sink, &interner);

    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();
    sym_table.cfg_env = musl_env;
    const mod_scope = try collectFileModuleItems(
        &sym_table,
        &interner,
        FileId.fromInt(95),
        ffi_src,
        &tok_buf,
        &cst_arena,
        &ast_arena,
        &sink,
    );
    try resolveFileUseImports(&sym_table, &interner, FileId.fromInt(95), ffi_src, &tok_buf, &cst_arena, &sink);

    // Zero errors and zero `W0201` casing warnings on `c_*` aliases or `@cfg` `c_char` twins:
    try std.testing.expectEqual(@as(usize, 0), sink.countDiagnostics());

    // `@cfg(target.abi == "musl")` kept `only_on_musl` and pruned `only_on_freestanding`:
    try std.testing.expect(
        !sym_table.lookupInScopeDirect(mod_scope, try interner.intern("only_on_musl"), NamespaceMask.VALUE_ONLY).isNone(),
    );
    try std.testing.expect(
        sym_table.lookupInScopeDirect(mod_scope, try interner.intern("only_on_freestanding"), NamespaceMask.VALUE_ONLY).isNone(),
    );
    try std.testing.expect(
        !sym_table.lookupInScopeDirect(mod_scope, try interner.intern("c_char"), NamespaceMask.TYPE_ONLY).isNone(),
    );

    // `.kw_async` module and `use async.{ task_group };` resolved cleanly:
    const tg_alias = sym_table.lookupInScopeDirect(mod_scope, try interner.intern("task_group"), NamespaceMask.VALUE_ONLY);
    try std.testing.expect(!tg_alias.isNone());

    // Standalone `extern "C"` block members inherited `is_extern`, `@link_lib("z")`, `@trusted`, and `@thread_local`:
    const zlib_fn = sym_table.lookupInScopeDirect(mod_scope, try interner.intern("zlib_version"), NamespaceMask.VALUE_ONLY);
    try std.testing.expect(!zlib_fn.isNone());
    try std.testing.expect(sym_table.getSymbol(zlib_fn).flags.is_extern);
    const zlib_contract = sym_table.getFfiContract(zlib_fn).?;
    try std.testing.expect(zlib_contract.is_trusted);
    try std.testing.expectEqualStrings("z", interner.get(zlib_contract.link_lib_name));

    const errno_sym = sym_table.lookupInScopeDirect(mod_scope, try interner.intern("ERRNO_TLS"), NamespaceMask.VALUE_ONLY);
    try std.testing.expect(!errno_sym.isNone());
    try std.testing.expectEqual(SymbolKind.extern_static_sym, sym_table.getSymbol(errno_sym).kind);
    try std.testing.expect(sym_table.getSymbol(errno_sym).flags.is_extern);
    try std.testing.expect(sym_table.getSymbol(errno_sym).flags.is_mut);
    try std.testing.expect(sym_table.getFfiContract(errno_sym).?.is_thread_local);

    const z_ok_sym = sym_table.lookupInScopeDirect(mod_scope, try interner.intern("Z_OK"), NamespaceMask.CONST_ONLY);
    try std.testing.expect(!z_ok_sym.isNone());

    // [3] Re-run under `WASM32_UNKNOWN_FREESTANDING` to confirm `@cfg(target.os == "freestanding" and target.abi == "none")`:
    var free_sym_table = try SymbolTable.init(allocator, &interner);
    defer free_sym_table.deinit();
    free_sym_table.cfg_env = free_env;
    const free_scope = try collectFileModuleItems(
        &free_sym_table,
        &interner,
        FileId.fromInt(95),
        ffi_src,
        &tok_buf,
        &cst_arena,
        &ast_arena,
        &sink,
    );
    try std.testing.expect(
        !free_sym_table.lookupInScopeDirect(free_scope, try interner.intern("only_on_freestanding"), NamespaceMask.VALUE_ONLY).isNone(),
    );
    try std.testing.expect(
        free_sym_table.lookupInScopeDirect(free_scope, try interner.intern("only_on_musl"), NamespaceMask.VALUE_ONLY).isNone(),
    );
}

test "test_symbol_resolver_not_send_not_sync_flags_and_cx_ffi_target_refresh" {
    const parser_mod = @import("parser.zig");
    const allocator = std.testing.allocator;

    const conc_src =
        \\@not_send
        \\pub struct LocalHandle {
        \\    pub id: u32,
        \\}
        \\@not_sync
        \\pub struct InteriorCell {
        \\    pub val: i32,
        \\}
        \\@thread_local
        \\extern "C" {
        \\    pub static mut TLS_COUNTER: i32;
        \\}
    ;

    var tok_buf = TokenBuffer.init(allocator);
    defer tok_buf.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();

    _ = try parser_mod.parseSource(conc_src, FileId.fromInt(96), &tok_buf, &cst_arena, &ast_arena, &sink, &interner);

    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();
    const mod_scope = try collectFileModuleItems(
        &sym_table,
        &interner,
        FileId.fromInt(96),
        conc_src,
        &tok_buf,
        &cst_arena,
        &ast_arena,
        &sink,
    );
    try std.testing.expectEqual(@as(usize, 0), sink.countDiagnostics());

    const local_handle_idx = sym_table.lookupInScopeDirect(
        mod_scope,
        try interner.intern("LocalHandle"),
        NamespaceMask.TYPE_ONLY,
    );
    try std.testing.expect(!local_handle_idx.isNone());
    try std.testing.expect(sym_table.getSymbol(local_handle_idx).extra_flags.is_not_send);
    try std.testing.expect(!sym_table.getSymbol(local_handle_idx).extra_flags.is_not_sync);

    const interior_cell_idx = sym_table.lookupInScopeDirect(
        mod_scope,
        try interner.intern("InteriorCell"),
        NamespaceMask.TYPE_ONLY,
    );
    try std.testing.expect(!interior_cell_idx.isNone());
    try std.testing.expect(sym_table.getSymbol(interior_cell_idx).extra_flags.is_not_sync);
    try std.testing.expect(!sym_table.getSymbol(interior_cell_idx).extra_flags.is_not_send);

    const tls_idx = sym_table.lookupInScopeDirect(
        mod_scope,
        try interner.intern("TLS_COUNTER"),
        NamespaceMask.VALUE_ONLY,
    );
    try std.testing.expect(!tls_idx.isNone());
    try std.testing.expect(sym_table.getSymbol(tls_idx).extra_flags.is_thread_local);
    try std.testing.expect(sym_table.getFfiContract(tls_idx).?.is_thread_local);

    // Verify `ensureCxRootScope` + `refreshCxFfiTargetAliases` update `c_char`, `c_long`, and `c_ulong` in-place:
    sym_table.cfg_env = CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_GNU, false);
    const cx_root = try sym_table.ensureCxRootScope(&interner);
    const ffi_mod = sym_table.lookupInScopeDirect(cx_root, try interner.intern("ffi"), NamespaceMask.VALUE_ONLY);
    const ffi_scope = sym_table.getSymbol(ffi_mod).target_scope;
    const c_char_sym = sym_table.lookupInScopeDirect(ffi_scope, try interner.intern("c_char"), NamespaceMask.TYPE_ONLY);
    const c_long_sym = sym_table.lookupInScopeDirect(ffi_scope, try interner.intern("c_long"), NamespaceMask.TYPE_ONLY);
    const c_ulong_sym = sym_table.lookupInScopeDirect(ffi_scope, try interner.intern("c_ulong"), NamespaceMask.TYPE_ONLY);

    try std.testing.expectEqual(TypeId.i8_ty, sym_table.getSymbol(c_char_sym).type_id);
    try std.testing.expectEqual(TypeId.i64_ty, sym_table.getSymbol(c_long_sym).type_id);
    try std.testing.expectEqual(TypeId.u64_ty, sym_table.getSymbol(c_ulong_sym).type_id);

    sym_table.cfg_env = CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.AARCH64_LINUX_GNU, false);
    sym_table.refreshCxFfiTargetAliases(&interner);
    try std.testing.expectEqual(TypeId.u8_ty, sym_table.getSymbol(c_char_sym).type_id);
    try std.testing.expectEqual(TypeId.i64_ty, sym_table.getSymbol(c_long_sym).type_id);

    sym_table.cfg_env = CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.X86_64_WINDOWS_MSVC, false);
    _ = try sym_table.ensureCxRootScope(&interner);
    try std.testing.expectEqual(TypeId.i8_ty, sym_table.getSymbol(c_char_sym).type_id);
    try std.testing.expectEqual(TypeId.i32_ty, sym_table.getSymbol(c_long_sym).type_id);
    try std.testing.expectEqual(TypeId.u32_ty, sym_table.getSymbol(c_ulong_sym).type_id);
}

test "test_multi_package_scope_isolation_hygiene_and_inactive_cfg_caps" {
    const allocator = std.testing.allocator;
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();

    sym_table.is_flat_named_module_scopes_suppressed = true;
    const ext_pkg = PackageId.fromInt(2);
    const ext_fid = FileId.fromInt(20);
    try sym_table.setFilePackageId(ext_fid, ext_pkg);
    try sym_table.registerPackageFeatureManifest(ext_pkg);
    try sym_table.declarePackageFeature(ext_pkg, try interner.intern("tls"));

    const ext_src =
        "use cx.net as net_mod;\n" ++
        "@cfg(os == .Windows)\n" ++
        "use core.mem;\n" ++
        "@cfg(os == .Windows)\n" ++
        "@std_cap_boundary(clears: [net])\n" ++
        "pub fn win_backdoor() {\n" ++
        "    net_mod.connect();\n" ++
        "    asm(\"nop\");\n" ++
        "}\n" ++
        "@cfg(feature == \"typo_feat\")\n" ++
        "pub fn bad_feat() {}\n";

    var tokens = TokenBuffer.init(allocator);
    defer tokens.deinit();
    var cst = LosslessCstArena.init(allocator);
    defer cst.deinit();
    var ast = AstArena.init(allocator);
    defer ast.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    sym_table.cfg_env.os = .linux;
    _ = try parser.parseSource(ext_src, ext_fid, &tokens, &cst, &ast, &sink, &interner);
    const ext_root_scope = try collectFileModuleItems(
        &sym_table,
        &interner,
        ext_fid,
        ext_src,
        &tokens,
        &cst,
        &ast,
        &sink,
    );
    try sym_table.setPackageRootScope(ext_pkg, ext_root_scope);
    try resolveFileUseImports(&sym_table, &interner, ext_fid, ext_src, &tokens, &cst, &sink);

    var has_e0218 = false;
    var has_e0327 = false;
    for (sink.asSlice()) |diag_entry| {
        if (diag_entry.code == .e0218_direct_core_import_forbidden) has_e0218 = true;
        if (diag_entry.code == .e0327_forbidden_sandbox_bypass_attribute) has_e0327 = true;
    }
    try std.testing.expect(has_e0218);
    try std.testing.expect(has_e0327);

    const file_cfg = sym_table.effectiveCfgEnvForFile(ext_fid);
    const inactive_scan = scanFileInactiveCfgCapabilities(&file_cfg, ext_fid, ext_src, &tokens, &cst);
    try std.testing.expect((inactive_scan.pub_inactive_caps_bits & CapabilityBits.NET) != 0);
    try std.testing.expect((inactive_scan.pub_inactive_caps_bits & CapabilityBits.FFI) != 0);
    try std.testing.expect((inactive_scan.pub_inactive_caps_bits & CapabilityBits.UNSAFE_OP) != 0);

    // Verify qualified `core.<ident>` inside inactive `@cfg` (without `use core…;`) emits `E0218` + `http`/`sys`/top-level `asm`:
    const ext_fid_b = FileId.fromInt(21);
    try sym_table.setFilePackageId(ext_fid_b, ext_pkg);
    const ext_src_b =
        "@cfg(os == .Windows)\n" ++
        "pub fn win_only() {\n" ++
        "    core.mem.zero();\n" ++
        "    cx.http.fetch();\n" ++
        "}\n" ++
        "@cfg(os == .Windows)\n" ++
        "asm(\".section .init_array\");\n";
    var tokens_b = TokenBuffer.init(allocator);
    defer tokens_b.deinit();
    var cst_b = LosslessCstArena.init(allocator);
    defer cst_b.deinit();
    var ast_b = AstArena.init(allocator);
    defer ast_b.deinit();
    var sink_b = DiagnosticSink.init(allocator);
    defer sink_b.deinit();

    _ = try parser.parseSource(ext_src_b, ext_fid_b, &tokens_b, &cst_b, &ast_b, null, &interner);
    _ = try collectFileModuleItems(&sym_table, &interner, ext_fid_b, ext_src_b, &tokens_b, &cst_b, &ast_b, &sink_b);
    var has_inactive_core_e0218 = false;
    for (sink_b.asSlice()) |diag_entry| {
        if (diag_entry.code == .e0218_direct_core_import_forbidden) has_inactive_core_e0218 = true;
    }
    try std.testing.expect(has_inactive_core_e0218);

    const file_cfg_b = sym_table.effectiveCfgEnvForFile(ext_fid_b);
    const scan_b = scanFileInactiveCfgCapabilities(&file_cfg_b, ext_fid_b, ext_src_b, &tokens_b, &cst_b);
    try std.testing.expect((scan_b.pub_inactive_caps_bits & CapabilityBits.NET) != 0);
    try std.testing.expect((scan_b.link_ambient_inactive_caps_bits & CapabilityBits.FFI) != 0);
    try std.testing.expect((scan_b.link_ambient_inactive_caps_bits & CapabilityBits.UNSAFE_OP) != 0);
}

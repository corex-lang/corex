//! Zero-`libclang` C11/C23 Preprocessor, Tokenizer & Declaration Parser (`c_frontend`)
//!
//! Preprocesses and parses C11/C23 header files in-process into an arena-backed Structure-of-Arrays
//! `CTranslationUnit` without external C/C++ compiler libraries (`DR-10` §2.1–2.4, `DR-20` `Prune-06`,
//! `Reject-01`, and Seam Checklist #6).
//!
//! Enforces strict upper bounds (`MAX_C_TOKENS_PER_UNIT`, `MAX_MACRO_EXPANSION_STEPS`, `MAX_INCLUDE_DEPTH`,
//! and `MAX_C_PARSE_DEPTH`), emitting `E0009` (`e0009_c_header_translation_failed`) on any cap or C error.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const codegen_abi = @import("codegen_abi.zig");
const diagnostic = @import("diag/diagnostic.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const BumpArena = mem_foundation.BumpArena;
const TargetSpec = codegen_abi.TargetSpec;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const LabeledSpan = diagnostic.LabeledSpan;

// ---------------------------------------- TYPES ----------------------------------------

// ----------------------- Typed Handles ------------------------

/// Strongly typed 32-bit index into `CTranslationUnit.tokens`.
pub const CTokenId = enum(u32) {
    /// Sentinel value representing no C token.
    none = std.math.maxInt(u32),
    _,

    /// Wraps a raw 32-bit index into a `CTokenId`.
    pub inline fn fromInt(index: u32) CTokenId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit index of `self`.
    pub inline fn asInt(self: CTokenId) u32 {
        return @backingInt(self);
    }

    /// Returns `true` when `self` is `.none`.
    pub inline fn isNone(self: CTokenId) bool {
        return self == .none;
    }
};

/// Strongly typed 32-bit index into `CTranslationUnit.types`.
pub const CTypeId = enum(u32) {
    /// Sentinel value representing no C type.
    none = std.math.maxInt(u32),
    _,

    /// Wraps a raw 32-bit index into a `CTypeId`.
    pub inline fn fromInt(index: u32) CTypeId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit index of `self`.
    pub inline fn asInt(self: CTypeId) u32 {
        return @backingInt(self);
    }

    /// Returns `true` when `self` is `.none`.
    pub inline fn isNone(self: CTypeId) bool {
        return self == .none;
    }
};

/// Strongly typed 32-bit index into `CTranslationUnit.decls`.
pub const CDeclId = enum(u32) {
    /// Sentinel value representing no C declaration.
    none = std.math.maxInt(u32),
    _,

    /// Wraps a raw 32-bit index into a `CDeclId`.
    pub inline fn fromInt(index: u32) CDeclId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit index of `self`.
    pub inline fn asInt(self: CDeclId) u32 {
        return @backingInt(self);
    }

    /// Returns `true` when `self` is `.none`.
    pub inline fn isNone(self: CDeclId) bool {
        return self == .none;
    }
};

// --------------------- C Tokens & Macros ----------------------

/// Error set returned by the C11/C23 preprocessor and declaration parser.
pub const CFrontendError = error{
    /// Memory allocation failed.
    OutOfMemory,
    /// Fatal C translation failure already recorded as `E0009` in `DiagnosticSink`.
    TranslationFailed,
};

/// Lexical token classification for C11/C23 preprocessing and declaration parsing.
pub const CTokenKind = enum(u8) {
    /// Identifier or C keyword (`foo`, `struct`, `int`).
    ident = 0,
    /// Preprocessing or numeric literal (`42`, `0xFFULL`, `3.14f`).
    number = 1,
    /// String literal (`"hello"`, `L"wide"`, `u8"utf8"`).
    string_lit = 2,
    /// Character constant (`'a'`, `'\n'`, `'\x7F'`).
    char_lit = 3,
    /// `(` delimiter.
    lparen = 4,
    /// `)` delimiter.
    rparen = 5,
    /// `[` delimiter.
    lbracket = 6,
    /// `]` delimiter.
    rbracket = 7,
    /// `{` delimiter.
    lbrace = 8,
    /// `}` delimiter.
    rbrace = 9,
    /// `.` member punctuator.
    dot = 10,
    /// `->` pointer member punctuator.
    arrow = 11,
    /// `&` address/bitwise-AND punctuator.
    amp = 12,
    /// `&&` logical-AND punctuator.
    amp_amp = 13,
    /// `|=` or `&=` compound assignment punctuator.
    amp_eq = 14,
    /// `|` bitwise-OR punctuator.
    pipe = 15,
    /// `||` logical-OR punctuator.
    pipe_pipe = 16,
    /// `|=` compound assignment punctuator.
    pipe_eq = 17,
    /// `^` bitwise-XOR punctuator.
    caret = 18,
    /// `^=` compound assignment punctuator.
    caret_eq = 19,
    /// `~` bitwise complement punctuator.
    tilde = 20,
    /// `!` logical negation punctuator.
    bang = 21,
    /// `!=` inequality punctuator.
    bang_eq = 22,
    /// `+` addition punctuator.
    plus = 23,
    /// `++` increment punctuator.
    plus_plus = 24,
    /// `+=` compound assignment punctuator.
    plus_eq = 25,
    /// `-` subtraction punctuator.
    minus = 26,
    /// `--` decrement punctuator.
    minus_minus = 27,
    /// `-=` compound assignment punctuator.
    minus_eq = 28,
    /// `*` pointer/multiply punctuator.
    star = 29,
    /// `*=` compound assignment punctuator.
    star_eq = 30,
    /// `/` division punctuator.
    slash = 31,
    /// `/=` compound assignment punctuator.
    slash_eq = 32,
    /// `%` remainder punctuator.
    percent = 33,
    /// `%=` compound assignment punctuator.
    percent_eq = 34,
    /// `<` less-than punctuator.
    lt = 35,
    /// `<=` less-or-equal punctuator.
    le = 36,
    /// `<<` left-shift punctuator.
    shl = 37,
    /// `<<=` compound assignment punctuator.
    shl_eq = 38,
    /// `>` greater-than punctuator.
    gt = 39,
    /// `>=` greater-or-equal punctuator.
    ge = 40,
    /// `>>` right-shift punctuator.
    shr = 41,
    /// `>>=` compound assignment punctuator.
    shr_eq = 42,
    /// `=` assignment punctuator.
    eq = 43,
    /// `==` equality punctuator.
    eq_eq = 44,
    /// `?` ternary conditional punctuator.
    question = 45,
    /// `:` bitfield/label/ternary punctuator.
    colon = 46,
    /// `::` C23 scoped attribute punctuator (`[[gnu::packed]]`).
    colon_colon = 47,
    /// `;` statement/declaration terminator.
    semi = 48,
    /// `,` separator punctuator.
    comma = 49,
    /// `...` variadic ellipsis punctuator.
    ellipses = 50,
    /// `#` preprocessor directive / stringize punctuator.
    hash = 51,
    /// `##` preprocessor token-paste punctuator.
    hash_hash = 52,
    /// Synthetic `#pragma pack(…)` directive marker preserved for struct layout parsing.
    pragma_pack = 53,
    /// End-of-translation-unit sentinel token.
    eof = 54,
};

/// 64-bit $O(1)$ membership bitmask over `CTokenKind` (`0..54`).
const CTokenMask64 = u64;

comptime {
    std.debug.assert(std.enums.values(CTokenKind).len <= 64);
    std.debug.assert(@backingInt(CTokenKind.eof) < 64);
}

/// `#pragma pack` stack operation attached to `.pragma_pack` tokens.
pub const PragmaPackOp = enum(u8) {
    /// Reset packing to target default (`#pragma pack()`).
    reset_pack = 0,
    /// Set active pack alignment (`#pragma pack(N)`).
    set_pack = 1,
    /// Push current pack alignment without changing it (`#pragma pack(push)`).
    push_only = 2,
    /// Push current pack alignment and set new alignment (`#pragma pack(push, N)`).
    push_pack = 3,
    /// Pop previous pack alignment (`#pragma pack(pop)`).
    pop_pack = 4,
};

/// Preprocessed or raw C lexical token stored in `CTranslationUnit.tokens`.
pub const CToken = struct {
    /// Token discriminant.
    kind: CTokenKind,
    /// Arena-owned UTF-8 lexeme slice.
    lexeme: []const u8,
    /// Source byte span (`Span.ZERO` for predefined macros).
    span: Span = Span.ZERO,
    /// `true` if this token appeared first on a physical/logical line before any non-space token.
    is_at_line_start: bool = false,
    /// `true` if whitespace or a comment immediately preceded this token on the same line.
    has_leading_space: bool = false,
    /// `true` if expanded or scanned from a bundled virtual system header.
    is_from_system_header: bool = false,
    /// Packing operation when `kind == .pragma_pack`.
    pack_op: PragmaPackOp = .reset_pack,
    /// Requested power-of-two byte alignment (`1`, `2`, `4`, `8`, `16`) when `kind == .pragma_pack`.
    pack_align: u8 = 0,
};

/// Command-line or programmatic `-DNAME` / `-DNAME=VAL` macro definition.
pub const MacroDefine = struct {
    /// Macro identifier name.
    name: []const u8,
    /// Optional replacement text (`null` defaults to `"1"` matching `-DNAME`).
    value: ?[]const u8 = null,
};

/// In-memory virtual header file entry for hermetic testing and `CompilerDb` overlays.
pub const VirtualHeaderEntry = struct {
    /// Normalized header path (e.g., `"my_lib.h"` or `"sub/defs.h"`).
    path: []const u8,
    /// UTF-8 header source contents.
    content: []const u8,
};

/// Strongly typed `#include` file resolution backend (zero untyped pointers).
pub const CIncludeLoader = union(enum) {
    /// Resolve strictly against `virtual_headers` and `BUNDLED_SYSTEM_HEADERS`.
    none,
    /// Resolve against `VfsSourceMap` virtual/mounted files before bundled headers.
    vfs: *vfs_sourcemap.VfsSourceMap,
    /// Resolve against the host filesystem via `std.Io` across `include_dirs`.
    host_fs: std.Io,
};

/// Classified scalar or string value of an object-like `#define` constant.
pub const MacroConstValue = union(enum) {
    /// Signed 64-bit integer constant.
    signed_int: i64,
    /// Unsigned 64-bit integer constant.
    unsigned_int: u64,
    /// IEEE-754 64-bit floating-point constant.
    float_val: f64,
    /// Decoded UTF-8 string literal constant.
    string_val: []const u8,
};

/// Promoted object-like `#define` constant recorded for `pub const` emission in `c_translate`.
pub const RecordedMacroConst = struct {
    /// Arena-owned macro identifier.
    name: []const u8,
    /// Evaluated scalar or string constant payload.
    value: MacroConstValue,
    /// Source span of the `#define` directive.
    span: Span,
    /// `true` when defined inside a bundled system header (`<stdint.h>`, `<limits.h>`, etc.).
    is_from_system_header: bool,
};

// -------------------- C Types & Contracts ---------------------

/// Pointer/callback nullability contract extracted from Clang `_Nonnull`/`_Nullable` or SAL.
pub const CNullability = enum(u8) {
    /// Unannotated C pointer (`*T` / `*mut T` raw pointer, `(extern "C" fn…)?` callback).
    unspecified = 0,
    /// Proven/contracted non-null (`_Nonnull`, `__attribute__((nonnull))`, `_In_`, `_Out_`).
    non_null = 1,
    /// Explicitly nullable (`_Nullable`, `_In_opt_`, `_Out_opt_`, `_Ret_maybenull_`).
    may_be_null = 2,
};

/// Windows PE/COFF DLL symbol visibility storage modifier (`__declspec(dllexport|dllimport)`).
pub const CDllStorage = enum(u8) {
    /// Standard C external linkage.
    none = 0,
    /// `__declspec(dllexport)` exported symbol.
    dllexport = 1,
    /// `__declspec(dllimport)` imported symbol.
    dllimport = 2,
};

/// FFI boundary SAST contract metadata extracted from Clang attributes and Microsoft SAL.
pub const CFfiContract = struct {
    /// Nullability annotation (`_Nonnull` vs `_Nullable`).
    nullability: CNullability = .unspecified,
    /// `true` for NUL-terminated string contracts (`_In_z_`, `_In_opt_z_`).
    is_null_terminated: bool = false,
    /// `true` for uninitialized out-parameter contracts (`_Out_`, `_Out_opt_`, `_Out_writes_`).
    is_out_param: bool = false,
    /// `true` for caller-owned allocation returns (`__attribute__((malloc))`).
    is_owned_by_caller: bool = false,
    /// Coupled length parameter/field identifier (`counted_by(n)`, `_In_reads_(n)`, `_Out_writes_(n)`).
    slice_len_param: []const u8 = "",
    /// Paired deallocator function name (`__attribute__((malloc(free_fn)))`).
    free_with_fn: []const u8 = "",
};

/// Canonical C primitive and exact-width standard typedef specifiers.
pub const CPrimitiveKind = enum(u8) {
    /// C `void`.
    c_void = 0,
    /// C11 `_Bool` / C23 `bool`.
    c_bool = 1,
    /// Plain C `char` (signedness governed by `target.isCCharSigned()`).
    c_char = 2,
    /// Explicit `signed char`.
    c_schar = 3,
    /// Explicit `unsigned char`.
    c_uchar = 4,
    /// `short` / `signed short`.
    c_short = 5,
    /// `unsigned short`.
    c_ushort = 6,
    /// `int` / `signed int`.
    c_int = 7,
    /// `unsigned` / `unsigned int`.
    c_uint = 8,
    /// `long` / `signed long` (`4B` on Windows/Wasm32, `8B` on 64-bit POSIX).
    c_long = 9,
    /// `unsigned long` (`4B` on Windows/Wasm32, `8B` on 64-bit POSIX).
    c_ulong = 10,
    /// `long long` / `signed long long` (`8B`).
    c_longlong = 11,
    /// `unsigned long long` (`8B`).
    c_ulonglong = 12,
    /// GNU/Clang `__int128` (`16B`).
    c_int128 = 13,
    /// GNU/Clang `unsigned __int128` (`16B`).
    c_uint128 = 14,
    /// IEEE-754 `float` (`4B`).
    c_float = 15,
    /// IEEE-754 `double` (`8B`).
    c_double = 16,
    /// Platform `long double` (`8B` on MSVC/Apple ARM64, `16B` elsewhere).
    c_longdouble = 17,
    /// `<stdint.h>` exact `int8_t` (`i8`).
    exact_i8 = 18,
    /// `<stdint.h>` exact `uint8_t` (`u8`).
    exact_u8 = 19,
    /// `<stdint.h>` exact `int16_t` (`i16`).
    exact_i16 = 20,
    /// `<stdint.h>` exact `uint16_t` (`u16`).
    exact_u16 = 21,
    /// `<stdint.h>` exact `int32_t` (`i32`).
    exact_i32 = 22,
    /// `<stdint.h>` exact `uint32_t` (`u32`).
    exact_u32 = 23,
    /// `<stdint.h>` exact `int64_t` (`i64`).
    exact_i64 = 24,
    /// `<stdint.h>` exact `uint64_t` (`u64`).
    exact_u64 = 25,
    /// `<stddef.h>` / `<stdint.h>` pointer-width signed (`ssize_t`, `ptrdiff_t`, `intptr_t` -> `isize`).
    exact_isize = 26,
    /// `<stddef.h>` / `<stdint.h>` pointer-width unsigned (`size_t`, `uintptr_t` -> `usize`).
    exact_usize = 27,
    /// `<stdarg.h>` `va_list` / `__builtin_va_list` (`VaList`).
    va_list = 28,

    /// Returns the target ABI byte width of `self` on `target`.
    pub fn byteSize(self: CPrimitiveKind, target: TargetSpec) u32 {
        return switch (self) {
            .c_void => 0,
            .c_bool, .c_char, .c_schar, .c_uchar, .exact_i8, .exact_u8 => 1,
            .c_short, .c_ushort, .exact_i16, .exact_u16 => 2,
            .c_int, .c_uint, .exact_i32, .exact_u32, .c_float => 4,
            .c_long, .c_ulong => target.cLongByteSize(),
            .c_longlong, .c_ulonglong, .exact_i64, .exact_u64, .c_double => 8,
            .c_int128, .c_uint128 => 16,
            .c_longdouble => if ((target.os == .windows and target.abi == .msvc) or
                (target.arch == .aarch64 and target.os == .macos)) 8 else 16,
            .exact_isize, .exact_usize => target.ptrBytes(),
            .va_list => if (target.arch == .x86_64 and (target.os == .linux or target.os == .macos))
                24
            else if (target.arch == .aarch64 and target.os == .linux)
                32
            else
                target.ptrBytes(),
        };
    }

    /// Returns the natural target ABI alignment in bytes of `self` on `target`.
    pub fn alignBytes(self: CPrimitiveKind, target: TargetSpec) u32 {
        return switch (self) {
            .c_void => 1,
            .va_list => target.ptrBytes(),
            else => @min(self.byteSize(target), 16),
        };
    }

    /// Returns `true` when `self` is an integer or `_Bool` primitive valid as a bitfield storage unit.
    pub fn isInteger(self: CPrimitiveKind) bool {
        return switch (self) {
            .c_void, .c_float, .c_double, .c_longdouble, .va_list => false,
            else => true,
        };
    }

    /// Returns `true` when `self` represents a signed integer on `target` (for bitfield sign-extension).
    pub fn isSignedInteger(self: CPrimitiveKind, target: TargetSpec) bool {
        return switch (self) {
            .c_char => target.isCCharSigned(),
            .c_schar, .c_short, .c_int, .c_long, .c_longlong, .c_int128 => true,
            .exact_i8, .exact_i16, .exact_i32, .exact_i64, .exact_isize => true,
            else => false,
        };
    }
};

/// Canonical C type node stored in `CTranslationUnit.types`.
pub const CTypeNode = union(enum) {
    /// Scalar, `void`, exact-width integer, or `va_list` primitive.
    primitive: CPrimitiveKind,
    /// Pointer type (`*T` when `is_const`, `*mut T` when `!is_const`).
    pointer: struct {
        /// Pointee `CTypeId`.
        pointee: CTypeId,
        /// `true` when the pointee is `const`-qualified (`const T *`).
        is_const: bool = false,
        /// `true` when the pointee is `volatile`-qualified.
        is_volatile: bool = false,
        /// `true` when the pointer itself is `restrict`-qualified.
        is_restrict: bool = false,
        /// Pointer nullability contract (`_Nonnull` / `_Nullable`).
        nullability: CNullability = .unspecified,
    },
    /// Fixed-size or incomplete flexible array (`T[N]` or `T[]`).
    array: struct {
        /// Element `CTypeId`.
        elem: CTypeId,
        /// Element count (`null` for incomplete `T[]`).
        len: ?u64,
    },
    /// Function signature type (used behind function pointers `R (*)(P…)`).
    function: struct {
        /// Return `CTypeId`.
        return_type: CTypeId,
        /// Start index in `CTranslationUnit.params`.
        param_start: u32,
        /// Number of formal parameters in `CTranslationUnit.params`.
        param_len: u32,
        /// `true` when prototype ends with `, ...`.
        is_variadic: bool,
        /// `true` when annotated `_Noreturn` / `[[noreturn]]` / `__attribute__((noreturn))`.
        is_noreturn: bool = false,
    },
    /// Reference to a `struct` or `union` declaration in `CTranslationUnit.decls`.
    record_ref: CDeclId,
    /// Reference to an `enum` declaration in `CTranslationUnit.decls`.
    enum_ref: CDeclId,
    /// Reference to a `typedef` declaration in `CTranslationUnit.decls`.
    typedef_ref: CDeclId,
    /// C11 `_Atomic(T)` qualified value type.
    atomic_val: CTypeId,
};

// --------------------- C AST Declarations ---------------------

/// Layout attributes attached to a C `struct` or `union` declaration (`Prune-06`).
pub const CRecordLayoutAttrs = struct {
    /// `true` for `__attribute__((packed))` or `[[gnu::packed]]`.
    is_packed: bool = false,
    /// `true` for `__attribute__((ms_struct))` forcing MSVC bitfield rules on non-Windows targets.
    is_ms_struct: bool = false,
    /// `true` for `__attribute__((gcc_struct))` forcing SysV/Itanium bitfield rules on Windows.
    is_gcc_struct: bool = false,
    /// Active `#pragma pack(N)` cap at struct definition (`0` = no pragma pack cap).
    pragma_pack: u8 = 0,
    /// Explicit over-alignment from `alignas(N)` / `__attribute__((aligned(N)))` (`0` = natural).
    explicit_align: u32 = 0,
};

/// Single member field or bitfield inside a C `struct` or `union`.
pub const CStructField = struct {
    /// Field identifier (`""` for unnamed bitfields or unnamed nested `struct`/`union` members).
    name: []const u8,
    /// Declared field `CTypeId`.
    type_id: CTypeId,
    /// Bitfield width (`0..64`), or `null` for standard non-bitfield members.
    bit_width: ?u16 = null,
    /// Explicit field alignment override (`_Alignas(N)` / `__attribute__((aligned(N)))`, `0` = none).
    explicit_align: u32 = 0,
    /// `true` when this specific field carries `__attribute__((packed))`.
    is_packed_field: bool = false,
    /// `true` when this member is an inline unnamed `struct { … };` or `union { … };`.
    is_anonymous_record: bool = false,
    /// SAL / `counted_by` contract metadata on pointer fields.
    contract: CFfiContract = .{},
    /// Source span of the field declaration.
    span: Span = Span.ZERO,
};

/// Single enumerator constant inside a C `enum` declaration.
pub const CEnumVariant = struct {
    /// Enumerator identifier (`SCREAMING_SNAKE_CASE` or mixed C case).
    name: []const u8,
    /// Resolved compile-time integer value (`i128` covering full signed/unsigned 64-bit C23 enums).
    value: i128,
    /// `true` when an explicit `= ConstExpr` was written in the C source.
    has_explicit_value: bool,
    /// Source span of the enumerator.
    span: Span = Span.ZERO,
};

/// Formal parameter in a C function prototype or function-pointer declarator.
pub const CFnParam = struct {
    /// Parameter identifier (`""` for unnamed prototype parameters such as `int foo(int)`).
    name: []const u8,
    /// Parameter `CTypeId` (after C11 array-to-pointer and function-to-pointer decay).
    type_id: CTypeId,
    /// FFI nullability, SAL, and `counted_by` boundary contract metadata.
    contract: CFfiContract = .{},
    /// Source span of the parameter.
    span: Span = Span.ZERO,
};

/// Top-level C declaration payload stored in `CDecl`.
pub const CDeclKind = union(enum) {
    /// `struct` or `union` tag declaration (forward opaque or complete).
    record_decl: struct {
        /// `true` for `union`, `false` for `struct`.
        is_union: bool,
        /// Tag identifier (`""` for anonymous `typedef struct { … } Alias;`).
        name: []const u8,
        /// `true` once a `{ … }` member body has been parsed.
        is_complete: bool,
        /// Start index in `CTranslationUnit.fields`.
        field_start: u32,
        /// Number of fields in `CTranslationUnit.fields`.
        field_len: u32,
        /// Packing and ABI struct-layout attributes.
        layout_attrs: CRecordLayoutAttrs = .{},
    },
    /// `enum` declaration (named or anonymous, optional C23 `: UnderlyingInt`).
    enum_decl: struct {
        /// Tag identifier (`""` for anonymous `enum { … }` or `typedef enum { … } Alias;`).
        name: []const u8,
        /// Explicit C23 fixed underlying integer primitive (`null` for standard C11 enums).
        underlying_prim: ?CPrimitiveKind,
        /// `true` once `{ … }` enumerators have been parsed.
        is_complete: bool,
        /// Start index in `CTranslationUnit.enum_variants`.
        variant_start: u32,
        /// Number of enumerators in `CTranslationUnit.enum_variants`.
        variant_len: u32,
    },
    /// `typedef` alias declaration.
    typedef_decl: struct {
        /// Declared alias name.
        name: []const u8,
        /// Target `CTypeId`.
        target_type: CTypeId,
    },
    /// Function prototype or inline header function declaration.
    fn_decl: struct {
        /// C function symbol name.
        name: []const u8,
        /// Return `CTypeId`.
        return_type: CTypeId,
        /// Start index in `CTranslationUnit.params`.
        param_start: u32,
        /// Number of formal parameters in `CTranslationUnit.params`.
        param_len: u32,
        /// `true` when prototype ends with `, ...`.
        is_variadic: bool,
        /// `true` when declared `static` (internal TU linkage).
        is_static: bool,
        /// `true` when declared `inline` / `__inline` / `__forceinline`.
        is_inline: bool,
        /// `true` when annotated `_Noreturn` / `[[noreturn]]` / `__attribute__((noreturn))`.
        is_noreturn: bool,
        /// `true` when followed by a `{ … }` body skipped via `DR-20` Seam #6.
        has_body: bool,
        /// Opening `{` token index when `has_body == true` (`.none` otherwise).
        body_first_token: CTokenId = .none,
        /// Exclusive token index past closing `}` when `has_body == true` (`.none` otherwise).
        body_end_token: CTokenId = .none,
        /// Return-value FFI ownership/nullability contract (`malloc`, `_Ret_maybenull_`, etc.).
        ret_contract: CFfiContract = .{},
        /// Optional `__declspec(dllexport|dllimport)`.
        dll_storage: CDllStorage = .none,
    },
    /// External global variable or `static const` header constant declaration.
    var_decl: struct {
        /// Variable or constant name.
        name: []const u8,
        /// Declared `CTypeId`.
        type_id: CTypeId,
        /// `true` when declared `extern`.
        is_extern: bool,
        /// `true` when declared `static`.
        is_static: bool,
        /// `true` when top-level storage value itself is `const`-qualified.
        is_const: bool,
        /// Evaluated initializer for `static const` / `const` header constants (`null` otherwise).
        const_val: ?MacroConstValue = null,
        /// Optional `__declspec(dllexport|dllimport)`.
        dll_storage: CDllStorage = .none,
    },
};

/// Top-level C declaration entry in `CTranslationUnit.decls`.
pub const CDecl = struct {
    /// Tagged declaration payload.
    kind: CDeclKind,
    /// Primary source span.
    span: Span = Span.ZERO,
    /// `true` if parsed inside a bundled system header.
    is_from_system_header: bool = false,
};

// ---------------------- Frontend Options ----------------------

/// Optional Phase 13.3 C function-body AST transpilation hook (`DR-20` Seam Checklist #6).
pub const CFunctionBodyHook = *const fn (
    unit: *const CTranslationUnit,
    decl_id: CDeclId,
    body_first_token: CTokenId,
    body_end_token: CTokenId,
    sink: *DiagnosticSink,
) CFrontendError!void;

/// Configuration options for preprocessing and parsing a C11/C23 translation unit.
pub const CFrontendOptions = struct {
    /// Target architecture, OS, and C ABI governing predefined macros and primitive widths.
    target: TargetSpec = TargetSpec.X86_64_LINUX_GNU,
    /// User `-DNAME` / `-DNAME=VAL` macro definitions applied after target predefined macros.
    defines: []const MacroDefine = &.{},
    /// Ordered `-Idir` search directories for `#include` resolution.
    include_dirs: []const []const u8 = &.{},
    /// In-memory virtual headers checked before filesystem / bundled system headers.
    virtual_headers: []const VirtualHeaderEntry = &.{},
    /// Optional VFS or host filesystem loader for `#include` resolution.
    include_loader: CIncludeLoader = .none,
    /// Optional Phase 13.3 C function-body transpilation hook (`null` in Phase 8 per `DR-20` Seam #6).
    body_hook: ?CFunctionBodyHook = null,
    /// Bounded token cap per translation unit (`AGENTS.md` §2).
    max_tokens: u32 = MAX_C_TOKENS_PER_UNIT,
    /// Bounded macro expansion step cap (`AGENTS.md` §2).
    max_macro_steps: u32 = MAX_MACRO_EXPANSION_STEPS,
    /// Bounded `#include` nesting depth cap (`AGENTS.md` §2).
    max_include_depth: u32 = MAX_INCLUDE_DEPTH,
    /// Bounded recursive C declarator/type/expression parse depth cap (`AGENTS.md` §2).
    max_parse_depth: u32 = MAX_C_PARSE_DEPTH,
};

/// Target-calibrated C ABI byte size and natural alignment pair for a C type or record.
pub const CRecordByteLayout = struct {
    /// Total ABI byte size (`sizeof`).
    size_bytes: u64,
    /// Required ABI byte alignment (`alignof`).
    align_bytes: u32,
};

/// Arena-backed Structure-of-Arrays C11/C23 translation unit consumed by `c_translate`.
pub const CTranslationUnit = struct {
    /// Backing general allocator for dynamic SoA arrays.
    allocator: std.mem.Allocator,
    /// Contiguous bump arena owning all cloned identifier, string, and macro lexemes.
    arena: BumpArena,
    /// Target specification used during preprocessing and parsing.
    target: TargetSpec,
    /// Flat preprocessed C token stream indexed by `CTokenId`.
    tokens: std.ArrayListUnmanaged(CToken) = .empty,
    /// Flat C type table indexed by `CTypeId`.
    types: std.ArrayListUnmanaged(CTypeNode) = .empty,
    /// Flat struct/union field pool sliced by `record_decl`.
    fields: std.ArrayListUnmanaged(CStructField) = .empty,
    /// Flat function parameter pool sliced by `fn_decl` and `CTypeNode.function`.
    params: std.ArrayListUnmanaged(CFnParam) = .empty,
    /// Flat enum variant pool sliced by `enum_decl`.
    enum_variants: std.ArrayListUnmanaged(CEnumVariant) = .empty,
    /// Ordered top-level C declarations indexed by `CDeclId`.
    decls: std.ArrayListUnmanaged(CDecl) = .empty,
    /// Simple scalar and string `#define` constants preserved from preprocessing.
    macro_consts: std.ArrayListUnmanaged(RecordedMacroConst) = .empty,
    /// `true` if any `E0009` error was emitted during preprocessing or parsing.
    has_errors: bool = false,

    /// Initializes an empty `CTranslationUnit` for `target`.
    pub fn init(allocator: std.mem.Allocator, target: TargetSpec) CTranslationUnit {
        return .{
            .allocator = allocator,
            .arena = BumpArena.init(allocator),
            .target = target,
        };
    }

    /// Releases all SoA tables and arena slabs owned by `self`.
    pub fn deinit(self: *CTranslationUnit) void {
        self.tokens.deinit(self.allocator);
        self.types.deinit(self.allocator);
        self.fields.deinit(self.allocator);
        self.params.deinit(self.allocator);
        self.enum_variants.deinit(self.allocator);
        self.decls.deinit(self.allocator);
        self.macro_consts.deinit(self.allocator);
        self.arena.deinit();
        self.* = undefined;
    }

    /// Appends a `CTypeNode` and returns its `CTypeId`.
    pub fn appendType(self: *CTranslationUnit, node: CTypeNode) !CTypeId {
        const type_id = CTypeId.fromInt(@intCast(self.types.items.len));
        try self.types.append(self.allocator, node);
        return type_id;
    }

    /// Retrieves `CTypeNode` for `type_id` in $O(1)$ time.
    pub inline fn getType(self: *const CTranslationUnit, type_id: CTypeId) CTypeNode {
        return self.types.items[type_id.asInt()];
    }

    /// Unwraps chained `typedef_ref` and `atomic_val` wrappers to the underlying concrete `CTypeId`.
    pub fn unwrapTypedefs(self: *const CTranslationUnit, start_type: CTypeId) CTypeId {
        var cursor = start_type;
        var guard: u32 = 0;
        while (!cursor.isNone() and cursor.asInt() < self.types.items.len and guard < MAX_C_PARSE_DEPTH) : (guard += 1) {
            switch (self.types.items[cursor.asInt()]) {
                .typedef_ref => |td_decl_id| {
                    const decl = self.decls.items[td_decl_id.asInt()];
                    if (decl.kind == .typedef_decl) {
                        cursor = decl.kind.typedef_decl.target_type;
                    } else {
                        break;
                    }
                },
                .atomic_val => |inner_id| cursor = inner_id,
                else => break,
            }
        }
        return cursor;
    }

    /// Computes exact target C ABI `sizeof(T)` for `type_id` with bounded recursion `depth`.
    pub fn computeTypeByteSize(self: *const CTranslationUnit, type_id: CTypeId, depth: u32) u64 {
        if (depth > MAX_C_PARSE_DEPTH or type_id.isNone() or type_id.asInt() >= self.types.items.len) return 0;
        const canon_id = self.unwrapTypedefs(type_id);
        if (canon_id.isNone() or canon_id.asInt() >= self.types.items.len) return 0;
        return switch (self.getType(canon_id)) {
            .primitive => |prim| prim.byteSize(self.target),
            .pointer => self.target.ptrBytes(),
            .enum_ref => |ed_id| blk: {
                const ed = self.getDecl(ed_id).kind.enum_decl;
                if (ed.underlying_prim) |up| break :blk up.byteSize(self.target);
                break :blk 4;
            },
            .array => |arr| if (arr.len) |n| n *| self.computeTypeByteSize(arr.elem, depth + 1) else 0,
            .record_ref => |rec_id| self.computeRecordByteLayout(rec_id, depth + 1).size_bytes,
            .function, .atomic_val, .typedef_ref => self.target.ptrBytes(),
        };
    }

    /// Computes natural target C ABI `alignof(T)` for `type_id` with bounded recursion `depth`.
    pub fn computeTypeNaturalAlign(self: *const CTranslationUnit, type_id: CTypeId, depth: u32) u32 {
        if (depth > MAX_C_PARSE_DEPTH or type_id.isNone() or type_id.asInt() >= self.types.items.len) return 1;
        const canon_id = self.unwrapTypedefs(type_id);
        if (canon_id.isNone() or canon_id.asInt() >= self.types.items.len) return 1;
        return switch (self.getType(canon_id)) {
            .primitive => |prim| prim.alignBytes(self.target),
            .pointer => self.target.ptrBytes(),
            .enum_ref => |ed_id| blk: {
                const ed = self.getDecl(ed_id).kind.enum_decl;
                if (ed.underlying_prim) |up| break :blk up.alignBytes(self.target);
                break :blk 4;
            },
            .array => |arr| self.computeTypeNaturalAlign(arr.elem, depth + 1),
            .record_ref => |rec_id| self.computeRecordByteLayout(rec_id, depth + 1).align_bytes,
            .function, .atomic_val, .typedef_ref => self.target.ptrBytes(),
        };
    }

    /// Computes canonical target C ABI `(size_bytes, align_bytes)` for `rec_id` across all 11 targets.
    pub fn computeRecordByteLayout(
        self: *const CTranslationUnit,
        rec_id: CDeclId,
        depth: u32,
    ) CRecordByteLayout {
        if (depth > MAX_C_PARSE_DEPTH or rec_id.isNone() or rec_id.asInt() >= self.decls.items.len) {
            return .{ .size_bytes = 0, .align_bytes = 1 };
        }
        const decl = self.getDecl(rec_id);
        if (decl.kind != .record_decl) return .{ .size_bytes = 0, .align_bytes = 1 };
        const rec = decl.kind.record_decl;
        if (!rec.is_complete) return .{ .size_bytes = 0, .align_bytes = 1 };

        const fields = self.getFields(rec.field_start, rec.field_len);
        const pragma_pack_cap: u32 = if (rec.layout_attrs.pragma_pack > 0) rec.layout_attrs.pragma_pack else 0;
        var max_align: u32 = @max(@as(u32, 1), rec.layout_attrs.explicit_align);
        const is_ms_bitfields = (self.target.os == .windows and !rec.layout_attrs.is_gcc_struct) or
            rec.layout_attrs.is_ms_struct;
        const is_aapcs64_linux = self.target.arch == .aarch64 and self.target.os == .linux;

        if (rec.is_union) {
            var max_size: u64 = 0;
            for (fields) |field| {
                const nat_al = self.computeTypeNaturalAlign(field.type_id, depth + 1);
                const pragma_only_al = if (pragma_pack_cap > 0) @min(nat_al, pragma_pack_cap) else nat_al;
                const is_fld_packed = rec.layout_attrs.is_packed or field.is_packed_field;
                var eff_al: u32 = if (is_fld_packed) 1 else pragma_only_al;
                eff_al = @max(eff_al, field.explicit_align);
                if (field.bit_width) |bw| {
                    if (bw == 0) {
                        if (is_aapcs64_linux) {
                            max_align = @max(max_align, pragma_only_al);
                        }
                        continue;
                    }
                    max_align = @max(max_align, eff_al);
                    const unit_sz = @max(self.computeTypeByteSize(field.type_id, depth + 1), 1);
                    const bf_bytes = if (is_fld_packed and !is_ms_bitfields) (bw + 7) / 8 else unit_sz;
                    max_size = @max(max_size, bf_bytes);
                } else {
                    max_align = @max(max_align, eff_al);
                    max_size = @max(max_size, self.computeTypeByteSize(field.type_id, depth + 1));
                }
            }
            return .{
                .size_bytes = std.mem.alignForward(u64, max_size, max_align),
                .align_bytes = max_align,
            };
        }

        if (is_ms_bitfields) {
            var cur_bytes: u64 = 0;
            var has_unit = false;
            var unit_off: u64 = 0;
            var unit_sz: u64 = 0;
            var unit_bits: u64 = 0;

            for (fields) |field| {
                const nat_al = self.computeTypeNaturalAlign(field.type_id, depth + 1);
                const pragma_only_al = if (pragma_pack_cap > 0) @min(nat_al, pragma_pack_cap) else nat_al;
                const is_fld_packed = rec.layout_attrs.is_packed or field.is_packed_field;
                var eff_al: u32 = if (is_fld_packed) 1 else pragma_only_al;
                eff_al = @max(eff_al, field.explicit_align);
                const field_sz = self.computeTypeByteSize(field.type_id, depth + 1);

                if (field.bit_width) |bw| {
                    if (bw == 0) {
                        if (has_unit) {
                            cur_bytes = unit_off + unit_sz;
                            has_unit = false;
                        }
                        continue;
                    }
                    max_align = @max(max_align, eff_al);
                    const req_unit_sz = @max(field_sz, 1);
                    if (!has_unit or unit_sz != req_unit_sz or unit_bits + bw > unit_sz * 8) {
                        if (has_unit) cur_bytes = unit_off + unit_sz;
                        cur_bytes = std.mem.alignForward(u64, cur_bytes, eff_al);
                        unit_off = cur_bytes;
                        unit_sz = req_unit_sz;
                        unit_bits = 0;
                        has_unit = true;
                    }
                    unit_bits += bw;
                } else {
                    if (has_unit) {
                        cur_bytes = unit_off + unit_sz;
                        has_unit = false;
                    }
                    max_align = @max(max_align, eff_al);
                    cur_bytes = std.mem.alignForward(u64, cur_bytes, eff_al);
                    cur_bytes += field_sz;
                }
            }
            if (has_unit) cur_bytes = unit_off + unit_sz;
            return .{
                .size_bytes = std.mem.alignForward(u64, cur_bytes, max_align),
                .align_bytes = max_align,
            };
        }

        // SysV / AAPCS64 / Apple ARM64 / Wasm32 bit-level cursor:
        var bit_cursor: u64 = 0;
        for (fields) |field| {
            const nat_al = self.computeTypeNaturalAlign(field.type_id, depth + 1);
            const pragma_only_al = if (pragma_pack_cap > 0) @min(nat_al, pragma_pack_cap) else nat_al;
            const is_fld_packed = rec.layout_attrs.is_packed or field.is_packed_field;
            var eff_al: u32 = if (is_fld_packed) 1 else pragma_only_al;
            eff_al = @max(eff_al, field.explicit_align);
            const unit_sz = @max(self.computeTypeByteSize(field.type_id, depth + 1), 1);

            if (field.bit_width) |bw| {
                if (bw == 0) {
                    if (is_aapcs64_linux) {
                        max_align = @max(max_align, pragma_only_al);
                    }
                    const zero_align_bits: u64 = @as(u64, pragma_only_al) * 8;
                    bit_cursor = std.mem.alignForward(u64, bit_cursor, @max(zero_align_bits, 8));
                    continue;
                }
                if (field.name.len > 0 or is_aapcs64_linux) {
                    max_align = @max(max_align, eff_al);
                }
                if (!is_fld_packed) {
                    const align_bits: u64 = @as(u64, eff_al) * 8;
                    const unit_bits: u64 = unit_sz * 8;
                    const base_bit = (bit_cursor / align_bits) * align_bits;
                    if (bit_cursor - base_bit + bw > unit_bits) {
                        bit_cursor = std.mem.alignForward(u64, bit_cursor, align_bits);
                    }
                }
                bit_cursor += bw;
            } else {
                max_align = @max(max_align, eff_al);
                var byte_off = (bit_cursor + 7) / 8;
                byte_off = std.mem.alignForward(u64, byte_off, eff_al);
                byte_off += self.computeTypeByteSize(field.type_id, depth + 1);
                bit_cursor = byte_off * 8;
            }
        }
        return .{
            .size_bytes = std.mem.alignForward(u64, (bit_cursor + 7) / 8, max_align),
            .align_bytes = max_align,
        };
    }

    /// Returns `true` if `type_id` embeds a `c_longdouble` value without pointer indirection.
    pub fn hasByValueLongDouble(self: *const CTranslationUnit, type_id: CTypeId, depth: u32) bool {
        if (depth > MAX_C_PARSE_DEPTH or type_id.isNone() or type_id.asInt() >= self.types.items.len) return false;
        const canon_id = self.unwrapTypedefs(type_id);
        if (canon_id.isNone() or canon_id.asInt() >= self.types.items.len) return false;
        return switch (self.getType(canon_id)) {
            .primitive => |prim| prim == .c_longdouble,
            .pointer, .enum_ref, .function, .typedef_ref => false,
            .array => |arr| self.hasByValueLongDouble(arr.elem, depth + 1),
            .atomic_val => |inner| self.hasByValueLongDouble(inner, depth + 1),
            .record_ref => |rec_id| blk: {
                const rec = self.getDecl(rec_id).kind.record_decl;
                if (!rec.is_complete) break :blk false;
                for (self.getFields(rec.field_start, rec.field_len)) |field| {
                    if (self.hasByValueLongDouble(field.type_id, depth + 1)) break :blk true;
                }
                break :blk false;
            },
        };
    }

    /// Retrieves `CDecl` for `decl_id` in $O(1)$ time.
    pub inline fn getDecl(self: *const CTranslationUnit, decl_id: CDeclId) CDecl {
        return self.decls.items[decl_id.asInt()];
    }

    /// Returns the `CStructField` slice for `[start .. start + len)`.
    pub inline fn getFields(self: *const CTranslationUnit, start: u32, len: u32) []const CStructField {
        return self.fields.items[start .. start + len];
    }

    /// Returns the `CFnParam` slice for `[start .. start + len)`.
    pub inline fn getParams(self: *const CTranslationUnit, start: u32, len: u32) []const CFnParam {
        return self.params.items[start .. start + len];
    }

    /// Returns the `CEnumVariant` slice for `[start .. start + len)`.
    pub inline fn getEnumVariants(self: *const CTranslationUnit, start: u32, len: u32) []const CEnumVariant {
        return self.enum_variants.items[start .. start + len];
    }
};

/// Internal preprocessor macro definition stored in `CPreprocessor.macros`.
const MacroEntry = struct {
    /// Macro name.
    name: []const u8,
    /// `true` when defined with `(` immediately adjacent to `name`.
    is_function_like: bool = false,
    /// `true` when parameter list ends with `...`.
    is_variadic: bool = false,
    /// Parameter names for function-like macros.
    params: []const []const u8 = &.{},
    /// Replacement token sequence.
    body: []const CToken = &.{},
    /// Source span of the `#define` line.
    span: Span = Span.ZERO,
    /// `true` when defined in a bundled system header or predefined target table.
    is_from_system_header: bool = false,
};

/// Conditional `#if` / `#ifdef` / `#elif` / `#else` frame on the preprocessor stack.
const CondFrame = struct {
    /// `true` if all enclosing conditional frames are active.
    is_parent_active: bool,
    /// `true` if the current branch is emitting tokens.
    is_branch_active: bool,
    /// `true` if at least one branch in this `#if` chain has already evaluated true.
    has_taken_branch: bool,
    /// `true` after `#else` has been seen (rejects duplicate `#else` or trailing `#elif`).
    has_seen_else: bool = false,
    /// Span of the opening `#if` / `#ifdef` / `#ifndef` directive.
    open_span: Span,
};

/// Integer constant value with C signed/unsigned promotion tracking for `#if` and constant expressions.
const CIntVal = struct {
    /// Two's-complement 64-bit bit pattern.
    bits: u64,
    /// `true` when typed as `uintmax_t` (`u64`), `false` when typed as `intmax_t` (`i64`).
    is_unsigned: bool,

    /// Interprets `bits` as a signed 64-bit integer.
    inline fn asSigned(self: CIntVal) i64 {
        return @bitCast(self.bits);
    }

    /// Interprets `self` as a 128-bit signed integer preserving signedness.
    inline fn asI128(self: CIntVal) i128 {
        return if (self.is_unsigned) @as(i128, self.bits) else @as(i128, self.asSigned());
    }

    /// Returns `true` if `bits != 0`.
    inline fn isTruthy(self: CIntVal) bool {
        return self.bits != 0;
    }
};

/// Parsed C declaration specifiers (`typedef`, `extern`, `static`, `const`, base type, attributes).
const ParsedDeclSpecs = struct {
    /// Resolved base `CTypeId` from type specifiers.
    type_id: CTypeId,
    /// `true` when `typedef` storage-class specifier was present.
    is_typedef: bool = false,
    /// `true` when `extern` storage-class specifier was present.
    is_extern: bool = false,
    /// `true` when `static` storage-class specifier was present.
    is_static: bool = false,
    /// `true` when `inline` / `__inline` / `__forceinline` function specifier was present.
    is_inline: bool = false,
    /// `true` when `_Noreturn` / `[[noreturn]]` / `__attribute__((noreturn))` was present.
    is_noreturn: bool = false,
    /// `true` when `const` qualifier appeared directly on the declaration specifiers.
    is_const: bool = false,
    /// `true` when `volatile` qualifier appeared directly on the declaration specifiers.
    is_volatile: bool = false,
    /// Explicit `_Alignas(N)` / `__attribute__((aligned(N)))` value (`0` = none).
    explicit_align: u32 = 0,
    /// `true` when `__attribute__((packed))` appeared on the declaration specifiers.
    is_packed: bool = false,
    /// Windows `__declspec(dllexport|dllimport)` modifier.
    dll_storage: CDllStorage = .none,
    /// SAL / Clang FFI contract attributes collected on the declaration specifiers.
    contract: CFfiContract = .{},
    /// 1-based parameter indices marked non-null via `__attribute__((nonnull(1, 2)))` (`0xFFFF_FFFF` = all).
    nonnull_param_mask: u32 = 0,
};

/// Function parameter-list suffix captured inside a C declarator.
const FnSuffixMod = struct {
    /// Start index in `CTranslationUnit.params`.
    param_start: u32,
    /// Number of parameters in `CTranslationUnit.params`.
    param_len: u32,
    /// `true` if variadic `...` is present.
    is_variadic: bool,
};

/// Declarator modifier applied from inside out onto a `ParsedDeclSpecs` base type.
const DeclaratorModifier = union(enum) {
    /// `*` pointer indirection with qualifiers and nullability.
    pointer: struct {
        /// `true` if the pointer value itself is `const` (`T * const p`).
        is_ptr_const: bool = false,
        /// `true` if the pointer is `volatile`.
        is_ptr_volatile: bool = false,
        /// `true` if the pointer is `restrict`.
        is_ptr_restrict: bool = false,
        /// Nullability annotation (`_Nonnull` / `_Nullable`).
        nullability: CNullability = .unspecified,
    },
    /// `[len]` array suffix.
    array: ?u64,
    /// `(params…)` function suffix.
    function: FnSuffixMod,
};

/// Parsed C declarator (optional identifier + ordered inside-out modifiers).
const ParsedDeclarator = struct {
    /// Declared identifier (`""` for abstract declarators).
    name: []const u8 = "",
    /// Span of the identifier or declarator start.
    span: Span = Span.ZERO,
    /// Final resolved `CTypeId`.
    type_id: CTypeId,
    /// `true` if top-level binding itself is `const` (either `const int x` with 0 pointers, or `int * const x`).
    is_top_const: bool = false,
    /// Merged FFI contract annotations from declarator and specifiers.
    contract: CFfiContract = .{},
};

// --------------------------------------- CONSTS ----------------------------------------

/// Hard upper bound on preprocessed C tokens per translation unit (`AGENTS.md` §2).
pub const MAX_C_TOKENS_PER_UNIT: u32 = 262_144;
/// Hard upper bound on macro expansion replacement steps per translation unit (`AGENTS.md` §2).
pub const MAX_MACRO_EXPANSION_STEPS: u32 = 65_536;
/// Hard upper bound on nested `#include` directives (`AGENTS.md` §2).
pub const MAX_INCLUDE_DEPTH: u32 = 64;
/// Hard upper bound on recursive C declarator, struct, and expression parse depth (`AGENTS.md` §2).
pub const MAX_C_PARSE_DEPTH: u32 = 256;

// ------------------- Bundled System Headers -------------------

/// Bundled virtual `<float.h>` IEEE-754 limits header.
const VIRTUAL_FLOAT_H: []const u8 =
    \\#ifndef __COREX_FLOAT_H
    \\#define __COREX_FLOAT_H 1
    \\#define FLT_RADIX 2
    \\#define FLT_MANT_DIG 24
    \\#define DBL_MANT_DIG 53
    \\#define FLT_DIG 6
    \\#define DBL_DIG 15
    \\#define FLT_MIN_EXP (-125)
    \\#define DBL_MIN_EXP (-1021)
    \\#define FLT_MAX_EXP 128
    \\#define DBL_MAX_EXP 1024
    \\#endif
;

/// Bundled virtual `<inttypes.h>` format macro and `imaxdiv_t` header.
const VIRTUAL_INTTYPES_H: []const u8 =
    \\#ifndef __COREX_INTTYPES_H
    \\#define __COREX_INTTYPES_H 1
    \\#include <stdint.h>
    \\#define PRId8 "d"
    \\#define PRId16 "d"
    \\#define PRId32 "d"
    \\#define PRIi8 "i"
    \\#define PRIi16 "i"
    \\#define PRIi32 "i"
    \\#define PRIu8 "u"
    \\#define PRIu16 "u"
    \\#define PRIu32 "u"
    \\#define PRIx8 "x"
    \\#define PRIx16 "x"
    \\#define PRIx32 "x"
    \\#define PRIX8 "X"
    \\#define PRIX16 "X"
    \\#define PRIX32 "X"
    \\#if __SIZEOF_LONG__ == 8
    \\#define PRId64 "ld"
    \\#define PRIi64 "li"
    \\#define PRIu64 "lu"
    \\#define PRIx64 "lx"
    \\#define PRIX64 "lX"
    \\#else
    \\#define PRId64 "lld"
    \\#define PRIi64 "lli"
    \\#define PRIu64 "llu"
    \\#define PRIx64 "llx"
    \\#define PRIX64 "llX"
    \\#endif
    \\typedef struct { intmax_t quot; intmax_t rem; } imaxdiv_t;
    \\#endif
;

/// Bundled virtual `<limits.h>` target-calibrated integer range header.
const VIRTUAL_LIMITS_H: []const u8 =
    \\#ifndef __COREX_LIMITS_H
    \\#define __COREX_LIMITS_H 1
    \\#define CHAR_BIT 8
    \\#define SCHAR_MIN (-128)
    \\#define SCHAR_MAX 127
    \\#define UCHAR_MAX 255
    \\#ifdef __CHAR_UNSIGNED__
    \\#define CHAR_MIN 0
    \\#define CHAR_MAX 255
    \\#else
    \\#define CHAR_MIN (-128)
    \\#define CHAR_MAX 127
    \\#endif
    \\#define SHRT_MIN (-32768)
    \\#define SHRT_MAX 32767
    \\#define USHRT_MAX 65535
    \\#define INT_MIN (-2147483647 - 1)
    \\#define INT_MAX 2147483647
    \\#define UINT_MAX 4294967295U
    \\#if __SIZEOF_LONG__ == 8
    \\#define LONG_MAX 9223372036854775807L
    \\#define LONG_MIN (-LONG_MAX - 1L)
    \\#define ULONG_MAX 18446744073709551615UL
    \\#else
    \\#define LONG_MAX 2147483647L
    \\#define LONG_MIN (-LONG_MAX - 1L)
    \\#define ULONG_MAX 4294967295UL
    \\#endif
    \\#define LLONG_MAX 9223372036854775807LL
    \\#define LLONG_MIN (-LLONG_MAX - 1LL)
    \\#define ULLONG_MAX 18446744073709551615ULL
    \\#endif
;

/// Bundled virtual `<stdarg.h>` variadic argument list header.
const VIRTUAL_STDARG_H: []const u8 =
    \\#ifndef __COREX_STDARG_H
    \\#define __COREX_STDARG_H 1
    \\typedef __builtin_va_list va_list;
    \\typedef __builtin_va_list __gnuc_va_list;
    \\#endif
;

/// Bundled virtual `<stdbool.h>` C99/C11 boolean macro header.
const VIRTUAL_STDBOOL_H: []const u8 =
    \\#ifndef __COREX_STDBOOL_H
    \\#define __COREX_STDBOOL_H 1
    \\#ifndef __bool_true_false_are_defined
    \\#define bool _Bool
    \\#define true 1
    \\#define false 0
    \\#define __bool_true_false_are_defined 1
    \\#endif
    \\#endif
;

/// Bundled virtual `<stddef.h>` pointer-difference, `size_t`, and `NULL` header.
const VIRTUAL_STDDEF_H: []const u8 =
    \\#ifndef __COREX_STDDEF_H
    \\#define __COREX_STDDEF_H 1
    \\#ifndef NULL
    \\#define NULL ((void*)0)
    \\#endif
    \\#define offsetof(type_name, member_name) (0)
    \\typedef int wchar_t;
    \\#endif
;

/// Bundled virtual `<stdint.h>` exact-width integer typedef and limit header.
const VIRTUAL_STDINT_H: []const u8 =
    \\#ifndef __COREX_STDINT_H
    \\#define __COREX_STDINT_H 1
    \\typedef int8_t int_least8_t;
    \\typedef int16_t int_least16_t;
    \\typedef int32_t int_least32_t;
    \\typedef int64_t int_least64_t;
    \\typedef uint8_t uint_least8_t;
    \\typedef uint16_t uint_least16_t;
    \\typedef uint32_t uint_least32_t;
    \\typedef uint64_t uint_least64_t;
    \\typedef int8_t int_fast8_t;
    \\typedef int32_t int_fast16_t;
    \\typedef int32_t int_fast32_t;
    \\typedef int64_t int_fast64_t;
    \\typedef uint8_t uint_fast8_t;
    \\typedef uint32_t uint_fast16_t;
    \\typedef uint32_t uint_fast32_t;
    \\typedef uint64_t uint_fast64_t;
    \\typedef int64_t intmax_t;
    \\typedef uint64_t uintmax_t;
    \\#define INT8_MIN (-128)
    \\#define INT16_MIN (-32768)
    \\#define INT32_MIN (-2147483647 - 1)
    \\#define INT64_MIN (-9223372036854775807LL - 1LL)
    \\#define INT8_MAX 127
    \\#define INT16_MAX 32767
    \\#define INT32_MAX 2147483647
    \\#define INT64_MAX 9223372036854775807LL
    \\#define UINT8_MAX 255U
    \\#define UINT16_MAX 65535U
    \\#define UINT32_MAX 4294967295U
    \\#define UINT64_MAX 18446744073709551615ULL
    \\#if __SIZEOF_POINTER__ == 8
    \\#define SIZE_MAX 18446744073709551615ULL
    \\#define UINTPTR_MAX 18446744073709551615ULL
    \\#define INTPTR_MAX 9223372036854775807LL
    \\#define INTPTR_MIN (-9223372036854775807LL - 1LL)
    \\#else
    \\#define SIZE_MAX 4294967295U
    \\#define UINTPTR_MAX 4294967295U
    \\#define INTPTR_MAX 2147483647
    \\#define INTPTR_MIN (-2147483647 - 1)
    \\#endif
    \\#define INT8_C(val) (val)
    \\#define INT16_C(val) (val)
    \\#define INT32_C(val) (val)
    \\#define INT64_C(val) (val ## LL)
    \\#define UINT8_C(val) (val ## U)
    \\#define UINT16_C(val) (val ## U)
    \\#define UINT32_C(val) (val ## U)
    \\#define UINT64_C(val) (val ## ULL)
    \\#endif
;

/// Bundled virtual `<sys/types.h>` POSIX scalar typedef header.
const VIRTUAL_SYS_TYPES_H: []const u8 =
    \\#ifndef __COREX_SYS_TYPES_H
    \\#define __COREX_SYS_TYPES_H 1
    \\#include <stddef.h>
    \\#include <stdint.h>
    \\typedef int64_t off_t;
    \\typedef int pid_t;
    \\typedef unsigned int uid_t;
    \\typedef unsigned int gid_t;
    \\typedef unsigned int mode_t;
    \\#endif
;

/// Authoritative $O(1)$ map of bundled in-memory standard C headers requiring zero installed C SDK.
pub const BUNDLED_SYSTEM_HEADERS = std.StaticStringMap([]const u8).initComptime(.{
    .{ "float.h", VIRTUAL_FLOAT_H },
    .{ "inttypes.h", VIRTUAL_INTTYPES_H },
    .{ "limits.h", VIRTUAL_LIMITS_H },
    .{ "stdarg.h", VIRTUAL_STDARG_H },
    .{ "stdbool.h", VIRTUAL_STDBOOL_H },
    .{ "stddef.h", VIRTUAL_STDDEF_H },
    .{ "stdint.h", VIRTUAL_STDINT_H },
    .{ "sys/types.h", VIRTUAL_SYS_TYPES_H },
});

/// $O(1)$ map of built-in exact-width `<stdint.h>` / `<stddef.h>` / `<stdarg.h>` type names.
const BUILTIN_EXACT_TYPE_MAP = std.StaticStringMap(CPrimitiveKind).initComptime(.{
    .{ "__builtin_va_list", .va_list },
    .{ "__gnuc_va_list", .va_list },
    .{ "__int128_t", .c_int128 },
    .{ "__ssize_t", .exact_isize },
    .{ "__uint128_t", .c_uint128 },
    .{ "bool", .c_bool },
    .{ "int16_t", .exact_i16 },
    .{ "int32_t", .exact_i32 },
    .{ "int64_t", .exact_i64 },
    .{ "int8_t", .exact_i8 },
    .{ "intptr_t", .exact_isize },
    .{ "ptrdiff_t", .exact_isize },
    .{ "size_t", .exact_usize },
    .{ "ssize_t", .exact_isize },
    .{ "uint16_t", .exact_u16 },
    .{ "uint32_t", .exact_u32 },
    .{ "uint64_t", .exact_u64 },
    .{ "uint8_t", .exact_u8 },
    .{ "uintptr_t", .exact_usize },
    .{ "va_list", .va_list },
});

/// $O(1)$ set of C declaration-specifier starter identifiers (excluding user `typedef` names).
const C_SPECIFIER_KEYWORD_SET = std.StaticStringMap(void).initComptime(.{
    .{ "_Alignas", {} },
    .{ "_Atomic", {} },
    .{ "_Bool", {} },
    .{ "_Noreturn", {} },
    .{ "_Thread_local", {} },
    .{ "__attribute", {} },
    .{ "__attribute__", {} },
    .{ "__builtin_va_list", {} },
    .{ "__cdecl", {} },
    .{ "__const", {} },
    .{ "__const__", {} },
    .{ "__declspec", {} },
    .{ "__extension__", {} },
    .{ "__fastcall", {} },
    .{ "__forceinline", {} },
    .{ "__gnuc_va_list", {} },
    .{ "__inline", {} },
    .{ "__inline__", {} },
    .{ "__int128", {} },
    .{ "__int128_t", {} },
    .{ "__restrict", {} },
    .{ "__restrict__", {} },
    .{ "__signed", {} },
    .{ "__signed__", {} },
    .{ "__ssize_t", {} },
    .{ "__stdcall", {} },
    .{ "__thread", {} },
    .{ "__uint128_t", {} },
    .{ "__vectorcall", {} },
    .{ "__volatile", {} },
    .{ "__volatile__", {} },
    .{ "alignas", {} },
    .{ "auto", {} },
    .{ "bool", {} },
    .{ "char", {} },
    .{ "const", {} },
    .{ "double", {} },
    .{ "enum", {} },
    .{ "extern", {} },
    .{ "float", {} },
    .{ "inline", {} },
    .{ "int", {} },
    .{ "int16_t", {} },
    .{ "int32_t", {} },
    .{ "int64_t", {} },
    .{ "int8_t", {} },
    .{ "intptr_t", {} },
    .{ "long", {} },
    .{ "ptrdiff_t", {} },
    .{ "register", {} },
    .{ "restrict", {} },
    .{ "short", {} },
    .{ "signed", {} },
    .{ "size_t", {} },
    .{ "ssize_t", {} },
    .{ "static", {} },
    .{ "struct", {} },
    .{ "thread_local", {} },
    .{ "typedef", {} },
    .{ "uint16_t", {} },
    .{ "uint32_t", {} },
    .{ "uint64_t", {} },
    .{ "uint8_t", {} },
    .{ "uintptr_t", {} },
    .{ "union", {} },
    .{ "unsigned", {} },
    .{ "va_list", {} },
    .{ "void", {} },
    .{ "volatile", {} },
});

/// $O(1)$ set of attributes recognized by `__has_attribute(…)` / `__has_c_attribute(…)`.
const SUPPORTED_C_ATTR_SET = std.StaticStringMap(void).initComptime(.{
    .{ "__aligned__", {} },
    .{ "__gcc_struct__", {} },
    .{ "__malloc__", {} },
    .{ "__ms_struct__", {} },
    .{ "__nonnull__", {} },
    .{ "__noreturn__", {} },
    .{ "__packed__", {} },
    .{ "aligned", {} },
    .{ "counted_by", {} },
    .{ "deprecated", {} },
    .{ "fallthrough", {} },
    .{ "gcc_struct", {} },
    .{ "malloc", {} },
    .{ "maybe_unused", {} },
    .{ "ms_struct", {} },
    .{ "nodiscard", {} },
    .{ "nonnull", {} },
    .{ "noreturn", {} },
    .{ "packed", {} },
    .{ "unused", {} },
});

/// $O(1)$ set of Clang nullability and Microsoft SAL contract annotation keywords.
const SAL_OR_NULLABILITY_IDENT_SET = std.StaticStringMap(void).initComptime(.{
    .{ "_In_", {} },
    .{ "_In_opt_", {} },
    .{ "_In_opt_z_", {} },
    .{ "_In_reads_", {} },
    .{ "_In_z_", {} },
    .{ "_Inout_", {} },
    .{ "_Inout_opt_", {} },
    .{ "_Nonnull", {} },
    .{ "_Null_unspecified", {} },
    .{ "_Nullable", {} },
    .{ "_Out_", {} },
    .{ "_Out_opt_", {} },
    .{ "_Out_writes_", {} },
    .{ "_Ret_maybenull_", {} },
    .{ "_Ret_notnull_", {} },
});

/// $O(1)$ set of C attribute introducer keywords (`__attribute__`, `_Alignas`, `__declspec`).
const C_ATTRIBUTE_KEYWORD_SET = std.StaticStringMap(void).initComptime(.{
    .{ "_Alignas", {} },
    .{ "__attribute", {} },
    .{ "__attribute__", {} },
    .{ "__declspec", {} },
    .{ "alignas", {} },
});

/// $O(1)$ set of Windows and x86 C calling-convention modifier keywords.
const C_CALLING_CONV_IDENT_SET = std.StaticStringMap(void).initComptime(.{
    .{ "__cdecl", {} },
    .{ "__fastcall", {} },
    .{ "__stdcall", {} },
    .{ "__vectorcall", {} },
});

// -------------------------------------- INTERNALS --------------------------------------

// --------------------- Tokenizer Helpers ----------------------

/// Emits `E0009` (`e0009_c_header_translation_failed`) into `sink` and marks `unit.has_errors = true`.
fn emitCTranslationError(
    unit: *CTranslationUnit,
    sink: *DiagnosticSink,
    span: Span,
    message: []const u8,
) !void {
    unit.has_errors = true;
    const owned_msg = try sink.arena.asAllocator().dupe(u8, message);
    if (!span.file_id.isNone()) {
        const labels = [1]LabeledSpan{.{
            .span = span,
            .label = "C11/C23 header translation failed here",
            .style = .primary,
        }};
        try sink.emit(.{
            .code = .e0009_c_header_translation_failed,
            .severity = .err,
            .primary_span = span,
            .message = owned_msg,
            .labels = &labels,
        });
    } else {
        try sink.emit(.{
            .code = .e0009_c_header_translation_failed,
            .severity = .err,
            .primary_span = span,
            .message = owned_msg,
        });
    }
}

/// Returns `true` if `byte_val` can start a C identifier (`[A-Za-z_$]`).
inline fn isCIdentStart(byte_val: u8) bool {
    return std.ascii.isAlphabetic(byte_val) or byte_val == '_' or byte_val == '$';
}

/// Returns `true` if `byte_val` can continue a C identifier (`[A-Za-z0-9_$]`).
inline fn isCIdentContinue(byte_val: u8) bool {
    return std.ascii.isAlphanumeric(byte_val) or byte_val == '_' or byte_val == '$';
}

/// Builds a compile-time 64-bit bitmask from `kinds` for $O(1)$ delimiter membership checks.
fn cTokenMask(comptime kinds: []const CTokenKind) CTokenMask64 {
    var mask: CTokenMask64 = 0;
    for (kinds) |kind| {
        mask |= @as(CTokenMask64, 1) << @as(u6, @intCast(@backingInt(kind)));
    }
    return mask;
}

/// Returns `true` in $O(1)$ when `kind` is present in `mask`.
inline fn isCTokenInMask(kind: CTokenKind, mask: CTokenMask64) bool {
    return (mask & (@as(CTokenMask64, 1) << @as(u6, @intCast(@backingInt(kind))))) != 0;
}

/// Removes C11 Phase-2 physical backslash-newline splices (`\\\n` and `\\\r\n`) into `arena`.
fn splicePhysicalLines(arena: *BumpArena, raw_source: []const u8) ![]const u8 {
    if (std.mem.indexOfScalar(u8, raw_source, '\\') == null) {
        return arena.dupe(u8, raw_source);
    }
    const out_buf = try arena.allocSlice(u8, raw_source.len);
    var write_idx: usize = 0;
    var read_idx: usize = 0;
    while (read_idx < raw_source.len) {
        if (raw_source[read_idx] == '\\') {
            if (read_idx + 1 < raw_source.len and raw_source[read_idx + 1] == '\n') {
                read_idx += 2;
                continue;
            } else if (read_idx + 2 < raw_source.len and
                raw_source[read_idx + 1] == '\r' and
                raw_source[read_idx + 2] == '\n')
            {
                read_idx += 3;
                continue;
            }
        }
        out_buf[write_idx] = raw_source[read_idx];
        write_idx += 1;
        read_idx += 1;
    }
    return out_buf[0..write_idx];
}

/// Tokenizes a line-spliced C buffer in a single deterministic $O(N)$ non-backtracking pass.
fn tokenizeCSBuffer(
    unit: *CTranslationUnit,
    sink: *DiagnosticSink,
    source: []const u8,
    file_id: FileId,
    is_system_header: bool,
    max_tokens: u32,
    out_tokens: *std.ArrayListUnmanaged(CToken),
) CFrontendError!void {
    var cursor: usize = 0;
    var is_at_line_start = true;
    var has_leading_space = false;

    while (cursor < source.len) {
        const cur_byte = source[cursor];

        // [1] Horizontal whitespace and line breaks:
        if (cur_byte == ' ' or cur_byte == '\t' or cur_byte == '\x0B' or cur_byte == '\x0C') {
            has_leading_space = true;
            cursor += 1;
            continue;
        } else if (cur_byte == '\r') {
            cursor += 1;
            continue;
        } else if (cur_byte == '\n') {
            is_at_line_start = true;
            has_leading_space = false;
            cursor += 1;
            continue;
        }

        // [2] Strip `//` line comments and `/* … */` block comments:
        if (cur_byte == '/' and cursor + 1 < source.len) {
            if (source[cursor + 1] == '/') {
                cursor += 2;
                while (cursor < source.len and source[cursor] != '\n') : (cursor += 1) {}
                has_leading_space = true;
                continue;
            } else if (source[cursor + 1] == '*') {
                const comment_start: u32 = @intCast(cursor);
                cursor += 2;
                var is_closed = false;
                while (cursor + 1 < source.len) : (cursor += 1) {
                    if (source[cursor] == '\n') {
                        // Multiline block comment acts as horizontal space unless followed by `\n`:
                        has_leading_space = true;
                    }
                    if (source[cursor] == '*' and source[cursor + 1] == '/') {
                        cursor += 2;
                        is_closed = true;
                        break;
                    }
                }
                if (!is_closed) {
                    try emitCTranslationError(
                        unit,
                        sink,
                        Span.init(file_id, comment_start, @intCast(source.len)),
                        "unterminated `/*` block comment in C header",
                    );
                    return error.TranslationFailed;
                }
                has_leading_space = true;
                continue;
            }
        }

        if (out_tokens.items.len >= max_tokens) {
            try emitCTranslationError(
                unit,
                sink,
                Span.init(file_id, @intCast(cursor), @intCast(@min(cursor + 1, source.len))),
                "C translation unit exceeded `MAX_C_TOKENS_PER_UNIT` resource cap",
            );
            return error.TranslationFailed;
        }

        const tok_start = cursor;
        var tok_kind: CTokenKind = .ident;

        // [3] String/character literals with optional `L`, `u`, `U`, `u8` encoding prefixes:
        const is_prefixed_quote = (cur_byte == 'L' or cur_byte == 'u' or cur_byte == 'U') and
            cursor + 1 < source.len and
            (source[cursor + 1] == '"' or source[cursor + 1] == '\'' or
                (cur_byte == 'u' and source[cursor + 1] == '8' and
                    cursor + 2 < source.len and
                    (source[cursor + 2] == '"' or source[cursor + 2] == '\'')));

        if (cur_byte == '"' or cur_byte == '\'' or is_prefixed_quote) {
            if (is_prefixed_quote) {
                cursor += if (cur_byte == 'u' and source[cursor + 1] == '8') 2 else 1;
            }
            const quote_char = source[cursor];
            tok_kind = if (quote_char == '"') .string_lit else .char_lit;
            cursor += 1;
            var is_terminated = false;
            while (cursor < source.len) {
                const ch = source[cursor];
                if (ch == '\\') {
                    cursor = @min(cursor + 2, source.len);
                    continue;
                }
                if (ch == '\n') break;
                cursor += 1;
                if (ch == quote_char) {
                    is_terminated = true;
                    break;
                }
            }
            if (!is_terminated) {
                try emitCTranslationError(
                    unit,
                    sink,
                    Span.init(file_id, @intCast(tok_start), @intCast(cursor)),
                    "unterminated string or character literal in C header",
                );
                return error.TranslationFailed;
            }
        } else if (isCIdentStart(cur_byte)) {
            // [4] Identifiers and C keywords:
            cursor += 1;
            while (cursor < source.len and isCIdentContinue(source[cursor])) : (cursor += 1) {}
            tok_kind = .ident;
        } else if (std.ascii.isDigit(cur_byte) or
            (cur_byte == '.' and cursor + 1 < source.len and std.ascii.isDigit(source[cursor + 1])))
        {
            // [5] C11/C23 preprocessing numbers (`pp-number`, supporting `e+`, `p-`, and `'` digit separators):
            tok_kind = .number;
            cursor += 1;
            while (cursor < source.len) {
                const nc = source[cursor];
                if ((nc == 'e' or nc == 'E' or nc == 'p' or nc == 'P') and
                    cursor + 1 < source.len and
                    (source[cursor + 1] == '+' or source[cursor + 1] == '-'))
                {
                    cursor += 2;
                    continue;
                }
                if (nc == '\'' and cursor + 1 < source.len and std.ascii.isAlphanumeric(source[cursor + 1])) {
                    cursor += 2;
                    continue;
                }
                if (std.ascii.isAlphanumeric(nc) or nc == '_' or nc == '.') {
                    cursor += 1;
                    continue;
                }
                break;
            }
        } else {
            // [6] Punctuators and operators:
            cursor += 1;
            switch (cur_byte) {
                '(' => tok_kind = .lparen,
                ')' => tok_kind = .rparen,
                '[' => tok_kind = .lbracket,
                ']' => tok_kind = .rbracket,
                '{' => tok_kind = .lbrace,
                '}' => tok_kind = .rbrace,
                '~' => tok_kind = .tilde,
                '?' => tok_kind = .question,
                ';' => tok_kind = .semi,
                ',' => tok_kind = .comma,
                '.' => {
                    if (cursor + 1 < source.len and source[cursor] == '.' and source[cursor + 1] == '.') {
                        cursor += 2;
                        tok_kind = .ellipses;
                    } else {
                        tok_kind = .dot;
                    }
                },
                ':' => {
                    if (cursor < source.len and source[cursor] == ':') {
                        cursor += 1;
                        tok_kind = .colon_colon;
                    } else {
                        tok_kind = .colon;
                    }
                },
                '#' => {
                    if (cursor < source.len and source[cursor] == '#') {
                        cursor += 1;
                        tok_kind = .hash_hash;
                    } else {
                        tok_kind = .hash;
                    }
                },
                '&' => {
                    if (cursor < source.len and source[cursor] == '&') {
                        cursor += 1;
                        tok_kind = .amp_amp;
                    } else if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .amp_eq;
                    } else {
                        tok_kind = .amp;
                    }
                },
                '|' => {
                    if (cursor < source.len and source[cursor] == '|') {
                        cursor += 1;
                        tok_kind = .pipe_pipe;
                    } else if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .pipe_eq;
                    } else {
                        tok_kind = .pipe;
                    }
                },
                '^' => {
                    if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .caret_eq;
                    } else {
                        tok_kind = .caret;
                    }
                },
                '!' => {
                    if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .bang_eq;
                    } else {
                        tok_kind = .bang;
                    }
                },
                '+' => {
                    if (cursor < source.len and source[cursor] == '+') {
                        cursor += 1;
                        tok_kind = .plus_plus;
                    } else if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .plus_eq;
                    } else {
                        tok_kind = .plus;
                    }
                },
                '-' => {
                    if (cursor < source.len and source[cursor] == '>') {
                        cursor += 1;
                        tok_kind = .arrow;
                    } else if (cursor < source.len and source[cursor] == '-') {
                        cursor += 1;
                        tok_kind = .minus_minus;
                    } else if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .minus_eq;
                    } else {
                        tok_kind = .minus;
                    }
                },
                '*' => {
                    if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .star_eq;
                    } else {
                        tok_kind = .star;
                    }
                },
                '/' => {
                    if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .slash_eq;
                    } else {
                        tok_kind = .slash;
                    }
                },
                '%' => {
                    if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .percent_eq;
                    } else {
                        tok_kind = .percent;
                    }
                },
                '=' => {
                    if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .eq_eq;
                    } else {
                        tok_kind = .eq;
                    }
                },
                '<' => {
                    if (cursor + 1 < source.len and source[cursor] == '<' and source[cursor + 1] == '=') {
                        cursor += 2;
                        tok_kind = .shl_eq;
                    } else if (cursor < source.len and source[cursor] == '<') {
                        cursor += 1;
                        tok_kind = .shl;
                    } else if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .le;
                    } else {
                        tok_kind = .lt;
                    }
                },
                '>' => {
                    if (cursor + 1 < source.len and source[cursor] == '>' and source[cursor + 1] == '=') {
                        cursor += 2;
                        tok_kind = .shr_eq;
                    } else if (cursor < source.len and source[cursor] == '>') {
                        cursor += 1;
                        tok_kind = .shr;
                    } else if (cursor < source.len and source[cursor] == '=') {
                        cursor += 1;
                        tok_kind = .ge;
                    } else {
                        tok_kind = .gt;
                    }
                },
                else => {
                    try emitCTranslationError(
                        unit,
                        sink,
                        Span.init(file_id, @intCast(tok_start), @intCast(cursor)),
                        "unexpected character in C header",
                    );
                    return error.TranslationFailed;
                },
            }
        }

        const lexeme = try unit.arena.dupe(u8, source[tok_start..cursor]);
        try out_tokens.append(unit.allocator, .{
            .kind = tok_kind,
            .lexeme = lexeme,
            .span = Span.init(file_id, @intCast(tok_start), @intCast(cursor)),
            .is_at_line_start = is_at_line_start,
            .has_leading_space = has_leading_space,
            .is_from_system_header = is_system_header,
        });
        is_at_line_start = false;
        has_leading_space = false;
    }
}

/// Decodes a single-byte C string escape starting after `\` at `raw[cursor.*..]`.
fn decodeCEscapeChar(raw: []const u8, cursor: *usize) u8 {
    if (cursor.* >= raw.len) return 0;
    const esc = raw[cursor.*];
    cursor.* += 1;
    return switch (esc) {
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        'a' => 0x07,
        'b' => 0x08,
        'f' => 0x0C,
        'v' => 0x0B,
        '\\', '\'', '"', '?' => esc,
        'x' => blk: {
            var val: u8 = 0;
            var digits: usize = 0;
            while (cursor.* < raw.len and digits < 2) {
                const nibble = std.fmt.charToDigit(raw[cursor.*], 16) catch break;
                val = (val << 4) | nibble;
                cursor.* += 1;
                digits += 1;
            }
            break :blk val;
        },
        '0'...'7' => blk: {
            var val: u8 = esc - '0';
            var digits: usize = 1;
            while (cursor.* < raw.len and digits < 3 and raw[cursor.*] >= '0' and raw[cursor.*] <= '7') {
                val = (val << 3) | (raw[cursor.*] - '0');
                cursor.* += 1;
                digits += 1;
            }
            break :blk val;
        },
        else => esc,
    };
}

/// Decodes a C character escape sequence (`\x…`, `\0…`, `\uXXXX`, `\UXXXXXXXX`) after `\` at `raw[cursor.*..]`.
fn decodeCEscapeCodepoint(raw: []const u8, cursor: *usize) ?u32 {
    if (cursor.* >= raw.len) return null;
    const esc = raw[cursor.*];
    cursor.* += 1;
    return switch (esc) {
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        'a' => 0x07,
        'b' => 0x08,
        'f' => 0x0C,
        'v' => 0x0B,
        '\\', '\'', '"', '?' => esc,
        'x' => blk: {
            var val: u32 = 0;
            var digits: usize = 0;
            while (cursor.* < raw.len) {
                const nibble = std.fmt.charToDigit(raw[cursor.*], 16) catch break;
                val = (val << 4) | @as(u32, nibble);
                cursor.* += 1;
                digits += 1;
            }
            if (digits == 0) break :blk null;
            break :blk val;
        },
        'u', 'U' => blk: {
            const needed_digits: usize = if (esc == 'u') 4 else 8;
            if (cursor.* + needed_digits > raw.len) break :blk null;
            var val: u32 = 0;
            var digit_i: usize = 0;
            while (digit_i < needed_digits) : (digit_i += 1) {
                const nibble = std.fmt.charToDigit(raw[cursor.*], 16) catch return null;
                val = (val << 4) | @as(u32, nibble);
                cursor.* += 1;
            }
            if (val > 0x10FFFF) break :blk null;
            break :blk val;
        },
        '0'...'7' => blk: {
            var val: u32 = esc - '0';
            var digits: usize = 1;
            while (cursor.* < raw.len and digits < 3 and raw[cursor.*] >= '0' and raw[cursor.*] <= '7') {
                val = (val << 3) | @as(u32, raw[cursor.*] - '0');
                cursor.* += 1;
                digits += 1;
            }
            break :blk val;
        },
        else => esc,
    };
}

/// Decodes a C string literal lexeme (`"…"`, `u8"…"`, `L"…"`) into `arena`.
fn decodeCStringLiteral(arena: *BumpArena, lexeme: []const u8) ![]const u8 {
    const first_quote = std.mem.indexOfScalar(u8, lexeme, '"') orelse return "";
    if (lexeme.len < first_quote + 2 or lexeme[lexeme.len - 1] != '"') return "";
    const inner = lexeme[first_quote + 1 .. lexeme.len - 1];
    const out_buf = try arena.allocSlice(u8, inner.len);
    var out_len: usize = 0;
    var cursor: usize = 0;
    while (cursor < inner.len) {
        if (inner[cursor] == '\\') {
            cursor += 1;
            out_buf[out_len] = decodeCEscapeChar(inner, &cursor);
            out_len += 1;
        } else {
            out_buf[out_len] = inner[cursor];
            out_len += 1;
            cursor += 1;
        }
    }
    return out_buf[0..out_len];
}

/// Evaluates a C11/C23 character literal (`'A'`, `'\xff'`, `u'λ'`, `U'…'`, `L'…'`, `u8'…'`) on `target`.
fn parseCCharLiteral(lexeme: []const u8, target: TargetSpec) ?CIntVal {
    const first_quote = std.mem.indexOfScalar(u8, lexeme, '\'') orelse return null;
    if (lexeme.len < first_quote + 3 or lexeme[lexeme.len - 1] != '\'') return null;
    const prefix = lexeme[0..first_quote];
    const inner = lexeme[first_quote + 1 .. lexeme.len - 1];
    if (inner.len == 0) return null;

    // [1] Wide and UTF-16/UTF-32 character constants (`u'…'`, `U'…'`, `L'…'`):
    if (std.mem.eql(u8, prefix, "u") or std.mem.eql(u8, prefix, "U") or std.mem.eql(u8, prefix, "L")) {
        const codepoint: u32 = if (inner[0] == '\\') blk: {
            var cursor: usize = 1;
            const esc_cp = decodeCEscapeCodepoint(inner, &cursor) orelse return null;
            if (cursor != inner.len) return null;
            break :blk esc_cp;
        } else blk: {
            const seq_len = std.unicode.utf8ByteSequenceLength(inner[0]) catch return null;
            if (seq_len != inner.len) return null;
            const decoded_cp = std.unicode.utf8Decode(inner[0..seq_len]) catch return null;
            break :blk @intCast(decoded_cp);
        };
        if (std.mem.eql(u8, prefix, "u") and codepoint > 0xFFFF) return null;
        return .{
            .bits = codepoint,
            .is_unsigned = std.mem.eql(u8, prefix, "U"),
        };
    }

    // [2] C23 UTF-8 `u8'…'` character constant (`char8_t` = `unsigned char`):
    if (std.mem.eql(u8, prefix, "u8")) {
        if (inner[0] == '\\') {
            var cursor: usize = 1;
            const esc_cp = decodeCEscapeCodepoint(inner, &cursor) orelse return null;
            if (cursor != inner.len or esc_cp > 0xFF) return null;
            return .{ .bits = esc_cp, .is_unsigned = true };
        }
        if (inner.len != 1 or inner[0] >= 0x80) return null;
        return .{ .bits = inner[0], .is_unsigned = true };
    }

    if (prefix.len != 0) return null;

    // [3] Unprefixed `'…'` C character constant (sign-extended from `char` when `target.isCCharSigned()`):
    var cursor: usize = 0;
    const first_cp: u32 = if (inner[0] == '\\') blk: {
        cursor = 1;
        break :blk decodeCEscapeCodepoint(inner, &cursor) orelse return null;
    } else blk: {
        cursor = 1;
        break :blk inner[0];
    };

    if (cursor == inner.len) {
        if (first_cp > 0xFF) return null;
        const byte_val: u8 = @intCast(first_cp);
        if (target.isCCharSigned()) {
            const signed_char: i8 = @bitCast(byte_val);
            return .{ .bits = @bitCast(@as(i64, signed_char)), .is_unsigned = false };
        }
        return .{ .bits = byte_val, .is_unsigned = false };
    }

    // Multi-character integer constant (up to 4 bytes, e.g., FourCC `'RIFF'`):
    if (first_cp > 0xFF) return null;
    var multi_acc: u32 = first_cp;
    var byte_count: usize = 1;
    while (cursor < inner.len) {
        if (byte_count >= 4) return null;
        const next_cp: u32 = if (inner[cursor] == '\\') blk: {
            cursor += 1;
            break :blk decodeCEscapeCodepoint(inner, &cursor) orelse return null;
        } else blk: {
            const raw_b = inner[cursor];
            cursor += 1;
            break :blk raw_b;
        };
        if (next_cp > 0xFF) return null;
        multi_acc = (multi_acc << 8) | next_cp;
        byte_count += 1;
    }
    const multi_i32: i32 = @bitCast(multi_acc);
    return .{ .bits = @bitCast(@as(i64, multi_i32)), .is_unsigned = false };
}

/// Parses a C11/C23 integer literal (`0x…`, `0b…`, `0…`, decimal, `'` separators, `U`/`L`/`ULL`/`Z` suffixes).
fn parseCIntegerLiteral(lexeme: []const u8) ?CIntVal {
    if (lexeme.len == 0) return null;
    var clean_buf: [128]u8 = undefined;
    var clean_len: usize = 0;
    for (lexeme) |ch| {
        if (ch == '\'') continue;
        if (ch == '.' or ch == '+' or ch == '-') return null;
        if (clean_len >= clean_buf.len) return null;
        clean_buf[clean_len] = ch;
        clean_len += 1;
    }
    const clean = clean_buf[0..clean_len];
    if (clean.len == 0) return null;

    var radix: u8 = 10;
    var start_idx: usize = 0;
    if (clean.len >= 2 and clean[0] == '0') {
        if (clean[1] == 'x' or clean[1] == 'X') {
            radix = 16;
            start_idx = 2;
        } else if (clean[1] == 'b' or clean[1] == 'B') {
            radix = 2;
            start_idx = 2;
        } else if (std.ascii.isDigit(clean[1])) {
            radix = 8;
            start_idx = 1;
        }
    }

    // Strip valid trailing integer suffixes (`u`, `U`, `l`, `L`, `z`, `Z`):
    var end_idx = clean.len;
    var has_u_suffix = false;
    while (end_idx > start_idx) {
        const tail = clean[end_idx - 1];
        if (tail == 'u' or tail == 'U') {
            has_u_suffix = true;
            end_idx -= 1;
        } else if (tail == 'l' or tail == 'L' or tail == 'z' or tail == 'Z') {
            end_idx -= 1;
        } else {
            break;
        }
    }
    if (end_idx <= start_idx) {
        if (clean.len == 1 and clean[0] == '0') return .{ .bits = 0, .is_unsigned = false };
        return null;
    }

    const digits = clean[start_idx..end_idx];
    const parsed_u64 = std.fmt.parseInt(u64, digits, radix) catch return null;
    const is_unsigned = has_u_suffix or (radix != 10 and parsed_u64 > @as(u64, std.math.maxInt(i64))) or
        parsed_u64 > @as(u64, std.math.maxInt(i64));
    return .{ .bits = parsed_u64, .is_unsigned = is_unsigned };
}

/// Parses a C floating-point literal (`3.14`, `1.5f`, `2.0e-4L`) to `f64`, or `null` if not a float.
fn parseCFloatLiteral(lexeme: []const u8) ?f64 {
    if (std.mem.indexOfAny(u8, lexeme, ".eEpP") == null) return null;
    var clean_buf: [128]u8 = undefined;
    var clean_len: usize = 0;
    for (lexeme) |ch| {
        if (ch == '\'') continue;
        if (clean_len >= clean_buf.len) return null;
        clean_buf[clean_len] = ch;
        clean_len += 1;
    }
    var slice = clean_buf[0..clean_len];
    if (slice.len > 0) {
        const last = slice[slice.len - 1];
        if (last == 'f' or last == 'F' or last == 'l' or last == 'L') {
            slice = slice[0 .. slice.len - 1];
        }
    }
    if (slice.len == 0) return null;
    return std.fmt.parseFloat(f64, slice) catch null;
}

/// Normalizes backslashes (`\`) to forward slashes (`/`) and collapses `./` segments into `arena`.
fn normalizeIncludePath(arena: *BumpArena, raw_path: []const u8) ![]const u8 {
    const buf = try arena.allocSlice(u8, raw_path.len);
    var out_len: usize = 0;
    var i: usize = 0;
    while (i < raw_path.len) : (i += 1) {
        const ch: u8 = if (raw_path[i] == '\\') '/' else raw_path[i];
        if (ch == '.' and i + 1 < raw_path.len and (raw_path[i + 1] == '/' or raw_path[i + 1] == '\\') and
            (out_len == 0 or buf[out_len - 1] == '/'))
        {
            i += 1;
            continue;
        }
        buf[out_len] = ch;
        out_len += 1;
    }
    return buf[0..out_len];
}

// -------------------- Preprocessor Engine ---------------------

/// Stateful C11/C23 preprocessor with Blue-Paint macro recursion prevention and `#pragma once`.
const CPreprocessor = struct {
    /// Owning translation unit receiving expanded tokens and macro constants.
    unit: *CTranslationUnit,
    /// Diagnostic sink for `E0009` errors.
    sink: *DiagnosticSink,
    /// Frontend configuration and resource caps.
    options: CFrontendOptions,
    /// Active `#define` symbol table.
    macros: std.StringHashMapUnmanaged(MacroEntry) = .empty,
    /// Ordered names of user object-like `#define` macros candidate for `pub const` promotion.
    user_object_macro_order: std.ArrayListUnmanaged([]const u8) = .empty,
    /// Canonical header paths marked with `#pragma once`.
    pragma_once_headers: std.StringHashMapUnmanaged(void) = .empty,
    /// Refcounted active macro names currently undergoing rescanning ($O(1)$ Blue-Paint guard).
    active_macro_counts: std.StringHashMapUnmanaged(u32) = .empty,
    /// `true` once `virtual_header_map` and `vfs_header_map` have been populated on first `#include`.
    has_built_include_maps: bool = false,
    /// Lazily built $O(1)$ normalized-path -> content map over `options.virtual_headers`.
    virtual_header_map: std.StringHashMapUnmanaged([]const u8) = .empty,
    /// Lazily built $O(1)$ virtual-path -> content map over `options.include_loader.vfs`.
    vfs_header_map: std.StringHashMapUnmanaged([]const u8) = .empty,
    /// Cumulative macro replacement steps executed across the unit.
    expansion_steps: u32 = 0,
    /// Current macro expansion / substitution call-stack depth (capped at `options.max_parse_depth`).
    macro_recursion_depth: u32 = 0,
    /// Cumulative expanded token count across all `substituteAndPasteMacroBody` and `expandTokenSequence` calls.
    expanded_token_budget: usize = 0,
    /// `true` once any preprocessor resource cap (`max_tokens`, `max_macro_steps`, `max_parse_depth`) has tripped.
    has_hit_resource_cap: bool = false,
    /// `true` while speculatively expanding candidate object-like `#define`s for `pub const` promotion.
    is_probing_macro_const: bool = false,

    /// Releases temporary hash maps and stacks owned by `self`.
    fn deinit(self: *CPreprocessor) void {
        self.macros.deinit(self.unit.allocator);
        self.user_object_macro_order.deinit(self.unit.allocator);
        self.pragma_once_headers.deinit(self.unit.allocator);
        self.active_macro_counts.deinit(self.unit.allocator);
        self.virtual_header_map.deinit(self.unit.allocator);
        self.vfs_header_map.deinit(self.unit.allocator);
    }

    /// Defines a single predefined scalar/identifier macro into `self.macros`.
    fn defineBuiltinText(self: *CPreprocessor, name: []const u8, val_text: []const u8) !void {
        const name_owned = try self.unit.arena.dupe(u8, name);
        var body_list: std.ArrayListUnmanaged(CToken) = .empty;
        defer body_list.deinit(self.unit.allocator);
        if (val_text.len > 0) {
            try tokenizeCSBuffer(
                self.unit,
                self.sink,
                val_text,
                .none,
                true,
                self.options.max_tokens,
                &body_list,
            );
        }
        const body_slice = try self.unit.arena.dupe(CToken, body_list.items);
        try self.macros.put(self.unit.allocator, name_owned, .{
            .name = name_owned,
            .body = body_slice,
            .is_from_system_header = true,
        });
    }

    /// Populates target-calibrated C11/C23 predefined macros and user `-D` defines.
    fn populatePredefinedMacros(self: *CPreprocessor) CFrontendError!void {
        const target = self.options.target;
        try self.defineBuiltinText("__STDC__", "1");
        try self.defineBuiltinText("__STDC_VERSION__", "201710L");
        try self.defineBuiltinText("__STDC_HOSTED__", if (target.isFreestanding()) "0" else "1");
        try self.defineBuiltinText("__ORDER_LITTLE_ENDIAN__", "1234");
        try self.defineBuiltinText("__ORDER_BIG_ENDIAN__", "4321");
        try self.defineBuiltinText("__BYTE_ORDER__", "__ORDER_LITTLE_ENDIAN__");
        try self.defineBuiltinText("__SIZEOF_SHORT__", "2");
        try self.defineBuiltinText("__SIZEOF_INT__", "4");
        try self.defineBuiltinText("__SIZEOF_LONG_LONG__", "8");

        const ptr_str = if (target.ptrBytes() == 4) "4" else "8";
        const long_str = if (target.cLongByteSize() == 4) "4" else "8";
        try self.defineBuiltinText("__SIZEOF_POINTER__", ptr_str);
        try self.defineBuiltinText("__SIZEOF_SIZE_T__", ptr_str);
        try self.defineBuiltinText("__SIZEOF_LONG__", long_str);

        if (target.cLongByteSize() == 8) {
            try self.defineBuiltinText("__LP64__", "1");
            try self.defineBuiltinText("_LP64", "1");
        }
        if (!target.isCCharSigned()) {
            try self.defineBuiltinText("__CHAR_UNSIGNED__", "1");
        }

        switch (target.arch) {
            .x86_64 => {
                try self.defineBuiltinText("__x86_64__", "1");
                try self.defineBuiltinText("__x86_64", "1");
                try self.defineBuiltinText("__amd64__", "1");
                if (target.os == .windows) {
                    try self.defineBuiltinText("_M_X64", "100");
                    try self.defineBuiltinText("_M_AMD64", "100");
                }
            },
            .aarch64 => {
                try self.defineBuiltinText("__aarch64__", "1");
                if (target.os == .windows) {
                    try self.defineBuiltinText("_M_ARM64", "1");
                }
            },
            .wasm32 => {
                try self.defineBuiltinText("__wasm32__", "1");
                try self.defineBuiltinText("__wasm__", "1");
            },
        }

        switch (target.os) {
            .linux => {
                try self.defineBuiltinText("__linux__", "1");
                try self.defineBuiltinText("__linux", "1");
                try self.defineBuiltinText("__unix__", "1");
            },
            .macos => {
                try self.defineBuiltinText("__APPLE__", "1");
                try self.defineBuiltinText("__MACH__", "1");
            },
            .windows => {
                try self.defineBuiltinText("_WIN32", "1");
                try self.defineBuiltinText("_WIN64", "1");
                if (target.abi == .msvc) {
                    try self.defineBuiltinText("_MSC_VER", "1930");
                } else {
                    try self.defineBuiltinText("__MINGW32__", "1");
                    try self.defineBuiltinText("__MINGW64__", "1");
                    try self.defineBuiltinText("__GNUC__", "14");
                }
            },
            .wasi => {
                try self.defineBuiltinText("__wasi__", "1");
            },
            .freestanding => {},
        }

        // Apply user `-DNAME` / `-DNAME=VAL` defines:
        for (self.options.defines) |user_def| {
            if (user_def.name.len == 0) continue;
            const val_str = user_def.value orelse "1";
            const name_owned = try self.unit.arena.dupe(u8, user_def.name);
            var def_toks: std.ArrayListUnmanaged(CToken) = .empty;
            defer def_toks.deinit(self.unit.allocator);
            if (val_str.len > 0) {
                try tokenizeCSBuffer(
                    self.unit,
                    self.sink,
                    val_str,
                    .none,
                    false,
                    self.options.max_tokens,
                    &def_toks,
                );
            }
            try self.macros.put(self.unit.allocator, name_owned, .{
                .name = name_owned,
                .body = try self.unit.arena.dupe(CToken, def_toks.items),
                .is_from_system_header = false,
            });
            try self.user_object_macro_order.append(self.unit.allocator, name_owned);
        }
    }

    /// Marks `macro_name` as active in the $O(1)$ Blue-Paint recursion table.
    fn pushActiveMacro(self: *CPreprocessor, macro_name: []const u8) !void {
        const gop = try self.active_macro_counts.getOrPut(self.unit.allocator, macro_name);
        gop.value_ptr.* = if (gop.found_existing) gop.value_ptr.* + 1 else 1;
    }

    /// Decrements `macro_name` in the $O(1)$ Blue-Paint recursion table, removing it at `0`.
    fn popActiveMacro(self: *CPreprocessor, macro_name: []const u8) void {
        if (self.active_macro_counts.getPtr(macro_name)) |count_ptr| {
            if (count_ptr.* <= 1) {
                _ = self.active_macro_counts.remove(macro_name);
            } else {
                count_ptr.* -= 1;
            }
        }
    }

    /// Returns `true` in $O(1)$ if `macro_name` is currently on the active Blue-Paint expansion set.
    inline fn isMacroBluePainted(self: *const CPreprocessor, macro_name: []const u8) bool {
        return self.active_macro_counts.contains(macro_name);
    }

    /// Lazily populates $O(1)$ lookup maps for `options.virtual_headers` and `VfsSourceMap` entries.
    fn ensureIncludeMapsBuilt(self: *CPreprocessor) !void {
        if (self.has_built_include_maps) return;
        self.has_built_include_maps = true;
        for (self.options.virtual_headers) |vh| {
            const norm_vh = try normalizeIncludePath(&self.unit.arena, vh.path);
            const gop = try self.virtual_header_map.getOrPut(self.unit.allocator, norm_vh);
            if (!gop.found_existing) {
                gop.value_ptr.* = vh.content;
            }
        }
        if (self.options.include_loader == .vfs) {
            const vfs_map = self.options.include_loader.vfs;
            for (vfs_map.entries.items) |entry| {
                const vpath = vfs_map.interner.get(entry.virtual_path);
                const gop = try self.vfs_header_map.getOrPut(self.unit.allocator, vpath);
                if (!gop.found_existing) {
                    gop.value_ptr.* = entry.content;
                }
            }
        }
    }

    /// Resolves `#include` content without mutating state (`is_probe_only == true` for `__has_include`).
    fn resolveIncludeContent(
        self: *CPreprocessor,
        include_name: []const u8,
        is_angled: bool,
        includer_path: []const u8,
    ) !?struct { canonical_key: []const u8, content: []const u8, is_system: bool } {
        try self.ensureIncludeMapsBuilt();
        const norm_req = try normalizeIncludePath(&self.unit.arena, include_name);

        // [1] For `"…"` includes, search relative to the current includer's directory first:
        if (!is_angled) {
            const parent_dir = if (std.mem.lastIndexOfScalar(u8, includer_path, '/')) |slash_idx|
                includer_path[0..slash_idx]
            else
                "";
            const rel_candidate = if (parent_dir.len > 0) blk: {
                const joined = try std.fmt.allocPrint(
                    self.unit.arena.asAllocator(),
                    "{s}/{s}",
                    .{ parent_dir, norm_req },
                );
                break :blk try normalizeIncludePath(&self.unit.arena, joined);
            } else norm_req;

            if (try self.tryLoadSingleCandidate(rel_candidate)) |found| {
                return .{ .canonical_key = rel_candidate, .content = found, .is_system = false };
            }
        }

        // [2] Search explicit `virtual_headers` directly by normalized name in $O(1)$:
        if (self.virtual_header_map.getEntry(norm_req)) |vh_entry| {
            return .{
                .canonical_key = vh_entry.key_ptr.*,
                .content = try self.unit.arena.dupe(u8, vh_entry.value_ptr.*),
                .is_system = false,
            };
        }

        // [3] Search `-Idir` `include_dirs`:
        for (self.options.include_dirs) |inc_dir| {
            const joined = try std.fmt.allocPrint(
                self.unit.arena.asAllocator(),
                "{s}/{s}",
                .{ inc_dir, norm_req },
            );
            const norm_joined = try normalizeIncludePath(&self.unit.arena, joined);
            if (try self.tryLoadSingleCandidate(norm_joined)) |found| {
                return .{ .canonical_key = norm_joined, .content = found, .is_system = is_angled };
            }
        }

        // [4] Check bundled virtual standard C headers (`<stdint.h>`, `<stddef.h>`, etc.):
        if (BUNDLED_SYSTEM_HEADERS.get(norm_req)) |bundled_src| {
            const sys_key = try std.fmt.allocPrint(
                self.unit.arena.asAllocator(),
                "<builtin:{s}>",
                .{norm_req},
            );
            return .{ .canonical_key = sys_key, .content = bundled_src, .is_system = true };
        }

        return null;
    }

    /// Probes `virtual_headers`, `VfsSourceMap`, or `std.Io` host disk for `candidate_path` in $O(1)$.
    fn tryLoadSingleCandidate(self: *CPreprocessor, candidate_path: []const u8) !?[]const u8 {
        try self.ensureIncludeMapsBuilt();
        if (self.virtual_header_map.get(candidate_path)) |vh_content| {
            return try self.unit.arena.dupe(u8, vh_content);
        }
        switch (self.options.include_loader) {
            .none => return null,
            .vfs => {
                if (self.vfs_header_map.get(candidate_path)) |vfs_content| {
                    return try self.unit.arena.dupe(u8, vfs_content);
                }
                return null;
            },
            .host_fs => |io| {
                const raw_bytes = std.Io.Dir.cwd().readFileAlloc(
                    io,
                    candidate_path,
                    self.unit.allocator,
                    .limited(16 * 1024 * 1024),
                ) catch return null;
                defer self.unit.allocator.free(raw_bytes);
                return try self.unit.arena.dupe(u8, raw_bytes);
            },
        }
    }

    /// Preprocesses `source` at `include_depth`, appending surviving tokens to `out_tokens`.
    fn preprocessBuffer(
        self: *CPreprocessor,
        source: []const u8,
        current_path: []const u8,
        file_id: FileId,
        is_system_header: bool,
        include_depth: u32,
        out_tokens: *std.ArrayListUnmanaged(CToken),
    ) CFrontendError!void {
        if (include_depth > self.options.max_include_depth) {
            try emitCTranslationError(
                self.unit,
                self.sink,
                Span.init(file_id, 0, 0),
                "`#include` nesting depth exceeded `MAX_INCLUDE_DEPTH` cap",
            );
            return error.TranslationFailed;
        }

        const spliced = try splicePhysicalLines(&self.unit.arena, source);
        var raw_tokens: std.ArrayListUnmanaged(CToken) = .empty;
        defer raw_tokens.deinit(self.unit.allocator);
        try tokenizeCSBuffer(
            self.unit,
            self.sink,
            spliced,
            file_id,
            is_system_header,
            self.options.max_tokens,
            &raw_tokens,
        );

        var cond_stack: std.ArrayListUnmanaged(CondFrame) = .empty;
        defer cond_stack.deinit(self.unit.allocator);

        var idx: usize = 0;
        const items = raw_tokens.items;
        while (idx < items.len) {
            const tok = items[idx];
            const is_active = cond_stack.items.len == 0 or
                cond_stack.items[cond_stack.items.len - 1].is_branch_active;

            if (tok.is_at_line_start and tok.kind == .hash) {
                const hash_span = tok.span;
                idx += 1;
                // Collect tokens up to end-of-line:
                const dir_start = idx;
                while (idx < items.len and !items[idx].is_at_line_start) : (idx += 1) {}
                const dir_tokens = items[dir_start..idx];
                if (dir_tokens.len == 0) continue; // Null `#` directive.

                const dir_name = dir_tokens[0].lexeme;
                const args = dir_tokens[1..];

                if (std.mem.eql(u8, dir_name, "ifdef") or std.mem.eql(u8, dir_name, "ifndef")) {
                    const is_ifndef = std.mem.eql(u8, dir_name, "ifndef");
                    if (!is_active) {
                        try cond_stack.append(self.unit.allocator, .{
                            .is_parent_active = false,
                            .is_branch_active = false,
                            .has_taken_branch = true,
                            .open_span = hash_span,
                        });
                    } else {
                        if (args.len == 0 or args[0].kind != .ident) {
                            try emitCTranslationError(
                                self.unit,
                                self.sink,
                                hash_span,
                                "expected macro identifier after `#ifdef` / `#ifndef`",
                            );
                            return error.TranslationFailed;
                        }
                        const is_defined = self.macros.contains(args[0].lexeme);
                        const is_taken = if (is_ifndef) !is_defined else is_defined;
                        try cond_stack.append(self.unit.allocator, .{
                            .is_parent_active = true,
                            .is_branch_active = is_taken,
                            .has_taken_branch = is_taken,
                            .open_span = hash_span,
                        });
                    }
                    continue;
                } else if (std.mem.eql(u8, dir_name, "if")) {
                    if (!is_active) {
                        try cond_stack.append(self.unit.allocator, .{
                            .is_parent_active = false,
                            .is_branch_active = false,
                            .has_taken_branch = true,
                            .open_span = hash_span,
                        });
                    } else {
                        const is_cond_true = try self.evaluateIfCondition(args, current_path, hash_span);
                        try cond_stack.append(self.unit.allocator, .{
                            .is_parent_active = true,
                            .is_branch_active = is_cond_true,
                            .has_taken_branch = is_cond_true,
                            .open_span = hash_span,
                        });
                    }
                    continue;
                } else if (std.mem.eql(u8, dir_name, "elif") or
                    std.mem.eql(u8, dir_name, "elifdef") or
                    std.mem.eql(u8, dir_name, "elifndef"))
                {
                    if (cond_stack.items.len == 0 or
                        cond_stack.items[cond_stack.items.len - 1].has_seen_else)
                    {
                        try emitCTranslationError(
                            self.unit,
                            self.sink,
                            hash_span,
                            "unmatched or out-of-order `#elif` / `#elifdef` / `#elifndef` directive",
                        );
                        return error.TranslationFailed;
                    }
                    const top = &cond_stack.items[cond_stack.items.len - 1];
                    if (!top.is_parent_active or top.has_taken_branch) {
                        top.is_branch_active = false;
                    } else {
                        const is_elif_taken: bool = if (std.mem.eql(u8, dir_name, "elif"))
                            try self.evaluateIfCondition(args, current_path, hash_span)
                        else blk: {
                            if (args.len == 0 or args[0].kind != .ident) {
                                try emitCTranslationError(
                                    self.unit,
                                    self.sink,
                                    hash_span,
                                    "expected macro identifier after `#elifdef` / `#elifndef`",
                                );
                                return error.TranslationFailed;
                            }
                            const is_def = self.macros.contains(args[0].lexeme);
                            break :blk if (std.mem.eql(u8, dir_name, "elifndef")) !is_def else is_def;
                        };
                        top.is_branch_active = is_elif_taken;
                        if (is_elif_taken) top.has_taken_branch = true;
                    }
                    continue;
                } else if (std.mem.eql(u8, dir_name, "else")) {
                    if (cond_stack.items.len == 0 or
                        cond_stack.items[cond_stack.items.len - 1].has_seen_else)
                    {
                        try emitCTranslationError(
                            self.unit,
                            self.sink,
                            hash_span,
                            "unmatched or duplicate `#else` directive",
                        );
                        return error.TranslationFailed;
                    }
                    const top = &cond_stack.items[cond_stack.items.len - 1];
                    top.has_seen_else = true;
                    top.is_branch_active = top.is_parent_active and !top.has_taken_branch;
                    if (top.is_branch_active) top.has_taken_branch = true;
                    continue;
                } else if (std.mem.eql(u8, dir_name, "endif")) {
                    if (cond_stack.items.len == 0) {
                        try emitCTranslationError(
                            self.unit,
                            self.sink,
                            hash_span,
                            "unmatched `#endif` directive in C header",
                        );
                        return error.TranslationFailed;
                    }
                    _ = cond_stack.pop();
                    continue;
                }

                // Skip all non-conditional directives inside inactive `#if` branches:
                if (!is_active) continue;

                if (std.mem.eql(u8, dir_name, "define")) {
                    try self.handleDefineDirective(args, hash_span, is_system_header);
                } else if (std.mem.eql(u8, dir_name, "undef")) {
                    if (args.len > 0 and args[0].kind == .ident) {
                        _ = self.macros.remove(args[0].lexeme);
                    }
                } else if (std.mem.eql(u8, dir_name, "error")) {
                    var err_msg_buf: std.ArrayListUnmanaged(u8) = .empty;
                    defer err_msg_buf.deinit(self.unit.allocator);
                    try err_msg_buf.appendSlice(self.unit.allocator, "`#error` in C header: ");
                    for (args, 0..) |arg_tok, arg_i| {
                        if (arg_i > 0 and arg_tok.has_leading_space) {
                            try err_msg_buf.append(self.unit.allocator, ' ');
                        }
                        try err_msg_buf.appendSlice(self.unit.allocator, arg_tok.lexeme);
                    }
                    try emitCTranslationError(self.unit, self.sink, hash_span, err_msg_buf.items);
                    return error.TranslationFailed;
                } else if (std.mem.eql(u8, dir_name, "include")) {
                    try self.handleIncludeDirective(
                        source,
                        args,
                        current_path,
                        hash_span,
                        include_depth,
                        out_tokens,
                    );
                } else if (std.mem.eql(u8, dir_name, "pragma")) {
                    try self.handlePragmaDirective(args, current_path, hash_span, out_tokens);
                }
                continue;
            }

            if (!is_active) {
                idx += 1;
                continue;
            }

            // Collect active non-directive tokens up to next directive line and expand macros:
            const seg_start = idx;
            while (idx < items.len and !(items[idx].is_at_line_start and items[idx].kind == .hash)) : (idx += 1) {}
            try self.expandTokenSequence(items[seg_start..idx], out_tokens);
        }

        if (cond_stack.items.len > 0) {
            const unclosed = cond_stack.items[cond_stack.items.len - 1];
            try emitCTranslationError(
                self.unit,
                self.sink,
                unclosed.open_span,
                "unterminated `#if` / `#ifdef` conditional block in C header",
            );
            return error.TranslationFailed;
        }
    }

    /// Parses `#define NAME(…) body` and registers it in `self.macros`.
    fn handleDefineDirective(
        self: *CPreprocessor,
        args: []const CToken,
        span: Span,
        is_system_header: bool,
    ) CFrontendError!void {
        if (args.len == 0 or args[0].kind != .ident) {
            try emitCTranslationError(self.unit, self.sink, span, "expected macro name after `#define`");
            return error.TranslationFailed;
        }
        const macro_name = args[0].lexeme;
        var body_start: usize = 1;
        var is_fn_like = false;
        var is_variadic = false;
        var param_names: std.ArrayListUnmanaged([]const u8) = .empty;
        defer param_names.deinit(self.unit.allocator);

        // Function-like iff `(` has NO leading space after `macro_name` (C11 §6.10.3):
        if (args.len >= 2 and args[1].kind == .lparen and !args[1].has_leading_space) {
            is_fn_like = true;
            var p_idx: usize = 2;
            while (p_idx < args.len and args[p_idx].kind != .rparen) {
                if (args[p_idx].kind == .ellipses) {
                    is_variadic = true;
                    p_idx += 1;
                    break;
                }
                if (args[p_idx].kind == .ident) {
                    const pname = args[p_idx].lexeme;
                    p_idx += 1;
                    // GNU `args...` named variadic parameter syntax:
                    if (p_idx < args.len and args[p_idx].kind == .ellipses) {
                        is_variadic = true;
                        try param_names.append(self.unit.allocator, "__VA_ARGS__");
                        p_idx += 1;
                        break;
                    }
                    try param_names.append(self.unit.allocator, pname);
                } else {
                    try emitCTranslationError(
                        self.unit,
                        self.sink,
                        args[p_idx].span,
                        "invalid parameter token in `#define` macro signature",
                    );
                    return error.TranslationFailed;
                }
                if (p_idx < args.len and args[p_idx].kind == .comma) {
                    p_idx += 1;
                } else {
                    break;
                }
            }
            if (p_idx >= args.len or args[p_idx].kind != .rparen) {
                try emitCTranslationError(self.unit, self.sink, span, "unclosed `(` in `#define` macro");
                return error.TranslationFailed;
            }
            body_start = p_idx + 1;
        }

        const owned_params = try self.unit.arena.dupe([]const u8, param_names.items);
        const owned_body = try self.unit.arena.dupe(CToken, args[body_start..]);
        try self.macros.put(self.unit.allocator, macro_name, .{
            .name = macro_name,
            .is_function_like = is_fn_like,
            .is_variadic = is_variadic,
            .params = owned_params,
            .body = owned_body,
            .span = span,
            .is_from_system_header = is_system_header,
        });
        if (!is_fn_like and !is_system_header) {
            try self.user_object_macro_order.append(self.unit.allocator, macro_name);
        }
    }

    /// Extracts `<header.h>` or `"header.h"` and preprocesses the included file unless guarded by `#pragma once`.
    fn handleIncludeDirective(
        self: *CPreprocessor,
        raw_spliced_src: []const u8,
        args: []const CToken,
        current_path: []const u8,
        span: Span,
        include_depth: u32,
        out_tokens: *std.ArrayListUnmanaged(CToken),
    ) CFrontendError!void {
        if (args.len == 0) {
            try emitCTranslationError(self.unit, self.sink, span, "missing header path after `#include`");
            return error.TranslationFailed;
        }

        var include_path: []const u8 = "";
        var is_angled = false;

        if (args[0].kind == .string_lit) {
            include_path = try decodeCStringLiteral(&self.unit.arena, args[0].lexeme);
            is_angled = false;
        } else if (args[0].kind == .lt) {
            // Reconstruct exact raw slice between `<` and `>` on the `#include` line:
            var close_idx: ?usize = null;
            for (args, 0..) |tok, i| {
                if (i > 0 and tok.kind == .gt) {
                    close_idx = i;
                    break;
                }
            }
            if (close_idx) |gt_i| {
                const start_b = args[0].span.end_byte;
                const end_b = args[gt_i].span.start_byte;
                if (start_b <= end_b and end_b <= raw_spliced_src.len) {
                    include_path = std.mem.trim(u8, raw_spliced_src[start_b..end_b], " \t");
                }
                is_angled = true;
            } else {
                try emitCTranslationError(self.unit, self.sink, span, "unclosed `<` in `#include <…>`");
                return error.TranslationFailed;
            }
        } else {
            // Computed `#include MACRO_HEADER`:
            var expanded_inc: std.ArrayListUnmanaged(CToken) = .empty;
            defer expanded_inc.deinit(self.unit.allocator);
            try self.expandTokenSequence(args, &expanded_inc);
            if (expanded_inc.items.len == 1 and expanded_inc.items[0].kind == .string_lit) {
                include_path = try decodeCStringLiteral(&self.unit.arena, expanded_inc.items[0].lexeme);
                is_angled = false;
            } else if (expanded_inc.items.len >= 3 and
                expanded_inc.items[0].kind == .lt and
                expanded_inc.items[expanded_inc.items.len - 1].kind == .gt)
            {
                var joined: std.ArrayListUnmanaged(u8) = .empty;
                defer joined.deinit(self.unit.allocator);
                for (expanded_inc.items[1 .. expanded_inc.items.len - 1]) |piece| {
                    try joined.appendSlice(self.unit.allocator, piece.lexeme);
                }
                include_path = try self.unit.arena.dupe(u8, joined.items);
                is_angled = true;
            } else {
                try emitCTranslationError(self.unit, self.sink, span, "invalid computed `#include` target");
                return error.TranslationFailed;
            }
        }

        const resolved = (try self.resolveIncludeContent(include_path, is_angled, current_path)) orelse {
            const err_msg = try std.fmt.allocPrint(
                self.unit.arena.asAllocator(),
                "cannot find included C header `{s}`",
                .{include_path},
            );
            try emitCTranslationError(self.unit, self.sink, span, err_msg);
            return error.TranslationFailed;
        };

        if (self.pragma_once_headers.contains(resolved.canonical_key)) return;

        try self.preprocessBuffer(
            resolved.content,
            resolved.canonical_key,
            .none,
            resolved.is_system,
            include_depth + 1,
            out_tokens,
        );
    }

    /// Handles `#pragma once` and `#pragma pack(…)` directives.
    fn handlePragmaDirective(
        self: *CPreprocessor,
        args: []const CToken,
        current_path: []const u8,
        span: Span,
        out_tokens: *std.ArrayListUnmanaged(CToken),
    ) CFrontendError!void {
        if (args.len == 0 or args[0].kind != .ident) return;
        if (std.mem.eql(u8, args[0].lexeme, "once")) {
            const key_owned = try self.unit.arena.dupe(u8, current_path);
            try self.pragma_once_headers.put(self.unit.allocator, key_owned, {});
            return;
        }
        if (!std.mem.eql(u8, args[0].lexeme, "pack")) return;
        if (args.len < 2 or args[1].kind != .lparen) return;

        // Parse `#pragma pack()`, `pack(N)`, `pack(push)`, `pack(push, N)`, `pack(pop)`:
        var pack_op: PragmaPackOp = .reset_pack;
        var pack_align: u8 = 0;
        if (args.len >= 3 and args[2].kind == .rparen) {
            pack_op = .reset_pack;
        } else if (args.len >= 3 and args[2].kind == .number) {
            if (parseCIntegerLiteral(args[2].lexeme)) |iv| {
                if (iv.bits >= 1 and iv.bits <= 16 and std.math.isPowerOfTwo(iv.bits)) {
                    pack_op = .set_pack;
                    pack_align = @intCast(iv.bits);
                }
            }
        } else if (args.len >= 3 and args[2].kind == .ident) {
            if (std.mem.eql(u8, args[2].lexeme, "pop")) {
                pack_op = .pop_pack;
            } else if (std.mem.eql(u8, args[2].lexeme, "push")) {
                pack_op = .push_only;
                for (args[3..]) |sub_tok| {
                    if (sub_tok.kind == .number) {
                        if (parseCIntegerLiteral(sub_tok.lexeme)) |iv| {
                            if (iv.bits >= 1 and iv.bits <= 16 and std.math.isPowerOfTwo(iv.bits)) {
                                pack_op = .push_pack;
                                pack_align = @intCast(iv.bits);
                                break;
                            }
                        }
                    }
                }
            }
        }
        try out_tokens.append(self.unit.allocator, .{
            .kind = .pragma_pack,
            .lexeme = "",
            .span = span,
            .pack_op = pack_op,
            .pack_align = pack_align,
        });
    }

    /// Evaluates `#if` / `#elif` integer constant expressions (`defined`, `__has_include`, `__has_attribute`).
    fn evaluateIfCondition(
        self: *CPreprocessor,
        raw_expr_tokens: []const CToken,
        current_path: []const u8,
        span: Span,
    ) CFrontendError!bool {
        // [1] Resolve `defined`, `__has_include`, `__has_builtin`, and `__has_attribute` before general expansion:
        var pre_expanded: std.ArrayListUnmanaged(CToken) = .empty;
        defer pre_expanded.deinit(self.unit.allocator);

        var i: usize = 0;
        while (i < raw_expr_tokens.len) {
            const tok = raw_expr_tokens[i];
            if (tok.kind == .ident and std.mem.eql(u8, tok.lexeme, "defined")) {
                var target_name: []const u8 = "";
                if (i + 1 < raw_expr_tokens.len and raw_expr_tokens[i + 1].kind == .ident) {
                    target_name = raw_expr_tokens[i + 1].lexeme;
                    i += 2;
                } else if (i + 3 < raw_expr_tokens.len and
                    raw_expr_tokens[i + 1].kind == .lparen and
                    raw_expr_tokens[i + 2].kind == .ident and
                    raw_expr_tokens[i + 3].kind == .rparen)
                {
                    target_name = raw_expr_tokens[i + 2].lexeme;
                    i += 4;
                } else {
                    try emitCTranslationError(self.unit, self.sink, tok.span, "malformed `defined` in `#if`");
                    return error.TranslationFailed;
                }
                const is_def = self.macros.contains(target_name);
                try pre_expanded.append(self.unit.allocator, .{
                    .kind = .number,
                    .lexeme = if (is_def) "1" else "0",
                    .span = tok.span,
                });
                continue;
            } else if (tok.kind == .ident and std.mem.eql(u8, tok.lexeme, "__has_include")) {
                var has_inc = false;
                if (i + 1 < raw_expr_tokens.len and raw_expr_tokens[i + 1].kind == .lparen) {
                    var close_p = i + 2;
                    while (close_p < raw_expr_tokens.len and raw_expr_tokens[close_p].kind != .rparen) : (close_p += 1) {}
                    const inner = raw_expr_tokens[i + 2 .. close_p];
                    if (inner.len == 1 and inner[0].kind == .string_lit) {
                        const dec = try decodeCStringLiteral(&self.unit.arena, inner[0].lexeme);
                        has_inc = (try self.resolveIncludeContent(dec, false, current_path)) != null;
                    } else if (inner.len >= 3 and inner[0].kind == .lt and inner[inner.len - 1].kind == .gt) {
                        var path_buf: std.ArrayListUnmanaged(u8) = .empty;
                        defer path_buf.deinit(self.unit.allocator);
                        for (inner[1 .. inner.len - 1]) |pt| {
                            try path_buf.appendSlice(self.unit.allocator, pt.lexeme);
                        }
                        has_inc = (try self.resolveIncludeContent(path_buf.items, true, current_path)) != null;
                    }
                    i = @min(close_p + 1, raw_expr_tokens.len);
                } else {
                    i += 1;
                }
                try pre_expanded.append(self.unit.allocator, .{
                    .kind = .number,
                    .lexeme = if (has_inc) "1" else "0",
                    .span = tok.span,
                });
                continue;
            } else if (tok.kind == .ident and
                (std.mem.eql(u8, tok.lexeme, "__has_attribute") or
                    std.mem.eql(u8, tok.lexeme, "__has_c_attribute") or
                    std.mem.eql(u8, tok.lexeme, "__has_builtin")))
            {
                const is_builtin_q = std.mem.eql(u8, tok.lexeme, "__has_builtin");
                var is_supported = false;
                if (i + 1 < raw_expr_tokens.len and raw_expr_tokens[i + 1].kind == .lparen) {
                    var close_p = i + 2;
                    while (close_p < raw_expr_tokens.len and raw_expr_tokens[close_p].kind != .rparen) : (close_p += 1) {}
                    const inner = raw_expr_tokens[i + 2 .. close_p];
                    if (!is_builtin_q and inner.len > 0) {
                        const last_ident = inner[inner.len - 1].lexeme;
                        is_supported = SUPPORTED_C_ATTR_SET.has(last_ident);
                    }
                    i = @min(close_p + 1, raw_expr_tokens.len);
                } else {
                    i += 1;
                }
                try pre_expanded.append(self.unit.allocator, .{
                    .kind = .number,
                    .lexeme = if (is_supported) "1" else "0",
                    .span = tok.span,
                });
                continue;
            }
            try pre_expanded.append(self.unit.allocator, tok);
            i += 1;
        }

        // [2] Expand macros across `pre_expanded` (re-handling any `defined` produced by macros):
        var expanded: std.ArrayListUnmanaged(CToken) = .empty;
        defer expanded.deinit(self.unit.allocator);
        try self.expandTokenSequence(pre_expanded.items, &expanded);

        // [3] C11 §6.10.1p4; replace `true` -> `1` and all remaining undefined identifiers -> `0`:
        var final_toks: std.ArrayListUnmanaged(CToken) = .empty;
        defer final_toks.deinit(self.unit.allocator);
        var f_idx: usize = 0;
        while (f_idx < expanded.items.len) : (f_idx += 1) {
            const ft = expanded.items[f_idx];
            if (ft.kind == .ident) {
                if (std.mem.eql(u8, ft.lexeme, "defined")) {
                    if (f_idx + 1 < expanded.items.len and expanded.items[f_idx + 1].kind == .ident) {
                        const is_d = self.macros.contains(expanded.items[f_idx + 1].lexeme);
                        try final_toks.append(self.unit.allocator, .{
                            .kind = .number,
                            .lexeme = if (is_d) "1" else "0",
                            .span = ft.span,
                        });
                        f_idx += 1;
                        continue;
                    } else if (f_idx + 3 < expanded.items.len and
                        expanded.items[f_idx + 1].kind == .lparen and
                        expanded.items[f_idx + 2].kind == .ident and
                        expanded.items[f_idx + 3].kind == .rparen)
                    {
                        const is_d = self.macros.contains(expanded.items[f_idx + 2].lexeme);
                        try final_toks.append(self.unit.allocator, .{
                            .kind = .number,
                            .lexeme = if (is_d) "1" else "0",
                            .span = ft.span,
                        });
                        f_idx += 3;
                        continue;
                    }
                }
                const is_true_kw = std.mem.eql(u8, ft.lexeme, "true");
                try final_toks.append(self.unit.allocator, .{
                    .kind = .number,
                    .lexeme = if (is_true_kw) "1" else "0",
                    .span = ft.span,
                });
            } else {
                try final_toks.append(self.unit.allocator, ft);
            }
        }

        if (final_toks.items.len == 0) {
            try emitCTranslationError(self.unit, self.sink, span, "empty expression in `#if` / `#elif`");
            return error.TranslationFailed;
        }

        var eval = ConstExprEvaluator{
            .unit = self.unit,
            .sink = self.sink,
            .tokens = final_toks.items,
            .max_depth = self.options.max_parse_depth,
            .is_comma_allowed = true,
        };
        const res = try eval.parseExpr(0, true);
        if (eval.pos != eval.tokens.len) {
            return eval.fail("unexpected trailing token in `#if` / `#elif` constant expression");
        }
        return res.isTruthy();
    }

    /// Emits `E0009` unless inside a non-cap speculative `#define` constant probe, returning `TranslationFailed`.
    fn emitMacroError(self: *CPreprocessor, span: Span, message: []const u8) CFrontendError {
        if (!self.is_probing_macro_const or self.has_hit_resource_cap) {
            try emitCTranslationError(self.unit, self.sink, span, message);
        }
        return error.TranslationFailed;
    }

    /// Appends a single expanded `tok` into `list`, charging `expanded_token_budget` against `max_tokens`.
    fn appendExpandedToken(
        self: *CPreprocessor,
        list: *std.ArrayListUnmanaged(CToken),
        tok: CToken,
        err_span: Span,
    ) CFrontendError!void {
        self.expanded_token_budget += 1;
        if (self.expanded_token_budget > self.options.max_tokens) {
            self.has_hit_resource_cap = true;
            return self.emitMacroError(
                err_span,
                "C macro expansion exceeded `MAX_C_TOKENS_PER_UNIT` token budget",
            );
        }
        try list.append(self.unit.allocator, tok);
    }

    /// Appends `slice` into `list`, charging `expanded_token_budget` before allocating to block token bombs.
    fn appendExpandedTokenSlice(
        self: *CPreprocessor,
        list: *std.ArrayListUnmanaged(CToken),
        slice: []const CToken,
        err_span: Span,
    ) CFrontendError!void {
        if (slice.len == 0) return;
        self.expanded_token_budget +|= slice.len;
        if (self.expanded_token_budget > self.options.max_tokens) {
            self.has_hit_resource_cap = true;
            return self.emitMacroError(
                err_span,
                "C macro expansion exceeded `MAX_C_TOKENS_PER_UNIT` token budget",
            );
        }
        try list.appendSlice(self.unit.allocator, slice);
    }

    /// Expands macros across `input_tokens` into `out_tokens`, enforcing Blue-Paint and depth/step/token caps.
    fn expandTokenSequence(
        self: *CPreprocessor,
        input_tokens: []const CToken,
        out_tokens: *std.ArrayListUnmanaged(CToken),
    ) CFrontendError!void {
        if (self.macro_recursion_depth >= self.options.max_parse_depth) {
            self.has_hit_resource_cap = true;
            const err_span = if (input_tokens.len > 0) input_tokens[0].span else Span.ZERO;
            return self.emitMacroError(
                err_span,
                "C macro recursion depth exceeded `MAX_C_PARSE_DEPTH` cap",
            );
        }
        self.macro_recursion_depth += 1;
        defer self.macro_recursion_depth -= 1;

        if (input_tokens.len > 16 and self.expanded_token_budget < self.options.max_tokens) {
            const rem_budget = self.options.max_tokens - self.expanded_token_budget;
            try out_tokens.ensureTotalCapacityPrecise(
                self.unit.allocator,
                out_tokens.items.len + @min(input_tokens.len, rem_budget),
            );
        }

        var i: usize = 0;
        while (i < input_tokens.len) {
            const tok = input_tokens[i];
            if (out_tokens.items.len >= self.options.max_tokens) {
                self.has_hit_resource_cap = true;
                return self.emitMacroError(
                    tok.span,
                    "C macro expansion exceeded `MAX_C_TOKENS_PER_UNIT` cap",
                );
            }

            if (tok.kind == .ident and !self.isMacroBluePainted(tok.lexeme)) {
                if (self.macros.get(tok.lexeme)) |macro| {
                    if (!macro.is_function_like) {
                        self.expansion_steps += 1;
                        if (self.expansion_steps > self.options.max_macro_steps) {
                            self.has_hit_resource_cap = true;
                            return self.emitMacroError(
                                tok.span,
                                "C macro expansion exceeded `MAX_MACRO_EXPANSION_STEPS` cap",
                            );
                        }
                        try self.pushActiveMacro(macro.name);
                        defer self.popActiveMacro(macro.name);

                        var pasted: std.ArrayListUnmanaged(CToken) = .empty;
                        defer pasted.deinit(self.unit.allocator);
                        try self.substituteAndPasteMacroBody(macro, &.{}, &.{}, tok, &pasted);
                        try self.expandTokenSequence(pasted.items, out_tokens);
                        i += 1;
                        continue;
                    } else if (i + 1 < input_tokens.len and input_tokens[i + 1].kind == .lparen) {
                        // Collect balanced `( arg0, arg1, … )` arguments:
                        var raw_args: std.ArrayListUnmanaged([]const CToken) = .empty;
                        defer raw_args.deinit(self.unit.allocator);

                        var arg_cursor = i + 2;
                        var paren_depth: u32 = 1;
                        var cur_arg_start = arg_cursor;
                        while (arg_cursor < input_tokens.len and paren_depth > 0) {
                            const ak = input_tokens[arg_cursor].kind;
                            if (ak == .lparen) {
                                paren_depth += 1;
                            } else if (ak == .rparen) {
                                paren_depth -= 1;
                                if (paren_depth == 0) {
                                    if (arg_cursor > cur_arg_start or raw_args.items.len > 0) {
                                        try raw_args.append(
                                            self.unit.allocator,
                                            input_tokens[cur_arg_start..arg_cursor],
                                        );
                                    }
                                    break;
                                }
                            } else if (ak == .comma and paren_depth == 1) {
                                try raw_args.append(
                                    self.unit.allocator,
                                    input_tokens[cur_arg_start..arg_cursor],
                                );
                                cur_arg_start = arg_cursor + 1;
                            }
                            arg_cursor += 1;
                        }
                        if (paren_depth != 0) {
                            return self.emitMacroError(
                                tok.span,
                                "unterminated argument list in function-like macro invocation",
                            );
                        }

                        // Handle 0-argument vs 1-empty-argument macro calls:
                        if (raw_args.items.len == 0 and macro.params.len == 1) {
                            try raw_args.append(self.unit.allocator, &.{});
                        }

                        var fixed_args: []const []const CToken = raw_args.items;
                        var va_tokens: std.ArrayListUnmanaged(CToken) = .empty;
                        defer va_tokens.deinit(self.unit.allocator);

                        if (macro.is_variadic) {
                            if (raw_args.items.len < macro.params.len) {
                                return self.emitMacroError(
                                    tok.span,
                                    "too few arguments to variadic C macro",
                                );
                            }
                            fixed_args = raw_args.items[0..macro.params.len];
                            const extra_slices = raw_args.items[macro.params.len..];
                            for (extra_slices, 0..) |va_slice, va_i| {
                                if (va_i > 0) {
                                    try self.appendExpandedToken(&va_tokens, .{
                                        .kind = .comma,
                                        .lexeme = ",",
                                        .span = tok.span,
                                    }, tok.span);
                                }
                                try self.appendExpandedTokenSlice(&va_tokens, va_slice, tok.span);
                            }
                        } else if (raw_args.items.len != macro.params.len) {
                            return self.emitMacroError(
                                tok.span,
                                "argument count mismatch in C function-like macro call",
                            );
                        }

                        self.expansion_steps += 1;
                        if (self.expansion_steps > self.options.max_macro_steps) {
                            self.has_hit_resource_cap = true;
                            return self.emitMacroError(
                                tok.span,
                                "C macro expansion exceeded `MAX_MACRO_EXPANSION_STEPS` cap",
                            );
                        }

                        var pasted: std.ArrayListUnmanaged(CToken) = .empty;
                        defer pasted.deinit(self.unit.allocator);
                        try self.substituteAndPasteMacroBody(
                            macro,
                            fixed_args,
                            va_tokens.items,
                            tok,
                            &pasted,
                        );

                        try self.pushActiveMacro(macro.name);
                        defer self.popActiveMacro(macro.name);
                        try self.expandTokenSequence(pasted.items, out_tokens);
                        i = arg_cursor + 1;
                        continue;
                    }
                }
            }

            try self.appendExpandedToken(out_tokens, tok, tok.span);
            i += 1;
        }
    }

    /// Performs parameter substitution, `#` stringification, C23 `__VA_OPT__`, and `##` token pasting.
    fn substituteAndPasteMacroBody(
        self: *CPreprocessor,
        macro: MacroEntry,
        fixed_args: []const []const CToken,
        va_tokens: []const CToken,
        call_tok: CToken,
        out_tokens: *std.ArrayListUnmanaged(CToken),
    ) CFrontendError!void {
        if (self.macro_recursion_depth >= self.options.max_parse_depth) {
            self.has_hit_resource_cap = true;
            return self.emitMacroError(
                call_tok.span,
                "C macro recursion depth exceeded `MAX_C_PARSE_DEPTH` cap",
            );
        }
        self.macro_recursion_depth += 1;
        defer self.macro_recursion_depth -= 1;

        // Pre-expand each argument once for non-`#` / non-`##` parameter occurrences:
        var expanded_fixed: std.ArrayListUnmanaged(std.ArrayListUnmanaged(CToken)) = .empty;
        defer {
            for (expanded_fixed.items) |*arg_list| arg_list.deinit(self.unit.allocator);
            expanded_fixed.deinit(self.unit.allocator);
        }
        for (fixed_args) |raw_arg| {
            var arg_list: std.ArrayListUnmanaged(CToken) = .empty;
            errdefer arg_list.deinit(self.unit.allocator);
            try self.expandTokenSequence(raw_arg, &arg_list);
            try expanded_fixed.append(self.unit.allocator, arg_list);
        }
        var expanded_va_list: std.ArrayListUnmanaged(CToken) = .empty;
        defer expanded_va_list.deinit(self.unit.allocator);
        if (va_tokens.len > 0) {
            try self.expandTokenSequence(va_tokens, &expanded_va_list);
        }

        const body = macro.body;
        if (body.len > 0 and self.expanded_token_budget < self.options.max_tokens) {
            var est_tokens: usize = 0;
            for (body) |btok| {
                if (btok.kind == .ident) {
                    if (macro.is_variadic and std.mem.eql(u8, btok.lexeme, "__VA_ARGS__")) {
                        est_tokens +|= expanded_va_list.items.len;
                        continue;
                    }
                    if (findMacroParamIndex(macro.params, btok.lexeme)) |p_i| {
                        est_tokens +|= expanded_fixed.items[p_i].items.len;
                        continue;
                    }
                }
                est_tokens +|= 1;
            }
            const rem_budget = self.options.max_tokens - self.expanded_token_budget;
            if (est_tokens > 16 and est_tokens <= rem_budget) {
                try out_tokens.ensureTotalCapacityPrecise(
                    self.unit.allocator,
                    out_tokens.items.len + est_tokens,
                );
            }
        }
        var idx: usize = 0;
        while (idx < body.len) {
            const btok = body[idx];

            // [1] C23 `__VA_OPT__(…)`:
            if (btok.kind == .ident and std.mem.eql(u8, btok.lexeme, "__VA_OPT__") and
                idx + 1 < body.len and body[idx + 1].kind == .lparen)
            {
                var close_idx = idx + 2;
                var depth: u32 = 1;
                while (close_idx < body.len and depth > 0) {
                    if (body[close_idx].kind == .lparen) depth += 1 else if (body[close_idx].kind == .rparen) {
                        depth -= 1;
                        if (depth == 0) break;
                    }
                    close_idx += 1;
                }
                if (expanded_va_list.items.len > 0) {
                    const sub_macro = MacroEntry{
                        .name = macro.name,
                        .is_function_like = macro.is_function_like,
                        .is_variadic = macro.is_variadic,
                        .params = macro.params,
                        .body = body[idx + 2 .. close_idx],
                        .span = macro.span,
                        .is_from_system_header = macro.is_from_system_header,
                    };
                    try self.substituteAndPasteMacroBody(
                        sub_macro,
                        fixed_args,
                        va_tokens,
                        call_tok,
                        out_tokens,
                    );
                }
                idx = @min(close_idx + 1, body.len);
                continue;
            }

            // [2] `#param` / `#__VA_ARGS__` stringification:
            if (btok.kind == .hash and idx + 1 < body.len and body[idx + 1].kind == .ident) {
                const target_ident = body[idx + 1].lexeme;
                var raw_target: ?[]const CToken = null;
                if (macro.is_variadic and std.mem.eql(u8, target_ident, "__VA_ARGS__")) {
                    raw_target = va_tokens;
                } else if (findMacroParamIndex(macro.params, target_ident)) |p_i| {
                    raw_target = fixed_args[p_i];
                }
                if (raw_target) |to_str| {
                    const str_tok = try self.stringifyTokenSlice(to_str, call_tok.span);
                    try self.appendExpandedToken(out_tokens, str_tok, call_tok.span);
                    idx += 2;
                    continue;
                }
            }

            // [3] `lhs ## rhs` token pasting (including GNU `, ## __VA_ARGS__` elision):
            const is_lhs_of_paste = idx + 1 < body.len and body[idx + 1].kind == .hash_hash;
            if (is_lhs_of_paste) {
                if (btok.kind == .comma and idx + 2 < body.len and
                    body[idx + 2].kind == .ident and
                    std.mem.eql(u8, body[idx + 2].lexeme, "__VA_ARGS__") and
                    va_tokens.len == 0)
                {
                    idx += 3;
                    continue;
                }

                var paste_accum: std.ArrayListUnmanaged(CToken) = .empty;
                defer paste_accum.deinit(self.unit.allocator);
                try self.appendRawParamOrSingle(btok, macro, fixed_args, va_tokens, call_tok.span, &paste_accum);

                while (idx + 2 < body.len and body[idx + 1].kind == .hash_hash) {
                    const rhs_btok = body[idx + 2];
                    var rhs_raw: std.ArrayListUnmanaged(CToken) = .empty;
                    defer rhs_raw.deinit(self.unit.allocator);
                    try self.appendRawParamOrSingle(rhs_btok, macro, fixed_args, va_tokens, call_tok.span, &rhs_raw);

                    if (paste_accum.items.len == 0) {
                        try self.appendExpandedTokenSlice(&paste_accum, rhs_raw.items, call_tok.span);
                    } else if (rhs_raw.items.len > 0) {
                        const left_last = paste_accum.items[paste_accum.items.len - 1];
                        const right_first = rhs_raw.items[0];
                        const joined_lex = try std.fmt.allocPrint(
                            self.unit.arena.asAllocator(),
                            "{s}{s}",
                            .{ left_last.lexeme, right_first.lexeme },
                        );
                        var relexed: std.ArrayListUnmanaged(CToken) = .empty;
                        defer relexed.deinit(self.unit.allocator);
                        try tokenizeCSBuffer(
                            self.unit,
                            self.sink,
                            joined_lex,
                            call_tok.span.file_id,
                            macro.is_from_system_header,
                            self.options.max_tokens,
                            &relexed,
                        );
                        _ = paste_accum.pop();
                        for (relexed.items) |*rt| rt.span = call_tok.span;
                        try self.appendExpandedTokenSlice(&paste_accum, relexed.items, call_tok.span);
                        if (rhs_raw.items.len > 1) {
                            try self.appendExpandedTokenSlice(&paste_accum, rhs_raw.items[1..], call_tok.span);
                        }
                    }
                    idx += 2;
                }
                try self.appendExpandedTokenSlice(out_tokens, paste_accum.items, call_tok.span);
                idx += 1;
                continue;
            }

            // [4] Standard expanded parameter / `__VA_ARGS__` substitution:
            if (btok.kind == .ident) {
                if (macro.is_variadic and std.mem.eql(u8, btok.lexeme, "__VA_ARGS__")) {
                    try self.appendExpandedTokenSlice(out_tokens, expanded_va_list.items, call_tok.span);
                    idx += 1;
                    continue;
                }
                if (findMacroParamIndex(macro.params, btok.lexeme)) |p_i| {
                    try self.appendExpandedTokenSlice(out_tokens, expanded_fixed.items[p_i].items, call_tok.span);
                    idx += 1;
                    continue;
                }
            }

            var cloned = btok;
            if (idx == 0) cloned.has_leading_space = call_tok.has_leading_space;
            cloned.is_from_system_header = macro.is_from_system_header or call_tok.is_from_system_header;
            try self.appendExpandedToken(out_tokens, cloned, call_tok.span);
            idx += 1;
        }
    }

    /// Appends unexpanded parameter tokens for `##` operands (supporting empty placemarkers).
    fn appendRawParamOrSingle(
        self: *CPreprocessor,
        btok: CToken,
        macro: MacroEntry,
        fixed_args: []const []const CToken,
        va_tokens: []const CToken,
        err_span: Span,
        out_list: *std.ArrayListUnmanaged(CToken),
    ) CFrontendError!void {
        if (btok.kind == .ident) {
            if (macro.is_variadic and std.mem.eql(u8, btok.lexeme, "__VA_ARGS__")) {
                try self.appendExpandedTokenSlice(out_list, va_tokens, err_span);
                return;
            }
            if (findMacroParamIndex(macro.params, btok.lexeme)) |p_i| {
                try self.appendExpandedTokenSlice(out_list, fixed_args[p_i], err_span);
                return;
            }
        }
        try self.appendExpandedToken(out_list, btok, err_span);
    }

    /// Converts `tokens` into a C11 stringified literal token (`#arg`).
    fn stringifyTokenSlice(self: *CPreprocessor, tokens: []const CToken, span: Span) !CToken {
        var str_buf: std.ArrayListUnmanaged(u8) = .empty;
        defer str_buf.deinit(self.unit.allocator);
        try str_buf.append(self.unit.allocator, '"');
        for (tokens, 0..) |tok, i| {
            if (i > 0 and tok.has_leading_space) {
                try str_buf.append(self.unit.allocator, ' ');
            }
            if (tok.kind == .string_lit or tok.kind == .char_lit) {
                for (tok.lexeme) |ch| {
                    if (ch == '"' or ch == '\\') {
                        try str_buf.append(self.unit.allocator, '\\');
                    }
                    try str_buf.append(self.unit.allocator, ch);
                }
            } else {
                try str_buf.appendSlice(self.unit.allocator, tok.lexeme);
            }
        }
        try str_buf.append(self.unit.allocator, '"');
        return .{
            .kind = .string_lit,
            .lexeme = try self.unit.arena.dupe(u8, str_buf.items),
            .span = span,
        };
    }

    /// Classifies surviving user object-like `#define`s into `unit.macro_consts`.
    fn collectSurvivingMacroConsts(self: *CPreprocessor) CFrontendError!void {
        var seen_names: std.StringHashMapUnmanaged(void) = .empty;
        defer seen_names.deinit(self.unit.allocator);
        self.is_probing_macro_const = true;
        defer self.is_probing_macro_const = false;

        var idx = self.user_object_macro_order.items.len;
        while (idx > 0) {
            idx -= 1;
            const name = self.user_object_macro_order.items[idx];
            if (seen_names.contains(name)) continue;
            try seen_names.put(self.unit.allocator, name, {});
            const macro = self.macros.get(name) orelse continue;
            if (macro.is_function_like or macro.body.len == 0 or macro.is_from_system_header) continue;

            var expanded: std.ArrayListUnmanaged(CToken) = .empty;
            defer expanded.deinit(self.unit.allocator);
            {
                try self.pushActiveMacro(name);
                defer self.popActiveMacro(name);
                self.expandTokenSequence(macro.body, &expanded) catch |err| {
                    if (err == error.OutOfMemory) return error.OutOfMemory;
                    if (self.has_hit_resource_cap) return error.TranslationFailed;
                    continue;
                };
            }
            if (expanded.items.len == 0) continue;

            if (try self.tryClassifyExpandedMacroConst(expanded.items)) |const_val| {
                try self.unit.macro_consts.append(self.unit.allocator, .{
                    .name = macro.name,
                    .value = const_val,
                    .span = macro.span,
                    .is_from_system_header = false,
                });
            }
        }
        std.mem.reverse(RecordedMacroConst, self.unit.macro_consts.items);
    }

    /// Attempts to evaluate `tokens` as an unambiguous string, float, or integer constant.
    fn tryClassifyExpandedMacroConst(
        self: *CPreprocessor,
        tokens: []const CToken,
    ) !?MacroConstValue {
        // Strip outer balanced parentheses `( … )`:
        var slice = tokens;
        while (slice.len >= 2 and slice[0].kind == .lparen and slice[slice.len - 1].kind == .rparen) {
            var depth: u32 = 0;
            var is_wrapping = true;
            for (slice[0 .. slice.len - 1], 0..) |tok, i| {
                if (tok.kind == .lparen) depth += 1 else if (tok.kind == .rparen) {
                    if (depth == 0) {
                        is_wrapping = false;
                        break;
                    }
                    depth -= 1;
                }
                if (depth == 0 and i > 0) {
                    is_wrapping = false;
                    break;
                }
            }
            if (!is_wrapping or depth != 1) break;
            slice = slice[1 .. slice.len - 1];
        }
        if (slice.len == 0) return null;

        // [1] Adjacent string literal concatenation (`"foo" "bar"`):
        var is_all_strings = true;
        for (slice) |tok| {
            if (tok.kind != .string_lit) {
                is_all_strings = false;
                break;
            }
        }
        if (is_all_strings) {
            var str_acc: std.ArrayListUnmanaged(u8) = .empty;
            defer str_acc.deinit(self.unit.allocator);
            for (slice) |tok| {
                const decoded = try decodeCStringLiteral(&self.unit.arena, tok.lexeme);
                try str_acc.appendSlice(self.unit.allocator, decoded);
            }
            return .{ .string_val = try self.unit.arena.dupe(u8, str_acc.items) };
        }

        // [2] Optional unary `+` / `-` float literal:
        if (slice.len == 1 and slice[0].kind == .number) {
            if (parseCFloatLiteral(slice[0].lexeme)) |fval| {
                return .{ .float_val = fval };
            }
        } else if (slice.len == 2 and
            (slice[0].kind == .minus or slice[0].kind == .plus) and
            slice[1].kind == .number)
        {
            if (parseCFloatLiteral(slice[1].lexeme)) |fval| {
                return .{ .float_val = if (slice[0].kind == .minus) -fval else fval };
            }
        }

        // [3] Pure integer constant expression (no unresolved identifiers or floats):
        for (slice) |tok| {
            switch (tok.kind) {
                .number => if (parseCIntegerLiteral(tok.lexeme) == null) return null,
                .char_lit => if (parseCCharLiteral(tok.lexeme, self.unit.target) == null) return null,
                .lparen,
                .rparen,
                .plus,
                .minus,
                .tilde,
                .bang,
                .star,
                .slash,
                .percent,
                .shl,
                .shr,
                .lt,
                .le,
                .gt,
                .ge,
                .eq_eq,
                .bang_eq,
                .amp,
                .caret,
                .pipe,
                .amp_amp,
                .pipe_pipe,
                .question,
                .colon,
                => {},
                else => return null,
            }
        }

        var dummy_sink = DiagnosticSink.init(self.unit.allocator);
        defer dummy_sink.deinit();
        var eval = ConstExprEvaluator{
            .unit = self.unit,
            .sink = &dummy_sink,
            .tokens = slice,
            .max_depth = self.options.max_parse_depth,
            .is_silent = true,
        };
        const res = eval.parseTernary(0, true) catch return null;
        if (eval.pos != slice.len) return null;
        if (res.is_unsigned or res.bits > @as(u64, std.math.maxInt(i64))) {
            return .{ .unsigned_int = res.bits };
        }
        return .{ .signed_int = res.asSigned() };
    }
};

/// Finds `target` inside `params`, returning its 0-based index or `null`.
fn findMacroParamIndex(params: []const []const u8, target: []const u8) ?usize {
    for (params, 0..) |param_name, i| {
        if (std.mem.eql(u8, param_name, target)) return i;
    }
    return null;
}

/// Depth-bounded C11/C23 integer constant expression evaluator (`#if`, `_Static_assert`, enums, arrays).
const ConstExprEvaluator = struct {
    /// Owning translation unit.
    unit: *CTranslationUnit,
    /// Diagnostic sink for `E0009` errors when `!is_silent`.
    sink: *DiagnosticSink,
    /// Slice of C tokens to evaluate.
    tokens: []const CToken,
    /// Current token cursor.
    pos: usize = 0,
    /// Optional known enum/const identifier lookup table (`null` in `#if` where idents were zeroed).
    known_consts: ?*const std.StringHashMapUnmanaged(i128) = null,
    /// Optional parser context for `sizeof(Type)` evaluation.
    parser_ctx: ?*CDeclParser = null,
    /// Recursion depth cap (`MAX_C_PARSE_DEPTH`).
    max_depth: u32 = MAX_C_PARSE_DEPTH,
    /// When `true`, suppresses diagnostic emission during speculative macro constant probing.
    is_silent: bool = false,
    /// When `true` (`#if` / `#elif`), enables the lowest-precedence C comma `,` operator.
    is_comma_allowed: bool = false,

    /// Emits `E0009` (unless `is_silent`) and aborts constant evaluation.
    fn fail(self: *ConstExprEvaluator, msg: []const u8) CFrontendError {
        if (!self.is_silent) {
            const span = if (self.pos < self.tokens.len)
                self.tokens[self.pos].span
            else if (self.tokens.len > 0)
                self.tokens[self.tokens.len - 1].span
            else
                Span.ZERO;
            try emitCTranslationError(self.unit, self.sink, span, msg);
        }
        return error.TranslationFailed;
    }

    /// Evaluates a top-level or parenthesized constant expression (including `,` when `is_comma_allowed`).
    fn parseExpr(self: *ConstExprEvaluator, depth: u32, is_eval: bool) CFrontendError!CIntVal {
        if (depth >= self.max_depth) return self.fail("C constant expression exceeded `MAX_C_PARSE_DEPTH`");
        var val = try self.parseTernary(depth + 1, is_eval);
        if (self.is_comma_allowed) {
            while (self.pos < self.tokens.len and self.tokens[self.pos].kind == .comma) {
                self.pos += 1;
                val = try self.parseTernary(depth + 1, is_eval);
            }
        }
        return val;
    }

    /// Evaluates `cond ? then_expr : else_expr` with short-circuit branch suppression (`is_eval`).
    fn parseTernary(self: *ConstExprEvaluator, depth: u32, is_eval: bool) CFrontendError!CIntVal {
        if (depth >= self.max_depth) return self.fail("C constant expression exceeded `MAX_C_PARSE_DEPTH`");
        const cond = try self.parseBinary(depth + 1, 1, is_eval);
        if (self.pos < self.tokens.len and self.tokens[self.pos].kind == .question) {
            self.pos += 1;
            const is_then_taken = cond.isTruthy();
            const then_val = try self.parseExpr(depth + 1, is_eval and is_then_taken);
            if (self.pos >= self.tokens.len or self.tokens[self.pos].kind != .colon) {
                return self.fail("expected `:` in C ternary constant expression");
            }
            self.pos += 1;
            const else_val = try self.parseTernary(depth + 1, is_eval and !is_then_taken);
            const is_unsigned = then_val.is_unsigned or else_val.is_unsigned;
            return .{
                .bits = if (is_then_taken) then_val.bits else else_val.bits,
                .is_unsigned = is_unsigned,
            };
        }
        return cond;
    }

    /// Precedence-climbing binary constant expression evaluator (`min_prec = 1..10`).
    fn parseBinary(
        self: *ConstExprEvaluator,
        depth: u32,
        min_prec: u8,
        is_eval: bool,
    ) CFrontendError!CIntVal {
        if (depth >= self.max_depth) return self.fail("C constant expression exceeded `MAX_C_PARSE_DEPTH`");
        var lhs = try self.parseUnary(depth + 1, is_eval);
        while (self.pos < self.tokens.len) {
            const op = self.tokens[self.pos].kind;
            const prec = getBinaryPrecedence(op) orelse break;
            if (prec < min_prec) break;
            self.pos += 1;

            const is_rhs_eval = switch (op) {
                .pipe_pipe => is_eval and !lhs.isTruthy(),
                .amp_amp => is_eval and lhs.isTruthy(),
                else => is_eval,
            };
            const rhs = try self.parseBinary(depth + 1, prec + 1, is_rhs_eval);
            const is_common_unsigned = lhs.is_unsigned or rhs.is_unsigned;

            lhs = switch (op) {
                .pipe_pipe => .{ .bits = @intFromBool(lhs.isTruthy() or rhs.isTruthy()), .is_unsigned = false },
                .amp_amp => .{ .bits = @intFromBool(lhs.isTruthy() and rhs.isTruthy()), .is_unsigned = false },
                .pipe => .{ .bits = lhs.bits | rhs.bits, .is_unsigned = is_common_unsigned },
                .caret => .{ .bits = lhs.bits ^ rhs.bits, .is_unsigned = is_common_unsigned },
                .amp => .{ .bits = lhs.bits & rhs.bits, .is_unsigned = is_common_unsigned },
                .eq_eq => .{ .bits = @intFromBool(lhs.bits == rhs.bits), .is_unsigned = false },
                .bang_eq => .{ .bits = @intFromBool(lhs.bits != rhs.bits), .is_unsigned = false },
                .lt => .{
                    .bits = @intFromBool(if (is_common_unsigned) lhs.bits < rhs.bits else lhs.asSigned() < rhs.asSigned()),
                    .is_unsigned = false,
                },
                .le => .{
                    .bits = @intFromBool(if (is_common_unsigned) lhs.bits <= rhs.bits else lhs.asSigned() <= rhs.asSigned()),
                    .is_unsigned = false,
                },
                .gt => .{
                    .bits = @intFromBool(if (is_common_unsigned) lhs.bits > rhs.bits else lhs.asSigned() > rhs.asSigned()),
                    .is_unsigned = false,
                },
                .ge => .{
                    .bits = @intFromBool(if (is_common_unsigned) lhs.bits >= rhs.bits else lhs.asSigned() >= rhs.asSigned()),
                    .is_unsigned = false,
                },
                .shl => blk: {
                    const sh: u6 = @intCast(@min(rhs.bits, 63));
                    break :blk .{ .bits = if (rhs.bits >= 64) 0 else lhs.bits << sh, .is_unsigned = lhs.is_unsigned };
                },
                .shr => blk: {
                    const sh: u6 = @intCast(@min(rhs.bits, 63));
                    const shifted: u64 = if (lhs.is_unsigned)
                        (if (rhs.bits >= 64) 0 else lhs.bits >> sh)
                    else
                        @bitCast(lhs.asSigned() >> sh);
                    break :blk .{ .bits = shifted, .is_unsigned = lhs.is_unsigned };
                },
                .plus => .{ .bits = lhs.bits +% rhs.bits, .is_unsigned = is_common_unsigned },
                .minus => .{ .bits = lhs.bits -% rhs.bits, .is_unsigned = is_common_unsigned },
                .star => .{ .bits = lhs.bits *% rhs.bits, .is_unsigned = is_common_unsigned },
                .slash => blk: {
                    if (!is_eval) break :blk .{ .bits = 0, .is_unsigned = is_common_unsigned };
                    if (rhs.bits == 0) return self.fail("division by zero in C constant expression");
                    if (is_common_unsigned) break :blk .{ .bits = lhs.bits / rhs.bits, .is_unsigned = true };
                    if (lhs.asSigned() == std.math.minInt(i64) and rhs.asSigned() == -1) {
                        break :blk .{ .bits = lhs.bits, .is_unsigned = false };
                    }
                    break :blk .{ .bits = @bitCast(@divTrunc(lhs.asSigned(), rhs.asSigned())), .is_unsigned = false };
                },
                .percent => blk: {
                    if (!is_eval) break :blk .{ .bits = 0, .is_unsigned = is_common_unsigned };
                    if (rhs.bits == 0) return self.fail("remainder by zero in C constant expression");
                    if (is_common_unsigned) break :blk .{ .bits = lhs.bits % rhs.bits, .is_unsigned = true };
                    if (lhs.asSigned() == std.math.minInt(i64) and rhs.asSigned() == -1) {
                        break :blk .{ .bits = 0, .is_unsigned = false };
                    }
                    break :blk .{ .bits = @bitCast(@rem(lhs.asSigned(), rhs.asSigned())), .is_unsigned = false };
                },
                else => unreachable,
            };
        }
        return lhs;
    }

    /// Evaluates unary `+`, `-`, `~`, `!`, `sizeof`, casts `(Type)expr`, and primary atoms.
    fn parseUnary(self: *ConstExprEvaluator, depth: u32, is_eval: bool) CFrontendError!CIntVal {
        if (depth >= self.max_depth) return self.fail("C constant expression exceeded `MAX_C_PARSE_DEPTH`");
        if (self.pos >= self.tokens.len) return self.fail("unexpected end of C constant expression");

        const tok = self.tokens[self.pos];
        switch (tok.kind) {
            .plus => {
                self.pos += 1;
                return self.parseUnary(depth + 1, is_eval);
            },
            .minus => {
                self.pos += 1;
                const inner = try self.parseUnary(depth + 1, is_eval);
                return .{ .bits = 0 -% inner.bits, .is_unsigned = inner.is_unsigned };
            },
            .tilde => {
                self.pos += 1;
                const inner = try self.parseUnary(depth + 1, is_eval);
                return .{ .bits = ~inner.bits, .is_unsigned = inner.is_unsigned };
            },
            .bang => {
                self.pos += 1;
                const inner = try self.parseUnary(depth + 1, is_eval);
                return .{ .bits = @intFromBool(!inner.isTruthy()), .is_unsigned = false };
            },
            .lparen => {
                // Support C integer type casts `(uint32_t)-1` inside constant expressions:
                if (self.parser_ctx) |pctx| {
                    if (self.pos + 1 < self.tokens.len and pctx.isTypeStartToken(self.tokens[self.pos + 1])) {
                        const saved_p_pos = pctx.pos;
                        const saved_p_toks = pctx.tokens;
                        pctx.tokens = self.tokens;
                        pctx.pos = self.pos + 1;
                        const cast_ty = pctx.parseTypeName(depth + 1) catch null;
                        if (cast_ty != null and pctx.pos < self.tokens.len and
                            self.tokens[pctx.pos].kind == .rparen)
                        {
                            self.pos = pctx.pos + 1;
                            pctx.tokens = saved_p_toks;
                            pctx.pos = saved_p_pos;
                            const cast_operand = try self.parseUnary(depth + 1, is_eval);
                            return self.applyIntegerCast(cast_ty.?, cast_operand);
                        }
                        pctx.tokens = saved_p_toks;
                        pctx.pos = saved_p_pos;
                    }
                }
                self.pos += 1;
                const inner = try self.parseExpr(depth + 1, is_eval);
                if (self.pos >= self.tokens.len or self.tokens[self.pos].kind != .rparen) {
                    return self.fail("unclosed `(` in C constant expression");
                }
                self.pos += 1;
                return inner;
            },
            .number => {
                self.pos += 1;
                return parseCIntegerLiteral(tok.lexeme) orelse
                    self.fail("invalid integer literal in C constant expression");
            },
            .char_lit => {
                self.pos += 1;
                return parseCCharLiteral(tok.lexeme, self.unit.target) orelse
                    self.fail("invalid character literal in C constant expression");
            },
            .ident => {
                if (std.mem.eql(u8, tok.lexeme, "sizeof") and self.parser_ctx != null) {
                    const pctx = self.parser_ctx.?;
                    self.pos += 1;
                    if (self.pos < self.tokens.len and self.tokens[self.pos].kind == .lparen) {
                        const saved_p_pos = pctx.pos;
                        const saved_p_toks = pctx.tokens;
                        pctx.tokens = self.tokens;
                        pctx.pos = self.pos + 1;
                        const sz_ty = try pctx.parseTypeName(depth + 1);
                        if (pctx.pos >= self.tokens.len or self.tokens[pctx.pos].kind != .rparen) {
                            pctx.tokens = saved_p_toks;
                            pctx.pos = saved_p_pos;
                            return self.fail("expected `)` after `sizeof(type)`");
                        }
                        self.pos = pctx.pos + 1;
                        pctx.tokens = saved_p_toks;
                        pctx.pos = saved_p_pos;
                        return .{ .bits = pctx.estimateTypeSizeBytes(sz_ty, depth + 1), .is_unsigned = true };
                    }
                }
                if (std.mem.eql(u8, tok.lexeme, "true")) {
                    self.pos += 1;
                    return .{ .bits = 1, .is_unsigned = false };
                } else if (std.mem.eql(u8, tok.lexeme, "false")) {
                    self.pos += 1;
                    return .{ .bits = 0, .is_unsigned = false };
                } else if (self.known_consts) |const_map| {
                    if (const_map.get(tok.lexeme)) |cval| {
                        self.pos += 1;
                        if (cval < 0) {
                            const s64: i64 = @intCast(cval);
                            return .{ .bits = @bitCast(s64), .is_unsigned = false };
                        }
                        return .{
                            .bits = @intCast(cval),
                            .is_unsigned = cval > @as(i128, std.math.maxInt(i64)),
                        };
                    }
                }
                return self.fail("unresolved identifier in C constant expression");
            },
            else => return self.fail("unexpected token in C constant expression"),
        }
    }

    /// Truncates or sign-extends `operand` when cast to a C integer primitive `target_ty`.
    fn applyIntegerCast(self: *const ConstExprEvaluator, target_ty: CTypeId, operand: CIntVal) CIntVal {
        const canon_id = self.unit.unwrapTypedefs(target_ty);
        const node = self.unit.getType(canon_id);
        if (node != .primitive) return operand;
        const prim = node.primitive;
        if (prim == .c_bool) return .{ .bits = @intFromBool(operand.bits != 0), .is_unsigned = true };
        if (!prim.isInteger()) return operand;
        const byte_sz = prim.byteSize(self.unit.target);
        const is_signed = prim.isSignedInteger(self.unit.target);
        return switch (byte_sz) {
            1 => if (is_signed)
                .{ .bits = @bitCast(@as(i64, @as(i8, @truncate(operand.asSigned())))), .is_unsigned = false }
            else
                .{ .bits = @as(u8, @truncate(operand.bits)), .is_unsigned = true },
            2 => if (is_signed)
                .{ .bits = @bitCast(@as(i64, @as(i16, @truncate(operand.asSigned())))), .is_unsigned = false }
            else
                .{ .bits = @as(u16, @truncate(operand.bits)), .is_unsigned = true },
            4 => if (is_signed)
                .{ .bits = @bitCast(@as(i64, @as(i32, @truncate(operand.asSigned())))), .is_unsigned = false }
            else
                .{ .bits = @as(u32, @truncate(operand.bits)), .is_unsigned = true },
            else => .{ .bits = operand.bits, .is_unsigned = !is_signed },
        };
    }
};

/// Returns climbing precedence (`1..10`) for binary C operators in constant expressions.
fn getBinaryPrecedence(kind: CTokenKind) ?u8 {
    return switch (kind) {
        .pipe_pipe => 1,
        .amp_amp => 2,
        .pipe => 3,
        .caret => 4,
        .amp => 5,
        .eq_eq, .bang_eq => 6,
        .lt, .le, .gt, .ge => 7,
        .shl, .shr => 8,
        .plus, .minus => 9,
        .star, .slash, .percent => 10,
        else => null,
    };
}

// --------------------- Declaration Parser ---------------------

/// C11/C23 recursive-descent declaration and type-specifier parser (`DR-10` §2.1, `DR-20` Seam #6).
const CDeclParser = struct {
    /// Target translation unit.
    unit: *CTranslationUnit,
    /// Diagnostic sink for `E0009` errors.
    sink: *DiagnosticSink,
    /// Frontend options (`body_hook`, `max_parse_depth`).
    options: CFrontendOptions,
    /// Preprocessed token stream.
    tokens: []const CToken,
    /// Current token index.
    pos: usize = 0,
    /// Lexical `typedef` name -> `CTypeId` map for declarator disambiguation.
    typedef_names: std.StringHashMapUnmanaged(CTypeId) = .empty,
    /// Tag table for `struct Name` -> `CDeclId`.
    struct_tags: std.StringHashMapUnmanaged(CDeclId) = .empty,
    /// Tag table for `union Name` -> `CDeclId`.
    union_tags: std.StringHashMapUnmanaged(CDeclId) = .empty,
    /// Tag table for `enum Name` -> `CDeclId`.
    enum_tags: std.StringHashMapUnmanaged(CDeclId) = .empty,
    /// Known enumerator and `static const` integer values for subsequent constant expressions.
    known_int_consts: std.StringHashMapUnmanaged(i128) = .empty,
    /// Active `#pragma pack(N)` alignment (`0` = default natural alignment).
    active_pack_align: u8 = 0,
    /// Stack of pushed `#pragma pack(push, …)` states.
    pack_stack: std.ArrayListUnmanaged(u8) = .empty,

    /// Releases parser lookup tables.
    fn deinit(self: *CDeclParser) void {
        self.typedef_names.deinit(self.unit.allocator);
        self.struct_tags.deinit(self.unit.allocator);
        self.union_tags.deinit(self.unit.allocator);
        self.enum_tags.deinit(self.unit.allocator);
        self.known_int_consts.deinit(self.unit.allocator);
        self.pack_stack.deinit(self.unit.allocator);
    }

    /// Consumes any pending `.pragma_pack` tokens and updates `active_pack_align`.
    fn flushPragmaPack(self: *CDeclParser) !void {
        while (self.pos < self.tokens.len and self.tokens[self.pos].kind == .pragma_pack) {
            const pk = self.tokens[self.pos];
            self.pos += 1;
            switch (pk.pack_op) {
                .reset_pack => self.active_pack_align = 0,
                .set_pack => self.active_pack_align = pk.pack_align,
                .push_only => try self.pack_stack.append(self.unit.allocator, self.active_pack_align),
                .push_pack => {
                    try self.pack_stack.append(self.unit.allocator, self.active_pack_align);
                    self.active_pack_align = pk.pack_align;
                },
                .pop_pack => {
                    if (self.pack_stack.pop()) |restored| {
                        self.active_pack_align = restored;
                    } else {
                        self.active_pack_align = 0;
                    }
                },
            }
        }
    }

    /// Peeks the current non-pragma token kind (`.eof` at end of stream).
    fn peekKind(self: *CDeclParser) !CTokenKind {
        try self.flushPragmaPack();
        return if (self.pos < self.tokens.len) self.tokens[self.pos].kind else .eof;
    }

    /// Peeks the current non-pragma `CToken`.
    fn peekToken(self: *CDeclParser) !CToken {
        try self.flushPragmaPack();
        if (self.pos < self.tokens.len) return self.tokens[self.pos];
        return .{
            .kind = .eof,
            .lexeme = "",
            .span = if (self.tokens.len > 0) self.tokens[self.tokens.len - 1].span else Span.ZERO,
        };
    }

    /// Emits `E0009` at the current token and returns `error.TranslationFailed`.
    fn failHere(self: *CDeclParser, msg: []const u8) CFrontendError {
        const span = if (self.pos < self.tokens.len)
            self.tokens[self.pos].span
        else if (self.tokens.len > 0)
            self.tokens[self.tokens.len - 1].span
        else
            Span.ZERO;
        try emitCTranslationError(self.unit, self.sink, span, msg);
        return error.TranslationFailed;
    }

    /// Returns `true` if `tok` can begin a C declaration-specifier or type-name.
    fn isTypeStartToken(self: *const CDeclParser, tok: CToken) bool {
        if (tok.kind == .lbracket and self.pos + 1 < self.tokens.len and
            self.tokens[self.pos + 1].kind == .lbracket)
        {
            return true;
        }
        if (tok.kind != .ident) return false;
        if (C_SPECIFIER_KEYWORD_SET.has(tok.lexeme)) return true;
        if (isSalOrNullabilityIdent(tok.lexeme)) return true;
        return self.typedef_names.contains(tok.lexeme);
    }

    /// Parses the entire translation unit declaration stream.
    fn parseTranslationUnit(self: *CDeclParser) CFrontendError!void {
        while ((try self.peekKind()) != .eof) {
            try self.parseExternalDeclaration(0);
        }
    }

    /// Parses a top-level C declaration, `_Static_assert`, or `extern "C" { … }` linkage block.
    fn parseExternalDeclaration(self: *CDeclParser, depth: u32) CFrontendError!void {
        if (depth >= self.options.max_parse_depth) {
            return self.failHere("C declaration nesting exceeded `MAX_C_PARSE_DEPTH`");
        }
        const cur_tok = try self.peekToken();
        if (cur_tok.kind == .semi) {
            self.pos += 1;
            return;
        }

        // Support `extern "C" { … }` blocks in mixed C/C++ headers:
        if (cur_tok.kind == .ident and std.mem.eql(u8, cur_tok.lexeme, "extern") and
            self.pos + 1 < self.tokens.len and self.tokens[self.pos + 1].kind == .string_lit)
        {
            self.pos += 2;
            if ((try self.peekKind()) == .lbrace) {
                self.pos += 1;
                while ((try self.peekKind()) != .rbrace and (try self.peekKind()) != .eof) {
                    try self.parseExternalDeclaration(depth + 1);
                }
                if ((try self.peekKind()) != .rbrace) {
                    return self.failHere("unclosed `extern \"C\" {` block in C header");
                }
                self.pos += 1;
                return;
            }
            try self.parseExternalDeclaration(depth + 1);
            return;
        }

        // C11 `_Static_assert(expr, "msg");` / C23 `static_assert(expr);`:
        if (cur_tok.kind == .ident and
            (std.mem.eql(u8, cur_tok.lexeme, "_Static_assert") or
                std.mem.eql(u8, cur_tok.lexeme, "static_assert")))
        {
            try self.parseStaticAssert(depth + 1);
            return;
        }

        const specs = try self.parseDeclSpecs(depth + 1);

        // Standalone tag declaration (`struct Foo;`, `struct Foo { … };`, `enum Bar { … };`):
        if ((try self.peekKind()) == .semi) {
            self.pos += 1;
            return;
        }

        var decl_index: usize = 0;
        while (true) : (decl_index += 1) {
            const decl = try self.parseDeclarator(specs, depth + 1, false);
            var post_contract = decl.contract;
            var post_noreturn = specs.is_noreturn;
            var post_nonnull_mask = specs.nonnull_param_mask;
            var post_align = specs.explicit_align;
            var post_packed = specs.is_packed;
            var post_dll = specs.dll_storage;
            try self.consumeLeadingOrTrailingAttributes(
                depth + 1,
                &post_contract,
                &post_noreturn,
                &post_nonnull_mask,
                &post_align,
                &post_packed,
                &post_dll,
            );
            // Skip optional GNU `asm("symbol")` linker redirect if present:
            if ((try self.peekKind()) == .ident and
                (std.mem.eql(u8, self.tokens[self.pos].lexeme, "asm") or
                    std.mem.eql(u8, self.tokens[self.pos].lexeme, "__asm") or
                    std.mem.eql(u8, self.tokens[self.pos].lexeme, "__asm__")))
            {
                self.pos += 1;
                try self.skipBalancedParens();
                try self.consumeLeadingOrTrailingAttributes(
                    depth + 1,
                    &post_contract,
                    &post_noreturn,
                    &post_nonnull_mask,
                    &post_align,
                    &post_packed,
                    &post_dll,
                );
            }

            if (specs.is_typedef) {
                if (decl.name.len == 0) return self.failHere("missing identifier in C `typedef` declaration");
                if (!cur_tok.is_from_system_header and self.hasUnsupportedFnLongDouble(decl.type_id, 0)) {
                    try emitCTranslationError(
                        self.unit,
                        self.sink,
                        decl.span,
                        "non-8-byte `long double` by-value ABI is unsupported in C function types on this target",
                    );
                    return error.TranslationFailed;
                }
                const decl_id = CDeclId.fromInt(@intCast(self.unit.decls.items.len));
                try self.unit.decls.append(self.unit.allocator, .{
                    .kind = .{ .typedef_decl = .{ .name = decl.name, .target_type = decl.type_id } },
                    .span = decl.span,
                    .is_from_system_header = cur_tok.is_from_system_header,
                });
                const td_ref_ty = try self.unit.appendType(.{ .typedef_ref = decl_id });
                try self.typedef_names.put(self.unit.allocator, decl.name, td_ref_ty);
            } else {
                const unwrapped = self.unit.getType(decl.type_id);
                if (unwrapped == .function) {
                    const fn_info = unwrapped.function;
                    self.applyNonnullParamMask(fn_info.param_start, fn_info.param_len, post_nonnull_mask);

                    const has_body = decl_index == 0 and (try self.peekKind()) == .lbrace;
                    var body_first: CTokenId = .none;
                    var body_end: CTokenId = .none;
                    if (has_body) {
                        body_first = CTokenId.fromInt(@intCast(self.pos));
                        try self.skipBalancedBraces();
                        body_end = CTokenId.fromInt(@intCast(self.pos));
                    }

                    if (!cur_tok.is_from_system_header and !specs.is_static and !has_body and
                        self.hasUnsupportedByValueLongDoubleSig(
                            fn_info.return_type,
                            fn_info.param_start,
                            fn_info.param_len,
                        ))
                    {
                        try emitCTranslationError(
                            self.unit,
                            self.sink,
                            decl.span,
                            "non-8-byte `long double` by-value ABI is unsupported in C function prototypes on this target",
                        );
                        return error.TranslationFailed;
                    }

                    const fn_decl_id = CDeclId.fromInt(@intCast(self.unit.decls.items.len));
                    try self.unit.decls.append(self.unit.allocator, .{
                        .kind = .{
                            .fn_decl = .{
                                .name = decl.name,
                                .return_type = fn_info.return_type,
                                .param_start = fn_info.param_start,
                                .param_len = fn_info.param_len,
                                .is_variadic = fn_info.is_variadic,
                                .is_static = specs.is_static,
                                .is_inline = specs.is_inline,
                                .is_noreturn = post_noreturn or fn_info.is_noreturn,
                                .has_body = has_body,
                                .body_first_token = body_first,
                                .body_end_token = body_end,
                                .ret_contract = post_contract,
                                .dll_storage = post_dll,
                            },
                        },
                        .span = decl.span,
                        .is_from_system_header = cur_tok.is_from_system_header,
                    });

                    // `DR-20` Seam #6 (`CFunctionBodyHook`, <= 20 LOC):
                    if (has_body) {
                        if (self.options.body_hook) |hook_fn| {
                            try hook_fn(self.unit, fn_decl_id, body_first, body_end, self.sink);
                        }
                        if ((try self.peekKind()) == .semi) self.pos += 1;
                        return;
                    }
                } else {
                    var init_const_val: ?MacroConstValue = null;
                    if ((try self.peekKind()) == .eq) {
                        self.pos += 1;
                        init_const_val = try self.parseInitializerOrConstVal(depth + 1);
                        if (decl.is_top_const and decl.name.len > 0) {
                            if (init_const_val) |cv| {
                                switch (cv) {
                                    .signed_int => |sv| try self.known_int_consts.put(
                                        self.unit.allocator,
                                        decl.name,
                                        sv,
                                    ),
                                    .unsigned_int => |uv| try self.known_int_consts.put(
                                        self.unit.allocator,
                                        decl.name,
                                        uv,
                                    ),
                                    else => {},
                                }
                            }
                        }
                    }
                    try self.unit.decls.append(self.unit.allocator, .{
                        .kind = .{
                            .var_decl = .{
                                .name = decl.name,
                                .type_id = decl.type_id,
                                .is_extern = specs.is_extern or (!specs.is_static and init_const_val == null),
                                .is_static = specs.is_static,
                                .is_const = decl.is_top_const,
                                .const_val = init_const_val,
                                .dll_storage = post_dll,
                            },
                        },
                        .span = decl.span,
                        .is_from_system_header = cur_tok.is_from_system_header,
                    });
                }
            }

            if ((try self.peekKind()) == .comma) {
                self.pos += 1;
                continue;
            }
            break;
        }

        if ((try self.peekKind()) != .semi) {
            return self.failHere("expected `;` at end of C declaration");
        }
        self.pos += 1;
    }

    /// Evaluates `_Static_assert(expr [, "msg"]);` / C23 `static_assert(expr);` at translation time.
    fn parseStaticAssert(self: *CDeclParser, depth: u32) CFrontendError!void {
        const kw_tok = try self.peekToken();
        self.pos += 1;
        if ((try self.peekKind()) != .lparen) {
            return self.failHere("expected `(` after `_Static_assert`");
        }
        self.pos += 1;
        const cond_val = try self.parseConstantIntExprUntilCommaOrRparen(depth + 1);
        var msg_text: []const u8 = "C `_Static_assert` condition evaluated to 0";
        if ((try self.peekKind()) == .comma) {
            self.pos += 1;
            if ((try self.peekKind()) == .string_lit) {
                const decoded = try decodeCStringLiteral(&self.unit.arena, self.tokens[self.pos].lexeme);
                msg_text = try std.fmt.allocPrint(
                    self.unit.arena.asAllocator(),
                    "C `_Static_assert` failed: {s}",
                    .{decoded},
                );
                self.pos += 1;
            }
        }
        if ((try self.peekKind()) != .rparen) {
            return self.failHere("expected `)` to close `_Static_assert`");
        }
        self.pos += 1;
        if ((try self.peekKind()) == .semi) self.pos += 1;

        if (cond_val == 0) {
            try emitCTranslationError(self.unit, self.sink, kw_tok.span, msg_text);
            return error.TranslationFailed;
        }
    }

    /// Parses C11/C23 declaration specifiers, qualifiers, SAL annotations, and struct/union/enum tags.
    fn parseDeclSpecs(self: *CDeclParser, depth: u32) CFrontendError!ParsedDeclSpecs {
        if (depth >= self.options.max_parse_depth) {
            return self.failHere("C specifier nesting exceeded `MAX_C_PARSE_DEPTH`");
        }
        var out = ParsedDeclSpecs{ .type_id = .none };
        var has_void = false;
        var has_bool = false;
        var has_char = false;
        var has_short = false;
        var has_int = false;
        var long_count: u8 = 0;
        var has_int128 = false;
        var has_float = false;
        var has_double = false;
        var has_signed = false;
        var has_unsigned = false;
        var is_atomic_qual = false;
        var explicit_type_id: CTypeId = .none;

        while (true) {
            try self.consumeLeadingOrTrailingAttributes(
                depth + 1,
                &out.contract,
                &out.is_noreturn,
                &out.nonnull_param_mask,
                &out.explicit_align,
                &out.is_packed,
                &out.dll_storage,
            );
            const tok = try self.peekToken();
            if (tok.kind != .ident) break;
            const lex = tok.lexeme;

            if (std.mem.eql(u8, lex, "typedef")) {
                out.is_typedef = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "extern")) {
                out.is_extern = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "static")) {
                out.is_static = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "inline") or
                std.mem.eql(u8, lex, "__inline") or
                std.mem.eql(u8, lex, "__inline__") or
                std.mem.eql(u8, lex, "__forceinline"))
            {
                out.is_inline = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_Noreturn")) {
                out.is_noreturn = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "auto") or
                std.mem.eql(u8, lex, "register") or
                std.mem.eql(u8, lex, "_Thread_local") or
                std.mem.eql(u8, lex, "thread_local") or
                std.mem.eql(u8, lex, "__thread") or
                std.mem.eql(u8, lex, "__extension__") or
                isCallingConvIdent(lex))
            {
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "const") or
                std.mem.eql(u8, lex, "__const") or
                std.mem.eql(u8, lex, "__const__"))
            {
                out.is_const = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "volatile") or
                std.mem.eql(u8, lex, "__volatile") or
                std.mem.eql(u8, lex, "__volatile__") or
                std.mem.eql(u8, lex, "restrict") or
                std.mem.eql(u8, lex, "__restrict") or
                std.mem.eql(u8, lex, "__restrict__"))
            {
                if (std.mem.startsWith(u8, lex, "volatile") or std.mem.startsWith(u8, lex, "__volatile")) {
                    out.is_volatile = true;
                }
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_Atomic")) {
                self.pos += 1;
                if ((try self.peekKind()) == .lparen and explicit_type_id.isNone()) {
                    self.pos += 1;
                    const inner_ty = try self.parseTypeName(depth + 1);
                    if ((try self.peekKind()) != .rparen) return self.failHere("expected `)` after `_Atomic(T)`");
                    self.pos += 1;
                    explicit_type_id = try self.unit.appendType(.{ .atomic_val = inner_ty });
                } else {
                    is_atomic_qual = true;
                }
            } else if (std.mem.eql(u8, lex, "void")) {
                has_void = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_Bool") or std.mem.eql(u8, lex, "bool")) {
                has_bool = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "char")) {
                has_char = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "short")) {
                has_short = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "int")) {
                has_int = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "long")) {
                long_count += 1;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "__int128")) {
                has_int128 = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "float")) {
                has_float = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "double")) {
                has_double = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "signed") or
                std.mem.eql(u8, lex, "__signed") or
                std.mem.eql(u8, lex, "__signed__"))
            {
                has_signed = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "unsigned")) {
                has_unsigned = true;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "struct") or std.mem.eql(u8, lex, "union")) {
                const is_union = std.mem.eql(u8, lex, "union");
                self.pos += 1;
                explicit_type_id = try self.parseStructOrUnionSpecifier(is_union, depth + 1);
            } else if (std.mem.eql(u8, lex, "enum")) {
                self.pos += 1;
                explicit_type_id = try self.parseEnumSpecifier(depth + 1);
            } else {
                const has_any_prim = !explicit_type_id.isNone() or has_void or has_bool or has_char or
                    has_short or has_int or long_count > 0 or has_int128 or has_float or has_double or
                    has_signed or has_unsigned;
                if (has_any_prim) break;

                if (BUILTIN_EXACT_TYPE_MAP.get(lex)) |exact_prim| {
                    self.pos += 1;
                    explicit_type_id = try self.unit.appendType(.{ .primitive = exact_prim });
                } else if (self.typedef_names.get(lex)) |td_ty| {
                    self.pos += 1;
                    explicit_type_id = td_ty;
                } else {
                    break;
                }
            }
        }

        if (explicit_type_id.isNone()) {
            const prim: CPrimitiveKind = if (has_void)
                .c_void
            else if (has_bool)
                .c_bool
            else if (has_float)
                .c_float
            else if (has_double)
                (if (long_count > 0) .c_longdouble else .c_double)
            else if (has_int128)
                (if (has_unsigned) .c_uint128 else .c_int128)
            else if (has_char)
                (if (has_unsigned) .c_uchar else if (has_signed) .c_schar else .c_char)
            else if (has_short)
                (if (has_unsigned) .c_ushort else .c_short)
            else if (long_count >= 2)
                (if (has_unsigned) .c_ulonglong else .c_longlong)
            else if (long_count == 1)
                (if (has_unsigned) .c_ulong else .c_long)
            else if (has_unsigned)
                .c_uint
            else if (has_int or has_signed)
                .c_int
            else
                return self.failHere("expected C type specifier in declaration");

            explicit_type_id = try self.unit.appendType(.{ .primitive = prim });
        }

        if (is_atomic_qual) {
            explicit_type_id = try self.unit.appendType(.{ .atomic_val = explicit_type_id });
        }
        out.type_id = explicit_type_id;
        return out;
    }

    /// Parses `struct [Attrs] [Tag] [{ Fields… }]` or `union [Attrs] [Tag] [{ Fields… }]`.
    fn parseStructOrUnionSpecifier(self: *CDeclParser, is_union: bool, depth: u32) CFrontendError!CTypeId {
        const start_tok = try self.peekToken();
        var layout = CRecordLayoutAttrs{ .pragma_pack = self.active_pack_align };
        try self.consumeRecordAttributes(depth + 1, &layout);

        var tag_name: []const u8 = "";
        if ((try self.peekKind()) == .ident and !isAttributeKeyword(self.tokens[self.pos].lexeme)) {
            tag_name = self.tokens[self.pos].lexeme;
            self.pos += 1;
        }
        try self.consumeRecordAttributes(depth + 1, &layout);

        const tag_map = if (is_union) &self.union_tags else &self.struct_tags;
        const has_body = (try self.peekKind()) == .lbrace;

        var decl_id: CDeclId = .none;
        if (tag_name.len > 0) {
            if (tag_map.get(tag_name)) |existing_id| {
                decl_id = existing_id;
            }
        }
        if (decl_id.isNone()) {
            decl_id = CDeclId.fromInt(@intCast(self.unit.decls.items.len));
            try self.unit.decls.append(self.unit.allocator, .{
                .kind = .{
                    .record_decl = .{
                        .is_union = is_union,
                        .name = tag_name,
                        .is_complete = false,
                        .field_start = 0,
                        .field_len = 0,
                        .layout_attrs = layout,
                    },
                },
                .span = start_tok.span,
                .is_from_system_header = start_tok.is_from_system_header,
            });
            if (tag_name.len > 0) {
                try tag_map.put(self.unit.allocator, tag_name, decl_id);
            }
        }

        if (has_body) {
            self.pos += 1;
            var local_fields: std.ArrayListUnmanaged(CStructField) = .empty;
            defer local_fields.deinit(self.unit.allocator);

            while ((try self.peekKind()) != .rbrace and (try self.peekKind()) != .eof) {
                const f_tok = try self.peekToken();
                if (f_tok.kind == .semi) {
                    self.pos += 1;
                    continue;
                }
                if (f_tok.kind == .ident and
                    (std.mem.eql(u8, f_tok.lexeme, "_Static_assert") or
                        std.mem.eql(u8, f_tok.lexeme, "static_assert")))
                {
                    try self.parseStaticAssert(depth + 1);
                    continue;
                }

                const f_specs = try self.parseDeclSpecs(depth + 1);

                // Anonymous nested `struct { … };` or `union { … };` member without declarator:
                if ((try self.peekKind()) == .semi) {
                    self.pos += 1;
                    const inner_ty = self.unit.getType(f_specs.type_id);
                    if (inner_ty == .record_ref) {
                        if (self.hasIncompleteRecordOrVoidByValue(f_specs.type_id, 0)) {
                            try emitCTranslationError(
                                self.unit,
                                self.sink,
                                f_tok.span,
                                "C struct or union field has incomplete or self-referential value type",
                            );
                            return error.TranslationFailed;
                        }
                        try local_fields.append(self.unit.allocator, .{
                            .name = "",
                            .type_id = f_specs.type_id,
                            .explicit_align = f_specs.explicit_align,
                            .is_packed_field = f_specs.is_packed,
                            .is_anonymous_record = true,
                            .span = f_tok.span,
                        });
                    }
                    continue;
                }

                while (true) {
                    if ((try self.peekKind()) == .colon) {
                        // Unnamed bitfield (`unsigned : 0;` or `unsigned : 4;`):
                        self.pos += 1;
                        const width_val = try self.parseConstantIntExprUntilCommaOrSemi(depth + 1);
                        if (width_val < 0 or width_val > 64) {
                            return self.failHere("C bitfield width out of valid `[0..64]` range");
                        }
                        if (!self.isValidBitfieldBaseType(f_specs.type_id)) {
                            try emitCTranslationError(
                                self.unit,
                                self.sink,
                                f_tok.span,
                                "C bitfield must have an integer, `_Bool`, or `enum` base type",
                            );
                            return error.TranslationFailed;
                        }
                        try local_fields.append(self.unit.allocator, .{
                            .name = "",
                            .type_id = f_specs.type_id,
                            .bit_width = @intCast(width_val),
                            .explicit_align = f_specs.explicit_align,
                            .is_packed_field = f_specs.is_packed,
                            .span = f_tok.span,
                        });
                    } else {
                        const f_decl = try self.parseDeclarator(f_specs, depth + 1, false);
                        var bit_width: ?u16 = null;
                        if ((try self.peekKind()) == .colon) {
                            self.pos += 1;
                            const width_val = try self.parseConstantIntExprUntilCommaOrSemi(depth + 1);
                            if (width_val < 0 or width_val > 64) {
                                return self.failHere("C bitfield width out of valid `[0..64]` range");
                            }
                            bit_width = @intCast(width_val);
                        }
                        var f_contract = f_decl.contract;
                        var dummy_nr = false;
                        var dummy_nn: u32 = 0;
                        var f_align = f_specs.explicit_align;
                        var f_packed = f_specs.is_packed;
                        var dummy_dll: CDllStorage = .none;
                        try self.consumeLeadingOrTrailingAttributes(
                            depth + 1,
                            &f_contract,
                            &dummy_nr,
                            &dummy_nn,
                            &f_align,
                            &f_packed,
                            &dummy_dll,
                        );
                        if (bit_width != null) {
                            if (!self.isValidBitfieldBaseType(f_decl.type_id)) {
                                try emitCTranslationError(
                                    self.unit,
                                    self.sink,
                                    f_decl.span,
                                    "C bitfield must have an integer, `_Bool`, or `enum` base type",
                                );
                                return error.TranslationFailed;
                            }
                        } else if (self.hasIncompleteRecordOrVoidByValue(f_decl.type_id, 0)) {
                            try emitCTranslationError(
                                self.unit,
                                self.sink,
                                f_decl.span,
                                "C struct or union field has incomplete or self-referential value type",
                            );
                            return error.TranslationFailed;
                        }
                        try local_fields.append(self.unit.allocator, .{
                            .name = f_decl.name,
                            .type_id = f_decl.type_id,
                            .bit_width = bit_width,
                            .explicit_align = f_align,
                            .is_packed_field = f_packed,
                            .contract = f_contract,
                            .span = f_decl.span,
                        });
                    }
                    if ((try self.peekKind()) == .comma) {
                        self.pos += 1;
                        continue;
                    }
                    break;
                }

                if ((try self.peekKind()) != .semi) {
                    return self.failHere("expected `;` after C struct/union member");
                }
                self.pos += 1;
            }

            if ((try self.peekKind()) != .rbrace) {
                return self.failHere("unclosed `{` in C struct/union definition");
            }
            self.pos += 1;
            try self.consumeRecordAttributes(depth + 1, &layout);

            const field_start: u32 = @intCast(self.unit.fields.items.len);
            try self.unit.fields.appendSlice(self.unit.allocator, local_fields.items);
            const rec_ptr = &self.unit.decls.items[decl_id.asInt()].kind.record_decl;
            rec_ptr.is_complete = true;
            rec_ptr.field_start = field_start;
            rec_ptr.field_len = @intCast(local_fields.items.len);
            rec_ptr.layout_attrs.is_packed = rec_ptr.layout_attrs.is_packed or layout.is_packed;
            rec_ptr.layout_attrs.is_ms_struct = rec_ptr.layout_attrs.is_ms_struct or layout.is_ms_struct;
            rec_ptr.layout_attrs.is_gcc_struct = rec_ptr.layout_attrs.is_gcc_struct or layout.is_gcc_struct;
            if (layout.pragma_pack != 0) rec_ptr.layout_attrs.pragma_pack = layout.pragma_pack;
            rec_ptr.layout_attrs.explicit_align = @max(
                rec_ptr.layout_attrs.explicit_align,
                layout.explicit_align,
            );
        }

        return self.unit.appendType(.{ .record_ref = decl_id });
    }

    /// Parses `enum [Attrs] [Tag] [: UnderlyingInt] [{ Variants… }]`.
    fn parseEnumSpecifier(self: *CDeclParser, depth: u32) CFrontendError!CTypeId {
        const start_tok = try self.peekToken();
        var dummy_layout = CRecordLayoutAttrs{};
        try self.consumeRecordAttributes(depth + 1, &dummy_layout);

        var tag_name: []const u8 = "";
        if ((try self.peekKind()) == .ident and !isAttributeKeyword(self.tokens[self.pos].lexeme)) {
            tag_name = self.tokens[self.pos].lexeme;
            self.pos += 1;
        }
        try self.consumeRecordAttributes(depth + 1, &dummy_layout);

        var underlying_prim: ?CPrimitiveKind = null;
        if ((try self.peekKind()) == .colon) {
            self.pos += 1;
            const under_specs = try self.parseDeclSpecs(depth + 1);
            const canon_under = self.unit.unwrapTypedefs(under_specs.type_id);
            const under_node = self.unit.getType(canon_under);
            if (under_node == .primitive and under_node.primitive.isInteger()) {
                underlying_prim = under_node.primitive;
            }
        }

        var decl_id: CDeclId = .none;
        if (tag_name.len > 0) {
            if (self.enum_tags.get(tag_name)) |existing_id| {
                decl_id = existing_id;
            }
        }
        if (decl_id.isNone()) {
            decl_id = CDeclId.fromInt(@intCast(self.unit.decls.items.len));
            try self.unit.decls.append(self.unit.allocator, .{
                .kind = .{
                    .enum_decl = .{
                        .name = tag_name,
                        .underlying_prim = underlying_prim,
                        .is_complete = false,
                        .variant_start = 0,
                        .variant_len = 0,
                    },
                },
                .span = start_tok.span,
                .is_from_system_header = start_tok.is_from_system_header,
            });
            if (tag_name.len > 0) {
                try self.enum_tags.put(self.unit.allocator, tag_name, decl_id);
            }
        }

        if ((try self.peekKind()) == .lbrace) {
            self.pos += 1;
            var local_variants: std.ArrayListUnmanaged(CEnumVariant) = .empty;
            defer local_variants.deinit(self.unit.allocator);
            var next_val: i128 = 0;

            while ((try self.peekKind()) != .rbrace and (try self.peekKind()) != .eof) {
                const v_tok = try self.peekToken();
                if (v_tok.kind != .ident) {
                    return self.failHere("expected enumerator identifier inside C `enum`");
                }
                const v_name = v_tok.lexeme;
                self.pos += 1;
                try self.consumeRecordAttributes(depth + 1, &dummy_layout);

                var has_explicit = false;
                if ((try self.peekKind()) == .eq) {
                    self.pos += 1;
                    next_val = try self.parseConstantIntExprUntilCommaOrRbrace(depth + 1);
                    has_explicit = true;
                }
                try self.known_int_consts.put(self.unit.allocator, v_name, next_val);
                try local_variants.append(self.unit.allocator, .{
                    .name = v_name,
                    .value = next_val,
                    .has_explicit_value = has_explicit,
                    .span = v_tok.span,
                });
                next_val += 1;

                if ((try self.peekKind()) == .comma) {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            if ((try self.peekKind()) != .rbrace) {
                return self.failHere("unclosed `{` in C `enum` definition");
            }
            self.pos += 1;
            try self.consumeRecordAttributes(depth + 1, &dummy_layout);

            const var_start: u32 = @intCast(self.unit.enum_variants.items.len);
            try self.unit.enum_variants.appendSlice(self.unit.allocator, local_variants.items);
            const enum_ptr = &self.unit.decls.items[decl_id.asInt()].kind.enum_decl;
            enum_ptr.is_complete = true;
            if (underlying_prim != null) enum_ptr.underlying_prim = underlying_prim;
            enum_ptr.variant_start = var_start;
            enum_ptr.variant_len = @intCast(local_variants.items.len);
        }

        return self.unit.appendType(.{ .enum_ref = decl_id });
    }

    /// Parses an abstract C type name (`sizeof(T)`, `_Atomic(T)`).
    fn parseTypeName(self: *CDeclParser, depth: u32) CFrontendError!CTypeId {
        return (try self.parseDeclarator(try self.parseDeclSpecs(depth + 1), depth + 1, true)).type_id;
    }

    /// Parses a direct or grouped inside-out C declarator (`*`, `(…)`, `[N]`, `(params…)`).
    fn parseDeclarator(
        self: *CDeclParser,
        specs: ParsedDeclSpecs,
        depth: u32,
        is_abstract_only: bool,
    ) CFrontendError!ParsedDeclarator {
        if (depth >= self.options.max_parse_depth) {
            return self.failHere("C declarator nesting exceeded `MAX_C_PARSE_DEPTH`");
        }
        var outer_mods: std.ArrayListUnmanaged(DeclaratorModifier) = .empty;
        defer outer_mods.deinit(self.unit.allocator);
        var inner_mods: std.ArrayListUnmanaged(DeclaratorModifier) = .empty;
        defer inner_mods.deinit(self.unit.allocator);

        var contract = specs.contract;
        const start_tok = try self.peekToken();
        var decl_name: []const u8 = "";
        var decl_span: Span = start_tok.span;

        // [1] Parse leading `*` pointer indirections:
        try self.parsePointerPrefixChain(depth + 1, &outer_mods, &contract);

        // [2] Check for grouped inner declarator `(*cb)` vs direct identifier:
        if (!is_abstract_only and (try self.peekKind()) == .lparen and self.isGroupedDeclaratorAhead()) {
            self.pos += 1;
            const inner_res = try self.parseGroupedInnerDeclarator(depth + 1, &inner_mods, &contract);
            decl_name = inner_res.name;
            decl_span = inner_res.span;
            if ((try self.peekKind()) != .rparen) {
                return self.failHere("expected `)` to close grouped C declarator");
            }
            self.pos += 1;
        } else if (is_abstract_only and (try self.peekKind()) == .lparen and self.isGroupedDeclaratorAhead()) {
            self.pos += 1;
            _ = try self.parseGroupedInnerDeclarator(depth + 1, &inner_mods, &contract);
            if ((try self.peekKind()) != .rparen) {
                return self.failHere("expected `)` to close abstract grouped C declarator");
            }
            self.pos += 1;
        } else if (!is_abstract_only and (try self.peekKind()) == .ident and
            !isSalOrNullabilityIdent(self.tokens[self.pos].lexeme) and
            !isAttributeKeyword(self.tokens[self.pos].lexeme))
        {
            decl_name = self.tokens[self.pos].lexeme;
            decl_span = self.tokens[self.pos].span;
            self.pos += 1;
        }

        // [3] Parse postfix `[len]` array and `(params…)` function suffixes on the outer level:
        var outer_postfixes: std.ArrayListUnmanaged(DeclaratorModifier) = .empty;
        defer outer_postfixes.deinit(self.unit.allocator);
        try self.parseDeclaratorPostfixes(depth + 1, &outer_postfixes);

        // [4] Assemble type from outermost base specifiers inward:
        var current_ty = specs.type_id;
        var is_pointee_const = specs.is_const;
        var is_pointee_volatile = specs.is_volatile;

        // Apply outer pointer chain (`const T *` makes first pointer point to `const T`):
        for (outer_mods.items) |pmod| {
            current_ty = try self.unit.appendType(.{
                .pointer = .{
                    .pointee = current_ty,
                    .is_const = is_pointee_const,
                    .is_volatile = is_pointee_volatile,
                    .is_restrict = pmod.pointer.is_ptr_restrict,
                    .nullability = pmod.pointer.nullability,
                },
            });
            is_pointee_const = pmod.pointer.is_ptr_const;
            is_pointee_volatile = pmod.pointer.is_ptr_volatile;
        }

        // Apply outer postfixes from right to left so `int a[2][3]` is `[ [int; 3]; 2 ]`:
        var op_idx = outer_postfixes.items.len;
        while (op_idx > 0) {
            op_idx -= 1;
            switch (outer_postfixes.items[op_idx]) {
                .array => |arr_len| {
                    current_ty = try self.unit.appendType(.{
                        .array = .{ .elem = current_ty, .len = arr_len },
                    });
                },
                .function => |fn_mod| {
                    current_ty = try self.unit.appendType(.{
                        .function = .{
                            .return_type = current_ty,
                            .param_start = fn_mod.param_start,
                            .param_len = fn_mod.param_len,
                            .is_variadic = fn_mod.is_variadic,
                            .is_noreturn = specs.is_noreturn,
                        },
                    });
                },
                .pointer => unreachable,
            }
            is_pointee_const = false;
            is_pointee_volatile = false;
        }

        // Apply grouped inner modifiers (`(*cb)(args)` wraps pointer around `fn(args) -> R`):
        for (inner_mods.items) |imod| {
            switch (imod) {
                .pointer => |pinfo| {
                    current_ty = try self.unit.appendType(.{
                        .pointer = .{
                            .pointee = current_ty,
                            .is_const = is_pointee_const,
                            .is_volatile = is_pointee_volatile,
                            .is_restrict = pinfo.is_ptr_restrict,
                            .nullability = pinfo.nullability,
                        },
                    });
                    is_pointee_const = pinfo.is_ptr_const;
                    is_pointee_volatile = pinfo.is_ptr_volatile;
                },
                .array => |arr_len| {
                    current_ty = try self.unit.appendType(.{
                        .array = .{ .elem = current_ty, .len = arr_len },
                    });
                    is_pointee_const = false;
                },
                .function => |fn_mod| {
                    current_ty = try self.unit.appendType(.{
                        .function = .{
                            .return_type = current_ty,
                            .param_start = fn_mod.param_start,
                            .param_len = fn_mod.param_len,
                            .is_variadic = fn_mod.is_variadic,
                        },
                    });
                    is_pointee_const = false;
                },
            }
        }

        // Propagate outermost pointer nullability onto `contract` if set via `_Nullable` / `_Nonnull`:
        const top_node = self.unit.getType(current_ty);
        if (top_node == .pointer and top_node.pointer.nullability != .unspecified and
            contract.nullability == .unspecified)
        {
            contract.nullability = top_node.pointer.nullability;
        }

        return .{
            .name = decl_name,
            .span = decl_span,
            .type_id = current_ty,
            .is_top_const = is_pointee_const,
            .contract = contract,
        };
    }

    /// Parses a parenthesized inner declarator (`*cb` or `*(*factory)(int)`).
    fn parseGroupedInnerDeclarator(
        self: *CDeclParser,
        depth: u32,
        out_mods: *std.ArrayListUnmanaged(DeclaratorModifier),
        contract: *CFfiContract,
    ) CFrontendError!struct { name: []const u8, span: Span } {
        if (depth >= self.options.max_parse_depth) {
            return self.failHere("C grouped declarator exceeded `MAX_C_PARSE_DEPTH`");
        }
        var lead_ptrs: std.ArrayListUnmanaged(DeclaratorModifier) = .empty;
        defer lead_ptrs.deinit(self.unit.allocator);
        try self.parsePointerPrefixChain(depth + 1, &lead_ptrs, contract);

        var name: []const u8 = "";
        var span: Span = (try self.peekToken()).span;
        var deeper_mods: std.ArrayListUnmanaged(DeclaratorModifier) = .empty;
        defer deeper_mods.deinit(self.unit.allocator);

        if ((try self.peekKind()) == .lparen and self.isGroupedDeclaratorAhead()) {
            self.pos += 1;
            const sub = try self.parseGroupedInnerDeclarator(depth + 1, &deeper_mods, contract);
            name = sub.name;
            span = sub.span;
            if ((try self.peekKind()) != .rparen) {
                return self.failHere("expected `)` in nested C declarator");
            }
            self.pos += 1;
        } else if ((try self.peekKind()) == .ident and
            !isSalOrNullabilityIdent(self.tokens[self.pos].lexeme) and
            !isAttributeKeyword(self.tokens[self.pos].lexeme))
        {
            name = self.tokens[self.pos].lexeme;
            span = self.tokens[self.pos].span;
            self.pos += 1;
        }

        var local_postfixes: std.ArrayListUnmanaged(DeclaratorModifier) = .empty;
        defer local_postfixes.deinit(self.unit.allocator);
        try self.parseDeclaratorPostfixes(depth + 1, &local_postfixes);

        try out_mods.appendSlice(self.unit.allocator, lead_ptrs.items);
        var p_idx = local_postfixes.items.len;
        while (p_idx > 0) {
            p_idx -= 1;
            try out_mods.append(self.unit.allocator, local_postfixes.items[p_idx]);
        }
        try out_mods.appendSlice(self.unit.allocator, deeper_mods.items);
        return .{ .name = name, .span = span };
    }

    /// Returns `true` when `(` at `self.pos` opens a grouped declarator rather than a parameter list.
    fn isGroupedDeclaratorAhead(self: *const CDeclParser) bool {
        if (self.pos + 1 >= self.tokens.len) return false;
        const next_tok = self.tokens[self.pos + 1];
        if (next_tok.kind == .rparen or next_tok.kind == .ellipses) return false;
        if (next_tok.kind == .star or next_tok.kind == .lparen or next_tok.kind == .lbracket) return true;
        if (next_tok.kind == .ident) {
            if (isCallingConvIdent(next_tok.lexeme) or isAttributeKeyword(next_tok.lexeme)) return true;
            return !self.isTypeStartToken(next_tok);
        }
        return false;
    }

    /// Parses zero or more `*` pointer prefixes and trailing pointer qualifiers (`const`, `_Nonnull`, etc.).
    fn parsePointerPrefixChain(
        self: *CDeclParser,
        depth: u32,
        out_mods: *std.ArrayListUnmanaged(DeclaratorModifier),
        contract: *CFfiContract,
    ) CFrontendError!void {
        while (true) {
            var dummy_nr = false;
            var dummy_nn: u32 = 0;
            var dummy_al: u32 = 0;
            var dummy_pk = false;
            var dummy_dll: CDllStorage = .none;
            try self.consumeLeadingOrTrailingAttributes(
                depth + 1,
                contract,
                &dummy_nr,
                &dummy_nn,
                &dummy_al,
                &dummy_pk,
                &dummy_dll,
            );
            if ((try self.peekKind()) == .ident and isCallingConvIdent(self.tokens[self.pos].lexeme)) {
                self.pos += 1;
                continue;
            }
            if ((try self.peekKind()) != .star) break;
            self.pos += 1;

            var is_p_const = false;
            var is_p_vol = false;
            var is_p_rest = false;
            var ptr_null: CNullability = .unspecified;

            while ((try self.peekKind()) == .ident or (try self.peekKind()) == .lbracket) {
                if ((try self.peekKind()) == .lbracket) {
                    if (self.pos + 1 < self.tokens.len and self.tokens[self.pos + 1].kind == .lbracket) {
                        var ptr_contract = CFfiContract{};
                        try self.consumeLeadingOrTrailingAttributes(
                            depth + 1,
                            &ptr_contract,
                            &dummy_nr,
                            &dummy_nn,
                            &dummy_al,
                            &dummy_pk,
                            &dummy_dll,
                        );
                        if (ptr_contract.slice_len_param.len > 0) {
                            contract.slice_len_param = ptr_contract.slice_len_param;
                        }
                        continue;
                    }
                    break;
                }
                const qlex = self.tokens[self.pos].lexeme;
                if (std.mem.eql(u8, qlex, "const") or std.mem.eql(u8, qlex, "__const") or
                    std.mem.eql(u8, qlex, "__const__"))
                {
                    is_p_const = true;
                    self.pos += 1;
                } else if (std.mem.eql(u8, qlex, "volatile") or std.mem.eql(u8, qlex, "__volatile") or
                    std.mem.eql(u8, qlex, "__volatile__"))
                {
                    is_p_vol = true;
                    self.pos += 1;
                } else if (std.mem.eql(u8, qlex, "restrict") or std.mem.eql(u8, qlex, "__restrict") or
                    std.mem.eql(u8, qlex, "__restrict__"))
                {
                    is_p_rest = true;
                    self.pos += 1;
                } else if (std.mem.eql(u8, qlex, "_Nonnull")) {
                    ptr_null = .non_null;
                    self.pos += 1;
                } else if (std.mem.eql(u8, qlex, "_Nullable")) {
                    ptr_null = .may_be_null;
                    self.pos += 1;
                } else if (std.mem.eql(u8, qlex, "_Null_unspecified") or isCallingConvIdent(qlex)) {
                    self.pos += 1;
                } else if (isAttributeKeyword(qlex)) {
                    var ptr_contract = CFfiContract{};
                    try self.consumeLeadingOrTrailingAttributes(
                        depth + 1,
                        &ptr_contract,
                        &dummy_nr,
                        &dummy_nn,
                        &dummy_al,
                        &dummy_pk,
                        &dummy_dll,
                    );
                    if (ptr_contract.slice_len_param.len > 0) {
                        contract.slice_len_param = ptr_contract.slice_len_param;
                    }
                } else {
                    break;
                }
            }

            try out_mods.append(self.unit.allocator, .{
                .pointer = .{
                    .is_ptr_const = is_p_const,
                    .is_ptr_volatile = is_p_vol,
                    .is_ptr_restrict = is_p_rest,
                    .nullability = ptr_null,
                },
            });
        }
    }

    /// Parses postfix `[len]` array and `(params…)` function suffixes.
    fn parseDeclaratorPostfixes(
        self: *CDeclParser,
        depth: u32,
        out_postfixes: *std.ArrayListUnmanaged(DeclaratorModifier),
    ) CFrontendError!void {
        while (true) {
            const pk = try self.peekKind();
            if (pk == .lbracket) {
                // Stop if C23 `[[…]]` attribute follows declarator:
                if (self.pos + 1 < self.tokens.len and self.tokens[self.pos + 1].kind == .lbracket) break;
                self.pos += 1;
                // Skip optional C99 `[static const 16]` array parameter qualifiers:
                while ((try self.peekKind()) == .ident) {
                    const qual_lex = self.tokens[self.pos].lexeme;
                    if (std.mem.eql(u8, qual_lex, "static") or std.mem.eql(u8, qual_lex, "const") or
                        std.mem.eql(u8, qual_lex, "restrict") or std.mem.eql(u8, qual_lex, "__restrict") or
                        std.mem.eql(u8, qual_lex, "volatile"))
                    {
                        self.pos += 1;
                    } else {
                        break;
                    }
                }
                var arr_len: ?u64 = null;
                if ((try self.peekKind()) == .star and
                    self.pos + 1 < self.tokens.len and
                    self.tokens[self.pos + 1].kind == .rbracket)
                {
                    self.pos += 1;
                } else if ((try self.peekKind()) != .rbracket) {
                    const len_val = try self.parseConstantIntExprUntilRbracket(depth + 1);
                    if (len_val < 0) return self.failHere("negative C array bound");
                    arr_len = @intCast(len_val);
                }
                if ((try self.peekKind()) != .rbracket) {
                    return self.failHere("expected `]` in C array declarator");
                }
                self.pos += 1;
                try out_postfixes.append(self.unit.allocator, .{ .array = arr_len });
            } else if (pk == .lparen) {
                self.pos += 1;
                const fn_params = try self.parseParameterTypeList(depth + 1);
                if ((try self.peekKind()) != .rparen) {
                    return self.failHere("expected `)` to close C function parameter list");
                }
                self.pos += 1;
                try out_postfixes.append(self.unit.allocator, .{ .function = fn_params });
            } else {
                break;
            }
        }
    }

    /// Parses a C function `(param0, param1, …)` list, applying `(void)` empty-param and array/fn decay.
    fn parseParameterTypeList(self: *CDeclParser, depth: u32) CFrontendError!FnSuffixMod {
        if ((try self.peekKind()) == .rparen) {
            return .{ .param_start = 0, .param_len = 0, .is_variadic = false };
        }
        var local_params: std.ArrayListUnmanaged(CFnParam) = .empty;
        defer local_params.deinit(self.unit.allocator);
        var is_variadic = false;

        while ((try self.peekKind()) != .rparen and (try self.peekKind()) != .eof) {
            if ((try self.peekKind()) == .ellipses) {
                is_variadic = true;
                self.pos += 1;
                break;
            }

            const p_specs = try self.parseDeclSpecs(depth + 1);
            const p_decl = try self.parseDeclarator(p_specs, depth + 1, false);
            var p_contract = p_decl.contract;
            var dummy_nr = false;
            var dummy_nn: u32 = 0;
            var dummy_al: u32 = 0;
            var dummy_pk = false;
            var dummy_dll: CDllStorage = .none;
            try self.consumeLeadingOrTrailingAttributes(
                depth + 1,
                &p_contract,
                &dummy_nr,
                &dummy_nn,
                &dummy_al,
                &dummy_pk,
                &dummy_dll,
            );

            // C11 `(void)` single unnamed `void` parameter means 0 parameters:
            if (local_params.items.len == 0 and p_decl.name.len == 0 and (try self.peekKind()) == .rparen) {
                const p_node = self.unit.getType(p_decl.type_id);
                if (p_node == .primitive and p_node.primitive == .c_void) {
                    return .{ .param_start = 0, .param_len = 0, .is_variadic = false };
                }
            }

            // C11 §6.7.6.3p7–8 parameter decay; `T[N]` -> `*T` / `*mut T` and `fn(…)` -> `*fn(…)`:
            var decayed_ty = p_decl.type_id;
            const raw_p_node = self.unit.getType(decayed_ty);
            if (raw_p_node == .array) {
                decayed_ty = try self.unit.appendType(.{
                    .pointer = .{
                        .pointee = raw_p_node.array.elem,
                        .is_const = p_specs.is_const and !self.isPointerChain(raw_p_node.array.elem),
                        .nullability = p_contract.nullability,
                    },
                });
            } else if (raw_p_node == .function) {
                decayed_ty = try self.unit.appendType(.{
                    .pointer = .{
                        .pointee = decayed_ty,
                        .is_const = true,
                        .nullability = p_contract.nullability,
                    },
                });
            }

            try local_params.append(self.unit.allocator, .{
                .name = p_decl.name,
                .type_id = decayed_ty,
                .contract = p_contract,
                .span = p_decl.span,
            });

            if ((try self.peekKind()) == .comma) {
                self.pos += 1;
                continue;
            }
            break;
        }

        const param_start: u32 = @intCast(self.unit.params.items.len);
        try self.unit.params.appendSlice(self.unit.allocator, local_params.items);
        return .{
            .param_start = param_start,
            .param_len = @intCast(local_params.items.len),
            .is_variadic = is_variadic,
        };
    }

    /// Returns `true` if `type_id` is already a `.pointer` node.
    fn isPointerChain(self: *const CDeclParser, type_id: CTypeId) bool {
        return self.unit.getType(type_id) == .pointer;
    }

    /// Applies `__attribute__((nonnull(…)))` bits onto `params[param_start .. param_start + param_len]`.
    fn applyNonnullParamMask(self: *CDeclParser, param_start: u32, param_len: u32, mask: u32) void {
        if (mask == 0 or param_len == 0) return;
        var i: u32 = 0;
        while (i < param_len) : (i += 1) {
            const has_bit = mask == std.math.maxInt(u32) or (i < 31 and ((mask >> @intCast(i)) & 1) != 0);
            if (has_bit) {
                const p_ptr = &self.unit.params.items[param_start + i];
                if (p_ptr.contract.nullability == .unspecified) {
                    p_ptr.contract.nullability = .non_null;
                }
            }
        }
    }

    /// Parses `struct`/`union`/`enum` layout attributes (`packed`, `aligned(N)`, `ms_struct`, `gcc_struct`).
    fn consumeRecordAttributes(
        self: *CDeclParser,
        depth: u32,
        layout: *CRecordLayoutAttrs,
    ) CFrontendError!void {
        var dummy_contract = CFfiContract{};
        var dummy_nr = false;
        var dummy_nn: u32 = 0;
        var dummy_dll: CDllStorage = .none;
        while (true) {
            const before = self.pos;
            const pk = try self.peekKind();
            if (pk == .ident and
                (std.mem.eql(u8, self.tokens[self.pos].lexeme, "__attribute__") or
                    std.mem.eql(u8, self.tokens[self.pos].lexeme, "__attribute")))
            {
                self.pos += 1;
                if ((try self.peekKind()) == .lparen) {
                    try self.parseGnuAttributeGroup(
                        depth + 1,
                        &dummy_contract,
                        &dummy_nr,
                        &dummy_nn,
                        &layout.explicit_align,
                        &layout.is_packed,
                        &layout.is_ms_struct,
                        &layout.is_gcc_struct,
                    );
                }
            } else if (pk == .lbracket and self.pos + 1 < self.tokens.len and
                self.tokens[self.pos + 1].kind == .lbracket)
            {
                try self.parseC23AttributeGroup(
                    depth + 1,
                    &dummy_contract,
                    &dummy_nr,
                    &layout.explicit_align,
                    &layout.is_packed,
                    &layout.is_ms_struct,
                    &layout.is_gcc_struct,
                );
            } else if (pk == .ident and
                (std.mem.eql(u8, self.tokens[self.pos].lexeme, "_Alignas") or
                    std.mem.eql(u8, self.tokens[self.pos].lexeme, "alignas") or
                    std.mem.eql(u8, self.tokens[self.pos].lexeme, "__declspec")))
            {
                try self.consumeLeadingOrTrailingAttributes(
                    depth + 1,
                    &dummy_contract,
                    &dummy_nr,
                    &dummy_nn,
                    &layout.explicit_align,
                    &layout.is_packed,
                    &dummy_dll,
                );
            } else {
                break;
            }
            if (self.pos == before) break;
        }
    }

    /// Consumes Clang/GNU `__attribute__`, C23 `[[…]]`, `_Alignas`, `__declspec`, and Microsoft SAL tokens.
    fn consumeLeadingOrTrailingAttributes(
        self: *CDeclParser,
        depth: u32,
        contract: *CFfiContract,
        is_noreturn: *bool,
        nonnull_mask: *u32,
        explicit_align: *u32,
        is_packed: *bool,
        dll_storage: *CDllStorage,
    ) CFrontendError!void {
        var dummy_ms = false;
        var dummy_gcc = false;
        while (true) {
            const pk = try self.peekKind();
            if (pk == .lbracket and self.pos + 1 < self.tokens.len and
                self.tokens[self.pos + 1].kind == .lbracket)
            {
                try self.parseC23AttributeGroup(
                    depth + 1,
                    contract,
                    is_noreturn,
                    explicit_align,
                    is_packed,
                    &dummy_ms,
                    &dummy_gcc,
                );
                continue;
            }
            if (pk != .ident) break;
            const lex = self.tokens[self.pos].lexeme;

            if (std.mem.eql(u8, lex, "__attribute__") or std.mem.eql(u8, lex, "__attribute")) {
                self.pos += 1;
                if ((try self.peekKind()) == .lparen) {
                    try self.parseGnuAttributeGroup(
                        depth + 1,
                        contract,
                        is_noreturn,
                        nonnull_mask,
                        explicit_align,
                        is_packed,
                        &dummy_ms,
                        &dummy_gcc,
                    );
                }
            } else if (std.mem.eql(u8, lex, "_Alignas") or std.mem.eql(u8, lex, "alignas")) {
                self.pos += 1;
                if ((try self.peekKind()) == .lparen) {
                    self.pos += 1;
                    if (self.pos < self.tokens.len and self.isTypeStartToken(self.tokens[self.pos])) {
                        const al_ty = try self.parseTypeName(depth + 1);
                        explicit_align.* = @max(explicit_align.*, self.estimateTypeAlignBytes(al_ty, depth + 1));
                    } else {
                        const al_val = try self.parseConstantIntExprUntilCommaOrRparen(depth + 1);
                        if (al_val > 0 and std.math.isPowerOfTwo(@as(u64, @intCast(al_val)))) {
                            explicit_align.* = @max(explicit_align.*, @as(u32, @intCast(al_val)));
                        }
                    }
                    if ((try self.peekKind()) == .rparen) self.pos += 1;
                }
            } else if (std.mem.eql(u8, lex, "__declspec")) {
                self.pos += 1;
                if ((try self.peekKind()) == .lparen) {
                    self.pos += 1;
                    while ((try self.peekKind()) != .rparen and (try self.peekKind()) != .eof) {
                        if (self.tokens[self.pos].kind == .ident) {
                            const ds_name = self.tokens[self.pos].lexeme;
                            self.pos += 1;
                            if (std.mem.eql(u8, ds_name, "dllexport")) {
                                dll_storage.* = .dllexport;
                            } else if (std.mem.eql(u8, ds_name, "dllimport")) {
                                dll_storage.* = .dllimport;
                            } else if (std.mem.eql(u8, ds_name, "noreturn")) {
                                is_noreturn.* = true;
                            } else if (std.mem.eql(u8, ds_name, "align") and (try self.peekKind()) == .lparen) {
                                self.pos += 1;
                                const al_v = try self.parseConstantIntExprUntilCommaOrRparen(depth + 1);
                                if (al_v > 0 and std.math.isPowerOfTwo(@as(u64, @intCast(al_v)))) {
                                    explicit_align.* = @max(explicit_align.*, @as(u32, @intCast(al_v)));
                                }
                                if ((try self.peekKind()) == .rparen) self.pos += 1;
                            } else if ((try self.peekKind()) == .lparen) {
                                try self.skipBalancedParens();
                            }
                        } else {
                            self.pos += 1;
                        }
                    }
                    if ((try self.peekKind()) == .rparen) self.pos += 1;
                }
            } else if (std.mem.eql(u8, lex, "_In_z_")) {
                // Microsoft SAL and Clang nullability annotations:
                contract.is_null_terminated = true;
                contract.nullability = .non_null;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_In_opt_z_")) {
                contract.is_null_terminated = true;
                contract.nullability = .may_be_null;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_Out_")) {
                contract.is_out_param = true;
                contract.nullability = .non_null;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_Out_opt_")) {
                contract.is_out_param = true;
                contract.nullability = .may_be_null;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_In_") or std.mem.eql(u8, lex, "_Inout_") or
                std.mem.eql(u8, lex, "_Ret_notnull_"))
            {
                contract.nullability = .non_null;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_In_opt_") or std.mem.eql(u8, lex, "_Inout_opt_") or
                std.mem.eql(u8, lex, "_Ret_maybenull_"))
            {
                contract.nullability = .may_be_null;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_In_reads_") or std.mem.eql(u8, lex, "_Out_writes_")) {
                if (std.mem.eql(u8, lex, "_Out_writes_")) contract.is_out_param = true;
                contract.nullability = .non_null;
                self.pos += 1;
                if ((try self.peekKind()) == .lparen) {
                    self.pos += 1;
                    if ((try self.peekKind()) == .ident or (try self.peekKind()) == .number) {
                        contract.slice_len_param = self.tokens[self.pos].lexeme;
                        self.pos += 1;
                    }
                    while ((try self.peekKind()) != .rparen and (try self.peekKind()) != .eof) : (self.pos += 1) {}
                    if ((try self.peekKind()) == .rparen) self.pos += 1;
                }
            } else if (std.mem.eql(u8, lex, "_Nonnull")) {
                contract.nullability = .non_null;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_Nullable")) {
                contract.nullability = .may_be_null;
                self.pos += 1;
            } else if (std.mem.eql(u8, lex, "_Null_unspecified")) {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    /// Parses `__attribute__((attr1, attr2(arg)))` groups.
    fn parseGnuAttributeGroup(
        self: *CDeclParser,
        depth: u32,
        contract: *CFfiContract,
        is_noreturn: *bool,
        nonnull_mask: *u32,
        explicit_align: *u32,
        is_packed: *bool,
        is_ms_struct: *bool,
        is_gcc_struct: *bool,
    ) CFrontendError!void {
        if ((try self.peekKind()) != .lparen) return;
        self.pos += 1;
        const has_double_paren = (try self.peekKind()) == .lparen;
        if (has_double_paren) self.pos += 1;

        while ((try self.peekKind()) != .rparen and (try self.peekKind()) != .eof) {
            if ((try self.peekKind()) == .comma) {
                self.pos += 1;
                continue;
            }
            if ((try self.peekKind()) != .ident) {
                if ((try self.peekKind()) == .lparen) {
                    try self.skipBalancedParens();
                } else {
                    self.pos += 1;
                }
                continue;
            }
            const attr_name = stripDoubleUnderscores(self.tokens[self.pos].lexeme);
            self.pos += 1;

            if (std.mem.eql(u8, attr_name, "packed")) {
                is_packed.* = true;
            } else if (std.mem.eql(u8, attr_name, "ms_struct")) {
                is_ms_struct.* = true;
            } else if (std.mem.eql(u8, attr_name, "gcc_struct")) {
                is_gcc_struct.* = true;
            } else if (std.mem.eql(u8, attr_name, "noreturn")) {
                is_noreturn.* = true;
            } else if (std.mem.eql(u8, attr_name, "aligned")) {
                if ((try self.peekKind()) == .lparen) {
                    self.pos += 1;
                    if ((try self.peekKind()) != .rparen) {
                        const al_val = try self.parseConstantIntExprUntilCommaOrRparen(depth + 1);
                        if (al_val > 0 and std.math.isPowerOfTwo(@as(u64, @intCast(al_val)))) {
                            explicit_align.* = @max(explicit_align.*, @as(u32, @intCast(al_val)));
                        }
                    } else {
                        explicit_align.* = @max(explicit_align.*, 16);
                    }
                    if ((try self.peekKind()) == .rparen) self.pos += 1;
                } else {
                    explicit_align.* = @max(explicit_align.*, 16);
                }
            } else if (std.mem.eql(u8, attr_name, "counted_by")) {
                if ((try self.peekKind()) == .lparen) {
                    self.pos += 1;
                    if ((try self.peekKind()) == .ident or (try self.peekKind()) == .number) {
                        contract.slice_len_param = self.tokens[self.pos].lexeme;
                        self.pos += 1;
                    }
                    while ((try self.peekKind()) != .rparen and (try self.peekKind()) != .eof) : (self.pos += 1) {}
                    if ((try self.peekKind()) == .rparen) self.pos += 1;
                }
            } else if (std.mem.eql(u8, attr_name, "malloc")) {
                contract.is_owned_by_caller = true;
                if ((try self.peekKind()) == .lparen) {
                    self.pos += 1;
                    if ((try self.peekKind()) == .ident) {
                        contract.free_with_fn = self.tokens[self.pos].lexeme;
                        self.pos += 1;
                    }
                    while ((try self.peekKind()) != .rparen and (try self.peekKind()) != .eof) : (self.pos += 1) {}
                    if ((try self.peekKind()) == .rparen) self.pos += 1;
                }
            } else if (std.mem.eql(u8, attr_name, "nonnull")) {
                if ((try self.peekKind()) == .lparen) {
                    self.pos += 1;
                    var has_any_idx = false;
                    while ((try self.peekKind()) != .rparen and (try self.peekKind()) != .eof) {
                        if ((try self.peekKind()) == .number) {
                            if (parseCIntegerLiteral(self.tokens[self.pos].lexeme)) |iv| {
                                if (iv.bits >= 1 and iv.bits <= 31) {
                                    nonnull_mask.* |= @as(u32, 1) << @intCast(iv.bits - 1);
                                    has_any_idx = true;
                                }
                            }
                        }
                        self.pos += 1;
                    }
                    if (!has_any_idx) nonnull_mask.* = std.math.maxInt(u32);
                    if ((try self.peekKind()) == .rparen) self.pos += 1;
                } else {
                    nonnull_mask.* = std.math.maxInt(u32);
                }
            } else if ((try self.peekKind()) == .lparen) {
                try self.skipBalancedParens();
            }
        }

        if ((try self.peekKind()) == .rparen) self.pos += 1;
        if (has_double_paren and (try self.peekKind()) == .rparen) self.pos += 1;
    }

    /// Parses C23 `[[gnu::packed]]`, `[[noreturn]]`, `[[clang::counted_by(len)]]` attribute groups.
    fn parseC23AttributeGroup(
        self: *CDeclParser,
        depth: u32,
        contract: *CFfiContract,
        is_noreturn: *bool,
        explicit_align: *u32,
        is_packed: *bool,
        is_ms_struct: *bool,
        is_gcc_struct: *bool,
    ) CFrontendError!void {
        _ = depth;
        self.pos += 2; // Consume `[[`.
        while (self.pos < self.tokens.len) {
            if (self.tokens[self.pos].kind == .rbracket and
                self.pos + 1 < self.tokens.len and
                self.tokens[self.pos + 1].kind == .rbracket)
            {
                self.pos += 2;
                break;
            }
            if (self.tokens[self.pos].kind == .ident) {
                var attr_ident = self.tokens[self.pos].lexeme;
                self.pos += 1;
                if (self.pos + 1 < self.tokens.len and self.tokens[self.pos].kind == .colon_colon and
                    self.tokens[self.pos + 1].kind == .ident)
                {
                    attr_ident = self.tokens[self.pos + 1].lexeme;
                    self.pos += 2;
                }
                const clean = stripDoubleUnderscores(attr_ident);
                if (std.mem.eql(u8, clean, "packed")) {
                    is_packed.* = true;
                } else if (std.mem.eql(u8, clean, "ms_struct")) {
                    is_ms_struct.* = true;
                } else if (std.mem.eql(u8, clean, "gcc_struct")) {
                    is_gcc_struct.* = true;
                } else if (std.mem.eql(u8, clean, "noreturn")) {
                    is_noreturn.* = true;
                } else if (std.mem.eql(u8, clean, "aligned") and
                    self.pos < self.tokens.len and
                    self.tokens[self.pos].kind == .lparen)
                {
                    self.pos += 1;
                    if (self.pos < self.tokens.len and self.tokens[self.pos].kind == .number) {
                        if (parseCIntegerLiteral(self.tokens[self.pos].lexeme)) |iv| {
                            if (iv.bits > 0 and std.math.isPowerOfTwo(iv.bits)) {
                                explicit_align.* = @max(explicit_align.*, @as(u32, @intCast(iv.bits)));
                            }
                        }
                        self.pos += 1;
                    }
                    if (self.pos < self.tokens.len and self.tokens[self.pos].kind == .rparen) self.pos += 1;
                } else if (std.mem.eql(u8, clean, "counted_by") and
                    self.pos < self.tokens.len and
                    self.tokens[self.pos].kind == .lparen)
                {
                    self.pos += 1;
                    if (self.pos < self.tokens.len and
                        (self.tokens[self.pos].kind == .ident or self.tokens[self.pos].kind == .number))
                    {
                        contract.slice_len_param = self.tokens[self.pos].lexeme;
                        self.pos += 1;
                    }
                    if (self.pos < self.tokens.len and self.tokens[self.pos].kind == .rparen) self.pos += 1;
                } else if (self.pos < self.tokens.len and self.tokens[self.pos].kind == .lparen) {
                    try self.skipBalancedParens();
                }
            } else {
                self.pos += 1;
            }
        }
    }

    /// Skips a balanced `( … )` group starting at `self.pos`.
    fn skipBalancedParens(self: *CDeclParser) CFrontendError!void {
        if ((try self.peekKind()) != .lparen) return;
        self.pos += 1;
        var depth: u32 = 1;
        while (self.pos < self.tokens.len and depth > 0) : (self.pos += 1) {
            const tok_kind = self.tokens[self.pos].kind;
            if (tok_kind == .lparen) {
                depth += 1;
                if (depth >= self.options.max_parse_depth) {
                    return self.failHere("C parenthesis nesting exceeded `MAX_C_PARSE_DEPTH`");
                }
            } else if (tok_kind == .rparen) {
                depth -= 1;
            }
        }
        if (depth != 0) return self.failHere("unclosed `(` in C attribute or expression");
    }

    /// Skips a balanced `{ … }` function body starting at `self.pos` (`DR-20` Seam #6).
    fn skipBalancedBraces(self: *CDeclParser) CFrontendError!void {
        if ((try self.peekKind()) != .lbrace) return;
        self.pos += 1;
        var depth: u32 = 1;
        while (self.pos < self.tokens.len and depth > 0) : (self.pos += 1) {
            const tok_kind = self.tokens[self.pos].kind;
            if (tok_kind == .lbrace) {
                depth += 1;
                if (depth >= self.options.max_parse_depth) {
                    return self.failHere("C brace nesting exceeded `MAX_C_PARSE_DEPTH`");
                }
            } else if (tok_kind == .rbrace) {
                depth -= 1;
            }
        }
        if (depth != 0) return self.failHere("unclosed `{` in C inline function body");
    }

    /// Parses a `static const` scalar/string initializer or skips complex aggregate initializers.
    fn parseInitializerOrConstVal(self: *CDeclParser, depth: u32) CFrontendError!?MacroConstValue {
        if (depth >= self.options.max_parse_depth) {
            return self.failHere("C initializer nesting exceeded `MAX_C_PARSE_DEPTH`");
        }
        if ((try self.peekKind()) == .lbrace) {
            try self.skipBalancedBraces();
            return null;
        }
        const start_idx = self.pos;
        var p_depth: u32 = 0;
        while (self.pos < self.tokens.len) {
            const tok_kind = self.tokens[self.pos].kind;
            if (p_depth == 0 and (tok_kind == .comma or tok_kind == .semi)) break;
            if (tok_kind == .lparen or tok_kind == .lbracket or tok_kind == .lbrace) {
                p_depth += 1;
                if (depth + p_depth >= self.options.max_parse_depth) {
                    return self.failHere("C initializer delimiter nesting exceeded `MAX_C_PARSE_DEPTH`");
                }
            } else if (tok_kind == .rparen or tok_kind == .rbracket or tok_kind == .rbrace) {
                if (p_depth == 0) break;
                p_depth -= 1;
            }
            self.pos += 1;
        }
        const expr_slice = self.tokens[start_idx..self.pos];
        if (expr_slice.len == 0) return null;
        if (expr_slice.len == 1 and expr_slice[0].kind == .string_lit) {
            return .{ .string_val = try decodeCStringLiteral(&self.unit.arena, expr_slice[0].lexeme) };
        } else if (expr_slice.len == 1 and expr_slice[0].kind == .number) {
            if (parseCFloatLiteral(expr_slice[0].lexeme)) |fv| return .{ .float_val = fv };
        } else if (expr_slice.len == 2 and
            (expr_slice[0].kind == .minus or expr_slice[0].kind == .plus) and
            expr_slice[1].kind == .number)
        {
            if (parseCFloatLiteral(expr_slice[1].lexeme)) |fv| {
                return .{ .float_val = if (expr_slice[0].kind == .minus) -fv else fv };
            }
        }
        var dummy_sink = DiagnosticSink.init(self.unit.allocator);
        defer dummy_sink.deinit();
        var eval = ConstExprEvaluator{
            .unit = self.unit,
            .sink = &dummy_sink,
            .tokens = expr_slice,
            .known_consts = &self.known_int_consts,
            .parser_ctx = self,
            .max_depth = self.options.max_parse_depth,
            .is_silent = true,
        };
        const res = eval.parseTernary(depth + 1, true) catch return null;
        if (eval.pos != expr_slice.len) return null;
        return if (res.is_unsigned or res.bits > @as(u64, std.math.maxInt(i64)))
            .{ .unsigned_int = res.bits }
        else
            .{ .signed_int = res.asSigned() };
    }

    /// Evaluates an integer constant expression stopping at top-level `,` or `)`.
    fn parseConstantIntExprUntilCommaOrRparen(self: *CDeclParser, depth: u32) CFrontendError!i128 {
        return self.parseConstantIntExprUntilSet(depth, comptime cTokenMask(&.{ .comma, .rparen }));
    }

    /// Evaluates an integer constant expression stopping at top-level `,` or `;`.
    fn parseConstantIntExprUntilCommaOrSemi(self: *CDeclParser, depth: u32) CFrontendError!i128 {
        return self.parseConstantIntExprUntilSet(depth, comptime cTokenMask(&.{ .comma, .semi }));
    }

    /// Evaluates an integer constant expression stopping at top-level `,` or `}`.
    fn parseConstantIntExprUntilCommaOrRbrace(self: *CDeclParser, depth: u32) CFrontendError!i128 {
        return self.parseConstantIntExprUntilSet(depth, comptime cTokenMask(&.{ .comma, .rbrace }));
    }

    /// Evaluates an integer constant expression stopping at top-level `]`.
    fn parseConstantIntExprUntilRbracket(self: *CDeclParser, depth: u32) CFrontendError!i128 {
        return self.parseConstantIntExprUntilSet(depth, comptime cTokenMask(&.{.rbracket}));
    }

    /// Slices tokens up to any top-level delimiter in `stop_mask` and evaluates to `i128`.
    fn parseConstantIntExprUntilSet(
        self: *CDeclParser,
        depth: u32,
        stop_mask: CTokenMask64,
    ) CFrontendError!i128 {
        try self.flushPragmaPack();
        const start_idx = self.pos;
        var nested: u32 = 0;
        while (self.pos < self.tokens.len) {
            const tok_kind = self.tokens[self.pos].kind;
            if (nested == 0 and isCTokenInMask(tok_kind, stop_mask)) break;
            if (tok_kind == .lparen or tok_kind == .lbracket or tok_kind == .lbrace) {
                nested += 1;
            } else if (tok_kind == .rparen or tok_kind == .rbracket or tok_kind == .rbrace) {
                if (nested == 0) break;
                nested -= 1;
            }
            self.pos += 1;
        }
        const slice = self.tokens[start_idx..self.pos];
        if (slice.len == 0) return self.failHere("expected integer constant expression in C declaration");
        var eval = ConstExprEvaluator{
            .unit = self.unit,
            .sink = self.sink,
            .tokens = slice,
            .known_consts = &self.known_int_consts,
            .parser_ctx = self,
            .max_depth = self.options.max_parse_depth,
        };
        const res = try eval.parseTernary(depth + 1, true);
        if (eval.pos != eval.tokens.len) {
            return eval.fail("unexpected trailing token in C integer constant expression");
        }
        return res.asI128();
    }

    /// Returns `true` if `type_id` embeds an incomplete or self-referential `struct`/`union` or `void` by value.
    fn hasIncompleteRecordOrVoidByValue(
        self: *const CDeclParser,
        type_id: CTypeId,
        depth: u32,
    ) bool {
        if (depth > MAX_C_PARSE_DEPTH or type_id.isNone()) return true;
        const canon_id = self.unit.unwrapTypedefs(type_id);
        return switch (self.unit.getType(canon_id)) {
            .pointer, .function, .enum_ref => false,
            .primitive => |prim| prim == .c_void,
            .record_ref => |rec_id| !self.unit.getDecl(rec_id).kind.record_decl.is_complete,
            .array => |arr| self.hasIncompleteRecordOrVoidByValue(arr.elem, depth + 1),
            .atomic_val => |inner| self.hasIncompleteRecordOrVoidByValue(inner, depth + 1),
            .typedef_ref => true,
        };
    }

    /// Returns `true` when `type_id` unwraps to an integer, `_Bool`, or `enum` valid for a C bitfield.
    fn isValidBitfieldBaseType(self: *const CDeclParser, type_id: CTypeId) bool {
        const canon_id = self.unit.unwrapTypedefs(type_id);
        return switch (self.unit.getType(canon_id)) {
            .primitive => |prim| prim.isInteger(),
            .enum_ref => true,
            else => false,
        };
    }

    /// Returns `true` if `type_id` embeds a function signature passing/returning non-8-byte `long double` by value.
    fn hasUnsupportedFnLongDouble(self: *const CDeclParser, type_id: CTypeId, depth: u32) bool {
        if (CPrimitiveKind.c_longdouble.byteSize(self.unit.target) == 8) return false;
        if (depth > MAX_C_PARSE_DEPTH or type_id.isNone()) return false;
        const canon_id = self.unit.unwrapTypedefs(type_id);
        return switch (self.unit.getType(canon_id)) {
            .function => |fn_ty| self.hasUnsupportedByValueLongDoubleSig(
                fn_ty.return_type,
                fn_ty.param_start,
                fn_ty.param_len,
            ),
            .pointer => |ptr| self.hasUnsupportedFnLongDouble(ptr.pointee, depth + 1),
            .array => |arr| self.hasUnsupportedFnLongDouble(arr.elem, depth + 1),
            .atomic_val => |inner| self.hasUnsupportedFnLongDouble(inner, depth + 1),
            else => false,
        };
    }

    /// Returns `true` if a C function signature passes or returns a non-8-byte `long double` (`f80`/`fp128`) by value.
    fn hasUnsupportedByValueLongDoubleSig(
        self: *const CDeclParser,
        return_type: CTypeId,
        param_start: u32,
        param_len: u32,
    ) bool {
        if (CPrimitiveKind.c_longdouble.byteSize(self.unit.target) == 8) return false;
        if (self.unit.hasByValueLongDouble(return_type, 0) or
            self.hasUnsupportedFnLongDouble(return_type, 0))
        {
            return true;
        }
        for (self.unit.getParams(param_start, param_len)) |param| {
            if (self.unit.hasByValueLongDouble(param.type_id, 0) or
                self.hasUnsupportedFnLongDouble(param.type_id, 0))
            {
                return true;
            }
        }
        return false;
    }

    /// Computes target `sizeof(T)` for `sizeof(…)` inside C `_Static_assert` / array bounds (`depth`-capped).
    fn estimateTypeSizeBytes(self: *const CDeclParser, type_id: CTypeId, depth: u32) u64 {
        return self.unit.computeTypeByteSize(type_id, depth);
    }

    /// Computes target `alignof(T)` for `_Alignas(Type)` (`depth`-capped).
    fn estimateTypeAlignBytes(self: *const CDeclParser, type_id: CTypeId, depth: u32) u32 {
        return self.unit.computeTypeNaturalAlign(type_id, depth);
    }

    /// Computes canonical target C ABI `(size_bytes, align_bytes)` for `rec_id` (`depth`-capped).
    fn estimateStructOrUnionLayout(self: *const CDeclParser, rec_id: CDeclId, depth: u32) CRecordByteLayout {
        return self.unit.computeRecordByteLayout(rec_id, depth);
    }
};

/// Strips matching leading and trailing `__` from GNU attribute identifiers (`__packed__` -> `packed`).
fn stripDoubleUnderscores(raw_ident: []const u8) []const u8 {
    if (raw_ident.len > 4 and
        std.mem.startsWith(u8, raw_ident, "__") and
        std.mem.endsWith(u8, raw_ident, "__"))
    {
        return raw_ident[2 .. raw_ident.len - 2];
    }
    return raw_ident;
}

/// Returns `true` in $O(1)$ if `lexeme` is a Clang nullability or Microsoft SAL annotation keyword.
inline fn isSalOrNullabilityIdent(lexeme: []const u8) bool {
    return SAL_OR_NULLABILITY_IDENT_SET.has(lexeme);
}

/// Returns `true` in $O(1)$ if `lexeme` introduces a C attribute (`__attribute__`, `_Alignas`, `__declspec`).
inline fn isAttributeKeyword(lexeme: []const u8) bool {
    return C_ATTRIBUTE_KEYWORD_SET.has(lexeme);
}

/// Returns `true` in $O(1)$ if `lexeme` is a Windows/x86 C calling-convention modifier.
inline fn isCallingConvIdent(lexeme: []const u8) bool {
    return C_CALLING_CONV_IDENT_SET.has(lexeme);
}

/// Test counter incremented by `testBodyHookCallback` to verify `DR-20` Seam #6 invocation.
var test_body_hook_invocations: u32 = 0;

/// Strongly typed `CFunctionBodyHook` test callback recording inline C function body spans.
fn testBodyHookCallback(
    unit: *const CTranslationUnit,
    decl_id: CDeclId,
    body_first_token: CTokenId,
    body_end_token: CTokenId,
    sink: *DiagnosticSink,
) CFrontendError!void {
    _ = sink;
    const decl = unit.getDecl(decl_id);
    if (decl.kind == .fn_decl and !body_first_token.isNone() and !body_end_token.isNone()) {
        if (body_first_token.asInt() < body_end_token.asInt()) {
            test_body_hook_invocations += 1;
        }
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Preprocesses and parses a C11/C23 header buffer into an arena-backed `CTranslationUnit`.
///
/// Parameters:
/// - `allocator`   Backing allocator for dynamic SoA tables and arena slabs.
/// - `source`      UTF-8 C11/C23 header source bytes.
/// - `header_path` Logical or physical path of `source` (used for relative `#include "…"`).
/// - `file_id`     `VfsSourceMap` `FileId` attached to emitted `E0009` spans (`FileId.none` in memory).
/// - `options`     Target specification, `-D` defines, `-I` paths, virtual headers, and resource caps.
/// - `sink`        Destination `DiagnosticSink` receiving `E0009` diagnostics on failure.
pub fn parseCHeader(
    allocator: std.mem.Allocator,
    source: []const u8,
    header_path: []const u8,
    file_id: FileId,
    options: CFrontendOptions,
    sink: *DiagnosticSink,
) CFrontendError!CTranslationUnit {
    var unit = CTranslationUnit.init(allocator, options.target);
    errdefer unit.deinit();

    // [1] Run C11/C23 preprocessor (target defines, `#include`, `#if`, `#`, `##`, `__VA_OPT__`):
    var pp = CPreprocessor{
        .unit = &unit,
        .sink = sink,
        .options = options,
    };
    defer pp.deinit();

    try pp.populatePredefinedMacros();
    const norm_root_path = try normalizeIncludePath(&unit.arena, header_path);
    try pp.preprocessBuffer(source, norm_root_path, file_id, false, 0, &unit.tokens);
    try pp.collectSurvivingMacroConsts();

    try unit.tokens.append(allocator, .{
        .kind = .eof,
        .lexeme = "",
        .span = Span.init(file_id, @intCast(source.len), @intCast(source.len)),
    });

    // [2] Run C11/C23 declaration, type-specifier, attribute, and `_Static_assert` parser:
    var parser = CDeclParser{
        .unit = &unit,
        .sink = sink,
        .options = options,
        .tokens = unit.tokens.items,
    };
    defer parser.deinit();

    try parser.parseTranslationUnit();
    return unit;
}

// ---------------------------------------- MAIN -----------------------------------------

test "c_frontend: C11/C23 preprocessor #if, #elifdef, ## paste, # stringify, __VA_OPT__, and Blue-Paint" {
    const allocator = std.testing.allocator;
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    const c_src =
        \\#include <stdint.h>
        \\#include <stdbool.h>
        \\#include <stddef.h>
        \\#include <stdarg.h>
        \\
        \\#define MAKE_IDENT(prefix, name) prefix ## _ ## name
        \\#define STR_VAL(x) #x
        \\#define BLUE_SELF (BLUE_SELF + 1)
        \\#define LOG_DECL(ret, name, ...) ret name(int level __VA_OPT__(, __VA_ARGS__))
        \\
        \\#if defined(__x86_64__) && __has_include(<stdint.h>) && (1 << 4) == 16
        \\#define TARGET_BITS 64
        \\#elifdef __wasm32__
        \\#define TARGET_BITS 32
        \\#else
        \\#define TARGET_BITS 0
        \\#endif
        \\
        \\#define API_NAME STR_VAL(corex_v1)
        \\
        \\typedef uint32_t MAKE_IDENT(cx, flags_t);
        \\LOG_DECL(int, log_plain);
        \\LOG_DECL(int, log_fmt, const char *fmt, va_list ap);
        \\int check_blue(int arr[sizeof(int)]);
    ;

    var unit = try parseCHeader(
        allocator,
        c_src,
        "test_pp.h",
        .none,
        .{ .target = TargetSpec.X86_64_LINUX_GNU },
        &sink,
    );
    defer unit.deinit();

    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try std.testing.expect(!unit.has_errors);

    // Verify `TARGET_BITS == 64` and `API_NAME == "corex_v1"` were promoted:
    var has_bits = false;
    var has_api_name = false;
    for (unit.macro_consts.items) |mc| {
        if (std.mem.eql(u8, mc.name, "TARGET_BITS")) {
            has_bits = true;
            try std.testing.expectEqual(@as(i64, 64), mc.value.signed_int);
        } else if (std.mem.eql(u8, mc.name, "API_NAME")) {
            has_api_name = true;
            try std.testing.expectEqualStrings("corex_v1", mc.value.string_val);
        }
    }
    try std.testing.expect(has_bits);
    try std.testing.expect(has_api_name);

    // Verify pasted `cx_flags_t` typedef and `__VA_OPT__` function prototypes:
    var has_typedef = false;
    var has_log_plain = false;
    var has_log_fmt = false;
    for (unit.decls.items) |decl| {
        if (decl.is_from_system_header) continue;
        switch (decl.kind) {
            .typedef_decl => |td| {
                if (std.mem.eql(u8, td.name, "cx_flags_t")) has_typedef = true;
            },
            .fn_decl => |fd| {
                if (std.mem.eql(u8, fd.name, "log_plain")) {
                    has_log_plain = true;
                    try std.testing.expectEqual(@as(u32, 1), fd.param_len);
                } else if (std.mem.eql(u8, fd.name, "log_fmt")) {
                    has_log_fmt = true;
                    try std.testing.expectEqual(@as(u32, 3), fd.param_len);
                }
            },
            else => {},
        }
    }
    try std.testing.expect(has_typedef);
    try std.testing.expect(has_log_plain);
    try std.testing.expect(has_log_fmt);
}

test "c_frontend: structs, unions, C23 enums, function pointers, SAL contracts, and Seam #6 body hook" {
    const allocator = std.testing.allocator;
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    test_body_hook_invocations = 0;

    const c_src =
        \\#include <stdint.h>
        \\#include <stddef.h>
        \\
        \\struct OpaqueDb;
        \\typedef struct OpaqueDb OpaqueDb;
        \\
        \\enum WireOp : uint8_t {
        \\    WIRE_PING = 1,
        \\    WIRE_PONG = 2,
        \\};
        \\
        \\typedef int (*ExecCallback)(void *ctx, int cols);
        \\
        \\__attribute__((malloc(free)))
        \\void *alloc_packet(size_t byte_len);
        \\
        \\int read_records(
        \\    _In_z_ const char *path,
        \\    _Out_writes_(cap) uint8_t *buf,
        \\    size_t cap,
        \\    _Out_ size_t *out_read,
        \\    ExecCallback _Nullable on_row
        \\);
        \\
        \\static inline int fast_clamp(int val, int hi) {
        \\    if (val > hi) { return hi; }
        \\    return val;
        \\}
        \\
        \\_Static_assert(sizeof(int) == 4, "int must be 32-bit");
    ;

    var unit = try parseCHeader(
        allocator,
        c_src,
        "contracts.h",
        .none,
        .{
            .target = TargetSpec.AARCH64_APPLE_DARWIN,
            .body_hook = testBodyHookCallback,
        },
        &sink,
    );
    defer unit.deinit();

    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try std.testing.expectEqual(@as(u32, 1), test_body_hook_invocations);

    var has_verified_alloc = false;
    var has_verified_read = false;
    var has_verified_inline = false;
    for (unit.decls.items) |decl| {
        if (decl.is_from_system_header) continue;
        if (decl.kind == .fn_decl) {
            const fd = decl.kind.fn_decl;
            if (std.mem.eql(u8, fd.name, "alloc_packet")) {
                has_verified_alloc = true;
                try std.testing.expect(fd.ret_contract.is_owned_by_caller);
                try std.testing.expectEqualStrings("free", fd.ret_contract.free_with_fn);
            } else if (std.mem.eql(u8, fd.name, "read_records")) {
                has_verified_read = true;
                const params = unit.getParams(fd.param_start, fd.param_len);
                try std.testing.expectEqual(@as(usize, 5), params.len);
                try std.testing.expect(params[0].contract.is_null_terminated);
                try std.testing.expect(params[1].contract.is_out_param);
                try std.testing.expectEqualStrings("cap", params[1].contract.slice_len_param);
                try std.testing.expect(params[3].contract.is_out_param);
                try std.testing.expectEqual(CNullability.may_be_null, params[4].contract.nullability);
            } else if (std.mem.eql(u8, fd.name, "fast_clamp")) {
                has_verified_inline = true;
                try std.testing.expect(fd.is_static and fd.is_inline and fd.has_body);
            }
        }
    }
    try std.testing.expect(has_verified_alloc);
    try std.testing.expect(has_verified_read);
    try std.testing.expect(has_verified_inline);
}

test "c_frontend: resource caps, #error, and failing _Static_assert emit E0009 cleanly" {
    const allocator = std.testing.allocator;

    // [1] `#error` directive emits `E0009`:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const res = parseCHeader(
            allocator,
            "#error unsupported target configuration\n",
            "bad.h",
            .none,
            .{},
            &sink,
        );
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expectEqual(@as(u32, 1), sink.error_count);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }

    // [2] False `_Static_assert` emits `E0009`:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const res = parseCHeader(
            allocator,
            "_Static_assert(sizeof(long) == 16, \"impossible long\");\n",
            "assert_fail.h",
            .none,
            .{ .target = TargetSpec.X86_64_WINDOWS_MSVC },
            &sink,
        );
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }

    // [3] Exceeding `max_tokens` cap emits `E0009` without unbounded growth:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const res = parseCHeader(
            allocator,
            "int a; int b; int c; int d; int e;\n",
            "cap.h",
            .none,
            .{ .max_tokens = 4 },
            &sink,
        );
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }

    // [4] Self-including header cycle hits `max_include_depth` and emits `E0009`:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const vheaders = [_]VirtualHeaderEntry{
            .{ .path = "cycle.h", .content = "#include \"cycle.h\"\n" },
        };
        const res = parseCHeader(
            allocator,
            "#include \"cycle.h\"\n",
            "root.h",
            .none,
            .{ .virtual_headers = &vheaders, .max_include_depth = 4 },
            &sink,
        );
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }

    // [5] Exceeding `max_macro_steps` emits `E0009`:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const macro_src =
            \\#define STEP1(val) ((val) + 1)
            \\#define STEP2(val) (STEP1(val) + STEP1(val))
            \\#define STEP3(val) (STEP2(val) + STEP2(val))
            \\int run_macro(int arr[STEP3(1)]);
        ;
        const res = parseCHeader(
            allocator,
            macro_src,
            "macro_cap.h",
            .none,
            .{ .max_macro_steps = 2 },
            &sink,
        );
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }

    // [6] Exceeding `max_parse_depth` emits `E0009`:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const deep_src = "int x = ((((((((((1))))))))));\n";
        const res = parseCHeader(
            allocator,
            deep_src,
            "depth_cap.h",
            .none,
            .{ .max_parse_depth = 4 },
            &sink,
        );
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }
}

test "c_frontend: target-calibrated predefined macros across AArch64, Windows MSVC, and Wasm32 WASI" {
    const allocator = std.testing.allocator;
    const probe_src =
        \\#include <limits.h>
        \\#include <float.h>
        \\#include <inttypes.h>
        \\#include <sys/types.h>
        \\#include "once_hdr.h"
        \\#include "once_hdr.h"
        \\
        \\#ifdef __CHAR_UNSIGNED__
        \\#define IS_CHAR_U 1
        \\#else
        \\#define IS_CHAR_U 0
        \\#endif
        \\
        \\_Static_assert(USER_CUSTOM_DEF == 77, "user -D define");
    ;
    const vheaders = [_]VirtualHeaderEntry{
        .{
            .path = "once_hdr.h",
            .content = "#pragma once\ntypedef int OnceCounter;\n",
        },
    };
    const user_defs = [_]MacroDefine{
        .{ .name = "USER_CUSTOM_DEF", .value = "77" },
    };

    // [1] `aarch64-linux-gnu`; unsigned `char`, `sizeof(long) == 8`:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var unit = try parseCHeader(
            allocator,
            probe_src,
            "probe.h",
            .none,
            .{
                .target = TargetSpec.AARCH64_LINUX_GNU,
                .defines = &user_defs,
                .virtual_headers = &vheaders,
            },
            &sink,
        );
        defer unit.deinit();
        try std.testing.expectEqual(@as(u32, 0), sink.error_count);

        var once_count: u32 = 0;
        for (unit.decls.items) |decl| {
            if (decl.kind == .typedef_decl and std.mem.eql(u8, decl.kind.typedef_decl.name, "OnceCounter")) {
                once_count += 1;
            }
        }
        try std.testing.expectEqual(@as(u32, 1), once_count);

        var has_unsigned_char = false;
        for (unit.macro_consts.items) |mc| {
            if (std.mem.eql(u8, mc.name, "IS_CHAR_U")) {
                has_unsigned_char = mc.value.signed_int == 1;
            }
        }
        try std.testing.expect(has_unsigned_char);
    }

    // [2] `wasm32-unknown-wasi`; 32-bit pointers & `long`:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const wasm_src =
            \\_Static_assert(__SIZEOF_POINTER__ == 4, "wasm32 ptr");
            \\_Static_assert(__SIZEOF_LONG__ == 4, "wasm32 long");
            \\_Static_assert(defined_check == 1, "wasi");
        ;
        const wasm_defs = [_]MacroDefine{
            .{ .name = "defined_check", .value = "__wasi__" },
        };
        var unit = try parseCHeader(
            allocator,
            wasm_src,
            "wasm_probe.h",
            .none,
            .{ .target = TargetSpec.WASM32_UNKNOWN_WASI, .defines = &wasm_defs },
            &sink,
        );
        defer unit.deinit();
        try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    }
}

test "c_frontend: [CRITICAL-06] billion-laughs X10^8 macro bomb and deep macro chain emit E0009 in bounded memory" {
    const allocator = std.testing.allocator;

    // [1] Exponential `X10^8(1)` (`10^8` tokens) aborts via `expanded_token_budget` inside `< 10 MiB`:
    {
        const backing_buf = try allocator.alloc(u8, 10 * 1024 * 1024);
        defer allocator.free(backing_buf);
        var fixed_alloc = std.heap.FixedBufferAllocator.init(backing_buf);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();

        const bomb_src =
            \\#define X10(a) a a a a a a a a a a
            \\int explode = X10(X10(X10(X10(X10(X10(X10(X10(1))))))));
        ;
        const res = parseCHeader(
            fixed_alloc.allocator(),
            bomb_src,
            "bomb.h",
            .none,
            .{},
            &sink,
        );
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expect(fixed_alloc.end_index < 10 * 1024 * 1024);
        try std.testing.expect(sink.error_count >= 1);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }

    // [2] Deep 400-level `#define M_0 M_1` … `#define M_400 1` chain hits `macro_recursion_depth` cap (`E0009`):
    {
        var chain_src: std.ArrayListUnmanaged(u8) = .empty;
        defer chain_src.deinit(allocator);
        var idx: u32 = 0;
        while (idx < 400) : (idx += 1) {
            const line = try std.fmt.allocPrint(allocator, "#define M_{d} M_{d}\n", .{ idx, idx + 1 });
            defer allocator.free(line);
            try chain_src.appendSlice(allocator, line);
        }
        try chain_src.appendSlice(allocator, "#define M_400 1\nint chain_val = M_0;\n");

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const res = parseCHeader(allocator, chain_src.items, "deep_chain.h", .none, .{}, &sink);
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expect(sink.error_count >= 1);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }
}

test "c_frontend: [CRITICAL-07] self-referential and incomplete struct/union value fields emit E0009" {
    const allocator = std.testing.allocator;

    // [1] Direct self-referential `struct Loop { struct Loop a; };` emits `E0009` without crashing:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const res = parseCHeader(
            allocator,
            "struct Loop { struct Loop a; };\n",
            "loop.h",
            .none,
            .{},
            &sink,
        );
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }

    // [2] Forward incomplete `struct Fwd; struct Bad { struct Fwd field_val; };` emits `E0009`:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const res = parseCHeader(
            allocator,
            "struct Fwd; struct Bad { struct Fwd field_val; };\n",
            "incomplete_field.h",
            .none,
            .{},
            &sink,
        );
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }

    // [3] Pointer to self (`struct Node { struct Node *next; };`) remains valid:
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var unit = try parseCHeader(
            allocator,
            "struct Node { struct Node *next; int payload; };\n",
            "list_node.h",
            .none,
            .{},
            &sink,
        );
        defer unit.deinit();
        try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    }
}

test "c_frontend: [MAJOR-02/03] MSVC WinHdr bitfield sizeof, packed SysV :0 sizeof, and AAPCS64 :0 promotion" {
    const allocator = std.testing.allocator;

    const win_hdr_src =
        \\#include <stdint.h>
        \\struct WinHdr {
        \\    uint16_t ver : 4;
        \\    uint16_t flags : 12;
        \\    uint32_t seq : 16;
        \\};
        \\_Static_assert(sizeof(struct WinHdr) == EXPECTED_WIN_HDR_SZ, "WinHdr layout");
    ;

    // [1] `x86_64-windows-msvc`; `uint16_t` and `uint32_t` bitfield units do not merge (`sizeof == 8`):
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const defs = [_]MacroDefine{.{ .name = "EXPECTED_WIN_HDR_SZ", .value = "8" }};
        var unit = try parseCHeader(
            allocator,
            win_hdr_src,
            "win_hdr.h",
            .none,
            .{ .target = TargetSpec.X86_64_WINDOWS_MSVC, .defines = &defs },
            &sink,
        );
        defer unit.deinit();
        try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    }

    // [2] `x86_64-linux-gnu`; `__attribute__((packed))` with `int : 0` advances to byte 4 (`sizeof == 5`):
    const packed_zero_src =
        \\struct __attribute__((packed)) S {
        \\    char a : 3;
        \\    int : 0;
        \\    char b : 2;
        \\};
        \\_Static_assert(sizeof(struct S) == EXPECTED_PACKED_SZ, "packed :0 layout");
    ;
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const defs = [_]MacroDefine{.{ .name = "EXPECTED_PACKED_SZ", .value = "5" }};
        var unit = try parseCHeader(
            allocator,
            packed_zero_src,
            "packed_sysv.h",
            .none,
            .{ .target = TargetSpec.X86_64_LINUX_GNU, .defines = &defs },
            &sink,
        );
        defer unit.deinit();
        try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    }

    // [3] `aarch64-linux-gnu` AAPCS64; `int : 0` also promotes container alignment to `4B` (`sizeof == 8`):
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const defs = [_]MacroDefine{.{ .name = "EXPECTED_PACKED_SZ", .value = "8" }};
        var unit = try parseCHeader(
            allocator,
            packed_zero_src,
            "packed_aapcs64.h",
            .none,
            .{ .target = TargetSpec.AARCH64_LINUX_GNU, .defines = &defs },
            &sink,
        );
        defer unit.deinit();
        try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    }
}

test "c_frontend: [MAJOR-04/06] char sign-extension, UTF char literals, #if comma op, trailing garbage, and f80/fp128" {
    const allocator = std.testing.allocator;

    const pp_expr_src =
        \\#if '\xff' < 0
        \\#define CHAR_FF_NEG 1
        \\#else
        \\#define CHAR_FF_NEG 0
        \\#endif
        \\#if (0, 1) && (u'λ' == 0x03BB) && (U'λ' == 0x03BB) && (L'λ' == 0x03BB)
        \\#define COMMA_AND_UTF_OK 1
        \\#else
        \\#define COMMA_AND_UTF_OK 0
        \\#endif
        \\_Static_assert(COMMA_AND_UTF_OK == 1, "comma + UTF char literal");
    ;

    // [1] Signed `char` on `x86_64-linux-gnu` (`'\xff' == -1 < 0`) vs unsigned `char` on `aarch64-linux-gnu` (`+255`):
    {
        var sysv_sink = DiagnosticSink.init(allocator);
        defer sysv_sink.deinit();
        var sysv_unit = try parseCHeader(
            allocator,
            pp_expr_src,
            "char_sysv.h",
            .none,
            .{ .target = TargetSpec.X86_64_LINUX_GNU },
            &sysv_sink,
        );
        defer sysv_unit.deinit();
        try std.testing.expectEqual(@as(u32, 0), sysv_sink.error_count);

        var is_sysv_neg = false;
        for (sysv_unit.macro_consts.items) |mc| {
            if (std.mem.eql(u8, mc.name, "CHAR_FF_NEG")) is_sysv_neg = (mc.value.signed_int == 1);
        }
        try std.testing.expect(is_sysv_neg);

        var arm_sink = DiagnosticSink.init(allocator);
        defer arm_sink.deinit();
        var arm_unit = try parseCHeader(
            allocator,
            pp_expr_src,
            "char_arm.h",
            .none,
            .{ .target = TargetSpec.AARCH64_LINUX_GNU },
            &arm_sink,
        );
        defer arm_unit.deinit();
        try std.testing.expectEqual(@as(u32, 0), arm_sink.error_count);

        var is_arm_neg = true;
        for (arm_unit.macro_consts.items) |mc| {
            if (std.mem.eql(u8, mc.name, "CHAR_FF_NEG")) is_arm_neg = (mc.value.signed_int == 1);
        }
        try std.testing.expect(!is_arm_neg);
    }

    // [2] Trailing garbage in `#if 1 2`, `#if 1 )`, and `int arr[1 2];` emits `E0009`:
    for ([_][]const u8{
        "#if 1 2\n#endif\n",
        "#if 1 )\n#endif\n",
        "int arr[1 2];\n",
    }) |bad_expr_src| {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const res = parseCHeader(allocator, bad_expr_src, "trailing_garbage.h", .none, .{}, &sink);
        try std.testing.expectError(error.TranslationFailed, res);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sink.diagnostics.items[0].code,
        );
    }

    // [3] Non-8B `long double` by-value prototype rejected on SysV (`E0009`) and accepted on MSVC (`8B` `f64`):
    {
        var sysv_sink = DiagnosticSink.init(allocator);
        defer sysv_sink.deinit();
        const sysv_res = parseCHeader(
            allocator,
            "long double sinl(long double val);\n",
            "ld_sysv.h",
            .none,
            .{ .target = TargetSpec.X86_64_LINUX_GNU },
            &sysv_sink,
        );
        try std.testing.expectError(error.TranslationFailed, sysv_res);
        try std.testing.expectEqual(
            DiagnosticCode.e0009_c_header_translation_failed,
            sysv_sink.diagnostics.items[0].code,
        );

        var msvc_sink = DiagnosticSink.init(allocator);
        defer msvc_sink.deinit();
        var msvc_unit = try parseCHeader(
            allocator,
            "long double sinl(long double val);\nint read_ld(long double *out_ptr);\n",
            "ld_msvc.h",
            .none,
            .{ .target = TargetSpec.X86_64_WINDOWS_MSVC },
            &msvc_sink,
        );
        defer msvc_unit.deinit();
        try std.testing.expectEqual(@as(u32, 0), msvc_sink.error_count);
    }
}

//! Canonical CoreX v1.0 `.cx` C11/C23 Header Emitter & `Prune-06` Bitfield Lowerer (`c_translate`)
//!
//! Lowers an arena-backed `c_frontend.CTranslationUnit` into canonical CoreX v1.0 `.cx` source bytes
//! conforming to `DR-10` §2.1–2.4, `DR-20` (`Prune-06` & Seam #6), `DR-21`, and `DR-22` (`ADR-22F`).
//!
//! Emits exact-fit `cx.ffi` / `core.ffi` imports (zero `W0402` unused symbols), target-ABI-calibrated
//! `MSVC` vs `SysV` / `AAPCS64` / `Wasm32` C bitfield byte arrays with synthesized getter/setter `impl`
//! methods, deduplicated opaque/complete `@repr(C)` records, and SAL / Clang FFI boundary contracts.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const codegen_abi = @import("codegen_abi.zig");
const diagnostic = @import("diag/diagnostic.zig");
const lexer = @import("lexer.zig");
const fmt_engine = @import("fmt_engine.zig");
const c_frontend = @import("c_frontend.zig");

const FileId = mem_foundation.FileId;
const BumpArena = mem_foundation.BumpArena;
const TargetSpec = codegen_abi.TargetSpec;
const DiagnosticSink = diagnostic.DiagnosticSink;
const CTranslationUnit = c_frontend.CTranslationUnit;
const CDeclId = c_frontend.CDeclId;
const CTypeId = c_frontend.CTypeId;
const CPrimitiveKind = c_frontend.CPrimitiveKind;
const CNullability = c_frontend.CNullability;
const CFfiContract = c_frontend.CFfiContract;
const CRecordLayoutAttrs = c_frontend.CRecordLayoutAttrs;
const CStructField = c_frontend.CStructField;
const MacroConstValue = c_frontend.MacroConstValue;

// ---------------------------------------- TYPES ----------------------------------------

/// Configuration options governing `.cx` code emission from a parsed `CTranslationUnit`.
pub const TranslateOptions = struct {
    /// Emits `use core.ffi.{…};` instead of `use cx.ffi.{…};` when bootstrapping `core` internals.
    is_internal_core: bool = false,
    /// Emits a 3-part `//!` module header comment at the top of the translated `.cx` buffer.
    has_header_comment: bool = false,
    /// Preserves original C nominal/symbol identifiers (adding `@allow(non_canonical_case)` where needed).
    is_preserving_c_names: bool = true,
    /// Runs `fmt_engine.formatSource` over the generated `.cx` output for guaranteed `corex fmt` idempotency.
    is_formatted: bool = true,
};

/// Ordered `cx.ffi` / `core.ffi` primitive symbols tracked for exact-fit `use` tree emission.
const FfiSymbolKind = enum(u4) {
    /// Platform `VaList` (`va_list` storage in structs, unions, locals, and typedefs).
    va_list = 0,
    /// Platform `VaListParam` (`va_list` decayed in C function parameter position).
    va_list_param = 1,
    /// Target `c_char`.
    c_char = 2,
    /// Target `c_int`.
    c_int = 3,
    /// Target `c_long`.
    c_long = 4,
    /// Target `c_longlong`.
    c_longlong = 5,
    /// Target `c_schar`.
    c_schar = 6,
    /// Target `c_short`.
    c_short = 7,
    /// Target `c_uchar`.
    c_uchar = 8,
    /// Target `c_uint`.
    c_uint = 9,
    /// Target `c_ulong`.
    c_ulong = 10,
    /// Target `c_ulonglong`.
    c_ulonglong = 11,
    /// Target `c_ushort`.
    c_ushort = 12,
};

/// Bitset tracking which `FfiSymbolKind` items were referenced in emitted declarations.
const FfiImportMask = struct {
    /// Bitmask indexed by `@backingInt(FfiSymbolKind)`.
    bits: u16 = 0,

    /// Marks `sym` as referenced in the translated `.cx` module.
    inline fn mark(self: *FfiImportMask, sym: FfiSymbolKind) void {
        self.bits |= @as(u16, 1) << @backingInt(sym);
    }

    /// Returns `true` when `sym` was referenced at least once.
    inline fn has(self: FfiImportMask, sym: FfiSymbolKind) bool {
        return (self.bits & (@as(u16, 1) << @backingInt(sym))) != 0;
    }

    /// Returns the number of distinct `ffi` symbols referenced.
    inline fn count(self: FfiImportMask) u32 {
        return @popCount(self.bits);
    }
};

/// Synthesized bitfield accessor metadata for `impl StructName` generation (`Prune-06`).
const BitfieldAccessorSpec = struct {
    /// Sanitized `.cx` getter base name (`foo` -> `pub fn foo` and `pub fn set_foo`).
    field_cx_name: []const u8,
    /// Lowered `.cx` scalar return/parameter type text (`c_int`, `u32`, `bool`, etc.).
    field_cx_type: []const u8,
    /// Backing `_bf_N` byte-array field identifier on `self`.
    storage_field_name: []const u8,
    /// Bit offset relative to byte `0` of `storage_field_name`.
    rel_bit_offset: u64,
    /// Bit width in `[1..64]`.
    bit_width: u16,
    /// `true` when `field_cx_type` is `bool`.
    is_bool: bool,
    /// `true` when two's-complement arithmetic sign-extension is required on extraction.
    is_signed: bool,
};

/// Exact byte/bit placement computed for a single C `struct` member during `Prune-06` layout lowering.
const ComputedMemberPlacement = union(enum) {
    /// Standard non-bitfield member placed at `byte_offset`.
    regular: struct {
        /// Original `CStructField`.
        field: CStructField,
        /// Exact target C ABI byte offset from struct start.
        byte_offset: u64,
        /// Target C ABI byte size of `field.type_id`.
        byte_size: u64,
        /// Natural CoreX alignment of `field.type_id` when emitted without `@packed`.
        natural_align: u32,
        /// Effective C ABI alignment after `#pragma pack` / `packed` / `alignas`.
        effective_align: u32,
    },
    /// Non-zero-width bitfield member placed at `global_bit_offset` from struct bit `0`.
    bitfield: struct {
        /// Original `CStructField`.
        field: CStructField,
        /// Global bit offset from byte `0`, bit `0` of the enclosing struct.
        global_bit_offset: u64,
        /// Exclusive byte end of the enclosing storage unit (MSVC) or touched byte span (SysV).
        storage_end_byte: u64,
        /// Bit width in `[1..64]`.
        bit_width: u16,
    },
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical alphabetical table of `cx.ffi` / `core.ffi` symbols corresponding to `FfiSymbolKind`.
const FFI_SYMBOL_TABLE = [13]struct {
    /// Tracked `FfiSymbolKind` enum discriminant.
    kind: FfiSymbolKind,
    /// Exported `.cx` symbol identifier in `cx.ffi` / `core.ffi`.
    name: []const u8,
}{
    .{ .kind = .va_list, .name = "VaList" },
    .{ .kind = .va_list_param, .name = "VaListParam" },
    .{ .kind = .c_char, .name = "c_char" },
    .{ .kind = .c_int, .name = "c_int" },
    .{ .kind = .c_long, .name = "c_long" },
    .{ .kind = .c_longlong, .name = "c_longlong" },
    .{ .kind = .c_schar, .name = "c_schar" },
    .{ .kind = .c_short, .name = "c_short" },
    .{ .kind = .c_uchar, .name = "c_uchar" },
    .{ .kind = .c_uint, .name = "c_uint" },
    .{ .kind = .c_ulong, .name = "c_ulong" },
    .{ .kind = .c_ulonglong, .name = "c_ulonglong" },
    .{ .kind = .c_ushort, .name = "c_ushort" },
};

// -------------------------------------- INTERNALS --------------------------------------

// --------------------- Identifier Hygiene ---------------------

/// Returns `true` if `ident` collides with any CoreX keyword, primitive type, or `ffi` import name.
fn isReservedCorexIdent(ident: []const u8) bool {
    if (ident.len == 0 or std.mem.eql(u8, ident, "_")) return true;
    return lexer.KEYWORD_OR_PRIM_MAP.has(ident);
}

/// Returns `true` if `ident` satisfies CoreX canonical `PascalCase` `TYPE_IDENT` rules without `W0201`.
fn isCanonicalPascalTypeIdent(ident: []const u8) bool {
    if (isReservedCorexIdent(ident)) return false;
    const classified = lexer.classifyIdentifierOrKeyword(ident);
    return classified.kind == .type_ident and classified.is_canonical;
}

/// Returns `true` if `ident` satisfies CoreX canonical `SCREAMING_SNAKE_CASE` `CONST_IDENT` rules.
fn isCanonicalScreamingConstIdent(ident: []const u8) bool {
    if (isReservedCorexIdent(ident)) return false;
    const classified = lexer.classifyIdentifierOrKeyword(ident);
    return classified.kind == .const_ident and classified.is_canonical;
}

/// Returns `true` if `ident` satisfies CoreX canonical `snake_case` `IDENT` rules without `W0201`.
fn isCanonicalSnakeValueIdent(ident: []const u8) bool {
    if (isReservedCorexIdent(ident)) return false;
    const classified = lexer.classifyIdentifierOrKeyword(ident);
    return classified.kind == .ident and classified.is_canonical;
}

/// Escapes a C struct/union field or function parameter name into a valid `.cx` identifier.
fn sanitizeFieldOrParamName(
    arena: *BumpArena,
    raw_name: []const u8,
    is_preserving_c_names: bool,
) ![]const u8 {
    if (raw_name.len == 0) return "";
    const candidate = if (is_preserving_c_names)
        raw_name
    else
        try lexer.toSnakeCase(arena.asAllocator(), raw_name);
    if (isReservedCorexIdent(candidate)) {
        return std.fmt.allocPrint(arena.asAllocator(), "{s}_", .{candidate});
    }
    return candidate;
}

/// Escapes a C `extern` function or `extern static` name, returning `(cx_ident, has_link_name_override)`.
fn sanitizeExternSymbolName(
    arena: *BumpArena,
    raw_name: []const u8,
    is_preserving_c_names: bool,
) !struct { cx_name: []const u8, has_link_name_override: bool } {
    const base_name = if (is_preserving_c_names)
        raw_name
    else
        try lexer.toSnakeCase(arena.asAllocator(), raw_name);
    if (isReservedCorexIdent(base_name)) {
        const escaped = try std.fmt.allocPrint(arena.asAllocator(), "{s}_", .{base_name});
        return .{ .cx_name = escaped, .has_link_name_override = true };
    }
    return .{
        .cx_name = base_name,
        .has_link_name_override = !std.mem.eql(u8, base_name, raw_name),
    };
}

/// Escapes a C `struct`, `union`, `enum`, or `typedef` nominal identifier for `.cx` emission.
fn sanitizeTypeIdent(
    arena: *BumpArena,
    raw_name: []const u8,
    is_preserving_c_names: bool,
) ![]const u8 {
    const base_name = if (is_preserving_c_names)
        raw_name
    else
        try lexer.toPascalCase(arena.asAllocator(), raw_name);
    if (isReservedCorexIdent(base_name)) {
        return std.fmt.allocPrint(arena.asAllocator(), "{s}Type", .{base_name});
    }
    return base_name;
}

/// Escapes UTF-8 bytes into a valid CoreX double-quoted string literal (`"` / `\` / `\n` / `{` / `}`).
fn appendEscapedCxStringLiteral(
    allocator: std.mem.Allocator,
    out_buf: *std.ArrayListUnmanaged(u8),
    raw_bytes: []const u8,
) !void {
    try out_buf.append(allocator, '"');
    for (raw_bytes) |byte_val| {
        switch (byte_val) {
            '"' => try out_buf.appendSlice(allocator, "\\\""),
            '\\' => try out_buf.appendSlice(allocator, "\\\\"),
            '\n' => try out_buf.appendSlice(allocator, "\\n"),
            '\r' => try out_buf.appendSlice(allocator, "\\r"),
            '\t' => try out_buf.appendSlice(allocator, "\\t"),
            0 => try out_buf.appendSlice(allocator, "\\0"),
            '{' => try out_buf.appendSlice(allocator, "{{"),
            '}' => try out_buf.appendSlice(allocator, "}}"),
            else => {
                if (byte_val >= 0x20 and byte_val <= 0x7E) {
                    try out_buf.append(allocator, byte_val);
                } else {
                    var hex_tmp: [4]u8 = undefined;
                    const formatted = std.fmt.bufPrint(&hex_tmp, "\\x{X:0>2}", .{byte_val}) catch unreachable;
                    try out_buf.appendSlice(allocator, formatted);
                }
            },
        }
    }
    try out_buf.append(allocator, '"');
}

/// Zero-intermediate-allocation byte writer backed by `*std.ArrayListUnmanaged(u8)`.
const ByteWriter = struct {
    /// Backing allocator for `ArrayListUnmanaged` growth.
    allocator: std.mem.Allocator,
    /// Destination byte buffer.
    buf: *std.ArrayListUnmanaged(u8),

    /// Appends `bytes` directly into `self.buf`.
    inline fn writeAll(self: ByteWriter, bytes: []const u8) !void {
        try self.buf.appendSlice(self.allocator, bytes);
    }

    /// Appends a single `byte_val` into `self.buf`.
    inline fn writeByte(self: ByteWriter, byte_val: u8) !void {
        try self.buf.append(self.allocator, byte_val);
    }

    /// Formats `fmt` with `args` directly into `self.buf`'s unused capacity slice.
    fn print(self: ByteWriter, comptime fmt: []const u8, args: anytype) !void {
        const needed: usize = @intCast(std.fmt.count(fmt, args));
        try self.buf.ensureUnusedCapacity(self.allocator, needed);
        _ = std.fmt.bufPrint(self.buf.unusedCapacitySlice()[0..needed], fmt, args) catch unreachable;
        self.buf.items.len += needed;
    }
};

// --------------------- Translator Context ---------------------

/// Stateful emitter lowering a `CTranslationUnit` into `.cx` declarations.
const CTranslator = struct {
    /// General allocator for dynamic scratch buffers.
    allocator: std.mem.Allocator,
    /// Bump arena owning temporary formatted type/identifier slices.
    arena: BumpArena,
    /// Input C11/C23 translation unit.
    unit: *const CTranslationUnit,
    /// Translation options.
    options: TranslateOptions,
    /// Bitmask of `cx.ffi` / `core.ffi` symbols referenced by emitted items.
    ffi_imports: FfiImportMask = .{},
    /// Resolved `.cx` nominal identifier per `CDeclId.asInt()` for records, enums, and typedefs.
    decl_cx_names: []const []const u8 = &.{},
    /// `true` per `CDeclId.asInt()` when a `typedef_decl` was folded into its target `struct`/`union`/`enum`.
    folded_typedefs: []bool = &.{},
    /// $O(1)$ arena-allocated slice marking each `record_decl` that had a `typedef` folded into it.
    is_folded_typedef_target: []bool = &.{},
    /// `true` per `CDeclId.asInt()` once a `record_decl` or `enum_decl` has been emitted.
    emitted_decls: []bool = &.{},
    /// Set of top-level `.cx` names already emitted (preventing duplicate `pub const` / symbol collisions).
    emitted_top_names: std.StringHashMapUnmanaged(void) = .empty,
    /// Output `.cx` body byte builder (preceded by `use cx.ffi.{…};` at final assembly).
    body_buf: std.ArrayListUnmanaged(u8) = .empty,

    /// Releases translator scratch state.
    fn deinit(self: *CTranslator) void {
        if (self.decl_cx_names.len > 0) self.allocator.free(self.decl_cx_names);
        if (self.folded_typedefs.len > 0) self.allocator.free(self.folded_typedefs);
        if (self.emitted_decls.len > 0) self.allocator.free(self.emitted_decls);
        self.emitted_top_names.deinit(self.allocator);
        self.body_buf.deinit(self.allocator);
        self.arena.deinit();
    }

    /// Returns a `ByteWriter` targeting `self.body_buf`.
    inline fn bodyWriter(self: *CTranslator) ByteWriter {
        return .{ .allocator = self.allocator, .buf = &self.body_buf };
    }

    /// Pre-computes nominal names and deduplicates `typedef struct Foo Foo` / `typedef struct { … } Foo`.
    fn prepareDeclNamesAndDeduplication(self: *CTranslator) !void {
        const decl_count = self.unit.decls.items.len;
        const names = try self.allocator.alloc([]const u8, decl_count);
        @memset(names, "");
        const folded = try self.allocator.alloc(bool, decl_count);
        @memset(folded, false);
        const folded_targets = try self.arena.allocSlice(bool, decl_count);
        @memset(folded_targets, false);
        const emitted = try self.allocator.alloc(bool, decl_count);
        @memset(emitted, false);

        // [1] Fold `typedef struct { … } Alias;` and `struct Foo; typedef struct Foo Foo;`:
        for (self.unit.decls.items, 0..) |decl, i| {
            if (decl.is_from_system_header) continue;
            if (decl.kind == .typedef_decl) {
                const td = decl.kind.typedef_decl;
                const td_node = self.unit.getType(td.target_type);
                if (td_node == .record_ref) {
                    const rec_id = td_node.record_ref;
                    const rec_decl = self.unit.getDecl(rec_id);
                    const rec = rec_decl.kind.record_decl;
                    if (rec.name.len == 0 and names[rec_id.asInt()].len == 0) {
                        names[rec_id.asInt()] = try sanitizeTypeIdent(
                            &self.arena,
                            td.name,
                            self.options.is_preserving_c_names,
                        );
                        folded[i] = true;
                        folded_targets[rec_id.asInt()] = true;
                    } else if (std.mem.eql(u8, rec.name, td.name)) {
                        names[rec_id.asInt()] = try sanitizeTypeIdent(
                            &self.arena,
                            td.name,
                            self.options.is_preserving_c_names,
                        );
                        folded[i] = true;
                        folded_targets[rec_id.asInt()] = true;
                    }
                } else if (td_node == .enum_ref) {
                    const en_id = td_node.enum_ref;
                    const en_decl = self.unit.getDecl(en_id);
                    const en = en_decl.kind.enum_decl;
                    if (en.name.len == 0 and names[en_id.asInt()].len == 0) {
                        names[en_id.asInt()] = try sanitizeTypeIdent(
                            &self.arena,
                            td.name,
                            self.options.is_preserving_c_names,
                        );
                        folded[i] = true;
                    } else if (std.mem.eql(u8, en.name, td.name)) {
                        names[en_id.asInt()] = try sanitizeTypeIdent(
                            &self.arena,
                            td.name,
                            self.options.is_preserving_c_names,
                        );
                        folded[i] = true;
                    }
                }
            }
        }

        // [2] Assign names to all remaining named and nested anonymous records/enums/typedefs:
        var anon_counter: u32 = 0;
        for (self.unit.decls.items, 0..) |decl, i| {
            if (names[i].len > 0) continue;
            switch (decl.kind) {
                .record_decl => |rec| {
                    if (rec.name.len > 0) {
                        names[i] = try sanitizeTypeIdent(
                            &self.arena,
                            rec.name,
                            self.options.is_preserving_c_names,
                        );
                    } else {
                        names[i] = try std.fmt.allocPrint(
                            self.arena.asAllocator(),
                            "CAnonRecord{d}",
                            .{anon_counter},
                        );
                        anon_counter += 1;
                    }
                },
                .enum_decl => |en| {
                    if (en.name.len > 0) {
                        names[i] = try sanitizeTypeIdent(
                            &self.arena,
                            en.name,
                            self.options.is_preserving_c_names,
                        );
                    }
                },
                .typedef_decl => |td| {
                    names[i] = try sanitizeTypeIdent(
                        &self.arena,
                        td.name,
                        self.options.is_preserving_c_names,
                    );
                },
                else => {},
            }
        }

        self.decl_cx_names = names;
        self.folded_typedefs = folded;
        self.is_folded_typedef_target = folded_targets;
        self.emitted_decls = emitted;
    }

    /// Lowers `prim` to its canonical CoreX v1.0 type string, recording any needed `ffi` import.
    fn lowerPrimitiveType(self: *CTranslator, prim: CPrimitiveKind) []const u8 {
        return switch (prim) {
            .c_void => "unit",
            .c_bool => "bool",
            .c_char => blk: {
                self.ffi_imports.mark(.c_char);
                break :blk "c_char";
            },
            .c_schar => blk: {
                self.ffi_imports.mark(.c_schar);
                break :blk "c_schar";
            },
            .c_uchar => blk: {
                self.ffi_imports.mark(.c_uchar);
                break :blk "c_uchar";
            },
            .c_short => blk: {
                self.ffi_imports.mark(.c_short);
                break :blk "c_short";
            },
            .c_ushort => blk: {
                self.ffi_imports.mark(.c_ushort);
                break :blk "c_ushort";
            },
            .c_int => blk: {
                self.ffi_imports.mark(.c_int);
                break :blk "c_int";
            },
            .c_uint => blk: {
                self.ffi_imports.mark(.c_uint);
                break :blk "c_uint";
            },
            .c_long => blk: {
                self.ffi_imports.mark(.c_long);
                break :blk "c_long";
            },
            .c_ulong => blk: {
                self.ffi_imports.mark(.c_ulong);
                break :blk "c_ulong";
            },
            .c_longlong => blk: {
                self.ffi_imports.mark(.c_longlong);
                break :blk "c_longlong";
            },
            .c_ulonglong => blk: {
                self.ffi_imports.mark(.c_ulonglong);
                break :blk "c_ulonglong";
            },
            .c_int128 => "i128",
            .c_uint128 => "u128",
            .c_float => "f32",
            .c_double => "f64",
            .c_longdouble => if (prim.byteSize(self.unit.target) == 8) "f64" else "u128",
            .exact_i8 => "i8",
            .exact_u8 => "u8",
            .exact_i16 => "i16",
            .exact_u16 => "u16",
            .exact_i32 => "i32",
            .exact_u32 => "u32",
            .exact_i64 => "i64",
            .exact_u64 => "u64",
            .exact_isize => "isize",
            .exact_usize => "usize",
            .va_list => blk: {
                self.ffi_imports.mark(.va_list);
                break :blk "VaList";
            },
        };
    }

    /// Maps an integer `CPrimitiveKind` to a built-in CoreX integer primitive (`i8`..`u64`, `isize`, `usize`).
    fn lowerEnumBackingIntPrimitive(self: *const CTranslator, prim: CPrimitiveKind) []const u8 {
        const target = self.unit.target;
        return switch (prim) {
            .c_bool, .c_uchar, .exact_u8 => "u8",
            .c_schar, .exact_i8 => "i8",
            .c_char => if (target.isCCharSigned()) "i8" else "u8",
            .c_short, .exact_i16 => "i16",
            .c_ushort, .exact_u16 => "u16",
            .c_int, .exact_i32 => "i32",
            .c_uint, .exact_u32 => "u32",
            .c_long => if (target.cLongByteSize() == 4) "i32" else "i64",
            .c_ulong => if (target.cLongByteSize() == 4) "u32" else "u64",
            .c_longlong, .exact_i64 => "i64",
            .c_ulonglong, .exact_u64 => "u64",
            .c_int128 => "i128",
            .c_uint128 => "u128",
            .exact_isize => "isize",
            .exact_usize => "usize",
            else => "i32",
        };
    }

    /// Ensures any prerequisite anonymous or forward record/enum referenced by `type_id` is emitted first.
    fn ensureReferencedNominalDeclsEmitted(self: *CTranslator, type_id: CTypeId, depth: u32) !void {
        if (type_id.isNone() or depth > c_frontend.MAX_C_PARSE_DEPTH) return;
        switch (self.unit.getType(type_id)) {
            .record_ref => |rec_id| {
                if (!self.emitted_decls[rec_id.asInt()]) {
                    const rec_decl = self.unit.getDecl(rec_id);
                    if (rec_decl.is_from_system_header or rec_decl.kind.record_decl.name.len == 0) {
                        try self.emitRecordDecl(rec_id, depth + 1);
                    }
                }
            },
            .enum_ref => |en_id| {
                if (!self.emitted_decls[en_id.asInt()]) {
                    const en_decl = self.unit.getDecl(en_id);
                    if (!en_decl.is_from_system_header and self.decl_cx_names[en_id.asInt()].len > 0) {
                        try self.emitEnumDecl(en_id);
                    }
                }
            },
            .pointer => |ptr| try self.ensureReferencedNominalDeclsEmitted(ptr.pointee, depth + 1),
            .array => |arr| try self.ensureReferencedNominalDeclsEmitted(arr.elem, depth + 1),
            .atomic_val => |inner| try self.ensureReferencedNominalDeclsEmitted(inner, depth + 1),
            .function => |fn_ty| {
                try self.ensureReferencedNominalDeclsEmitted(fn_ty.return_type, depth + 1);
                for (self.unit.getParams(fn_ty.param_start, fn_ty.param_len)) |param| {
                    try self.ensureReferencedNominalDeclsEmitted(param.type_id, depth + 1);
                }
            },
            .typedef_ref => |td_id| {
                const td_decl = self.unit.getDecl(td_id);
                if (td_decl.is_from_system_header) {
                    try self.ensureReferencedNominalDeclsEmitted(td_decl.kind.typedef_decl.target_type, depth + 1);
                }
            },
            .primitive => {},
        }
    }

    /// Lowers a `CTypeId` into canonical CoreX v1.0 type syntax (`ADR-22F`), decaying `va_list` parameters.
    fn lowerType(
        self: *CTranslator,
        type_id: CTypeId,
        override_nullability: CNullability,
        is_param_position: bool,
        depth: u32,
    ) anyerror![]const u8 {
        if (type_id.isNone() or depth > c_frontend.MAX_C_PARSE_DEPTH) return "opaque";

        // On System V `x86_64`, `va_list` (`struct __va_list_tag[1]`) decays to `VaListParam` (`*mut VaList`) in params:
        if (is_param_position) {
            const canon_node = self.unit.getType(self.unit.unwrapTypedefs(type_id));
            if (canon_node == .primitive and canon_node.primitive == .va_list) {
                self.ffi_imports.mark(.va_list_param);
                return "VaListParam";
            }
        }

        const node = self.unit.getType(type_id);
        return switch (node) {
            .primitive => |prim| self.lowerPrimitiveType(prim),
            .atomic_val => |inner| self.lowerType(inner, override_nullability, is_param_position, depth + 1),
            .typedef_ref => |td_id| {
                const td_decl = self.unit.getDecl(td_id);
                if (td_decl.is_from_system_header) {
                    return self.lowerType(
                        td_decl.kind.typedef_decl.target_type,
                        override_nullability,
                        is_param_position,
                        depth + 1,
                    );
                }
                return self.decl_cx_names[td_id.asInt()];
            },
            .record_ref => |rec_id| self.decl_cx_names[rec_id.asInt()],
            .enum_ref => |en_id| {
                const cx_name = self.decl_cx_names[en_id.asInt()];
                if (cx_name.len > 0) return cx_name;
                const en = self.unit.getDecl(en_id).kind.enum_decl;
                if (en.underlying_prim) |up| return self.lowerEnumBackingIntPrimitive(up);
                return "i32";
            },
            .array => |arr| {
                const elem_cx = try self.lowerType(arr.elem, .unspecified, false, depth + 1);
                const elem_count = arr.len orelse 0;
                return std.fmt.allocPrint(
                    self.arena.asAllocator(),
                    "[{s}; {d}]",
                    .{ elem_cx, elem_count },
                );
            },
            .function => |fn_sig| self.lowerBareFnSignature(
                fn_sig.return_type,
                fn_sig.param_start,
                fn_sig.param_len,
                fn_sig.is_variadic,
                fn_sig.is_noreturn,
                depth + 1,
            ),
            .pointer => |ptr| {
                const eff_null = if (override_nullability != .unspecified)
                    override_nullability
                else
                    ptr.nullability;

                // [1] C function pointer (`int (*cb)(void*, int)`) -> `(extern "C" fn(…))?` (`8B` niche):
                const unwrapped_pointee = self.unit.unwrapTypedefs(ptr.pointee);
                const pointee_node = self.unit.getType(unwrapped_pointee);
                if (pointee_node == .function) {
                    const fn_sig = pointee_node.function;
                    const bare_fn = try self.lowerBareFnSignature(
                        fn_sig.return_type,
                        fn_sig.param_start,
                        fn_sig.param_len,
                        fn_sig.is_variadic,
                        fn_sig.is_noreturn,
                        depth + 1,
                    );
                    if (eff_null == .non_null) return bare_fn;
                    return std.fmt.allocPrint(self.arena.asAllocator(), "({s})?", .{bare_fn});
                }

                // [2] `void*` -> `*mut opaque`, `const void*` -> `*opaque` (`ADR-22F`):
                if (pointee_node == .primitive and pointee_node.primitive == .c_void) {
                    return if (ptr.is_const) "*opaque" else "*mut opaque";
                }

                // [3] Data pointer; `const T*` -> `*T`, `T*` -> `*mut T` (never `16B` `*T?`):
                const inner_cx = try self.lowerType(ptr.pointee, .unspecified, false, depth + 1);
                return if (ptr.is_const)
                    std.fmt.allocPrint(self.arena.asAllocator(), "*{s}", .{inner_cx})
                else
                    std.fmt.allocPrint(self.arena.asAllocator(), "*mut {s}", .{inner_cx});
            },
        };
    }

    /// Formats `extern "C" fn(arg0: T0, …) [-> Ret]` for function-pointer types.
    fn lowerBareFnSignature(
        self: *CTranslator,
        return_type: CTypeId,
        param_start: u32,
        param_len: u32,
        is_variadic: bool,
        is_noreturn: bool,
        depth: u32,
    ) ![]const u8 {
        if (depth > c_frontend.MAX_C_PARSE_DEPTH) return "extern \"C\" fn()";
        var sig_buf: std.ArrayListUnmanaged(u8) = .empty;
        defer sig_buf.deinit(self.allocator);
        const sig_writer = ByteWriter{ .allocator = self.allocator, .buf = &sig_buf };

        try sig_buf.appendSlice(self.allocator, "extern \"C\" fn(");
        const params = self.unit.getParams(param_start, param_len);
        var used_param_names: std.StringHashMapUnmanaged(void) = .empty;
        defer used_param_names.deinit(self.allocator);

        for (params, 0..) |param, i| {
            if (i > 0) try sig_buf.appendSlice(self.allocator, ", ");
            const p_name = try self.chooseUniqueParamName(param.name, i, &used_param_names);
            const p_ty = try self.lowerType(param.type_id, param.contract.nullability, true, depth + 1);
            try sig_writer.print("{s}: {s}", .{ p_name, p_ty });
        }
        if (is_variadic) {
            if (params.len > 0) try sig_buf.appendSlice(self.allocator, ", ");
            try sig_buf.appendSlice(self.allocator, "...");
        }
        try sig_buf.append(self.allocator, ')');

        if (is_noreturn) {
            try sig_buf.appendSlice(self.allocator, " -> never");
        } else {
            const ret_unwrapped = self.unit.getType(self.unit.unwrapTypedefs(return_type));
            if (!(ret_unwrapped == .primitive and ret_unwrapped.primitive == .c_void)) {
                const ret_cx = try self.lowerType(return_type, .unspecified, false, depth + 1);
                try sig_writer.print(" -> {s}", .{ret_cx});
            }
        }
        return self.arena.dupe(u8, sig_buf.items);
    }

    /// Synthesizes `arg0`, `arg1`, … for unnamed C parameters and deduplicates colliding names.
    fn chooseUniqueParamName(
        self: *CTranslator,
        raw_name: []const u8,
        param_idx: usize,
        used_names: *std.StringHashMapUnmanaged(void),
    ) ![]const u8 {
        var candidate = if (raw_name.len == 0)
            try std.fmt.allocPrint(self.arena.asAllocator(), "arg{d}", .{param_idx})
        else
            try sanitizeFieldOrParamName(&self.arena, raw_name, self.options.is_preserving_c_names);

        var suffix: u32 = 1;
        while (used_names.contains(candidate)) : (suffix += 1) {
            candidate = try std.fmt.allocPrint(
                self.arena.asAllocator(),
                "{s}_{d}",
                .{ candidate, suffix },
            );
        }
        try used_names.put(self.allocator, candidate, {});
        return candidate;
    }

    // ------------------- ABI Size/Align Queries -------------------

    /// Computes exact target C ABI `sizeof(T)` for `type_id` with bounded recursion `depth`.
    fn computeCTypeByteSize(self: *const CTranslator, type_id: CTypeId, depth: u32) u64 {
        return self.unit.computeTypeByteSize(type_id, depth);
    }

    /// Computes natural target C ABI `alignof(T)` for `type_id` with bounded recursion `depth`.
    fn computeCTypeNaturalAlign(self: *const CTranslator, type_id: CTypeId, depth: u32) u32 {
        return self.unit.computeTypeNaturalAlign(type_id, depth);
    }

    /// Computes `(size_bytes, align_bytes)` for `rec_id` matching `MSVC` vs `SysV` / `AAPCS64` / `Wasm32`.
    fn computeCRecordSummary(
        self: *const CTranslator,
        rec_id: CDeclId,
        depth: u32,
    ) c_frontend.CRecordByteLayout {
        return self.unit.computeRecordByteLayout(rec_id, depth);
    }

    /// Resolves the synthesized `.cx` integer/bool type and signedness for a bitfield accessor (`E0423`-safe).
    fn lowerBitfieldAccessorType(
        self: *CTranslator,
        type_id: CTypeId,
    ) !struct { cx_type: []const u8, is_bool: bool, is_signed: bool } {
        const canon_id = self.unit.unwrapTypedefs(type_id);
        return switch (self.unit.getType(canon_id)) {
            .primitive => |prim| {
                if (prim == .c_bool) {
                    return .{ .cx_type = "bool", .is_bool = true, .is_signed = false };
                }
                const ty_txt = try self.lowerType(type_id, .unspecified, false, 0);
                return .{
                    .cx_type = ty_txt,
                    .is_bool = false,
                    .is_signed = prim.isSignedInteger(self.unit.target),
                };
            },
            .enum_ref => |en_id| {
                const en = self.unit.getDecl(en_id).kind.enum_decl;
                if (en.underlying_prim) |up| {
                    return .{
                        .cx_type = self.lowerPrimitiveType(up),
                        .is_bool = up == .c_bool,
                        .is_signed = up.isSignedInteger(self.unit.target),
                    };
                }
                const variants = self.unit.getEnumVariants(en.variant_start, en.variant_len);
                var min_v: i128 = 0;
                var max_v: i128 = 0;
                for (variants) |variant_item| {
                    min_v = @min(min_v, variant_item.value);
                    max_v = @max(max_v, variant_item.value);
                }
                if (min_v < 0) {
                    if (min_v >= std.math.minInt(i32) and max_v <= std.math.maxInt(i32)) {
                        return .{ .cx_type = self.lowerPrimitiveType(.c_int), .is_bool = false, .is_signed = true };
                    }
                    return .{ .cx_type = "i64", .is_bool = false, .is_signed = true };
                }
                const is_msvc_enum = self.unit.target.os == .windows and self.unit.target.abi == .msvc;
                if (variants.len == 0 or (is_msvc_enum and max_v <= std.math.maxInt(i32))) {
                    return .{ .cx_type = self.lowerPrimitiveType(.c_int), .is_bool = false, .is_signed = true };
                }
                if (max_v <= std.math.maxInt(u32)) {
                    return .{ .cx_type = self.lowerPrimitiveType(.c_uint), .is_bool = false, .is_signed = false };
                }
                if (max_v <= std.math.maxInt(i64)) {
                    return .{ .cx_type = "i64", .is_bool = false, .is_signed = true };
                }
                return .{ .cx_type = "u64", .is_bool = false, .is_signed = false };
            },
            else => .{
                .cx_type = try self.lowerType(type_id, .unspecified, false, 0),
                .is_bool = false,
                .is_signed = false,
            },
        };
    }

    /// Returns `true` if `return_type` or `params` pass a non-8-byte `long double` (`f80`/`fp128`) by value.
    fn hasUnsupportedLongDoubleByValue(
        self: *const CTranslator,
        return_type: CTypeId,
        params: []const c_frontend.CFnParam,
    ) bool {
        if (CPrimitiveKind.c_longdouble.byteSize(self.unit.target) == 8) return false;
        if (self.unit.hasByValueLongDouble(return_type, 0)) return true;
        for (params) |param| {
            if (self.unit.hasByValueLongDouble(param.type_id, 0)) return true;
        }
        return false;
    }

    // ------------------- Record & Bitfield Emit -------------------

    /// Emits a `@repr(C)` `struct` or `union` declaration (plus `impl` bitfield methods when needed).
    fn emitRecordDecl(self: *CTranslator, rec_id: CDeclId, depth: u32) anyerror!void {
        if (depth > c_frontend.MAX_C_PARSE_DEPTH or self.emitted_decls[rec_id.asInt()]) return;
        self.emitted_decls[rec_id.asInt()] = true;

        const rec = self.unit.getDecl(rec_id).kind.record_decl;
        const cx_name = self.decl_cx_names[rec_id.asInt()];
        if (cx_name.len == 0 or self.emitted_top_names.contains(cx_name)) return;

        // Ensure nested anonymous/referenced record/enum types are emitted prior to this record:
        if (rec.is_complete) {
            for (self.unit.getFields(rec.field_start, rec.field_len)) |fld| {
                try self.ensureReferencedNominalDeclsEmitted(fld.type_id, depth + 1);
            }
        }

        try self.emitted_top_names.put(self.allocator, cx_name, {});
        const writer = self.bodyWriter();

        // [1] Incomplete forward-declared `struct Handle;` -> opaque zero-sized nominal struct:
        if (!rec.is_complete) {
            if (!isCanonicalPascalTypeIdent(cx_name)) {
                try writer.writeAll("@allow(non_canonical_case)\n");
            }
            try writer.print(
                "@repr(C)\npub {s} {s} {{\n    _opaque: [u8; 0],\n}}\n\n",
                .{ if (rec.is_union) "union" else "struct", cx_name },
            );
            return;
        }

        const fields = self.unit.getFields(rec.field_start, rec.field_len);

        // [2] Union emission (all members overlap at byte offset 0):
        if (rec.is_union) {
            try self.emitUnionBody(rec_id, cx_name, fields, rec.layout_attrs);
            return;
        }

        // [3] Check whether this struct contains any bitfields or custom `#pragma pack` overrides:
        var has_bitfields = false;
        var has_sub_natural_pack = false;
        const pack_cap: u32 = if (rec.layout_attrs.pragma_pack > 0) rec.layout_attrs.pragma_pack else 0;
        for (fields) |fld| {
            if (fld.bit_width != null) has_bitfields = true;
            if (fld.is_packed_field or fld.explicit_align > 0) has_sub_natural_pack = true;
            if (pack_cap > 1 and self.computeCTypeNaturalAlign(fld.type_id, 0) > pack_cap) {
                has_sub_natural_pack = true;
            }
        }

        if (!has_bitfields and !has_sub_natural_pack) {
            try self.emitPlainStructBody(cx_name, fields, rec.layout_attrs);
            return;
        }

        try self.emitBitfieldOrPackedStructBody(rec_id, cx_name, fields, rec.layout_attrs);
    }

    /// Emits a C `union` declaration, synthesizing `_raw_bytes` + masked bitfield accessors when needed.
    fn emitUnionBody(
        self: *CTranslator,
        rec_id: CDeclId,
        cx_name: []const u8,
        fields: []const CStructField,
        layout_attrs: CRecordLayoutAttrs,
    ) !void {
        const summary = self.computeCRecordSummary(rec_id, 0);
        const is_packed_union = layout_attrs.is_packed or layout_attrs.pragma_pack == 1;

        var has_nonzero_bitfield = false;
        var regular_field_count: usize = 0;
        var max_regular_size: u64 = 0;
        for (fields) |fld| {
            if (fld.bit_width) |bw| {
                if (bw > 0) has_nonzero_bitfield = true;
            } else {
                regular_field_count += 1;
                max_regular_size = @max(max_regular_size, self.computeCTypeByteSize(fld.type_id, 0));
            }
        }

        const auto_reg_size = if (is_packed_union)
            max_regular_size
        else
            std.mem.alignForward(u64, max_regular_size, summary.align_bytes);
        const has_raw_bytes_layout = summary.size_bytes > 0 and
            (has_nonzero_bitfield or regular_field_count == 0 or auto_reg_size < summary.size_bytes);

        const writer = self.bodyWriter();
        if (!isCanonicalPascalTypeIdent(cx_name)) {
            try writer.writeAll("@allow(non_canonical_case)\n");
        }
        if (layout_attrs.explicit_align > 1 or (has_raw_bytes_layout and summary.align_bytes > 1)) {
            try writer.print("@align({d})\n", .{summary.align_bytes});
        }
        if (is_packed_union) {
            try writer.writeAll("@packed\n");
        }
        try writer.print("@repr(C)\npub union {s} {{\n", .{cx_name});

        if (fields.len == 0 or summary.size_bytes == 0) {
            try writer.writeAll("    _empty: [u8; 0],\n}\n\n");
            return;
        }

        var used_field_names: std.StringHashMapUnmanaged(void) = .empty;
        defer used_field_names.deinit(self.allocator);
        var accessors: std.ArrayListUnmanaged(BitfieldAccessorSpec) = .empty;
        defer accessors.deinit(self.allocator);
        var anon_idx: u32 = 0;

        for (fields) |fld| {
            if (fld.bit_width != null) continue;
            const raw_fname = if (fld.name.len > 0)
                try sanitizeFieldOrParamName(&self.arena, fld.name, self.options.is_preserving_c_names)
            else blk: {
                const gen = try std.fmt.allocPrint(self.arena.asAllocator(), "anon_{d}", .{anon_idx});
                anon_idx += 1;
                break :blk gen;
            };
            const fname = try self.dedupMemberName(raw_fname, &used_field_names);
            const fty = try self.lowerType(fld.type_id, fld.contract.nullability, false, 0);
            if (!isCanonicalSnakeValueIdent(fname)) {
                try writer.writeAll("    @allow(non_canonical_case)\n");
            }
            try self.emitInlineFieldContractAttrs(fld.contract);
            try writer.print("    pub {s}: {s},\n", .{ fname, fty });
        }

        var raw_storage_name: []const u8 = "_raw_bytes";
        if (has_raw_bytes_layout) {
            raw_storage_name = try self.dedupMemberName("_raw_bytes", &used_field_names);
            try writer.print("    pub {s}: [u8; {d}],\n", .{ raw_storage_name, summary.size_bytes });
        }
        try writer.writeAll("}\n\n");

        if (has_nonzero_bitfield) {
            for (fields) |fld| {
                const bw = fld.bit_width orelse continue;
                if (bw == 0 or fld.name.len == 0) continue;
                const raw_acc_name = try sanitizeFieldOrParamName(
                    &self.arena,
                    fld.name,
                    self.options.is_preserving_c_names,
                );
                const acc_name = try self.dedupMemberName(raw_acc_name, &used_field_names);
                const acc_info = try self.lowerBitfieldAccessorType(fld.type_id);
                try accessors.append(self.allocator, .{
                    .field_cx_name = acc_name,
                    .field_cx_type = acc_info.cx_type,
                    .storage_field_name = raw_storage_name,
                    .rel_bit_offset = 0,
                    .bit_width = bw,
                    .is_bool = acc_info.is_bool,
                    .is_signed = acc_info.is_signed,
                });
            }
            if (accessors.items.len > 0) {
                try self.emitBitfieldAccessorImpl(cx_name, accessors.items);
            }
        }
    }

    /// Emits a non-bitfield C `struct` directly in declaration order.
    fn emitPlainStructBody(
        self: *CTranslator,
        cx_name: []const u8,
        fields: []const CStructField,
        layout_attrs: CRecordLayoutAttrs,
    ) !void {
        const writer = self.bodyWriter();
        if (!isCanonicalPascalTypeIdent(cx_name)) {
            try writer.writeAll("@allow(non_canonical_case)\n");
        }
        if (layout_attrs.explicit_align > 1) {
            try writer.print("@align({d})\n", .{layout_attrs.explicit_align});
        }
        if (layout_attrs.is_packed or layout_attrs.pragma_pack == 1) {
            try writer.writeAll("@packed\n");
        }
        try writer.print("@repr(C)\npub struct {s} {{\n", .{cx_name});

        if (fields.len == 0) {
            try writer.writeAll("    _empty: [u8; 0],\n}\n\n");
            return;
        }

        var used_field_names: std.StringHashMapUnmanaged(void) = .empty;
        defer used_field_names.deinit(self.allocator);
        var anon_idx: u32 = 0;

        for (fields) |fld| {
            const raw_fname = if (fld.name.len > 0)
                try sanitizeFieldOrParamName(&self.arena, fld.name, self.options.is_preserving_c_names)
            else blk: {
                const gen = try std.fmt.allocPrint(self.arena.asAllocator(), "anon_{d}", .{anon_idx});
                anon_idx += 1;
                break :blk gen;
            };
            const fname = try self.dedupMemberName(raw_fname, &used_field_names);
            const fty = try self.lowerType(fld.type_id, fld.contract.nullability, false, 0);
            if (!isCanonicalSnakeValueIdent(fname)) {
                try writer.writeAll("    @allow(non_canonical_case)\n");
            }
            try self.emitInlineFieldContractAttrs(fld.contract);
            try writer.print("    pub {s}: {s},\n", .{ fname, fty });
        }
        try writer.writeAll("}\n\n");
    }

    /// Emits target-ABI-accurate `_bf_N: [u8; K]` bitfield arrays + synthesized `impl` getters/setters (`Prune-06`).
    fn emitBitfieldOrPackedStructBody(
        self: *CTranslator,
        rec_id: CDeclId,
        cx_name: []const u8,
        fields: []const CStructField,
        layout_attrs: CRecordLayoutAttrs,
    ) !void {
        var placements: std.ArrayListUnmanaged(ComputedMemberPlacement) = .empty;
        defer placements.deinit(self.allocator);

        const pragma_pack_cap: u32 = if (layout_attrs.pragma_pack > 0) layout_attrs.pragma_pack else 0;
        var max_align: u32 = @max(@as(u32, 1), layout_attrs.explicit_align);

        const is_ms_bitfields = (self.unit.target.os == .windows and !layout_attrs.is_gcc_struct) or
            layout_attrs.is_ms_struct;

        // [1] Compute exact bit/byte offsets for every field under MSVC vs SysV/AAPCS64/Wasm32:
        if (is_ms_bitfields) {
            var cur_bytes: u64 = 0;
            var has_unit = false;
            var unit_off: u64 = 0;
            var unit_sz: u64 = 0;
            var unit_bits: u64 = 0;

            for (fields) |fld| {
                const nat_al = self.computeCTypeNaturalAlign(fld.type_id, 0);
                const pragma_only_al = if (pragma_pack_cap > 0) @min(nat_al, pragma_pack_cap) else nat_al;
                const is_fld_packed = layout_attrs.is_packed or fld.is_packed_field;
                var eff_al = if (is_fld_packed) 1 else pragma_only_al;
                eff_al = @max(eff_al, fld.explicit_align);
                const f_sz = self.computeCTypeByteSize(fld.type_id, 0);

                if (fld.bit_width) |bw| {
                    if (bw == 0) {
                        if (has_unit) {
                            cur_bytes = unit_off + unit_sz;
                            has_unit = false;
                        }
                        continue;
                    }
                    max_align = @max(max_align, eff_al);
                    const req_unit_sz = @max(f_sz, 1);
                    if (!has_unit or unit_sz != req_unit_sz or unit_bits + bw > unit_sz * 8) {
                        if (has_unit) cur_bytes = unit_off + unit_sz;
                        cur_bytes = std.mem.alignForward(u64, cur_bytes, eff_al);
                        unit_off = cur_bytes;
                        unit_sz = req_unit_sz;
                        unit_bits = 0;
                        has_unit = true;
                    }
                    try placements.append(self.allocator, .{
                        .bitfield = .{
                            .field = fld,
                            .global_bit_offset = unit_off * 8 + unit_bits,
                            .storage_end_byte = unit_off + unit_sz,
                            .bit_width = bw,
                        },
                    });
                    unit_bits += bw;
                } else {
                    if (has_unit) {
                        cur_bytes = unit_off + unit_sz;
                        has_unit = false;
                    }
                    max_align = @max(max_align, eff_al);
                    cur_bytes = std.mem.alignForward(u64, cur_bytes, eff_al);
                    try placements.append(self.allocator, .{
                        .regular = .{
                            .field = fld,
                            .byte_offset = cur_bytes,
                            .byte_size = f_sz,
                            .natural_align = nat_al,
                            .effective_align = eff_al,
                        },
                    });
                    cur_bytes += f_sz;
                }
            }
        } else {
            var bit_cursor: u64 = 0;
            const is_aapcs64_linux = self.unit.target.arch == .aarch64 and self.unit.target.os == .linux;
            for (fields) |fld| {
                const nat_al = self.computeCTypeNaturalAlign(fld.type_id, 0);
                const pragma_only_al = if (pragma_pack_cap > 0) @min(nat_al, pragma_pack_cap) else nat_al;
                const is_fld_packed = layout_attrs.is_packed or fld.is_packed_field;
                var eff_al = if (is_fld_packed) 1 else pragma_only_al;
                eff_al = @max(eff_al, fld.explicit_align);
                const f_sz = @max(self.computeCTypeByteSize(fld.type_id, 0), 1);

                if (fld.bit_width) |bw| {
                    if (bw == 0) {
                        if (is_aapcs64_linux) {
                            max_align = @max(max_align, pragma_only_al);
                        }
                        const z_al_bits: u64 = @as(u64, pragma_only_al) * 8;
                        bit_cursor = std.mem.alignForward(u64, bit_cursor, @max(z_al_bits, 8));
                        continue;
                    }
                    if (fld.name.len > 0 or is_aapcs64_linux) {
                        max_align = @max(max_align, eff_al);
                    }
                    if (!is_fld_packed) {
                        const align_bits: u64 = @as(u64, eff_al) * 8;
                        const unit_bits: u64 = f_sz * 8;
                        const base_bit = (bit_cursor / align_bits) * align_bits;
                        if (bit_cursor - base_bit + bw > unit_bits) {
                            bit_cursor = std.mem.alignForward(u64, bit_cursor, align_bits);
                        }
                    }
                    const end_bit = bit_cursor + bw;
                    try placements.append(self.allocator, .{
                        .bitfield = .{
                            .field = fld,
                            .global_bit_offset = bit_cursor,
                            .storage_end_byte = (end_bit + 7) / 8,
                            .bit_width = bw,
                        },
                    });
                    bit_cursor = end_bit;
                } else {
                    max_align = @max(max_align, eff_al);
                    var byte_off = (bit_cursor + 7) / 8;
                    byte_off = std.mem.alignForward(u64, byte_off, eff_al);
                    const reg_sz = self.computeCTypeByteSize(fld.type_id, 0);
                    try placements.append(self.allocator, .{
                        .regular = .{
                            .field = fld,
                            .byte_offset = byte_off,
                            .byte_size = reg_sz,
                            .natural_align = nat_al,
                            .effective_align = eff_al,
                        },
                    });
                    bit_cursor = (byte_off + reg_sz) * 8;
                }
            }
        }

        const summary = self.computeCRecordSummary(rec_id, 0);
        max_align = summary.align_bytes;
        const total_struct_bytes = summary.size_bytes;

        // Check if any regular field sits at an offset unaligned to its natural CoreX alignment:
        var is_packed_struct_needed = layout_attrs.is_packed or layout_attrs.pragma_pack == 1;
        for (placements.items) |pl| {
            if (pl == .regular and pl.regular.natural_align > 1) {
                if ((pl.regular.byte_offset % pl.regular.natural_align) != 0) {
                    is_packed_struct_needed = true;
                    break;
                }
            }
        }

        // [2] Emit struct header and physical fields (`_bf_N`, `_pad_N`, and regular members):
        const writer = self.bodyWriter();
        if (!isCanonicalPascalTypeIdent(cx_name)) {
            try writer.writeAll("@allow(non_canonical_case)\n");
        }
        if (max_align > 1) {
            try writer.print("@align({d})\n", .{max_align});
        }
        if (is_packed_struct_needed) {
            try writer.writeAll("@packed\n");
        }
        try writer.print("@repr(C)\npub struct {s} {{\n", .{cx_name});

        var accessors: std.ArrayListUnmanaged(BitfieldAccessorSpec) = .empty;
        defer accessors.deinit(self.allocator);
        var used_field_names: std.StringHashMapUnmanaged(void) = .empty;
        defer used_field_names.deinit(self.allocator);

        var emitted_byte_cursor: u64 = 0;
        var bf_cluster_idx: u32 = 0;
        var pad_idx: u32 = 0;
        var anon_idx: u32 = 0;

        var idx: usize = 0;
        while (idx < placements.items.len) {
            switch (placements.items[idx]) {
                .bitfield => {
                    // Coalesce contiguous `.bitfield` entries up to the next `.regular` member:
                    const run_start = idx;
                    const first_bf_byte = placements.items[idx].bitfield.global_bit_offset / 8;
                    var cluster_end_byte = placements.items[idx].bitfield.storage_end_byte;
                    idx += 1;
                    while (idx < placements.items.len and placements.items[idx] == .bitfield) : (idx += 1) {
                        cluster_end_byte = @max(
                            cluster_end_byte,
                            placements.items[idx].bitfield.storage_end_byte,
                        );
                    }

                    if (first_bf_byte > emitted_byte_cursor) {
                        const gap = first_bf_byte - emitted_byte_cursor;
                        try writer.print("    pub _pad_{d}: [u8; {d}],\n", .{ pad_idx, gap });
                        pad_idx += 1;
                        emitted_byte_cursor = first_bf_byte;
                    }

                    const bf_byte_len = @max(cluster_end_byte - emitted_byte_cursor, 1);
                    const bf_field_name = try std.fmt.allocPrint(
                        self.arena.asAllocator(),
                        "_bf_{d}",
                        .{bf_cluster_idx},
                    );
                    bf_cluster_idx += 1;
                    const bf_base_byte = emitted_byte_cursor;
                    try writer.print("    pub {s}: [u8; {d}],\n", .{ bf_field_name, bf_byte_len });
                    emitted_byte_cursor += bf_byte_len;

                    for (placements.items[run_start..idx]) |bf_item| {
                        const bf = bf_item.bitfield;
                        if (bf.field.name.len == 0) continue;
                        const raw_acc_name = try sanitizeFieldOrParamName(
                            &self.arena,
                            bf.field.name,
                            self.options.is_preserving_c_names,
                        );
                        const acc_name = try self.dedupMemberName(raw_acc_name, &used_field_names);
                        const acc_info = try self.lowerBitfieldAccessorType(bf.field.type_id);
                        try accessors.append(self.allocator, .{
                            .field_cx_name = acc_name,
                            .field_cx_type = acc_info.cx_type,
                            .storage_field_name = bf_field_name,
                            .rel_bit_offset = bf.global_bit_offset - bf_base_byte * 8,
                            .bit_width = bf.bit_width,
                            .is_bool = acc_info.is_bool,
                            .is_signed = acc_info.is_signed,
                        });
                    }
                },
                .regular => |reg| {
                    idx += 1;
                    const corex_field_align: u32 = if (is_packed_struct_needed) 1 else reg.natural_align;
                    const natural_next_off = std.mem.alignForward(u64, emitted_byte_cursor, corex_field_align);
                    if (reg.byte_offset > natural_next_off or
                        (is_packed_struct_needed and reg.byte_offset > emitted_byte_cursor))
                    {
                        const gap = reg.byte_offset - emitted_byte_cursor;
                        try writer.print("    pub _pad_{d}: [u8; {d}],\n", .{ pad_idx, gap });
                        pad_idx += 1;
                        emitted_byte_cursor = reg.byte_offset;
                    } else {
                        emitted_byte_cursor = natural_next_off;
                    }

                    const raw_fname = if (reg.field.name.len > 0)
                        try sanitizeFieldOrParamName(
                            &self.arena,
                            reg.field.name,
                            self.options.is_preserving_c_names,
                        )
                    else blk: {
                        const gen = try std.fmt.allocPrint(self.arena.asAllocator(), "anon_{d}", .{anon_idx});
                        anon_idx += 1;
                        break :blk gen;
                    };
                    const fname = try self.dedupMemberName(raw_fname, &used_field_names);
                    const fty = try self.lowerType(reg.field.type_id, reg.field.contract.nullability, false, 0);
                    if (!isCanonicalSnakeValueIdent(fname)) {
                        try writer.writeAll("    @allow(non_canonical_case)\n");
                    }
                    try self.emitInlineFieldContractAttrs(reg.field.contract);
                    try writer.print("    pub {s}: {s},\n", .{ fname, fty });
                    emitted_byte_cursor += reg.byte_size;
                },
            }
        }

        // Emit explicit tail padding when `@packed` or trailing unnamed bitfields extend `total_struct_bytes`:
        const auto_rounded_end = if (is_packed_struct_needed)
            emitted_byte_cursor
        else
            std.mem.alignForward(u64, emitted_byte_cursor, max_align);
        if (total_struct_bytes > auto_rounded_end) {
            const tail_gap = total_struct_bytes - emitted_byte_cursor;
            try writer.print("    pub _pad_{d}: [u8; {d}],\n", .{ pad_idx, tail_gap });
            emitted_byte_cursor += tail_gap;
        }
        if (emitted_byte_cursor == 0 and total_struct_bytes == 0) {
            try writer.writeAll("    _empty: [u8; 0],\n");
        }
        try writer.writeAll("}\n\n");

        // [3] Synthesize `impl StructName` type-safe getters & setters for named bitfields:
        if (accessors.items.len > 0) {
            try self.emitBitfieldAccessorImpl(cx_name, accessors.items);
        }
    }

    /// Emits `impl StructName { pub fn <field>(&self) -> T … pub fn set_<field>(&mut self, value: T) … }`.
    fn emitBitfieldAccessorImpl(
        self: *CTranslator,
        struct_cx_name: []const u8,
        accessors: []const BitfieldAccessorSpec,
    ) !void {
        const writer = self.bodyWriter();
        try writer.print("impl {s} {{\n", .{struct_cx_name});

        for (accessors, 0..) |acc, acc_i| {
            if (acc_i > 0) try writer.writeByte('\n');

            const first_byte: u64 = acc.rel_bit_offset / 8;
            const last_byte: u64 = (acc.rel_bit_offset + acc.bit_width - 1) / 8;
            const intra_bit: u64 = acc.rel_bit_offset % 8;
            const mask_u64: u64 = if (acc.bit_width >= 64)
                std.math.maxInt(u64)
            else
                (@as(u64, 1) << @intCast(acc.bit_width)) - 1;

            // Getter (`pub fn <field>(&self) -> <FieldTy>`):
            if (!isCanonicalSnakeValueIdent(acc.field_cx_name)) {
                try writer.writeAll("    @allow(non_canonical_case)\n");
            }
            try writer.writeAll("    @inline @no_alloc @no_panic\n");
            try writer.print(
                "    pub fn {s}(&self) -> {s} {{\n        let raw_bits: u64 = (",
                .{ acc.field_cx_name, acc.field_cx_type },
            );

            var byte_i = first_byte;
            while (byte_i <= last_byte) : (byte_i += 1) {
                const local_idx = byte_i - first_byte;
                if (local_idx > 0) try writer.writeAll(" | ");
                if (local_idx == 0) {
                    if (intra_bit == 0) {
                        try writer.print("(self.{s}[{d}] as u64)", .{ acc.storage_field_name, byte_i });
                    } else {
                        try writer.print(
                            "((self.{s}[{d}] as u64) >> {d}_u64)",
                            .{ acc.storage_field_name, byte_i, intra_bit },
                        );
                    }
                } else {
                    const left_shift = local_idx * 8 - intra_bit;
                    try writer.print(
                        "((self.{s}[{d}] as u64) << {d}_u64)",
                        .{ acc.storage_field_name, byte_i, left_shift },
                    );
                }
            }

            if (acc.bit_width >= 64) {
                try writer.writeAll(");\n");
            } else {
                try writer.print(") & {d}_u64;\n", .{mask_u64});
            }

            if (acc.is_bool) {
                try writer.writeAll("        return raw_bits != 0_u64;\n    }\n\n");
            } else if (acc.is_signed) {
                if (acc.bit_width >= 64) {
                    if (std.mem.eql(u8, acc.field_cx_type, "i64")) {
                        try writer.writeAll("        return raw_bits as i64;\n    }\n\n");
                    } else {
                        try writer.print(
                            "        return (raw_bits as i64) as {s};\n    }}\n\n",
                            .{acc.field_cx_type},
                        );
                    }
                } else {
                    const sign_bit: u64 = @as(u64, 1) << @intCast(acc.bit_width - 1);
                    try writer.print(
                        "        let signed_bits: i64 = ((raw_bits ^ {d}_u64) -% {d}_u64) as i64;\n",
                        .{ sign_bit, sign_bit },
                    );
                    if (std.mem.eql(u8, acc.field_cx_type, "i64")) {
                        try writer.writeAll("        return signed_bits;\n    }\n\n");
                    } else {
                        try writer.print(
                            "        return signed_bits as {s};\n    }}\n\n",
                            .{acc.field_cx_type},
                        );
                    }
                }
            } else {
                if (std.mem.eql(u8, acc.field_cx_type, "u64")) {
                    try writer.writeAll("        return raw_bits;\n    }\n\n");
                } else {
                    try writer.print("        return raw_bits as {s};\n    }}\n\n", .{acc.field_cx_type});
                }
            }

            // Setter (`pub fn set_<field>(&mut self, value: <FieldTy>)`):
            const setter_name = try std.fmt.allocPrint(
                self.arena.asAllocator(),
                "set_{s}",
                .{acc.field_cx_name},
            );
            if (!isCanonicalSnakeValueIdent(setter_name)) {
                try writer.writeAll("    @allow(non_canonical_case)\n");
            }
            try writer.writeAll("    @inline @no_alloc @no_panic\n");
            try writer.print(
                "    pub fn {s}(&mut self, value: {s}) {{\n",
                .{ setter_name, acc.field_cx_type },
            );
            if (acc.is_bool) {
                try writer.writeAll("        let masked_val: u64 = if value { 1_u64 } else { 0_u64 };\n");
            } else if (acc.bit_width >= 64) {
                try writer.writeAll("        let masked_val: u64 = value as u64;\n");
            } else {
                try writer.print(
                    "        let masked_val: u64 = (value as u64) & {d}_u64;\n",
                    .{mask_u64},
                );
            }

            byte_i = first_byte;
            while (byte_i <= last_byte) : (byte_i += 1) {
                const ov_start = @max(byte_i * 8, acc.rel_bit_offset);
                const ov_end = @min(byte_i * 8 + 8, acc.rel_bit_offset + acc.bit_width);
                const in_byte_shift: u3 = @intCast(ov_start - byte_i * 8);
                const chunk_width: u4 = @intCast(ov_end - ov_start);
                const from_val_shift: u6 = @intCast(ov_start - acc.rel_bit_offset);
                const field_mask_u8: u8 = if (chunk_width == 8)
                    0xFF
                else
                    ((@as(u8, 1) << @intCast(chunk_width)) - 1) << in_byte_shift;
                const keep_mask_u8: u8 = ~field_mask_u8;

                if (keep_mask_u8 == 0) {
                    if (from_val_shift == 0) {
                        try writer.print(
                            "        self.{s}[{d}] = (masked_val & 255_u64) as u8;\n",
                            .{ acc.storage_field_name, byte_i },
                        );
                    } else {
                        try writer.print(
                            "        self.{s}[{d}] = ((masked_val >> {d}_u64) & 255_u64) as u8;\n",
                            .{ acc.storage_field_name, byte_i, from_val_shift },
                        );
                    }
                } else if (from_val_shift == 0) {
                    if (in_byte_shift == 0) {
                        try writer.print(
                            "        self.{s}[{d}] = (self.{s}[{d}] & {d}_u8) | ((masked_val as u8) & {d}_u8);\n",
                            .{
                                acc.storage_field_name,
                                byte_i,
                                acc.storage_field_name,
                                byte_i,
                                keep_mask_u8,
                                field_mask_u8,
                            },
                        );
                    } else {
                        try writer.print(
                            "        self.{s}[{d}] = (self.{s}[{d}] & {d}_u8) | (((masked_val as u8) << {d}_u8) & {d}_u8);\n",
                            .{
                                acc.storage_field_name,
                                byte_i,
                                acc.storage_field_name,
                                byte_i,
                                keep_mask_u8,
                                in_byte_shift,
                                field_mask_u8,
                            },
                        );
                    }
                } else {
                    try writer.print(
                        "        self.{s}[{d}] = (self.{s}[{d}] & {d}_u8) | (((masked_val >> {d}_u64) as u8) & {d}_u8);\n",
                        .{
                            acc.storage_field_name,
                            byte_i,
                            acc.storage_field_name,
                            byte_i,
                            keep_mask_u8,
                            from_val_shift,
                            field_mask_u8,
                        },
                    );
                }
            }
            try writer.writeAll("    }\n");
        }
        try writer.writeAll("}\n\n");
    }

    /// Deduplicates colliding member names within a single `struct`/`union`.
    fn dedupMemberName(
        self: *CTranslator,
        base_name: []const u8,
        used_names: *std.StringHashMapUnmanaged(void),
    ) ![]const u8 {
        var candidate = base_name;
        var suffix: u32 = 1;
        while (used_names.contains(candidate)) : (suffix += 1) {
            candidate = try std.fmt.allocPrint(
                self.arena.asAllocator(),
                "{s}_{d}",
                .{ base_name, suffix },
            );
        }
        try used_names.put(self.allocator, candidate, {});
        return candidate;
    }

    // ------------------ Enum, Typedef & Fn Emit -------------------

    /// Emits a named `@repr(C)` integer-backed `enum` or promotes an anonymous C `enum` to `pub const`s.
    fn emitEnumDecl(self: *CTranslator, en_id: CDeclId) !void {
        if (self.emitted_decls[en_id.asInt()]) return;
        self.emitted_decls[en_id.asInt()] = true;

        const en = self.unit.getDecl(en_id).kind.enum_decl;
        const cx_name = self.decl_cx_names[en_id.asInt()];
        const variants = self.unit.getEnumVariants(en.variant_start, en.variant_len);
        const writer = self.bodyWriter();

        // Determine backing primitive integer width:
        const backing_ty: []const u8 = if (en.underlying_prim) |up|
            self.lowerEnumBackingIntPrimitive(up)
        else blk: {
            var min_v: i128 = 0;
            var max_v: i128 = 0;
            for (variants) |v_item| {
                min_v = @min(min_v, v_item.value);
                max_v = @max(max_v, v_item.value);
            }
            if (min_v >= std.math.minInt(i32) and max_v <= std.math.maxInt(i32)) break :blk "i32";
            if (min_v >= 0 and max_v <= std.math.maxInt(u32)) break :blk "u32";
            if (min_v >= std.math.minInt(i64) and max_v <= std.math.maxInt(i64)) break :blk "i64";
            break :blk "u64";
        };

        // Anonymous `enum { A = 1, B = 2 };` -> direct `pub const` integer bindings:
        if (cx_name.len == 0) {
            for (variants) |v_item| {
                try self.emitSingleEnumConstBinding(v_item.name, backing_ty, v_item.value);
            }
            return;
        }

        if (self.emitted_top_names.contains(cx_name)) return;
        try self.emitted_top_names.put(self.allocator, cx_name, {});

        // Incomplete or empty enum -> integer type alias:
        if (!en.is_complete or variants.len == 0) {
            if (!isCanonicalPascalTypeIdent(cx_name)) {
                try writer.writeAll("@allow(non_canonical_case)\n");
            }
            try writer.print("pub type {s} = {s};\n\n", .{ cx_name, backing_ty });
            return;
        }

        if (!isCanonicalPascalTypeIdent(cx_name)) {
            try writer.writeAll("@allow(non_canonical_case)\n");
        }
        try writer.print("@repr(C)\npub enum {s}: {s} {{\n", .{ cx_name, backing_ty });

        var seen_discrims: std.AutoHashMapUnmanaged(i128, []const u8) = .empty;
        defer seen_discrims.deinit(self.allocator);
        var used_var_names: std.StringHashMapUnmanaged(void) = .empty;
        defer used_var_names.deinit(self.allocator);

        // Module-scope C enumerator constant alias pending emission after the `enum` body:
        const ExportedEnumConst = struct {
            /// Original C enumerator identifier.
            c_name: []const u8,
            /// Emitted `PascalCase` variant identifier on `cx_name`.
            variant_name: []const u8,
        };
        var exported_consts: std.ArrayListUnmanaged(ExportedEnumConst) = .empty;
        defer exported_consts.deinit(self.allocator);

        for (variants) |v_item| {
            if (seen_discrims.get(v_item.value)) |existing_var_name| {
                try exported_consts.append(self.allocator, .{
                    .c_name = v_item.name,
                    .variant_name = existing_var_name,
                });
                continue;
            }
            var pascal_var = try lexer.toPascalCase(self.arena.asAllocator(), v_item.name);
            if (pascal_var.len == 0 or isReservedCorexIdent(pascal_var)) {
                pascal_var = try std.fmt.allocPrint(self.arena.asAllocator(), "{s}Val", .{pascal_var});
            }
            const unique_var = try self.dedupMemberName(pascal_var, &used_var_names);
            try seen_discrims.put(self.allocator, v_item.value, unique_var);
            try writer.print("    {s} = {d},\n", .{ unique_var, v_item.value });
            try exported_consts.append(self.allocator, .{
                .c_name = v_item.name,
                .variant_name = unique_var,
            });
        }
        try writer.writeAll("}\n\n");

        // Export C enumerators at module scope (`pub const WIRE_PING: WireOp = WireOp.WirePing;`):
        for (exported_consts.items) |ec| {
            const const_name = if (isCanonicalScreamingConstIdent(ec.c_name))
                ec.c_name
            else
                try lexer.toScreamingSnakeCase(self.arena.asAllocator(), ec.c_name);
            if (const_name.len == 0 or isReservedCorexIdent(const_name)) continue;
            if (self.emitted_top_names.contains(const_name)) continue;
            try self.emitted_top_names.put(self.allocator, const_name, {});
            try writer.print(
                "pub const {s}: {s} = {s}.{s};\n",
                .{ const_name, cx_name, cx_name, ec.variant_name },
            );
        }
        if (exported_consts.items.len > 0) try writer.writeByte('\n');
    }

    /// Emits a single `pub const NAME: IntTy = val;` from an anonymous C `enum`.
    fn emitSingleEnumConstBinding(
        self: *CTranslator,
        raw_name: []const u8,
        int_ty: []const u8,
        val: i128,
    ) !void {
        const const_name = if (isCanonicalScreamingConstIdent(raw_name))
            raw_name
        else
            try lexer.toScreamingSnakeCase(self.arena.asAllocator(), raw_name);
        if (const_name.len == 0 or isReservedCorexIdent(const_name)) return;
        if (self.emitted_top_names.contains(const_name)) return;
        try self.emitted_top_names.put(self.allocator, const_name, {});
        try self.bodyWriter().print(
            "pub const {s}: {s} = {d};\n",
            .{ const_name, int_ty, val },
        );
    }

    /// Emits a non-folded C `typedef` as `pub type Alias = Target;`.
    fn emitTypedefDecl(self: *CTranslator, td_id: CDeclId) !void {
        if (self.folded_typedefs[td_id.asInt()]) return;
        const td = self.unit.getDecl(td_id).kind.typedef_decl;
        const cx_name = self.decl_cx_names[td_id.asInt()];
        if (cx_name.len == 0 or self.emitted_top_names.contains(cx_name)) return;

        try self.ensureReferencedNominalDeclsEmitted(td.target_type, 0);
        const target_node = self.unit.getType(td.target_type);
        const target_cx = if (target_node == .primitive and target_node.primitive == .c_void)
            "opaque"
        else
            try self.lowerType(td.target_type, .unspecified, false, 0);

        if (std.mem.eql(u8, cx_name, target_cx)) return;
        try self.emitted_top_names.put(self.allocator, cx_name, {});

        const writer = self.bodyWriter();
        if (!isCanonicalPascalTypeIdent(cx_name)) {
            try writer.writeAll("@allow(non_canonical_case)\n");
        }
        try writer.print("pub type {s} = {s};\n\n", .{ cx_name, target_cx });
    }

    /// Emits an `extern "C" fn` prototype with SAL/Clang FFI contract attributes (skipping `static` inline bodies).
    fn emitFnDecl(self: *CTranslator, fn_decl_id: CDeclId) !void {
        const fd = self.unit.getDecl(fn_decl_id).kind.fn_decl;
        // Phase 8 (`DR-20` Seam #6); skip `static` / inline C helper definitions with `{ … }` bodies:
        if (fd.is_static or fd.has_body) return;

        const params = self.unit.getParams(fd.param_start, fd.param_len);
        if (self.hasUnsupportedLongDoubleByValue(fd.return_type, params)) return;

        const sym_info = try sanitizeExternSymbolName(
            &self.arena,
            fd.name,
            self.options.is_preserving_c_names,
        );
        if (self.emitted_top_names.contains(sym_info.cx_name)) return;

        try self.ensureReferencedNominalDeclsEmitted(fd.return_type, 0);
        for (params) |param| {
            try self.ensureReferencedNominalDeclsEmitted(param.type_id, 0);
        }

        try self.emitted_top_names.put(self.allocator, sym_info.cx_name, {});
        const writer = self.bodyWriter();

        // Emit stacked return-level FFI contract and `@link_name` attributes:
        if (fd.ret_contract.free_with_fn.len > 0) {
            const free_sym = try sanitizeExternSymbolName(
                &self.arena,
                fd.ret_contract.free_with_fn,
                self.options.is_preserving_c_names,
            );
            try writer.print("@free_with({s})\n", .{free_sym.cx_name});
        }
        if (sym_info.has_link_name_override) {
            try writer.writeAll("@link_name(");
            try appendEscapedCxStringLiteral(self.allocator, &self.body_buf, fd.name);
            try writer.writeAll(")\n");
        }
        if (fd.ret_contract.nullability == .may_be_null) {
            try writer.writeAll("@may_be_null\n");
        } else if (fd.ret_contract.nullability == .non_null) {
            try writer.writeAll("@non_null\n");
        }
        if (fd.ret_contract.is_null_terminated) {
            try writer.writeAll("@null_terminated\n");
        }
        if (fd.ret_contract.is_owned_by_caller) {
            try writer.writeAll("@owned_by_caller\n");
        }

        try writer.print("pub extern \"C\" fn {s}(", .{sym_info.cx_name});
        var used_param_names: std.StringHashMapUnmanaged(void) = .empty;
        defer used_param_names.deinit(self.allocator);

        for (params, 0..) |param, i| {
            if (i > 0) try writer.writeAll(", ");
            try self.emitInlineParamContractAttrs(param.contract);
            const p_name = try self.chooseUniqueParamName(param.name, i, &used_param_names);
            const p_ty = try self.lowerType(param.type_id, param.contract.nullability, true, 0);
            try writer.print("{s}: {s}", .{ p_name, p_ty });
        }
        if (fd.is_variadic) {
            if (params.len > 0) try writer.writeAll(", ");
            try writer.writeAll("...");
        }
        try writer.writeByte(')');

        if (fd.is_noreturn) {
            try writer.writeAll(" -> never;\n\n");
        } else {
            const ret_unwrapped = self.unit.getType(self.unit.unwrapTypedefs(fd.return_type));
            if (ret_unwrapped == .primitive and ret_unwrapped.primitive == .c_void) {
                try writer.writeAll(";\n\n");
            } else {
                const ret_cx = try self.lowerType(fd.return_type, fd.ret_contract.nullability, false, 0);
                try writer.print(" -> {s};\n\n", .{ret_cx});
            }
        }
    }

    /// Emits inline parameter FFI contract attributes (`@slice_len(n)`, `@may_be_null`, `@null_terminated`, `@out_param`).
    fn emitInlineParamContractAttrs(self: *CTranslator, contract: CFfiContract) !void {
        const writer = self.bodyWriter();
        if (contract.slice_len_param.len > 0) {
            const len_arg = if (std.ascii.isDigit(contract.slice_len_param[0]))
                contract.slice_len_param
            else
                try sanitizeFieldOrParamName(
                    &self.arena,
                    contract.slice_len_param,
                    self.options.is_preserving_c_names,
                );
            try writer.print("@slice_len({s}) ", .{len_arg});
        }
        if (contract.nullability == .may_be_null) {
            try writer.writeAll("@may_be_null ");
        } else if (contract.nullability == .non_null) {
            try writer.writeAll("@non_null ");
        }
        if (contract.is_null_terminated) {
            try writer.writeAll("@null_terminated ");
        }
        if (contract.is_out_param) {
            try writer.writeAll("@out_param ");
        }
    }

    /// Emits struct-field pointer FFI contract attributes (`@slice_len(n)`, `@may_be_null`, `@null_terminated`).
    fn emitInlineFieldContractAttrs(self: *CTranslator, contract: CFfiContract) !void {
        const has_any = contract.slice_len_param.len > 0 or
            contract.nullability != .unspecified or
            contract.is_null_terminated;
        if (!has_any) return;
        const writer = self.bodyWriter();
        try writer.writeAll("    ");
        try self.emitInlineParamContractAttrs(contract);
        try writer.writeByte('\n');
    }

    /// Emits `pub extern "C" static [mut] name: Type;` or promotes `static const` header constants.
    fn emitVarDecl(self: *CTranslator, var_decl_id: CDeclId) !void {
        const vd = self.unit.getDecl(var_decl_id).kind.var_decl;
        if (vd.is_static) {
            if (vd.is_const) {
                if (vd.const_val) |cval| {
                    try self.emitPromotedConst(vd.name, cval);
                }
            }
            return;
        }
        if (!vd.is_extern) return;

        const sym_info = try sanitizeExternSymbolName(
            &self.arena,
            vd.name,
            self.options.is_preserving_c_names,
        );
        if (self.emitted_top_names.contains(sym_info.cx_name)) return;
        try self.ensureReferencedNominalDeclsEmitted(vd.type_id, 0);
        try self.emitted_top_names.put(self.allocator, sym_info.cx_name, {});

        const ty_cx = try self.lowerType(vd.type_id, .unspecified, false, 0);
        const writer = self.bodyWriter();
        if (sym_info.has_link_name_override) {
            try writer.writeAll("@link_name(");
            try appendEscapedCxStringLiteral(self.allocator, &self.body_buf, vd.name);
            try writer.writeAll(")\n");
        }
        if (vd.is_const) {
            try writer.print("pub extern \"C\" static {s}: {s};\n\n", .{ sym_info.cx_name, ty_cx });
        } else {
            try writer.print("pub extern \"C\" static mut {s}: {s};\n\n", .{ sym_info.cx_name, ty_cx });
        }
    }

    /// Emits `pub const NAME: <Ty> = <Lit>;` for valid `SCREAMING_SNAKE_CASE` `#define` and `static const` items.
    fn emitPromotedConst(self: *CTranslator, raw_name: []const u8, val: MacroConstValue) !void {
        if (!isCanonicalScreamingConstIdent(raw_name)) return;
        if (self.emitted_top_names.contains(raw_name)) return;
        try self.emitted_top_names.put(self.allocator, raw_name, {});

        const writer = self.bodyWriter();
        switch (val) {
            .signed_int => |sv| {
                if (sv == std.math.minInt(i64)) {
                    try writer.print(
                        "pub const {s}: i64 = -9223372036854775807_i64 -% 1_i64;\n",
                        .{raw_name},
                    );
                } else {
                    try writer.print("pub const {s}: i64 = {d}_i64;\n", .{ raw_name, sv });
                }
            },
            .unsigned_int => |uv| {
                try writer.print("pub const {s}: u64 = {d}_u64;\n", .{ raw_name, uv });
            },
            .float_val => |fv| {
                if (!std.math.isFinite(fv)) {
                    _ = self.emitted_top_names.remove(raw_name);
                    return;
                }
                var flt_buf: [64]u8 = undefined;
                const flt_txt = std.fmt.bufPrint(&flt_buf, "{d}", .{fv}) catch return;
                if (std.mem.indexOfAny(u8, flt_txt, ".eE") == null) {
                    try writer.print("pub const {s}: f64 = {s}.0;\n", .{ raw_name, flt_txt });
                } else {
                    try writer.print("pub const {s}: f64 = {s};\n", .{ raw_name, flt_txt });
                }
            },
            .string_val => |str_bytes| {
                try writer.print("pub const {s}: str = ", .{raw_name});
                try appendEscapedCxStringLiteral(self.allocator, &self.body_buf, str_bytes);
                try writer.writeAll(";\n");
            },
        }
    }

    /// Assembles the complete `.cx` source buffer (header + `use cx.ffi.{…};` + declarations).
    fn assembleFinalSource(self: *CTranslator) ![]u8 {
        var full_out: std.ArrayListUnmanaged(u8) = .empty;
        errdefer full_out.deinit(self.allocator);
        const writer = ByteWriter{ .allocator = self.allocator, .buf = &full_out };

        if (self.options.has_header_comment) {
            try writer.writeAll(
                "//! Auto-Translated C11/C23 Foreign Function Interface Bindings\n" ++
                    "//!\n" ++
                    "//! Generated by the CoreX zero-`libclang` C header translator (`DR-10`, `DR-20` `Prune-06`).\n" ++
                    "//!\n" ++
                    "//! Target-calibrated C primitive widths, bitfield byte arrays, and FFI boundary contracts.\n\n",
            );
        }

        // Emit exact-fit `use cx.ffi` / `use core.ffi` ONLY for referenced symbols:
        const import_count = self.ffi_imports.count();
        if (import_count > 0) {
            const pkg_prefix = if (self.options.is_internal_core) "core.ffi" else "cx.ffi";
            if (import_count == 1) {
                for (FFI_SYMBOL_TABLE) |entry| {
                    if (self.ffi_imports.has(entry.kind)) {
                        try writer.print("use {s}.{s};\n\n", .{ pkg_prefix, entry.name });
                        break;
                    }
                }
            } else {
                try writer.print("use {s}.{{", .{pkg_prefix});
                var emitted_i: u32 = 0;
                for (FFI_SYMBOL_TABLE) |entry| {
                    if (self.ffi_imports.has(entry.kind)) {
                        if (emitted_i > 0) try writer.writeAll(", ");
                        try writer.writeAll(entry.name);
                        emitted_i += 1;
                    }
                }
                try writer.writeAll("};\n\n");
            }
        }

        try full_out.appendSlice(self.allocator, self.body_buf.items);

        if (!self.options.is_formatted) {
            return full_out.toOwnedSlice(self.allocator);
        }

        const raw_slice = try full_out.toOwnedSlice(self.allocator);
        defer self.allocator.free(raw_slice);

        const fmt_res = try fmt_engine.formatSource(self.allocator, raw_slice, .none);
        return fmt_res.formatted_text;
    }
};

// ------------------------------------- PUBLIC API --------------------------------------

/// Translates a parsed `CTranslationUnit` into canonical CoreX v1.0 `.cx` source bytes.
///
/// Parameters:
/// - `allocator`   Allocator owning the returned UTF-8 `.cx` slice.
/// - `unit`        Parsed `CTranslationUnit` produced by `c_frontend.parseCHeader`.
/// - `options`     Controls `core.ffi` vs `cx.ffi`, C identifier preservation, and `corex fmt` pass.
pub fn translateUnit(
    allocator: std.mem.Allocator,
    unit: *const CTranslationUnit,
    options: TranslateOptions,
) ![]u8 {
    var translator = CTranslator{
        .allocator = allocator,
        .arena = BumpArena.init(allocator),
        .unit = unit,
        .options = options,
    };
    defer translator.deinit();

    try translator.prepareDeclNamesAndDeduplication();

    // [1] Emit all non-system top-level C declarations in source order:
    for (unit.decls.items, 0..) |decl, i| {
        if (decl.is_from_system_header) continue;
        const decl_id = CDeclId.fromInt(@intCast(i));
        switch (decl.kind) {
            .record_decl => |rec| {
                // Defer unnamed nested records until referenced by their enclosing struct/typedef:
                if (rec.name.len > 0 or translator.is_folded_typedef_target[decl_id.asInt()]) {
                    try translator.emitRecordDecl(decl_id, 0);
                }
            },
            .enum_decl => try translator.emitEnumDecl(decl_id),
            .typedef_decl => try translator.emitTypedefDecl(decl_id),
            .fn_decl => try translator.emitFnDecl(decl_id),
            .var_decl => try translator.emitVarDecl(decl_id),
        }
    }

    // [2] Emit promoted object-like `#define` scalar/string constants (`SCREAMING_SNAKE_CASE`):
    for (unit.macro_consts.items) |mc| {
        if (mc.is_from_system_header) continue;
        try translator.emitPromotedConst(mc.name, mc.value);
    }

    return translator.assembleFinalSource();
}

/// Preprocesses, parses, and translates a C11/C23 header buffer into canonical CoreX v1.0 `.cx` bytes.
///
/// Parameters:
/// - `allocator`           Allocator owning the returned UTF-8 `.cx` source slice.
/// - `source`              UTF-8 C11/C23 header contents.
/// - `header_path`         Logical or physical path for relative `#include "…"` resolution.
/// - `file_id`             `VfsSourceMap` `FileId` attached to `E0009` diagnostics (`FileId.none` in memory).
/// - `frontend_options`    Target ABI, `-D` defines, `-I` search paths, virtual headers, and resource caps.
/// - `translate_options`   `.cx` emission and formatting configuration.
/// - `sink`                Destination `DiagnosticSink` receiving `E0009` on C frontend failure.
pub fn translateHeaderSource(
    allocator: std.mem.Allocator,
    source: []const u8,
    header_path: []const u8,
    file_id: FileId,
    frontend_options: c_frontend.CFrontendOptions,
    translate_options: TranslateOptions,
    sink: *DiagnosticSink,
) ![]u8 {
    var unit = try c_frontend.parseCHeader(
        allocator,
        source,
        header_path,
        file_id,
        frontend_options,
        sink,
    );
    defer unit.deinit();
    return translateUnit(allocator, &unit, translate_options);
}

// ---------------------------------------- MAIN -----------------------------------------

test "c_translate: core/ffi.cx parses, formats idempotently, and typechecks with zero diagnostics" {
    const allocator = std.testing.allocator;
    const parser = @import("parser.zig");
    const syntax_arenas = @import("syntax_arenas.zig");
    const symbol_resolver = @import("symbol_resolver.zig");
    const type_system = @import("type_system.zig");

    const raw_ffi_src = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        "core/ffi.cx",
        allocator,
        .limited(256 * 1024),
    );
    defer allocator.free(raw_ffi_src);

    var lf_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer lf_buf.deinit(allocator);
    for (raw_ffi_src) |byte_val| {
        if (byte_val != '\r') try lf_buf.append(allocator, byte_val);
    }
    const core_ffi_src = lf_buf.items;

    // [1] Verify `< 150` column limit on every line of `core/ffi.cx`:
    var line_it = std.mem.splitScalar(u8, core_ffi_src, '\n');
    while (line_it.next()) |clean_line| {
        try std.testing.expect(clean_line.len < 150);
    }

    // [2] Verify `core/ffi.cx` is 100% `corex fmt` idempotent with zero syntax errors:
    const fmt_res = try fmt_engine.formatSource(allocator, core_ffi_src, FileId.fromInt(1));
    defer allocator.free(fmt_res.formatted_text);
    try std.testing.expect(!fmt_res.has_syntax_errors);
    try std.testing.expectEqualStrings(core_ffi_src, fmt_res.formatted_text);
    try std.testing.expect(!fmt_res.is_changed);

    // [3] Typecheck `core/ffi.cx` with `is_internal_core = true` and verify `CStr` layout across targets:
    const ffi_fid = FileId.fromInt(1);
    var interner = try mem_foundation.StringInterner.init(allocator);
    defer interner.deinit();
    var token_buffer = syntax_arenas.TokenBuffer.init(allocator);
    defer token_buffer.deinit();
    var cst_arena = syntax_arenas.LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = syntax_arenas.AstArena.init(allocator);
    defer ast_arena.deinit();
    var diagnostics = DiagnosticSink.init(allocator);
    defer diagnostics.deinit();

    _ = try parser.parseSource(
        core_ffi_src,
        ffi_fid,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
        &interner,
    );
    var type_pool = try type_system.InternPool.init(allocator);
    defer type_pool.deinit();
    var symbol_table = try symbol_resolver.SymbolTable.init(allocator, &interner);
    defer symbol_table.deinit();
    symbol_table.is_internal_core = true;

    _ = try symbol_resolver.collectFileModuleItems(
        &symbol_table,
        &interner,
        ffi_fid,
        core_ffi_src,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    try symbol_resolver.resolveFileUseImports(
        &symbol_table,
        &interner,
        ffi_fid,
        core_ffi_src,
        &token_buffer,
        &cst_arena,
        &diagnostics,
    );

    var checker = try type_system.TypeChecker.init(
        allocator,
        &interner,
        &type_pool,
        &symbol_table,
        ffi_fid,
        core_ffi_src,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    defer checker.deinit();
    checker.is_internal_core = true;

    try checker.resolveModuleSignatures();
    try checker.checkFileBodies();
    try std.testing.expectEqual(@as(usize, 0), diagnostics.countDiagnostics());

    for ([_]TargetSpec{
        TargetSpec.X86_64_LINUX_GNU,
        TargetSpec.AARCH64_LINUX_GNU,
        TargetSpec.X86_64_WINDOWS_MSVC,
        TargetSpec.AARCH64_APPLE_DARWIN,
        TargetSpec.WASM32_UNKNOWN_WASI,
    }) |target_spec| {
        var layout_resolver = codegen_abi.TypeLayoutResolver.init(
            allocator,
            &type_pool,
            &symbol_table,
            target_spec,
        );
        defer layout_resolver.deinit();

        var has_checked_cstr = false;
        for (symbol_table.symbols.items) |sym| {
            const sym_name = interner.get(sym.name);
            if (sym.kind == .struct_sym and std.mem.eql(u8, sym_name, "CStr")) {
                const cstr_layout = try layout_resolver.resolveType(sym.type_id);
                try std.testing.expectEqual(@as(u64, target_spec.ptrBytes()), cstr_layout.size_bytes);
                has_checked_cstr = true;
            }
        }
        try std.testing.expect(has_checked_cstr);
    }
}

test "c_translate: Prune-06 SysV vs MSVC bitfield layout parity and comptime getter/setter execution" {
    const allocator = std.testing.allocator;
    const type_system = @import("type_system.zig");

    const bitfield_c_src =
        \\#include <stdint.h>
        \\struct S2 {
        \\    int a : 10;
        \\    short b : 10;
        \\};
        \\struct __attribute__((packed)) PackedBits {
        \\    int x : 4;
        \\    int y : 30;
        \\    int z : 30;
        \\};
    ;

    // [1] Translate for `x86_64-linux-gnu` (SysV; `sizeof(S2) == 4`, `sizeof(PackedBits) == 8`):
    var sysv_sink = DiagnosticSink.init(allocator);
    defer sysv_sink.deinit();
    const sysv_cx = try translateHeaderSource(
        allocator,
        bitfield_c_src,
        "bf.h",
        .none,
        .{ .target = TargetSpec.X86_64_LINUX_GNU },
        .{},
        &sysv_sink,
    );
    defer allocator.free(sysv_cx);
    try std.testing.expectEqual(@as(u32, 0), sysv_sink.error_count);

    // [2] Translate for `x86_64-windows-msvc` (MSVC; `sizeof(S2) == 8`, `sizeof(PackedBits) == 12`):
    var msvc_sink = DiagnosticSink.init(allocator);
    defer msvc_sink.deinit();
    const msvc_cx = try translateHeaderSource(
        allocator,
        bitfield_c_src,
        "bf.h",
        .none,
        .{ .target = TargetSpec.X86_64_WINDOWS_MSVC },
        .{},
        &msvc_sink,
    );
    defer allocator.free(msvc_cx);
    try std.testing.expectEqual(@as(u32, 0), msvc_sink.error_count);

    // [3] Typecheck + execute `MirVm` `@compile_assert` verifying layout and signed bitfield roundtrip:
    const sysv_harness = try std.fmt.allocPrint(
        allocator,
        \\pub type c_int = i32;
        \\pub type c_short = i16;
        \\{s}
        \\pub comptime fn verify_sysv() -> bool {{
        \\    var s2_val: S2 = @default_init[S2]();
        \\    s2_val.set_a(-300);
        \\    s2_val.set_b(255);
        \\    var packed_val: PackedBits = @default_init[PackedBits]();
        \\    packed_val.set_x(-5);
        \\    packed_val.set_y(123456789);
        \\    packed_val.set_z(-234567890);
        \\    return s2_val.a() == -300 and s2_val.b() == 255 and
        \\        packed_val.x() == -5 and packed_val.y() == 123456789 and packed_val.z() == -234567890;
        \\}}
        \\pub fn check_all() {{
        \\    @compile_assert(@size_of[S2]() == 4, "SysV S2 must be 4 bytes");
        \\    @compile_assert(@align_of[S2]() == 4, "SysV S2 must be 4-byte aligned");
        \\    @compile_assert(@size_of[PackedBits]() == 8, "SysV PackedBits must be 8 bytes");
        \\    @compile_assert(@align_of[PackedBits]() == 1, "SysV PackedBits must be 1-byte aligned");
        \\    @compile_assert(verify_sysv(), "SysV signed bitfield getter/setter roundtrip failed");
        \\}}
    ,
        .{sysv_cx[std.mem.indexOf(u8, sysv_cx, "\n\n").? + 2 ..]},
    );
    defer allocator.free(sysv_harness);

    var sysv_tc = try type_system.typecheckSource(allocator, FileId.fromInt(2), sysv_harness);
    defer sysv_tc.deinit();
    try std.testing.expectEqual(@as(usize, 0), sysv_tc.diagnostics.countDiagnostics());

    const msvc_harness = try std.fmt.allocPrint(
        allocator,
        \\pub type c_int = i32;
        \\pub type c_short = i16;
        \\{s}
        \\pub comptime fn verify_msvc() -> bool {{
        \\    var s2_val: S2 = @default_init[S2]();
        \\    s2_val.set_a(-512);
        \\    s2_val.set_b(-123);
        \\    return s2_val.a() == -512 and s2_val.b() == -123;
        \\}}
        \\pub fn check_msvc() {{
        \\    @compile_assert(@size_of[S2]() == 8, "MSVC S2 must be 8 bytes");
        \\    @compile_assert(@align_of[S2]() == 4, "MSVC S2 must be 4-byte aligned");
        \\    @compile_assert(@size_of[PackedBits]() == 12, "MSVC PackedBits must be 12 bytes");
        \\    @compile_assert(@align_of[PackedBits]() == 1, "MSVC PackedBits must be 1-byte aligned");
        \\    @compile_assert(verify_msvc(), "MSVC signed bitfield roundtrip failed");
        \\}}
    ,
        .{msvc_cx[std.mem.indexOf(u8, msvc_cx, "\n\n").? + 2 ..]},
    );
    defer allocator.free(msvc_harness);

    var msvc_tc = try type_system.typecheckSource(allocator, FileId.fromInt(3), msvc_harness);
    defer msvc_tc.deinit();
    try std.testing.expectEqual(@as(usize, 0), msvc_tc.diagnostics.countDiagnostics());
}

test "c_translate: ADR-22F pointers, opaque structs, SAL contracts, keyword escaping, and fmt idempotency" {
    const allocator = std.testing.allocator;

    const c_header =
        \\#include <stdint.h>
        \\#include <stdbool.h>
        \\#include <stddef.h>
        \\#include <stdarg.h>
        \\
        \\#define SQLITE_OK 0
        \\#define SQLITE_VERSION "3.46.0"
        \\
        \\struct sqlite3;
        \\typedef struct sqlite3 sqlite3;
        \\
        \\typedef struct Packet {
        \\    uint32_t magic;
        \\    int type;
        \\} Packet;
        \\
        \\typedef int (*RowHandler)(void *ctx, int col_count);
        \\
        \\__attribute__((malloc(sqlite3_free)))
        \\void *sqlite3_malloc(size_t n);
        \\void sqlite3_free(void *ptr);
        \\
        \\int match(
        \\    _In_z_ const char *query,
        \\    _In_reads_(len) const uint8_t *payload,
        \\    size_t len,
        \\    _Out_ sqlite3 **out_db,
        \\    RowHandler on_row,
        \\    va_list args
        \\);
        \\
        \\extern const int global_version_num;
        \\static inline int ignored_inline_helper(int val) { return val * 2; }
    ;

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    const cx_out = try translateHeaderSource(
        allocator,
        c_header,
        "sqlite3_mini.h",
        .none,
        .{ .target = TargetSpec.X86_64_LINUX_GNU },
        .{},
        &sink,
    );
    defer allocator.free(cx_out);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);

    // [1] Verify `corex fmt` idempotency (`!is_changed`, `!has_syntax_errors`):
    const re_fmt = try fmt_engine.formatSource(allocator, cx_out, .none);
    defer allocator.free(re_fmt.formatted_text);
    try std.testing.expect(!re_fmt.has_syntax_errors);
    try std.testing.expect(!re_fmt.is_changed);

    // [2] Verify exact-fit `use cx.ffi.{VaListParam, c_char, c_int};` (zero unused `VaList` / `c_long` / `c_uint`):
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "use cx.ffi.{VaListParam, c_char, c_int};") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "args: VaListParam") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "c_ulong") == null);

    // [3] Verify opaque `sqlite3`, deduplicated `Packet`, keyword escape `type_` & `@link_name("match")`:
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "_opaque: [u8; 0]") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "pub type_: c_int") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "@link_name(\"match\")") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "pub extern \"C\" fn match_(") != null);

    // [4] Verify `ADR-22F` pointer & callback lowering + SAL / `malloc` contracts:
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "(extern \"C\" fn(ctx: *mut opaque, col_count: c_int) -> c_int)?") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "@free_with(sqlite3_free)") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "@owned_by_caller") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "@null_terminated") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "@slice_len(len)") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "@out_param") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "pub const SQLITE_OK: i64 = 0_i64;") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "pub const SQLITE_VERSION: str = \"3.46.0\";") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "ignored_inline_helper") == null);
}

test "c_translate: C23 enums with duplicate discriminants, nested anonymous unions, and core.ffi mode" {
    const allocator = std.testing.allocator;
    const type_system = @import("type_system.zig");

    const c_header =
        \\#include <stdint.h>
        \\enum Status : uint8_t {
        \\    STATUS_OK = 0,
        \\    STATUS_SUCCESS = 0,
        \\    STATUS_ERR = 1,
        \\};
        \\struct TaggedEvent {
        \\    uint32_t kind;
        \\    union {
        \\        uint64_t ticks;
        \\        double seconds;
        \\    };
        \\};
        \\int SDL_Init(unsigned int flags);
    ;

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    const cx_out = try translateHeaderSource(
        allocator,
        c_header,
        "event.h",
        .none,
        .{ .target = TargetSpec.AARCH64_APPLE_DARWIN },
        .{ .is_internal_core = true, .is_preserving_c_names = false, .has_header_comment = true },
        &sink,
    );
    defer allocator.free(cx_out);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);

    // Verify `use core.ffi.` and `@link_name("SDL_Init")` on normalized `sdl_init`:
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "use core.ffi.{c_int, c_uint};") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "@link_name(\"SDL_Init\")") != null);
    try std.testing.expect(std.mem.indexOf(u8, cx_out, "pub extern \"C\" fn sdl_init(") != null);

    // Verify the emitted enum + duplicate-discriminant constant alias + nested union typecheck cleanly:
    const body_after_use = cx_out[std.mem.indexOf(u8, cx_out, "use core.ffi").?..];
    const after_semi = body_after_use[std.mem.indexOfScalar(u8, body_after_use, ';').? + 1 ..];
    const tc_harness = try std.fmt.allocPrint(
        allocator,
        \\pub type c_int = i32;
        \\pub type c_uint = u32;
        \\{s}
        \\pub fn verify_event() {{
        \\    @compile_assert(STATUS_OK == STATUS_SUCCESS, "duplicate C enumerator alias");
        \\    @compile_assert(@size_of[TaggedEvent]() == 16, "TaggedEvent size with 8B union");
        \\}}
    ,
        .{after_semi},
    );
    defer allocator.free(tc_harness);

    var tc_res = try type_system.typecheckSource(allocator, FileId.fromInt(4), tc_harness);
    defer tc_res.deinit();
    try std.testing.expectEqual(@as(usize, 0), tc_res.diagnostics.countDiagnostics());
}

test "c_translate: [CRITICAL-03] va_list parameter decay (VaListParam 8B on SysV x86_64 vs 32B on AAPCS64)" {
    const allocator = std.testing.allocator;
    const parser = @import("parser.zig");
    const syntax_arenas = @import("syntax_arenas.zig");
    const symbol_resolver = @import("symbol_resolver.zig");
    const type_system = @import("type_system.zig");

    const vsnprintf_hdr =
        \\#include <stddef.h>
        \\#include <stdarg.h>
        \\int vsnprintf(char *buf, size_t n, const char *fmt, va_list ap);
    ;
    const mixed_va_hdr =
        \\#include <stddef.h>
        \\#include <stdarg.h>
        \\struct VaFrame {
        \\    va_list stored;
        \\};
        \\int vsnprintf(char *buf, size_t n, const char *fmt, va_list ap);
    ;

    const raw_ffi_src = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        "core/ffi.cx",
        allocator,
        .limited(256 * 1024),
    );
    defer allocator.free(raw_ffi_src);
    var lf_ffi: std.ArrayListUnmanaged(u8) = .empty;
    defer lf_ffi.deinit(allocator);
    for (raw_ffi_src) |byte_val| {
        if (byte_val != '\r') try lf_ffi.append(allocator, byte_val);
    }

    // Expected `VaList` storage and parameter ABI byte sizes for a target triple:
    const TargetExpectation = struct {
        /// Target architecture, OS, and ABI under test.
        target: TargetSpec,
        /// Expected `sizeof(VaList)` when stored in a struct or local (`bytes`).
        expected_va_storage_bytes: u64,
        /// Expected `sizeof(VaListParam)` when passed as a C function parameter (`bytes`).
        expected_va_param_bytes: u64,
    };
    const matrix = [_]TargetExpectation{
        .{
            .target = TargetSpec.X86_64_LINUX_GNU,
            .expected_va_storage_bytes = 24,
            .expected_va_param_bytes = 8,
        },
        .{
            .target = TargetSpec.AARCH64_LINUX_GNU,
            .expected_va_storage_bytes = 32,
            .expected_va_param_bytes = 32,
        },
        .{
            .target = TargetSpec.X86_64_WINDOWS_MSVC,
            .expected_va_storage_bytes = 8,
            .expected_va_param_bytes = 8,
        },
    };

    for (matrix) |entry| {
        // [1] `vsnprintf` alone imports ONLY `VaListParam` (never unused `VaList`):
        var fn_sink = DiagnosticSink.init(allocator);
        defer fn_sink.deinit();
        const fn_cx = try translateHeaderSource(
            allocator,
            vsnprintf_hdr,
            "stdio_va.h",
            .none,
            .{ .target = entry.target },
            .{},
            &fn_sink,
        );
        defer allocator.free(fn_cx);
        try std.testing.expectEqual(@as(u32, 0), fn_sink.error_count);
        try std.testing.expect(std.mem.indexOf(u8, fn_cx, "use cx.ffi.{VaListParam, c_char, c_int};") != null);
        try std.testing.expect(std.mem.indexOf(u8, fn_cx, "ap: VaListParam") != null);

        // [2] Struct field keeps `VaList` while function parameter decays to `VaListParam`:
        var mix_sink = DiagnosticSink.init(allocator);
        defer mix_sink.deinit();
        const mix_cx = try translateHeaderSource(
            allocator,
            mixed_va_hdr,
            "mixed_va.h",
            .none,
            .{ .target = entry.target },
            .{},
            &mix_sink,
        );
        defer allocator.free(mix_cx);
        try std.testing.expectEqual(@as(u32, 0), mix_sink.error_count);
        try std.testing.expect(
            std.mem.indexOf(u8, mix_cx, "use cx.ffi.{VaList, VaListParam, c_char, c_int};") != null,
        );
        try std.testing.expect(std.mem.indexOf(u8, mix_cx, "pub stored: VaList,") != null);
        try std.testing.expect(std.mem.indexOf(u8, mix_cx, "ap: VaListParam") != null);

        // [3] Typecheck `core/ffi.cx` + translated bindings under target `@cfg` and verify exact ABI byte sizes:
        const body_without_use = mix_cx[std.mem.indexOf(u8, mix_cx, "\n\n").? + 2 ..];
        const combined_cx = try std.fmt.allocPrint(allocator, "{s}\n{s}", .{ lf_ffi.items, body_without_use });
        defer allocator.free(combined_cx);

        const fid = FileId.fromInt(10);
        var interner = try mem_foundation.StringInterner.init(allocator);
        defer interner.deinit();
        var token_buffer = syntax_arenas.TokenBuffer.init(allocator);
        defer token_buffer.deinit();
        var cst_arena = syntax_arenas.LosslessCstArena.init(allocator);
        defer cst_arena.deinit();
        var ast_arena = syntax_arenas.AstArena.init(allocator);
        defer ast_arena.deinit();
        var diagnostics = DiagnosticSink.init(allocator);
        defer diagnostics.deinit();

        _ = try parser.parseSource(
            combined_cx,
            fid,
            &token_buffer,
            &cst_arena,
            &ast_arena,
            &diagnostics,
            &interner,
        );
        var type_pool = try type_system.InternPool.init(allocator);
        defer type_pool.deinit();
        var symbol_table = try symbol_resolver.SymbolTable.init(allocator, &interner);
        defer symbol_table.deinit();
        symbol_table.is_internal_core = true;
        symbol_table.cfg_env = symbol_resolver.CfgEnv.fromTargetSpec(entry.target, false);

        const mod_scope = try symbol_resolver.collectFileModuleItems(
            &symbol_table,
            &interner,
            fid,
            combined_cx,
            &token_buffer,
            &cst_arena,
            &ast_arena,
            &diagnostics,
        );
        try symbol_resolver.resolveFileUseImports(
            &symbol_table,
            &interner,
            fid,
            combined_cx,
            &token_buffer,
            &cst_arena,
            &diagnostics,
        );

        var checker = try type_system.TypeChecker.init(
            allocator,
            &interner,
            &type_pool,
            &symbol_table,
            fid,
            combined_cx,
            &token_buffer,
            &cst_arena,
            &ast_arena,
            &diagnostics,
        );
        defer checker.deinit();
        checker.is_internal_core = true;
        checker.cfg_env = symbol_table.cfg_env;
        try checker.resolveModuleSignatures();
        try checker.checkFileBodies();
        try std.testing.expectEqual(@as(usize, 0), diagnostics.countDiagnostics());

        var layout_resolver = codegen_abi.TypeLayoutResolver.init(
            allocator,
            &type_pool,
            &symbol_table,
            entry.target,
        );
        defer layout_resolver.deinit();

        const va_list_lookup = symbol_table.lookupInTargetScope(
            mod_scope,
            mod_scope,
            try interner.intern("VaList"),
            symbol_resolver.NamespaceMask.TYPE_ONLY,
        );
        try std.testing.expect(va_list_lookup == .found);
        const va_list_layout = try layout_resolver.resolveType(
            symbol_table.getSymbol(va_list_lookup.found).type_id,
        );
        try std.testing.expectEqual(entry.expected_va_storage_bytes, va_list_layout.size_bytes);

        const va_param_lookup = symbol_table.lookupInTargetScope(
            mod_scope,
            mod_scope,
            try interner.intern("VaListParam"),
            symbol_resolver.NamespaceMask.TYPE_ONLY,
        );
        try std.testing.expect(va_param_lookup == .found);
        const va_param_layout = try layout_resolver.resolveType(
            symbol_table.getSymbol(va_param_lookup.found).type_id,
        );
        try std.testing.expectEqual(entry.expected_va_param_bytes, va_param_layout.size_bytes);
    }
}

test "c_translate: [MAJOR-02/03/04] enum bitfields, union bitfields, WinHdr MSVC layout, and packed :0 typecheck" {
    const allocator = std.testing.allocator;
    const type_system = @import("type_system.zig");

    // [1] SysV `x86_64-linux-gnu`; `enum` bitfields, `union` bitfields, and `__attribute__((packed))` `: 0`:
    const sysv_c_hdr =
        \\#include <stdint.h>
        \\enum Kind {
        \\    KIND_ZERO = 0,
        \\    KIND_ONE = 1,
        \\    KIND_TWO = 2,
        \\    KIND_THREE = 3,
        \\};
        \\enum SignedKind {
        \\    SK_NEG = -1,
        \\    SK_POS = 1,
        \\};
        \\enum ByteKind : uint8_t {
        \\    BK_OFF = 0,
        \\    BK_ON = 1,
        \\};
        \\struct EnumBits {
        \\    enum Kind kind_val : 2;
        \\    enum SignedKind signed_kind : 2;
        \\    enum ByteKind byte_kind : 1;
        \\};
        \\union AnonBitsOnly {
        \\    int : 4;
        \\};
        \\union MaskedUnion {
        \\    int low_three : 3;
        \\    int raw_word;
        \\};
        \\struct __attribute__((packed)) PackedZeroGap {
        \\    char first_bf : 3;
        \\    int : 0;
        \\    char second_bf : 2;
        \\};
    ;

    var sysv_sink = DiagnosticSink.init(allocator);
    defer sysv_sink.deinit();
    const sysv_cx = try translateHeaderSource(
        allocator,
        sysv_c_hdr,
        "enum_union_bf.h",
        .none,
        .{ .target = TargetSpec.X86_64_LINUX_GNU },
        .{},
        &sysv_sink,
    );
    defer allocator.free(sysv_cx);
    try std.testing.expectEqual(@as(u32, 0), sysv_sink.error_count);

    const sysv_body = sysv_cx[std.mem.indexOf(u8, sysv_cx, "\n\n").? + 2 ..];
    const sysv_harness = try std.fmt.allocPrint(
        allocator,
        \\pub type c_char = i8;
        \\pub type c_int = i32;
        \\pub type c_uint = u32;
        \\{s}
        \\pub comptime fn verify_enum_and_union_bitfields() -> bool {{
        \\    var eb: EnumBits = @default_init[EnumBits]();
        \\    eb.set_kind_val(3);
        \\    eb.set_signed_kind(-1);
        \\    eb.set_byte_kind(1);
        \\    var mu: MaskedUnion = @default_init[MaskedUnion]();
        \\    mu.raw_word = 32;
        \\    mu.set_low_three(-3);
        \\    var pzg: PackedZeroGap = @default_init[PackedZeroGap]();
        \\    pzg.set_first_bf(-2);
        \\    pzg.set_second_bf(1);
        \\    return eb.kind_val() == 3 and eb.signed_kind() == -1 and eb.byte_kind() == 1 and
        \\        mu.low_three() == -3 and mu.raw_word == 37 and
        \\        pzg.first_bf() == -2 and pzg.second_bf() == 1;
        \\}}
        \\pub fn assert_sysv_all() {{
        \\    @compile_assert(@size_of[AnonBitsOnly]() == 4, "AnonBitsOnly must be 4B");
        \\    @compile_assert(@align_of[AnonBitsOnly]() == 4, "AnonBitsOnly must be 4B aligned");
        \\    @compile_assert(@size_of[MaskedUnion]() == 4, "MaskedUnion must be 4B");
        \\    @compile_assert(@size_of[PackedZeroGap]() == 5, "PackedZeroGap must be 5B on SysV");
        \\    @compile_assert(@align_of[PackedZeroGap]() == 1, "PackedZeroGap must be 1B aligned");
        \\    @compile_assert(verify_enum_and_union_bitfields(), "enum/union/packed bitfield roundtrip");
        \\}}
    ,
        .{sysv_body},
    );
    defer allocator.free(sysv_harness);

    var sysv_tc = try type_system.typecheckSource(allocator, FileId.fromInt(20), sysv_harness);
    defer sysv_tc.deinit();
    try std.testing.expectEqual(@as(usize, 0), sysv_tc.diagnostics.countDiagnostics());

    // [2] MSVC `x86_64-windows-msvc`; `WinHdr` (`sizeof == 8`) and `8B` `long double` (`-> f64`):
    const msvc_c_hdr =
        \\#include <stdint.h>
        \\struct WinHdr {
        \\    uint16_t ver : 4;
        \\    uint16_t flags : 12;
        \\    uint32_t seq : 16;
        \\};
        \\_Static_assert(sizeof(struct WinHdr) == 8, "MSVC WinHdr 8B");
        \\long double sinl(long double val);
    ;
    var msvc_sink = DiagnosticSink.init(allocator);
    defer msvc_sink.deinit();
    const msvc_cx = try translateHeaderSource(
        allocator,
        msvc_c_hdr,
        "msvc_hdr.h",
        .none,
        .{ .target = TargetSpec.X86_64_WINDOWS_MSVC },
        .{},
        &msvc_sink,
    );
    defer allocator.free(msvc_cx);
    try std.testing.expectEqual(@as(u32, 0), msvc_sink.error_count);
    try std.testing.expect(std.mem.indexOf(u8, msvc_cx, "pub extern \"C\" fn sinl(val: f64) -> f64;") != null);

    const msvc_harness = try std.fmt.allocPrint(
        allocator,
        \\{s}
        \\pub fn assert_msvc_win_hdr() {{
        \\    @compile_assert(@size_of[WinHdr]() == 8, "MSVC WinHdr must be 8B");
        \\    @compile_assert(@align_of[WinHdr]() == 4, "MSVC WinHdr must be 4B aligned");
        \\}}
    ,
        .{msvc_cx},
    );
    defer allocator.free(msvc_harness);

    var msvc_tc = try type_system.typecheckSource(allocator, FileId.fromInt(21), msvc_harness);
    defer msvc_tc.deinit();
    try std.testing.expectEqual(@as(usize, 0), msvc_tc.diagnostics.countDiagnostics());
}

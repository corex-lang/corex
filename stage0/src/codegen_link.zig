//! CoreX Stage-0 Cross-Target Linker, Deterministic Archive & COFF `.def` -> `.lib` Bridge
//!
//! Implements Phase 8 cross-target binary linking across all 11 canonical targets (`DR-10` §1–§3,
//! `DR-20` `Prune-02` & `D-11`), deterministic `!<arch>\n` static archive generation (`K_GNU`,
//! `K_BSD`, `K_COFF`), and programmatic PE/COFF `.def` to Short-Import `.lib` synthesis without
//! external `lib.exe`, `ar`, `dlltool`, or Windows/macOS SDK dependencies.
//!
//! Delegates to the in-process C++20 `corex_llvm` static bridge (`cx_llvm_link_with_lld`,
//! `cx_llvm_write_archive`, `cx_llvm_write_coff_import_library`) when `-Dllvm-prefix` is active,
//! and falls back seamlessly to pure-Zig deterministic writers + `zig cc` (`LLD`) otherwise.

const std = @import("std");
const build_options = @import("build_options");
const mem_foundation = @import("mem_foundation.zig");
const diagnostic = @import("diag/diagnostic.zig");
const codegen_abi = @import("codegen_abi.zig");
const sim_seam = @import("sim_seam.zig");

const Span = mem_foundation.Span;
const DiagnosticSink = diagnostic.DiagnosticSink;
const TargetSpec = codegen_abi.TargetSpec;
const LinkMode = codegen_abi.LinkMode;
const OutputArtifactKind = codegen_abi.OutputArtifactKind;

// ---------------------------------------- TYPES ----------------------------------------

// -------------------- C99 Bridge Bindings ---------------------

/// Strongly typed C99 FFI declarations mirroring `stage0/src/corex_llvm.h` (strictly typed handles).
const c_llvm_link_bridge = struct {
    /// Mirrors `CxLldFlavor` in `stage0/src/corex_llvm.h`.
    pub const CxLldFlavor = enum(c_int) {
        /// Linux / Unix ELF64 driver (`ld.lld`).
        elf = 0,
        /// Apple Darwin Mach-O driver (`ld64.lld`).
        macho = 1,
        /// Windows PE/COFF driver (`lld-link`).
        coff = 2,
        /// WebAssembly module driver (`wasm-ld`).
        wasm = 3,
    };

    /// Success status code matching `CX_LLVM_OK` (`0`).
    pub const CX_LLVM_OK: i32 = 0;

    /// Returns `1` when embedded `lld` drivers are compiled into `corex_llvm.cpp`.
    pub extern "c" fn cx_llvm_has_embedded_lld() c_int;

    /// Invokes embedded `lld` (`ld.lld`, `ld64.lld`, `lld-link`, `wasm-ld`) in-process.
    pub extern "c" fn cx_llvm_link_with_lld(
        flavor: CxLldFlavor,
        args_ptr: [*]const [*:0]const u8,
        args_len: usize,
        err_buf: [*]u8,
        err_cap: usize,
    ) i32;

    /// Writes a deterministic `.a` or `.lib` archive via `llvm::writeArchive`.
    pub extern "c" fn cx_llvm_write_archive(
        output_path: [*:0]const u8,
        member_paths_ptr: [*]const [*:0]const u8,
        member_paths_len: usize,
        is_darwin: c_int,
        is_coff_thin_or_win: c_int,
        err_buf: [*]u8,
        err_cap: usize,
    ) i32;

    /// Synthesizes a PE/COFF Short-Import `.lib` from `.def` text via `llvm::object::writeImportLibrary`.
    pub extern "c" fn cx_llvm_write_coff_import_library(
        def_contents_ptr: [*]const u8,
        def_contents_len: usize,
        output_lib_path: [*:0]const u8,
        coff_machine: u16,
        err_buf: [*]u8,
        err_cap: usize,
    ) i32;
};

// ------------- Archive & COFF Import Descriptors --------------

/// Error set returned by cross-target linking, archive writing, and `.def` -> `.lib` synthesis.
pub const LinkError = error{
    /// Backing allocator ran out of memory.
    OutOfMemory,
    /// Malformed `.def` module definition syntax or empty DLL name.
    InvalidModuleDef,
    /// Input object/member file could not be opened or read.
    MemberReadFailed,
    /// Archive serialization or disk publication failed.
    ArchiveWriteFailed,
    /// Target is not a Windows PE/COFF architecture for `.def` import synthesis.
    UnsupportedCoffTarget,
    /// Embedded `lld` or `zig cc` linker invocation failed (`E0008`).
    LinkerFailed,
};

/// Canonical `!<arch>\n` static archive symbol-table layout flavor.
pub const ArchiveKind = enum(u8) {
    /// System V / GNU `ar` format (`/` big-endian symbol directory, `//` longnames).
    gnu = 0,
    /// BSD / Apple Darwin `ar` format (`#1/<len>` headers + `__.SYMDEF SORTED` `ranlib` directory).
    darwin_bsd = 1,
    /// Microsoft PE/COFF `.lib` format (1st big-endian `/` + 2nd little-endian indexed `/` directory).
    coff = 2,

    /// Selects the canonical `ArchiveKind` for `spec` and optional `output_path` extension.
    pub fn forTarget(spec: TargetSpec, output_path: []const u8) ArchiveKind {
        if (spec.isDarwin()) return .darwin_bsd;
        if (spec.isWindows() and (spec.abi == .msvc or std.mem.endsWith(u8, output_path, ".lib"))) {
            return .coff;
        }
        return .gnu;
    }
};

/// In-memory archive member descriptor consumed by `serializeDeterministicArchiveBytes`.
pub const ArchiveMemberInput = struct {
    /// Archive member filename (basename without directory prefix, e.g., `"module.o"` or `"kernel32.dll"`).
    name: []const u8,
    /// Raw member payload bytes (object file or 20-byte COFF Short Import record).
    data: []const u8,
    /// Optional pre-populated exported symbol names; when `null`, extracted automatically from `data`.
    explicit_symbols: ?[]const []const u8 = null,
};

/// Target PE/COFF machine identifier for Windows Short-Import `.lib` generation (`DR-10` §1.2.3).
pub const CoffMachine = enum(u16) {
    /// 64-bit x86 (`IMAGE_FILE_MACHINE_AMD64`).
    amd64 = 0x8664,
    /// 64-bit ARM (`IMAGE_FILE_MACHINE_ARM64`).
    arm64 = 0xAA64,

    /// Resolves `CoffMachine` from `spec` (`null` for non-Windows targets).
    pub inline fn forTarget(spec: TargetSpec) ?CoffMachine {
        if (!spec.isWindows()) return null;
        return switch (spec.arch) {
            .x86_64 => .amd64,
            .aarch64 => .arm64,
            .wasm32 => null,
        };
    }

    /// Returns the COFF `ADDR32NB` 32-bit RVA relocation type code for `self`.
    pub inline fn addr32NbRelocType(self: CoffMachine) u16 {
        return switch (self) {
            .amd64 => @backingInt(std.coff.IMAGE.REL.AMD64.ADDR32NB),
            .arm64 => @backingInt(std.coff.IMAGE.REL.ARM64.ADDR32NB),
        };
    }
};

/// Single parsed `EXPORTS` symbol entry from a Windows `.def` module definition file.
pub const ModuleDefExport = struct {
    /// Public imported symbol identifier owned by `ParsedModuleDef` (`SymName`).
    sym_name: []u8,
    /// Optional target DLL export alias when `SymName == DllExportName` is present (`IMPORT_NAME_EXPORTAS`).
    ext_name: ?[]u8 = null,
    /// Optional `@ordinal` value (`1..65535`).
    ordinal: ?u16 = null,
    /// `true` when `NONAME` follows `@ordinal` (imports strictly by ordinal (`IMPORT_OBJECT_ORDINAL`)).
    is_noname: bool = false,
    /// `true` when `DATA` is specified (`IMPORT_DATA`, omitting the jump thunk symbol).
    is_data: bool = false,
    /// `true` when `CONSTANT` is specified (`IMPORT_CONST`).
    is_constant: bool = false,
    /// `true` when `PRIVATE` is specified (omitted from generated import library).
    is_private: bool = false,
};

/// Case-normalized attribute keyword following a symbol inside a `.def` `EXPORTS` entry.
const DefExportAttrKeyword = enum(u8) {
    /// Marks an export as `CONSTANT` (`IMPORT_CONST`).
    constant,
    /// Marks an export as `DATA` (`IMPORT_DATA`).
    data,
    /// Marks an `@ordinal` export as `NONAME` (`IMPORT_OBJECT_ORDINAL`).
    noname,
    /// Excludes an export from the synthesized import library (`PRIVATE`).
    private,
};

/// Owned representation of a parsed Windows `.def` module definition file.
pub const ParsedModuleDef = struct {
    /// Target DLL filename including extension (e.g., `"kernel32.dll"`), owned by `allocator`.
    dll_name: []u8,
    /// Ordered exported symbol specifications, owned by `allocator`.
    exports: []ModuleDefExport,

    /// Releases all strings and slices owned by `self`.
    pub fn deinit(self: *ParsedModuleDef, allocator: std.mem.Allocator) void {
        allocator.free(self.dll_name);
        for (self.exports) |exp_item| {
            allocator.free(exp_item.sym_name);
            if (exp_item.ext_name) |ext_s| allocator.free(ext_s);
        }
        allocator.free(self.exports);
        self.* = undefined;
    }
};

/// 20-byte binary-exact PE/COFF Short Import Header (`DR-10` §1.2.3 & §3.3).
pub const CoffShortImportHeader = extern struct {
    /// Must be `0x0000` (`IMAGE_FILE_MACHINE_UNKNOWN`).
    sig1: u16 = 0x0000,
    /// Must be `0xFFFF` (`IMPORT_OBJECT_HDR_SIG2`).
    sig2: u16 = 0xFFFF,
    /// Structure format version (`0`).
    version: u16 = 0,
    /// Target `CoffMachine` (`0x8664` or `0xAA64`).
    machine: u16,
    /// Deterministic zero timestamp (`0`).
    time_date_stamp: u32 = 0,
    /// Byte length of `<SymbolName>\0<DllName>\0[ExportName\0]` payload immediately following header.
    size_of_data: u32,
    /// Export ordinal (when `IMPORT_OBJECT_ORDINAL`) or linker hint (`0` default).
    ordinal_or_hint: u16 = 0,
    /// Packed `ImportType` (`bits 0..1`) | (`ImportNameType` << 2) (`bits 2..4`).
    type_info: u16,
};

// ---------------- Cross-Target Linker Options -----------------

/// Configuration bundle consumed by `buildZigCcLinkArgs` and `linkCrossTarget`.
pub const CrossLinkOptions = struct {
    /// Target architecture, OS, SIMD tier, and C ABI flavor.
    target: TargetSpec,
    /// Input relocatable object paths (`.o` / `.obj`) and static archive paths (`.a` / `.lib`).
    object_paths: []const []const u8,
    /// Destination path on disk (`.exe`, `.wasm`, `.so`, `.dylib`, `.dll`, `.a`, `.lib`).
    output_path: []const u8,
    /// Requested output artifact kind (`.executable`, `.static_library`, `.shared_library`).
    artifact_kind: OutputArtifactKind = .executable,
    /// Requested binary linkage mode (`.auto`, `.static`, `.dynamic`).
    link_mode: LinkMode = .auto,
    /// `true` in `--release` builds (enables `-Oz` and `--strip-all` on WebAssembly targets).
    is_release_mode: bool = false,
    /// `true` when DWARF v5 debug line tables are present (`-Wl,--compress-debug-sections=zstd` on Linux ELF).
    has_dwarf_tables: bool = false,
    /// `true` to omit standard C startup / `libc` (`-nostdlib`, automatic on `wasm32-unknown-freestanding`).
    is_nostdlib: bool = false,
    /// Optional custom entrypoint symbol (`-Wl,-e,<sym>` / `/ENTRY:<sym>`).
    entry_symbol: ?[]const u8 = null,
    /// Additional library names (`-l<name>`) or direct `.a`/`.lib`/`.def` paths.
    extra_libs: []const []const u8 = &.{},
    /// Additional library search directories (`-L<dir>`).
    lib_dirs: []const []const u8 = &.{},
    /// Optional Windows `.def` module definition file paths synthesized into Short-Import `.lib`s on demand.
    def_files: []const []const u8 = &.{},
    /// Prefer in-process `cx_llvm_link_with_lld` when embedded `lld` is linked and `is_nostdlib` is active.
    is_embedded_lld_preferred: bool = true,
    /// Optional host environment map forwarded to `zig` executable lookup and `zig cc`.
    environ_map: ?*const std.process.Environ.Map = null,
    /// Optional `DiagnosticSink` receiving structured `E0008` diagnostics on linker failure.
    diagnostic_sink: ?*DiagnosticSink = null,
};

/// Internal symbol-to-member binding used when constructing archive symbol directories.
const IndexedArchiveSymbol = struct {
    /// Borrowed symbol name slice.
    name: []const u8,
    /// Zero-based index into the archive's regular member array.
    member_index: u32,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Standard 8-byte Unix / COFF `ar` magic signature.
pub const ARCHIVE_MAGIC: *const [8]u8 = "!<arch>\n";
/// Byte size of each fixed-width ASCII `ar` member header.
const AR_HEADER_BYTES: usize = 60;
/// COFF section characteristics for `.idata$2` and `.idata$3` (`CNT_INITIALIZED_DATA | ALIGN_4BYTES | MEM_READ | MEM_WRITE`).
const COFF_SCN_IDATA_4B_RW: u32 = 0xC030_0040;
/// COFF section characteristics for `.idata$6` (`CNT_INITIALIZED_DATA | ALIGN_2BYTES | MEM_READ | MEM_WRITE`).
const COFF_SCN_IDATA_2B_RW: u32 = 0xC020_0040;
/// COFF section characteristics for `.idata$4` and `.idata$5` (`CNT_INITIALIZED_DATA | ALIGN_8BYTES | MEM_READ | MEM_WRITE`).
const COFF_SCN_IDATA_8B_RW: u32 = 0xC040_0040;
/// COFF symbol storage class `IMAGE_SYM_CLASS_EXTERNAL` (`2`).
const COFF_SYM_CLASS_EXTERNAL: u8 = 2;
/// COFF symbol storage class `IMAGE_SYM_CLASS_STATIC` (`3`).
const COFF_SYM_CLASS_STATIC: u8 = 3;
/// COFF symbol storage class `IMAGE_SYM_CLASS_SECTION` (`104`).
const COFF_SYM_CLASS_SECTION: u8 = 104;
/// COFF symbol storage class `IMAGE_SYM_CLASS_WEAK_EXTERNAL` (`105`).
const COFF_SYM_CLASS_WEAK_EXTERNAL: u8 = 105;
/// Short-import `ImportType` code for executable functions (`IMPORT_CODE = 0`).
const COFF_IMPORT_CODE: u16 = 0;
/// Short-import `ImportType` code for exported data variables (`IMPORT_DATA = 1`).
const COFF_IMPORT_DATA: u16 = 1;
/// Short-import `ImportType` code for `CONSTANT` exports (`IMPORT_CONST = 2`).
const COFF_IMPORT_CONST: u16 = 2;
/// Short-import `ImportNameType` importing strictly by 16-bit ordinal (`IMPORT_OBJECT_ORDINAL = 0`).
const COFF_IMPORT_NAME_ORDINAL: u16 = 0;
/// Short-import `ImportNameType` importing by exact public symbol name (`IMPORT_OBJECT_NAME = 1`).
const COFF_IMPORT_NAME_EXACT: u16 = 1;
/// Short-import `ImportNameType` aliasing public symbol to internal DLL export (`IMPORT_NAME_EXPORTAS = 4`).
const COFF_IMPORT_NAME_EXPORTAS: u16 = 4;
/// $O(1)$ lowercase keyword table for `.def` `EXPORTS` symbol attributes.
const DEF_EXPORT_ATTR_MAP = std.StaticStringMap(DefExportAttrKeyword).initComptime(.{
    .{ "const", .constant },
    .{ "constant", .constant },
    .{ "data", .data },
    .{ "noname", .noname },
    .{ "private", .private },
});
/// $O(1)$ lowercase keyword set for non-`EXPORTS` `.def` section headers that terminate `EXPORTS` mode.
const DEF_OTHER_SECTIONS_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "description", {} },
    .{ "heapsize", {} },
    .{ "sections", {} },
    .{ "segments", {} },
    .{ "stacksize", {} },
    .{ "version", {} },
});
/// $O(1)$ static extension set identifying direct archive/object/shared-library path arguments.
const DIRECT_LIB_EXT_MAP = std.StaticStringMap(void).initComptime(.{
    .{ ".a", {} },
    .{ ".dll", {} },
    .{ ".dylib", {} },
    .{ ".lib", {} },
    .{ ".o", {} },
    .{ ".obj", {} },
    .{ ".so", {} },
    .{ ".tbd", {} },
    .{ ".wasm", {} },
});
/// Monotonic scratch sequence counter isolating concurrent `linkCrossTarget` staging directories.
var next_link_scratch_seq: std.atomic.Value(u64) = std.atomic.Value(u64).init(1);

// -------------------------------------- INTERNALS --------------------------------------

// --------------- Object Symbol Table Extraction ---------------

/// Aligns `val` upward to the next multiple of `align_to` (`align_to` must be a power of two).
inline fn alignUpUsize(val: usize, align_to: usize) usize {
    return (val + (align_to - 1)) & ~(align_to - 1);
}

/// Decodes an unsigned LEB128 integer from `bytes[*cursor_ptr..]` (`null` on truncation or overflow).
fn readUleb128(bytes: []const u8, cursor_ptr: *usize) ?u64 {
    var result: u64 = 0;
    var shift: u6 = 0;
    var pos = cursor_ptr.*;
    while (pos < bytes.len) {
        const byte_val = bytes[pos];
        pos += 1;
        result |= (@as(u64, byte_val & 0x7F) << shift);
        if ((byte_val & 0x80) == 0) {
            cursor_ptr.* = pos;
            return result;
        }
        if (shift >= 57) return null;
        shift += 7;
    }
    return null;
}

/// Skips a single signed or unsigned LEB128 integer in `bytes[*cursor_ptr..]`.
fn skipLeb128(bytes: []const u8, cursor_ptr: *usize) bool {
    var pos = cursor_ptr.*;
    var count: usize = 0;
    while (pos < bytes.len and count < 10) : (count += 1) {
        const byte_val = bytes[pos];
        pos += 1;
        if ((byte_val & 0x80) == 0) {
            cursor_ptr.* = pos;
            return true;
        }
    }
    return false;
}

/// Appends a duplicated symbol name to `out_syms` if non-empty.
fn appendOwnedSymbol(
    allocator: std.mem.Allocator,
    out_syms: *std.ArrayListUnmanaged([]u8),
    sym_name: []const u8,
) !void {
    if (sym_name.len == 0) return;
    try out_syms.append(allocator, try allocator.dupe(u8, sym_name));
}

/// Extracts defined global/weak symbols from a little-endian ELF64 or ELF32 relocatable object.
fn extractElfDefinedSymbols(
    allocator: std.mem.Allocator,
    obj_bytes: []const u8,
    out_syms: *std.ArrayListUnmanaged([]u8),
) !void {
    if (obj_bytes.len < 64 or obj_bytes[5] != 1) return;
    const ei_class = obj_bytes[4];
    if (ei_class == 2) {
        const shoff: usize = @intCast(std.mem.readInt(u64, obj_bytes[40..48], .little));
        const shentsize: usize = std.mem.readInt(u16, obj_bytes[58..60], .little);
        const shnum: usize = std.mem.readInt(u16, obj_bytes[60..62], .little);
        if (shoff == 0 or shentsize < 64 or shoff + shentsize * shnum > obj_bytes.len) return;

        var sec_i: usize = 0;
        while (sec_i < shnum) : (sec_i += 1) {
            const sh_base = shoff + sec_i * shentsize;
            const sh_type = std.mem.readInt(u32, obj_bytes[sh_base + 4 ..][0..4], .little);
            if (sh_type != 2) continue; // `SHT_SYMTAB == 2`.

            const sym_off: usize = @intCast(std.mem.readInt(u64, obj_bytes[sh_base + 24 ..][0..8], .little));
            const sym_size: usize = @intCast(std.mem.readInt(u64, obj_bytes[sh_base + 32 ..][0..8], .little));
            const str_sec_idx: usize = std.mem.readInt(u32, obj_bytes[sh_base + 40 ..][0..4], .little);
            const first_global: usize = std.mem.readInt(u32, obj_bytes[sh_base + 44 ..][0..4], .little);
            const sym_entsize_raw: usize = @intCast(std.mem.readInt(u64, obj_bytes[sh_base + 56 ..][0..8], .little));
            const sym_entsize: usize = if (sym_entsize_raw >= 24) sym_entsize_raw else 24;
            if (str_sec_idx >= shnum or sym_off + sym_size > obj_bytes.len) continue;

            const str_sh = shoff + str_sec_idx * shentsize;
            const str_off: usize = @intCast(std.mem.readInt(u64, obj_bytes[str_sh + 24 ..][0..8], .little));
            const str_size: usize = @intCast(std.mem.readInt(u64, obj_bytes[str_sh + 32 ..][0..8], .little));
            if (str_off + str_size > obj_bytes.len) continue;
            const strtab = obj_bytes[str_off .. str_off + str_size];

            const sym_count = sym_size / sym_entsize;
            var sym_i: usize = @min(first_global, sym_count);
            while (sym_i < sym_count) : (sym_i += 1) {
                const entry = obj_bytes[sym_off + sym_i * sym_entsize ..][0..24];
                const st_name: usize = std.mem.readInt(u32, entry[0..4], .little);
                const st_info = entry[4];
                const st_bind = st_info >> 4;
                const st_type = st_info & 0x0F;
                const st_shndx = std.mem.readInt(u16, entry[6..8], .little);
                if (st_shndx == 0) continue; // `SHN_UNDEF`.
                if (st_bind != 1 and st_bind != 2) continue; // `STB_GLOBAL` or `STB_WEAK`.
                if (st_type == 3 or st_type == 4) continue; // Skip `STT_SECTION` / `STT_FILE`.
                if (st_name >= strtab.len) continue;
                try appendOwnedSymbol(allocator, out_syms, std.mem.sliceTo(strtab[st_name..], 0));
            }
        }
    } else if (ei_class == 1 and obj_bytes.len >= 52) {
        const shoff: usize = std.mem.readInt(u32, obj_bytes[32..36], .little);
        const shentsize: usize = std.mem.readInt(u16, obj_bytes[46..48], .little);
        const shnum: usize = std.mem.readInt(u16, obj_bytes[48..50], .little);
        if (shoff == 0 or shentsize < 40 or shoff + shentsize * shnum > obj_bytes.len) return;

        var sec_i: usize = 0;
        while (sec_i < shnum) : (sec_i += 1) {
            const sh_base = shoff + sec_i * shentsize;
            const sh_type = std.mem.readInt(u32, obj_bytes[sh_base + 4 ..][0..4], .little);
            if (sh_type != 2) continue;

            const sym_off: usize = std.mem.readInt(u32, obj_bytes[sh_base + 16 ..][0..4], .little);
            const sym_size: usize = std.mem.readInt(u32, obj_bytes[sh_base + 20 ..][0..4], .little);
            const str_sec_idx: usize = std.mem.readInt(u32, obj_bytes[sh_base + 24 ..][0..4], .little);
            const first_global: usize = std.mem.readInt(u32, obj_bytes[sh_base + 28 ..][0..4], .little);
            if (str_sec_idx >= shnum or sym_off + sym_size > obj_bytes.len) continue;

            const str_sh = shoff + str_sec_idx * shentsize;
            const str_off: usize = std.mem.readInt(u32, obj_bytes[str_sh + 16 ..][0..4], .little);
            const str_size: usize = std.mem.readInt(u32, obj_bytes[str_sh + 20 ..][0..4], .little);
            if (str_off + str_size > obj_bytes.len) continue;
            const strtab = obj_bytes[str_off .. str_off + str_size];

            const sym_count = sym_size / 16;
            var sym_i: usize = @min(first_global, sym_count);
            while (sym_i < sym_count) : (sym_i += 1) {
                const entry = obj_bytes[sym_off + sym_i * 16 ..][0..16];
                const st_name: usize = std.mem.readInt(u32, entry[0..4], .little);
                const st_info = entry[12];
                const st_bind = st_info >> 4;
                const st_type = st_info & 0x0F;
                const st_shndx = std.mem.readInt(u16, entry[14..16], .little);
                if (st_shndx == 0 or (st_bind != 1 and st_bind != 2) or st_type == 3 or st_type == 4) continue;
                if (st_name >= strtab.len) continue;
                try appendOwnedSymbol(allocator, out_syms, std.mem.sliceTo(strtab[st_name..], 0));
            }
        }
    }
}

/// Extracts defined external symbols from a 64-bit Mach-O relocatable object (`0xFEEDFACF`).
fn extractMachODefinedSymbols(
    allocator: std.mem.Allocator,
    obj_bytes: []const u8,
    out_syms: *std.ArrayListUnmanaged([]u8),
) !void {
    if (obj_bytes.len < 32) return;
    const ncmds: usize = std.mem.readInt(u32, obj_bytes[16..20], .little);
    const sizeofcmds: usize = std.mem.readInt(u32, obj_bytes[20..24], .little);
    if (32 + sizeofcmds > obj_bytes.len) return;

    var cmd_off: usize = 32;
    var cmd_i: usize = 0;
    while (cmd_i < ncmds and cmd_off + 8 <= 32 + sizeofcmds) : (cmd_i += 1) {
        const cmd = std.mem.readInt(u32, obj_bytes[cmd_off..][0..4], .little);
        const cmdsize: usize = std.mem.readInt(u32, obj_bytes[cmd_off + 4 ..][0..4], .little);
        if (cmdsize < 8 or cmd_off + cmdsize > obj_bytes.len) break;

        if (cmd == 0x02 and cmdsize >= 24) { // `LC_SYMTAB`.
            const symoff: usize = std.mem.readInt(u32, obj_bytes[cmd_off + 8 ..][0..4], .little);
            const nsyms: usize = std.mem.readInt(u32, obj_bytes[cmd_off + 12 ..][0..4], .little);
            const stroff: usize = std.mem.readInt(u32, obj_bytes[cmd_off + 16 ..][0..4], .little);
            const strsize: usize = std.mem.readInt(u32, obj_bytes[cmd_off + 20 ..][0..4], .little);
            if (symoff + nsyms * 16 <= obj_bytes.len and stroff + strsize <= obj_bytes.len) {
                const strtab = obj_bytes[stroff .. stroff + strsize];
                var sym_i: usize = 0;
                while (sym_i < nsyms) : (sym_i += 1) {
                    const nl = obj_bytes[symoff + sym_i * 16 ..][0..16];
                    const n_strx: usize = std.mem.readInt(u32, nl[0..4], .little);
                    const n_type = nl[4];
                    const n_value = std.mem.readInt(u64, nl[8..16], .little);
                    if ((n_type & 0x01) == 0 or (n_type & 0xE0) != 0) continue; // Require `N_EXT`, no `N_STAB`.
                    const kind_bits = n_type & 0x0E;
                    if (kind_bits == 0x00 and n_value == 0) continue; // Undefined external (`N_UNDF` with `0` size).
                    if (n_strx >= strtab.len) continue;
                    try appendOwnedSymbol(allocator, out_syms, std.mem.sliceTo(strtab[n_strx..], 0));
                }
            }
        }
        cmd_off += cmdsize;
    }
}

/// Extracts defined external symbols from a PE/COFF relocatable `.obj` or 20-byte Short Import record.
fn extractCoffDefinedSymbols(
    allocator: std.mem.Allocator,
    obj_bytes: []const u8,
    out_syms: *std.ArrayListUnmanaged([]u8),
) !void {
    if (obj_bytes.len < 20) return;
    const sig1 = std.mem.readInt(u16, obj_bytes[0..2], .little);
    const sig2 = std.mem.readInt(u16, obj_bytes[2..4], .little);

    // [1] Handle 20-byte PE/COFF Short Import member:
    if (sig1 == 0x0000 and sig2 == 0xFFFF) {
        const size_of_data: usize = std.mem.readInt(u32, obj_bytes[12..16], .little);
        const type_info = std.mem.readInt(u16, obj_bytes[18..20], .little);
        if (20 + size_of_data > obj_bytes.len) return;
        const sym_name = std.mem.sliceTo(obj_bytes[20 .. 20 + size_of_data], 0);
        if (sym_name.len == 0) return;
        const imp_sym = try std.fmt.allocPrint(allocator, "__imp_{s}", .{sym_name});
        errdefer allocator.free(imp_sym);
        try out_syms.append(allocator, imp_sym);
        if ((type_info & 0x03) == COFF_IMPORT_CODE) {
            try appendOwnedSymbol(allocator, out_syms, sym_name);
        }
        return;
    }

    // [2] Handle standard COFF relocatable object (`IMAGE_FILE_HEADER` + symbol table):
    const symtab_off: usize = std.mem.readInt(u32, obj_bytes[8..12], .little);
    const num_syms: usize = std.mem.readInt(u32, obj_bytes[12..16], .little);
    if (symtab_off == 0 or num_syms == 0 or symtab_off + num_syms * 18 > obj_bytes.len) return;

    const strtab_off = symtab_off + num_syms * 18;
    const strtab: []const u8 = if (strtab_off + 4 <= obj_bytes.len) blk: {
        const strtab_sz: usize = std.mem.readInt(u32, obj_bytes[strtab_off..][0..4], .little);
        if (strtab_sz >= 4 and strtab_off + strtab_sz <= obj_bytes.len) {
            break :blk obj_bytes[strtab_off .. strtab_off + strtab_sz];
        }
        break :blk &.{};
    } else &.{};

    var sym_i: usize = 0;
    while (sym_i < num_syms) {
        const raw = obj_bytes[symtab_off + sym_i * 18 ..][0..18];
        const sym_val = std.mem.readInt(u32, raw[8..12], .little);
        const sec_num = std.mem.readInt(i16, raw[12..14], .little);
        const storage_class = raw[16];
        sym_i += 1 + @as(usize, raw[17]);

        if (storage_class != COFF_SYM_CLASS_EXTERNAL and storage_class != COFF_SYM_CLASS_WEAK_EXTERNAL) continue;
        if (sec_num == 0 and sym_val == 0) continue; // Undefined external reference.

        const first_dword = std.mem.readInt(u32, raw[0..4], .little);
        const sym_name: []const u8 = if (first_dword == 0) blk: {
            const name_off: usize = std.mem.readInt(u32, raw[4..8], .little);
            if (name_off < 4 or name_off >= strtab.len) continue;
            break :blk std.mem.sliceTo(strtab[name_off..], 0);
        } else std.mem.sliceTo(raw[0..8], 0);

        try appendOwnedSymbol(allocator, out_syms, sym_name);
    }
}

/// Extracts defined global symbols from a WebAssembly relocatable `.o` (`"linking"` custom section).
fn extractWasmDefinedSymbols(
    allocator: std.mem.Allocator,
    obj_bytes: []const u8,
    out_syms: *std.ArrayListUnmanaged([]u8),
) !void {
    if (obj_bytes.len < 8) return;
    var cursor: usize = 8;
    while (cursor < obj_bytes.len) {
        const sec_id = obj_bytes[cursor];
        cursor += 1;
        const sec_len: usize = @intCast(readUleb128(obj_bytes, &cursor) orelse return);
        if (cursor + sec_len > obj_bytes.len) return;
        const sec_end = cursor + sec_len;

        if (sec_id == 0) {
            var sub_cur = cursor;
            const name_len: usize = @intCast(readUleb128(obj_bytes, &sub_cur) orelse {
                cursor = sec_end;
                continue;
            });
            if (sub_cur + name_len <= sec_end and std.mem.eql(u8, obj_bytes[sub_cur .. sub_cur + name_len], "linking")) {
                sub_cur += name_len;
                _ = readUleb128(obj_bytes, &sub_cur) orelse {
                    cursor = sec_end;
                    continue;
                };
                while (sub_cur < sec_end) {
                    var sym_cur = sub_cur + 1;
                    const sub_len: usize = @intCast(readUleb128(obj_bytes, &sym_cur) orelse break);
                    if (sym_cur + sub_len > sec_end) break;
                    const sub_end = sym_cur + sub_len;

                    if (obj_bytes[sub_cur] == 8) { // `WASM_SYMBOL_TABLE`.
                        var rem_syms = readUleb128(obj_bytes, &sym_cur) orelse break;
                        while (rem_syms > 0 and sym_cur < sub_end) : (rem_syms -= 1) {
                            const sym_kind = obj_bytes[sym_cur];
                            sym_cur += 1;
                            const sym_flags = readUleb128(obj_bytes, &sym_cur) orelse break;
                            const is_undefined = (sym_flags & 0x10) != 0;

                            var parsed_name: []const u8 = "";
                            switch (sym_kind) {
                                0, 2, 4, 5 => { // Function, Global, Event, Table.
                                    _ = readUleb128(obj_bytes, &sym_cur) orelse break;
                                    if (!is_undefined or (sym_flags & 0x40) != 0) {
                                        const nl_usz: usize = @intCast(readUleb128(obj_bytes, &sym_cur) orelse break);
                                        if (sym_cur + nl_usz > sub_end) break;
                                        parsed_name = obj_bytes[sym_cur .. sym_cur + nl_usz];
                                        sym_cur += nl_usz;
                                    }
                                },
                                1 => { // Data symbol.
                                    const nl_usz: usize = @intCast(readUleb128(obj_bytes, &sym_cur) orelse break);
                                    if (sym_cur + nl_usz > sub_end) break;
                                    parsed_name = obj_bytes[sym_cur .. sym_cur + nl_usz];
                                    sym_cur += nl_usz;
                                    if (!is_undefined) {
                                        _ = readUleb128(obj_bytes, &sym_cur) orelse break;
                                        _ = readUleb128(obj_bytes, &sym_cur) orelse break;
                                        _ = readUleb128(obj_bytes, &sym_cur) orelse break;
                                    }
                                },
                                3 => { // Section symbol.
                                    _ = readUleb128(obj_bytes, &sym_cur) orelse break;
                                },
                                else => break,
                            }
                            if (!is_undefined and (sym_flags & 0x02) == 0 and sym_kind != 3 and parsed_name.len > 0) {
                                try appendOwnedSymbol(allocator, out_syms, parsed_name);
                            }
                        }
                    }
                    sub_cur = sub_end;
                }
            }
        } else if (sec_id == 7) { // Fallback: standard Wasm `Export` section.
            var exp_cur = cursor;
            var rem_exports = readUleb128(obj_bytes, &exp_cur) orelse {
                cursor = sec_end;
                continue;
            };
            while (rem_exports > 0 and exp_cur < sec_end) : (rem_exports -= 1) {
                const nl_usz: usize = @intCast(readUleb128(obj_bytes, &exp_cur) orelse break);
                if (exp_cur + nl_usz + 1 > sec_end) break;
                const exp_name = obj_bytes[exp_cur .. exp_cur + nl_usz];
                exp_cur += nl_usz;
                var next_cur = exp_cur + 1;
                if (!skipLeb128(obj_bytes, &next_cur)) break;
                if (obj_bytes[exp_cur] == 0 and !std.mem.eql(u8, exp_name, "memory")) {
                    try appendOwnedSymbol(allocator, out_syms, exp_name);
                }
                exp_cur = next_cur;
            }
        }
        cursor = sec_end;
    }
}

/// Dispatches object-format detection and returns owned defined symbol strings for `obj_bytes`.
fn extractDefinedSymbolsFromObject(
    allocator: std.mem.Allocator,
    obj_bytes: []const u8,
) ![][]u8 {
    var syms: std.ArrayListUnmanaged([]u8) = .empty;
    errdefer {
        for (syms.items) |owned| allocator.free(owned);
        syms.deinit(allocator);
    }

    if (obj_bytes.len >= 4 and std.mem.eql(u8, obj_bytes[0..4], "\x7FELF")) {
        try extractElfDefinedSymbols(allocator, obj_bytes, &syms);
    } else if (obj_bytes.len >= 4 and std.mem.readInt(u32, obj_bytes[0..4], .little) == 0xFEED_FACF) {
        try extractMachODefinedSymbols(allocator, obj_bytes, &syms);
    } else if (obj_bytes.len >= 8 and std.mem.eql(u8, obj_bytes[0..8], "\x00asm\x01\x00\x00\x00")) {
        try extractWasmDefinedSymbols(allocator, obj_bytes, &syms);
    } else if (obj_bytes.len >= 20) {
        const first_u16 = std.mem.readInt(u16, obj_bytes[0..2], .little);
        if ((first_u16 == 0x0000 and std.mem.readInt(u16, obj_bytes[2..4], .little) == 0xFFFF) or
            first_u16 == 0x8664 or first_u16 == 0xAA64 or first_u16 == 0x014C)
        {
            try extractCoffDefinedSymbols(allocator, obj_bytes, &syms);
        }
    }
    return syms.toOwnedSlice(allocator);
}

// --------------- Deterministic Archive Writers ----------------

/// Formats a fixed-width space-padded ASCII `ar` header (`mtime = 0`, `uid = 0`, `gid = 0`).
fn appendFixedArHeader(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    name_field: []const u8,
    mode_octal: []const u8,
    body_size: usize,
) !void {
    var hdr: [AR_HEADER_BYTES]u8 = @splat(' ');
    const clamped_name = name_field[0..@min(name_field.len, 16)];
    @memcpy(hdr[0..clamped_name.len], clamped_name);
    hdr[16] = '0'; // `mtime = 0`.
    hdr[28] = '0'; // `uid = 0`.
    hdr[34] = '0'; // `gid = 0`.
    const clamped_mode = mode_octal[0..@min(mode_octal.len, 8)];
    @memcpy(hdr[40 .. 40 + clamped_mode.len], clamped_mode);

    var size_buf: [16]u8 = undefined;
    const size_str = std.fmt.bufPrint(&size_buf, "{d}", .{body_size}) catch unreachable;
    const clamped_sz_len: usize = @min(size_str.len, 10);
    @memcpy(hdr[48 .. 48 + clamped_sz_len], size_str[0..clamped_sz_len]);
    hdr[58] = '`';
    hdr[59] = '\n';
    try out.appendSlice(allocator, &hdr);
}

/// Serializes a deterministic `K_GNU` or `K_COFF` `!<arch>\n` archive into an owned byte slice.
fn serializeGnuOrCoffArchive(
    allocator: std.mem.Allocator,
    is_coff: bool,
    members: []const ArchiveMemberInput,
    member_symbols: []const []const []const u8,
) LinkError![]u8 {
    if (is_coff and members.len >= std.math.maxInt(u16)) return error.ArchiveWriteFailed;
    if (members.len > std.math.maxInt(u32)) return error.ArchiveWriteFailed;

    // [1] Build optional `//` longnames table for member basenames exceeding 15 bytes:
    var longnames_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer longnames_buf.deinit(allocator);
    const member_name_fields = allocator.alloc([16]u8, members.len) catch return error.OutOfMemory;
    defer allocator.free(member_name_fields);

    for (members, 0..) |mem_in, i| {
        const base = std.fs.path.basename(mem_in.name);
        member_name_fields[i] = @splat(' ');
        if (base.len <= 15) {
            @memcpy(member_name_fields[i][0..base.len], base);
            member_name_fields[i][base.len] = '/';
        } else {
            var off_str_buf: [15]u8 = undefined;
            const off_str = std.fmt.bufPrint(&off_str_buf, "/{d}", .{longnames_buf.items.len}) catch
                return error.ArchiveWriteFailed;
            @memcpy(member_name_fields[i][0..off_str.len], off_str);
            longnames_buf.appendSlice(allocator, base) catch return error.OutOfMemory;
            if (is_coff) {
                longnames_buf.append(allocator, 0) catch return error.OutOfMemory;
            } else {
                longnames_buf.appendSlice(allocator, "/\n") catch return error.OutOfMemory;
            }
        }
    }

    // [2] Flatten `(symbol, member_index)` pairs in member order and compute sorted view for `K_COFF`:
    var all_syms: std.ArrayListUnmanaged(IndexedArchiveSymbol) = .empty;
    defer all_syms.deinit(allocator);
    var sym_strings_bytes: usize = 0;
    for (member_symbols, 0..) |syms_for_mem, mem_i| {
        for (syms_for_mem) |sym_s| {
            all_syms.append(allocator, .{ .name = sym_s, .member_index = @intCast(mem_i) }) catch return error.OutOfMemory;
            sym_strings_bytes = std.math.add(usize, sym_strings_bytes, sym_s.len + 1) catch return error.ArchiveWriteFailed;
        }
    }
    if (all_syms.items.len > std.math.maxInt(u32)) return error.ArchiveWriteFailed;

    const has_symtab = is_coff or all_syms.items.len > 0;
    const first_linker_body_len: usize = if (has_symtab)
        4 + all_syms.items.len * 4 + sym_strings_bytes
    else
        0;
    const second_linker_body_len: usize = if (is_coff)
        4 + members.len * 4 + 4 + all_syms.items.len * 2 + sym_strings_bytes
    else
        0;

    // [3] Compute exact file byte offsets of every regular archive member:
    var cursor: usize = ARCHIVE_MAGIC.len;
    if (has_symtab) {
        cursor = std.math.add(usize, cursor, AR_HEADER_BYTES + alignUpUsize(first_linker_body_len, 2)) catch
            return error.ArchiveWriteFailed;
    }
    if (is_coff) {
        cursor = std.math.add(usize, cursor, AR_HEADER_BYTES + alignUpUsize(second_linker_body_len, 2)) catch
            return error.ArchiveWriteFailed;
    }
    if (longnames_buf.items.len > 0) {
        cursor = std.math.add(usize, cursor, AR_HEADER_BYTES + alignUpUsize(longnames_buf.items.len, 2)) catch
            return error.ArchiveWriteFailed;
    }

    const member_offsets = allocator.alloc(u32, members.len) catch return error.OutOfMemory;
    defer allocator.free(member_offsets);
    for (members, 0..) |mem_in, i| {
        if (cursor > std.math.maxInt(u32)) return error.ArchiveWriteFailed;
        member_offsets[i] = @intCast(cursor);
        if (mem_in.data.len > std.math.maxInt(u32)) return error.ArchiveWriteFailed;
        cursor = std.math.add(usize, cursor, AR_HEADER_BYTES + alignUpUsize(mem_in.data.len, 2)) catch
            return error.ArchiveWriteFailed;
        if (cursor > std.math.maxInt(u32)) return error.ArchiveWriteFailed;
    }

    // [4] Emit `!<arch>\n` + 1st Linker Member + optional 2nd Linker Member + `//` + regular members:
    var out: std.ArrayListUnmanaged(u8) = .empty;
    errdefer out.deinit(allocator);
    out.ensureTotalCapacity(allocator, cursor) catch return error.OutOfMemory;
    out.appendSlice(allocator, ARCHIVE_MAGIC) catch return error.OutOfMemory;

    if (has_symtab) {
        appendFixedArHeader(allocator, &out, "/", "0", first_linker_body_len) catch return error.OutOfMemory;
        var be_buf: [4]u8 = undefined;
        std.mem.writeInt(u32, &be_buf, @intCast(all_syms.items.len), .big);
        out.appendSlice(allocator, &be_buf) catch return error.OutOfMemory;
        for (all_syms.items) |sym_entry| {
            std.mem.writeInt(u32, &be_buf, member_offsets[sym_entry.member_index], .big);
            out.appendSlice(allocator, &be_buf) catch return error.OutOfMemory;
        }
        for (all_syms.items) |sym_entry| {
            out.appendSlice(allocator, sym_entry.name) catch return error.OutOfMemory;
            out.append(allocator, 0) catch return error.OutOfMemory;
        }
        if ((first_linker_body_len & 1) != 0) out.append(allocator, '\n') catch return error.OutOfMemory;
    }

    if (is_coff) {
        const sorted_syms = allocator.dupe(IndexedArchiveSymbol, all_syms.items) catch return error.OutOfMemory;
        defer allocator.free(sorted_syms);
        std.mem.sort(IndexedArchiveSymbol, sorted_syms, {}, struct {
            /// Orders COFF 2nd Linker Member symbols lexicographically (`strcmp` unsigned byte order).
            fn lessThan(_: void, lhs: IndexedArchiveSymbol, rhs: IndexedArchiveSymbol) bool {
                const cmp = std.mem.order(u8, lhs.name, rhs.name);
                if (cmp != .eq) return cmp == .lt;
                return lhs.member_index < rhs.member_index;
            }
        }.lessThan);

        appendFixedArHeader(allocator, &out, "/", "0", second_linker_body_len) catch return error.OutOfMemory;
        var le32_buf: [4]u8 = undefined;
        std.mem.writeInt(u32, &le32_buf, @intCast(members.len), .little);
        out.appendSlice(allocator, &le32_buf) catch return error.OutOfMemory;
        for (member_offsets) |off_val| {
            std.mem.writeInt(u32, &le32_buf, off_val, .little);
            out.appendSlice(allocator, &le32_buf) catch return error.OutOfMemory;
        }
        std.mem.writeInt(u32, &le32_buf, @intCast(sorted_syms.len), .little);
        out.appendSlice(allocator, &le32_buf) catch return error.OutOfMemory;
        var le16_buf: [2]u8 = undefined;
        for (sorted_syms) |sym_entry| {
            std.mem.writeInt(u16, &le16_buf, @intCast(sym_entry.member_index + 1), .little);
            out.appendSlice(allocator, &le16_buf) catch return error.OutOfMemory;
        }
        for (sorted_syms) |sym_entry| {
            out.appendSlice(allocator, sym_entry.name) catch return error.OutOfMemory;
            out.append(allocator, 0) catch return error.OutOfMemory;
        }
        if ((second_linker_body_len & 1) != 0) out.append(allocator, '\n') catch return error.OutOfMemory;
    }

    if (longnames_buf.items.len > 0) {
        appendFixedArHeader(allocator, &out, "//", "0", longnames_buf.items.len) catch return error.OutOfMemory;
        out.appendSlice(allocator, longnames_buf.items) catch return error.OutOfMemory;
        if ((longnames_buf.items.len & 1) != 0) out.append(allocator, '\n') catch return error.OutOfMemory;
    }

    for (members, 0..) |mem_in, i| {
        appendFixedArHeader(allocator, &out, &member_name_fields[i], "100644", mem_in.data.len) catch return error.OutOfMemory;
        out.appendSlice(allocator, mem_in.data) catch return error.OutOfMemory;
        if ((mem_in.data.len & 1) != 0) out.append(allocator, '\n') catch return error.OutOfMemory;
    }

    return out.toOwnedSlice(allocator) catch return error.OutOfMemory;
}

/// Serializes a deterministic BSD / Apple Darwin (`K_BSD`) `!<arch>\n` archive with 8-byte aligned payloads.
fn serializeDarwinBsdArchive(
    allocator: std.mem.Allocator,
    members: []const ArchiveMemberInput,
    member_symbols: []const []const []const u8,
) LinkError![]u8 {
    if (members.len > std.math.maxInt(u32)) return error.ArchiveWriteFailed;

    // [1] Sort symbols lexicographically for `__.SYMDEF SORTED`:
    var sorted_syms: std.ArrayListUnmanaged(IndexedArchiveSymbol) = .empty;
    defer sorted_syms.deinit(allocator);
    for (member_symbols, 0..) |syms_for_mem, mem_i| {
        for (syms_for_mem) |sym_s| {
            sorted_syms.append(allocator, .{ .name = sym_s, .member_index = @intCast(mem_i) }) catch return error.OutOfMemory;
        }
    }
    std.mem.sort(IndexedArchiveSymbol, sorted_syms.items, {}, struct {
        /// Orders BSD `ranlib` directory symbols lexicographically.
        fn lessThan(_: void, lhs: IndexedArchiveSymbol, rhs: IndexedArchiveSymbol) bool {
            const cmp = std.mem.order(u8, lhs.name, rhs.name);
            if (cmp != .eq) return cmp == .lt;
            return lhs.member_index < rhs.member_index;
        }
    }.lessThan);

    var sym_strtab: std.ArrayListUnmanaged(u8) = .empty;
    defer sym_strtab.deinit(allocator);
    const sym_strx = allocator.alloc(u32, sorted_syms.items.len) catch return error.OutOfMemory;
    defer allocator.free(sym_strx);
    for (sorted_syms.items, 0..) |sym_entry, i| {
        if (sym_strtab.items.len > std.math.maxInt(u32)) return error.ArchiveWriteFailed;
        sym_strx[i] = @intCast(sym_strtab.items.len);
        sym_strtab.appendSlice(allocator, sym_entry.name) catch return error.OutOfMemory;
        sym_strtab.append(allocator, 0) catch return error.OutOfMemory;
    }
    while ((sym_strtab.items.len & 7) != 0) {
        sym_strtab.append(allocator, 0) catch return error.OutOfMemory;
    }

    // `"__.SYMDEF SORTED"` (16B) + 4 NUL pad bytes => `AR_HEADER_BYTES (60) + 20 = 80` (multiple of 8):
    const symdef_ext_name = "__.SYMDEF SORTED\x00\x00\x00\x00";
    const ranlib_bytes: usize = std.math.mul(usize, sorted_syms.items.len, 8) catch return error.ArchiveWriteFailed;
    if (ranlib_bytes > std.math.maxInt(u32) or sym_strtab.items.len > std.math.maxInt(u32)) {
        return error.ArchiveWriteFailed;
    }
    const symdef_body_len: usize = symdef_ext_name.len + 4 + ranlib_bytes + 4 + sym_strtab.items.len;

    // [2] Compute 2-byte aligned `ar_hdr` offsets and 8-byte aligned Mach-O payload offsets:
    var cursor: usize = ARCHIVE_MAGIC.len + AR_HEADER_BYTES + symdef_body_len;
    const member_offsets = allocator.alloc(u32, members.len) catch return error.OutOfMemory;
    defer allocator.free(member_offsets);
    const ext_name_lens = allocator.alloc(usize, members.len) catch return error.OutOfMemory;
    defer allocator.free(ext_name_lens);

    for (members, 0..) |mem_in, i| {
        if ((cursor & 1) != 0) cursor += 1;
        if (cursor > std.math.maxInt(u32)) return error.ArchiveWriteFailed;
        member_offsets[i] = @intCast(cursor);
        const base = std.fs.path.basename(mem_in.name);
        const rem = (cursor + AR_HEADER_BYTES + base.len) & 7;
        const pad_name: usize = if (rem == 0) 0 else (8 - rem);
        const ext_len = base.len + pad_name;
        ext_name_lens[i] = ext_len;
        if (mem_in.data.len > std.math.maxInt(u32)) return error.ArchiveWriteFailed;
        const unpadded_body = std.math.add(usize, ext_len, mem_in.data.len) catch return error.ArchiveWriteFailed;
        const step_bytes = std.math.add(usize, AR_HEADER_BYTES + unpadded_body, unpadded_body & 1) catch
            return error.ArchiveWriteFailed;
        cursor = std.math.add(usize, cursor, step_bytes) catch return error.ArchiveWriteFailed;
        if (cursor > std.math.maxInt(u32)) return error.ArchiveWriteFailed;
    }

    // [3] Emit `!<arch>\n` + `__.SYMDEF SORTED` + 8-byte aligned BSD members (exact unpadded `ar_size`):
    var out: std.ArrayListUnmanaged(u8) = .empty;
    errdefer out.deinit(allocator);
    out.ensureTotalCapacity(allocator, cursor) catch return error.OutOfMemory;
    out.appendSlice(allocator, ARCHIVE_MAGIC) catch return error.OutOfMemory;

    var symdef_hdr_name: [16]u8 = @splat(' ');
    const symdef_tag = std.fmt.bufPrint(&symdef_hdr_name, "#1/{d}", .{symdef_ext_name.len}) catch unreachable;
    for (symdef_hdr_name[symdef_tag.len..]) |*ch| ch.* = ' ';
    appendFixedArHeader(allocator, &out, &symdef_hdr_name, "100644", symdef_body_len) catch return error.OutOfMemory;
    out.appendSlice(allocator, symdef_ext_name) catch return error.OutOfMemory;

    var le32_buf: [4]u8 = undefined;
    std.mem.writeInt(u32, &le32_buf, @intCast(ranlib_bytes), .little);
    out.appendSlice(allocator, &le32_buf) catch return error.OutOfMemory;
    for (sorted_syms.items, 0..) |sym_entry, i| {
        std.mem.writeInt(u32, &le32_buf, sym_strx[i], .little);
        out.appendSlice(allocator, &le32_buf) catch return error.OutOfMemory;
        std.mem.writeInt(u32, &le32_buf, member_offsets[sym_entry.member_index], .little);
        out.appendSlice(allocator, &le32_buf) catch return error.OutOfMemory;
    }
    std.mem.writeInt(u32, &le32_buf, @intCast(sym_strtab.items.len), .little);
    out.appendSlice(allocator, &le32_buf) catch return error.OutOfMemory;
    out.appendSlice(allocator, sym_strtab.items) catch return error.OutOfMemory;

    for (members, 0..) |mem_in, i| {
        if ((out.items.len & 1) != 0) out.append(allocator, '\n') catch return error.OutOfMemory;
        std.debug.assert(out.items.len == member_offsets[i]);
        const base = std.fs.path.basename(mem_in.name);
        const ext_len = ext_name_lens[i];
        const unpadded_body = ext_len + mem_in.data.len;

        var hdr_name: [16]u8 = @splat(' ');
        const tag = std.fmt.bufPrint(&hdr_name, "#1/{d}", .{ext_len}) catch return error.ArchiveWriteFailed;
        for (hdr_name[tag.len..]) |*ch| ch.* = ' ';
        appendFixedArHeader(allocator, &out, &hdr_name, "100644", unpadded_body) catch return error.OutOfMemory;
        out.appendSlice(allocator, base) catch return error.OutOfMemory;
        out.appendNTimes(allocator, 0, ext_len - base.len) catch return error.OutOfMemory;
        std.debug.assert((out.items.len & 7) == 0);
        out.appendSlice(allocator, mem_in.data) catch return error.OutOfMemory;
        if ((unpadded_body & 1) == 1) out.append(allocator, '\n') catch return error.OutOfMemory;
    }

    return out.toOwnedSlice(allocator) catch return error.OutOfMemory;
}

// ------------- COFF Short-Import Object Builders --------------

/// Appends a 20-byte COFF `IMAGE_FILE_HEADER` to `buf`.
fn appendCoffFileHeader(
    allocator: std.mem.Allocator,
    buf: *std.ArrayListUnmanaged(u8),
    machine: CoffMachine,
    num_sections: u16,
    symtab_ptr: u32,
    num_symbols: u32,
) !void {
    var hdr: [20]u8 = @splat(0);
    std.mem.writeInt(u16, hdr[0..2], @backingInt(machine), .little);
    std.mem.writeInt(u16, hdr[2..4], num_sections, .little);
    std.mem.writeInt(u32, hdr[4..8], 0, .little); // `TimeDateStamp = 0`.
    std.mem.writeInt(u32, hdr[8..12], symtab_ptr, .little);
    std.mem.writeInt(u32, hdr[12..16], num_symbols, .little);
    std.mem.writeInt(u16, hdr[16..18], 0, .little);
    std.mem.writeInt(u16, hdr[18..20], 0, .little);
    try buf.appendSlice(allocator, &hdr);
}

/// Appends a 40-byte COFF `IMAGE_SECTION_HEADER` to `buf`.
fn appendCoffSectionHeader(
    allocator: std.mem.Allocator,
    buf: *std.ArrayListUnmanaged(u8),
    sec_name: []const u8,
    raw_size: u32,
    raw_ptr: u32,
    reloc_ptr: u32,
    num_relocs: u16,
    characteristics: u32,
) !void {
    var shdr: [40]u8 = @splat(0);
    @memcpy(shdr[0..@min(sec_name.len, 8)], sec_name[0..@min(sec_name.len, 8)]);
    std.mem.writeInt(u32, shdr[16..20], raw_size, .little);
    std.mem.writeInt(u32, shdr[20..24], raw_ptr, .little);
    std.mem.writeInt(u32, shdr[24..28], reloc_ptr, .little);
    std.mem.writeInt(u16, shdr[32..34], num_relocs, .little);
    std.mem.writeInt(u32, shdr[36..40], characteristics, .little);
    try buf.appendSlice(allocator, &shdr);
}

/// Appends a 10-byte COFF relocation entry to `buf`.
fn appendCoffRelocation(
    allocator: std.mem.Allocator,
    buf: *std.ArrayListUnmanaged(u8),
    vaddr: u32,
    sym_idx: u32,
    rel_type: u16,
) !void {
    var rel: [10]u8 = @splat(0);
    std.mem.writeInt(u32, rel[0..4], vaddr, .little);
    std.mem.writeInt(u32, rel[4..8], sym_idx, .little);
    std.mem.writeInt(u16, rel[8..10], rel_type, .little);
    try buf.appendSlice(allocator, &rel);
}

/// Appends an 18-byte COFF `IMAGE_SYMBOL` (adding names `> 8` bytes into `strtab`) to `buf`.
fn appendCoffSymbol(
    allocator: std.mem.Allocator,
    buf: *std.ArrayListUnmanaged(u8),
    strtab: *std.ArrayListUnmanaged(u8),
    sym_name: []const u8,
    sym_value: u32,
    section_number: i16,
    storage_class: u8,
) !void {
    var sym: [18]u8 = @splat(0);
    if (sym_name.len <= 8) {
        @memcpy(sym[0..sym_name.len], sym_name);
    } else {
        const str_off: u32 = @intCast(strtab.items.len);
        std.mem.writeInt(u32, sym[0..4], 0, .little);
        std.mem.writeInt(u32, sym[4..8], str_off, .little);
        try strtab.appendSlice(allocator, sym_name);
        try strtab.append(allocator, 0);
    }
    std.mem.writeInt(u32, sym[8..12], sym_value, .little);
    std.mem.writeInt(i16, sym[12..14], section_number, .little);
    sym[16] = storage_class;
    try buf.appendSlice(allocator, &sym);
}

/// Synthesizes Member 0 (`__IMPORT_DESCRIPTOR_<DLL_STEM>`) COFF object (`DR-10` §1.2.3).
fn buildCoffImportDescriptorObject(
    allocator: std.mem.Allocator,
    dll_name: []const u8,
    imp_desc_sym: []const u8,
    null_thunk_sym: []const u8,
    machine: CoffMachine,
) ![]u8 {
    var buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer buf.deinit(allocator);
    var strtab: std.ArrayListUnmanaged(u8) = .empty;
    defer strtab.deinit(allocator);
    try strtab.appendNTimes(allocator, 0, 4); // Reserve 4-byte `strtab` byte size header.

    const dll_raw_len: u32 = @intCast(dll_name.len + 1);
    const idata2_ptr: u32 = 20 + 2 * 40; // `100`.
    const reloc_ptr: u32 = idata2_ptr + 20; // `120`.
    const idata6_ptr: u32 = reloc_ptr + 3 * 10; // `150`.

    try appendCoffFileHeader(allocator, &buf, machine, 2, idata6_ptr + dll_raw_len, 7);
    try appendCoffSectionHeader(allocator, &buf, ".idata$2", 20, idata2_ptr, reloc_ptr, 3, COFF_SCN_IDATA_4B_RW);
    try appendCoffSectionHeader(allocator, &buf, ".idata$6", dll_raw_len, idata6_ptr, 0, 0, COFF_SCN_IDATA_2B_RW);

    try buf.appendNTimes(allocator, 0, 20); // `IMAGE_IMPORT_DESCRIPTOR` zeroed template.
    const rva_rel = machine.addr32NbRelocType();
    try appendCoffRelocation(allocator, &buf, 12, 2, rva_rel); // `Name` -> `.idata$6` (`sym 2`).
    try appendCoffRelocation(allocator, &buf, 0, 3, rva_rel); // `OriginalFirstThunk` -> `.idata$4` (`sym 3`).
    try appendCoffRelocation(allocator, &buf, 16, 4, rva_rel); // `FirstThunk` -> `.idata$5` (`sym 4`).

    try buf.appendSlice(allocator, dll_name);
    try buf.append(allocator, 0);

    try appendCoffSymbol(allocator, &buf, &strtab, imp_desc_sym, 0, 1, COFF_SYM_CLASS_EXTERNAL);
    try appendCoffSymbol(allocator, &buf, &strtab, ".idata$2", 0, 1, COFF_SYM_CLASS_SECTION);
    try appendCoffSymbol(allocator, &buf, &strtab, ".idata$6", 0, 2, COFF_SYM_CLASS_STATIC);
    try appendCoffSymbol(allocator, &buf, &strtab, ".idata$4", 0, 0, COFF_SYM_CLASS_SECTION);
    try appendCoffSymbol(allocator, &buf, &strtab, ".idata$5", 0, 0, COFF_SYM_CLASS_SECTION);
    try appendCoffSymbol(allocator, &buf, &strtab, "__NULL_IMPORT_DESCRIPTOR", 0, 0, COFF_SYM_CLASS_EXTERNAL);
    try appendCoffSymbol(allocator, &buf, &strtab, null_thunk_sym, 0, 0, COFF_SYM_CLASS_EXTERNAL);

    std.mem.writeInt(u32, strtab.items[0..4], @intCast(strtab.items.len), .little);
    try buf.appendSlice(allocator, strtab.items);
    return buf.toOwnedSlice(allocator);
}

/// Synthesizes Member 1 (`__NULL_IMPORT_DESCRIPTOR`) COFF object (`DR-10` §1.2.3).
fn buildCoffNullImportDescriptorObject(allocator: std.mem.Allocator, machine: CoffMachine) ![]u8 {
    var buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer buf.deinit(allocator);
    var strtab: std.ArrayListUnmanaged(u8) = .empty;
    defer strtab.deinit(allocator);
    try strtab.appendNTimes(allocator, 0, 4);

    try appendCoffFileHeader(allocator, &buf, machine, 1, 80, 1);
    try appendCoffSectionHeader(allocator, &buf, ".idata$3", 20, 60, 0, 0, COFF_SCN_IDATA_4B_RW);
    try buf.appendNTimes(allocator, 0, 20);
    try appendCoffSymbol(allocator, &buf, &strtab, "__NULL_IMPORT_DESCRIPTOR", 0, 1, COFF_SYM_CLASS_EXTERNAL);

    std.mem.writeInt(u32, strtab.items[0..4], @intCast(strtab.items.len), .little);
    try buf.appendSlice(allocator, strtab.items);
    return buf.toOwnedSlice(allocator);
}

/// Synthesizes Member 2 (`\x7f<DLL_STEM>_NULL_THUNK_DATA`) COFF object (`DR-10` §1.2.3).
fn buildCoffNullThunkObject(
    allocator: std.mem.Allocator,
    null_thunk_sym: []const u8,
    machine: CoffMachine,
) ![]u8 {
    var buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer buf.deinit(allocator);
    var strtab: std.ArrayListUnmanaged(u8) = .empty;
    defer strtab.deinit(allocator);
    try strtab.appendNTimes(allocator, 0, 4);

    try appendCoffFileHeader(allocator, &buf, machine, 2, 116, 1);
    try appendCoffSectionHeader(allocator, &buf, ".idata$5", 8, 100, 0, 0, COFF_SCN_IDATA_8B_RW);
    try appendCoffSectionHeader(allocator, &buf, ".idata$4", 8, 108, 0, 0, COFF_SCN_IDATA_8B_RW);
    try buf.appendNTimes(allocator, 0, 16);
    try appendCoffSymbol(allocator, &buf, &strtab, null_thunk_sym, 0, 1, COFF_SYM_CLASS_EXTERNAL);

    std.mem.writeInt(u32, strtab.items[0..4], @intCast(strtab.items.len), .little);
    try buf.appendSlice(allocator, strtab.items);
    return buf.toOwnedSlice(allocator);
}

/// Synthesizes a 20-byte `CoffShortImportHeader` + `<SymbolName>\0<DllName>\0` member (`DR-10` §3.3).
fn buildCoffShortImportMember(
    allocator: std.mem.Allocator,
    dll_name: []const u8,
    exp_item: ModuleDefExport,
    machine: CoffMachine,
) LinkError![]u8 {
    const import_type: u16 = if (exp_item.is_constant)
        COFF_IMPORT_CONST
    else if (exp_item.is_data)
        COFF_IMPORT_DATA
    else
        COFF_IMPORT_CODE;

    const has_export_alias = if (exp_item.ext_name) |ext_s|
        !std.mem.eql(u8, ext_s, exp_item.sym_name)
    else
        false;

    const name_type: u16 = if (exp_item.is_noname and exp_item.ordinal != null)
        COFF_IMPORT_NAME_ORDINAL
    else if (has_export_alias)
        COFF_IMPORT_NAME_EXPORTAS
    else
        COFF_IMPORT_NAME_EXACT;

    const has_export_as_str = (name_type == COFF_IMPORT_NAME_EXPORTAS);
    const alias_extra_len: usize = if (has_export_as_str) exp_item.ext_name.?.len + 1 else 0;
    const payload_len: usize = exp_item.sym_name.len + 1 + dll_name.len + 1 + alias_extra_len;
    if (payload_len > std.math.maxInt(u32)) return error.ArchiveWriteFailed;

    const hdr: CoffShortImportHeader = .{
        .machine = @backingInt(machine),
        .size_of_data = @intCast(payload_len),
        .ordinal_or_hint = exp_item.ordinal orelse 0,
        .type_info = import_type | (name_type << 2),
    };

    var buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer buf.deinit(allocator);
    buf.ensureTotalCapacity(allocator, @sizeOf(CoffShortImportHeader) + payload_len) catch return error.OutOfMemory;

    var hdr_bytes: [20]u8 = undefined;
    std.mem.writeInt(u16, hdr_bytes[0..2], hdr.sig1, .little);
    std.mem.writeInt(u16, hdr_bytes[2..4], hdr.sig2, .little);
    std.mem.writeInt(u16, hdr_bytes[4..6], hdr.version, .little);
    std.mem.writeInt(u16, hdr_bytes[6..8], hdr.machine, .little);
    std.mem.writeInt(u32, hdr_bytes[8..12], hdr.time_date_stamp, .little);
    std.mem.writeInt(u32, hdr_bytes[12..16], hdr.size_of_data, .little);
    std.mem.writeInt(u16, hdr_bytes[16..18], hdr.ordinal_or_hint, .little);
    std.mem.writeInt(u16, hdr_bytes[18..20], hdr.type_info, .little);
    buf.appendSlice(allocator, &hdr_bytes) catch return error.OutOfMemory;

    buf.appendSlice(allocator, exp_item.sym_name) catch return error.OutOfMemory;
    buf.append(allocator, 0) catch return error.OutOfMemory;
    buf.appendSlice(allocator, dll_name) catch return error.OutOfMemory;
    buf.append(allocator, 0) catch return error.OutOfMemory;
    if (has_export_as_str) {
        buf.appendSlice(allocator, exp_item.ext_name.?) catch return error.OutOfMemory;
        buf.append(allocator, 0) catch return error.OutOfMemory;
    }
    return buf.toOwnedSlice(allocator) catch return error.OutOfMemory;
}

/// Extracts the next whitespace-delimited, `"…"` quoted, `=`, or `==` token from `line[*pos_ptr..]`.
fn extractNextDefToken(line: []const u8, pos_ptr: *usize) ?[]const u8 {
    var idx = pos_ptr.*;
    while (idx < line.len and (line[idx] == ' ' or line[idx] == '\t')) : (idx += 1) {}
    if (idx >= line.len) {
        pos_ptr.* = idx;
        return null;
    }
    if (line[idx] == '=') {
        const eq_len: usize = if (idx + 1 < line.len and line[idx + 1] == '=') 2 else 1;
        pos_ptr.* = idx + eq_len;
        return line[idx .. idx + eq_len];
    }
    if (line[idx] == '"') {
        const start = idx + 1;
        idx += 1;
        while (idx < line.len and line[idx] != '"') : (idx += 1) {}
        pos_ptr.* = if (idx < line.len) idx + 1 else idx;
        return line[start..idx];
    }
    const start = idx;
    while (idx < line.len and line[idx] != ' ' and line[idx] != '\t' and line[idx] != '=') : (idx += 1) {}
    pos_ptr.* = idx;
    return line[start..idx];
}

/// Lowercases `raw_tok` into `lower_buf` when `raw_tok.len <= lower_buf.len`, or returns `null`.
inline fn toLowerBounded(lower_buf: *[32]u8, raw_tok: []const u8) ?[]const u8 {
    if (raw_tok.len > lower_buf.len) return null;
    for (raw_tok, 0..) |byte_val, i| lower_buf[i] = std.ascii.toLower(byte_val);
    return lower_buf[0..raw_tok.len];
}

/// Returns `true` when `lib_arg` denotes a direct filesystem path or archive/object filename rather than `-l<stem>`.
fn isDirectLibraryPathArg(lib_arg: []const u8) bool {
    if (std.mem.indexOfAny(u8, lib_arg, "/\\") != null) return true;
    const raw_ext = std.fs.path.extension(lib_arg);
    if (DIRECT_LIB_EXT_MAP.has(raw_ext)) return true;
    var ext_lower_buf: [32]u8 = undefined;
    if (toLowerBounded(&ext_lower_buf, raw_ext)) |lower_ext| {
        return DIRECT_LIB_EXT_MAP.has(lower_ext);
    }
    return false;
}

/// Duplicates `raw_text` into a NUL-terminated `[:0]u8` slice owned by `allocator`.
fn dupeSentineledZ(allocator: std.mem.Allocator, raw_text: []const u8) ![:0]u8 {
    const z_buf = try allocator.allocSentinel(u8, raw_text.len, 0);
    @memcpy(z_buf[0..raw_text.len], raw_text);
    return z_buf;
}

/// Appends a NUL-terminated copy of `raw_arg` into `owned_z`.
fn appendSentineledZ(
    allocator: std.mem.Allocator,
    owned_z: *std.ArrayListUnmanaged([:0]u8),
    raw_arg: []const u8,
) !void {
    const z_buf = try dupeSentineledZ(allocator, raw_arg);
    errdefer allocator.free(z_buf);
    try owned_z.append(allocator, z_buf);
}

/// Appends `prefix ++ middle ++ suffix` as a NUL-terminated slice into `owned_z`.
fn appendJoinedSentineledZ(
    allocator: std.mem.Allocator,
    owned_z: *std.ArrayListUnmanaged([:0]u8),
    prefix: []const u8,
    middle: []const u8,
    suffix: []const u8,
) !void {
    const total_len = prefix.len + middle.len + suffix.len;
    const z_buf = try allocator.allocSentinel(u8, total_len, 0);
    @memcpy(z_buf[0..prefix.len], prefix);
    @memcpy(z_buf[prefix.len .. prefix.len + middle.len], middle);
    @memcpy(z_buf[prefix.len + middle.len .. total_len], suffix);
    errdefer allocator.free(z_buf);
    try owned_z.append(allocator, z_buf);
}

/// Appends embedded `wasm-ld` arguments into `owned_z`, honoring `entry_symbol`, `has_dwarf_tables`, and `extra_libs`.
fn populateEmbeddedWasmLldArgs(
    allocator: std.mem.Allocator,
    owned_z: *std.ArrayListUnmanaged([:0]u8),
    staged_output_path: []const u8,
    options: CrossLinkOptions,
) !void {
    if (options.entry_symbol) |entry_sym| {
        if (entry_sym.len > 0) {
            try appendJoinedSentineledZ(allocator, owned_z, "--entry=", entry_sym, "");
        } else {
            try appendSentineledZ(allocator, owned_z, "--no-entry");
        }
    } else {
        try appendSentineledZ(allocator, owned_z, "--no-entry");
    }
    try appendSentineledZ(allocator, owned_z, "--gc-sections");
    if (options.is_release_mode) {
        try appendSentineledZ(allocator, owned_z, "--icf=safe");
        if (!options.has_dwarf_tables) {
            try appendSentineledZ(allocator, owned_z, "--strip-all");
        }
    }
    try appendSentineledZ(allocator, owned_z, "-z");
    try appendSentineledZ(allocator, owned_z, "stack-size=8192");
    for (options.lib_dirs) |dir_p| {
        if (dir_p.len == 0) continue;
        try appendJoinedSentineledZ(allocator, owned_z, "-L", dir_p, "");
    }
    for (options.object_paths) |obj_p| try appendSentineledZ(allocator, owned_z, obj_p);
    for (options.extra_libs) |lib_item| {
        if (lib_item.len == 0 or std.mem.endsWith(u8, lib_item, ".def")) continue;
        if (isDirectLibraryPathArg(lib_item)) {
            try appendSentineledZ(allocator, owned_z, lib_item);
        } else {
            try appendJoinedSentineledZ(allocator, owned_z, "-l", lib_item, "");
        }
    }
    try appendSentineledZ(allocator, owned_z, "-o");
    try appendSentineledZ(allocator, owned_z, staged_output_path);
}

/// Appends embedded `lld-link` PE/COFF arguments into `owned_z`, mapping bare library stems to `-defaultlib:<stem>.lib`.
fn populateEmbeddedCoffLldArgs(
    allocator: std.mem.Allocator,
    owned_z: *std.ArrayListUnmanaged([:0]u8),
    staged_output_path: []const u8,
    generated_implibs: []const []const u8,
    options: CrossLinkOptions,
) !void {
    try appendSentineledZ(
        allocator,
        owned_z,
        if (options.target.arch == .aarch64) "/MACHINE:ARM64" else "/MACHINE:X64",
    );
    try appendSentineledZ(
        allocator,
        owned_z,
        if (options.artifact_kind == .shared_library) "/DLL" else "/SUBSYSTEM:CONSOLE",
    );
    try appendSentineledZ(allocator, owned_z, "/OPT:REF");
    try appendSentineledZ(allocator, owned_z, "/OPT:ICF");
    try appendSentineledZ(allocator, owned_z, "/BREPRO");
    if (options.entry_symbol) |entry_sym| {
        if (entry_sym.len > 0) {
            try appendJoinedSentineledZ(allocator, owned_z, "/ENTRY:", entry_sym, "");
        }
    }
    for (options.lib_dirs) |dir_p| {
        if (dir_p.len == 0) continue;
        try appendJoinedSentineledZ(allocator, owned_z, "/LIBPATH:", dir_p, "");
    }
    for (options.object_paths) |obj_p| try appendSentineledZ(allocator, owned_z, obj_p);
    for (generated_implibs) |imp_p| try appendSentineledZ(allocator, owned_z, imp_p);
    for (options.extra_libs) |lib_item| {
        if (lib_item.len == 0 or std.mem.endsWith(u8, lib_item, ".def")) continue;
        if (isDirectLibraryPathArg(lib_item)) {
            try appendSentineledZ(allocator, owned_z, lib_item);
        } else {
            try appendJoinedSentineledZ(allocator, owned_z, "-defaultlib:", lib_item, ".lib");
        }
    }
    try appendJoinedSentineledZ(allocator, owned_z, "/OUT:", staged_output_path, "");
}

/// Appends a duplicated string argument to `argv`.
fn appendOwnedArg(
    allocator: std.mem.Allocator,
    argv: *std.ArrayListUnmanaged([]u8),
    raw_arg: []const u8,
) !void {
    const owned_copy = try allocator.dupe(u8, raw_arg);
    errdefer allocator.free(owned_copy);
    try argv.append(allocator, owned_copy);
}

/// Appends `prefix ++ suffix` as a newly allocated string argument to `argv`.
fn appendPrefixedArg(
    allocator: std.mem.Allocator,
    argv: *std.ArrayListUnmanaged([]u8),
    prefix: []const u8,
    suffix: []const u8,
) !void {
    const combined = try allocator.alloc(u8, prefix.len + suffix.len);
    @memcpy(combined[0..prefix.len], prefix);
    @memcpy(combined[prefix.len..], suffix);
    errdefer allocator.free(combined);
    try argv.append(allocator, combined);
}

/// Invokes embedded `lld` (`cx_llvm_link_with_lld`) directly for `wasm32-unknown-freestanding` or `-nostdlib` links.
fn tryLinkWithEmbeddedLld(
    allocator: std.mem.Allocator,
    staged_output_path: []const u8,
    generated_implibs: []const []const u8,
    options: CrossLinkOptions,
) !bool {
    if (!build_options.has_llvm_cpp_bridge) return false;
    if (!hasEmbeddedLld() or !options.is_embedded_lld_preferred) return false;
    if (!options.target.isFreestanding() and !options.is_nostdlib) return false;

    const flavor: c_llvm_link_bridge.CxLldFlavor = if (options.target.isWasm())
        .wasm
    else if (options.target.isDarwin())
        .macho
    else if (options.target.isWindows())
        .coff
    else
        .elf;

    var owned_z: std.ArrayListUnmanaged([:0]u8) = .empty;
    defer {
        for (owned_z.items) |z_s| allocator.free(z_s);
        owned_z.deinit(allocator);
    }

    switch (flavor) {
        .wasm => {
            try populateEmbeddedWasmLldArgs(allocator, &owned_z, staged_output_path, options);
        },
        .coff => {
            try populateEmbeddedCoffLldArgs(allocator, &owned_z, staged_output_path, generated_implibs, options);
        },
        .macho, .elf => return false,
    }

    const c_ptrs = try allocator.alloc([*:0]const u8, owned_z.items.len);
    defer allocator.free(c_ptrs);
    for (owned_z.items, 0..) |z_s, i| c_ptrs[i] = z_s.ptr;

    var err_buf: [2048]u8 = @splat(0);
    const status = c_llvm_link_bridge.cx_llvm_link_with_lld(
        flavor,
        c_ptrs.ptr,
        c_ptrs.len,
        &err_buf,
        err_buf.len,
    );
    if (status != c_llvm_link_bridge.CX_LLVM_OK) {
        if (options.diagnostic_sink) |sink| {
            codegen_abi.emitLinkerFailureDiagnostic(
                sink,
                Span.ZERO,
                @intCast(@max(status, 1)),
                std.mem.sliceTo(&err_buf, 0),
            ) catch {};
        }
        return error.LinkerFailed;
    }
    return true;
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Returns `true` when embedded C++20 `lld` drivers are compiled into this `corex` binary.
pub fn hasEmbeddedLld() bool {
    if (build_options.has_llvm_cpp_bridge) {
        return c_llvm_link_bridge.cx_llvm_has_embedded_lld() != 0;
    }
    return false;
}

/// Releases an owned argument list returned by `buildZigCcLinkArgs`.
pub fn freeOwnedArgList(allocator: std.mem.Allocator, argv: *std.ArrayListUnmanaged([]u8)) void {
    for (argv.items) |owned_s| allocator.free(owned_s);
    argv.deinit(allocator);
}

/// Serializes `members` into a deterministic `!<arch>\n` archive (`K_GNU`, `K_BSD`, or `K_COFF`) in memory.
pub fn serializeDeterministicArchiveBytes(
    allocator: std.mem.Allocator,
    kind: ArchiveKind,
    members: []const ArchiveMemberInput,
) LinkError![]u8 {
    var extracted_lists = allocator.alloc(?[][]u8, members.len) catch return error.OutOfMemory;
    for (extracted_lists) |*slot| slot.* = null;
    defer {
        for (extracted_lists) |maybe_list| {
            if (maybe_list) |list| {
                for (list) |sym_str| allocator.free(sym_str);
                allocator.free(list);
            }
        }
        allocator.free(extracted_lists);
    }

    const sym_views = allocator.alloc([]const []const u8, members.len) catch return error.OutOfMemory;
    defer allocator.free(sym_views);

    for (members, 0..) |mem_in, i| {
        if (mem_in.explicit_symbols) |exp_syms| {
            sym_views[i] = exp_syms;
        } else {
            const extracted = extractDefinedSymbolsFromObject(allocator, mem_in.data) catch
                return error.OutOfMemory;
            extracted_lists[i] = extracted;
            sym_views[i] = extracted;
        }
    }

    return switch (kind) {
        .gnu => serializeGnuOrCoffArchive(allocator, false, members, sym_views),
        .coff => serializeGnuOrCoffArchive(allocator, true, members, sym_views),
        .darwin_bsd => serializeDarwinBsdArchive(allocator, members, sym_views),
    };
}

/// Writes a bit-for-bit deterministic `.a` or `.lib` archive (`mtime = 0`, `uid = 0`, `gid = 0`, `mode = 100644`).
pub fn writeDeterministicArchive(
    io: std.Io,
    allocator: std.mem.Allocator,
    target: TargetSpec,
    output_path: []const u8,
    member_paths: []const []const u8,
) LinkError!void {
    const ar_kind = ArchiveKind.forTarget(target, output_path);

    // [1] Delegate to `cx_llvm_write_archive` when `-Dllvm-prefix` static C++20 bridge is active:
    if (build_options.has_llvm_cpp_bridge) {
        const staged_path = std.fmt.allocPrint(
            allocator,
            "{s}.ar_stage.{d}",
            .{ output_path, next_link_scratch_seq.fetchAdd(1, .monotonic) },
        ) catch return error.OutOfMemory;
        defer allocator.free(staged_path);
        defer std.Io.Dir.cwd().deleteFile(io, staged_path) catch {};

        if (std.fs.path.dirname(staged_path)) |parent_dir| {
            if (parent_dir.len > 0) std.Io.Dir.cwd().createDirPath(io, parent_dir) catch {};
        }

        const c_out = dupeSentineledZ(allocator, staged_path) catch return error.OutOfMemory;
        defer allocator.free(c_out);

        var c_member_storage = allocator.alloc([:0]u8, member_paths.len) catch return error.OutOfMemory;
        var built_count: usize = 0;
        defer {
            for (c_member_storage[0..built_count]) |z_str| allocator.free(z_str);
            allocator.free(c_member_storage);
        }
        const c_member_ptrs = allocator.alloc([*:0]const u8, @max(member_paths.len, 1)) catch
            return error.OutOfMemory;
        defer allocator.free(c_member_ptrs);

        for (member_paths, 0..) |m_path, i| {
            c_member_storage[i] = dupeSentineledZ(allocator, m_path) catch return error.OutOfMemory;
            built_count += 1;
            c_member_ptrs[i] = c_member_storage[i].ptr;
        }

        var err_buf: [1024]u8 = @splat(0);
        const status = c_llvm_link_bridge.cx_llvm_write_archive(
            c_out.ptr,
            c_member_ptrs.ptr,
            member_paths.len,
            if (ar_kind == .darwin_bsd) 1 else 0,
            if (ar_kind == .coff) 1 else 0,
            &err_buf,
            err_buf.len,
        );
        if (status != c_llvm_link_bridge.CX_LLVM_OK) return error.ArchiveWriteFailed;
        codegen_abi.publishStagedFileAtomic(io, allocator, staged_path, output_path) catch
            return error.ArchiveWriteFailed;
        return;
    }

    // [2] Pure-Zig deterministic archive writer:
    var owned_payloads = allocator.alloc([]u8, member_paths.len) catch return error.OutOfMemory;
    var loaded_count: usize = 0;
    defer {
        for (owned_payloads[0..loaded_count]) |buf| allocator.free(buf);
        allocator.free(owned_payloads);
    }

    const member_inputs = allocator.alloc(ArchiveMemberInput, member_paths.len) catch return error.OutOfMemory;
    defer allocator.free(member_inputs);

    for (member_paths, 0..) |m_path, i| {
        const opened = std.Io.Dir.cwd().openFile(io, m_path, .{
            .mode = .read_only,
            .allow_directory = false,
        }) catch return error.MemberReadFailed;
        defer opened.close(io);

        const f_size: usize = @intCast((opened.stat(io) catch return error.MemberReadFailed).size);
        const data_buf = allocator.alloc(u8, f_size) catch return error.OutOfMemory;
        if ((opened.readPositionalAll(io, data_buf, 0) catch return error.MemberReadFailed) != f_size) {
            allocator.free(data_buf);
            return error.MemberReadFailed;
        }
        owned_payloads[i] = data_buf;
        loaded_count += 1;
        member_inputs[i] = .{
            .name = std.fs.path.basename(m_path),
            .data = data_buf,
        };
    }

    const archive_bytes = try serializeDeterministicArchiveBytes(allocator, ar_kind, member_inputs);
    defer allocator.free(archive_bytes);

    codegen_abi.writeArtifactAtomic(io, allocator, output_path, archive_bytes) catch
        return error.ArchiveWriteFailed;
}

/// Parses a standard Microsoft / MinGW-w64 `.def` module definition text buffer (`LIBRARY`, `EXPORTS`).
pub fn parseModuleDef(
    allocator: std.mem.Allocator,
    def_source: []const u8,
    fallback_dll_name: []const u8,
) LinkError!ParsedModuleDef {
    var dll_name_owned: ?[]u8 = null;
    errdefer if (dll_name_owned) |d_s| allocator.free(d_s);

    var exports: std.ArrayListUnmanaged(ModuleDefExport) = .empty;
    errdefer {
        for (exports.items) |exp_item| {
            allocator.free(exp_item.sym_name);
            if (exp_item.ext_name) |ext_s| allocator.free(ext_s);
        }
        exports.deinit(allocator);
    }

    var is_in_exports = false;
    var line_iter = std.mem.splitScalar(u8, def_source, '\n');
    while (line_iter.next()) |raw_line| {
        const no_comment = if (std.mem.indexOfScalar(u8, raw_line, ';')) |semi_idx|
            raw_line[0..semi_idx]
        else
            raw_line;
        const trimmed = std.mem.trim(u8, no_comment, " \t\r");
        if (trimmed.len == 0) continue;

        var pos: usize = 0;
        const first_tok = extractNextDefToken(trimmed, &pos) orelse continue;

        var lower_buf: [32]u8 = undefined;
        if (std.ascii.eqlIgnoreCase(first_tok, "LIBRARY") or std.ascii.eqlIgnoreCase(first_tok, "NAME")) {
            is_in_exports = false;
            if (extractNextDefToken(trimmed, &pos)) |raw_lib_tok| {
                if (raw_lib_tok.len == 0) return error.InvalidModuleDef;
                if (dll_name_owned) |prev| allocator.free(prev);
                dll_name_owned = if (std.mem.indexOfScalar(u8, raw_lib_tok, '.') != null)
                    allocator.dupe(u8, raw_lib_tok) catch return error.OutOfMemory
                else
                    std.fmt.allocPrint(allocator, "{s}.dll", .{raw_lib_tok}) catch return error.OutOfMemory;
            }
            continue;
        } else if (std.ascii.eqlIgnoreCase(first_tok, "EXPORTS")) {
            // Keep `pos` immediately after `EXPORTS` to scan any inline symbol on the same line:
            is_in_exports = true;
        } else if (if (toLowerBounded(&lower_buf, first_tok)) |lower_sec| DEF_OTHER_SECTIONS_MAP.has(lower_sec) else false) {
            is_in_exports = false;
            continue;
        } else {
            pos = 0;
        }

        if (!is_in_exports) continue;

        const sym_tok = extractNextDefToken(trimmed, &pos) orelse continue;
        if (sym_tok.len == 0 or std.mem.eql(u8, sym_tok, "=") or std.mem.eql(u8, sym_tok, "==")) {
            return error.InvalidModuleDef;
        }

        var exp_entry: ModuleDefExport = .{
            .sym_name = allocator.dupe(u8, sym_tok) catch return error.OutOfMemory,
        };
        errdefer {
            allocator.free(exp_entry.sym_name);
            if (exp_entry.ext_name) |ext_s| allocator.free(ext_s);
        }

        while (extractNextDefToken(trimmed, &pos)) |attr_tok| {
            if (std.mem.eql(u8, attr_tok, "=")) {
                const internal_tok = extractNextDefToken(trimmed, &pos) orelse return error.InvalidModuleDef;
                if (internal_tok.len == 0 or
                    std.mem.eql(u8, internal_tok, "=") or
                    std.mem.eql(u8, internal_tok, "=="))
                {
                    return error.InvalidModuleDef;
                }
            } else if (std.mem.eql(u8, attr_tok, "==")) {
                const export_as_tok = extractNextDefToken(trimmed, &pos) orelse return error.InvalidModuleDef;
                if (export_as_tok.len == 0 or
                    std.mem.eql(u8, export_as_tok, "=") or
                    std.mem.eql(u8, export_as_tok, "=="))
                {
                    return error.InvalidModuleDef;
                }
                if (exp_entry.ext_name) |prev_ext| allocator.free(prev_ext);
                exp_entry.ext_name = allocator.dupe(u8, export_as_tok) catch return error.OutOfMemory;
            } else if (attr_tok[0] == '@' and attr_tok.len > 1) {
                const parsed_ord = std.fmt.parseUnsigned(u16, attr_tok[1..], 10) catch return error.InvalidModuleDef;
                if (parsed_ord == 0) return error.InvalidModuleDef;
                exp_entry.ordinal = parsed_ord;
            } else if (if (toLowerBounded(&lower_buf, attr_tok)) |lower_kw| DEF_EXPORT_ATTR_MAP.get(lower_kw) else null) |attr_kw| {
                switch (attr_kw) {
                    .noname => exp_entry.is_noname = true,
                    .data => exp_entry.is_data = true,
                    .constant => exp_entry.is_constant = true,
                    .private => exp_entry.is_private = true,
                }
            } else {
                return error.InvalidModuleDef;
            }
        }
        if (exp_entry.is_noname and exp_entry.ordinal == null) return error.InvalidModuleDef;
        exports.append(allocator, exp_entry) catch return error.OutOfMemory;
    }

    const final_dll: []u8 = if (dll_name_owned) |explicit_dll|
        explicit_dll
    else blk: {
        const clean_fb = std.mem.trim(u8, fallback_dll_name, " \t\r\n");
        if (clean_fb.len == 0) return error.InvalidModuleDef;
        break :blk if (std.mem.indexOfScalar(u8, clean_fb, '.') != null)
            allocator.dupe(u8, clean_fb) catch return error.OutOfMemory
        else
            std.fmt.allocPrint(allocator, "{s}.dll", .{clean_fb}) catch return error.OutOfMemory;
    };
    errdefer if (dll_name_owned == null) allocator.free(final_dll);

    return .{
        .dll_name = final_dll,
        .exports = exports.toOwnedSlice(allocator) catch return error.OutOfMemory,
    };
}

/// Serializes a `ParsedModuleDef` into a complete PE/COFF Short-Import `.lib` archive in memory (`DR-10` §3.3).
pub fn serializeCoffShortImportLibrary(
    allocator: std.mem.Allocator,
    parsed_def: ParsedModuleDef,
    machine: CoffMachine,
) LinkError![]u8 {
    if (parsed_def.dll_name.len == 0) return error.InvalidModuleDef;
    const dll_base = std.fs.path.basename(parsed_def.dll_name);
    const dll_stem = std.fs.path.stem(dll_base);

    const imp_desc_sym = std.fmt.allocPrint(allocator, "__IMPORT_DESCRIPTOR_{s}", .{dll_stem}) catch
        return error.OutOfMemory;
    defer allocator.free(imp_desc_sym);
    const null_thunk_sym = std.fmt.allocPrint(allocator, "\x7f{s}_NULL_THUNK_DATA", .{dll_stem}) catch
        return error.OutOfMemory;
    defer allocator.free(null_thunk_sym);

    const desc_obj = buildCoffImportDescriptorObject(
        allocator,
        dll_base,
        imp_desc_sym,
        null_thunk_sym,
        machine,
    ) catch return error.OutOfMemory;
    defer allocator.free(desc_obj);

    const null_desc_obj = buildCoffNullImportDescriptorObject(allocator, machine) catch
        return error.OutOfMemory;
    defer allocator.free(null_desc_obj);

    const null_thunk_obj = buildCoffNullThunkObject(allocator, null_thunk_sym, machine) catch
        return error.OutOfMemory;
    defer allocator.free(null_thunk_obj);

    var short_blobs: std.ArrayListUnmanaged([]u8) = .empty;
    defer {
        for (short_blobs.items) |blob| allocator.free(blob);
        short_blobs.deinit(allocator);
    }
    var owned_imp_syms: std.ArrayListUnmanaged([]u8) = .empty;
    defer {
        for (owned_imp_syms.items) |imp_str| allocator.free(imp_str);
        owned_imp_syms.deinit(allocator);
    }
    var owned_sym_slices: std.ArrayListUnmanaged([][]const u8) = .empty;
    defer {
        for (owned_sym_slices.items) |sl| allocator.free(sl);
        owned_sym_slices.deinit(allocator);
    }

    var members: std.ArrayListUnmanaged(ArchiveMemberInput) = .empty;
    defer members.deinit(allocator);

    const desc_syms: [1][]const u8 = .{imp_desc_sym};
    const null_desc_syms: [1][]const u8 = .{"__NULL_IMPORT_DESCRIPTOR"};
    const null_thunk_syms: [1][]const u8 = .{null_thunk_sym};

    members.append(allocator, .{ .name = dll_base, .data = desc_obj, .explicit_symbols = &desc_syms }) catch
        return error.OutOfMemory;
    members.append(allocator, .{ .name = dll_base, .data = null_desc_obj, .explicit_symbols = &null_desc_syms }) catch
        return error.OutOfMemory;
    members.append(allocator, .{ .name = dll_base, .data = null_thunk_obj, .explicit_symbols = &null_thunk_syms }) catch
        return error.OutOfMemory;

    for (parsed_def.exports) |exp_item| {
        if (exp_item.is_private) continue;
        const short_bytes = try buildCoffShortImportMember(allocator, dll_base, exp_item, machine);
        short_blobs.append(allocator, short_bytes) catch {
            allocator.free(short_bytes);
            return error.OutOfMemory;
        };

        const imp_sym = std.fmt.allocPrint(allocator, "__imp_{s}", .{exp_item.sym_name}) catch
            return error.OutOfMemory;
        owned_imp_syms.append(allocator, imp_sym) catch {
            allocator.free(imp_sym);
            return error.OutOfMemory;
        };

        const is_code = !exp_item.is_data and !exp_item.is_constant;
        const sym_list = allocator.alloc([]const u8, if (is_code) 2 else 1) catch return error.OutOfMemory;
        sym_list[0] = imp_sym;
        if (is_code) sym_list[1] = exp_item.sym_name;
        owned_sym_slices.append(allocator, sym_list) catch {
            allocator.free(sym_list);
            return error.OutOfMemory;
        };

        members.append(allocator, .{
            .name = dll_base,
            .data = short_bytes,
            .explicit_symbols = sym_list,
        }) catch return error.OutOfMemory;
    }

    return serializeDeterministicArchiveBytes(allocator, .coff, members.items);
}

/// Parses `def_contents` and writes a deterministic PE/COFF Short-Import `.lib` to `output_lib_path`.
pub fn writeCoffShortImportLibrary(
    io: std.Io,
    allocator: std.mem.Allocator,
    def_contents: []const u8,
    output_lib_path: []const u8,
    machine: CoffMachine,
) LinkError!void {
    if (build_options.has_llvm_cpp_bridge) {
        const staged_path = std.fmt.allocPrint(
            allocator,
            "{s}.imp_stage.{d}",
            .{ output_lib_path, next_link_scratch_seq.fetchAdd(1, .monotonic) },
        ) catch return error.OutOfMemory;
        defer allocator.free(staged_path);
        defer std.Io.Dir.cwd().deleteFile(io, staged_path) catch {};

        if (std.fs.path.dirname(staged_path)) |parent_dir| {
            if (parent_dir.len > 0) std.Io.Dir.cwd().createDirPath(io, parent_dir) catch {};
        }

        const c_out = dupeSentineledZ(allocator, staged_path) catch return error.OutOfMemory;
        defer allocator.free(c_out);

        var err_buf: [1024]u8 = @splat(0);
        const status = c_llvm_link_bridge.cx_llvm_write_coff_import_library(
            def_contents.ptr,
            def_contents.len,
            c_out.ptr,
            @backingInt(machine),
            &err_buf,
            err_buf.len,
        );
        if (status != c_llvm_link_bridge.CX_LLVM_OK) return error.ArchiveWriteFailed;
        codegen_abi.publishStagedFileAtomic(io, allocator, staged_path, output_lib_path) catch
            return error.ArchiveWriteFailed;
        return;
    }

    var parsed_def = try parseModuleDef(allocator, def_contents, std.fs.path.stem(output_lib_path));
    defer parsed_def.deinit(allocator);

    const lib_bytes = try serializeCoffShortImportLibrary(allocator, parsed_def, machine);
    defer allocator.free(lib_bytes);

    codegen_abi.writeArtifactAtomic(io, allocator, output_lib_path, lib_bytes) catch
        return error.ArchiveWriteFailed;
}

/// Builds the complete `zig cc` cross-linker argument vector for any of the 11 canonical CoreX targets.
pub fn buildZigCcLinkArgs(
    allocator: std.mem.Allocator,
    zig_exe: []const u8,
    staged_output_path: []const u8,
    generated_implibs: []const []const u8,
    options: CrossLinkOptions,
) !std.ArrayListUnmanaged([]u8) {
    var argv: std.ArrayListUnmanaged([]u8) = .empty;
    errdefer freeOwnedArgList(allocator, &argv);

    try appendOwnedArg(allocator, &argv, zig_exe);
    try appendOwnedArg(allocator, &argv, "cc");
    try appendOwnedArg(allocator, &argv, "-target");
    try appendOwnedArg(allocator, &argv, options.target.asZigTargetTriple());

    if (options.artifact_kind == .shared_library and !options.target.isWasm()) {
        try appendOwnedArg(allocator, &argv, if (options.target.isDarwin()) "-dynamiclib" else "-shared");
    }

    // [1] Target-specific linkage, dead-stripping, and linear-memory flags across all 11 targets:
    if (options.target.isFreestanding()) {
        try appendOwnedArg(allocator, &argv, "-nostdlib");
        if (if (options.entry_symbol) |entry_sym| entry_sym.len == 0 else true) {
            try appendOwnedArg(allocator, &argv, "-Wl,--no-entry");
        }
        try appendOwnedArg(allocator, &argv, "-Wl,--gc-sections");
        if (options.is_release_mode) {
            if (!options.has_dwarf_tables) {
                try appendOwnedArg(allocator, &argv, "-Wl,--strip-all");
            }
            try appendOwnedArg(allocator, &argv, "-Oz");
        }
        try appendOwnedArg(allocator, &argv, "-Wl,-z,stack-size=8192");
    } else if (options.target.os == .wasi) {
        if (options.is_nostdlib) try appendOwnedArg(allocator, &argv, "-nostdlib");
        if (options.artifact_kind == .shared_library) {
            try appendOwnedArg(allocator, &argv, "-Wl,--no-entry");
        }
        try appendOwnedArg(allocator, &argv, "-Wl,--gc-sections");
        if (options.is_release_mode) {
            if (!options.has_dwarf_tables) {
                try appendOwnedArg(allocator, &argv, "-Wl,--strip-all");
            }
            try appendOwnedArg(allocator, &argv, "-Oz");
        }
    } else if (options.target.os == .linux) {
        if (options.is_nostdlib) try appendOwnedArg(allocator, &argv, "-nostdlib");
        if (options.artifact_kind != .shared_library) {
            const is_using_static = if (options.target.abi == .musl)
                (options.link_mode == .auto or options.link_mode == .static)
            else
                (options.link_mode == .static);
            if (is_using_static) {
                try appendOwnedArg(allocator, &argv, "-static");
            }
        }
        try appendOwnedArg(allocator, &argv, "-Wl,--gc-sections");
        if (options.has_dwarf_tables) {
            try appendOwnedArg(allocator, &argv, "-Wl,--compress-debug-sections=zstd");
        }
    } else if (options.target.isDarwin()) {
        if (options.is_nostdlib) try appendOwnedArg(allocator, &argv, "-nostdlib");
        try appendOwnedArg(allocator, &argv, "-Wl,-dead_strip");
    } else if (options.target.isWindows()) {
        if (options.is_nostdlib) {
            try appendOwnedArg(allocator, &argv, "-nostdlib");
            if (options.artifact_kind == .executable) {
                try appendOwnedArg(allocator, &argv, "-Wl,--subsystem,console");
            }
        }
        try appendOwnedArg(allocator, &argv, "-Wl,--gc-sections");
    }

    if (options.entry_symbol) |entry_sym| {
        if (entry_sym.len > 0) {
            try appendPrefixedArg(allocator, &argv, "-Wl,-e,", entry_sym);
        }
    }

    // [2] Library search paths, input objects, synthesized `.lib` imports, and `-l<lib>` flags:
    for (options.lib_dirs) |dir_path| {
        if (dir_path.len > 0) {
            try appendPrefixedArg(allocator, &argv, "-L", dir_path);
        }
    }
    for (options.object_paths) |obj_path| {
        try appendOwnedArg(allocator, &argv, obj_path);
    }
    for (generated_implibs) |imp_path| {
        try appendOwnedArg(allocator, &argv, imp_path);
    }
    for (options.extra_libs) |lib_item| {
        if (lib_item.len == 0 or std.mem.endsWith(u8, lib_item, ".def")) continue;
        if (isDirectLibraryPathArg(lib_item)) {
            try appendOwnedArg(allocator, &argv, lib_item);
        } else {
            try appendPrefixedArg(allocator, &argv, "-l", lib_item);
        }
    }

    try appendOwnedArg(allocator, &argv, "-o");
    try appendOwnedArg(allocator, &argv, staged_output_path);
    return argv;
}

/// Links or archives cross-target build artifacts across all 11 canonical targets (`Prune-02` atomic replace).
pub fn linkCrossTarget(
    io: std.Io,
    allocator: std.mem.Allocator,
    options: CrossLinkOptions,
) LinkError!void {
    if (options.artifact_kind == .static_library) {
        return writeDeterministicArchive(
            io,
            allocator,
            options.target,
            options.output_path,
            options.object_paths,
        );
    }

    const scratch_dir = std.fmt.allocPrint(
        allocator,
        ".zig-cache/cx_link_{x}_{d}",
        .{
            @intFromPtr(&next_link_scratch_seq) ^
                @as(usize, @truncate(std.hash.Wyhash.hash(0, options.output_path))),
            next_link_scratch_seq.fetchAdd(1, .monotonic),
        },
    ) catch return error.OutOfMemory;
    defer allocator.free(scratch_dir);
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    std.Io.Dir.cwd().createDirPath(io, scratch_dir) catch return error.ArchiveWriteFailed;

    // [1] Synthesize Short-Import `.lib` archives for any `.def` files when targeting Windows:
    var generated_implibs: std.ArrayListUnmanaged([]u8) = .empty;
    defer {
        for (generated_implibs.items) |imp_path| allocator.free(imp_path);
        generated_implibs.deinit(allocator);
    }

    if (CoffMachine.forTarget(options.target)) |coff_machine| {
        var def_idx: usize = 0;
        const synthOneDef = struct {
            /// Reads `def_path` and emits a staged `.lib` inside `dir_path`.
            fn run(
                io_ctx: std.Io,
                alloc: std.mem.Allocator,
                dir_path: []const u8,
                def_path: []const u8,
                ordinal_idx: usize,
                mach: CoffMachine,
                out_libs: *std.ArrayListUnmanaged([]u8),
            ) LinkError!void {
                const opened = std.Io.Dir.cwd().openFile(io_ctx, def_path, .{
                    .mode = .read_only,
                    .allow_directory = false,
                }) catch return error.MemberReadFailed;
                defer opened.close(io_ctx);
                const f_sz: usize = @intCast((opened.stat(io_ctx) catch return error.MemberReadFailed).size);
                const def_text = alloc.alloc(u8, f_sz) catch return error.OutOfMemory;
                defer alloc.free(def_text);
                if ((opened.readPositionalAll(io_ctx, def_text, 0) catch return error.MemberReadFailed) != f_sz) {
                    return error.MemberReadFailed;
                }
                const lib_path = std.fmt.allocPrint(alloc, "{s}/{s}_{d}.lib", .{ dir_path, std.fs.path.stem(def_path), ordinal_idx }) catch
                    return error.OutOfMemory;
                errdefer alloc.free(lib_path);
                try writeCoffShortImportLibrary(io_ctx, alloc, def_text, lib_path, mach);
                out_libs.append(alloc, lib_path) catch return error.OutOfMemory;
            }
        }.run;

        for (options.def_files) |def_p| {
            try synthOneDef(io, allocator, scratch_dir, def_p, def_idx, coff_machine, &generated_implibs);
            def_idx += 1;
        }
        for (options.extra_libs) |extra_item| {
            if (std.mem.endsWith(u8, extra_item, ".def")) {
                try synthOneDef(io, allocator, scratch_dir, extra_item, def_idx, coff_machine, &generated_implibs);
                def_idx += 1;
            }
        }
    }

    const out_ext = if (options.artifact_kind == .shared_library)
        options.target.defaultSharedLibExtension()
    else
        options.target.defaultExeExtension();
    const staged_out = std.fmt.allocPrint(allocator, "{s}/linked_out{s}", .{ scratch_dir, out_ext }) catch
        return error.OutOfMemory;
    defer allocator.free(staged_out);

    // [2] Link via embedded `lld` when available & eligible, else invoke `zig cc` cross-driver:
    const is_linked_in_process = tryLinkWithEmbeddedLld(
        allocator,
        staged_out,
        generated_implibs.items,
        options,
    ) catch |lld_err| switch (lld_err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.LinkerFailed => return error.LinkerFailed,
    };

    if (!is_linked_in_process) {
        const zig_exe = codegen_abi.resolveZigExecutable(io, allocator, options.environ_map) catch
            return error.OutOfMemory;
        defer allocator.free(zig_exe);

        var owned_argv = buildZigCcLinkArgs(
            allocator,
            zig_exe,
            staged_out,
            generated_implibs.items,
            options,
        ) catch return error.OutOfMemory;
        defer freeOwnedArgList(allocator, &owned_argv);

        const const_argv = allocator.alloc([]const u8, owned_argv.items.len) catch return error.OutOfMemory;
        defer allocator.free(const_argv);
        for (owned_argv.items, 0..) |arg_s, i| const_argv[i] = arg_s;

        const run_res = std.process.run(allocator, io, .{
            .argv = const_argv,
            .environ_map = options.environ_map,
        }) catch return error.LinkerFailed;
        defer allocator.free(run_res.stdout);
        defer allocator.free(run_res.stderr);

        if (!run_res.term.success()) {
            if (options.diagnostic_sink) |sink| {
                const exit_code: u32 = switch (run_res.term) {
                    .exited => |code| code,
                    else => 1,
                };
                codegen_abi.emitLinkerFailureDiagnostic(sink, Span.ZERO, exit_code, run_res.stderr) catch {};
            }
            return error.LinkerFailed;
        }
    }

    // [3] Publish linked artifact atomically (`Prune-02` `UnlinkAndReplace` – `SIGKILL`-safe on macOS):
    codegen_abi.publishStagedFileAtomic(io, allocator, staged_out, options.output_path) catch
        return error.ArchiveWriteFailed;
}

// ---------------------------------------- MAIN -----------------------------------------

comptime {
    std.debug.assert(@sizeOf(CoffShortImportHeader) == 20 and @alignOf(CoffShortImportHeader) == 4);
}

test "test_codegen_link_deterministic_archives_gnu_bsd_and_coff" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const test_dir = ".zig-cache/test_codegen_link_ar";
    defer std.Io.Dir.cwd().deleteTree(io, test_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, test_dir);

    const zig_exe = try codegen_abi.resolveZigExecutable(io, allocator, null);
    defer allocator.free(zig_exe);

    const c_src = "int cx_ar_mul_add(int a, int b, int c) { return a * b + c; }\n";
    const c_path = test_dir ++ "/math_unit.c";
    try codegen_abi.writeArtifactAtomic(io, allocator, c_path, c_src);

    const ar_targets = [_]TargetSpec{
        TargetSpec.X86_64_LINUX_GNU,
        TargetSpec.AARCH64_APPLE_DARWIN,
        TargetSpec.X86_64_WINDOWS_MSVC,
    };

    for (ar_targets, 0..) |spec, idx| {
        const obj_path = try std.fmt.allocPrint(allocator, "{s}/obj_{d}{s}", .{ test_dir, idx, spec.defaultObjExtension() });
        defer allocator.free(obj_path);

        const cc_res = try std.process.run(allocator, io, .{
            .argv = &.{ zig_exe, "cc", "-c", "-nostdlib", "-target", spec.asZigTargetTriple(), "-O2", c_path, "-o", obj_path },
        });
        defer allocator.free(cc_res.stdout);
        defer allocator.free(cc_res.stderr);
        try std.testing.expect(cc_res.term.success());

        const ar_path_1 = try std.fmt.allocPrint(allocator, "{s}/lib1_{d}{s}", .{ test_dir, idx, spec.defaultStaticLibExtension() });
        defer allocator.free(ar_path_1);
        const ar_path_2 = try std.fmt.allocPrint(allocator, "{s}/lib2_{d}{s}", .{ test_dir, idx, spec.defaultStaticLibExtension() });
        defer allocator.free(ar_path_2);

        try writeDeterministicArchive(io, allocator, spec, ar_path_1, &.{obj_path});
        try writeDeterministicArchive(io, allocator, spec, ar_path_2, &.{obj_path});

        const f1 = try std.Io.Dir.cwd().openFile(io, ar_path_1, .{ .mode = .read_only });
        defer f1.close(io);
        const sz1: usize = @intCast((try f1.stat(io)).size);
        const bytes_1 = try allocator.alloc(u8, sz1);
        defer allocator.free(bytes_1);
        _ = try f1.readPositionalAll(io, bytes_1, 0);

        const f2 = try std.Io.Dir.cwd().openFile(io, ar_path_2, .{ .mode = .read_only });
        defer f2.close(io);
        const sz2: usize = @intCast((try f2.stat(io)).size);
        const bytes_2 = try allocator.alloc(u8, sz2);
        defer allocator.free(bytes_2);
        _ = try f2.readPositionalAll(io, bytes_2, 0);

        // Bit-for-bit identical archives across repeated runs with `!<arch>\n` signature and indexed symbol:
        try std.testing.expectEqualSlices(u8, bytes_1, bytes_2);
        try std.testing.expectEqualStrings(ARCHIVE_MAGIC, bytes_1[0..8]);
        try std.testing.expect(std.mem.indexOf(u8, bytes_1, "cx_ar_mul_add") != null);
    }
}

test "test_codegen_link_coff_def_aliases_and_short_import_cross_link" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const def_text =
        \\; Synthetic kernel32 subset without Windows SDK
        \\LIBRARY "kernel32.dll"
        \\EXPORTS
        \\    ExitProcess
        \\    GetCurrentProcessId @12
        \\    CxTickAlias = InternalTickImpl
        \\    CxExportRename == GetTickCount64
        \\    ExportedGlobalCounter DATA
        \\    HiddenInternalHelper PRIVATE
    ;

    var parsed = try parseModuleDef(allocator, def_text, "fallback");
    defer parsed.deinit(allocator);
    try std.testing.expectEqualStrings("kernel32.dll", parsed.dll_name);
    try std.testing.expectEqual(@as(usize, 6), parsed.exports.len);
    try std.testing.expectEqual(@as(u16, 12), parsed.exports[1].ordinal.?);
    try std.testing.expectEqualStrings("CxTickAlias", parsed.exports[2].sym_name);
    try std.testing.expect(parsed.exports[2].ext_name == null);
    try std.testing.expectEqualStrings("CxExportRename", parsed.exports[3].sym_name);
    try std.testing.expectEqualStrings("GetTickCount64", parsed.exports[3].ext_name.?);
    try std.testing.expect(parsed.exports[4].is_data);
    try std.testing.expect(parsed.exports[5].is_private);

    const test_dir = ".zig-cache/test_codegen_link_coff";
    defer std.Io.Dir.cwd().deleteTree(io, test_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, test_dir);

    const def_path = test_dir ++ "/kernel32.def";
    try codegen_abi.writeArtifactAtomic(io, allocator, def_path, def_text);

    const caller_c =
        \\__declspec(dllimport) void ExitProcess(unsigned int code);
        \\__declspec(dllimport) unsigned int GetCurrentProcessId(void);
        \\void cx_win_entry(void) {
        \\    unsigned int pid = GetCurrentProcessId();
        \\    ExitProcess(pid & 0u);
        \\}
    ;
    const caller_c_path = test_dir ++ "/win_caller.c";
    try codegen_abi.writeArtifactAtomic(io, allocator, caller_c_path, caller_c);

    const zig_exe = try codegen_abi.resolveZigExecutable(io, allocator, null);
    defer allocator.free(zig_exe);

    const win_targets = [_]struct { spec: TargetSpec, expected_pe_machine: u16 }{
        .{ .spec = TargetSpec.X86_64_WINDOWS_MSVC, .expected_pe_machine = 0x8664 },
        .{ .spec = TargetSpec.X86_64_WINDOWS_GNU, .expected_pe_machine = 0x8664 },
        .{ .spec = TargetSpec.AARCH64_WINDOWS_MSVC, .expected_pe_machine = 0xAA64 },
    };

    for (win_targets, 0..) |entry, idx| {
        const obj_path = try std.fmt.allocPrint(allocator, "{s}/caller_{d}{s}", .{
            test_dir,
            idx,
            entry.spec.defaultObjExtension(),
        });
        defer allocator.free(obj_path);

        const cc_res = try std.process.run(allocator, io, .{
            .argv = &.{ zig_exe, "cc", "-c", "-nostdlib", "-target", entry.spec.asZigTargetTriple(), "-O2", caller_c_path, "-o", obj_path },
        });
        defer allocator.free(cc_res.stdout);
        defer allocator.free(cc_res.stderr);
        try std.testing.expect(cc_res.term.success());

        const exe_path = try std.fmt.allocPrint(allocator, "{s}/app_{d}.exe", .{ test_dir, idx });
        defer allocator.free(exe_path);

        try linkCrossTarget(io, allocator, .{
            .target = entry.spec,
            .object_paths = &.{obj_path},
            .output_path = exe_path,
            .artifact_kind = .executable,
            .is_nostdlib = true,
            .entry_symbol = "cx_win_entry",
            .def_files = &.{def_path},
        });

        const pe_file = try std.Io.Dir.cwd().openFile(io, exe_path, .{ .mode = .read_only });
        defer pe_file.close(io);
        const pe_sz: usize = @intCast((try pe_file.stat(io)).size);
        const pe_bytes = try allocator.alloc(u8, pe_sz);
        defer allocator.free(pe_bytes);
        _ = try pe_file.readPositionalAll(io, pe_bytes, 0);

        try std.testing.expect(pe_bytes.len > 0x80);
        try std.testing.expectEqualStrings("MZ", pe_bytes[0..2]);
        const pe_off: usize = std.mem.readInt(u32, pe_bytes[0x3C..0x40], .little);
        try std.testing.expect(pe_off + 6 <= pe_bytes.len);
        try std.testing.expectEqualStrings("PE\x00\x00", pe_bytes[pe_off .. pe_off + 4]);
        try std.testing.expectEqual(entry.expected_pe_machine, std.mem.readInt(u16, pe_bytes[pe_off + 4 ..][0..2], .little));
    }
}

test "test_codegen_link_target_arg_matrix_and_freestanding_wasm_size" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Verify `buildZigCcLinkArgs` covers all 11 canonical targets cleanly:
    for (codegen_abi.ALL_CANONICAL_TARGETS) |spec| {
        var args = try buildZigCcLinkArgs(allocator, "zig", "out.bin", &.{}, .{
            .target = spec,
            .object_paths = &.{"mod.o"},
            .output_path = "out.bin",
            .is_release_mode = true,
        });
        defer freeOwnedArgList(allocator, &args);
        try std.testing.expect(args.items.len >= 6);

        if (spec.isFreestanding()) {
            var has_no_entry = false;
            var has_stack_flag = false;
            for (args.items) |arg_s| {
                if (std.mem.eql(u8, arg_s, "-Wl,--no-entry")) has_no_entry = true;
                if (std.mem.eql(u8, arg_s, "-Wl,-z,stack-size=8192")) has_stack_flag = true;
            }
            try std.testing.expect(has_no_entry and has_stack_flag);
        } else if (spec.os == .linux and spec.abi == .musl) {
            var has_static_flag = false;
            for (args.items) |arg_s| {
                if (std.mem.eql(u8, arg_s, "-static")) has_static_flag = true;
            }
            try std.testing.expect(has_static_flag);
        } else if (spec.isDarwin()) {
            var has_dead_strip = false;
            for (args.items) |arg_s| {
                if (std.mem.eql(u8, arg_s, "-Wl,-dead_strip")) has_dead_strip = true;
            }
            try std.testing.expect(has_dead_strip);
        }
    }

    // [2] Compile & link a real `wasm32-unknown-freestanding` kernel and assert `< 10 KB` footprint:
    const test_dir = ".zig-cache/test_codegen_link_wasm";
    defer std.Io.Dir.cwd().deleteTree(io, test_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, test_dir);

    const wasm_c =
        \\__attribute__((visibility("default"))) int cx_simd_dot4(int a0, int a1, int b0, int b1) {
        \\    return (a0 * b0) + (a1 * b1);
        \\}
    ;
    const wasm_c_path = test_dir ++ "/kernel.c";
    const wasm_obj_path = test_dir ++ "/kernel.o";
    const wasm_out_path = test_dir ++ "/kernel.wasm";
    try codegen_abi.writeArtifactAtomic(io, allocator, wasm_c_path, wasm_c);

    const zig_exe = try codegen_abi.resolveZigExecutable(io, allocator, null);
    defer allocator.free(zig_exe);

    const cc_res = try std.process.run(allocator, io, .{
        .argv = &.{
            zig_exe,
            "cc",
            "-c",
            "-target",
            "wasm32-freestanding",
            "-Oz",
            "-ffunction-sections",
            "-fdata-sections",
            wasm_c_path,
            "-o",
            wasm_obj_path,
        },
    });
    defer allocator.free(cc_res.stdout);
    defer allocator.free(cc_res.stderr);
    try std.testing.expect(cc_res.term.success());

    try linkCrossTarget(io, allocator, .{
        .target = TargetSpec.WASM32_UNKNOWN_FREESTANDING,
        .object_paths = &.{wasm_obj_path},
        .output_path = wasm_out_path,
        .artifact_kind = .executable,
        .is_release_mode = true,
    });

    const wasm_file = try std.Io.Dir.cwd().openFile(io, wasm_out_path, .{ .mode = .read_only });
    defer wasm_file.close(io);
    const wasm_sz: usize = @intCast((try wasm_file.stat(io)).size);
    const wasm_bytes = try allocator.alloc(u8, wasm_sz);
    defer allocator.free(wasm_bytes);
    _ = try wasm_file.readPositionalAll(io, wasm_bytes, 0);

    try std.testing.expect(wasm_bytes.len >= 8 and wasm_bytes.len < 10_240);
    try std.testing.expectEqualSlices(u8, "\x00asm\x01\x00\x00\x00", wasm_bytes[0..8]);
}

/// Deterministic mock reactor world exercising EOF, error, and terminal CQE reaping.
const MockWorld = struct {
    /// Fault-injection mode (`0 = EOF`, `1 = (size_t)-1`, `2 = emit CQE`).
    mode: u8 = 0,
    /// Synthetic terminal CQE delivered in mode `2`.
    cqe_to_emit: sim_seam.ReactorCqe = .{},
    /// Captured orphan file descriptor from `onOrphan`.
    reaped_fd: i32 = -1,
    /// Captured orphan DMA buffer pool ID from `onOrphan`.
    reaped_pool: u32 = 0,
    /// Captured orphan cleanup action from `onOrphan`.
    reaped_action: sim_seam.ReaperAction = .none,
    /// Invocation count of `pollOrPark`.
    poll_calls: u32 = 0,

    /// Deterministic mock `poll_or_park` hook testing EOF, error, and terminal CQE delivery.
    fn pollOrPark(
        raw_ctx: *sim_seam.ReactorCtx,
        cqes_out: [*]sim_seam.ReactorCqe,
        cap: usize,
        _: bool,
    ) callconv(.c) usize {
        const world: *@This() = @ptrCast(@alignCast(raw_ctx));
        world.poll_calls += 1;
        if (world.mode == 0) {
            return 0;
        } else if (world.mode == 1) {
            return std.math.maxInt(usize);
        }
        std.debug.assert(cap >= 1);
        cqes_out[0] = world.cqe_to_emit;
        return 1;
    }

    /// Captures orphaned resource metadata reported during `drainQuarantinedBarrier`.
    fn onOrphan(raw_ctx: *sim_seam.ReactorCtx, outcome: sim_seam.ReapOutcome) callconv(.c) void {
        const world: *@This() = @ptrCast(@alignCast(raw_ctx));
        world.reaped_fd = outcome.orphan_fd;
        world.reaped_pool = outcome.orphan_buf.owned_pool_id;
        world.reaped_action = outcome.orphan_action;
    }
};

test "test_codegen_link_sim_seam_reaper_aba_and_orphan_barrier" {
    var slots: [4]sim_seam.InFlightOpSlot = @splat(.{});
    var reaper = sim_seam.CompletionReaper.init(&slots);

    // [1] Submit slot 0, complete it, and verify ABA-guarded `releaseCompletedSlot`:
    const s0 = reaper.acquireSlot().?;
    var dummy_storage: [16]u8 = @splat(0xAB);
    const key0 = reaper.markSubmitted(
        s0,
        1,
        17,
        .{ .base = &dummy_storage, .len = 16, .capacity = 16, .owned_pool_id = 3 },
        .release_buffer,
    );
    const stale_key0: sim_seam.IoUserData = .{
        .slot_index = key0.slot_index,
        .generation = key0.generation +% 1,
        .worker_id = 1,
    };
    try std.testing.expect(!reaper.requestCancel(stale_key0, null, null));
    const done_out = reaper.reapCompletion(.{ .user_data = key0.asU64(), .result = 16 }).?;
    try std.testing.expectEqual(sim_seam.SlotState.completed, done_out.state);
    try std.testing.expectEqual(@as(i32, 16), done_out.cqe_result);
    try std.testing.expect(reaper.releaseCompletedSlot(stale_key0) == null);
    const released_buf = reaper.releaseCompletedSlot(key0).?;
    try std.testing.expectEqual(@as(usize, 16), released_buf.len);
    try std.testing.expectEqual(@as(u32, 3), released_buf.owned_pool_id);
    // Double-release with `key0` must fail ABA generation check (`generation` bumped to `1`):
    try std.testing.expect(reaper.releaseCompletedSlot(key0) == null);

    // [2] Re-acquire recycled slot 0 (`generation == 1`), verify `key0` (`generation == 0`) cannot cancel it:
    const s0_reused = reaper.acquireSlot().?;
    try std.testing.expectEqual(s0, s0_reused);
    const key0_gen1 = reaper.markSubmitted(
        s0_reused,
        2,
        99,
        .{ .base = &dummy_storage, .len = 8, .capacity = 16, .owned_pool_id = 9 },
        .release_buf_and_close_fd,
    );
    try std.testing.expect(!reaper.requestCancel(key0, null, null));
    try std.testing.expect(reaper.requestCancel(key0_gen1, null, null));
    try std.testing.expectEqual(@as(u32, 1), reaper.quarantined_count);

    // [3] Verify `drainQuarantinedBarrier` breaks immediately on `0` (EOF) and `maxInt(usize)` (`(size_t)-1` error):
    var world: MockWorld = .{
        .mode = 0,
        .cqe_to_emit = .{ .user_data = key0_gen1.asU64(), .result = -125 },
    };
    const vt: sim_seam.ReactorVTable = .{ .poll_or_park = &MockWorld.pollOrPark };
    const ctx_ptr: *sim_seam.ReactorCtx = @ptrCast(&world);

    try std.testing.expect(!reaper.drainQuarantinedBarrier(&vt, ctx_ptr, 64, &MockWorld.onOrphan));
    try std.testing.expectEqual(@as(u32, 1), world.poll_calls);

    world.mode = 1;
    world.poll_calls = 0;
    try std.testing.expect(!reaper.drainQuarantinedBarrier(&vt, ctx_ptr, 64, &MockWorld.onOrphan));
    try std.testing.expectEqual(@as(u32, 1), world.poll_calls);

    // [4] Deliver terminal CQE for quarantined slot and verify orphan FD + buffer metadata are preserved:
    world.mode = 2;
    try std.testing.expect(reaper.drainQuarantinedBarrier(&vt, ctx_ptr, 8, &MockWorld.onOrphan));
    try std.testing.expectEqual(@as(u32, 0), reaper.quarantined_count);
    try std.testing.expectEqual(@as(i32, 99), world.reaped_fd);
    try std.testing.expectEqual(@as(u32, 9), world.reaped_pool);
    try std.testing.expectEqual(sim_seam.ReaperAction.release_buf_and_close_fd, world.reaped_action);
}

test "test_codegen_link_darwin_bsd_archive_eight_byte_alignment" {
    const allocator = std.testing.allocator;

    // Construct 3 synthetic Mach-O member payloads with odd/unaligned lengths (`37`, `51`, `29` bytes):
    var macho_0: [37]u8 = @splat(0xA1);
    std.mem.writeInt(u32, macho_0[0..4], 0xFEED_FACF, .little);
    std.mem.writeInt(u32, macho_0[16..20], 0, .little);
    std.mem.writeInt(u32, macho_0[20..24], 0, .little);

    var macho_1: [51]u8 = @splat(0xB2);
    std.mem.writeInt(u32, macho_1[0..4], 0xFEED_FACF, .little);
    std.mem.writeInt(u32, macho_1[16..20], 0, .little);
    std.mem.writeInt(u32, macho_1[20..24], 0, .little);

    var macho_2: [29]u8 = @splat(0xC3);
    std.mem.writeInt(u32, macho_2[0..4], 0xFEED_FACF, .little);
    std.mem.writeInt(u32, macho_2[16..20], 0, .little);
    std.mem.writeInt(u32, macho_2[20..24], 0, .little);

    const syms_0: [1][]const u8 = .{"_sym_alpha"};
    const syms_1: [1][]const u8 = .{"_sym_beta_long"};
    const syms_2: [1][]const u8 = .{"_sym_gamma"};
    const members = [_]ArchiveMemberInput{
        .{ .name = "a.o", .data = &macho_0, .explicit_symbols = &syms_0 },
        .{ .name = "longer_member_b.o", .data = &macho_1, .explicit_symbols = &syms_1 },
        .{ .name = "unit_c.o", .data = &macho_2, .explicit_symbols = &syms_2 },
    };

    const ar_bytes = try serializeDeterministicArchiveBytes(allocator, .darwin_bsd, &members);
    defer allocator.free(ar_bytes);
    try std.testing.expectEqualStrings(ARCHIVE_MAGIC, ar_bytes[0..8]);

    // Walk every `ar_hdr` record (`__.SYMDEF SORTED` + 3 Mach-O members) and verify alignment & exact slices:
    var cursor: usize = ARCHIVE_MAGIC.len;
    var member_idx: usize = 0;
    while (cursor < ar_bytes.len) {
        try std.testing.expectEqual(@as(usize, 0), cursor & 1);
        try std.testing.expect(cursor + AR_HEADER_BYTES <= ar_bytes.len);
        const hdr = ar_bytes[cursor .. cursor + AR_HEADER_BYTES];
        try std.testing.expectEqualStrings("`\n", hdr[58..60]);

        const name_field = std.mem.trimEnd(u8, hdr[0..16], " ");
        try std.testing.expect(std.mem.startsWith(u8, name_field, "#1/"));
        const ext_len = try std.fmt.parseUnsigned(usize, name_field[3..], 10);
        const ar_size = try std.fmt.parseUnsigned(usize, std.mem.trimEnd(u8, hdr[48..58], " "), 10);

        const payload_start = cursor + AR_HEADER_BYTES + ext_len;
        const payload_len = ar_size - ext_len;
        try std.testing.expectEqual(@as(usize, 0), payload_start & 7);
        try std.testing.expect(payload_start + payload_len <= ar_bytes.len);

        if (member_idx > 0) {
            const expected_data = members[member_idx - 1].data;
            try std.testing.expectEqual(expected_data.len, payload_len);
            try std.testing.expectEqualSlices(u8, expected_data, ar_bytes[payload_start .. payload_start + payload_len]);
        }
        cursor = cursor + AR_HEADER_BYTES + ar_size + (ar_size & 1);
        member_idx += 1;
    }
    try std.testing.expectEqual(@as(usize, 4), member_idx);
    try std.testing.expectEqual(ar_bytes.len, cursor);
}

test "test_codegen_link_inline_exports_noname_and_embedded_lld_flags" {
    const allocator = std.testing.allocator;

    // [1] Inline `EXPORTS EXP @1`, `EXPORTS "QuotedSym" @2`, `=` internal alias, and `==` DLL export rename:
    const def_src =
        \\LIBRARY "custom.dll"
        \\EXPORTS EXP @1
        \\EXPORTS "QuotedSym" @2
        \\    InternalAlias = LocalImpl == TargetFn @12 NONAME
        \\    RenamedImport == RealDllExport
    ;
    var parsed = try parseModuleDef(allocator, def_src, "fallback");
    defer parsed.deinit(allocator);
    try std.testing.expectEqual(@as(usize, 4), parsed.exports.len);
    try std.testing.expectEqualStrings("EXP", parsed.exports[0].sym_name);
    try std.testing.expectEqual(@as(u16, 1), parsed.exports[0].ordinal.?);
    try std.testing.expectEqualStrings("QuotedSym", parsed.exports[1].sym_name);
    try std.testing.expectEqual(@as(u16, 2), parsed.exports[1].ordinal.?);
    try std.testing.expectEqualStrings("InternalAlias", parsed.exports[2].sym_name);
    try std.testing.expectEqualStrings("TargetFn", parsed.exports[2].ext_name.?);
    try std.testing.expect(parsed.exports[2].is_noname);
    try std.testing.expectEqualStrings("RenamedImport", parsed.exports[3].sym_name);
    try std.testing.expectEqualStrings("RealDllExport", parsed.exports[3].ext_name.?);

    const noname_member = try buildCoffShortImportMember(allocator, "custom.dll", parsed.exports[2], .amd64);
    defer allocator.free(noname_member);
    const expected_payload_len: usize = "InternalAlias".len + 1 + "custom.dll".len + 1;
    try std.testing.expectEqual(@as(usize, 20) + expected_payload_len, noname_member.len);
    try std.testing.expectEqual(@as(u32, @intCast(expected_payload_len)), std.mem.readInt(u32, noname_member[12..16], .little));
    const type_info = std.mem.readInt(u16, noname_member[18..20], .little);
    try std.testing.expectEqual(COFF_IMPORT_NAME_ORDINAL, (type_info >> 2) & 0x07);

    const exportas_member = try buildCoffShortImportMember(allocator, "custom.dll", parsed.exports[3], .amd64);
    defer allocator.free(exportas_member);
    const exportas_type_info = std.mem.readInt(u16, exportas_member[18..20], .little);
    try std.testing.expectEqual(COFF_IMPORT_NAME_EXPORTAS, (exportas_type_info >> 2) & 0x07);

    // [2] Embedded `wasm-ld` and `lld-link` flags honor `entry_symbol`, `--icf=safe`, and `-defaultlib:<stem>.lib`:
    var wasm_args: std.ArrayListUnmanaged([:0]u8) = .empty;
    defer {
        for (wasm_args.items) |z_arg| allocator.free(z_arg);
        wasm_args.deinit(allocator);
    }
    try populateEmbeddedWasmLldArgs(allocator, &wasm_args, "out.wasm", .{
        .target = TargetSpec.WASM32_UNKNOWN_FREESTANDING,
        .object_paths = &.{"k.o"},
        .output_path = "out.wasm",
        .is_release_mode = true,
        .has_dwarf_tables = true,
        .entry_symbol = "cx_custom_entry",
        .extra_libs = &.{ "m", "vendor.a" },
    });
    var has_entry = false;
    var has_strip = false;
    var has_icf_safe = false;
    var has_initial_mem = false;
    var has_export_dyn = false;
    var has_lib_m = false;
    var has_vendor_a = false;
    for (wasm_args.items) |z_arg| {
        if (std.mem.eql(u8, z_arg, "--entry=cx_custom_entry")) {
            has_entry = true;
        } else if (std.mem.eql(u8, z_arg, "--strip-all")) {
            has_strip = true;
        } else if (std.mem.eql(u8, z_arg, "--icf=safe")) {
            has_icf_safe = true;
        } else if (std.mem.startsWith(u8, z_arg, "--initial-memory")) {
            has_initial_mem = true;
        } else if (std.mem.eql(u8, z_arg, "--export-dynamic")) {
            has_export_dyn = true;
        } else if (std.mem.eql(u8, z_arg, "-lm")) {
            has_lib_m = true;
        } else if (std.mem.eql(u8, z_arg, "vendor.a")) {
            has_vendor_a = true;
        }
    }
    try std.testing.expect(
        has_entry and !has_strip and has_icf_safe and !has_initial_mem and !has_export_dyn and has_lib_m and has_vendor_a,
    );

    var coff_args: std.ArrayListUnmanaged([:0]u8) = .empty;
    defer {
        for (coff_args.items) |z_arg| allocator.free(z_arg);
        coff_args.deinit(allocator);
    }
    try populateEmbeddedCoffLldArgs(allocator, &coff_args, "app.exe", &.{"synth.lib"}, .{
        .target = TargetSpec.X86_64_WINDOWS_MSVC,
        .object_paths = &.{"main.obj"},
        .output_path = "app.exe",
        .extra_libs = &.{ "kernel32", "vendor.lib" },
    });
    var has_defaultlib_k32 = false;
    var has_vendor_lib = false;
    for (coff_args.items) |z_arg| {
        if (std.mem.eql(u8, z_arg, "-defaultlib:kernel32.lib")) {
            has_defaultlib_k32 = true;
        } else if (std.mem.eql(u8, z_arg, "vendor.lib")) {
            has_vendor_lib = true;
        }
    }
    try std.testing.expect(has_defaultlib_k32 and has_vendor_lib);
}

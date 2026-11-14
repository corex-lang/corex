//! CoreX Stage-0 Target Specification, `TypeLayoutResolver`, `AbiClassifier` & `CodegenBackend`
//!
//! Provides the single canonical layout, niche, `#soa` column, and calling-convention authority
//! shared across `MirVm`, Tier A (`-ofmt=c`), and Tier B (`LLVM 20–23`), eliminating dev/release
//! ABI or padding divergence (`DR-09` §1.1, `DR-20` `Prune-01`–`Prune-04`, `Fix-07`).
//!
//! All binary metadata structs (`TargetSpec` `4B`, `NicheSpec` `24B`, `ResolvedTypeLayout` `32B`,
//! `AbiParamRecipe` `16B`, `ProvenValueRange` `24B`) carry `comptime` size and alignment guards,
//! and `CodegenBackend` is an exhaustive tagged union with zero untyped pointer escape hatches.

const std = @import("std");
const builtin = @import("builtin");
const mem_foundation = @import("mem_foundation.zig");
const diagnostic = @import("diag/diagnostic.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const mir = @import("mir.zig");
const mir_sast = @import("mir_sast.zig");
const mir_vm = @import("mir_vm.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const codegen_c = @import("codegen_c.zig");
const codegen_llvm = @import("codegen_llvm.zig");

const Span = mem_foundation.Span;
const TypeId = mem_foundation.TypeId;
const StringInterner = mem_foundation.StringInterner;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolRecord = symbol_resolver.SymbolRecord;
const SymbolTable = symbol_resolver.SymbolTable;
const InternPool = type_system.InternPool;
const ParamMode = type_system.ParamMode;
const TargetLayout = type_system.TargetLayout;
const NominalTypeSubst = type_system.NominalTypeSubst;

/// Re-exported 24-byte Pentagon-proven SSA scalar range and alignment fact (`[MAJOR-08]`).
pub const ProvenValueRange = mir_sast.ProvenValueRange;

// ---------------------------------------- TYPES ----------------------------------------

// ------------------- Target Specifications --------------------

/// Supported Phase-7 hardware instruction-set architectures (`PLAN.md` Phase 7).
pub const TargetArch = enum(u8) {
    /// 64-bit x86 (`AMD64` / `Intel 64`).
    x86_64 = 0,
    /// 64-bit ARM (`ARMv8-A` / Apple Silicon).
    aarch64 = 1,
    /// 32-bit WebAssembly (`wasm32`).
    wasm32 = 2,
};

/// Supported Phase-7 operating system and runtime ABI environments (`PLAN.md` Phase 7).
pub const TargetOs = enum(u8) {
    /// Linux (`ELF64`, `SysV AMD64` / `AAPCS64`).
    linux = 0,
    /// Apple macOS (`Mach-O`, `SysV AMD64` / `Apple ARM64` with `128B` L2 coherence line).
    macos = 1,
    /// Microsoft Windows (`PE/COFF`, `Win64` / `ARM64` with SEH `.pdata`/`.xdata`).
    windows = 2,
    /// WebAssembly System Interface (`WASI` Preview 1 MVP ABI).
    wasi = 3,
};

/// Target SIMD vector-width tier governing `#soa` column alignment (`DR-09` §1.1, `[CRITICAL-03]`).
pub const SimdLevel = enum(u8) {
    /// Scalar fallback (`8`-byte alignment floor).
    none = 0,
    /// Baseline `128`-bit SIMD (`SSE2` on `x86_64`, `NEON` on `aarch64`, `SIMD128` on `wasm32` -> `16B`).
    sse2_neon_simd128 = 1,
    /// `256`-bit `AVX2` SIMD on `x86_64` (`32B` column alignment).
    avx2 = 2,
    /// `512`-bit `AVX-512` SIMD on `x86_64` (`64B` column alignment).
    avx512 = 3,
};

/// 4-byte binary-exact target specification covering all 7 canonical Phase-7 targets.
pub const TargetSpec = extern struct {
    /// Target CPU architecture (`1B`).
    arch: TargetArch,
    /// Target OS / ABI environment (`1B`).
    os: TargetOs,
    /// Target SIMD alignment tier (`1B`).
    simd_level: SimdLevel = .sse2_neon_simd128,
    /// Explicit zero padding (`1B`).
    _pad: u8 = 0,

    /// Canonical `x86_64-linux` target (`64B` cache line, `16B` baseline SIMD).
    pub const X86_64_LINUX: TargetSpec = .{ .arch = .x86_64, .os = .linux };
    /// Canonical `x86_64-macos` target (`64B` cache line, `16B` baseline SIMD).
    pub const X86_64_MACOS: TargetSpec = .{ .arch = .x86_64, .os = .macos };
    /// Canonical `x86_64-windows` target (`64B` cache line, `16B` baseline SIMD).
    pub const X86_64_WINDOWS: TargetSpec = .{ .arch = .x86_64, .os = .windows };
    /// Canonical `aarch64-linux` target (`64B` cache line, `16B` NEON SIMD).
    pub const AARCH64_LINUX: TargetSpec = .{ .arch = .aarch64, .os = .linux };
    /// Canonical `aarch64-macos` target (`128B` Apple Silicon cache line per `D-10A`, `16B` NEON SIMD).
    pub const AARCH64_MACOS: TargetSpec = .{ .arch = .aarch64, .os = .macos };
    /// Canonical `aarch64-windows` target (`64B` cache line, `16B` NEON SIMD).
    pub const AARCH64_WINDOWS: TargetSpec = .{ .arch = .aarch64, .os = .windows };
    /// Canonical `wasm32-wasi` target (`32`-bit pointers, `64B` cache line, `16B` SIMD128).
    pub const WASM32_WASI: TargetSpec = .{ .arch = .wasm32, .os = .wasi };

    /// Returns the `TargetSpec` matching the host machine running `stage0/corex`.
    pub fn host() TargetSpec {
        const host_arch: TargetArch = switch (builtin.cpu.arch) {
            .x86_64 => .x86_64,
            .aarch64 => .aarch64,
            .wasm32 => .wasm32,
            else => .x86_64,
        };
        const host_os: TargetOs = switch (builtin.os.tag) {
            .linux => .linux,
            .macos => .macos,
            .windows => .windows,
            .wasi => .wasi,
            else => if (host_arch == .wasm32) .wasi else .linux,
        };
        if (!isValidCombination(host_arch, host_os)) {
            return if (host_arch == .wasm32) WASM32_WASI else X86_64_LINUX;
        }
        return .{ .arch = host_arch, .os = host_os };
    }

    /// Returns `true` iff `(arch, os)` is one of the 7 supported Phase-7 target combinations.
    pub inline fn isValidCombination(arch: TargetArch, os: TargetOs) bool {
        return switch (arch) {
            .x86_64, .aarch64 => os == .linux or os == .macos or os == .windows,
            .wasm32 => os == .wasi,
        };
    }

    /// Represents `self` as the frontend `type_system.TargetLayout` (`D-10A`, `[CRITICAL-03]`).
    pub inline fn asTargetLayout(self: TargetSpec) TargetLayout {
        const is_wasm = self.arch == .wasm32;
        const cache_log2: u8 = if (self.arch == .aarch64 and self.os == .macos) 7 else 6;
        const simd_log2: u8 = switch (self.simd_level) {
            .none => 3,
            .sse2_neon_simd128 => 4,
            .avx2 => 5,
            .avx512 => 6,
        };
        return .{
            .ptr_byte_size = if (is_wasm) 4 else 8,
            .ptr_align_log2 = if (is_wasm) 2 else 3,
            .cache_line_align_log2 = cache_log2,
            .simd_align_log2 = simd_log2,
        };
    }

    /// Returns the pointer byte width (`4` on `wasm32`, `8` on 64-bit native targets).
    pub inline fn ptrBytes(self: TargetSpec) u8 {
        return if (self.arch == .wasm32) 4 else 8;
    }

    /// Returns `true` when targeting Apple macOS (`Mach-O`).
    pub inline fn isDarwin(self: TargetSpec) bool {
        return self.os == .macos;
    }

    /// Returns `true` when targeting Microsoft Windows (`PE/COFF`).
    pub inline fn isWindows(self: TargetSpec) bool {
        return self.os == .windows;
    }

    /// Returns `true` when targeting `wasm32-wasi`.
    pub inline fn isWasm(self: TargetSpec) bool {
        return self.arch == .wasm32;
    }

    /// Packs `(arch, os)` into the 16-bit tag stored in `CxDevSeamHeader.arch_os_tag`.
    pub inline fn archOsTag(self: TargetSpec) u16 {
        return (@as(u16, @backingInt(self.arch)) << 8) | @as(u16, @backingInt(self.os));
    }

    /// Returns the canonical short CoreX target name (`"x86_64-linux"`, …).
    pub fn canonicalName(self: TargetSpec) []const u8 {
        return switch (self.arch) {
            .x86_64 => switch (self.os) {
                .linux => "x86_64-linux",
                .macos => "x86_64-macos",
                .windows => "x86_64-windows",
                .wasi => "wasm32-wasi",
            },
            .aarch64 => switch (self.os) {
                .linux => "aarch64-linux",
                .macos => "aarch64-macos",
                .windows => "aarch64-windows",
                .wasi => "wasm32-wasi",
            },
            .wasm32 => "wasm32-wasi",
        };
    }

    /// Represents `self` as the `zig cc -target <triple>` string for cross-compilation (`LLD` + bundled sysroots).
    pub fn asZigTargetTriple(self: TargetSpec) []const u8 {
        return switch (self.arch) {
            .x86_64 => switch (self.os) {
                .linux => "x86_64-linux-gnu",
                .macos => "x86_64-macos",
                .windows => "x86_64-windows-gnu",
                .wasi => "wasm32-wasi",
            },
            .aarch64 => switch (self.os) {
                .linux => "aarch64-linux-gnu",
                .macos => "aarch64-macos",
                .windows => "aarch64-windows-gnu",
                .wasi => "wasm32-wasi",
            },
            .wasm32 => "wasm32-wasi",
        };
    }

    /// Represents `self` as the canonical LLVM 20–23 `target triple = "…"` header string.
    pub fn asLlvmTargetTriple(self: TargetSpec) []const u8 {
        return switch (self.arch) {
            .x86_64 => switch (self.os) {
                .linux => "x86_64-unknown-linux-gnu",
                .macos => "x86_64-apple-macosx14.0.0",
                .windows => "x86_64-w64-windows-gnu",
                .wasi => "wasm32-unknown-wasi",
            },
            .aarch64 => switch (self.os) {
                .linux => "aarch64-unknown-linux-gnu",
                .macos => "arm64-apple-macosx14.0.0",
                .windows => "aarch64-w64-windows-gnu",
                .wasi => "wasm32-unknown-wasi",
            },
            .wasm32 => "wasm32-unknown-wasi",
        };
    }

    /// Represents `self` as the exact LLVM 20–23 `target datalayout = "…"` string.
    pub fn asLlvmDataLayout(self: TargetSpec) []const u8 {
        return switch (self.arch) {
            .x86_64 => switch (self.os) {
                .linux => "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
                .macos => "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
                .windows => "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
                .wasi => "e-m:e-p:32:32-p10:8:8-p20:8:8-i64:64-n32:64-S128-ni:1:10:20",
            },
            .aarch64 => switch (self.os) {
                .linux => "e-m:e-p270:32:32-p271:32:32-p272:64:64-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32",
                .macos => "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32",
                .windows => "e-m:w-p:64:64-i32:32-i64:64-i128:128-n32:64-S128-Fn32",
                .wasi => "e-m:e-p:32:32-p10:8:8-p20:8:8-i64:64-n32:64-S128-ni:1:10:20",
            },
            .wasm32 => "e-m:e-p:32:32-p10:8:8-p20:8:8-i64:64-n32:64-S128-ni:1:10:20",
        };
    }

    /// Returns the default executable file extension for `self` (`".exe"`, `".wasm"`, or `""`).
    pub fn executableExtension(self: TargetSpec) []const u8 {
        return switch (self.os) {
            .windows => ".exe",
            .wasi => ".wasm",
            .linux, .macos => "",
        };
    }

    /// Returns the default relocatable object file extension for `self` (`".obj"` or `".o"`).
    pub fn objectExtension(self: TargetSpec) []const u8 {
        return switch (self.os) {
            .windows => ".obj",
            .linux, .macos, .wasi => ".o",
        };
    }

    /// Parses a target triple string (plus optional `+avx2` / `+avx512` feature suffix on `x86_64`) in $O(1)$ time.
    pub fn parseTargetTriple(raw_triple: []const u8) ?TargetSpec {
        const trimmed = std.mem.trim(u8, raw_triple, " \t\r\n");
        if (trimmed.len == 0) return null;
        if (std.mem.eql(u8, trimmed, "native") or std.mem.eql(u8, trimmed, "host")) {
            return host();
        }
        var base_triple = trimmed;
        var override_simd: ?SimdLevel = null;
        if (std.mem.indexOfScalar(u8, trimmed, '+')) |plus_idx| {
            base_triple = trimmed[0..plus_idx];
            const feat_str = trimmed[plus_idx + 1 ..];
            if (std.mem.eql(u8, feat_str, "avx2")) {
                override_simd = .avx2;
            } else if (std.mem.eql(u8, feat_str, "avx512")) {
                override_simd = .avx512;
            } else if (std.mem.eql(u8, feat_str, "scalar") or std.mem.eql(u8, feat_str, "none")) {
                override_simd = .none;
            } else {
                return null;
            }
        }
        var spec = TARGET_TRIPLE_MAP.get(base_triple) orelse return null;
        if (override_simd) |simd_lvl| {
            if ((simd_lvl == .avx2 or simd_lvl == .avx512) and spec.arch != .x86_64) return null;
            spec.simd_level = simd_lvl;
        }
        return spec;
    }

    /// Parses `raw_triple` or emits `E0006` (`e0006_invalid_target_triple`) into `sink`.
    pub fn parseOrEmitInvalidTarget(
        raw_triple: []const u8,
        span: Span,
        sink: *DiagnosticSink,
    ) !?TargetSpec {
        if (parseTargetTriple(raw_triple)) |valid_spec| return valid_spec;
        const arena_alloc = sink.arena.asAllocator();
        const msg = try std.fmt.allocPrint(
            arena_alloc,
            "unsupported or malformed target triple `{s}`",
            .{raw_triple},
        );
        try sink.emit(.{
            .code = .e0006_invalid_target_triple,
            .severity = .err,
            .primary_span = span,
            .message = msg,
            .notes = &.{
                "help: supported targets are `x86_64-linux`, `x86_64-macos`, `x86_64-windows`, " ++
                    "`aarch64-linux`, `aarch64-macos`, `aarch64-windows`, and `wasm32-wasi`",
            },
        });
        return null;
    }
};

// ----------------- Layout & Niche Descriptors -----------------

/// Niche encoding classification inside `NicheSpec` (`DR-07`, `DR-09` §1.1, `[CRITICAL-04]`).
pub const NicheEncoding = enum(u8) {
    /// Type exposes no spare invalid bit-patterns (`0`).
    none = 0,
    /// Non-null pointer/reference/slice/closure (`0` at `byte_offset` is invalid).
    zero_niche = 1,
    /// Contiguous invalid unsigned scalar range `[invalid_first .. invalid_first + invalid_count - 1]`.
    high_range = 2,
};

/// 24-byte binary-exact niche descriptor (`@sizeOf == 24`, `@alignOf == 8`).
pub const NicheSpec = extern struct {
    /// Byte offset of the niche-bearing scalar or pointer within the enclosing type (`0..u32::MAX`).
    byte_offset: u32 = 0,
    /// Width of the niche-bearing scalar in bytes (`1`, `2`, `4`, or `8`; `0` when `.none`).
    scalar_bytes: u8 = 0,
    /// Niche encoding strategy (`1B`).
    encoding: NicheEncoding = .none,
    /// Explicit zero padding (`2B`).
    _pad: u16 = 0,
    /// First invalid unsigned bit-pattern in `[invalid_first .. invalid_first + invalid_count - 1]`.
    invalid_first: u64 = 0,
    /// Total count of contiguous invalid bit-patterns (`>= 1` when `encoding != .none`).
    invalid_count: u64 = 0,
};

/// Canonical sum-type in-memory discriminant layout (`[CRITICAL-04]`).
pub const SumReprKind = enum(u8) {
    /// Product, scalar, pointer, or array type (not a sum type).
    not_sum = 0,
    /// Uninhabited alternate branch (`Result[T, never]`), represented identically to `T`.
    transparent_ok = 1,
    /// Single-ZST-variant sum (`Option[T]`, `Result[T, unit]`, `Result[unit, E]`) folded into payload leaf niche.
    niche_single = 2,
    /// Canonical explicit integer tag at offset `0` followed by aligned union payload.
    explicit_tag = 3,
};

/// 1-byte bit-packed representation properties stored in `ResolvedTypeLayout.repr_flags_bits`.
pub const ReprFlags = packed struct(u8) {
    /// `true` if annotated with `@repr(C)`.
    is_repr_c: bool = false,
    /// `true` if annotated with `@packed`.
    is_packed: bool = false,
    /// `true` if annotated with `@cache_aligned`.
    is_cache_aligned: bool = false,
    /// `true` if annotated with `@zero_pad` (`DR-20` `D-01`).
    is_zero_pad: bool = false,
    /// `true` if `size_bytes == 0` (`unit`, empty struct/tuple, `[T; 0]`).
    is_zst: bool = false,
    /// `true` if unsized or symbolic (`!TypeLayout.is_sized`).
    is_unsized: bool = false,
    /// `true` if internal or tail alignment padding bytes exist inside this aggregate.
    has_padding: bool = false,
    /// `true` if this type is a `#soa [S; C]` array.
    is_soa: bool = false,
};

/// Resolved field/element descriptor stored in `TypeLayoutResolver.fields_by_decl`.
pub const ResolvedFieldLayout = struct {
    /// Logical source declaration ordinal (`0 .. F - 1`).
    decl_ordinal: u32,
    /// Physical memory emission index (`0 .. F - 1`) sorted by ascending `byte_offset`.
    phys_index: u32,
    /// Exact byte offset from the start of the enclosing `struct` or `tuple`.
    byte_offset: u64,
    /// Resolved byte size of this field.
    size_bytes: u64,
    /// Concrete substituted `TypeId` of this field.
    field_ty: TypeId,
    /// Effective `log2` alignment of this field (`0` when `@packed`).
    align_log2: u8,
};

/// Contiguous padding hole `[byte_offset .. byte_offset + byte_len)` inside a `struct` or `tuple`.
pub const PaddingSpan = struct {
    /// Starting byte offset of the padding hole.
    byte_offset: u64,
    /// Number of padding bytes (`>= 1`).
    byte_len: u64,
};

/// Detailed sum-type discriminant and payload layout metadata cached in `TypeLayoutResolver`.
pub const ResolvedSumDetail = struct {
    /// Sum representation strategy (`.transparent_ok`, `.niche_single`, or `.explicit_tag`).
    repr: SumReprKind,
    /// Width of the explicit discriminant tag at byte `0` (`0` unless `.explicit_tag`).
    tag_bytes: u8,
    /// Byte offset of the variant payload storage (`0` for `.transparent_ok` and `.niche_single`).
    payload_offset: u64,
    /// Discriminant ordinal of the ZST variant when `repr == .niche_single`.
    zst_discriminant: u32 = 0,
    /// Discriminant ordinal of the non-ZST payload variant when `repr == .niche_single` or `.transparent_ok`.
    payload_discriminant: u32 = 0,
    /// Non-ZST payload `TypeId` when `repr == .niche_single` or `.transparent_ok`.
    payload_ty: TypeId = .unit_ty,
    /// Active leaf niche descriptor when `repr == .niche_single`.
    niche: NicheSpec = .{},
};

/// 32-byte binary-exact resolved type layout record (`@sizeOf == 32`, `@alignOf == 8`).
pub const ResolvedTypeLayout = extern struct {
    /// Total in-memory size in bytes (including tail padding).
    size_bytes: u64,
    /// Array element stride in bytes (`alignUp(size_bytes, 1 << align_log2)`).
    stride_bytes: u64,
    /// Start index in `TypeLayoutResolver.fields_by_decl` and `phys_to_decl` (`0` for non-aggregates).
    aux_start: u32 = 0,
    /// Field or tuple-element count (`0` for non-aggregates).
    aux_len: u32 = 0,
    /// Index in `TypeLayoutResolver.niches` (`NO_NICHE_IDX` when the type has no niche).
    niche_idx: u32 = NO_NICHE_IDX,
    /// Base-2 logarithm of byte alignment (`align_bytes = 1 << align_log2`).
    align_log2: u8 = 0,
    /// Packed `ReprFlags` byte.
    repr_flags_bits: u8 = 0,
    /// Sum discriminant representation tag.
    sum_repr: SumReprKind = .not_sum,
    /// Register piece count (`0..4`) for direct scalar/pair/quad passing (`0xFF` when indirect).
    abi_piece_count: u8 = 0,

    /// Decodes `repr_flags_bits` into `ReprFlags`.
    pub inline fn reprFlags(self: ResolvedTypeLayout) ReprFlags {
        return @bitCast(self.repr_flags_bits);
    }

    /// Returns the alignment in bytes (`1 << align_log2`).
    pub inline fn alignBytes(self: ResolvedTypeLayout) u32 {
        return @as(u32, 1) << @intCast(self.align_log2);
    }

    /// Returns `true` when `size_bytes == 0`.
    pub inline fn isZst(self: ResolvedTypeLayout) bool {
        return self.size_bytes == 0;
    }

    /// Returns `true` when `niche_idx != NO_NICHE_IDX`.
    pub inline fn hasNiche(self: ResolvedTypeLayout) bool {
        return self.niche_idx != NO_NICHE_IDX;
    }
};

// ------------------ ABI Classification Types ------------------

/// Lowered machine calling convention (`DR-09` §1.1, `DR-20` `Fix-07`, `[CRITICAL-06]`).
pub const CallingConvKind = enum(u8) {
    /// Native CoreX `swiftcc` convention (`x86_64` / `aarch64`).
    cx_native = 0,
    /// Native CoreX fallible `swiftcc` + `swifterror` convention (`Fix-07`, `[CRITICAL-06]`).
    cx_result_cc = 1,
    /// Platform C ABI (`SysV AMD64`, `Win64`, `AAPCS64`, `Apple ARM64`).
    c_system = 2,
    /// WebAssembly `wasm32-wasi` MVP C/CoreX convention.
    wasm_mvp = 3,
};

/// Per-parameter or return value passing mode in `AbiParamRecipe`.
pub const AbiPassMode = enum(u8) {
    /// Zero-sized type (`unit`, empty struct) omitted from machine signature.
    ignore_zst = 0,
    /// Passed or returned directly in 1 scalar GPR or XMM/NEON/Wasm register.
    direct_scalar = 1,
    /// Passed or returned directly in 2 eightbyte registers (`9..16B` or `i128`).
    direct_pair = 2,
    /// Returned directly in 3 or 4 `i64` GPRs under `swiftcc` (`17..32B`).
    direct_quad = 3,
    /// Homogeneous Floating-Point Aggregate (`1..4` identical `f32`/`f64` lanes on `AAPCS64` / `Apple ARM64`).
    direct_hfa = 4,
    /// Passed via non-null pointer to caller storage (`&T` / `&mut T` / caller copy on `Win64`).
    indirect_by_ref = 5,
    /// Passed on the stack via LLVM `byval(T)` (`SysV AMD64` aggregates `> 16B`).
    indirect_byval = 6,
    /// Returned via hidden 1st `ptr noalias nonnull sret(T)` parameter.
    sret_ptr = 7,
    /// Hidden `ptr swifterror` slot in `cx_result_cc` (`R12` / `X21`, `[CRITICAL-06]`).
    swifterror_ptr = 8,
};

/// Target physical register bank class for direct scalar/pair/HFA pieces.
pub const RegBank = enum(u8) {
    /// Unused piece or memory-indirect slot.
    none = 0,
    /// General-purpose integer/pointer register bank (`RAX`/`RDI`/`RCX`, `X0`..`X7`, Wasm `i32`/`i64`).
    gpr = 1,
    /// Floating-point / SIMD vector bank (`XMM0`..`XMM7`, `V0`..`V7`, Wasm `f32`/`f64`/`v128`).
    xmm_vec = 2,
};

/// 1-byte bit-packed LLVM 20–23 parameter/return attributes stored in `AbiParamRecipe.attr_bits`.
pub const ParamAttrFlags = packed struct(u8) {
    /// `noalias` (proven disjoint by MVS `DR-02` / `DR-06`).
    is_noalias: bool = false,
    /// `nonnull` (CoreX references, `inout`/`set`/`sret`, or `Context*`).
    is_nonnull: bool = false,
    /// `noundef` (initialized scalar/pointer without unzeroed padding).
    is_noundef: bool = false,
    /// `readonly` (immutable `let` indirect borrow).
    is_readonly: bool = false,
    /// `writeonly` (`set` out-parameter or `sret` return slot).
    is_writeonly: bool = false,
    /// `nocapture` (non-escaping pointer proven by `FnRegionSummary`).
    is_nocapture: bool = false,
    /// `zeroext` (narrow unsigned integer / `bool` under `Apple ARM64` / `SysV` / `Wasm` C ABI).
    is_zext: bool = false,
    /// `signext` (narrow signed integer under `Apple ARM64` / `SysV` / `Wasm` C ABI).
    is_sext: bool = false,
};

/// 16-byte binary-exact parameter or return ABI lowering recipe (`@sizeOf == 16`, `@alignOf == 4`).
pub const AbiParamRecipe = extern struct {
    /// Lowered payload or `dereferenceable(N)` byte size (`0` for ZST).
    lowered_size_bytes: u32 = 0,
    /// Pointee or value alignment in bytes (`>= 1`).
    pointee_align_bytes: u32 = 1,
    /// Lowering mode (`ignore_zst`, `direct_*`, `indirect_*`, `sret_ptr`, `swifterror_ptr`).
    pass_mode: AbiPassMode = .ignore_zst,
    /// Primary register bank (piece `0`).
    bank_0: RegBank = .none,
    /// Secondary register bank (piece `1` for `direct_pair`).
    bank_1: RegBank = .none,
    /// Packed `ParamAttrFlags` bits.
    attr_bits: u8 = 0,
    /// Number of physical register pieces (`0..4`).
    piece_count: u8 = 0,
    /// Explicit zero padding (`3B`).
    _pad: [3]u8 = .{ 0, 0, 0 },

    /// Decodes `attr_bits` into `ParamAttrFlags`.
    pub inline fn attrs(self: AbiParamRecipe) ParamAttrFlags {
        return @bitCast(self.attr_bits);
    }
};

/// Error-channel encoding in `cx_result_cc` (`Fix-07`, `[CRITICAL-06]`).
pub const SwifterrorKind = enum(u8) {
    /// Function does not use `swifterror`.
    none = 0,
    /// `sizeof(E) == 0` (`.Err` encoded as `inttoptr (i64 1 to ptr)`).
    zst_err = 1,
    /// `1 <= sizeof(E) <= 7` (`.Err(e)` encoded as `inttoptr (((1 << 56) | zext_u64(e)) to ptr)`).
    tagged_int56 = 2,
    /// `sizeof(E) == 8` with `zero_niche` at offset `0` (`&U`, `&mut U`, `fn`; non-null pointer value IS `.Err`).
    nonnull_ptr = 3,
};

/// Formal parameter view consumed by `AbiClassifier.classifyFn` (depends solely on signature types/modes).
pub const FnParamSpec = struct {
    /// Concrete parameter `TypeId`.
    type_id: TypeId,
    /// CoreX parameter passing convention (`let_mode`, `inout_mode`, `set_mode`, `sink_mode`).
    mode: ParamMode = .let_mode,
    /// `true` when `FnRegionSummary` or MVS rules prove pointer does not escape (`nocapture`).
    is_non_escaping: bool = true,
};

/// Function signature view consumed by `AbiClassifier.classifyFn` (identical for direct and indirect calls).
pub const FnSignatureView = struct {
    /// Ordered formal parameter descriptors.
    params: []const FnParamSpec,
    /// Concrete return `TypeId`.
    ret_ty: TypeId,
    /// `true` for `extern "C"` / `@export` C-ABI functions.
    is_extern_c: bool = false,
    /// `true` when implicit `Context*` parameter is elided (`@no_alloc` / `contextless` / `D5` proven).
    is_contextless: bool = true,
};

/// Complete lowered machine calling-convention recipe for a function or indirect call site.
pub const AbiFnRecipe = struct {
    /// Selected machine calling convention.
    calling_conv: CallingConvKind,
    /// Return-channel recipe (holds `PackedOk(T)` when `calling_conv == .cx_result_cc`).
    ret_recipe: AbiParamRecipe,
    /// `true` if a hidden 1st `sret(T)` pointer parameter is prepended.
    has_sret: bool = false,
    /// Recipe for the hidden `sret(T)` parameter when `has_sret == true`.
    sret_recipe: AbiParamRecipe = .{},
    /// `true` if an implicit `Context*` pointer parameter is passed.
    has_implicit_context: bool = false,
    /// Recipe for the implicit `Context*` parameter when `has_implicit_context == true`.
    context_recipe: AbiParamRecipe = .{},
    /// `swifterror` encoding flavor (`.none` unless `calling_conv == .cx_result_cc`).
    swifterror_kind: SwifterrorKind = .none,
    /// Recipe for bare `ptr swifterror %_cx_err_slot` when `swifterror_kind != .none` (`[CRITICAL-06]`).
    swifterror_recipe: AbiParamRecipe = .{},
    /// Unwrapped `T` payload `TypeId` when `calling_conv == .cx_result_cc`.
    ok_ty: TypeId = .unit_ty,
    /// Unwrapped `E` error `TypeId` when `calling_conv == .cx_result_cc`.
    err_ty: TypeId = .unit_ty,
    /// Lowered formal parameter recipes (`params.len` entries, owned by `allocator`).
    param_recipes: []AbiParamRecipe,

    /// Releases `param_recipes` allocated by `AbiClassifier.classifyFn`.
    pub fn deinit(self: *AbiFnRecipe, allocator: std.mem.Allocator) void {
        allocator.free(self.param_recipes);
        self.* = undefined;
    }

    /// Computes a deterministic 64-bit `Wyhash(0)` signature digest for `CxGotSlotMeta.abi_sig_hash64`.
    pub fn abiSigHash64(self: *const AbiFnRecipe) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(&[_]u8{
            @backingInt(self.calling_conv),
            @intFromBool(self.has_sret),
            @intFromBool(self.has_implicit_context),
            @backingInt(self.swifterror_kind),
        });
        hasher.update(std.mem.asBytes(&self.ret_recipe));
        if (self.has_sret) hasher.update(std.mem.asBytes(&self.sret_recipe));
        if (self.has_implicit_context) hasher.update(std.mem.asBytes(&self.context_recipe));
        if (self.swifterror_kind != .none) hasher.update(std.mem.asBytes(&self.swifterror_recipe));
        hasher.update(std.mem.sliceAsBytes(self.param_recipes));
        return hasher.final();
    }
};

// ---------------- CodegenBackend Configuration ----------------

/// Optimization tier for Tier B LLVM 20–23 emission (`DR-09` §1.2).
pub const OptLevel = enum(u8) {
    /// Unoptimized fast debug emission (`-O0`).
    debug_o0 = 0,
    /// Standard production optimization (`-O2`).
    release_fast_o2 = 1,
    /// Aggressive loop/vector optimization (`-O3`).
    release_aggressive_o3 = 2,
    /// Code-size-minimized production optimization (`-Oz`).
    release_small_oz = 3,
};

/// Configuration for Tier A (`-ofmt=c` deterministic ISO C99 emitter + `zig cc` driver).
pub const CBackendConfig = struct {
    /// Target architecture, OS, and SIMD level.
    target: TargetSpec,
    /// `true` for `--release` (`-O2`), `false` for `--dev` (`-O0` + 16-slot `ErrorReturnTrace`).
    is_release_mode: bool = false,
    /// `true` when `--fuzz` `SanitizerCoverage` instrumentation is enabled.
    is_fuzz_instrumented: bool = false,
    /// `true` when `#line` source directives are emitted for DWARF debugging.
    has_line_directives: bool = true,
};

/// Configuration for Tier B (LLVM 20–23 `.ll` emitter + optional `corex_llvm` static C++20 bridge / `zig cc`).
pub const LlvmBackendConfig = struct {
    /// Target architecture, OS, and SIMD level.
    target: TargetSpec,
    /// Optimization pipeline level (`-O0`, `-O2`, `-O3`, `-Oz`).
    opt_level: OptLevel = .debug_o0,
    /// `true` for `--release`, `false` for `--dev` (`ErrorReturnTrace` + `.cx_dev_meta` seam).
    is_release_mode: bool = false,
    /// `true` when `--fuzz` `SanitizerCoverage` + Windows `.SCOV$*` shim are emitted.
    is_fuzz_instrumented: bool = false,
    /// `true` to prefer linked `-Dllvm-prefix` `corex_llvm` static bridge when compiled in.
    is_static_llvm_bridge_enabled: bool = false,
};

/// Requested output artifact form produced by `CodegenBackend.emitModule`.
pub const OutputArtifactKind = enum(u8) {
    /// Emit deterministic textual `.c` or `.ll` source in memory (and optionally write to `output_path`).
    source_text = 0,
    /// Emit relocatable `.o` / `.obj` / `.wasm` object file at `output_path`.
    object_file = 1,
    /// Compile and link a standalone native or WASI executable at `output_path`.
    executable = 2,
};

/// Owned result returned by `CodegenBackend.emitModule`.
pub const CodegenArtifact = struct {
    /// Deterministic emitted `.c` or `.ll` textual representation owned by `allocator`.
    emitted_text: []u8,
    /// Optional serialized `.cx_dev_meta` binary payload (`DR-19` Seam #3) owned by `allocator`.
    dev_seam_bytes: ?[]u8 = null,
    /// Optional path written on disk via `atomicWriteOutputFile` (`Prune-02`), owned by `allocator`.
    written_output_path: ?[]u8 = null,

    /// Releases all buffers owned by `self`.
    pub fn deinit(self: *CodegenArtifact, allocator: std.mem.Allocator) void {
        if (self.emitted_text.len > 0) allocator.free(self.emitted_text);
        if (self.dev_seam_bytes) |seam_buf| allocator.free(seam_buf);
        if (self.written_output_path) |path_buf| allocator.free(path_buf);
        self.* = undefined;
    }
};

/// Strongly typed input bundle consumed by Tier A and Tier B module emitters.
pub const CodegenModuleInput = struct {
    /// Lowered, SAST-elaborated, and optionally optimized `MirBody` functions.
    bodies: []const mir.MirBody,
    /// Shared `InternPool` type arena (may intern concrete instantiated field types during layout resolution).
    pool: *InternPool,
    /// Shared `SymbolTable`.
    sym_table: *const SymbolTable,
    /// Shared `StringInterner`.
    interner: *const StringInterner,
    /// Logical module identifier used for debug info and `.ll` header metadata.
    module_name: []const u8 = "corex_mod",
    /// Optional `VfsSourceMap` resolving `FileId` paths and line numbers for `#line` / DWARF v5 tables.
    vfs_source_map: ?*const vfs_sourcemap.VfsSourceMap = null,
    /// Optional map `FileId.asInt() -> *const TokenBuffer` resolving `TokenIndex` byte spans.
    file_tokens: ?*const std.AutoHashMapUnmanaged(u32, *const syntax_arenas.TokenBuffer) = null,
    /// Optional promoted `.rodata` constant pool (`MirVm`).
    rodata_pool: ?*const mir_vm.RodataPool = null,
    /// Optional pre-materialized `@embed_bytes` blob store (`[CRITICAL-07]`).
    blob_store: ?*const mir.MirBlobStore = null,
    /// Optional per-body Pentagon `ProvenValueRange` slices (`[MAJOR-08]`).
    proven_ranges: ?[]const []const ProvenValueRange = null,
    /// Optional interprocedural `FnSummaryStore` for `nocapture` / effect queries.
    summary_store: ?*const mir_sast.FnSummaryStore = null,
    /// `true` to emit `--dev` GOT function-pointer table indirection (`_cx_dev_got` + `.cx_dev_meta`).
    is_dev_got_enabled: bool = false,
    /// `true` to enable `COREX_ORACLE_TRACE_FILE` trap/drop/return instrumentation (`D-07A`).
    is_oracle_trace_enabled: bool = false,
    /// Requested output artifact kind (`.source_text`, `.object_file`, or `.executable`).
    artifact_kind: OutputArtifactKind = .source_text,
    /// Destination path on disk (required for `.object_file` and `.executable`).
    output_path: ?[]const u8 = null,
    /// Zig `Io` handle used for `zig cc` subprocesses and `atomicWriteOutputFile`.
    io: ?std.Io = null,
    /// Optional host environment map forwarded to `zig` driver lookup and `zig cc`.
    environ_map: ?*const std.process.Environ.Map = null,
    /// Optional `DiagnosticSink` receiving `E0007` / `E0008` diagnostics on backend or linker failure.
    diagnostic_sink: ?*DiagnosticSink = null,
};

/// Exhaustive tagged-union backend dispatcher with zero `*anyopaque` or `void*` (`AGENTS.md` §1, `[CRITICAL-09]`).
pub const CodegenBackend = union(enum) {
    /// Tier A deterministic ISO C99 backend (`-ofmt=c`).
    tier_a_c99: CBackendConfig,
    /// Tier B LLVM 20–23 `.ll` / static bridge backend.
    tier_b_llvm: LlvmBackendConfig,

    /// Returns the active `TargetSpec` of `self`.
    pub inline fn targetSpec(self: CodegenBackend) TargetSpec {
        return switch (self) {
            .tier_a_c99 => |cfg| cfg.target,
            .tier_b_llvm => |cfg| cfg.target,
        };
    }

    /// Returns `true` if `self` is configured for `--release` compilation.
    pub inline fn isReleaseMode(self: CodegenBackend) bool {
        return switch (self) {
            .tier_a_c99 => |cfg| cfg.is_release_mode,
            .tier_b_llvm => |cfg| cfg.is_release_mode,
        };
    }

    /// Dispatches `input` to Tier A (`codegen_c`) or Tier B (`codegen_llvm`) without dynamic vtables.
    pub fn emitModule(
        self: CodegenBackend,
        allocator: std.mem.Allocator,
        input: CodegenModuleInput,
    ) !CodegenArtifact {
        return switch (self) {
            .tier_a_c99 => |cfg| codegen_c.emitModule(allocator, cfg, input),
            .tier_b_llvm => |cfg| codegen_llvm.emitModule(allocator, cfg, input),
        };
    }
};

/// Lazy `zig` driver path resolver (`AGENTS.md` §2: zero eager startup probing).
pub const ZigDriverLocator = struct {
    /// Lazily resolved path owned by `allocator` (`null` until first `resolve` call).
    cached_path: ?[]u8 = null,

    /// Releases `cached_path` if previously resolved.
    pub fn deinit(self: *ZigDriverLocator, allocator: std.mem.Allocator) void {
        if (self.cached_path) |owned| allocator.free(owned);
        self.cached_path = null;
    }

    /// Resolves and caches the `zig` executable path on first invocation.
    pub fn resolve(
        self: *ZigDriverLocator,
        io: std.Io,
        allocator: std.mem.Allocator,
        environ_map: ?*const std.process.Environ.Map,
    ) ![]const u8 {
        if (self.cached_path) |existing| return existing;
        const found = try resolveZigExecutable(io, allocator, environ_map);
        self.cached_path = found;
        return found;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum recursive structural type-resolution depth in `TypeLayoutResolver.resolveTypeBounded`.
pub const MAX_LAYOUT_RESOLVE_DEPTH: u32 = 64;
/// Sentinel index indicating a type carries no `NicheSpec` (`0xFFFF_FFFF`).
pub const NO_NICHE_IDX: u32 = std.math.maxInt(u32);

/// Canonical list of all 7 supported Phase-7 `TargetSpec` targets.
pub const ALL_CANONICAL_TARGETS = [7]TargetSpec{
    TargetSpec.X86_64_LINUX,
    TargetSpec.X86_64_MACOS,
    TargetSpec.X86_64_WINDOWS,
    TargetSpec.AARCH64_LINUX,
    TargetSpec.AARCH64_MACOS,
    TargetSpec.AARCH64_WINDOWS,
    TargetSpec.WASM32_WASI,
};

/// $O(1)$ static lookup map from canonical and vendor-qualified target triples to `TargetSpec`.
const TARGET_TRIPLE_MAP = std.StaticStringMap(TargetSpec).initComptime(.{
    .{ "aarch64-apple-darwin", TargetSpec.AARCH64_MACOS },
    .{ "aarch64-apple-macos", TargetSpec.AARCH64_MACOS },
    .{ "aarch64-apple-macosx", TargetSpec.AARCH64_MACOS },
    .{ "aarch64-linux", TargetSpec.AARCH64_LINUX },
    .{ "aarch64-linux-gnu", TargetSpec.AARCH64_LINUX },
    .{ "aarch64-linux-musl", TargetSpec.AARCH64_LINUX },
    .{ "aarch64-macos", TargetSpec.AARCH64_MACOS },
    .{ "aarch64-macos-none", TargetSpec.AARCH64_MACOS },
    .{ "aarch64-pc-windows-gnu", TargetSpec.AARCH64_WINDOWS },
    .{ "aarch64-pc-windows-msvc", TargetSpec.AARCH64_WINDOWS },
    .{ "aarch64-unknown-linux-gnu", TargetSpec.AARCH64_LINUX },
    .{ "aarch64-unknown-linux-musl", TargetSpec.AARCH64_LINUX },
    .{ "aarch64-w64-windows-gnu", TargetSpec.AARCH64_WINDOWS },
    .{ "aarch64-windows", TargetSpec.AARCH64_WINDOWS },
    .{ "aarch64-windows-gnu", TargetSpec.AARCH64_WINDOWS },
    .{ "aarch64-windows-msvc", TargetSpec.AARCH64_WINDOWS },
    .{ "arm64-apple-darwin", TargetSpec.AARCH64_MACOS },
    .{ "arm64-apple-macos", TargetSpec.AARCH64_MACOS },
    .{ "arm64-macos", TargetSpec.AARCH64_MACOS },
    .{ "wasm32-unknown-wasi", TargetSpec.WASM32_WASI },
    .{ "wasm32-wasi", TargetSpec.WASM32_WASI },
    .{ "wasm32-wasip1", TargetSpec.WASM32_WASI },
    .{ "x86_64-apple-darwin", TargetSpec.X86_64_MACOS },
    .{ "x86_64-apple-macos", TargetSpec.X86_64_MACOS },
    .{ "x86_64-apple-macosx", TargetSpec.X86_64_MACOS },
    .{ "x86_64-linux", TargetSpec.X86_64_LINUX },
    .{ "x86_64-linux-gnu", TargetSpec.X86_64_LINUX },
    .{ "x86_64-linux-musl", TargetSpec.X86_64_LINUX },
    .{ "x86_64-macos", TargetSpec.X86_64_MACOS },
    .{ "x86_64-macos-none", TargetSpec.X86_64_MACOS },
    .{ "x86_64-pc-windows-gnu", TargetSpec.X86_64_WINDOWS },
    .{ "x86_64-pc-windows-msvc", TargetSpec.X86_64_WINDOWS },
    .{ "x86_64-unknown-linux-gnu", TargetSpec.X86_64_LINUX },
    .{ "x86_64-unknown-linux-musl", TargetSpec.X86_64_LINUX },
    .{ "x86_64-w64-windows-gnu", TargetSpec.X86_64_WINDOWS },
    .{ "x86_64-windows", TargetSpec.X86_64_WINDOWS },
    .{ "x86_64-windows-gnu", TargetSpec.X86_64_WINDOWS },
    .{ "x86_64-windows-msvc", TargetSpec.X86_64_WINDOWS },
});

// -------------------------------------- INTERNALS --------------------------------------

/// Monotonic process-wide sequence counter qualifying `atomicWriteOutputFile` temporary filenames.
var atomic_write_seq: std.atomic.Value(u64) = std.atomic.Value(u64).init(1);

/// Converts `type_system.LeafNicheInfo` into binary-exact `NicheSpec`.
fn leafNicheToSpec(leaf: type_system.LeafNicheInfo) NicheSpec {
    return switch (leaf.kind) {
        .none => .{},
        .zero_ptr => .{
            .byte_offset = leaf.byte_offset,
            .scalar_bytes = leaf.scalar_bytes,
            .encoding = .zero_niche,
            .invalid_first = leaf.invalid_first,
            .invalid_count = leaf.invalid_count,
        },
        .high_scalar_range => .{
            .byte_offset = leaf.byte_offset,
            .scalar_bytes = leaf.scalar_bytes,
            .encoding = .high_range,
            .invalid_first = leaf.invalid_first,
            .invalid_count = leaf.invalid_count,
        },
    };
}

/// Returns `true` if `ty` unwraps to a single IEEE-754 floating-point scalar (`f32` or `f64`).
fn isScalarFloatType(pool: *const InternPool, raw_ty: TypeId) bool {
    const unwrapped = pool.unwrapUnderlyingType(raw_ty);
    return unwrapped == .f32_ty or unwrapped == .f64_ty;
}

/// Returns `true` if `ty` unwraps to a narrow `< 32`-bit unsigned integer or `bool`.
fn isNarrowZeroExtType(pool: *const InternPool, raw_ty: TypeId) bool {
    const unwrapped = pool.unwrapUnderlyingType(raw_ty);
    return unwrapped == .bool_ty or unwrapped == .u8_ty or unwrapped == .u16_ty;
}

/// Returns `true` if `ty` unwraps to a narrow `< 32`-bit signed integer (`i8` or `i16`).
fn isNarrowSignExtType(pool: *const InternPool, raw_ty: TypeId) bool {
    const unwrapped = pool.unwrapUnderlyingType(raw_ty);
    return unwrapped == .i8_ty or unwrapped == .i16_ty;
}

/// Returns `true` if `ty` unwraps to a non-null single pointer (`&T`, `&mut T`, or `fn`).
fn isSingleNonNullPointerType(pool: *const InternPool, raw_ty: TypeId) bool {
    const unwrapped = pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped.isPrimitiveOrSentinel()) return false;
    const tag = pool.getNode(unwrapped).tag;
    return tag == .ref_ty or tag == .mut_ref_ty or tag == .fn_ty;
}

/// Detects an `AAPCS64` / `Apple ARM64` Homogeneous Floating-Point Aggregate (`1..4` identical `f32`/`f64` lanes).
const HfaInfo = struct {
    /// Scalar lane byte size (`4` for `f32`, `8` for `f64`).
    elem_bytes: u8,
    /// Total floating-point lane count (`1..4`).
    lane_count: u8,
};

/// Recursively inspects `raw_ty` to determine whether all leaf scalars form a valid `AAPCS64` `HFA`.
fn inspectAarch64HfaBounded(
    resolver: *TypeLayoutResolver,
    raw_ty: TypeId,
    depth: u32,
) !?HfaInfo {
    if (depth >= 16) return null;
    const unwrapped = resolver.pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped == .f32_ty) return .{ .elem_bytes = 4, .lane_count = 1 };
    if (unwrapped == .f64_ty) return .{ .elem_bytes = 8, .lane_count = 1 };
    if (unwrapped.isPrimitiveOrSentinel()) return null;

    const layout = try resolver.resolveTypeBounded(unwrapped, depth + 1);
    if (layout.size_bytes == 0 or layout.size_bytes > 32 or layout.reprFlags().is_packed) return null;
    const node = resolver.pool.getNode(unwrapped);
    switch (node.tag) {
        .array_ty => {
            if ((node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) != 0 or node.rhs == 0 or node.rhs > 4) return null;
            const elem_hfa = (try inspectAarch64HfaBounded(resolver, TypeId.fromInt(node.lhs), depth + 1)) orelse
                return null;
            const total_lanes: u16 = @as(u16, elem_hfa.lane_count) * @as(u16, @intCast(node.rhs));
            if (total_lanes == 0 or total_lanes > 4) return null;
            if (layout.size_bytes != @as(u64, total_lanes) * @as(u64, elem_hfa.elem_bytes)) return null;
            return .{ .elem_bytes = elem_hfa.elem_bytes, .lane_count = @intCast(total_lanes) };
        },
        .struct_ty, .tuple_ty => {
            const start = layout.aux_start;
            const len = layout.aux_len;
            if (len == 0) return null;
            var common_elem_bytes: u8 = 0;
            var total_lanes: u8 = 0;
            var fld_i: u32 = 0;
            while (fld_i < len) : (fld_i += 1) {
                const fld = resolver.fields_by_decl.items[start + fld_i];
                if (fld.size_bytes == 0) continue;
                const sub_hfa = (try inspectAarch64HfaBounded(resolver, fld.field_ty, depth + 1)) orelse return null;
                if (common_elem_bytes == 0) {
                    common_elem_bytes = sub_hfa.elem_bytes;
                } else if (common_elem_bytes != sub_hfa.elem_bytes) {
                    return null;
                }
                if (total_lanes + sub_hfa.lane_count > 4) return null;
                total_lanes += sub_hfa.lane_count;
            }
            if (total_lanes == 0 or layout.size_bytes != @as(u64, total_lanes) * @as(u64, common_elem_bytes)) {
                return null;
            }
            return .{ .elem_bytes = common_elem_bytes, .lane_count = total_lanes };
        },
        .union_ty => {
            const start = layout.aux_start;
            const len = layout.aux_len;
            if (len == 0) return null;
            var common_elem_bytes: u8 = 0;
            var max_lanes: u8 = 0;
            var fld_i: u32 = 0;
            while (fld_i < len) : (fld_i += 1) {
                const fld = resolver.fields_by_decl.items[start + fld_i];
                if (fld.size_bytes == 0) continue;
                const sub_hfa = (try inspectAarch64HfaBounded(resolver, fld.field_ty, depth + 1)) orelse return null;
                if (common_elem_bytes == 0) {
                    common_elem_bytes = sub_hfa.elem_bytes;
                } else if (common_elem_bytes != sub_hfa.elem_bytes) {
                    return null;
                }
                if (sub_hfa.lane_count > max_lanes) max_lanes = sub_hfa.lane_count;
            }
            if (max_lanes == 0 or max_lanes > 4 or
                layout.size_bytes != @as(u64, max_lanes) * @as(u64, common_elem_bytes))
            {
                return null;
            }
            return .{ .elem_bytes = common_elem_bytes, .lane_count = max_lanes };
        },
        else => return null,
    }
}

/// Merges `.gpr` across all `SysV AMD64` eightbytes overlapped by `[byte_offset .. byte_offset + byte_size)`.
inline fn mergeSysVGprSpan(byte_offset: u64, byte_size: u64, classes: *[2]RegBank) void {
    const start_eb: usize = @intCast(byte_offset / 8);
    const end_eb: usize = @intCast((byte_offset + byte_size + 7) / 8);
    var eb = start_eb;
    while (eb < end_eb and eb < 2) : (eb += 1) {
        classes[eb] = .gpr;
    }
}

/// Classifies the two eightbytes (`0..7` and `8..15`) of a `<= 16B` type under the `SysV AMD64` C ABI.
fn classifySysVAmd64EightbytesBounded(
    resolver: *TypeLayoutResolver,
    raw_ty: TypeId,
    byte_offset: u64,
    classes: *[2]RegBank,
    has_unaligned: *bool,
    depth: u32,
) !void {
    if (has_unaligned.*) return;
    if (depth >= 16) {
        has_unaligned.* = true;
        return;
    }
    const unwrapped = resolver.pool.unwrapUnderlyingType(raw_ty);
    const layout = try resolver.resolveTypeBounded(unwrapped, depth + 1);
    if (layout.size_bytes == 0) return;

    if (unwrapped == .f32_ty or unwrapped == .f64_ty) {
        if ((byte_offset & (@as(u64, layout.alignBytes()) - 1)) != 0) {
            has_unaligned.* = true;
            return;
        }
        const idx: usize = @intCast(byte_offset / 8);
        if (idx < 2 and classes[idx] == .none) {
            classes[idx] = .xmm_vec;
        }
        return;
    }
    if (unwrapped == .i128_ty or unwrapped == .u128_ty) {
        if ((byte_offset & 15) != 0) {
            has_unaligned.* = true;
            return;
        }
        mergeSysVGprSpan(byte_offset, layout.size_bytes, classes);
        return;
    }
    if (unwrapped.isPrimitive()) {
        if ((byte_offset & (@as(u64, layout.alignBytes()) - 1)) != 0) {
            has_unaligned.* = true;
            return;
        }
        mergeSysVGprSpan(byte_offset, layout.size_bytes, classes);
        return;
    }

    const node = resolver.pool.getNode(unwrapped);
    switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .fn_ty, .slice_ty, .soa_slice_ty, .closure_ty => {
            if ((byte_offset & (@as(u64, layout.alignBytes()) - 1)) != 0) {
                has_unaligned.* = true;
                return;
            }
            mergeSysVGprSpan(byte_offset, layout.size_bytes, classes);
        },
        .array_ty => {
            if ((node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) != 0) return;
            const elem_ty = TypeId.fromInt(node.lhs);
            const elem_layout = try resolver.resolveTypeBounded(elem_ty, depth + 1);
            var elem_i: u32 = 0;
            while (elem_i < node.rhs) : (elem_i += 1) {
                try classifySysVAmd64EightbytesBounded(
                    resolver,
                    elem_ty,
                    byte_offset + @as(u64, elem_i) * elem_layout.stride_bytes,
                    classes,
                    has_unaligned,
                    depth + 1,
                );
            }
        },
        .struct_ty, .tuple_ty => {
            if (layout.reprFlags().is_packed) {
                has_unaligned.* = true;
                return;
            }
            // Snapshot slice bounds in case recursive `resolveType` grows `fields_by_decl`:
            const start = layout.aux_start;
            const len = layout.aux_len;
            var fld_i: u32 = 0;
            while (fld_i < len) : (fld_i += 1) {
                const fld = resolver.fields_by_decl.items[start + fld_i];
                try classifySysVAmd64EightbytesBounded(
                    resolver,
                    fld.field_ty,
                    byte_offset + fld.byte_offset,
                    classes,
                    has_unaligned,
                    depth + 1,
                );
            }
        },
        .union_ty => {
            if (layout.reprFlags().is_packed or (byte_offset & (@as(u64, layout.alignBytes()) - 1)) != 0) {
                has_unaligned.* = true;
                return;
            }
            const start = layout.aux_start;
            const len = layout.aux_len;
            if (len == 0) {
                mergeSysVGprSpan(byte_offset, layout.size_bytes, classes);
                return;
            }
            var fld_i: u32 = 0;
            while (fld_i < len) : (fld_i += 1) {
                const fld = resolver.fields_by_decl.items[start + fld_i];
                try classifySysVAmd64EightbytesBounded(
                    resolver,
                    fld.field_ty,
                    byte_offset,
                    classes,
                    has_unaligned,
                    depth + 1,
                );
            }
        },
        else => {
            if ((byte_offset & (@as(u64, layout.alignBytes()) - 1)) != 0) {
                has_unaligned.* = true;
                return;
            }
            mergeSysVGprSpan(byte_offset, layout.size_bytes, classes);
        },
    }
}

/// Checks whether `raw_ty` unwraps to a single C scalar (`bool`, `i8..i64`, `f32..f64`, pointer, or 1-field wrapper).
fn unwrapWasmCSingleScalar(resolver: *TypeLayoutResolver, raw_ty: TypeId, depth: u32) !?TypeId {
    if (depth >= 16) return null;
    const unwrapped = resolver.pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped == .unit_ty or unwrapped == .never_ty or unwrapped == .i128_ty or unwrapped == .u128_ty) {
        return null;
    }
    if (unwrapped == .str_ty) return null;
    if (unwrapped.isPrimitive()) return unwrapped;
    switch (resolver.pool.getNode(unwrapped).tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .fn_ty => return unwrapped,
        .enum_ty => {
            const layout = try resolver.resolveTypeBounded(unwrapped, depth + 1);
            if (layout.sum_repr == .explicit_tag and layout.size_bytes <= 8) {
                if (resolver.sum_details.get(unwrapped.toU32())) |detail| {
                    if (layout.size_bytes == detail.tag_bytes) return .u32_ty;
                }
            }
            return null;
        },
        .struct_ty, .tuple_ty => {
            const layout = try resolver.resolveTypeBounded(unwrapped, depth + 1);
            if (layout.aux_len == 0 or layout.reprFlags().is_packed) return null;
            var single_ty: ?TypeId = null;
            const start = layout.aux_start;
            const len = layout.aux_len;
            var fld_i: u32 = 0;
            while (fld_i < len) : (fld_i += 1) {
                const fld = resolver.fields_by_decl.items[start + fld_i];
                if (fld.size_bytes == 0) continue;
                if (single_ty != null) return null;
                single_ty = fld.field_ty;
            }
            if (single_ty) |only_ty| {
                return unwrapWasmCSingleScalar(resolver, only_ty, depth + 1);
            }
            return null;
        },
        else => return null,
    }
}

/// Computes a non-zero process-local identifier for temporary output file naming without requiring `libc`.
fn computeProcessNonceTag() u32 {
    if (builtin.os.tag == .linux) {
        return @bitCast(std.os.linux.getpid());
    }
    return @truncate((@intFromPtr(&atomic_write_seq) >> 4) ^ 0xC0AE_7001);
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Frontend-unified layout, field-order, `#soa` column, and niche resolver (`DR-09` §1.1, `[CRITICAL-01]`–`[CRITICAL-04]`).
pub const TypeLayoutResolver = struct {
    /// Backing allocator owning cached layout, field, padding, and niche tables.
    allocator: std.mem.Allocator,
    /// Shared `InternPool` type arena.
    pool: *InternPool,
    /// Read-only `SymbolTable`.
    sym_table: *const SymbolTable,
    /// Target hardware/OS/SIMD specification.
    target_spec: TargetSpec,
    /// Derived `type_system.TargetLayout` (`ptr_byte_size`, `cache_line_align_log2`, `simd_align_log2`).
    target_layout: TargetLayout,
    /// Memoized `TypeId.toU32() -> ResolvedTypeLayout` cache.
    resolved_cache: std.AutoHashMapUnmanaged(u32, ResolvedTypeLayout) = .empty,
    /// Flat field/tuple-element records indexed in $O(1)$ by `aux_start + decl_ordinal`.
    fields_by_decl: std.ArrayListUnmanaged(ResolvedFieldLayout) = .empty,
    /// Flat physical-offset-ordered `decl_ordinal` permutation (`aux_start .. aux_start + aux_len`).
    phys_to_decl: std.ArrayListUnmanaged(u32) = .empty,
    /// Deduplicated or per-type `NicheSpec` arena indexed by `ResolvedTypeLayout.niche_idx`.
    niches: std.ArrayListUnmanaged(NicheSpec) = .empty,
    /// Detailed sum discriminant/payload metadata keyed by `TypeId.toU32()`.
    sum_details: std.AutoHashMapUnmanaged(u32, ResolvedSumDetail) = .empty,
    /// Contiguous pool of `PaddingSpan` intervals for `@zero_pad` C99/LLVM emission.
    padding_pool: std.ArrayListUnmanaged(PaddingSpan) = .empty,
    /// Per-type `[start .. start + len)` slice inside `padding_pool` keyed by `TypeId.toU32()`.
    padding_ranges: std.AutoHashMapUnmanaged(u32, struct { start: u32, len: u32 }) = .empty,

    /// Initializes a `TypeLayoutResolver` bound to `pool`, `sym_table`, and `target_spec`.
    pub fn init(
        allocator: std.mem.Allocator,
        pool: *InternPool,
        sym_table: *const SymbolTable,
        target_spec: TargetSpec,
    ) TypeLayoutResolver {
        return .{
            .allocator = allocator,
            .pool = pool,
            .sym_table = sym_table,
            .target_spec = target_spec,
            .target_layout = target_spec.asTargetLayout(),
        };
    }

    /// Releases all cached layout, field, niche, sum, and padding tables.
    pub fn deinit(self: *TypeLayoutResolver) void {
        self.resolved_cache.deinit(self.allocator);
        self.fields_by_decl.deinit(self.allocator);
        self.phys_to_decl.deinit(self.allocator);
        self.niches.deinit(self.allocator);
        self.sum_details.deinit(self.allocator);
        self.padding_pool.deinit(self.allocator);
        self.padding_ranges.deinit(self.allocator);
        self.* = undefined;
    }

    /// Resolves and caches the canonical 32-byte `ResolvedTypeLayout` for `raw_ty`.
    pub fn resolveType(self: *TypeLayoutResolver, raw_ty: TypeId) !ResolvedTypeLayout {
        return self.resolveTypeBounded(raw_ty, 0);
    }

    /// Depth-bounded (`MAX_LAYOUT_RESOLVE_DEPTH`) layout resolution helper.
    pub fn resolveTypeBounded(self: *TypeLayoutResolver, raw_ty: TypeId, depth: u32) !ResolvedTypeLayout {
        if (self.resolved_cache.get(raw_ty.toU32())) |cached| return cached;
        if (depth >= MAX_LAYOUT_RESOLVE_DEPTH) {
            return .{
                .size_bytes = 0,
                .stride_bytes = 0,
            };
        }

        const base_layout = type_system.computeTypeLayoutWithPool(
            self.pool,
            self.sym_table,
            raw_ty,
            self.target_layout,
        );
        const leaf_niche = type_system.computeLeafNiche(
            self.pool,
            self.sym_table,
            raw_ty,
            self.target_layout,
        );
        var niche_idx: u32 = NO_NICHE_IDX;
        if (leaf_niche.kind != .none) {
            niche_idx = @intCast(self.niches.items.len);
            try self.niches.append(self.allocator, leafNicheToSpec(leaf_niche));
        }

        var repr_flags: ReprFlags = .{
            .is_zst = base_layout.byte_size == 0,
            .is_unsized = !base_layout.is_sized,
        };
        var aux_start: u32 = 0;
        var aux_len: u32 = 0;
        var sum_repr: SumReprKind = .not_sum;

        const unwrapped = self.pool.unwrapUnderlyingType(raw_ty);
        if (!unwrapped.isPrimitiveOrSentinel()) {
            const node = self.pool.getNode(unwrapped);
            switch (node.tag) {
                .soa_array_ty => {
                    repr_flags.is_soa = true;
                },
                .tuple_ty => {
                    const elems = self.pool.getTupleElements(unwrapped);
                    try self.populateTupleFields(raw_ty, elems, base_layout.byte_size, &aux_start, &aux_len, &repr_flags);
                },
                .struct_ty => {
                    const sym_idx = SymbolIndex.fromInt(node.rhs);
                    if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) {
                        const st_sym = self.sym_table.getSymbol(sym_idx).*;
                        repr_flags.is_repr_c = st_sym.contract_flags.is_repr_c;
                        repr_flags.is_packed = st_sym.contract_flags.is_packed;
                        repr_flags.is_cache_aligned = st_sym.contract_flags.is_cache_aligned;
                        repr_flags.is_zero_pad = st_sym.contract_flags.is_zero_pad;
                        try self.populateStructFields(
                            raw_ty,
                            unwrapped,
                            st_sym,
                            base_layout.byte_size,
                            &aux_start,
                            &aux_len,
                            &repr_flags,
                        );
                    }
                },
                .union_ty => {
                    const sym_idx = SymbolIndex.fromInt(node.rhs);
                    if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) {
                        const un_sym = self.sym_table.getSymbol(sym_idx).*;
                        repr_flags.is_repr_c = un_sym.contract_flags.is_repr_c;
                        repr_flags.is_packed = un_sym.contract_flags.is_packed;
                        repr_flags.is_cache_aligned = un_sym.contract_flags.is_cache_aligned;
                        repr_flags.is_zero_pad = un_sym.contract_flags.is_zero_pad;
                        try self.populateUnionFields(
                            unwrapped,
                            un_sym,
                            &aux_start,
                            &aux_len,
                        );
                    }
                },
                .optional_ty, .result_ty, .enum_ty => {
                    if (node.tag == .enum_ty) {
                        const sym_idx = SymbolIndex.fromInt(node.rhs);
                        if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) {
                            const en_sym = self.sym_table.getSymbol(sym_idx).*;
                            repr_flags.is_cache_aligned = en_sym.contract_flags.is_cache_aligned;
                            repr_flags.is_zero_pad = en_sym.contract_flags.is_zero_pad;
                        }
                    }
                    const sum_mem = type_system.computeSumMemoryLayout(
                        self.pool,
                        self.sym_table,
                        unwrapped,
                        self.target_layout,
                    );
                    sum_repr = switch (sum_mem.repr) {
                        .transparent_ok => .transparent_ok,
                        .niche_single => .niche_single,
                        .explicit_tag => .explicit_tag,
                    };
                    const detail: ResolvedSumDetail = .{
                        .repr = sum_repr,
                        .tag_bytes = sum_mem.tag_bytes,
                        .payload_offset = sum_mem.payload_offset,
                        .zst_discriminant = sum_mem.zst_discriminant,
                        .payload_discriminant = sum_mem.payload_discriminant,
                        .payload_ty = sum_mem.payload_ty,
                        .niche = leafNicheToSpec(sum_mem.niche),
                    };
                    try self.sum_details.put(self.allocator, raw_ty.toU32(), detail);
                    if (raw_ty != unwrapped) {
                        try self.sum_details.put(self.allocator, unwrapped.toU32(), detail);
                    }
                },
                else => {},
            }
        }

        const ptr_sz: u64 = self.target_layout.ptr_byte_size;
        const piece_count: u8 = if (base_layout.byte_size == 0)
            0
        else if (base_layout.byte_size <= ptr_sz * 4)
            @intCast((base_layout.byte_size + ptr_sz - 1) / ptr_sz)
        else
            0xFF;

        const out_layout: ResolvedTypeLayout = .{
            .size_bytes = base_layout.byte_size,
            .stride_bytes = type_system.alignUpU64(base_layout.byte_size, base_layout.align_bytes),
            .aux_start = aux_start,
            .aux_len = aux_len,
            .niche_idx = niche_idx,
            .align_log2 = base_layout.align_log2,
            .repr_flags_bits = @bitCast(repr_flags),
            .sum_repr = sum_repr,
            .abi_piece_count = piece_count,
        };
        try self.resolved_cache.put(self.allocator, raw_ty.toU32(), out_layout);
        return out_layout;
    }

    /// Returns the $O(1)$ declaration-ordered `ResolvedFieldLayout` slice (`fields_by_decl[decl_ordinal]`).
    pub inline fn getFieldsByDecl(self: *const TypeLayoutResolver, layout: ResolvedTypeLayout) []const ResolvedFieldLayout {
        if (layout.aux_len == 0) return &.{};
        return self.fields_by_decl.items[layout.aux_start .. layout.aux_start + layout.aux_len];
    }

    /// Returns the physical-offset-ordered `decl_ordinal` slice (`0 .. F - 1` sorted by ascending `byte_offset`).
    pub inline fn getPhysicalFieldOrder(self: *const TypeLayoutResolver, layout: ResolvedTypeLayout) []const u32 {
        if (layout.aux_len == 0) return &.{};
        return self.phys_to_decl.items[layout.aux_start .. layout.aux_start + layout.aux_len];
    }

    /// Looks up field `decl_ordinal` of `raw_ty` in $O(1)$ time after resolving `raw_ty`.
    pub fn getFieldByDeclOrdinal(
        self: *TypeLayoutResolver,
        raw_ty: TypeId,
        decl_ordinal: u32,
    ) !?ResolvedFieldLayout {
        const layout = try self.resolveType(raw_ty);
        if (decl_ordinal >= layout.aux_len) return null;
        return self.fields_by_decl.items[layout.aux_start + decl_ordinal];
    }

    /// Returns the `NicheSpec` of `layout` (`.encoding == .none` when `layout.niche_idx == NO_NICHE_IDX`).
    pub inline fn getNicheSpec(self: *const TypeLayoutResolver, layout: ResolvedTypeLayout) NicheSpec {
        if (layout.niche_idx == NO_NICHE_IDX) return .{};
        return self.niches.items[layout.niche_idx];
    }

    /// Resolves `raw_ty` and returns its `ResolvedSumDetail` (`null` when `raw_ty` is not a sum type).
    pub fn getSumDetail(self: *TypeLayoutResolver, raw_ty: TypeId) !?ResolvedSumDetail {
        _ = try self.resolveType(raw_ty);
        return self.sum_details.get(raw_ty.toU32());
    }

    /// Resolves `raw_ty` and returns all inter-field and tail `PaddingSpan` intervals.
    pub fn getPaddingSpans(self: *TypeLayoutResolver, raw_ty: TypeId) ![]const PaddingSpan {
        _ = try self.resolveType(raw_ty);
        if (self.padding_ranges.get(raw_ty.toU32())) |rng| {
            return self.padding_pool.items[rng.start .. rng.start + rng.len];
        }
        return &.{};
    }

    /// Resolves `#soa [S; C]` column offset and alignment for `field_ordinal` (`[CRITICAL-03]`).
    pub fn getSoaColumnOffset(
        self: *const TypeLayoutResolver,
        elem_struct_ty: TypeId,
        field_ordinal: u32,
        capacity: u64,
    ) ?type_system.SoaColumnInfo {
        return type_system.computeSoaColumnInfoReadOnly(
            self.pool,
            self.sym_table,
            elem_struct_ty,
            capacity,
            field_ordinal,
            self.target_layout,
        );
    }

    /// Populates `fields_by_decl`, `phys_to_decl`, and `padding_pool` for a native-reordered `tuple`.
    fn populateTupleFields(
        self: *TypeLayoutResolver,
        owner_ty: TypeId,
        elems: []const u32,
        total_size: u64,
        aux_start_out: *u32,
        aux_len_out: *u32,
        repr_flags: *ReprFlags,
    ) !void {
        if (elems.len == 0) return;
        const count: u32 = @intCast(elems.len);
        var temp_by_decl = try self.allocator.alloc(ResolvedFieldLayout, elems.len);
        defer self.allocator.free(temp_by_decl);
        var temp_phys = try self.allocator.alloc(u32, elems.len);
        defer self.allocator.free(temp_phys);

        var rank_mask: u64 = 0;
        for (elems, 0..) |raw_elem, i| {
            const elem_ty = TypeId.fromInt(raw_elem);
            const elem_layout = type_system.computeTypeLayoutWithPool(
                self.pool,
                self.sym_table,
                elem_ty,
                self.target_layout,
            );
            const has_niche = type_system.computeLeafNiche(
                self.pool,
                self.sym_table,
                elem_ty,
                self.target_layout,
            ).kind != .none;
            const rank: u6 = (@as(u6, @intCast(@min(elem_layout.align_log2, 30))) << 1) | @intFromBool(has_niche);
            rank_mask |= (@as(u64, 1) << rank);
            temp_by_decl[i] = .{
                .decl_ordinal = @intCast(i),
                .phys_index = 0,
                .byte_offset = 0,
                .size_bytes = elem_layout.byte_size,
                .field_ty = elem_ty,
                .align_log2 = elem_layout.align_log2,
            };
        }

        const pad_start: u32 = @intCast(self.padding_pool.items.len);
        var cur_offset: u64 = 0;
        var phys_idx: u32 = 0;
        while (rank_mask != 0) {
            const top_rank: u6 = @intCast(63 - @clz(rank_mask));
            rank_mask &= ~(@as(u64, 1) << top_rank);
            for (elems, 0..) |raw_elem, i| {
                const elem_ty = TypeId.fromInt(raw_elem);
                const has_niche = type_system.computeLeafNiche(
                    self.pool,
                    self.sym_table,
                    elem_ty,
                    self.target_layout,
                ).kind != .none;
                const rank: u6 = (@as(u6, @intCast(@min(temp_by_decl[i].align_log2, 30))) << 1) |
                    @intFromBool(has_niche);
                if (rank != top_rank) continue;
                const align_bytes: u32 = @as(u32, 1) << @intCast(temp_by_decl[i].align_log2);
                const aligned_off = type_system.alignUpU64(cur_offset, align_bytes);
                if (aligned_off > cur_offset) {
                    try self.padding_pool.append(self.allocator, .{
                        .byte_offset = cur_offset,
                        .byte_len = aligned_off - cur_offset,
                    });
                }
                temp_by_decl[i].phys_index = phys_idx;
                temp_by_decl[i].byte_offset = aligned_off;
                temp_phys[phys_idx] = @intCast(i);
                phys_idx += 1;
                cur_offset = aligned_off +| temp_by_decl[i].size_bytes;
            }
        }
        if (total_size > cur_offset) {
            try self.padding_pool.append(self.allocator, .{
                .byte_offset = cur_offset,
                .byte_len = total_size - cur_offset,
            });
        }
        const pad_len: u32 = @intCast(self.padding_pool.items.len - pad_start);
        if (pad_len > 0) {
            repr_flags.has_padding = true;
            try self.padding_ranges.put(self.allocator, owner_ty.toU32(), .{ .start = pad_start, .len = pad_len });
        }

        aux_start_out.* = @intCast(self.fields_by_decl.items.len);
        aux_len_out.* = count;
        try self.fields_by_decl.appendSlice(self.allocator, temp_by_decl);
        try self.phys_to_decl.appendSlice(self.allocator, temp_phys);
    }

    /// Populates `fields_by_decl`, `phys_to_decl`, and `padding_pool` for a `@repr(C)`, `@packed`, or native `struct`.
    fn populateStructFields(
        self: *TypeLayoutResolver,
        owner_ty: TypeId,
        unwrapped_ty: TypeId,
        st_sym: SymbolRecord,
        total_size: u64,
        aux_start_out: *u32,
        aux_len_out: *u32,
        repr_flags: *ReprFlags,
    ) !void {
        if (st_sym.target_scope.isNone()) return;
        const members = self.sym_table.getScopeMembers(st_sym.target_scope);
        var field_count: usize = 0;
        for (members) |mem_idx| {
            if (self.sym_table.getSymbol(mem_idx).kind == .field_sym) field_count += 1;
        }
        if (field_count == 0) {
            if (total_size > 0) {
                const pad_start: u32 = @intCast(self.padding_pool.items.len);
                try self.padding_pool.append(self.allocator, .{ .byte_offset = 0, .byte_len = total_size });
                repr_flags.has_padding = true;
                try self.padding_ranges.put(self.allocator, owner_ty.toU32(), .{ .start = pad_start, .len = 1 });
            }
            return;
        }

        const subst = NominalTypeSubst.fromNominal(
            self.pool,
            self.sym_table,
            unwrapped_ty,
            st_sym,
            &NominalTypeSubst.EMPTY,
        );
        var temp_by_decl = try self.allocator.alloc(ResolvedFieldLayout, field_count);
        defer self.allocator.free(temp_by_decl);
        var temp_phys = try self.allocator.alloc(u32, field_count);
        defer self.allocator.free(temp_phys);
        var temp_has_niche = try self.allocator.alloc(bool, field_count);
        defer self.allocator.free(temp_has_niche);

        const is_packed = st_sym.contract_flags.is_packed;
        const is_decl_order = is_packed or st_sym.contract_flags.is_repr_c;

        var decl_ord: usize = 0;
        var rank_mask: u64 = 0;
        for (members) |mem_idx| {
            const mem_sym = self.sym_table.getSymbol(mem_idx).*;
            if (mem_sym.kind != .field_sym) continue;
            const subst_field_ty = try subst.applyMut(
                self.allocator,
                self.pool,
                mem_sym.type_id,
            );
            const fld_layout = type_system.computeTypeLayoutWithPool(
                self.pool,
                self.sym_table,
                subst_field_ty,
                self.target_layout,
            );
            const eff_log2: u8 = if (is_packed) 0 else fld_layout.align_log2;
            const has_niche = !is_packed and type_system.computeLeafNiche(
                self.pool,
                self.sym_table,
                subst_field_ty,
                self.target_layout,
            ).kind != .none;
            temp_has_niche[decl_ord] = has_niche;
            temp_by_decl[decl_ord] = .{
                .decl_ordinal = @intCast(decl_ord),
                .phys_index = 0,
                .byte_offset = 0,
                .size_bytes = fld_layout.byte_size,
                .field_ty = subst_field_ty,
                .align_log2 = eff_log2,
            };
            if (!is_decl_order) {
                const rank: u6 = (@as(u6, @intCast(@min(eff_log2, 30))) << 1) | @intFromBool(has_niche);
                rank_mask |= (@as(u64, 1) << rank);
            }
            decl_ord += 1;
        }

        const pad_start: u32 = @intCast(self.padding_pool.items.len);
        var cur_offset: u64 = 0;
        if (is_decl_order) {
            var i: usize = 0;
            while (i < field_count) : (i += 1) {
                const align_bytes: u32 = if (is_packed) 1 else (@as(u32, 1) << @intCast(temp_by_decl[i].align_log2));
                const aligned_off = type_system.alignUpU64(cur_offset, align_bytes);
                if (aligned_off > cur_offset) {
                    try self.padding_pool.append(self.allocator, .{
                        .byte_offset = cur_offset,
                        .byte_len = aligned_off - cur_offset,
                    });
                }
                temp_by_decl[i].phys_index = @intCast(i);
                temp_by_decl[i].byte_offset = aligned_off;
                temp_phys[i] = @intCast(i);
                cur_offset = aligned_off +| temp_by_decl[i].size_bytes;
            }
        } else {
            var phys_idx: u32 = 0;
            while (rank_mask != 0) {
                const top_rank: u6 = @intCast(63 - @clz(rank_mask));
                rank_mask &= ~(@as(u64, 1) << top_rank);
                var i: usize = 0;
                while (i < field_count) : (i += 1) {
                    const rank: u6 = (@as(u6, @intCast(@min(temp_by_decl[i].align_log2, 30))) << 1) |
                        @intFromBool(temp_has_niche[i]);
                    if (rank != top_rank) continue;
                    const align_bytes: u32 = @as(u32, 1) << @intCast(temp_by_decl[i].align_log2);
                    const aligned_off = type_system.alignUpU64(cur_offset, align_bytes);
                    if (aligned_off > cur_offset) {
                        try self.padding_pool.append(self.allocator, .{
                            .byte_offset = cur_offset,
                            .byte_len = aligned_off - cur_offset,
                        });
                    }
                    temp_by_decl[i].phys_index = phys_idx;
                    temp_by_decl[i].byte_offset = aligned_off;
                    temp_phys[phys_idx] = @intCast(i);
                    phys_idx += 1;
                    cur_offset = aligned_off +| temp_by_decl[i].size_bytes;
                }
            }
        }
        if (total_size > cur_offset) {
            try self.padding_pool.append(self.allocator, .{
                .byte_offset = cur_offset,
                .byte_len = total_size - cur_offset,
            });
        }
        const pad_len: u32 = @intCast(self.padding_pool.items.len - pad_start);
        if (pad_len > 0) {
            repr_flags.has_padding = true;
            try self.padding_ranges.put(self.allocator, owner_ty.toU32(), .{ .start = pad_start, .len = pad_len });
        }

        aux_start_out.* = @intCast(self.fields_by_decl.items.len);
        aux_len_out.* = @intCast(field_count);
        try self.fields_by_decl.appendSlice(self.allocator, temp_by_decl);
        try self.phys_to_decl.appendSlice(self.allocator, temp_phys);
    }

    /// Populates `fields_by_decl` and `phys_to_decl` (all at `byte_offset = 0`) for a `union`.
    fn populateUnionFields(
        self: *TypeLayoutResolver,
        unwrapped_ty: TypeId,
        un_sym: SymbolRecord,
        aux_start_out: *u32,
        aux_len_out: *u32,
    ) !void {
        if (un_sym.target_scope.isNone()) return;
        const members = self.sym_table.getScopeMembers(un_sym.target_scope);
        var field_count: usize = 0;
        for (members) |mem_idx| {
            if (self.sym_table.getSymbol(mem_idx).kind == .field_sym) field_count += 1;
        }
        if (field_count == 0) return;

        const subst = NominalTypeSubst.fromNominal(
            self.pool,
            self.sym_table,
            unwrapped_ty,
            un_sym,
            &NominalTypeSubst.EMPTY,
        );
        var temp_by_decl = try self.allocator.alloc(ResolvedFieldLayout, field_count);
        defer self.allocator.free(temp_by_decl);
        var temp_phys = try self.allocator.alloc(u32, field_count);
        defer self.allocator.free(temp_phys);

        const is_packed = un_sym.contract_flags.is_packed;
        var decl_ord: usize = 0;
        for (members) |mem_idx| {
            const mem_sym = self.sym_table.getSymbol(mem_idx).*;
            if (mem_sym.kind != .field_sym) continue;
            const subst_field_ty = try subst.applyMut(
                self.allocator,
                self.pool,
                mem_sym.type_id,
            );
            const fld_layout = type_system.computeTypeLayoutWithPool(
                self.pool,
                self.sym_table,
                subst_field_ty,
                self.target_layout,
            );
            temp_by_decl[decl_ord] = .{
                .decl_ordinal = @intCast(decl_ord),
                .phys_index = @intCast(decl_ord),
                .byte_offset = 0,
                .size_bytes = fld_layout.byte_size,
                .field_ty = subst_field_ty,
                .align_log2 = if (is_packed) 0 else fld_layout.align_log2,
            };
            temp_phys[decl_ord] = @intCast(decl_ord);
            decl_ord += 1;
        }

        aux_start_out.* = @intCast(self.fields_by_decl.items.len);
        aux_len_out.* = @intCast(field_count);
        try self.fields_by_decl.appendSlice(self.allocator, temp_by_decl);
        try self.phys_to_decl.appendSlice(self.allocator, temp_phys);
    }
};

/// Canonical machine calling-convention classifier (`cx_native`, `cx_result_cc`, `c_system`, `wasm_mvp`).
pub const AbiClassifier = struct {
    /// Classifies `sig` for `resolver.target_spec` using only signature types/modes (`DR-09` §1.1, `[CRITICAL-06]`).
    pub fn classifyFn(
        allocator: std.mem.Allocator,
        resolver: *TypeLayoutResolver,
        sig: FnSignatureView,
    ) !AbiFnRecipe {
        const target = resolver.target_spec;
        const param_recipes = try allocator.alloc(AbiParamRecipe, sig.params.len);
        errdefer allocator.free(param_recipes);

        if (target.isWasm()) {
            return classifyWasmMvpFn(resolver, sig, param_recipes);
        }
        if (sig.is_extern_c) {
            return classifyCSystemFn(resolver, sig, param_recipes);
        }
        return classifyCxNativeFn(resolver, sig, param_recipes);
    }

    /// Classifies native `x86_64` / `aarch64` CoreX functions (`cx_native` & `cx_result_cc` `Fix-07` / `[CRITICAL-06]`).
    fn classifyCxNativeFn(
        resolver: *TypeLayoutResolver,
        sig: FnSignatureView,
        param_recipes: []AbiParamRecipe,
    ) !AbiFnRecipe {
        var recipe: AbiFnRecipe = .{
            .calling_conv = .cx_native,
            .ret_recipe = .{},
            .param_recipes = param_recipes,
        };

        // [1] Implicit `Context*` parameter when `!sig.is_contextless`:
        if (!sig.is_contextless) {
            recipe.has_implicit_context = true;
            const ctx_attrs: ParamAttrFlags = .{
                .is_nonnull = true,
                .is_noundef = true,
                .is_nocapture = true,
            };
            recipe.context_recipe = .{
                .lowered_size_bytes = 32,
                .pointee_align_bytes = 8,
                .pass_mode = .indirect_by_ref,
                .bank_0 = .gpr,
                .attr_bits = @bitCast(ctx_attrs),
                .piece_count = 1,
            };
        }

        // [2] Check `[CRITICAL-06]` `cx_result_cc` (`swiftcc` + `swifterror`) eligibility:
        const unwrapped_ret = resolver.pool.unwrapUnderlyingType(sig.ret_ty);
        if (!unwrapped_ret.isPrimitiveOrSentinel() and resolver.pool.getNode(unwrapped_ret).tag == .result_ty) {
            const ret_node = resolver.pool.getNode(unwrapped_ret);
            const ok_ty = TypeId.fromInt(ret_node.lhs);
            const err_ty = TypeId.fromInt(ret_node.rhs);
            if (resolver.pool.unwrapUnderlyingType(err_ty) != .never_ty) {
                const ok_layout = try resolver.resolveType(ok_ty);
                const err_layout = try resolver.resolveType(err_ty);
                if (ok_layout.size_bytes <= 32) {
                    var swifterr_kind: SwifterrorKind = .none;
                    if (err_layout.size_bytes == 0) {
                        swifterr_kind = .zst_err;
                    } else if (err_layout.size_bytes >= 1 and err_layout.size_bytes <= 7) {
                        swifterr_kind = .tagged_int56;
                    } else if (err_layout.size_bytes == 8) {
                        const err_niche = resolver.getNicheSpec(err_layout);
                        if (err_niche.encoding == .zero_niche and
                            err_niche.byte_offset == 0 and
                            err_niche.scalar_bytes == 8)
                        {
                            swifterr_kind = .nonnull_ptr;
                        }
                    }
                    if (swifterr_kind != .none) {
                        recipe.calling_conv = .cx_result_cc;
                        recipe.swifterror_kind = swifterr_kind;
                        recipe.ok_ty = ok_ty;
                        recipe.err_ty = err_ty;
                        recipe.swifterror_recipe = .{
                            .lowered_size_bytes = 8,
                            .pointee_align_bytes = 8,
                            .pass_mode = .swifterror_ptr,
                            .bank_0 = .gpr,
                            .attr_bits = 0,
                            .piece_count = 1,
                        };
                        recipe.ret_recipe = classifyPackedSwiftReturn(resolver.pool, ok_ty, ok_layout);
                    }
                }
            }
        }

        // [3] Standard `cx_native` return classification (`<= 32B` in up to 4 GPRs, `> 32B` via `sret`):
        if (recipe.calling_conv == .cx_native) {
            const ret_layout = try resolver.resolveType(sig.ret_ty);
            if (ret_layout.size_bytes <= 32) {
                recipe.ret_recipe = classifyPackedSwiftReturn(resolver.pool, sig.ret_ty, ret_layout);
            } else {
                const sret_attrs: ParamAttrFlags = .{
                    .is_noalias = true,
                    .is_nonnull = true,
                    .is_noundef = true,
                    .is_writeonly = true,
                    .is_nocapture = true,
                };
                const clamped_sz: u32 = @intCast(@min(ret_layout.size_bytes, std.math.maxInt(u32)));
                recipe.has_sret = true;
                recipe.sret_recipe = .{
                    .lowered_size_bytes = clamped_sz,
                    .pointee_align_bytes = ret_layout.alignBytes(),
                    .pass_mode = .sret_ptr,
                    .bank_0 = .gpr,
                    .attr_bits = @bitCast(sret_attrs),
                    .piece_count = 1,
                };
                recipe.ret_recipe = recipe.sret_recipe;
            }
        }

        // [4] Formal parameter classification (`DR-09` §1.1 & `phase7_spec.md` §2.3):
        for (sig.params, 0..) |param, i| {
            const p_layout = try resolver.resolveType(param.type_id);
            if (p_layout.size_bytes == 0) {
                param_recipes[i] = .{ .pointee_align_bytes = p_layout.alignBytes(), .pass_mode = .ignore_zst };
                continue;
            }
            const clamped_sz: u32 = @intCast(@min(p_layout.size_bytes, std.math.maxInt(u32)));
            if (param.mode == .inout_mode or param.mode == .set_mode) {
                const mut_attrs: ParamAttrFlags = .{
                    .is_noalias = true,
                    .is_nonnull = true,
                    .is_noundef = true,
                    .is_writeonly = (param.mode == .set_mode),
                    .is_nocapture = param.is_non_escaping,
                };
                param_recipes[i] = .{
                    .lowered_size_bytes = clamped_sz,
                    .pointee_align_bytes = p_layout.alignBytes(),
                    .pass_mode = .indirect_by_ref,
                    .bank_0 = .gpr,
                    .attr_bits = @bitCast(mut_attrs),
                    .piece_count = 1,
                };
                continue;
            }
            if (p_layout.size_bytes <= 8) {
                const is_flt = isScalarFloatType(resolver.pool, param.type_id);
                const val_attrs: ParamAttrFlags = .{
                    .is_nonnull = isSingleNonNullPointerType(resolver.pool, param.type_id),
                    .is_noundef = !p_layout.reprFlags().has_padding,
                };
                param_recipes[i] = .{
                    .lowered_size_bytes = clamped_sz,
                    .pointee_align_bytes = p_layout.alignBytes(),
                    .pass_mode = .direct_scalar,
                    .bank_0 = if (is_flt) .xmm_vec else .gpr,
                    .attr_bits = @bitCast(val_attrs),
                    .piece_count = 1,
                };
            } else if (p_layout.size_bytes <= 16) {
                const pair_attrs: ParamAttrFlags = .{
                    .is_noundef = !p_layout.reprFlags().has_padding,
                };
                param_recipes[i] = .{
                    .lowered_size_bytes = clamped_sz,
                    .pointee_align_bytes = p_layout.alignBytes(),
                    .pass_mode = .direct_pair,
                    .bank_0 = .gpr,
                    .bank_1 = .gpr,
                    .attr_bits = @bitCast(pair_attrs),
                    .piece_count = 2,
                };
            } else {
                const ref_attrs: ParamAttrFlags = .{
                    .is_noalias = true,
                    .is_nonnull = true,
                    .is_noundef = true,
                    .is_readonly = (param.mode == .let_mode),
                    .is_nocapture = param.is_non_escaping,
                };
                param_recipes[i] = .{
                    .lowered_size_bytes = clamped_sz,
                    .pointee_align_bytes = p_layout.alignBytes(),
                    .pass_mode = .indirect_by_ref,
                    .bank_0 = .gpr,
                    .attr_bits = @bitCast(ref_attrs),
                    .piece_count = 1,
                };
            }
        }
        return recipe;
    }

    /// Classifies `PackedOk(T)` or `<= 32B` `swiftcc` return values (`[CRITICAL-06]`: `<= 4` registers).
    fn classifyPackedSwiftReturn(
        pool: *const InternPool,
        ret_ty: TypeId,
        ret_layout: ResolvedTypeLayout,
    ) AbiParamRecipe {
        if (ret_layout.size_bytes == 0) {
            return .{ .pointee_align_bytes = ret_layout.alignBytes(), .pass_mode = .ignore_zst };
        }
        const clamped_sz: u32 = @intCast(ret_layout.size_bytes);
        const ret_attrs: ParamAttrFlags = .{
            .is_nonnull = isSingleNonNullPointerType(pool, ret_ty),
            .is_noundef = !ret_layout.reprFlags().has_padding,
        };
        if (ret_layout.size_bytes <= 8) {
            const is_flt = isScalarFloatType(pool, ret_ty);
            return .{
                .lowered_size_bytes = clamped_sz,
                .pointee_align_bytes = ret_layout.alignBytes(),
                .pass_mode = .direct_scalar,
                .bank_0 = if (is_flt) .xmm_vec else .gpr,
                .attr_bits = @bitCast(ret_attrs),
                .piece_count = 1,
            };
        }
        if (ret_layout.size_bytes <= 16) {
            return .{
                .lowered_size_bytes = clamped_sz,
                .pointee_align_bytes = ret_layout.alignBytes(),
                .pass_mode = .direct_pair,
                .bank_0 = .gpr,
                .bank_1 = .gpr,
                .attr_bits = @bitCast(ret_attrs),
                .piece_count = 2,
            };
        }
        const words: u8 = @intCast((ret_layout.size_bytes + 7) / 8);
        return .{
            .lowered_size_bytes = clamped_sz,
            .pointee_align_bytes = ret_layout.alignBytes(),
            .pass_mode = .direct_quad,
            .bank_0 = .gpr,
            .bank_1 = .gpr,
            .attr_bits = @bitCast(ret_attrs),
            .piece_count = words,
        };
    }

    /// Classifies `extern "C"` functions for `SysV AMD64`, `Win64`, `AAPCS64`, and `Apple ARM64`.
    fn classifyCSystemFn(
        resolver: *TypeLayoutResolver,
        sig: FnSignatureView,
        param_recipes: []AbiParamRecipe,
    ) !AbiFnRecipe {
        const target = resolver.target_spec;
        var recipe: AbiFnRecipe = .{
            .calling_conv = .c_system,
            .ret_recipe = .{},
            .param_recipes = param_recipes,
        };

        // [1] Classify C return type:
        const ret_layout = try resolver.resolveType(sig.ret_ty);
        if (ret_layout.size_bytes == 0) {
            recipe.ret_recipe = .{ .pointee_align_bytes = ret_layout.alignBytes(), .pass_mode = .ignore_zst };
        } else if (target.arch == .x86_64 and target.os == .windows) {
            const sz = ret_layout.size_bytes;
            if (sz == 1 or sz == 2 or sz == 4 or sz == 8) {
                const is_flt = isScalarFloatType(resolver.pool, sig.ret_ty);
                recipe.ret_recipe = .{
                    .lowered_size_bytes = @intCast(sz),
                    .pointee_align_bytes = ret_layout.alignBytes(),
                    .pass_mode = .direct_scalar,
                    .bank_0 = if (is_flt) .xmm_vec else .gpr,
                    .piece_count = 1,
                };
            } else {
                populateCSret(&recipe, ret_layout);
            }
        } else if (target.arch == .aarch64) {
            if (try inspectAarch64HfaBounded(resolver, sig.ret_ty, 0)) |hfa| {
                recipe.ret_recipe = .{
                    .lowered_size_bytes = @intCast(ret_layout.size_bytes),
                    .pointee_align_bytes = ret_layout.alignBytes(),
                    .pass_mode = .direct_hfa,
                    .bank_0 = .xmm_vec,
                    .piece_count = hfa.lane_count,
                };
            } else if (ret_layout.size_bytes <= 8) {
                var ext_attrs: ParamAttrFlags = .{};
                if (target.isDarwin()) {
                    ext_attrs.is_zext = isNarrowZeroExtType(resolver.pool, sig.ret_ty);
                    ext_attrs.is_sext = isNarrowSignExtType(resolver.pool, sig.ret_ty);
                }
                recipe.ret_recipe = .{
                    .lowered_size_bytes = @intCast(ret_layout.size_bytes),
                    .pointee_align_bytes = ret_layout.alignBytes(),
                    .pass_mode = .direct_scalar,
                    .bank_0 = if (isScalarFloatType(resolver.pool, sig.ret_ty)) .xmm_vec else .gpr,
                    .attr_bits = @bitCast(ext_attrs),
                    .piece_count = 1,
                };
            } else if (ret_layout.size_bytes <= 16) {
                recipe.ret_recipe = .{
                    .lowered_size_bytes = @intCast(ret_layout.size_bytes),
                    .pointee_align_bytes = ret_layout.alignBytes(),
                    .pass_mode = .direct_pair,
                    .bank_0 = .gpr,
                    .bank_1 = .gpr,
                    .piece_count = 2,
                };
            } else {
                populateCSret(&recipe, ret_layout);
            }
        } else {
            // `SysV AMD64` (`x86_64-linux` / `x86_64-macos`):
            if (ret_layout.size_bytes <= 16) {
                var classes: [2]RegBank = .{ .none, .none };
                var has_unaligned = false;
                try classifySysVAmd64EightbytesBounded(resolver, sig.ret_ty, 0, &classes, &has_unaligned, 0);
                if (has_unaligned) {
                    populateCSret(&recipe, ret_layout);
                } else {
                    const ext_attrs: ParamAttrFlags = .{
                        .is_zext = isNarrowZeroExtType(resolver.pool, sig.ret_ty),
                        .is_sext = isNarrowSignExtType(resolver.pool, sig.ret_ty),
                    };
                    const is_two = ret_layout.size_bytes > 8;
                    recipe.ret_recipe = .{
                        .lowered_size_bytes = @intCast(ret_layout.size_bytes),
                        .pointee_align_bytes = ret_layout.alignBytes(),
                        .pass_mode = if (is_two) .direct_pair else .direct_scalar,
                        .bank_0 = if (classes[0] == .none) .gpr else classes[0],
                        .bank_1 = if (is_two) (if (classes[1] == .none) .gpr else classes[1]) else .none,
                        .attr_bits = @bitCast(ext_attrs),
                        .piece_count = if (is_two) 2 else 1,
                    };
                }
            } else {
                populateCSret(&recipe, ret_layout);
            }
        }

        // [2] Classify C parameters:
        for (sig.params, 0..) |param, i| {
            const p_layout = try resolver.resolveType(param.type_id);
            if (p_layout.size_bytes == 0) {
                param_recipes[i] = .{ .pointee_align_bytes = p_layout.alignBytes(), .pass_mode = .ignore_zst };
                continue;
            }
            const clamped_sz: u32 = @intCast(@min(p_layout.size_bytes, std.math.maxInt(u32)));
            if (param.mode == .inout_mode or param.mode == .set_mode) {
                const ptr_attrs: ParamAttrFlags = .{ .is_nonnull = true, .is_noundef = true };
                param_recipes[i] = .{
                    .lowered_size_bytes = clamped_sz,
                    .pointee_align_bytes = p_layout.alignBytes(),
                    .pass_mode = .indirect_by_ref,
                    .bank_0 = .gpr,
                    .attr_bits = @bitCast(ptr_attrs),
                    .piece_count = 1,
                };
                continue;
            }
            if (target.arch == .x86_64 and target.os == .windows) {
                const sz = p_layout.size_bytes;
                if (sz == 1 or sz == 2 or sz == 4 or sz == 8) {
                    param_recipes[i] = .{
                        .lowered_size_bytes = @intCast(sz),
                        .pointee_align_bytes = p_layout.alignBytes(),
                        .pass_mode = .direct_scalar,
                        .bank_0 = if (isScalarFloatType(resolver.pool, param.type_id)) .xmm_vec else .gpr,
                        .piece_count = 1,
                    };
                } else {
                    const win_ref_attrs: ParamAttrFlags = .{ .is_nonnull = true, .is_noundef = true };
                    param_recipes[i] = .{
                        .lowered_size_bytes = clamped_sz,
                        .pointee_align_bytes = p_layout.alignBytes(),
                        .pass_mode = .indirect_by_ref,
                        .bank_0 = .gpr,
                        .attr_bits = @bitCast(win_ref_attrs),
                        .piece_count = 1,
                    };
                }
            } else if (target.arch == .aarch64) {
                if (try inspectAarch64HfaBounded(resolver, param.type_id, 0)) |hfa| {
                    param_recipes[i] = .{
                        .lowered_size_bytes = clamped_sz,
                        .pointee_align_bytes = p_layout.alignBytes(),
                        .pass_mode = .direct_hfa,
                        .bank_0 = .xmm_vec,
                        .piece_count = hfa.lane_count,
                    };
                } else if (p_layout.size_bytes <= 8) {
                    var ext_attrs: ParamAttrFlags = .{};
                    if (target.isDarwin()) {
                        ext_attrs.is_zext = isNarrowZeroExtType(resolver.pool, param.type_id);
                        ext_attrs.is_sext = isNarrowSignExtType(resolver.pool, param.type_id);
                    }
                    param_recipes[i] = .{
                        .lowered_size_bytes = clamped_sz,
                        .pointee_align_bytes = p_layout.alignBytes(),
                        .pass_mode = .direct_scalar,
                        .bank_0 = if (isScalarFloatType(resolver.pool, param.type_id)) .xmm_vec else .gpr,
                        .attr_bits = @bitCast(ext_attrs),
                        .piece_count = 1,
                    };
                } else if (p_layout.size_bytes <= 16) {
                    param_recipes[i] = .{
                        .lowered_size_bytes = clamped_sz,
                        .pointee_align_bytes = p_layout.alignBytes(),
                        .pass_mode = .direct_pair,
                        .bank_0 = .gpr,
                        .bank_1 = .gpr,
                        .piece_count = 2,
                    };
                } else {
                    const arm_ref_attrs: ParamAttrFlags = .{ .is_nonnull = true, .is_noundef = true };
                    param_recipes[i] = .{
                        .lowered_size_bytes = clamped_sz,
                        .pointee_align_bytes = p_layout.alignBytes(),
                        .pass_mode = .indirect_by_ref,
                        .bank_0 = .gpr,
                        .attr_bits = @bitCast(arm_ref_attrs),
                        .piece_count = 1,
                    };
                }
            } else {
                // `SysV AMD64` (`x86_64-linux` / `x86_64-macos`):
                if (p_layout.size_bytes <= 16) {
                    var classes: [2]RegBank = .{ .none, .none };
                    var has_unaligned = false;
                    try classifySysVAmd64EightbytesBounded(resolver, param.type_id, 0, &classes, &has_unaligned, 0);
                    if (has_unaligned) {
                        param_recipes[i] = .{
                            .lowered_size_bytes = clamped_sz,
                            .pointee_align_bytes = @max(p_layout.alignBytes(), 8),
                            .pass_mode = .indirect_byval,
                            .piece_count = 0,
                        };
                    } else {
                        const ext_attrs: ParamAttrFlags = .{
                            .is_zext = isNarrowZeroExtType(resolver.pool, param.type_id),
                            .is_sext = isNarrowSignExtType(resolver.pool, param.type_id),
                        };
                        const is_two = p_layout.size_bytes > 8;
                        param_recipes[i] = .{
                            .lowered_size_bytes = clamped_sz,
                            .pointee_align_bytes = p_layout.alignBytes(),
                            .pass_mode = if (is_two) .direct_pair else .direct_scalar,
                            .bank_0 = if (classes[0] == .none) .gpr else classes[0],
                            .bank_1 = if (is_two) (if (classes[1] == .none) .gpr else classes[1]) else .none,
                            .attr_bits = @bitCast(ext_attrs),
                            .piece_count = if (is_two) 2 else 1,
                        };
                    }
                } else {
                    param_recipes[i] = .{
                        .lowered_size_bytes = clamped_sz,
                        .pointee_align_bytes = @max(p_layout.alignBytes(), 8),
                        .pass_mode = .indirect_byval,
                        .piece_count = 0,
                    };
                }
            }
        }
        return recipe;
    }

    /// Populates `has_sret` and `sret_recipe` for C-ABI indirect aggregate returns.
    fn populateCSret(recipe: *AbiFnRecipe, ret_layout: ResolvedTypeLayout) void {
        const sret_attrs: ParamAttrFlags = .{
            .is_noalias = true,
            .is_nonnull = true,
            .is_noundef = true,
            .is_writeonly = true,
            .is_nocapture = true,
        };
        const clamped_sz: u32 = @intCast(@min(ret_layout.size_bytes, std.math.maxInt(u32)));
        recipe.has_sret = true;
        recipe.sret_recipe = .{
            .lowered_size_bytes = clamped_sz,
            .pointee_align_bytes = ret_layout.alignBytes(),
            .pass_mode = .sret_ptr,
            .bank_0 = .gpr,
            .attr_bits = @bitCast(sret_attrs),
            .piece_count = 1,
        };
        recipe.ret_recipe = recipe.sret_recipe;
    }

    /// Classifies `wasm32-wasi` functions under the WebAssembly MVP ABI (`swifterror` disabled per `[CRITICAL-06]`).
    fn classifyWasmMvpFn(
        resolver: *TypeLayoutResolver,
        sig: FnSignatureView,
        param_recipes: []AbiParamRecipe,
    ) !AbiFnRecipe {
        var recipe: AbiFnRecipe = .{
            .calling_conv = .wasm_mvp,
            .ret_recipe = .{},
            .param_recipes = param_recipes,
        };

        if (!sig.is_extern_c and !sig.is_contextless) {
            recipe.has_implicit_context = true;
            const ctx_attrs: ParamAttrFlags = .{
                .is_nonnull = true,
                .is_noundef = true,
                .is_nocapture = true,
            };
            recipe.context_recipe = .{
                .lowered_size_bytes = 16,
                .pointee_align_bytes = 4,
                .pass_mode = .indirect_by_ref,
                .bank_0 = .gpr,
                .attr_bits = @bitCast(ctx_attrs),
                .piece_count = 1,
            };
        }

        const ret_layout = try resolver.resolveType(sig.ret_ty);
        const unwrapped_ret = resolver.pool.unwrapUnderlyingType(sig.ret_ty);
        if (ret_layout.size_bytes == 0) {
            recipe.ret_recipe = .{ .pointee_align_bytes = ret_layout.alignBytes(), .pass_mode = .ignore_zst };
        } else if (sig.is_extern_c) {
            if (try unwrapWasmCSingleScalar(resolver, sig.ret_ty, 0)) |scalar_ty| {
                const ext_attrs: ParamAttrFlags = .{
                    .is_zext = isNarrowZeroExtType(resolver.pool, scalar_ty),
                    .is_sext = isNarrowSignExtType(resolver.pool, scalar_ty),
                };
                recipe.ret_recipe = .{
                    .lowered_size_bytes = @intCast(ret_layout.size_bytes),
                    .pointee_align_bytes = ret_layout.alignBytes(),
                    .pass_mode = .direct_scalar,
                    .bank_0 = if (isScalarFloatType(resolver.pool, scalar_ty)) .xmm_vec else .gpr,
                    .attr_bits = @bitCast(ext_attrs),
                    .piece_count = 1,
                };
            } else {
                populateCSret(&recipe, ret_layout);
            }
        } else if (ret_layout.size_bytes <= 8) {
            recipe.ret_recipe = .{
                .lowered_size_bytes = @intCast(ret_layout.size_bytes),
                .pointee_align_bytes = ret_layout.alignBytes(),
                .pass_mode = .direct_scalar,
                .bank_0 = if (isScalarFloatType(resolver.pool, unwrapped_ret)) .xmm_vec else .gpr,
                .piece_count = 1,
            };
        } else {
            populateCSret(&recipe, ret_layout);
        }

        for (sig.params, 0..) |param, i| {
            const p_layout = try resolver.resolveType(param.type_id);
            if (p_layout.size_bytes == 0) {
                param_recipes[i] = .{ .pointee_align_bytes = p_layout.alignBytes(), .pass_mode = .ignore_zst };
                continue;
            }
            const clamped_sz: u32 = @intCast(@min(p_layout.size_bytes, std.math.maxInt(u32)));
            if (param.mode == .inout_mode or param.mode == .set_mode) {
                const mut_attrs: ParamAttrFlags = .{
                    .is_noalias = !sig.is_extern_c,
                    .is_nonnull = true,
                    .is_noundef = true,
                    .is_writeonly = (param.mode == .set_mode),
                    .is_nocapture = param.is_non_escaping,
                };
                param_recipes[i] = .{
                    .lowered_size_bytes = clamped_sz,
                    .pointee_align_bytes = p_layout.alignBytes(),
                    .pass_mode = .indirect_by_ref,
                    .bank_0 = .gpr,
                    .attr_bits = @bitCast(mut_attrs),
                    .piece_count = 1,
                };
                continue;
            }
            const unwrapped_p = resolver.pool.unwrapUnderlyingType(param.type_id);
            if (sig.is_extern_c) {
                if (unwrapped_p == .i128_ty or unwrapped_p == .u128_ty) {
                    param_recipes[i] = .{
                        .lowered_size_bytes = 16,
                        .pointee_align_bytes = p_layout.alignBytes(),
                        .pass_mode = .direct_pair,
                        .bank_0 = .gpr,
                        .bank_1 = .gpr,
                        .piece_count = 2,
                    };
                } else if (try unwrapWasmCSingleScalar(resolver, param.type_id, 0)) |scalar_ty| {
                    const ext_attrs: ParamAttrFlags = .{
                        .is_zext = isNarrowZeroExtType(resolver.pool, scalar_ty),
                        .is_sext = isNarrowSignExtType(resolver.pool, scalar_ty),
                    };
                    param_recipes[i] = .{
                        .lowered_size_bytes = clamped_sz,
                        .pointee_align_bytes = p_layout.alignBytes(),
                        .pass_mode = .direct_scalar,
                        .bank_0 = if (isScalarFloatType(resolver.pool, scalar_ty)) .xmm_vec else .gpr,
                        .attr_bits = @bitCast(ext_attrs),
                        .piece_count = 1,
                    };
                } else {
                    const ref_attrs: ParamAttrFlags = .{ .is_nonnull = true, .is_noundef = true };
                    param_recipes[i] = .{
                        .lowered_size_bytes = clamped_sz,
                        .pointee_align_bytes = p_layout.alignBytes(),
                        .pass_mode = .indirect_by_ref,
                        .bank_0 = .gpr,
                        .attr_bits = @bitCast(ref_attrs),
                        .piece_count = 1,
                    };
                }
            } else if (p_layout.size_bytes <= 8) {
                param_recipes[i] = .{
                    .lowered_size_bytes = clamped_sz,
                    .pointee_align_bytes = p_layout.alignBytes(),
                    .pass_mode = .direct_scalar,
                    .bank_0 = if (isScalarFloatType(resolver.pool, unwrapped_p)) .xmm_vec else .gpr,
                    .piece_count = 1,
                };
            } else {
                const ref_attrs: ParamAttrFlags = .{
                    .is_noalias = true,
                    .is_nonnull = true,
                    .is_noundef = true,
                    .is_readonly = (param.mode == .let_mode),
                    .is_nocapture = param.is_non_escaping,
                };
                param_recipes[i] = .{
                    .lowered_size_bytes = clamped_sz,
                    .pointee_align_bytes = p_layout.alignBytes(),
                    .pass_mode = .indirect_by_ref,
                    .bank_0 = .gpr,
                    .attr_bits = @bitCast(ref_attrs),
                    .piece_count = 1,
                };
            }
        }
        return recipe;
    }
};

/// Emits structured `E0007` (`e0007_codegen_backend_failure`) when Tier A / Tier B codegen fails.
pub fn emitBackendFailureDiagnostic(
    sink: *DiagnosticSink,
    span: Span,
    backend_label: []const u8,
    detail: []const u8,
) !void {
    const msg = try std.fmt.allocPrint(
        sink.arena.asAllocator(),
        "codegen backend `{s}` failed: {s}",
        .{ backend_label, detail },
    );
    try sink.emit(.{
        .code = .e0007_codegen_backend_failure,
        .severity = .err,
        .primary_span = span,
        .message = msg,
    });
}

/// Emits structured `E0008` (`e0008_linker_invocation_failed`) when `zig cc` / `LLD` linking fails.
pub fn emitLinkerFailureDiagnostic(
    sink: *DiagnosticSink,
    span: Span,
    exit_status: u32,
    stderr_snippet: []const u8,
) !void {
    const trimmed_stderr = std.mem.trim(u8, stderr_snippet, " \t\r\n");
    const msg = if (trimmed_stderr.len > 0)
        try std.fmt.allocPrint(
            sink.arena.asAllocator(),
            "linker invocation exited with status {d}: {s}",
            .{ exit_status, trimmed_stderr },
        )
    else
        try std.fmt.allocPrint(
            sink.arena.asAllocator(),
            "linker invocation exited with status {d}",
            .{exit_status},
        );
    try sink.emit(.{
        .code = .e0008_linker_invocation_failed,
        .severity = .err,
        .primary_span = span,
        .message = msg,
    });
}

/// Writes `content` to `dest_path` using `Prune-02` `SIGKILL`-safe `UnlinkAndReplace` + Windows lock retry (`[MAJOR-10]`).
pub fn atomicWriteOutputFile(
    io: std.Io,
    allocator: std.mem.Allocator,
    dest_path: []const u8,
    content: []const u8,
) !void {
    if (std.fs.path.dirname(dest_path)) |parent_dir| {
        if (parent_dir.len > 0) {
            std.Io.Dir.cwd().createDirPath(io, parent_dir) catch {};
        }
    }
    const seq_num = atomic_write_seq.fetchAdd(1, .monotonic);
    const proc_tag = computeProcessNonceTag();
    const tmp_path = try std.fmt.allocPrint(
        allocator,
        "{s}.tmp.{x}.{d}",
        .{ dest_path, proc_tag, seq_num },
    );
    defer allocator.free(tmp_path);

    var is_tmp_live = false;
    errdefer if (is_tmp_live) {
        std.Io.Dir.cwd().deleteFile(io, tmp_path) catch {};
    };

    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = tmp_path,
        .data = content,
    });
    is_tmp_live = true;

    var attempt: u8 = 0;
    while (attempt < 3) : (attempt += 1) {
        std.Io.Dir.cwd().deleteFile(io, dest_path) catch |del_err| switch (del_err) {
            error.FileNotFound => {},
            else => |other_del_err| {
                if (builtin.os.tag != .windows or attempt == 2) return other_del_err;
            },
        };

        if (std.Io.Dir.rename(std.Io.Dir.cwd(), tmp_path, std.Io.Dir.cwd(), dest_path, io)) |_| {
            is_tmp_live = false;
            return;
        } else |ren_err| {
            if (builtin.os.tag == .windows and attempt < 2 and ren_err == error.AccessDenied) {
                var spin_idx: u32 = 0;
                while (spin_idx < 10_000) : (spin_idx += 1) {
                    std.atomic.spinLoopHint();
                }
                continue;
            }
            return ren_err;
        }
    }
}

/// Reads `staged_src_path` and atomically publishes it onto `final_dest_path` (`Prune-02`).
pub fn publishStagedFileAtomic(
    io: std.Io,
    allocator: std.mem.Allocator,
    staged_src_path: []const u8,
    final_dest_path: []const u8,
) !void {
    const opened_file = try std.Io.Dir.cwd().openFile(io, staged_src_path, .{
        .mode = .read_only,
        .allow_directory = false,
    });
    defer opened_file.close(io);

    const file_size: usize = @intCast((try opened_file.stat(io)).size);
    const staged_bytes = try allocator.alloc(u8, file_size);
    defer allocator.free(staged_bytes);
    if ((try opened_file.readPositionalAll(io, staged_bytes, 0)) != file_size) {
        return error.UnexpectedEndOfFile;
    }
    try atomicWriteOutputFile(io, allocator, final_dest_path, staged_bytes);
}

/// Lazily locates the `zig` compiler driver executable via `COREX_ZIG_EXE` or `PATH` (`AGENTS.md` §2).
pub fn resolveZigExecutable(
    io: std.Io,
    allocator: std.mem.Allocator,
    environ_map: ?*const std.process.Environ.Map,
) ![]u8 {
    const exe_name = if (builtin.os.tag == .windows) "zig.exe" else "zig";
    const env = environ_map orelse return allocator.dupe(u8, exe_name);

    if (env.get("COREX_ZIG_EXE")) |override_zig| {
        if (override_zig.len > 0) {
            return allocator.dupe(u8, override_zig);
        }
    }

    const path_val = env.get("PATH") orelse env.get("Path") orelse return allocator.dupe(u8, exe_name);
    const path_sep: u8 = if (builtin.os.tag == .windows) ';' else ':';
    var dir_iter = std.mem.splitScalar(u8, path_val, path_sep);
    while (dir_iter.next()) |raw_dir| {
        const clean_dir = std.mem.trim(u8, raw_dir, " \t\"");
        if (clean_dir.len == 0) continue;
        const candidate = try std.fs.path.join(allocator, &.{ clean_dir, exe_name });
        if (std.Io.Dir.cwd().openFile(io, candidate, .{ .mode = .read_only })) |opened| {
            opened.close(io);
            return candidate;
        } else |_| {
            allocator.free(candidate);
        }
    }
    return allocator.dupe(u8, exe_name);
}

comptime {
    std.debug.assert(@sizeOf(TargetSpec) == 4 and @alignOf(TargetSpec) == 1);
    std.debug.assert(@sizeOf(NicheSpec) == 24 and @alignOf(NicheSpec) == 8);
    std.debug.assert(@sizeOf(ReprFlags) == 1 and @bitSizeOf(ReprFlags) == 8);
    std.debug.assert(@sizeOf(ResolvedTypeLayout) == 32 and @alignOf(ResolvedTypeLayout) == 8);
    std.debug.assert(@sizeOf(ParamAttrFlags) == 1 and @bitSizeOf(ParamAttrFlags) == 8);
    std.debug.assert(@sizeOf(AbiParamRecipe) == 16 and @alignOf(AbiParamRecipe) == 4);
    std.debug.assert(@sizeOf(ProvenValueRange) == 24 and @alignOf(ProvenValueRange) == 8);
    std.debug.assert(@typeInfo(CodegenBackend) == .@"union");
}

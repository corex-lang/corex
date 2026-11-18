//! CoreX Stage-0 LLVM 20–23 & LLD C99 Bridge Header (`corex_llvm.h`)
//!
//! Exposes a strictly typed, zero-`void*` ISO C99 FFI boundary (`AGENTS.md` Section 1,
//! `DR-09` Section 1.2, `DR-10` Section 1.4, `[CRITICAL-09]`) between `stage0/src/codegen_llvm.zig`,
//! `stage0/src/codegen_link.zig`, and the optional `-Dllvm-prefix` C++20 static LLVM/LLD bridge
//! (`stage0/src/corex_llvm.cpp`).
//!
//! All status codes use deterministic 32-bit `CxLlvmResult` (`CxLlvmStatus`) discriminants, and
//! every diagnostic output buffer is explicitly capacity-bounded and NUL-terminated.

#ifndef COREX_STAGE0_LLVM_BRIDGE_H
#define COREX_STAGE0_LLVM_BRIDGE_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// ---------------------------------------- TYPES ----------------------------------------

/// Forward-declared strongly typed opaque session handle (zero raw untyped pointers).
typedef struct CxLlvmBridgeSession CxLlvmBridgeSession;

/// Optimization pipeline level mirrored from `codegen_abi.OptLevel`.
typedef enum CxLlvmOptLevel {
    /// Debug / unoptimized `-O0` pipeline.
    CX_LLVM_OPT_O0 = 0,
    /// Production release `-O2` pipeline.
    CX_LLVM_OPT_O2 = 1,
    /// Aggressive release `-O3` pipeline.
    CX_LLVM_OPT_O3 = 2,
    /// Size-optimized `-Oz` pipeline.
    CX_LLVM_OPT_OZ = 3
} CxLlvmOptLevel;

/// Embedded `lld` target object-format driver flavor (`DR-10` Section 1.4).
typedef enum CxLldFlavor {
    /// Linux / Unix ELF64 linker driver (`ld.lld`).
    CX_LLD_ELF = 0,
    /// Apple Darwin Mach-O 64-bit linker driver (`ld64.lld`).
    CX_LLD_MACHO = 1,
    /// Microsoft Windows PE/COFF linker driver (`lld-link`).
    CX_LLD_COFF = 2,
    /// WebAssembly module linker driver (`wasm-ld`).
    CX_LLD_WASM = 3
} CxLldFlavor;

/// Deterministic 32-bit status code returned by `corex_llvm` bridge entrypoints.
typedef int32_t CxLlvmStatus;

/// Canonical result alias matching Phase 8 linker/archive bridge specifications.
typedef CxLlvmStatus CxLlvmResult;

/// Status discriminant tags stored inside `CxLlvmStatus` / `CxLlvmResult`.
enum CxLlvmStatusCode {
    /// Operation succeeded cleanly.
    CX_LLVM_OK = 0,
    /// Required pointer or count argument was invalid or `NULL`.
    CX_LLVM_ERR_INVALID_ARG = 1,
    /// Target triple or `llvm::TargetMachine` lookup failed.
    CX_LLVM_ERR_TARGET_LOOKUP = 2,
    /// Textual `.ll` assembly parsing failed.
    CX_LLVM_ERR_IR_PARSE = 3,
    /// `llvm::verifyModule` rejected the parsed module.
    CX_LLVM_ERR_VERIFY = 4,
    /// Optimization pass pipeline execution failed.
    CX_LLVM_ERR_PASS_PIPELINE = 5,
    /// Object file stream creation or target codegen pass emission failed.
    CX_LLVM_ERR_EMIT_OBJECT = 6,
    /// Embedded `lld` headers/libraries were not linked into `corex_llvm.cpp`.
    CX_LLVM_ERR_LLD_UNAVAILABLE = 7,
    /// In-process `lld` link driver returned a non-zero exit status.
    CX_LLVM_ERR_LLD_LINK = 8,
    /// Deterministic `.a` / `.lib` static archive creation failed.
    CX_LLVM_ERR_ARCHIVE_WRITE = 9,
    /// PE/COFF `.def` parsing or Short-Import `.lib` generation failed.
    CX_LLVM_ERR_COFF_IMPLIB = 10
};

/// Strongly typed compilation request passed across the C99 FFI boundary.
typedef struct CxLlvmCompileRequest {
    /// NUL-terminated LLVM target triple string (`"x86_64-unknown-linux-gnu"`, …).
    const char *target_triple;
    /// Optional NUL-terminated CPU model (`"generic"` when `NULL`).
    const char *target_cpu;
    /// Optional NUL-terminated comma-separated target feature string (`""` when `NULL`).
    const char *target_features;
    /// Optional NUL-terminated logical module identifier (`"corex_mod"` when `NULL`).
    const char *module_name;
    /// Pointer to UTF-8 `.ll` assembly text buffer (`ir_text_len` bytes).
    const char *ir_text_ptr;
    /// Byte length of `ir_text_ptr`.
    size_t ir_text_len;
    /// NUL-terminated destination `.o`/`.obj`/`.wasm` object path.
    const char *output_obj_path;
    /// Encoded `CxLlvmOptLevel` (`0..3`).
    uint8_t opt_level;
    /// Non-zero when `OptimizerLastEP` `SanitizerCoveragePass` is requested.
    uint8_t is_fuzz_sancov;
    /// Non-zero to request position-independent code (`llvm::Reloc::PIC_`).
    uint8_t is_pic;
    /// Explicit zero tail padding to 4-byte alignment.
    uint8_t _pad;
} CxLlvmCompileRequest;

// ------------------------------------- PUBLIC API --------------------------------------

/// Returns the linked LLVM major version (`20`–`23`).
uint32_t cx_llvm_bridge_version_major(void);

/// Returns `1` when embedded `lld` drivers are compiled in (`COREX_HAS_LLD`), `0` otherwise.
int cx_llvm_has_embedded_lld(void);

/// Parses `ir_text_ptr[0..ir_text_len]`, verifies IR, runs the LLVM 20–23 `PassBuilder` pipeline,
/// and writes a relocatable object file to `output_obj_path` (recording failures in `err_buf`).
CxLlvmStatus cx_llvm_compile_ir_to_object(
    const CxLlvmCompileRequest *request,
    char *err_buf,
    size_t err_buf_cap
);

/// Invokes the embedded `lld` driver (`ld.lld`, `ld64.lld`, `lld-link`, or `wasm-ld`) in-process.
CxLlvmResult cx_llvm_link_with_lld(
    CxLldFlavor flavor,
    const char *const *args_ptr,
    size_t args_len,
    char *err_buf,
    size_t err_cap
);

/// Writes a deterministic `.a` or `.lib` archive (`K_GNU`, `K_DARWIN`, or `K_COFF`) via `llvm::writeArchive`.
CxLlvmResult cx_llvm_write_archive(
    const char *output_path,
    const char *const *member_paths_ptr,
    size_t member_paths_len,
    int is_darwin,
    int is_coff_thin_or_win,
    char *err_buf,
    size_t err_cap
);

/// Parses `def_contents_ptr[0..def_contents_len]` and writes a PE/COFF Short-Import `.lib` to `output_lib_path`.
CxLlvmResult cx_llvm_write_coff_import_library(
    const char *def_contents_ptr,
    size_t def_contents_len,
    const char *output_lib_path,
    uint16_t coff_machine,
    char *err_buf,
    size_t err_cap
);

#ifdef __cplusplus
}
#endif

#endif // End `COREX_STAGE0_LLVM_BRIDGE_H`.

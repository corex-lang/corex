//! CoreX Stage-0 LLVM 20–23 C99 Bridge Header (`corex_llvm.h`)
//!
//! Exposes a strictly typed, zero-`void*` ISO C99 FFI boundary (`AGENTS.md` Section 1,
//! `DR-09` Section 1.2, `[CRITICAL-09]`) between `stage0/src/codegen_llvm.zig` and the
//! optional `-Dllvm-prefix` C++20 static LLVM `PassBuilder` + `SanitizerCoveragePass`
//! object emitter (`stage0/src/corex_llvm.cpp`).

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

/// Deterministic 32-bit status code returned by `cx_llvm_compile_ir_to_object`.
typedef int32_t CxLlvmStatus;

/// Status discriminant tags stored inside `CxLlvmStatus`.
enum CxLlvmStatusCode {
    /// Object emission succeeded cleanly.
    CX_LLVM_OK = 0,
    /// Required pointer field in `CxLlvmCompileRequest` was `NULL`.
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
    CX_LLVM_ERR_EMIT_OBJECT = 6
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

/// Parses `ir_text_ptr[0..ir_text_len]`, verifies IR, runs the LLVM 20–23 `PassBuilder` pipeline,
/// and writes a relocatable object file to `output_obj_path` (recording failures in `err_buf`).
CxLlvmStatus cx_llvm_compile_ir_to_object(
    const CxLlvmCompileRequest *request,
    char *err_buf,
    size_t err_buf_cap
);

#ifdef __cplusplus
}
#endif

#endif // End `COREX_STAGE0_LLVM_BRIDGE_H`.

---
name: build
description: Compiles the CoreX toolchain, verifies cross-compilation targets, and validates the multi-stage self-hosting bootstrap pipeline.
---

# Build

Use this skill to compile the `corex` toolchain, build standard library modules, verify all 11 cross-compilation targets (`linux`, `macos`, `windows`, `wasm32`), and validate self-hosting bootstrap reproducibility.

---

## 1. Prerequisites & Pre-Build Validation

Before packaging or running release builds, always run the full validation suite per `AGENTS.md` Section 3 (`test` skill) and confirm zero errors, zero warnings, and zero lint issues.

---

## 2. Build Modes & Pipeline Stages

The CoreX build system supports both the initial bootstrap compiler (Stage 0, retained side-by-side through `PLAN.md` `Phase 12.6`) and the self-hosted `.cx` compiler (Stages 1–3, plus the permanent C99 + `stage1/corex1.wasm.zst` offline bootstrap seed from `Phase 12.7` onward):

1.  **Stage 0 (Bootstrap Compiler / Differential Oracle):** Built from the Stage 0 Zig source tree (`stage0/`, configured via `build.zig` with unified binary name `corex`) into `build/stage0/corex` (or `build/stage0/corex.exe` on Windows) with strict Zig compiler checks and zero warnings; `zig build test` executes all Stage 0 unit, snapshot, fuzz, and drift-guard suites. From `Phase 12.7` onward, fresh C99-only hosts replace `stage0/` with `bootstrap.c` + `stage1/corex1.wasm.zst` (`DR-01` §5) to produce `corex1`.
2.  **Stage 1 (First Self-Hosted Build):** Built by invoking `build/stage0/corex build` (or `corex1` in C99 bootstrap mode) on the self-hosted compiler source tree (`compiler/*.cx`), producing `build/stage1/corex`.
3.  **Stage 2 (Self-Compiled Build):** Built by invoking `build/stage1/corex build` on the identical `compiler/*.cx` source tree, producing `build/stage2/corex`.
4.  **Stage 3 (Fixed-Point Verification Build):** Built by invoking `build/stage2/corex build` on the identical `compiler/*.cx` source tree, producing `build/stage3/corex`.

### Self-Hosting Determinism Gate

Once self-hosted codegen (`Phase 12.6`) is operational, every compiler build verification **must** assert deterministic fixed-point compilation:

-   Compare `build/stage2/corex` and `build/stage3/corex` byte-for-byte (`SHA-256` digest match under `SOURCE_DATE_EPOCH=0`).
-   Any binary divergence between Stage 2 and Stage 3 indicates non-deterministic iteration order (e.g., unseeded hash map iteration), uninitialized memory padding, or a miscompilation bug that must be fixed immediately.

---

## 3. Dual-Mode Compilation Verification

Verify both compilation pipelines whenever modifying IR lowering or backend code generation:

-   **Development Mode (`corex build --dev` / `corex run`):** Exercises fast `--dev` compilation (`D0`–`D5` MIR pipeline + `-ofmt=c` or self-hosted Tier C native emitter in `Phase 13.0`) for sub-second turnaround.
-   **Production Mode (`corex build --release`):** Exercises the full AOT optimizing LLVM 20–23 / C99 pipeline (`R1`–`R6` MIR optimizations, SAST verification, function/data section DCE, Pointer-Shape ICF, and in-process `lld` linking).

---

## 4. 11-Target Cross-Compilation & Linking Matrix

Every backend, ABI, or linker change must be verified against all 11 canonical `TargetSpec` triples from any host OS:

| Target Triple                  | Linking Modes                                  | Verification Artifact                          |
| ------------------------------ | ---------------------------------------------- | ---------------------------------------------- |
| `x86_64-linux-gnu`             | Dynamic glibc & static standalone ELF          | ELF64 SysV AMD64 header + ABI check            |
| `x86_64-linux-musl`            | Zero-dependency static standalone ELF          | Static ELF64 (`PT_INTERP` absent) check        |
| `aarch64-linux-gnu`            | Dynamic glibc & static standalone ELF          | ELF64 AAPCS64 header + ABI check               |
| `aarch64-linux-musl`           | Zero-dependency static standalone ELF          | Static ARM64 ELF64 check                       |
| `x86_64-apple-darwin`          | Dynamic `libSystem` Mach-O                     | Mach-O 64-bit x86_64 + ad-hoc code-sign check  |
| `aarch64-apple-darwin`         | Dynamic `libSystem` Mach-O (`128B` cache line) | Mach-O 64-bit arm64 + Apple ARM64 `HFA` check  |
| `x86_64-windows-msvc`          | PE32+ executable & synthesized Short-Import    | PE32+ AMD64 (`0x8664`) + `.pdata` unwind check |
| `x86_64-windows-gnu`           | MinGW-ABI PE32+ executable & `.a` archive      | PE32+ AMD64 GNU ABI check                      |
| `aarch64-windows-msvc`         | PE32+ ARM64 executable & Short-Import `.lib`   | PE32+ ARM64 (`0xAA64`) Win64 ABI check         |
| `wasm32-unknown-wasi`          | Standalone WASI Preview 1 `.wasm` module       | WebAssembly validation + WASI import check     |
| `wasm32-unknown-freestanding`  | Zero-runtime `< 10 KB` `.wasm` module          | Zero-host-import Wasm validation               |

---

## 5. Clean Artifacts

Keep build outputs strictly inside gitignored build directories (`build/`, `zig-out/`, `.zig-cache/`, `target/`, `.corex/`). Never leave temporary object files (`.o`, `.obj`), `.wasm` binaries, or `.exe` files in the repository root, `core/`, `stdlib/`, or `compiler/` directories.

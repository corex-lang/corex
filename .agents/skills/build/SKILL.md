---
name: build
description: Compiles the CoreX toolchain, verifies cross-compilation targets, and validates the multi-stage self-hosting bootstrap pipeline.
---

# Build

Use this skill to compile the `corex` toolchain, build standard library modules, verify cross-compilation targets (`linux`, `macos`, `windows`, `wasm32`), and validate self-hosting bootstrap reproducibility.

---

## 1. Prerequisites & Pre-Build Validation

Before packaging or running release builds, always run the full validation suite per `AGENTS.md` Section 3 (`test` skill) and confirm zero errors, zero warnings, and zero lint issues.

---

## 2. Build Modes & Pipeline Stages

The CoreX build system supports both the initial bootstrap compiler (Stage 0) and the self-hosted `.cx` compiler (Stages 1–2):

1.  **Stage 0 (Bootstrap Compiler):** Built from the host systems language source tree into `build/stage0/corex` (or `corex.exe` on Windows) with maximum compiler warnings treated as errors (`-Wall -Wextra -Werror` / strict lint profiles).
2.  **Stage 1 (First Self-Hosted Build):** Built by invoking `build/stage0/corex build` on the self-hosted compiler source tree (`compiler/*.cx`), producing `build/stage1/corex`.
3.  **Stage 2 (Reproducibility Verification Build):** Built by invoking `build/stage1/corex build` on the identical `compiler/*.cx` source tree, producing `build/stage2/corex`.

### Self-Hosting Determinism Gate

Once Stage 1 is operational, every compiler build verification **must** assert deterministic fixed-point compilation:

-   Compare `build/stage1/corex` and `build/stage2/corex` byte-for-byte (SHA-256 digest match).
-   Any binary divergence between Stage 1 and Stage 2 indicates non-deterministic iteration order (e.g., unseeded hash map iteration), uninitialized memory padding, or a miscompilation bug that must be fixed immediately.

---

## 3. Dual-Mode Compilation Verification

Verify both compilation pipelines whenever modifying IR lowering or backend code generation:

-   **Development Mode (`corex build --dev` / `corex run`):** Exercises the fast unoptimized / JIT / instant-codegen backend for sub-second turnaround.
-   **Production Mode (`corex build --release`):** Exercises the full AOT optimizing backend with static vulnerability analysis (SAST), dead-code elimination, monomorphization, and link-time optimization.

---

## 4. Cross-Compilation & Linking Matrix

Every backend or linker change must be verified against the cross-compilation target matrix from any host OS:

| Target Triple           | Linking Modes                        | Verification Artifact               |
| ----------------------- | ------------------------------------ | ----------------------------------- |
| `x86_64-linux-gnu`      | Static standalone & dynamic binary   | ELF64 header + syscall/ABI check    |
| `aarch64-linux-gnu`     | Static standalone & dynamic binary   | ELF64 header + AAPCS64 check        |
| `x86_64-apple-darwin`   | Dynamic system `libSystem` binary    | Mach-O 64-bit header + load command |
| `aarch64-apple-darwin`  | Dynamic system `libSystem` binary    | Mach-O 64-bit arm64 header check    |
| `x86_64-windows-msvc`   | Static standalone & DLL import table | PE32+ header + Win64 ABI check      |
| `wasm32-unknown-wasi`   | Standalone `.wasm` module            | WebAssembly binary validation       |
| `wasm32-unknown-freestanding` | Browser/web `.wasm` bundle     | Zero-host-import Wasm validation    |

---

## 5. Clean Artifacts

Keep build outputs strictly inside gitignored build directories (`build/`, `target/`, `.corex/`). Never leave temporary object files (`.o`, `.obj`), `.wasm` binaries, or `.exe` files in the repository root or `src/` directories.

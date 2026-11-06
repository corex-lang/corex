# CoreX

> *A streamlined, zero-GC, statically typed programming language built for instant compilation, compile-time safety, and C-level runtime speed.*

**CoreX** (`corex-lang/corex`) is a systems and application programming language designed for maximum developer ergonomics, deterministic compile-time memory safety without a tracing garbage collector, and zero-cold-start native and WebAssembly execution.

## Key Characteristics

-   **Source Extension:** `.cx`
-   **Toolchain CLI:** `corex` (`corex run`, `corex build`, `corex test`, `corex fmt`, `corex check`, `corex upgrade`, `corex lsp`)
-   **Dual-Mode Compilation:** Sub-second incremental compilation for instant development feedback, paired with full Ahead-of-Time (AOT) optimizing codegen for production binaries.
-   **Zero-GC Deterministic Safety:** Automatic compile-time memory management by default, optional manual memory layout control, and built-in static vulnerability verification (SAST) with zero runtime garbage collection overhead.
-   **First-Class Targets:** Cross-compiles out of the box to Linux, macOS, Windows (standalone static or dynamically linked binaries), and `wasm32`.

## License

Licensed under the [MIT License](LICENSE).

// CoreX Self-Hosting C99 Bootstrap Seed Driver
//
// Dependency-free C99 bootstrap driver (`DR-01` Section 5.2) that orchestrates deterministic
// `wasm32-wasi` seed decompression (`wasm2c.c`), C99 compilation, and multi-stage fixed-point
// verification across Windows (`CreateProcessA`), Linux, and macOS (`fork`/`execvp`/`waitpid`).
//
// Enforces zero-timestamp determinism (`SOURCE_DATE_EPOCH=0`, `ZERO_AR_DATE=1`, `TZ=UTC`, `LC_ALL=C`)
// before invoking the host C99 compiler (`CC`).

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#else
#include <sys/wait.h>
#include <unistd.h>
#endif

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum command-line byte buffer capacity for Windows `CreateProcessA` invocation.
enum { MAX_CMDLINE_BYTES = 8192 };

// -------------------------------------- INTERNALS --------------------------------------

/// Prints a fatal bootstrap diagnostic to `stderr` and aborts execution immediately.
static void panicWithMessage(const char *message) {
    fprintf(stderr, "✗ corex-bootstrap fatal: %s\n", message);
    abort();
}

#if defined(_WIN32)
/// Sets deterministic build environment variables on Windows hosts.
static void configureDeterministicEnv(void) {
    _putenv_s("SOURCE_DATE_EPOCH", "0");
    _putenv_s("ZERO_AR_DATE", "1");
    _putenv_s("TZ", "UTC");
    _putenv_s("LC_ALL", "C");
}

/// Spawns a child process synchronously on Windows and verifies a zero exit code.
static void runChildProcess(const char *const *argv) {
    char cmdline[MAX_CMDLINE_BYTES];
    size_t cursor_pos = 0;
    size_t i = 0;
    while (argv[i] != NULL) {
        int written_bytes = snprintf(
            cmdline + cursor_pos,
            sizeof(cmdline) - cursor_pos,
            (i == 0) ? "\"%s\"" : " \"%s\"",
            argv[i]
        );
        if (written_bytes < 0 || (size_t)written_bytes >= sizeof(cmdline) - cursor_pos) {
            panicWithMessage("command line buffer overflow");
        }
        cursor_pos += (size_t)written_bytes;
        i += 1;
    }

    STARTUPINFOA startup_info;
    PROCESS_INFORMATION process_info;
    ZeroMemory(&startup_info, sizeof(startup_info));
    startup_info.cb = sizeof(startup_info);
    ZeroMemory(&process_info, sizeof(process_info));

    if (!CreateProcessA(NULL, cmdline, NULL, NULL, TRUE, 0, NULL, NULL, &startup_info, &process_info)) {
        panicWithMessage("CreateProcessA failed");
    }
    WaitForSingleObject(process_info.hProcess, INFINITE);

    DWORD exit_code = 1;
    GetExitCodeProcess(process_info.hProcess, &exit_code);
    CloseHandle(process_info.hProcess);
    CloseHandle(process_info.hThread);
    if (exit_code != 0) {
        panicWithMessage("child process exited with non-zero status");
    }
}
#else
/// Sets deterministic build environment variables on POSIX hosts.
static void configureDeterministicEnv(void) {
    setenv("SOURCE_DATE_EPOCH", "0", 1);
    setenv("ZERO_AR_DATE", "1", 1);
    setenv("TZ", "UTC", 1);
    setenv("LC_ALL", "C", 1);
}

/// Forks and executes a child process synchronously on POSIX hosts, verifying a zero exit status.
static void runChildProcess(const char *const *argv) {
    pid_t child_pid = fork();
    if (child_pid < 0) {
        panicWithMessage("fork() failed");
    }
    if (child_pid == 0) {
        execvp(argv[0], (char *const *)argv);
        perror("execvp");
        _exit(127);
    }
    int wait_status = 0;
    if (waitpid(child_pid, &wait_status, 0) < 0) {
        panicWithMessage("waitpid() failed");
    }
    if (!WIFEXITED(wait_status) || WEXITSTATUS(wait_status) != 0) {
        panicWithMessage("child process exited with non-zero status");
    }
}
#endif

/// Logs the command line to `stderr` with a monochrome glyph and executes it via `runChildProcess`.
static void printAndRunCommand(const char *const *argv) {
    fprintf(stderr, "▸ [bootstrap]");
    size_t i = 0;
    while (argv[i] != NULL) {
        fprintf(stderr, " %s", argv[i]);
        i += 1;
    }
    fprintf(stderr, "\n");
    runChildProcess(argv);
}

/// Resolves the host C99 compiler executable from `CC`, defaulting to `"cc"`.
static const char *resolveHostCc(void) {
    const char *cc_env = getenv("CC");
    return (cc_env != NULL && cc_env[0] != '\0') ? cc_env : "cc";
}

/// Resolves the target triple for the current host architecture and operating system.
static const char *resolveHostTriple(void) {
    const char *triple_override = getenv("COREX_HOST_TRIPLE");
    if (triple_override != NULL && triple_override[0] != '\0') {
        return triple_override;
    }
#if defined(__x86_64__) || defined(_M_X64)
#define COREX_BOOTSTRAP_ARCH "x86_64"
#elif defined(__aarch64__) || defined(_M_ARM64)
#define COREX_BOOTSTRAP_ARCH "aarch64"
#elif defined(__riscv) && (__riscv_xlen == 64)
#define COREX_BOOTSTRAP_ARCH "riscv64"
#else
#error "Specify COREX_HOST_TRIPLE for this architecture"
#endif

#if defined(_WIN32)
    return COREX_BOOTSTRAP_ARCH "-windows-gnu";
#elif defined(__APPLE__)
    return COREX_BOOTSTRAP_ARCH "-macos-none";
#elif defined(__linux__)
    return COREX_BOOTSTRAP_ARCH "-linux-gnu";
#else
#error "Specify COREX_HOST_TRIPLE for this operating system"
#endif
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the 7-step deterministic CoreX self-hosting bootstrap pipeline (`DR-01` Section 5.2).
int main(void) {
    configureDeterministicEnv();
    const char *host_cc = resolveHostCc();
    const char *host_triple = resolveHostTriple();

    // [1] Compile the C99 `wasm2c` translator and `zstd` seed decompressor:
    {
        const char *argv[] = {
            host_cc, "-o", "corex-wasm2c", "stage1/wasm2c.c", "-O2", "-std=c99", NULL
        };
        printAndRunCommand(argv);
    }

    // [2] Decompress and translate `stage1/corex1.wasm.zst` into portable C99 `corex1.c`:
    {
        const char *argv[] = {
            "./corex-wasm2c", "stage1/corex1.wasm.zst", "corex1.c", NULL
        };
        printAndRunCommand(argv);
    }

    // [3] Compile `corex1.c` and the 23-syscall WASI shim (`stage1/wasi.c`) into `./corex1`:
    {
        const char *argv[] = {
            host_cc, "-o", "corex1", "corex1.c", "stage1/wasi.c", "-std=c99", "-Os", "-lm", NULL
        };
        printAndRunCommand(argv);
    }

    // [4] Emit deterministic bootstrap configuration file `config.cx`:
    {
        FILE *config_file = fopen("config.cx", "wb");
        if (config_file == NULL) {
            panicWithMessage("failed to open config.cx for writing");
        }
        fprintf(
            config_file,
            "pub const HAVE_LLVM: bool = false;\n"
            "pub const VERSION: str = \"0.1.0-bootstrap\";\n"
            "pub const DEV_PROFILE: Profile = .bootstrap;\n"
        );
        fclose(config_file);
    }

    // [5] Invoke `./corex1` (Wasm seed) to transpile in-tree `.cx` compiler sources into `corex2.c`:
    {
        const char *argv[] = {
            "./corex1", "build-exe", "src/main.cx",
            "-ofmt=c", "-OReleaseSmall", "-target", host_triple,
            "--name", "corex2", "-femit-bin=corex2.c", NULL
        };
        printAndRunCommand(argv);
    }

    // [6] Compile `corex2.c` and `stage1/compiler_rt.c` with the host C99 compiler:
    {
        const char *argv[] = {
            host_cc, "-o", "corex2", "corex2.c", "stage1/compiler_rt.c",
            "-std=c99", "-O2", "-fno-stack-protector", "-Istage1",
#if defined(__APPLE__)
            "-Wl,-stack_size,0x10000000",
#elif !defined(_WIN32)
            "-Wl,-z,stack-size=0x10000000", "-pthread",
#endif
            NULL
        };
        printAndRunCommand(argv);
    }

    // [7] Use `./corex2` to build Stage 3 and verify Stage 3 == Stage 4 bit-for-bit reproducibility:
    {
        const char *argv[] = {
            "./corex2", "build", "--stage3-verify-fixed-point", NULL
        };
        printAndRunCommand(argv);
    }

    return 0;
}

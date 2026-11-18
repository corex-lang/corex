//! CoreX Stage-0 LLVM 20–23 & LLD Static C++20 Bridge (`corex_llvm.cpp`)
//!
//! Compiled with `-std=c++20 -fno-exceptions -fno-rtti` exclusively when `-Dllvm-prefix=<path>`
//! is supplied to `zig build`. Drives LLVM 20–23's New Pass Manager (`llvm::PassBuilder`),
//! per-symbol `FunctionSections`/`DataSections` dead-stripping, `SanitizerCoveragePass`,
//! in-process `lld` linking, deterministic `.a`/`.lib` archiving, and COFF `.def` -> `.lib` synthesis.
//!
//! All entrypoints are thread-safe (`std::call_once` for target registration and `g_lld_mutex`
//! serializing `lld` static arenas) and expose zero untyped `void*` handles (`AGENTS.md` Section 1–2).

#include "corex_llvm.h"

#include <cstring>
#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <system_error>
#include <utility>

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/SmallString.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Analysis/BasicAliasAnalysis.h>
#include <llvm/Analysis/ScopedNoAliasAA.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/TargetTransformInfo.h>
#include <llvm/Analysis/TypeBasedAliasAnalysis.h>
#include <llvm/AsmParser/Parser.h>
#include <llvm/BinaryFormat/COFF.h>
#include <llvm/Config/llvm-config.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/MC/TargetRegistry.h>
#include <llvm/Object/Archive.h>
#include <llvm/Object/ArchiveWriter.h>
#include <llvm/Object/COFFImportFile.h>
#include <llvm/Object/COFFModuleDefinition.h>
#include <llvm/Passes/OptimizationLevel.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/CodeGen.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Target/TargetMachine.h>
#include <llvm/Target/TargetOptions.h>
#include <llvm/TargetParser/Triple.h>
#include <llvm/Transforms/Instrumentation/SanitizerCoverage.h>

#if defined(COREX_HAS_LLD) && __has_include(<lld/Common/Driver.h>)
#define COREX_EMBEDDED_LLD_ACTIVE 1
#include <lld/Common/Driver.h>
#if __has_include(<lld/Common/CommonLinkerContext.h>)
#include <lld/Common/CommonLinkerContext.h>
#endif
#if __has_include(<lld/Common/Memory.h>)
#include <lld/Common/Memory.h>
#endif
LLD_HAS_DRIVER(elf)
LLD_HAS_DRIVER(macho)
LLD_HAS_DRIVER(coff)
LLD_HAS_DRIVER(wasm)
#else
#define COREX_EMBEDDED_LLD_ACTIVE 0
#endif

namespace {

// -------------------------------------- INTERNALS --------------------------------------

/// Process-wide one-time initialization guard for LLVM target registries.
std::once_flag g_llvm_targets_once;

#if COREX_EMBEDDED_LLD_ACTIVE
/// Process-wide mutex serializing in-process `lld` invocations across worker threads.
std::mutex g_lld_mutex;
#endif

/// Lazily initializes all registered LLVM target descriptions on first bridge invocation (`AGENTS.md` Section 2).
void ensureLlvmTargetsInitialized() {
    std::call_once(g_llvm_targets_once, []() {
        llvm::InitializeAllTargetInfos();
        llvm::InitializeAllTargets();
        llvm::InitializeAllTargetMCs();
        llvm::InitializeAllAsmPrinters();
        llvm::InitializeAllAsmParsers();
    });
}

/// Copies `message` into bounded `err_buf[0..err_buf_cap]` with guaranteed NUL termination.
void writeBoundedError(char *err_buf, size_t err_buf_cap, llvm::StringRef message) {
    if (err_buf == nullptr || err_buf_cap == 0) {
        return;
    }
    const size_t copy_len = message.size() < (err_buf_cap - 1) ? message.size() : (err_buf_cap - 1);
    if (copy_len > 0) {
        std::memcpy(err_buf, message.data(), copy_len);
    }
    err_buf[copy_len] = '\0';
}

/// Converts `CxLlvmOptLevel` onto `llvm::OptimizationLevel`.
llvm::OptimizationLevel toLlvmOptLevel(uint8_t raw_level) {
    switch (static_cast<CxLlvmOptLevel>(raw_level)) {
        case CX_LLVM_OPT_O0:
            return llvm::OptimizationLevel::O0;
        case CX_LLVM_OPT_O2:
            return llvm::OptimizationLevel::O2;
        case CX_LLVM_OPT_O3:
            return llvm::OptimizationLevel::O3;
        case CX_LLVM_OPT_OZ:
            return llvm::OptimizationLevel::Oz;
    }
    return llvm::OptimizationLevel::O2;
}

/// Dispatches `llvm::writeArchive` across LLVM 20–23 `SymtabWritingMode` vs boolean `WriteSymtab` overloads.
template <typename ArchiveMembersT>
llvm::Error invokeWriteArchiveCompat(
    llvm::StringRef output_path,
    ArchiveMembersT &members,
    llvm::object::Archive::Kind archive_kind
) {
    if constexpr (requires {
        llvm::writeArchive(
            output_path,
            members,
            llvm::SymtabWritingMode::NormalSymtab,
            archive_kind,
            true,
            false
        );
    }) {
        return llvm::writeArchive(
            output_path,
            members,
            llvm::SymtabWritingMode::NormalSymtab,
            archive_kind,
            /*Deterministic=*/true,
            /*Thin=*/false
        );
    } else {
        return llvm::writeArchive(
            output_path,
            members,
            /*WriteSymtab=*/true,
            archive_kind,
            /*Deterministic=*/true,
            /*Thin=*/false
        );
    }
}

/// Dispatches `llvm::object::writeImportLibrary` across LLVM 20–23 5-arg and 6-arg `NativeExports` signatures.
template <typename ExportsT>
llvm::Error invokeWriteImportLibraryCompat(
    llvm::StringRef import_dll_name,
    llvm::StringRef output_lib_path,
    const ExportsT &exports,
    llvm::COFF::MachineTypes machine
) {
    if constexpr (requires {
        llvm::object::writeImportLibrary(import_dll_name, output_lib_path, exports, machine, true);
    }) {
        return llvm::object::writeImportLibrary(
            import_dll_name,
            output_lib_path,
            exports,
            machine,
            /*MinGW=*/true
        );
    } else {
        return llvm::object::writeImportLibrary(
            import_dll_name,
            output_lib_path,
            exports,
            machine,
            /*MinGW=*/true,
            {}
        );
    }
}

#if COREX_EMBEDDED_LLD_ACTIVE
/// Tears down any residual `lld::CommonLinkerContext` / arena state after `exitEarly = false` runs.
template <typename UnusedT = void>
void destroyLldContextIfPresent() {
#if __has_include(<lld/Common/CommonLinkerContext.h>)
    if constexpr (requires { lld::CommonLinkerContext::destroy(); }) {
        lld::CommonLinkerContext::destroy();
    }
#elif __has_include(<lld/Common/Memory.h>)
    if constexpr (requires { lld::freeArena(); }) {
        lld::freeArena();
    }
#endif
}

/// Executes a single `lld` flavor directly with `exitEarly = false` so link errors never `_exit(1)`.
template <typename DriverFnT>
bool invokeEmbeddedLldFlavor(
    DriverFnT driver_fn,
    llvm::ArrayRef<const char *> full_args,
    llvm::raw_ostream &stdout_os,
    llvm::raw_ostream &stderr_os
) {
    const bool is_linked = driver_fn(
        full_args,
        stdout_os,
        stderr_os,
        /*exitEarly=*/false,
        /*disableOutput=*/false
    );
    stdout_os.flush();
    stderr_os.flush();
    destroyLldContextIfPresent<>();
    return is_linked;
}
#endif

} // End anonymous namespace.

// ------------------------------------- PUBLIC API --------------------------------------

/// Returns the linked LLVM major version (`20`–`23`).
extern "C" uint32_t cx_llvm_bridge_version_major(void) {
    return static_cast<uint32_t>(LLVM_VERSION_MAJOR);
}

/// Returns `1` when embedded `lld` drivers are compiled in (`COREX_HAS_LLD`), `0` otherwise.
extern "C" int cx_llvm_has_embedded_lld(void) {
    return COREX_EMBEDDED_LLD_ACTIVE;
}

/// Parses, verifies, optimizes, and emits a relocatable object file for `request` via LLVM `PassBuilder`.
extern "C" CxLlvmStatus cx_llvm_compile_ir_to_object(
    const CxLlvmCompileRequest *request,
    char *err_buf,
    size_t err_buf_cap
) {
    writeBoundedError(err_buf, err_buf_cap, "");
    if (request == nullptr || request->target_triple == nullptr || request->ir_text_ptr == nullptr ||
        request->output_obj_path == nullptr) {
        writeBoundedError(err_buf, err_buf_cap, "null argument in CxLlvmCompileRequest");
        return CX_LLVM_ERR_INVALID_ARG;
    }

    ensureLlvmTargetsInitialized();

    const std::string triple_str(request->target_triple);
    const llvm::Triple target_triple(triple_str);
    std::string lookup_err;
    const llvm::Target *llvm_target = llvm::TargetRegistry::lookupTarget(
#if LLVM_VERSION_MAJOR >= 21
        target_triple,
#else
        triple_str,
#endif
        lookup_err
    );
    if (llvm_target == nullptr) {
        writeBoundedError(err_buf, err_buf_cap, lookup_err);
        return CX_LLVM_ERR_TARGET_LOOKUP;
    }

    llvm::LLVMContext llvm_ctx;
    llvm::SMDiagnostic parse_diag;
    const llvm::StringRef ir_ref(request->ir_text_ptr, request->ir_text_len);
    const llvm::StringRef mod_name_ref(
        request->module_name != nullptr ? request->module_name : "corex_mod"
    );
    std::unique_ptr<llvm::MemoryBuffer> mem_buf =
        llvm::MemoryBuffer::getMemBuffer(ir_ref, mod_name_ref, false);
    std::unique_ptr<llvm::Module> llvm_mod =
        llvm::parseAssembly(mem_buf->getMemBufferRef(), parse_diag, llvm_ctx);
    if (!llvm_mod) {
        std::string diag_str;
        llvm::raw_string_ostream diag_os(diag_str);
        parse_diag.print("corex_llvm", diag_os, false);
        diag_os.flush();
        writeBoundedError(err_buf, err_buf_cap, diag_str);
        return CX_LLVM_ERR_IR_PARSE;
    }

    std::string verify_err;
    llvm::raw_string_ostream verify_os(verify_err);
    if (llvm::verifyModule(*llvm_mod, &verify_os)) {
        verify_os.flush();
        writeBoundedError(err_buf, err_buf_cap, verify_err);
        return CX_LLVM_ERR_VERIFY;
    }

    // Enable per-function and per-data sections so `--gc-sections` / `-dead_strip` / `/OPT:REF` strips dead code (`DR-10` §5.2):
    llvm::TargetOptions target_opts;
    target_opts.FunctionSections = true;
    target_opts.DataSections = true;

    const std::optional<llvm::Reloc::Model> reloc_model =
        request->is_pic != 0 ? std::optional<llvm::Reloc::Model>(llvm::Reloc::PIC_) : std::nullopt;
    const llvm::StringRef cpu_ref(request->target_cpu != nullptr ? request->target_cpu : "generic");
    const llvm::StringRef feat_ref(request->target_features != nullptr ? request->target_features : "");

    const llvm::CodeGenOptLevel cg_opt = request->opt_level == CX_LLVM_OPT_O0
        ? llvm::CodeGenOptLevel::None
        : (request->opt_level == CX_LLVM_OPT_O3 ? llvm::CodeGenOptLevel::Aggressive
                                                : llvm::CodeGenOptLevel::Default);

    std::unique_ptr<llvm::TargetMachine> target_machine(llvm_target->createTargetMachine(
#if LLVM_VERSION_MAJOR >= 21
        target_triple,
#else
        triple_str,
#endif
        cpu_ref,
        feat_ref,
        target_opts,
        reloc_model,
        std::nullopt,
        cg_opt
    ));
    if (!target_machine) {
        writeBoundedError(err_buf, err_buf_cap, "failed to create llvm::TargetMachine");
        return CX_LLVM_ERR_TARGET_LOOKUP;
    }

    llvm_mod->setDataLayout(target_machine->createDataLayout());
#if LLVM_VERSION_MAJOR >= 21
    llvm_mod->setTargetTriple(target_triple);
#else
    llvm_mod->setTargetTriple(triple_str);
#endif

    // Configure New Pass Manager (`DR-09` Section 4.1 MVS AA + `DR-18` `OptimizerLastEP` SanCov):
    llvm::PipelineTuningOptions tuning_opts;
    tuning_opts.LoopVectorization = (request->opt_level != CX_LLVM_OPT_O0);
    tuning_opts.SLPVectorization = (request->opt_level != CX_LLVM_OPT_O0);

    llvm::PassBuilder pass_builder(target_machine.get(), tuning_opts);
    if (request->is_fuzz_sancov != 0) {
        pass_builder.registerOptimizerLastEPCallback(
#if LLVM_VERSION_MAJOR >= 20
            [](llvm::ModulePassManager &mpm, llvm::OptimizationLevel, llvm::ThinOrFullLTOPhase) {
#else
            [](llvm::ModulePassManager &mpm, llvm::OptimizationLevel) {
#endif
                llvm::SanitizerCoverageOptions sancov_opts;
                sancov_opts.CoverageType = llvm::SanitizerCoverageOptions::SCK_Edge;
                sancov_opts.Inline8bitCounters = true;
                sancov_opts.PCTable = true;
                sancov_opts.TraceCmp = true;
                sancov_opts.TraceDiv = true;
                sancov_opts.NoPrune = false;
                mpm.addPass(llvm::SanitizerCoveragePass(sancov_opts));
            }
        );
    }

    llvm::LoopAnalysisManager lam;
    llvm::FunctionAnalysisManager fam;
    llvm::CGSCCAnalysisManager cgam;
    llvm::ModuleAnalysisManager mam;

    fam.registerPass([&]() {
        return pass_builder.buildDefaultAAPipeline();
    });

    pass_builder.registerModuleAnalyses(mam);
    pass_builder.registerCGSCCAnalyses(cgam);
    pass_builder.registerFunctionAnalyses(fam);
    pass_builder.registerLoopAnalyses(lam);
    pass_builder.crossRegisterProxies(lam, fam, cgam, mam);

    const llvm::OptimizationLevel opt_level = toLlvmOptLevel(request->opt_level);
    llvm::ModulePassManager mpm = opt_level == llvm::OptimizationLevel::O0
        ? pass_builder.buildO0DefaultPipeline(opt_level)
        : pass_builder.buildPerModuleDefaultPipeline(opt_level);
    mpm.run(*llvm_mod, mam);

    std::error_code file_ec;
    llvm::raw_fd_ostream obj_out(request->output_obj_path, file_ec, llvm::sys::fs::OF_None);
    if (file_ec) {
        writeBoundedError(err_buf, err_buf_cap, file_ec.message());
        return CX_LLVM_ERR_EMIT_OBJECT;
    }

    llvm::legacy::PassManager codegen_pm;
    if (target_machine->addPassesToEmitFile(
            codegen_pm, obj_out, nullptr, llvm::CodeGenFileType::ObjectFile)) {
        writeBoundedError(err_buf, err_buf_cap, "TargetMachine cannot emit ObjectFile for target");
        return CX_LLVM_ERR_EMIT_OBJECT;
    }
    codegen_pm.run(*llvm_mod);
    obj_out.flush();
    return CX_LLVM_OK;
}

/// Invokes the embedded `lld` driver (`ld.lld`, `ld64.lld`, `lld-link`, or `wasm-ld`) in-process.
extern "C" CxLlvmResult cx_llvm_link_with_lld(
    CxLldFlavor flavor,
    const char *const *args_ptr,
    size_t args_len,
    char *err_buf,
    size_t err_cap
) {
    writeBoundedError(err_buf, err_cap, "");
    if (args_len > 0 && args_ptr == nullptr) {
        writeBoundedError(err_buf, err_cap, "null args_ptr passed to cx_llvm_link_with_lld");
        return CX_LLVM_ERR_INVALID_ARG;
    }
#if !COREX_EMBEDDED_LLD_ACTIVE
    (void)flavor;
    writeBoundedError(err_buf, err_cap, "embedded lld was not linked into corex_llvm");
    return CX_LLVM_ERR_LLD_UNAVAILABLE;
#else
    const char *driver_argv0 = nullptr;
    switch (flavor) {
        case CX_LLD_ELF:
            driver_argv0 = "ld.lld";
            break;
        case CX_LLD_MACHO:
            driver_argv0 = "ld64.lld";
            break;
        case CX_LLD_COFF:
            driver_argv0 = "lld-link";
            break;
        case CX_LLD_WASM:
            driver_argv0 = "wasm-ld";
            break;
    }
    if (driver_argv0 == nullptr) {
        writeBoundedError(err_buf, err_cap, "unknown CxLldFlavor discriminant");
        return CX_LLVM_ERR_INVALID_ARG;
    }

    std::lock_guard<std::mutex> lock(g_lld_mutex);
    llvm::SmallVector<const char *, 64> full_args;
    full_args.reserve(args_len + 1);
    if (args_len == 0 || (args_ptr[0] != nullptr && std::strcmp(args_ptr[0], driver_argv0) != 0)) {
        full_args.push_back(driver_argv0);
    }
    for (size_t i = 0; i < args_len; i += 1) {
        if (args_ptr[i] == nullptr) {
            writeBoundedError(err_buf, err_cap, "null argument element in cx_llvm_link_with_lld");
            return CX_LLVM_ERR_INVALID_ARG;
        }
        full_args.push_back(args_ptr[i]);
    }

    llvm::SmallString<4096> out_str;
    llvm::SmallString<4096> err_str;
    llvm::raw_svector_ostream stdout_os(out_str);
    llvm::raw_svector_ostream stderr_os(err_str);

    bool is_ok = false;
    switch (flavor) {
        case CX_LLD_ELF:
            is_ok = invokeEmbeddedLldFlavor(&lld::elf::link, full_args, stdout_os, stderr_os);
            break;
        case CX_LLD_MACHO:
            is_ok = invokeEmbeddedLldFlavor(&lld::macho::link, full_args, stdout_os, stderr_os);
            break;
        case CX_LLD_COFF:
            is_ok = invokeEmbeddedLldFlavor(&lld::coff::link, full_args, stdout_os, stderr_os);
            break;
        case CX_LLD_WASM:
            is_ok = invokeEmbeddedLldFlavor(&lld::wasm::link, full_args, stdout_os, stderr_os);
            break;
    }

    if (!is_ok) {
        writeBoundedError(err_buf, err_cap, err_str.empty() ? out_str.str() : err_str.str());
        return CX_LLVM_ERR_LLD_LINK;
    }
    return CX_LLVM_OK;
#endif
}

/// Writes a deterministic `.a` or `.lib` archive (`K_GNU`, `K_DARWIN`, or `K_COFF`) via `llvm::writeArchive`.
extern "C" CxLlvmResult cx_llvm_write_archive(
    const char *output_path,
    const char *const *member_paths_ptr,
    size_t member_paths_len,
    int is_darwin,
    int is_coff_thin_or_win,
    char *err_buf,
    size_t err_cap
) {
    writeBoundedError(err_buf, err_cap, "");
    if (output_path == nullptr || (member_paths_len > 0 && member_paths_ptr == nullptr)) {
        writeBoundedError(err_buf, err_cap, "null argument passed to cx_llvm_write_archive");
        return CX_LLVM_ERR_INVALID_ARG;
    }

    llvm::SmallVector<llvm::NewArchiveMember, 32> members;
    members.reserve(member_paths_len);
    for (size_t i = 0; i < member_paths_len; i += 1) {
        if (member_paths_ptr[i] == nullptr) {
            writeBoundedError(err_buf, err_cap, "null member path in cx_llvm_write_archive");
            return CX_LLVM_ERR_INVALID_ARG;
        }
        llvm::Expected<llvm::NewArchiveMember> member_or_err =
            llvm::NewArchiveMember::getFile(member_paths_ptr[i], /*Deterministic=*/true);
        if (!member_or_err) {
            writeBoundedError(err_buf, err_cap, llvm::toString(member_or_err.takeError()));
            return CX_LLVM_ERR_ARCHIVE_WRITE;
        }
        members.push_back(std::move(*member_or_err));
    }

    llvm::object::Archive::Kind archive_kind = llvm::object::Archive::K_GNU;
    if (is_darwin != 0) {
        archive_kind = llvm::object::Archive::K_DARWIN;
    } else if (is_coff_thin_or_win != 0) {
        archive_kind = llvm::object::Archive::K_COFF;
    }

    llvm::Error write_err = invokeWriteArchiveCompat(output_path, members, archive_kind);
    if (write_err) {
        writeBoundedError(err_buf, err_cap, llvm::toString(std::move(write_err)));
        return CX_LLVM_ERR_ARCHIVE_WRITE;
    }
    return CX_LLVM_OK;
}

/// Parses `def_contents_ptr[0..def_contents_len]` and writes a PE/COFF Short-Import `.lib` to `output_lib_path`.
extern "C" CxLlvmResult cx_llvm_write_coff_import_library(
    const char *def_contents_ptr,
    size_t def_contents_len,
    const char *output_lib_path,
    uint16_t coff_machine,
    char *err_buf,
    size_t err_cap
) {
    writeBoundedError(err_buf, err_cap, "");
    if (output_lib_path == nullptr || (def_contents_len > 0 && def_contents_ptr == nullptr)) {
        writeBoundedError(err_buf, err_cap, "null argument passed to cx_llvm_write_coff_import_library");
        return CX_LLVM_ERR_INVALID_ARG;
    }

    const llvm::StringRef def_text(def_contents_ptr != nullptr ? def_contents_ptr : "", def_contents_len);
    const llvm::MemoryBufferRef def_buf(def_text, "module.def");
    const auto machine = static_cast<llvm::COFF::MachineTypes>(coff_machine);

    llvm::Expected<llvm::object::COFFModuleDefinition> def_or_err =
        llvm::object::parseCOFFModuleDefinition(def_buf, machine, /*MingwDef=*/true);
    if (!def_or_err) {
        writeBoundedError(err_buf, err_cap, llvm::toString(def_or_err.takeError()));
        return CX_LLVM_ERR_COFF_IMPLIB;
    }

    std::string fallback_dll;
    llvm::StringRef import_dll = def_or_err->OutputFile;
    if (import_dll.empty()) {
        fallback_dll = (llvm::sys::path::stem(output_lib_path) + ".dll").str();
        import_dll = fallback_dll;
    }

    llvm::Error write_err = invokeWriteImportLibraryCompat(
        import_dll,
        output_lib_path,
        def_or_err->Exports,
        machine
    );
    if (write_err) {
        writeBoundedError(err_buf, err_cap, llvm::toString(std::move(write_err)));
        return CX_LLVM_ERR_COFF_IMPLIB;
    }
    return CX_LLVM_OK;
}

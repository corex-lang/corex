//! CoreX Stage-0 LLVM 20–23 Static C++20 Bridge (`corex_llvm.cpp`)
//!
//! Compiled with `-std=c++20 -fno-exceptions -fno-rtti` exclusively when `-Dllvm-prefix=<path>`
//! is supplied to `zig build`. Drives LLVM 20–23's New Pass Manager (`llvm::PassBuilder`),
//! `ScopedNoAliasAA` + `TypeBasedAA` MVS alias pipelines, `OptimizerLastEP` `SanitizerCoveragePass`
//! (`Inline8bitCounters`, `PCTable`, `TraceCmp`, `TraceDiv`, `NoPrune = false`), and native object
//! file emission (`DR-09` Section 1.2, `DR-18` Section 2.1, `AGENTS.md` Section 1–2).

#include "corex_llvm.h"

#include <cstring>
#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <system_error>

#include <llvm/Analysis/BasicAliasAnalysis.h>
#include <llvm/Analysis/ScopedNoAliasAA.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/TargetTransformInfo.h>
#include <llvm/Analysis/TypeBasedAliasAnalysis.h>
#include <llvm/AsmParser/Parser.h>
#include <llvm/Config/llvm-config.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/MC/TargetRegistry.h>
#include <llvm/Passes/OptimizationLevel.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/CodeGen.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Target/TargetMachine.h>
#include <llvm/Target/TargetOptions.h>
#include <llvm/TargetParser/Triple.h>
#include <llvm/Transforms/Instrumentation/SanitizerCoverage.h>

namespace {

// -------------------------------------- INTERNALS --------------------------------------

/// Process-wide one-time initialization guard for LLVM target registries.
std::once_flag g_llvm_targets_once;

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
void writeBoundedError(char *err_buf, size_t err_buf_cap, const std::string &message) {
    if (err_buf == nullptr || err_buf_cap == 0) {
        return;
    }
    const size_t copy_len = message.size() < (err_buf_cap - 1) ? message.size() : (err_buf_cap - 1);
    if (copy_len > 0) {
        std::memcpy(err_buf, message.data(), copy_len);
    }
    err_buf[copy_len] = '\0';
}

/// Maps `CxLlvmOptLevel` onto `llvm::OptimizationLevel`.
llvm::OptimizationLevel mapOptLevel(uint8_t raw_level) {
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

} // End anonymous namespace.

// ------------------------------------- PUBLIC API --------------------------------------

/// Returns the linked LLVM major version (`20`–`23`).
extern "C" uint32_t cx_llvm_bridge_version_major(void) {
    return static_cast<uint32_t>(LLVM_VERSION_MAJOR);
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

    llvm::TargetOptions target_opts;
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

    const llvm::OptimizationLevel opt_level = mapOptLevel(request->opt_level);
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

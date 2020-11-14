#ifndef HAVE_LLVM
#error "This code needs LLVM enabled"
#endif

#include <set>
#include <iostream>
#include <sstream>
#include <fstream>
#include <string>
#include <cassert>
#include <cstdio>

// ignore unused parameters in LLVM libraries
#if (__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_os_ostream.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/CommandLine.h>

#if LLVM_VERSION_MAJOR >= 4
#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>
#else
#include <llvm/Bitcode/ReaderWriter.h>
#endif

#if (__clang__)
#pragma clang diagnostic pop // ignore -Wunused-parameter
#else
#pragma GCC diagnostic pop
#endif

#undef NDEBUG // we need dump methods
#include "dg/llvm/ValueRelations/GraphBuilder.h"
#include "dg/llvm/ValueRelations/StructureAnalyzer.h"
#include "dg/llvm/ValueRelations/RelationsAnalyzer.h"
#include "dg/llvm/ValueRelations/AnalysisGraph.h"
#include "dg/llvm/ValueRelations/getValName.h"

#include "dg/tools/TimeMeasure.h"

using namespace dg::vr;
using llvm::errs;

llvm::cl::opt<bool> todot("dot",
    llvm::cl::desc("Dump graph in grahviz format"), llvm::cl::init(false));

llvm::cl::opt<unsigned> max_iter("max-iter",
    llvm::cl::desc("Maximal number of iterations"), llvm::cl::init(100));

llvm::cl::opt<std::string> inputFile(llvm::cl::Positional, llvm::cl::Required,
    llvm::cl::desc("<input file>"), llvm::cl::init(""));

int main(int argc, char *argv[])
{
    llvm::Module *M;
    llvm::LLVMContext context;
    llvm::SMDiagnostic SMD;

    llvm::cl::ParseCommandLineOptions(argc, argv);

    if (inputFile.empty()) {
        errs() << "Usage: % IR_module\n";
        return 1;
    }

#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR <= 5))
    M = llvm::ParseIRFile(inputFile, SMD, context);
#else
    auto _M = llvm::parseIRFile(inputFile, SMD, context);
    // _M is unique pointer, we need to get Module *
    M = _M.get();
#endif

    if (!M) {
        llvm::errs() << "Failed parsing '" << inputFile << "' file:\n";
        SMD.print(argv[0], errs());
        return 1;
    }

    dg::debug::TimeMeasure tm;

    tm.start();

    // perform preparations and analysis
    std::map<const llvm::Instruction*, VRLocation*> locationMapping;
    std::map<const llvm::BasicBlock*, std::unique_ptr<VRBBlock>> blockMapping;

    GraphBuilder gb(*M, locationMapping, blockMapping);
    gb.build();

    StructureAnalyzer structure(*M, locationMapping, blockMapping);
    structure.analyzeBeforeRelationsAnalysis();

    RelationsAnalyzer ra(*M, locationMapping, blockMapping, structure);
    unsigned num_iter = ra.analyze(max_iter);

    structure.analyzeAfterRelationsAnalysis();

    tm.stop();
    tm.report("INFO: Value Relations analysis took");
    std::cerr << "INFO: The analysis made " << num_iter << " passes." << std::endl;
    std::cerr << std::endl;

    AnalysisGraph analysis(locationMapping, structure);

    for (const auto& instrLoc : locationMapping) {
        const llvm::Instruction* instr = instrLoc.first;
        if (auto gep = llvm::dyn_cast<llvm::GetElementPtrInst>(instr)) {
            const llvm::Value* size = llvm::ConstantInt::get(
                    llvm::Type::getInt32Ty(M->getContext()),
                    gep->getResultElementType()->getPrimitiveSizeInBits() / 8);
            std::cerr << analysis.isValidPointer(gep, size) << std::endl;
        }
    }

    if (todot) {
        std::cout << "digraph VR {\n";
        for (const auto& block : blockMapping) {
            for (const auto& loc : block.second->locations) {
                std::cout << "  NODE" << loc->id;
                std::cout << "[label=\"";
                std::cout << "LOCATION " << loc->id << "\\n";
                loc->relations.dump();
                std::cout << "\"];\n";
            }
        }

        unsigned dummyIndex = 0;
        for (const auto& block : blockMapping) {
            for (const auto& loc : block.second->locations) {
                for (const auto& succ : loc->successors) {
                    if (succ->target)
                        std::cout << "  NODE" << loc->id << " -> NODE" << succ->target->id;
                    else {
                        std::cout << "DUMMY_NODE" << ++dummyIndex << std::endl;
                        std::cout << "  NODE" << loc->id << " -> DUMMY_NODE" << dummyIndex;
                    }
                    std::cout << " [label=\"";
                    succ->op->dump();
                    std::cout << "\"];\n";
                }
            }
        }
        std::cout << "}\n";
    }

    return 0;
}

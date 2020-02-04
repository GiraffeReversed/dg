#ifndef _DG_LLVM_VALUE_RELATION_GRAPH_ANALYZER_HPP_
#define _DG_LLVM_VALUE_RELATION_GRAPH_ANALYZER_HPP_

// ignore unused parameters in LLVM libraries
#if (__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

#include <llvm/IR/Value.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/CFG.h>

#if (__clang__)
#pragma clang diagnostic pop // ignore -Wunused-parameter
#else
#pragma GCC diagnostic pop
#endif

#include "GraphElements.hpp"
#include "RelationsGraph.hpp"

#ifndef NDEBUG
#include "getValName.h"
#endif

namespace dg {
namespace analysis {
namespace vr {


class GraphAnalyzer {
    const llvm::Module& module;

    // VRLocation corresponding to the state of the program BEFORE executing the instruction
    std::map<const llvm::Instruction *, VRLocation *>& locationMapping;
    std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blockMapping;

    GraphAnalyzer(const llvm::Module& m,
                  std::map<const llvm::Instruction *, VRLocation *>& locs,
                  std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blcs)
                  : module(m), locationMapping(locs), blockMapping(blcs) {}

    void analyze() {
        for (auto& pair : blockMapping) {

        }
    }

    void processOperation(VRLocation* source, VRLocation* target, VROp* op) {
        if (! target) return;

        assert(source && target && op);

    if (op->isNoop()) {
        return;
    } else if (op->isInstruction()) {
        processInstruction(source, target, static_cast<VRInstruction>(op).getInstruction());
    } else { // op is assume




    }

};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_VALUE_RELATION_GRAPH_ANALYZER_HPP_

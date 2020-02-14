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

    bool processOperation(VRLocation* source, VRLocation* target, VROp* op) const {
        if (! target) return;
        assert(source && target && op);

        RelationsGraph<llvm::Instruction*> newGraph = source->rg;
        
        if (op->isInstruction()) {
            processInstruction(newGraph, static_cast<VRInstruction *>(op).getInstruction());
        } else if (op->isAssume()) { 
            if (op->isAssumeBool())
                processAssumeBool(newGraph, static_cast<VRAssumeBool *>(op))
            else // isAssumeEqual
                processAssumeEqual(newGraph, static_cast<VRAssumeEqual *>(op))
        } // else op is noop

        // TODO handle loads

        if (relationsEqual(newGraph, target->rg))
            return false;
        
        target->rg.swap(newGraph);
        return true;
    }

    void processInstruction(RelationsGraph& newGraph, llvm::Instruction* inst) {

    }

    void processAssumeBool(RelationsGraph& newGraph, VRAssumeBool* assume) {
        const llmv::ICmpInst* icmp = llvm::dyn_cast<ICmpInst>(assume->getValue());
        assert(icmp);
        bool assumption = assume->getAssumption();

        const llvm::Value* op1 = icmp->getOperand(0);
        const llvm::Value* op2 = icmp->getOperand(1);

        switch (icmp->getSignedPredicate()) {
            case ICmpInst::Predicate::ICMP_EQ:
                newGraph.setEqual(op1, op2); break;

            case ICmpInst::Predicate::ICMP_NE:
                break; // DANGER, no information doesn't mean nonequal

            case ICmpInst::Predicate::ICMP_ULE:
            case ICmpInst::Predicate::ICMP_SLE:
                newGraph.setLesserEqual(op1, op2); break;

            case ICmpInst::Predicate::ICMP_ULT:
            case ICmpInst::Predicate::ICMP_SLT:
                newGraph.setLesser(op1, op2); break;

            case ICmpInst::Predicate::ICMP_UGE:
            case ICmpInst::Predicate::ICMP_SGE:
                newGraph.setLesser(op2, op1); break;

            case ICmpInst::Predicate::ICMP_UGT:
            case ICmpInst::Predicate::ICMP_SGT:
                newGraph.setLesserEqual(op2, op1); break;

            default:
#ifndef NDEBUG
                errs() << "Unhandled predicate in" << *icmp << "\n";
#endif
                abort();
        }
    }

    void processAssumeEqual(RelationsGraph& newGraph, VRAssumeEqual* assume) {
        const llvm::Value* val1 = assume->getValue();
        const llvm::Value* val2 = assume->getAssumption();
        newGraph.setEqual(val1, val2);
    }
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_VALUE_RELATION_GRAPH_ANALYZER_HPP_

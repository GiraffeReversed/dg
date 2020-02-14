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

using RelationsGraph = ::dg::vr::RelationsGraph<const llvm::Value*>;


class GraphAnalyzer {
    const llvm::Module& module;

    // VRLocation corresponding to the state of the program BEFORE executing the instruction
    const std::map<const llvm::Instruction *, VRLocation *>& locationMapping;
    const std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blockMapping;

    bool processOperation(VRLocation* source, VRLocation* target, VROp* op) const {
        if (! target) return false;
        assert(source && target && op);

        RelationsGraph newGraph = source->relations;
        
        if (op->isInstruction()) {
            processInstruction(newGraph, static_cast<VRInstruction *>(op)->getInstruction());
        } else if (op->isAssume()) { 
            if (op->isAssumeBool())
                processAssumeBool(newGraph, static_cast<VRAssumeBool *>(op));
            else // isAssumeEqual
                processAssumeEqual(newGraph, static_cast<VRAssumeEqual *>(op));
        } // else op is noop

        // TODO handle loads

        if (relationsEqual(newGraph, target->relations))
            return false;
        
        swap(target->relations, newGraph);
        return true;
    }

    void processInstruction(RelationsGraph& newGraph, const llvm::Instruction* inst) const {

    }

    void processAssumeBool(RelationsGraph& newGraph, VRAssumeBool* assume) const {
        const llvm::ICmpInst* icmp = llvm::dyn_cast<llvm::ICmpInst>(assume->getValue());
        assert(icmp);
        bool assumption = assume->getAssumption();

        const llvm::Value* op1 = icmp->getOperand(0);
        const llvm::Value* op2 = icmp->getOperand(1);

        llvm::ICmpInst::Predicate pred = assumption ?
                                         icmp->getSignedPredicate() : icmp->getInversePredicate();

        switch (pred) {
            case llvm::ICmpInst::Predicate::ICMP_EQ:
                newGraph.setEqual(op1, op2); break;

            case llvm::ICmpInst::Predicate::ICMP_NE:
                break; // DANGER, no information doesn't mean nonequal

            case llvm::ICmpInst::Predicate::ICMP_ULE:
            case llvm::ICmpInst::Predicate::ICMP_SLE:
                newGraph.setLesserEqual(op1, op2); break;

            case llvm::ICmpInst::Predicate::ICMP_ULT:
            case llvm::ICmpInst::Predicate::ICMP_SLT:
                newGraph.setLesser(op1, op2); break;

            case llvm::ICmpInst::Predicate::ICMP_UGE:
            case llvm::ICmpInst::Predicate::ICMP_SGE:
                newGraph.setLesser(op2, op1); break;

            case llvm::ICmpInst::Predicate::ICMP_UGT:
            case llvm::ICmpInst::Predicate::ICMP_SGT:
                newGraph.setLesserEqual(op2, op1); break;

            default:
#ifndef NDEBUG
                llvm::errs() << "Unhandled predicate in" << *icmp << "\n";
#endif
                abort();
        }
    }

    void processAssumeEqual(RelationsGraph& newGraph, VRAssumeEqual* assume) const {
        const llvm::Value* val1 = assume->getValue();
        const llvm::Value* val2 = assume->getAssumption();
        newGraph.setEqual(val1, val2);
    }

public:
    GraphAnalyzer(const llvm::Module& m,
                  std::map<const llvm::Instruction *, VRLocation *>& locs,
                  std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blcs)
                  : module(m), locationMapping(locs), blockMapping(blcs) {}

    void analyze() const {
        for (auto& pair : blockMapping) {

        }
    }
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_VALUE_RELATION_GRAPH_ANALYZER_HPP_

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

    using RelationsGraph = RelationsGraph<const llvm::Value*>;

    const llvm::Module& module;

    // VRLocation corresponding to the state of the program BEFORE executing the instruction
    const std::map<const llvm::Instruction *, VRLocation *>& locationMapping;
    const std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blockMapping;

    bool processOperation(VRLocation* source, VRLocation* target, VROp* op) {
        if (! target) return false;
        assert(source && target && op);

        RelationsGraph newGraph = source->relations;
        
        if (op->isInstruction()) {
            const llvm::Instruction* inst = static_cast<VRInstruction *>(op)->getInstruction();
            forgetInvalidated(newGraph, inst);
            processInstruction(newGraph, inst);
        } else if (op->isAssume()) { 
            if (op->isAssumeBool())
                processAssumeBool(newGraph, static_cast<VRAssumeBool *>(op));
            else // isAssumeEqual
                processAssumeEqual(newGraph, static_cast<VRAssumeEqual *>(op));
        } // else op is noop

        return andSwapIfChanged(target->relations, newGraph);
    }

    void forgetInvalidated(RelationsGraph& graph, const llvm::Instruction* inst) const {
        if (! inst->mayWriteToMemory() && ! inst->mayHaveSideEffects()) return;
        // DIFF does not ignore some intrinsic insts

        if (! llvm::isa<llvm::StoreInst>(inst)) {
            // unable to presume anything about such instruction
            graph.unsetAllLoads();
            return;
        }

        auto store = llvm::dyn_cast<llvm::StoreInst>(inst);
        const llvm::Value* memoryPtr = stripCastsAndGEPs(store->getPointerOperand());
        // TODO check against actual loads generation
        // what if load information is stored about cast or gep?

        if (! eqivToAlloca(graph.getEqual(memoryPtr))) {
            // we can't tell, where the instruction writes to
            graph.unsetAllLoads();
            return;
        }

        graph.unsetAllLoadsByPtr(memoryPtr);

        // unset all loads whose origin is unknown
        //   (since they may be aliases of written location)
        for (const auto& fromsValues : graph.getAllLoads()) {

            if (! eqivToAlloca(fromsValues.first))
                graph.unsetAllLoadsByPtr(fromsValues.first[0]); // aka first memoryPtr of bucket
        }
    }

    const llvm::Value* stripCastsAndGEPs(const llvm::Value* memoryPtr) const {
        memoryPtr = memoryPtr->stripPointerCasts();
        while (auto gep = llvm::dyn_cast<llvm::GetElementPtrInst>(memoryPtr)) {
            memoryPtr = gep->getPointerOperand()->stripPointerCasts();
        }
        return memoryPtr;
    }

    bool eqivToAlloca(const std::vector<const llvm::Value*>& froms) const {
        for (auto memoryPtr : froms) {
            memoryPtr = stripCastsAndGEPs(memoryPtr);
            if (llvm::isa<llvm::AllocaInst>(memoryPtr)) return true;
        }
        return false;
    }

    void storeGen(RelationsGraph& graph, const llvm::StoreInst* store) {
        graph.setLoad(store->getValueOperand(), store->getPointerOperand()->stripPointerCasts());
    }

    void loadGen(RelationsGraph& graph, const llvm::LoadInst* load) {
        graph.setLoad(load, load->getPointerOperand()->stripPointerCasts());
    }

    void gepGen(RelationsGraph& graph, const llvm::GetElementPtrInst* gep) {
        if (gep->hasAllZeroIndices())
            graph.setEqual(gep, gep->getPointerOperand());
        // TODO something more?
        // indices method gives iterator over indices
    }

    void extGen(RelationsGraph& graph, const llvm::CastInst* ext) {
        graph.setEqual(ext, ext->getOperand(0));
    }

    void addGen(RelationsGraph& graph, const llvm::BinaryOperator* add) {
        auto c1 = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(0));
        auto c2 = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(1));

        if (c1 && c2) {
            const llvm::APInt& sum = c1->getValue() + c2->getValue();
            return graph.setEqual(add, llvm::ConstantInt::get(c1->getType(), sum));
        }

        if (! c1 && ! c2) {
            // TODO if unsigned, result must be greater
            // but DANGER not true if overflowed
            return;
        }

        const llvm::Value* param = nullptr;
        if (c2) { c1 = c2; param = add->getOperand(0); }
        else param = add->getOperand(1);

        assert(c1 && add && param);
        // add = param + c1
        if (c1->isZero()) return graph.setEqual(add, param);
        
        else if (c1->isNegative()) {
            // c1 < 0  ==>  param + c1 < param
            graph.setLesser(add, param);

            // lesser < param  ==>  lesser <= param - 1
            if (c1->isMinusOne()) {
                std::vector<const llvm::Value*> sample = graph.getSampleLesser(param);
                for (const llvm::Value* lesser : sample)
                    graph.setLesserEqual(lesser, add);
            }

        } else {
            // c1 > 0 => param < param + c1
            graph.setLesser(param, add);

            // param < greater => param + 1 <= greater
            if (c1->isOne()) {
                std::vector<const llvm::Value*> sample = graph.getSampleGreater(param);
                for (const llvm::Value* greater : sample)
                    graph.setLesserEqual(add, greater);
            }
        }
    }

    void processInstruction(RelationsGraph& graph, const llvm::Instruction* inst) {
        switch(inst->getOpcode()) {
            case llvm::Instruction::Store:
                return storeGen(graph, llvm::dyn_cast<llvm::StoreInst>(inst));
            case llvm::Instruction::Load:
                return loadGen(graph, llvm::dyn_cast<llvm::LoadInst>(inst));
            case llvm::Instruction::GetElementPtr:
                return gepGen(graph, llvm::cast<llvm::GetElementPtrInst>(inst));
            case llvm::Instruction::ZExt:
            case llvm::Instruction::SExt: // (S)ZExt should not change value
                return extGen(graph, llvm::dyn_cast<llvm::CastInst>(inst));
            case llvm::Instruction::Add:
                return addGen(graph, llvm::dyn_cast<llvm::BinaryOperator>(inst));
            case llvm::Instruction::Sub:
                //return minusGen(I, source->equalities, E, Rel);
            case llvm::Instruction::Mul:
                //return mulGen(I, E, Rel);
            default:
                /*if (auto C = dyn_cast<CastInst>(I)) {
                    if (C->isLosslessCast() || C->isNoopCast(_M->getDataLayout())) {
                        return E.add(C, C->getOperand(0));
                    }
                }*/
                return;
        }
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
                newGraph.setLesserEqual(op2, op1); break;

            case llvm::ICmpInst::Predicate::ICMP_UGT:
            case llvm::ICmpInst::Predicate::ICMP_SGT:
                newGraph.setLesser(op2, op1); break;

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

    bool relatesInAll(const std::vector<VREdge*>& preds,
                      const llvm::Value* fst,
                      const llvm::Value* snd,
                      bool (RelationsGraph::*relates)(const llvm::Value*, const llvm::Value*) const) const {
                      // which is function pointer to isEqual, isLesser, or isLesserEqual

        for (const VREdge* predEdge : preds) {
            const RelationsGraph& predGraph = predEdge->source->relations;
            if (! (predGraph.*relates)(fst, snd))
                return false;
        }
        return true;
    }

    bool mergeRelations(VRLocation* location) {
        RelationsGraph newGraph;

        const std::vector<VREdge*>& preds = location->predecessors;
        std::vector<const llvm::Value*> values = preds[0]->source->relations.getAllValues();

        for (const llvm::Value* fst : values) {
            for (const llvm::Value* snd : values) {

                if (relatesInAll(preds, fst, snd, &RelationsGraph::isEqual))
                    newGraph.setEqual(fst, snd);
                if (relatesInAll(preds, fst, snd, &RelationsGraph::isLesser))
                    newGraph.setLesser(fst, snd);
                if (relatesInAll(preds, snd, fst, &RelationsGraph::isLesser))
                    newGraph.setLesser(snd, fst);
                if (relatesInAll(preds, fst, snd, &RelationsGraph::isLesserEqual))
                    newGraph.setLesserEqual(fst, snd);
                if (relatesInAll(preds, snd, fst, &RelationsGraph::isLesserEqual))
                    newGraph.setLesserEqual(snd, fst);
            }
        }

        return andSwapIfChanged(location->relations, newGraph);
    }

    bool loadsInAll(const std::vector<VREdge*>& preds, const llvm::Value* from, const llvm::Value* value) const {
        for (const VREdge* predEdge : preds) {
            const RelationsGraph& predGraph = predEdge->source->relations;
            if (! predGraph.isLoad(from, value))
                // DANGER does it suffice that from equals to value's ptr (before instruction on edge)?
                return false;
        }
        return true;
    }

    bool mergeLoads(VRLocation* location) {
        RelationsGraph newGraph = location->relations;

        const std::vector<VREdge*>& preds = location->predecessors;
        const auto& loadBucketPairs = preds[0]->source->relations.getAllLoads();

        for (const auto& fromsValues : loadBucketPairs) {
            for (const llvm::Value* from : fromsValues.first) {
                for (const llvm::Value* val : fromsValues.second) {
                    if (loadsInAll(location->predecessors, from, val))
                        newGraph.setLoad(val, from);
                }
            }
        }

        return andSwapIfChanged(location->relations, newGraph);
    }

    bool andSwapIfChanged(RelationsGraph& oldGraph, RelationsGraph& newGraph) {
        if (oldGraph == newGraph)
            return false;
            
        swap(oldGraph, newGraph);
        return true;
    }

public:
    GraphAnalyzer(const llvm::Module& m,
                  std::map<const llvm::Instruction *, VRLocation *>& locs,
                  std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blcs)
                  : module(m), locationMapping(locs), blockMapping(blcs) {}

    void analyze() {
        for (auto& pair : blockMapping) {
            auto& vrblockPtr = pair.second;

            for (auto& locationPtr : vrblockPtr->locations) {
                if (locationPtr->predecessors.size() > 1) {
                    mergeRelations(locationPtr.get());
                    mergeLoads(locationPtr.get());
                } else if (locationPtr->predecessors.size() == 1) {
                    VREdge* edge = locationPtr->predecessors[0];
                    processOperation(edge->source, edge->target, edge->op.get());
                } // else no predecessors => nothing to be passed
            }

        }
    }
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_VALUE_RELATION_GRAPH_ANALYZER_HPP_

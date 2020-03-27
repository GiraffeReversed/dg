#ifndef _DG_LLVM_VALUE_RELATION_RELATIONS_ANALYZER_HPP_
#define _DG_LLVM_VALUE_RELATION_RELATIONS_ANALYZER_HPP_

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

#include <algorithm>

#include "GraphElements.hpp"
#include "RelationsGraph.hpp"
#include "StructureAnalyzer.hpp"

#ifndef NDEBUG
#include "getValName.h"
#endif

namespace dg {
namespace analysis {
namespace vr {


class RelationsAnalyzer {

    const llvm::Module& module;

    // VRLocation corresponding to the state of the program BEFORE executing the instruction
    const std::map<const llvm::Instruction *, VRLocation *>& locationMapping;
    const std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blockMapping;

    // holds information about structural properties of analyzed module
    // like set of instructions executed in loop starging at given location
    // or possibly set of values defined at given location
    const StructureAnalyzer& structure;

    bool processOperation(VRLocation* source, VRLocation* target, VROp* op) {
        if (! target) return false;
        assert(source && target && op);

        RelationsGraph& newGraph = target->relations;

        bool changed = false;
        changed |= newGraph.mergeRelations(source->relations);
        changed |= newGraph.mergeCallRelations(source->relations);
        std::cerr << "after dump" << std::endl;
        newGraph.ddump();

        if (op->isInstruction()) {
            const llvm::Instruction* inst = static_cast<VRInstruction *>(op)->getInstruction();
            changed |= newGraph.mergeLoads(source->relations, instructionInvalidates(source->relations, inst));
            changed |= processInstruction(newGraph, inst);

        } else if (op->isAssume()) {
            if (op->isAssumeBool())
                changed |= processAssumeBool(newGraph, static_cast<VRAssumeBool *>(op));
            else // isAssumeEqual
                changed |= processAssumeEqual(newGraph, static_cast<VRAssumeEqual *>(op));
            changed |= newGraph.mergeLoads(source->relations); // we have to manage phi before loads

        } else  // op is noop
            changed |= newGraph.mergeLoads(source->relations);

        //swap(newGraph, target->relations);
        return changed;
    }

    bool forgetInvalidated(RelationsGraph& graph, const llvm::Instruction* inst) const {
        bool changed = false;
        for (const llvm::Value* invalid : instructionInvalidates(graph, inst))
            changed |= graph.unsetAllLoadsByPtr(invalid);

        return changed;
    }

    std::set<const llvm::Value*>
    instructionInvalidates(const RelationsGraph& graph,
                           const llvm::Instruction* inst) const {

        if (! inst->mayWriteToMemory() && ! inst->mayHaveSideEffects())
            return std::set<const llvm::Value*>();
        // DIFF does not ignore some intrinsic insts

        // handle nondet_int individually just because
        if (auto call = llvm::dyn_cast<llvm::CallInst>(inst)) {
            auto function = call->getCalledFunction();
            if (function && function->getName().equals("__VERIFIER_nondet_int"))
                return std::set<const llvm::Value*>();
        }

        if (! llvm::isa<llvm::StoreInst>(inst)) { // most probably CallInst
            // unable to presume anything about such instruction

            std::set<const llvm::Value*> allFroms;
            for (const auto& fromsValues : graph.getAllLoads()) {
                allFroms.insert(fromsValues.first[0]);
                // no need to add all froms, a sample is enough
            }
            return allFroms;
        }

        std::set<const llvm::Value*> writtenTo;

        auto store = llvm::cast<llvm::StoreInst>(inst);
        const llvm::Value* memoryPtr = stripCastsAndGEPs(store->getPointerOperand());
        // TODO check against actual loads generation
        // what if load information is stored about cast or gep?

        // DANGER TODO unset everything in between too
        writtenTo.insert(memoryPtr); // unset underlying memory
        writtenTo.insert(store->getPointerOperand()); // unset pointer itself

        if (! equivToAlloca(graph.getEqual(memoryPtr))) {
            // we can't tell, where the instruction writes to
            //     except that it can't be memory, that surely has no alias

            for (const auto& fromsValues : graph.getAllLoads()) {
                for (const llvm::Value* from : fromsValues.first) {
                    if (mayHaveAlias(llvm::cast<llvm::User>(from))) {
                        writtenTo.insert(from);
                        break;
                    } // else we may remember this load
                }
            }
            return writtenTo;
        }

        // unset all loads whose origin is unknown and may have and alias
        //   (since they may be aliases of written location)
        for (const auto& fromsValues : graph.getAllLoads()) {

            if (! equivToAlloca(fromsValues.first))
                for (const llvm::Value* from : fromsValues.first) {
                    if (mayHaveAlias(llvm::cast<llvm::User>(from))) {
                        writtenTo.insert(from);
                        break;
                    }
                }
        }

        return writtenTo;
    }

    static const llvm::Value* stripCastsAndGEPs(const llvm::Value* memoryPtr) {
        memoryPtr = memoryPtr->stripPointerCasts();
        while (auto gep = llvm::dyn_cast<llvm::GetElementPtrInst>(memoryPtr)) {
            memoryPtr = gep->getPointerOperand()->stripPointerCasts();
        }
        return memoryPtr;
    }

    static bool equivToAlloca(const std::vector<const llvm::Value*>& froms) {
        for (auto memoryPtr : froms) {
            memoryPtr = stripCastsAndGEPs(memoryPtr);
            if (llvm::isa<llvm::AllocaInst>(memoryPtr)) return true;
        }
        return false;
    }

    bool storeGen(RelationsGraph& graph, const llvm::StoreInst* store) {
        return graph.setLoad(store->getPointerOperand()->stripPointerCasts(), store->getValueOperand());
    }

    bool loadGen(RelationsGraph& graph, const llvm::LoadInst* load) {
        return graph.setLoad(load->getPointerOperand()->stripPointerCasts(), load);
    }

    bool gepGen(RelationsGraph& graph, const llvm::GetElementPtrInst* gep) {
        bool changed = false;
        if (gep->hasAllZeroIndices())
            changed |= graph.setEqual(gep, gep->getPointerOperand());

        for (auto& fromsValues : graph.getAllLoads()) {
            for (const llvm::Value* from : fromsValues.first) {
                if (auto otherGep = llvm::dyn_cast<llvm::GetElementPtrInst>(from)) {
                    if (operandsEqual(graph, gep, otherGep, true))
                        changed |= graph.setEqual(gep, otherGep);
                }
            }
        }
        // TODO something more?
        // indices method gives iterator over indices
        return changed;
    }

    bool extGen(RelationsGraph& graph, const llvm::CastInst* ext) {
        return graph.setEqual(ext, ext->getOperand(0));
    }

    bool addGen(RelationsGraph& graph, const llvm::BinaryOperator* add) {
        auto c1 = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(0));
        auto c2 = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(1));
        // TODO check wheter equal to constant

        bool changed = false;
        changed |= solveEquality(graph, add);
        changed |= solveCommutativity(graph, add);

        if ((c1 && c2) || (! c1 && ! c2))
            return changed | solvesSameType(graph, c1, c2, add);

        const llvm::Value* param = nullptr;
        if (c2) { c1 = c2; param = add->getOperand(0); }
        else param = add->getOperand(1);

        assert(c1 && add && param);
        // add = param + c1
        if (c1->isZero()) return changed | graph.setEqual(add, param);
        
        else if (c1->isNegative()) {
            // c1 < 0  ==>  param + c1 < param
            changed |= graph.setLesser(add, param);

            // lesser < param  ==>  lesser <= param + (-1)
            if (c1->isMinusOne())
                changed |= solvesDiffOne(graph, param, add, true);

        } else {
            // c1 > 0 => param < param + c1
            changed |= graph.setLesser(param, add);

            // param < greater => param + 1 <= greater
            if (c1->isOne())
                changed |= solvesDiffOne(graph, param, add, false);
        }

        const llvm::ConstantInt* constBound = graph.getLesserEqualConstant(param);
        if (constBound) {
            const llvm::APInt& boundResult = constBound->getValue() + c2->getValue();
            const llvm::Constant* llvmResult = llvm::ConstantInt::get(add->getType(), boundResult);
            if (graph.isLesser(constBound, param)) changed |= graph.setLesser(llvmResult, add);
            else if (graph.isEqual(constBound, param)) changed |= graph.setEqual(llvmResult, add);
            else changed |= graph.setLesserEqual(llvmResult, add);
        }
        return changed;
    }

    bool subGen(RelationsGraph& graph, const llvm::BinaryOperator* sub) {
        auto c1 = llvm::dyn_cast<llvm::ConstantInt>(sub->getOperand(0));
        auto c2 = llvm::dyn_cast<llvm::ConstantInt>(sub->getOperand(1));
        // TODO check wheter equal to constant

        bool changed = false;
        changed |= solveEquality(graph, sub);

        if ((c1 && c2) || (! c1 && ! c2))
            return changed | solvesSameType(graph, c1, c2, sub);

        if (c1) {
            // TODO collect something here?
            return changed;
        }

        const llvm::Value* param = sub->getOperand(0);
        assert(c2 && sub && param);
        // sub = param - c1
        if (c2->isZero()) return changed | graph.setEqual(sub, param);
        
        else if (c2->isNegative()) {
            // c1 < 0  ==>  param < param - c1
            changed |= graph.setLesser(param, sub);

            // param < greater ==> param - (-1) <= greater
            if (c2->isMinusOne())
                changed |= solvesDiffOne(graph, param, sub, false);

        } else {
            // c1 > 0 => param - c1 < param
            changed |= graph.setLesser(sub, param);

            // lesser < param  ==>  lesser <= param - 1
            if (c2->isOne())
                changed |= solvesDiffOne(graph, param, sub, true);
        }

        const llvm::ConstantInt* constBound = graph.getLesserEqualConstant(param);
        if (constBound) {
            const llvm::APInt& boundResult = constBound->getValue() - c2->getValue();
            const llvm::Constant* llvmResult = llvm::ConstantInt::get(sub->getType(), boundResult);
            
            if (graph.isLesser(constBound, param)) changed |= graph.setLesser(llvmResult, sub);
            else if (graph.isEqual(constBound, param)) changed |= graph.setEqual(llvmResult, sub);
            else changed |= graph.setLesserEqual(llvmResult, sub);
        }
        return changed;
    }

    bool mulGen(RelationsGraph& graph, const llvm::BinaryOperator* mul) {
        auto c1 = llvm::dyn_cast<llvm::ConstantInt>(mul->getOperand(0));
        auto c2 = llvm::dyn_cast<llvm::ConstantInt>(mul->getOperand(1));
        // TODO check wheter equal to constant

        bool changed = false;
        changed |= solveEquality(graph, mul);
        changed |= solveCommutativity(graph, mul);

        if ((c1 && c2) || (! c1 && ! c2))
            return changed | solvesSameType(graph, c1, c2, mul);

        const llvm::Value* param = nullptr;
        if (c2) { c1 = c2; param = mul->getOperand(0); }
        else param = mul->getOperand(1);

        assert(c1 && mul && param);
        // mul = param + c1
        if (c1->isZero()) changed |= graph.setEqual(mul, c1);
        else if (c1->isOne()) changed |= graph.setEqual(mul, param);

        // TODO collect something here?
        return changed;
    }

    bool solvesSameType(RelationsGraph& graph,
                        const llvm::ConstantInt* c1, const llvm::ConstantInt* c2,
                        const llvm::BinaryOperator* op) {
        if (c1 && c2) {
            llvm::APInt result;
            
            switch(op->getOpcode()) {
                case llvm::Instruction::Add:
                    result = c1->getValue() + c2->getValue(); break;
                case llvm::Instruction::Sub:
                    result = c1->getValue() - c2->getValue(); break;
                case llvm::Instruction::Mul:
                    result = c1->getValue() * c2->getValue(); break;
                default:
                    assert(0 && "solvesSameType: shouldn't handle any other operation");
            }
            return graph.setEqual(op, llvm::ConstantInt::get(c1->getType(), result));
        }

        // else ! c1 && ! c2
        llvm::Type* i32 = llvm::Type::getInt32Ty(op->getContext());
        const llvm::Constant* one = llvm::ConstantInt::getSigned(i32, 1);
        const llvm::Constant* minusOne = llvm::ConstantInt::getSigned(i32, -1);

        const llvm::Value* fst = op->getOperand(0);
        const llvm::Value* snd = op->getOperand(1);

        bool changed = false;
        switch (op->getOpcode()) {
            case llvm::Instruction::Add:
                if (graph.isLesserEqual(one, fst)) changed |= graph.setLesser(snd, op);
                if (graph.isLesserEqual(one, snd)) changed |= graph.setLesser(fst, op);
                if (graph.isLesserEqual(fst, minusOne)) changed |= graph.setLesser(op, snd);
                if (graph.isLesserEqual(snd, minusOne)) changed |= graph.setLesser(op, fst);
                break;
            case llvm::Instruction::Sub:
                if (graph.isLesserEqual(one, snd)) changed |= graph.setLesser(op, fst);
                if (graph.isLesserEqual(snd, minusOne)) changed |= graph.setLesser(fst, op);
                break;
            default:
                break;
        }
        return changed;
    }

    bool solvesDiffOne(RelationsGraph& graph,
                       const llvm::Value* param,
                       const llvm::BinaryOperator* op,
                       bool getLesser) {

        std::vector<const llvm::Value*> sample = getLesser ?
                    graph.getSampleLesser(param) : graph.getSampleGreater(param);

        bool changed = false;
        for (const llvm::Value* value : sample)
            if (getLesser) changed |= graph.setLesserEqual(value, op);
            else           changed |= graph.setLesserEqual(op, value);
        return changed;
    }

    bool operandsEqual(RelationsGraph& graph,
                       const llvm::Instruction* fst,
                       const llvm::Instruction* snd,
                       bool sameOrder) const { // false means checking in reverse order
        unsigned total = fst->getNumOperands();
        if (total != snd->getNumOperands()) return false;

        for (unsigned i = 0; i < total; ++i) {
            unsigned otherI = sameOrder ? i : total - i - 1;

            if (! graph.isEqual(fst->getOperand(i), snd->getOperand(otherI))) return false;
        }
        return true;
    }

    bool solveByOperands(RelationsGraph& graph, const llvm::BinaryOperator* operation, bool sameOrder) {
        bool changed = false;
        for (auto same : structure.getInstructionSetFor(operation->getOpcode())) {
            auto sameOperation = llvm::dyn_cast<const llvm::BinaryOperator>(same);

            if (operandsEqual(graph, operation, sameOperation, sameOrder))
                changed |= graph.setEqual(operation, sameOperation);
        }
        return changed;
    }

    bool solveEquality(RelationsGraph& graph, const llvm::BinaryOperator* operation) {
        return solveByOperands(graph, operation, true);
    }

    bool solveCommutativity(RelationsGraph& graph, const llvm::BinaryOperator* operation) {
        return solveByOperands(graph, operation, false);
    }

    bool remGen(RelationsGraph& graph, const llvm::BinaryOperator* rem) {
        assert(rem);
        const llvm::Constant* zero = llvm::ConstantInt::getSigned(rem->getType(), 0);

        if (! graph.isLesserEqual(zero, rem->getOperand(0))) return false;

        bool changed = false; 
        changed |= graph.setLesserEqual(zero, rem);
        changed |= graph.setLesser(rem, rem->getOperand(1));
        return changed;
    }

    bool castGen(RelationsGraph& graph, const llvm::CastInst* cast) {
        if (cast->isLosslessCast() || cast->isNoopCast(module.getDataLayout()))
            return graph.setEqual(cast, cast->getOperand(0));
        return false;
    }

    bool processInstruction(RelationsGraph& graph, const llvm::Instruction* inst) {
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
                return subGen(graph, llvm::dyn_cast<llvm::BinaryOperator>(inst));
            case llvm::Instruction::Mul:
                return mulGen(graph, llvm::dyn_cast<llvm::BinaryOperator>(inst));
            case llvm::Instruction::SRem:
            case llvm::Instruction::URem:
                return remGen(graph, llvm::dyn_cast<llvm::BinaryOperator>(inst));
            default:
                if (auto cast = llvm::dyn_cast<llvm::CastInst>(inst)) {
                    return castGen(graph, cast);
                }
        }
        return false;
    } 

    bool processAssumeBool(RelationsGraph& newGraph, VRAssumeBool* assume) const {
        if (llvm::isa<llvm::ICmpInst>(assume->getValue()))
            return processICMP(newGraph, assume);
        if (llvm::isa<llvm::PHINode>(assume->getValue()))
            return processPhi(newGraph, assume);
        return false;
    }

    bool processICMP(RelationsGraph& newGraph, VRAssumeBool* assume) const {
        const llvm::ICmpInst* icmp = llvm::cast<llvm::ICmpInst>(assume->getValue());
        bool assumption = assume->getAssumption();

        const llvm::Value* op1 = icmp->getOperand(0);
        const llvm::Value* op2 = icmp->getOperand(1);

        llvm::ICmpInst::Predicate pred = assumption ?
            icmp->getSignedPredicate() : icmp->getInversePredicate();

        switch (pred) {
            case llvm::ICmpInst::Predicate::ICMP_EQ:
                return newGraph.setEqual(op1, op2);

            case llvm::ICmpInst::Predicate::ICMP_NE:
                return newGraph.setNonEqual(op1, op2);

            case llvm::ICmpInst::Predicate::ICMP_ULE:
            case llvm::ICmpInst::Predicate::ICMP_SLE:
                return newGraph.setLesserEqual(op1, op2);

            case llvm::ICmpInst::Predicate::ICMP_ULT:
            case llvm::ICmpInst::Predicate::ICMP_SLT:
                return newGraph.setLesser(op1, op2);

            case llvm::ICmpInst::Predicate::ICMP_UGE:
            case llvm::ICmpInst::Predicate::ICMP_SGE:
                return newGraph.setLesserEqual(op2, op1);

            case llvm::ICmpInst::Predicate::ICMP_UGT:
            case llvm::ICmpInst::Predicate::ICMP_SGT:
                return newGraph.setLesser(op2, op1);

            default:
        #ifndef NDEBUG
                llvm::errs() << "Unhandled predicate in" << *icmp << "\n";
        #endif
                abort();
        }
    }

    bool processPhi(RelationsGraph& newGraph, VRAssumeBool* assume) const {
        const llvm::PHINode* phi = llvm::cast<llvm::PHINode>(assume->getValue());
        bool assumption = assume->getAssumption();

        const llvm::BasicBlock* assumedPred = nullptr;
        for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
            const llvm::Value* result = phi->getIncomingValue(i);
            auto constResult = llvm::dyn_cast<llvm::ConstantInt>(result);
            if (! constResult || (constResult
                    && ((constResult->isOne() && assumption)
                    || (constResult->isZero() && ! assumption)))) {
                if (! assumedPred) assumedPred = phi->getIncomingBlock(i);
                else return false; // we found other viable incoming block
            }
        }
        assert (assumedPred);

        VRBBlock* vrbblock = blockMapping.at(assumedPred).get();
        VRLocation* source = vrbblock->last();
        return newGraph.mergeAll(source->relations);
    }

    bool processAssumeEqual(RelationsGraph& newGraph, VRAssumeEqual* assume) const {
        const llvm::Value* val1 = assume->getValue();
        const llvm::Value* val2 = assume->getAssumption();
        return newGraph.setEqual(val1, val2);
    }

    bool relatesInAll(const std::vector<VRLocation*>& locations,
                      const llvm::Value* fst,
                      const llvm::Value* snd,
                      bool (RelationsGraph::*relates)(const llvm::Value*, const llvm::Value*) const) const {
                      // which is function pointer to isEqual, isLesser, or isLesserEqual

        for (const VRLocation* vrloc : locations) {
            if (! (vrloc->relations.*relates)(fst, snd))
                return false;
        }
        return true;
    }

    bool relatesByLoadInAll(const std::vector<VRLocation*>& locations,
                            const llvm::Value* related,
                            const llvm::Value* from,
                            bool (RelationsGraph::*relates)(const llvm::Value*, const llvm::Value*) const,
                            bool flip) const {
        
        for (const VRLocation* vrloc : locations) {
            const std::vector<const llvm::Value*>& loaded = vrloc->relations.getValsByPtr(from);
            if (loaded.empty()) return false;
            if (! flip && ! (vrloc->relations.*relates)(related, loaded[0])) return false;
            if (  flip && ! (vrloc->relations.*relates)(loaded[0], related)) return false;
        }
        return true;
    }

    bool mergeRelations(VRLocation* location) {
        return mergeRelations(location->getPredLocations(), location);
    }

    bool mergeRelations(const std::vector<VRLocation*>& preds, VRLocation* location) {
        if (preds.empty()) return false;

        RelationsGraph& newGraph = location->relations;
        RelationsGraph& oldGraph = preds[0]->relations;
        std::vector<const llvm::Value*> values = oldGraph.getAllValues();

        bool changed = false;
        // merge from all predecessors
        for (auto valueIt = values.begin(); valueIt != values.end(); ++valueIt) {
            const llvm::Value* val = *valueIt;

            for (auto it = oldGraph.begin_lesserEqual(val);
                      it != oldGraph.end_lesserEqual(val);
                      ++it) {
                const llvm::Value* related; Relation relation;
                std::tie(related, relation) = *it;

                if (related == val) continue;

                switch (relation) {
                    case Relation::EQ:
                        if (relatesInAll(preds, related, val, &RelationsGraph::isEqual)) {
                            changed |= newGraph.setEqual(related, val);

                            auto found = std::find(values.begin(), values.end(), related);
                            if (found != values.end()) {
                                values.erase(found);
                                valueIt = std::find(values.begin(), values.end(), val);
                            }
                        }
                        break;

                    case Relation::LT:
                        if (relatesInAll(preds, related, val, &RelationsGraph::isLesser))
                            changed |= newGraph.setLesser(related, val);
                        break;

                    case Relation::LE:
                        if (relatesInAll(preds, related, val, &RelationsGraph::isLesserEqual))
                            changed |= newGraph.setLesserEqual(related, val);
                        break;

                    default: assert(0 && "going down, not up");
                }
            }
        }

        // merge relations from tree predecessor only
        VRLocation* treePred = getTreePred(location);
        const RelationsGraph& treePredGraph = treePred->relations;

        if (location->isJustLoopJoin())
            changed |= newGraph.mergeRelations(treePredGraph);

        // simply pass xor relations over tree edge
        newGraph.getCallRelations() = treePredGraph.getCallRelations();

        return changed;
    }

    bool loadsInAll(const std::vector<VRLocation*>& locations, const llvm::Value* from, const llvm::Value* value) const {
        for (const VRLocation* vrloc : locations) {
            if (! vrloc->relations.isLoad(from, value))
                // DANGER does it suffice that from equals to value's ptr (before instruction on edge)?
                return false;
        }
        return true;
    }

    bool loadsSomethingInAll(const std::vector<VRLocation*>& locations, const llvm::Value* from) const {
        for (const VRLocation* vrloc : locations) {
            if (! vrloc->relations.hasLoad(from))
                return false;
        }
        return true;
    }

    bool mergeLoads(VRLocation* location) {
        return mergeLoads(location->getPredLocations(), location);
    }

    bool mergeLoads(const std::vector<VRLocation*>& preds, VRLocation* location) {
        if (preds.empty()) return false;

        RelationsGraph& newGraph = location->relations;
        const auto& loadBucketPairs = preds[0]->relations.getAllLoads();

        bool changed = false;

        // merge loads from all predecessors
        for (const auto& fromsValues : loadBucketPairs) {
            for (const llvm::Value* from : fromsValues.first) {
                for (const llvm::Value* val : fromsValues.second) {
                    if (loadsInAll(preds, from, val))
                        changed |= newGraph.setLoad(from, val);
                }
            }
        }

        // merge loads from outloop predecessor, that are not invalidated
        // inside the loop
        if (location->isJustLoopJoin()) {

            std::set<const llvm::Value*> allInvalid;

            for (VRLocation* pred : preds) { // TODO unnecessary to do for all preds
                RelationsGraph& graph = pred->relations;

                for (const auto* inst : structure.getInloopValues(location)) {
                    auto invalid = instructionInvalidates(graph, inst);
                    allInvalid.insert(invalid.begin(), invalid.end());
                }
            }

            VRLocation* treePred = getTreePred(location);
            const RelationsGraph& oldGraph = treePred->relations;

            for (const auto& fromsValues : oldGraph.getAllLoads()) {
                if (! anyInvalidated(allInvalid, fromsValues.first)) {
                    for (auto from : fromsValues.first) {
                        for (auto val : fromsValues.second) {
                            changed |= newGraph.setLoad(from, val);
                        }
                    }
                }
            }
        }

        return changed;
    }

    VRLocation* getTreePred(VRLocation* location) const {
        VRLocation* treePred = nullptr;
        for (VREdge* predEdge : location->predecessors) {
            if (predEdge->type == EdgeType::TREE) treePred = predEdge->source;
        }
        assert(treePred);
        return treePred;
    }

    bool hasConflictLoad(const std::vector<VRLocation*>& preds,
                         const llvm::Value* from,
                         const llvm::Value* val) {
        for (const VRLocation* pred : preds) {
            for (const auto& fromsValues : pred->relations.getAllLoads()) {
                auto findFrom = std::find(fromsValues.first.begin(), fromsValues.first.end(), from);
                auto findVal = std::find(fromsValues.second.begin(), fromsValues.second.end(), val);
                
                if (findFrom != fromsValues.first.end() && findVal == fromsValues.second.end())
                    return true;
            }
        }
        return false;
    }

    bool anyInvalidated(const std::set<const llvm::Value*>& allInvalid,
                        const std::vector<const llvm::Value*>& froms) {
        for (auto from : froms) {
            if (allInvalid.find(from) != allInvalid.end()) return true;
        }
        return false;
    }

    bool mergeRelationsByLoads(VRLocation* location) {
        return mergeRelationsByLoads(location->getPredLocations(), location);
    }

    bool mergeRelationsByLoads(const std::vector<VRLocation*>& preds, VRLocation* location) {
        RelationsGraph& newGraph = location->relations;

        std::vector<const llvm::Value*> froms;
        for (auto fromsValues : preds[0]->relations.getAllLoads()) {
            for (auto from : fromsValues.first) {
                if (isGoodFromForPlaceholder(preds, from, fromsValues.second))
                    froms.emplace_back(from);
            }
        }

        bool changed = false;

        // infer some invariants in loop
        if (preds.size() == 2 && location->isJustLoopJoin()) {
            for (const llvm::Value* from : froms) {
                const auto& predEdges = location->predecessors;

                VRLocation* outloopPred = predEdges[0]->type == EdgeType::BACK ?
                                            predEdges[1]->source : predEdges[0]->source;
                VRLocation* inloopPred = predEdges[0]->type == EdgeType::BACK ?
                                            predEdges[0]->source : predEdges[1]->source;

                std::vector<const llvm::Value*> valsInloop
                    = inloopPred->relations.getValsByPtr(from);
                if (valsInloop.empty()) continue;
                const llvm::Value* valInloop = valsInloop[0];

                std::vector<const llvm::Value*> allRelated
                    = inloopPred->relations.getAllRelated(valInloop);

                // get some value, that is both related to the value loaded from
                // from at the end of the loop and at the same time is loaded
                // from from in given loop
                const llvm::Value* firstLoadInLoop = nullptr;
                for (const auto* val : structure.getInloopValues(location)) {

                    const RelationsGraph& relations = locationMapping.at(val)->relations;
                    auto invalidated = instructionInvalidates(relations, val);
                    if (invalidated.find(from) != invalidated.end()) break;

                    if (std::find(allRelated.begin(), allRelated.end(), val)
                            != allRelated.end()) {
                        if (auto load = llvm::dyn_cast<llvm::LoadInst>(val)) {
                            if (load->getPointerOperand() == from) {
                                firstLoadInLoop = load;
                                break;
                            }
                        }
                    }
                }

                // set all preserved relations
                if (firstLoadInLoop) {

                    // get all equal vals from load from outloopPred
                    std::vector<const llvm::Value*> valsOutloop
                        = outloopPred->relations.getValsByPtr(from);
                    if (valsOutloop.empty()) continue;

                    bool setSomething = false;
                    const unsigned* temp = newGraph.getPlaceholderBucket(from);
                    unsigned placeholder = temp ? *temp : newGraph.newPlaceholderBucket();
                    bool newPlaceholder = temp == nullptr;

                    if (inloopPred->relations.isLesser(firstLoadInLoop, valInloop))
                        setSomething |= newGraph.setLesserEqual(valsOutloop[0], placeholder);

                    if (inloopPred->relations.isLesser(valInloop, firstLoadInLoop))
                        setSomething |= newGraph.setLesserEqual(placeholder, valsOutloop[0]);

                    if (setSomething) {
                        newGraph.setLoad(from, placeholder);

                        for (const llvm::Value* val : valsOutloop)
                            newGraph.setEqual(valsOutloop[0], val);

                        changed = true;
                    } else if (newPlaceholder)
                        newGraph.erasePlaceholderBucket(placeholder);
                    
                }
            }
        }

        for (const llvm::Value* from : froms)
            changed |= intersectByLoad(preds, from, newGraph);

        if (location->isJustLoopJoin()) {
            VRLocation* treePred = getTreePred(location);

            for (auto fromsValues : treePred->relations.getAllLoads()) {
                for (const llvm::Value* from : fromsValues.first) {
                    std::vector<VRLocation*> locationsAfterInvalidating = { treePred };

                    // get all locations which influence value loaded from from
                    for (const llvm::Instruction* invalidating : structure.getInloopValues(location)) {
                        const RelationsGraph& relations = locationMapping.at(invalidating)->relations;
                        auto invalidated = instructionInvalidates(relations, invalidating);

                        if (invalidated.find(from) != invalidated.end()) {
                            locationsAfterInvalidating.emplace_back(locationMapping.at(invalidating)->getSuccLocations()[0]);
                        }
                    }

                    if (! isGoodFromForPlaceholder(locationsAfterInvalidating, from, fromsValues.second)) continue;

                    changed |= intersectByLoad(locationsAfterInvalidating, from, newGraph);
                }
            }
        }

        return changed;

    }

    bool isGoodFromForPlaceholder(const std::vector<VRLocation*>& preds, const llvm::Value* from, const std::vector<const llvm::Value*> values) {
         if (! loadsSomethingInAll(preds, from)) return false;

        for (auto value : values) {
            if (loadsInAll(preds, from, value)) return false;
        }
        return true;
    }

    bool intersectByLoad(const std::vector<VRLocation*>& preds, const llvm::Value* from, RelationsGraph& newGraph) {
        const llvm::ConstantInt* bound = nullptr;
        for (VRLocation* pred : preds) {
            const RelationsGraph& predGraph = pred->relations;

            auto& loads = predGraph.getValsByPtr(from);
            if (loads.empty()) return false;
            
            const llvm::ConstantInt* value = predGraph.getLesserEqualConstant(loads[0]);
            if (! value) {
                bound = nullptr;
                break;
            }

            if (! bound || value->getValue().slt(bound->getValue())) bound = value;
        }

        bool setSomething = false;
        const unsigned* temp = newGraph.getPlaceholderBucket(from);
        unsigned placeholder = temp ? *temp : newGraph.newPlaceholderBucket();
        bool newPlaceholder = temp == nullptr;


        if (bound)
            setSomething |= newGraph.setLesserEqual(bound, placeholder);

        const llvm::Value* loaded = preds[0]->relations.getValsByPtr(from)[0];

        bool changed = false;

        for (auto it = preds[0]->relations.begin_all(loaded);
                  it != preds[0]->relations.end_all(loaded);
                ++it) {
            const llvm::Value* related; Relation relation;
            std::tie(related, relation) = *it;

            if (related == loaded) continue;
            switch (relation) {
                case Relation::EQ:
                    if (relatesByLoadInAll(preds, related, from, &RelationsGraph::isEqual, false))
                        setSomething |= newGraph.setEqual(related, placeholder);
                    else if (relatesByLoadInAll(preds, related, from, &RelationsGraph::isLesserEqual, false))
                        setSomething |= newGraph.setLesserEqual(related, placeholder);
                    else if (relatesByLoadInAll(preds, related, from, &RelationsGraph::isLesserEqual, true))
                        setSomething |= newGraph.setLesserEqual(placeholder, related);
                    break;

                case Relation::LT:
                    if (relatesByLoadInAll(preds, related, from, &RelationsGraph::isLesser, false))
                        setSomething |= newGraph.setLesser(related, placeholder);
                    else if (relatesByLoadInAll(preds, related, from, &RelationsGraph::isLesserEqual, false))
                        setSomething |= newGraph.setLesserEqual(related, placeholder);
                    break;
                
                case Relation::LE:
                    if (relatesByLoadInAll(preds, related, from, &RelationsGraph::isLesserEqual, false))
                        setSomething |= newGraph.setLesserEqual(related, placeholder);
                    break;
                
                case Relation::GT:
                    if (relatesByLoadInAll(preds, related, from, &RelationsGraph::isLesser, true))
                        setSomething |= newGraph.setLesser(placeholder, related);
                    else if (relatesByLoadInAll(preds, related, from, &RelationsGraph::isLesserEqual, true))
                        setSomething |= newGraph.setLesserEqual(placeholder, related);
                    break;

                case Relation::GE:
                    if (relatesByLoadInAll(preds, related, from, &RelationsGraph::isLesserEqual, true))
                        setSomething |= newGraph.setLesserEqual(placeholder, related);
                    break;
            }
        }

        if (setSomething) {
            newGraph.setLoad(from, placeholder);
            changed = true;
        } else if (newPlaceholder)
            newGraph.erasePlaceholderBucket(placeholder);

        return changed;
    }

    void initializeCallRelations() {
        for (const llvm::Function& function : module) {
            if (function.isDeclaration())
                continue;
            
            VRBBlock* vrblockOfEntry = blockMapping.at(&function.getEntryBlock()).get();
            assert(vrblockOfEntry);

            // for each location, where the function is called
            for (const llvm::Value* user : function.users()) {

                // get call from user
                const llvm::CallInst* call = llvm::dyn_cast<llvm::CallInst>(user);
                if (! call) continue;

                RelationsGraph::CallRelation& callRelation = vrblockOfEntry->first()->relations.newCallRelation();
                // set pointer to relations valid at call
                callRelation.callSiteRelations = &locationMapping.at(call)->relations;

                // set formal parameters equal to real
                unsigned argCount = 0;
                for (const llvm::Argument& receivedArg : function.args()) {
                    if (argCount > call->getNumArgOperands()) break;
                    const llvm::Value* sentArg = call->getArgOperand(argCount);

                    callRelation.equalPairs.emplace_back(sentArg, &receivedArg);
                    ++argCount;
                }
            }
        }
    }

    bool analysisPass() {
        bool changed = false;

        for (auto& pair : blockMapping) {
            auto& vrblockPtr = pair.second;

            for (auto& locationPtr : vrblockPtr->locations) {
                bool temp = false;
                std::cerr << "LOCATION " << locationPtr->id << std::endl;
                for (VREdge* predEdge : locationPtr->predecessors) 
                    std::cerr << predEdge->op->toStr() << std::endl;
                locationPtr->relations.ddump();

                if (locationPtr->predecessors.size() > 1) {
                    temp = mergeRelations(locationPtr.get())
                            | mergeLoads(locationPtr.get())
                            | mergeRelationsByLoads(locationPtr.get());
                } else if (locationPtr->predecessors.size() == 1) {
                    VREdge* edge = locationPtr->predecessors[0];
                    temp |= processOperation(edge->source, edge->target, edge->op.get());
                } // else no predecessors => nothing to be passed
                locationPtr->relations.ddump();
                changed |= temp;
            }

        }
        return changed;
    }

    bool mayHaveAlias(const llvm::User* val) const {
        // if value is not pointer, we don't care whether there can be other name for same value
        if (! val->getType()->isPointerTy()) return false;

        for (const llvm::User* user : val->users()) {

            // if value is stored, it can be accessed
            if (llvm::isa<llvm::StoreInst>(user)) {
                if (user->getOperand(0) == val) return true;

            } else if (llvm::isa<llvm::CastInst>(user)) {
                if (mayHaveAlias(user)) return true;

            } else if (auto gep = llvm::dyn_cast<llvm::GetElementPtrInst>(user)) {
                if (gep->getPointerOperand() == val) {
                    if (gep->hasAllZeroIndices()) return true;

                    llvm::Type* valType = val->getType();
                    llvm::Type* gepType = gep->getPointerOperandType();
                    if (gepType->isVectorTy() || valType->isVectorTy())
                        assert(0 && "i dont know what it is and when does it happen");
                    if (gepType->getPrimitiveSizeInBits() < valType->getPrimitiveSizeInBits()) return true;
                }

            } else if (auto inst = llvm::dyn_cast<llvm::Instruction>(user)) {
                if (inst->mayWriteToMemory()) return true;
            }
            // DIFF doesn't check debug information and some intrinsic instructions
        }
        return false;
    }


public:
    RelationsAnalyzer(const llvm::Module& m,
                  std::map<const llvm::Instruction *, VRLocation *>& locs,
                  std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blcs,
                  const StructureAnalyzer& sa)
                  : module(m), locationMapping(locs), blockMapping(blcs), structure(sa) {}

    void analyze(unsigned maxPass) {

        initializeCallRelations();

        bool changed = true;
        unsigned passNum = 0;
        while (changed && ++passNum <= maxPass) {
            std::cerr << "========================================================" << std::endl;
            std::cerr << "                     PASS NUMBER " << passNum             << std::endl;
            std::cerr << "========================================================" << std::endl;
            changed = analysisPass();
        }
    }
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_VALUE_RELATION_RELATIONS_ANALYZER_HPP_

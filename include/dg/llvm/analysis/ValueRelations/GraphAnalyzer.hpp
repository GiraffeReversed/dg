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

#include <algorithm>

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

    // holds vector of instructions, which are processed on any path back to given location
    // is computed only for locations with more than one predecessor
    std::map<VRLocation*, std::vector<const llvm::Instruction*>> inloopValues;

    // holds vector of values, which are defined at given location
    std::map<VRLocation*, std::set<const llvm::Value*>> defined;

    bool processOperation(VRLocation* source, VRLocation* target, VROp* op) {
        if (! target) return false;
        assert(source && target && op);

        RelationsGraph newGraph = source->relations;
        
        if (op->isInstruction()) {
            const llvm::Instruction* inst = static_cast<VRInstruction *>(op)->getInstruction();
    		std::cerr << debug::getValName(inst) << ":" << std::endl;
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

        for (const llvm::Value* invalid : instructionInvalidates(graph, inst))
            graph.unsetAllLoadsByPtr(invalid);
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

        if (! eqivToAlloca(graph.getEqual(memoryPtr))) {
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

            if (! eqivToAlloca(fromsValues.first))
                for (const llvm::Value* from : fromsValues.first) {
                    if (mayHaveAlias(llvm::cast<llvm::User>(from))) {
                        writtenTo.insert(from);
                        break;
                    }
                }
        }

        return writtenTo;
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
        graph.setLoad(store->getPointerOperand()->stripPointerCasts(), store->getValueOperand());
    }

    void loadGen(RelationsGraph& graph, const llvm::LoadInst* load) {
        graph.setLoad(load->getPointerOperand()->stripPointerCasts(), load);
    }

    void gepGen(RelationsGraph& graph, const llvm::GetElementPtrInst* gep) {
        if (gep->hasAllZeroIndices())
            graph.setEqual(gep, gep->getPointerOperand());

        for (auto& fromsValues : graph.getAllLoads()) {
            for (const llvm::Value* from : fromsValues.first) {
                if (auto otherGep = llvm::dyn_cast<llvm::GetElementPtrInst>(from)) {
                    if (allGepParametersAreEqual(graph, gep, otherGep))
                        graph.setEqual(gep, otherGep);
                }
            }
        }
        // TODO something more?
        // indices method gives iterator over indices
    }

    bool allGepParametersAreEqual(const RelationsGraph& graph,
                                  const llvm::GetElementPtrInst* gepOne,
                                  const llvm::GetElementPtrInst* gepTwo) const {
        for (int i = 0; i < fmin(gepOne->getNumOperands(), gepTwo->getNumOperands()); i++) {
            if (! graph.isEqual(gepOne->getOperand(i), gepTwo->getOperand(i))) return false;
        }
        return true;
    }

    void extGen(RelationsGraph& graph, const llvm::CastInst* ext) {
        graph.setEqual(ext, ext->getOperand(0));
    }

    void addGen(RelationsGraph& graph, const llvm::BinaryOperator* add) {
        auto c1 = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(0));
        auto c2 = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(1));
        // TODO check wheter equal to constant

        if (solvesSameType(graph, c1, c2, add)) return;

        const llvm::Value* param = nullptr;
        if (c2) { c1 = c2; param = add->getOperand(0); }
        else param = add->getOperand(1);

        assert(c1 && add && param);
        // add = param + c1
        if (c1->isZero()) return graph.setEqual(add, param);
        
        else if (c1->isNegative()) {
            // c1 < 0  ==>  param + c1 < param
            graph.setLesser(add, param);

            // lesser < param  ==>  lesser <= param + (-1)
            if (c1->isMinusOne()) solvesDiffOne(graph, param, add, true);

        } else {
            // c1 > 0 => param < param + c1
            graph.setLesser(param, add);

            // param < greater => param + 1 <= greater
            if (c1->isOne()) solvesDiffOne(graph, param, add, false);
        }
    }

    void subGen(RelationsGraph& graph, const llvm::BinaryOperator* sub) {
        auto c1 = llvm::dyn_cast<llvm::ConstantInt>(sub->getOperand(0));
        auto c2 = llvm::dyn_cast<llvm::ConstantInt>(sub->getOperand(1));
        // TODO check wheter equal to constant

        if (solvesSameType(graph, c1, c2, sub)) return;

        if (c1) {
            // TODO collect something here?
            return;
        }

        const llvm::Value* param = sub->getOperand(0);
        assert(c2 && sub && param);
        // sub = param - c1
        if (c2->isZero()) return graph.setEqual(sub, param);
        
        else if (c2->isNegative()) {
            // c1 < 0  ==>  param < param - c1
            graph.setLesser(param, sub);

            // param < greater ==> param - (-1) <= greater
            if (c2->isMinusOne()) solvesDiffOne(graph, param, sub, false);

        } else {
            // c1 > 0 => param - c1 < param
            graph.setLesser(sub, param);

            // lesser < param  ==>  lesser <= param - 1
            if (c2->isOne()) solvesDiffOne(graph, param, sub, true);
        }
    }

    void mulGen(RelationsGraph& graph, const llvm::BinaryOperator* mul) {
        auto c1 = llvm::dyn_cast<llvm::ConstantInt>(mul->getOperand(0));
        auto c2 = llvm::dyn_cast<llvm::ConstantInt>(mul->getOperand(1));
        // TODO check wheter equal to constant

        if (solvesSameType(graph, c1, c2, mul)) return;

        const llvm::Value* param = nullptr;
        if (c2) { c1 = c2; param = mul->getOperand(0); }
        else param = mul->getOperand(1);

        assert(c1 && mul && param);
        // mul = param + c1
        if (c1->isZero()) return graph.setEqual(mul, c1);
        else if (c1->isOne()) return graph.setEqual(mul, param);

        // TODO collect something here?
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
            graph.setEqual(op, llvm::ConstantInt::get(c1->getType(), result));
            return true;
        }

        if (! c1 && ! c2) {
            // TODO collect something here?
            return true;
        }
        return false;
    }

    void solvesDiffOne(RelationsGraph& graph,
                       const llvm::Value* param,
                       const llvm::BinaryOperator* op,
                       bool getLesser) {

        std::vector<const llvm::Value*> sample = getLesser ?
                    graph.getSampleLesser(param) : graph.getSampleGreater(param);

        for (const llvm::Value* value : sample)
            if (getLesser) graph.setLesserEqual(value, op);
            else           graph.setLesserEqual(op, value);
    }

    void castGen(RelationsGraph& graph, const llvm::CastInst* cast) {
        if (cast->isLosslessCast() || cast->isNoopCast(module.getDataLayout()))
            graph.setEqual(cast, cast->getOperand(0));
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
                return subGen(graph, llvm::dyn_cast<llvm::BinaryOperator>(inst));
            case llvm::Instruction::Mul:
                return mulGen(graph, llvm::dyn_cast<llvm::BinaryOperator>(inst));
            default:
                if (auto cast = llvm::dyn_cast<llvm::CastInst>(inst)) {
                    return castGen(graph, cast);
                }
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
                newGraph.setNonEqual(op1, op2); break;

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

    bool mergeRelations(VRLocation* location) {
        return mergeRelations(location->getPredLocations(), location);
        // TODO to keep more relations we could use placeholder buckets
        // when we know, what we load load from some address
        // and on each incoming edge we can determine some relation
        // we can say, that the address loads placeholder bucket (bucket, which is empty)
        // and that this bucket is in given relation
        // when we later perform load from that address
        // we will directly infer the relation
        // I can use it in the basic_loop exmaple
    }

    bool mergeRelations(const std::vector<VRLocation*>& preds, VRLocation* location) {
        if (preds.empty()) return false;

        RelationsGraph newGraph = location->relations;
        RelationsGraph& oldGraph = preds[0]->relations;
        std::vector<const llvm::Value*> values = oldGraph.getAllValues();

        for (const llvm::Value* fst : values) {
            for (const llvm::Value* snd : values) {
                if (fst == snd) continue;

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

        if (isLoopJoin(location) && ! isBranchJoin(location)) {
            VRLocation* outloopPred = nullptr;

            for (VREdge* predEdge : location->predecessors) {
                if (predEdge->type == EdgeType::TREE) outloopPred = predEdge->source;
            }
            assert(outloopPred);

            const RelationsGraph& oldGraph = outloopPred->relations;
            std::vector<const llvm::Value*> values = oldGraph.getAllValues();

            for (const llvm::Value* fst : values) {
                for (const llvm::Value* snd : values) {
                    if (fst == snd) continue;

                    if (oldGraph.isEqual(fst, snd)) newGraph.setEqual(fst, snd);
                    if (oldGraph.isLesser(fst, snd)) newGraph.setLesser(fst, snd);
                    if (oldGraph.isLesser(snd, fst)) newGraph.setLesser(snd, fst);
                    if (oldGraph.isLesserEqual(fst, snd)) newGraph.setLesserEqual(fst, snd);
                    if (oldGraph.isLesserEqual(snd, fst)) newGraph.setLesserEqual(snd, fst);
                }
            }


        }

        return andSwapIfChanged(location->relations, newGraph);
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

        RelationsGraph newGraph = location->relations;
        const auto& loadBucketPairs = preds[0]->relations.getAllLoads();

        for (const auto& fromsValues : loadBucketPairs) {
            for (const llvm::Value* from : fromsValues.first) {
                for (const llvm::Value* val : fromsValues.second) {
                    if (loadsInAll(preds, from, val))
                        newGraph.setLoad(from, val);
                }
            }
        }

        if (preds.size() == 2 && preds[0]->inLoop != preds[1]->inLoop) {
            for (const auto& fromsValues : loadBucketPairs) {
                for (const llvm::Value* from : fromsValues.first) {
                    if (loadsSomethingInAll(preds, from)) {
                        std::cerr << "[from]" << debug::getValName(from) << std::endl;

                        VRLocation* outloopPred = preds[0]->inLoop ? preds[1] : preds[0];
                        VRLocation* inloopPred  = preds[0]->inLoop ? preds[0] : preds[1];

                        const llvm::Value* valInloop
                            = inloopPred->relations.getValsByPtr(from)[0];

                        std::vector<const llvm::Value*> allRelated
                            = inloopPred->relations.getAllRelated(valInloop);

                        std::cerr << "[valInloop]" << debug::getValName(valInloop) << std::endl;
                        std::cerr << "[allRelated]" << std::endl;
                        for (auto related : allRelated) {
                            std::cerr << "    " << debug::getValName(related) << std::endl;
                        }
                        std::cerr << std::endl;

                        // get vector of values, that are both related to value loaded from
                        // from at the end of the loop and at the same time are loads
                        // from from in given loop
                        const llvm::Value* firstLoadInLoop = nullptr;
                        for (const llvm::Value* val : inloopValues.at(location)) {
                            std::cerr << "[inloopVal]" << debug::getValName(val) << std::endl;
                            if (std::find(allRelated.begin(), allRelated.end(), val)
                                    != allRelated.end()) {
                                if (auto store = llvm::dyn_cast<llvm::StoreInst>(val)) {
                                    if (store->getPointerOperand() == from) break;
                                }
                                if (auto load = llvm::dyn_cast<llvm::LoadInst>(val)) {
                                    if (load->getPointerOperand() == from) {
                                        firstLoadInLoop = load;
                                        break;
                                    }
                                }
                            }
                        }
                        std::cerr << std::endl;

                        // get all equal vals from load from outloopPred
                        std::vector<const llvm::Value*> valsOutloop
                            = outloopPred->relations.getValsByPtr(from);
                        for (const llvm::Value* val : valsOutloop) {
                            std::cerr << "[valOutloop]" << debug::getValName(val) << std::endl;
                            location->relations.setEqual(valsOutloop[0], val);
                        }
                        std::cerr << std::endl;

                        // set all preserved relations
                        if (firstLoadInLoop) {
                            if (inloopPred->relations.isLesser(firstLoadInLoop, valInloop)) {
                                newGraph.setLesserEqual(valsOutloop[0], firstLoadInLoop);
                                newGraph.setLoad(from, firstLoadInLoop);
                            }
                            if (inloopPred->relations.isLesser(valInloop, firstLoadInLoop)) {
                                newGraph.setLesserEqual(firstLoadInLoop, valsOutloop[0]);
                                newGraph.setLoad(from, firstLoadInLoop);
                            }
                        }


                    }
                }
            }
        }

        std::set<const llvm::Value*> allInvalid;

        // if we are merging loop, not branches or function calls
        // there may be invalidated loads
        if (inloopValues.find(location) != inloopValues.end()) {

            for (VRLocation* pred : preds) {
                RelationsGraph& graph = pred->relations;

                for (const llvm::Instruction* inst : inloopValues.at(location)) {
                    auto invalid = instructionInvalidates(graph, inst);
                    allInvalid.insert(invalid.begin(), invalid.end());
                }
            }
        }

        for (VRLocation* pred : preds) {
            RelationsGraph& graph = pred->relations;
            
            for (const auto& fromsValues : graph.getAllLoads()) {
                if (! anyInvalidated(allInvalid, fromsValues.first)) {
                    for (auto from : fromsValues.first) {
                        for (auto val : fromsValues.second)
                            if (! hasConflictLoad(preds, from, val)
                                    //&& isDefined(location, from)
                                    //&& isDefined(location, val)
                                )
                                newGraph.setLoad(from, val);
                    }
                }
            }
        }

        return andSwapIfChanged(location->relations, newGraph);
    }

    bool isDefined(VRLocation* loc, const llvm::Value* val) const {
        auto definedHere = defined.at(loc);
        return llvm::isa<llvm::Constant>(val) || definedHere.find(val) != definedHere.end();
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

    bool andSwapIfChanged(RelationsGraph& oldGraph, RelationsGraph& newGraph) {
        if (oldGraph == newGraph)
            return false;
            
        swap(oldGraph, newGraph);
        return true;
    }

    bool passCallSiteRelations() {
        bool changed = false;

        for (const llvm::Function& function : module) {
            if (function.isDeclaration())
                continue;
            
            VRBBlock* vrblockOfEntry = blockMapping.at(&function.getEntryBlock()).get();
            assert(vrblockOfEntry);

            // for each location, where the function is called
            std::vector<VRLocation*> callLocs;
            for (const llvm::Value* user : function.users()) {
                const llvm::CallInst* call = llvm::dyn_cast<llvm::CallInst>(user);
                if (! call) continue;

                VRLocation* vrlocOfCall = locationMapping.at(call);
                assert(vrlocOfCall);
                callLocs.push_back(vrlocOfCall);

                RelationsGraph newGraph = vrblockOfEntry->first()->relations;

                unsigned argCount = 0;
                for (const llvm::Argument& receivedArg : function.args()) {
                    if (argCount > call->getNumArgOperands()) break;
                    const llvm::Value* sentArg = call->getArgOperand(argCount);

                    newGraph.setEqual(sentArg, &receivedArg);
                    // DANGER, if function is called multiple times, all it's parameters are set equal
                    ++argCount;
                }
                changed |= andSwapIfChanged(vrblockOfEntry->first()->relations, newGraph);
            }
            changed |= mergeRelations(callLocs, vrblockOfEntry->first());
            changed |= mergeLoads(callLocs, vrblockOfEntry->first());
        }
        return changed;
    }

    bool analysisPass() {
        bool changed = false;
        changed |= passCallSiteRelations();

        for (auto& pair : blockMapping) {
            auto& vrblockPtr = pair.second;

            for (auto& locationPtr : vrblockPtr->locations) {
                if (locationPtr->predecessors.size() > 1) {
                    changed = mergeRelations(locationPtr.get())
                            | mergeLoads(locationPtr.get());
                } else if (locationPtr->predecessors.size() == 1) {
                    VREdge* edge = locationPtr->predecessors[0];
                    changed |= processOperation(edge->source, edge->target, edge->op.get());
                } // else no predecessors => nothing to be passed
                locationPtr->relations.ddump();
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

    void categorizeEdges() {
        for (auto& function : module) {
            if (function.isDeclaration()) continue;

            VRBBlock* vrblockOfEntry = blockMapping.at(&function.getEntryBlock()).get();
            assert(vrblockOfEntry);

            VRLocation* first = vrblockOfEntry->first();

            std::vector<std::pair<VRLocation*, int>> stack;
            std::set<VRLocation*> found;

            stack.emplace_back(first, 0);
            found.emplace(first);

            VRLocation* current;
            unsigned succIndex;
            while (! stack.empty()) {
                std::tie(current, succIndex) = stack.back();
                stack.pop_back();

                // check if there is next successor
                if (current->successors.size() <= succIndex)
                    continue;

                VREdge* succEdge = current->getSuccessors()[succIndex];
                VRLocation* successor = succEdge->target;

                // if there is, plan return
                stack.emplace_back(current, ++succIndex);

                if (! successor) {
                    succEdge->type = EdgeType::TREE;
                    continue;
                }

                // if successor was already searched, we can at least gorize the edge
                if (found.find(successor) != found.end()) {
                    std::vector<VRLocation*> mockStack;
                    for (auto& locIndex : stack)
                        mockStack.push_back(locIndex.first);

                    if (std::find(mockStack.begin(), mockStack.end(), successor) != mockStack.end())
                        succEdge->type = EdgeType::BACK;
                    else
                        succEdge->type = EdgeType::FORWARD;
                    continue;
                }

                // plan visit to successor
                stack.emplace_back(successor, 0);
                found.emplace(successor);
                succEdge->type = EdgeType::TREE;
            }

        }
    }

    void findLoops() {
        for (auto& pair : locationMapping) {
            auto& locationPtr = pair.second;
            std::vector<VREdge*>& predEdges = locationPtr->predecessors;
            if (predEdges.size() > 1) {

                if (isBranchJoin(locationPtr) && ! isLoopJoin(locationPtr)) continue;

                std::vector<VREdge*> treeEdges;
                for (auto it = predEdges.begin(); it != predEdges.end(); ++it) {
                    if ((*it)->type == EdgeType::TREE) {
                        treeEdges.emplace_back(*it);
                        predEdges.erase(it);
                    }
                }
                
                auto forwardReach = genericReach(locationPtr, true);
                auto backwardReach = genericReach(locationPtr, false);

                for (VREdge* predEdge : treeEdges)
                    predEdges.emplace_back(predEdge);

                auto inloopValuesIt = inloopValues.emplace(locationPtr,
                                std::vector<const llvm::Instruction*>()).first;

                for (auto edge : forwardReach) {
                    if (std::find(backwardReach.begin(), backwardReach.end(), edge)
                            != backwardReach.end()) {
                        edge->target->inLoop = true;
                        if (auto op = dynamic_cast<VRInstruction*>(edge->op.get())) {
                            inloopValuesIt->second.emplace_back(op->getInstruction());
                        }
                    }
                }
            }
        }
    }

    std::vector<VREdge*> genericReach(VRLocation* from, bool goForward) {
        std::set<VRLocation*> found = { from };
        std::list<VRLocation*> toVisit = { from };

        std::vector<VREdge*> result;
        while (! toVisit.empty()) {
            VRLocation* current = toVisit.front();
            toVisit.pop_front();

            auto nextEdges = goForward ? current->getSuccessors() : current->getPredecessors();
            for (VREdge* nextEdge : nextEdges) {
                if (! nextEdge->target) continue;

                result.emplace_back(nextEdge);

                auto nextLocation = goForward ? nextEdge->target : nextEdge->source;
                if (found.find(nextLocation) == found.end()) {
                    found.insert(nextLocation);
                    toVisit.push_back(nextLocation);
                }
            }
        }
        return result;
    }

    bool isBranchJoin(const VRLocation* location) const {
        for (VREdge* pred : location->predecessors) {
            if (pred->type == EdgeType::FORWARD) return true;
        }
        return false;
    }

    bool isLoopJoin(const VRLocation* location) const {
        for (VREdge* pred : location->predecessors) {
            if (pred->type == EdgeType::BACK) return true;
        }
        return false;
    }

    void initializeDefined() {
        bool changed;
        do {
            changed = false;
            for (const llvm::Function& function : module) {
                if (function.isDeclaration()) continue;

                auto& block = function.getEntryBlock();
                VRBBlock* vrblock = blockMapping.at(&block).get();

                std::set<VRLocation*> found = { vrblock->first() };
                std::list<VRLocation*> toVisit = { vrblock->first() };

                std::set<const llvm::Value*> temp;
                for (auto& arg : function.args())
                    temp.emplace(&arg);
                defined.emplace(vrblock->first(), temp);

                while (! toVisit.empty()) {
                    VRLocation* current = toVisit.front();
                    toVisit.pop_front();

                    //std::set<VRLocation*> backwardReach;
                    //for (VREdge* edge : genericReach(current, false)) {
                    //    backwardReach.insert(edge->source);
                    //    if (edge->target) backwardReach.insert(edge->target);
                    //}


                    for (VREdge* succEdge : current->getSuccessors()) {

                        VRLocation* succLoc = succEdge->target;
                        if (! succLoc) continue;

                        auto definedSucc = defined.find(succLoc);
                        if (definedSucc == defined.end() || ! current->inLoop)
                            std::tie(definedSucc, changed) = defined.emplace(succLoc,
                                                        std::set<const llvm::Value*>());
                        

                        if(! definedSucc->second.empty())
                                //&& backwardReach.find(succLoc) != backwardReach.end())
                            continue;

                        auto& definedHere = defined.at(current);
                        for (const llvm::Value* defined : definedHere)
                            changed |= definedSucc->second.emplace(defined).second;

                        if (auto op = dynamic_cast<VRInstruction*>(succEdge->op.get()))
                            changed |= definedSucc->second.emplace(op->getInstruction()).second;

                        if (found.find(succLoc) == found.end()) {
                            found.emplace(succLoc);
                            toVisit.push_back(succLoc);
                        }

                        //for (auto def : defined.at(succLoc)) {
                        //    std::cerr << debug::getValName(def) << std::endl;
                        //}
                        //std::cerr << std::endl;
                    }
                }
            }

            // pass definitions from function calls
            for (const llvm::Function& function : module) {
                if (function.isDeclaration()) continue;
                VRBBlock* entryBlock = blockMapping.at(&function.getEntryBlock()).get();
                VRLocation* entryLoc = entryBlock->first();

                auto& definedHere = defined.at(entryLoc);

                for (const llvm::User* call : function.users()) {
                    VRLocation* callLocation = locationMapping.at(
                        static_cast<const llvm::Instruction*>(call));
                    auto definedAtCall = defined.at(callLocation);

                    for (const llvm::Value* defined : definedAtCall)
                        changed |= definedHere.emplace(defined).second;
                }

                //std::cerr << "[entry after passing]" << std::endl;
                //for (auto defined : definedHere) {
                //    std::cerr << debug::getValName(defined) << std::endl;
                //}
                //std::cerr << std::endl;
            }
        } while (changed);
    }


public:
    GraphAnalyzer(const llvm::Module& m,
                  std::map<const llvm::Instruction *, VRLocation *>& locs,
                  std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blcs)
                  : module(m), locationMapping(locs), blockMapping(blcs) {
        categorizeEdges();
        findLoops();
        initializeDefined();
    }

    void analyze(unsigned maxPass) {

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

#endif // _DG_LLVM_VALUE_RELATION_GRAPH_ANALYZER_HPP_

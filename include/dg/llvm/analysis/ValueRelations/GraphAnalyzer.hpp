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

    std::set<const llvm::Value*> fixedMemory;

    bool processOperation(VRLocation* source, VRLocation* target, VROp* op) {
        if (! target) return false;
        assert(source && target && op);

        RelationsGraph newGraph = source->relations;
        
        if (op->isInstruction()) {
            const llvm::Instruction* inst = static_cast<VRInstruction *>(op)->getInstruction();
    		std::cerr << debug::getValName(inst) << ":" << std::endl;
            forgetInvalidated(newGraph, inst);
            processInstruction(newGraph, inst);
            newGraph.ddump();
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

        graph.unsetAllLoadsByPtr(memoryPtr); // unset underlying memory
        graph.unsetAllLoadsByPtr(inst); // unset pointer itself

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
                        newGraph.setLoad(val, from);
                }
            }
        }

        for (const VRLocation* pred : preds) {
            for (const auto& fromsValues : pred->relations.getAllLoads()) {
                for (const llvm::Value* from : fromsValues.first) {
                    if (fixedMemory.find(from) != fixedMemory.end()) {
                        for (const auto& val : fromsValues.second) {
                            newGraph.setLoad(val, from);
                            // DANGER DIFF doesn't check whether value (not from) changes
                        }
                    }
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
            }

        }
        return changed;
    }

    void initializeFixedMemory() {
        for (const auto& function : module) {
            for (const auto& block : function) {
                for (const auto& inst : block) {

                    if (auto alloca = llvm::dyn_cast<llvm::AllocaInst>(&inst)) {
                        bool temp = false;
                        if (! mayHaveAlias(alloca) && writtenMaxOnce(alloca, temp))
                            fixedMemory.insert(alloca);
                    }
                }
            }
        }
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

            } else if (auto inst = llvm::dyn_cast<llvm::Instruction>(user)) {
                if (inst->mayWriteToMemory()) return true;
            }
            // DIFF doesn't check debug information and some intrinsic instructions
        }
        return false;
    }

    bool writtenMaxOnce(const llvm::User* val, bool& writtenAlready) const {
        for (const llvm::User* user : val->users()) {

            if (llvm::isa<llvm::StoreInst>(user)) {
                if (user->getOperand(1)->stripPointerCasts() == val) {
                    if (writtenAlready) return false;
                    writtenAlready = true;
                }
            } else if (llvm::isa<llvm::CastInst>(user)) {
                if (! writtenMaxOnce(user, writtenAlready)) return false;

            } else if (auto inst = llvm::dyn_cast<llvm::Instruction>(user)) {
                if (inst->mayWriteToMemory()) return false;
            }
        }
        return true;
    }



public:
    GraphAnalyzer(const llvm::Module& m,
                  std::map<const llvm::Instruction *, VRLocation *>& locs,
                  std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blcs)
                  : module(m), locationMapping(locs), blockMapping(blcs) {
        initializeFixedMemory();
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

#ifndef _DG_LLVM_VALUE_RELATION_STRUCTURE_ANALYZER_HPP_
#define _DG_LLVM_VALUE_RELATION_STRUCTURE_ANALYZER_HPP_

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

#if (__clang__)
#pragma clang diagnostic pop // ignore -Wunused-parameter
#else
#pragma GCC diagnostic pop
#endif

#include <algorithm>

#include "GraphElements.hpp"

#ifndef NDEBUG
#include "getValName.h"
#endif

namespace {

bool contains(const std::vector<std::string>& haystack, const std::string& needle) {
    for (auto& item : haystack)
        if (item == needle) return true;
    return false;
}

} // namespace

namespace dg {
namespace analysis {
namespace vr {

const llvm::Value* stripCasts(const llvm::Value* inst) {
    while (auto cast = llvm::dyn_cast<llvm::CastInst>(inst))
        inst = cast->getOperand(0);
    return inst;
}

uint64_t getBytes(const llvm::Type* type) {
    unsigned byteWidth = 8;
    assert(type->isSized());

    uint64_t size = type->getPrimitiveSizeInBits();
    assert (size % byteWidth == 0);

    return size / byteWidth;
}

struct AllocatedSizeView{
    const llvm::Value* elementCount = nullptr;
    uint64_t elementSize = 0; // in bytes

    AllocatedSizeView() = default;
    AllocatedSizeView(const llvm::Value* count, uint64_t size)
    : elementCount(count), elementSize(size) {}
};

class AllocatedArea {
    const llvm::Value* ptr;
    // used only if memory was allocated with realloc, as fallback when realloc fails
    const llvm::Value* reallocatedPtr = nullptr;
    AllocatedSizeView originalSizeView;

public:

    AllocatedArea(const llvm::AllocaInst* alloca): ptr(alloca) {
        const llvm::Type* allocatedType = alloca->getAllocatedType();
        
        if (allocatedType->isArrayTy()) {
            const llvm::Type* elemType = allocatedType->getArrayElementType();
            // DANGER just an arbitrary type
            llvm::Type* i32 = llvm::Type::getInt32Ty(elemType->getContext());
            uint64_t intCount = allocatedType->getArrayNumElements();

            originalSizeView = AllocatedSizeView(llvm::ConstantInt::get(i32, intCount), getBytes(elemType));
        } else {
            originalSizeView = AllocatedSizeView(alloca->getOperand(0), getBytes(allocatedType));
        }
    }

    AllocatedArea(const llvm::CallInst* call): ptr(call) {
        auto function = call->getCalledFunction();

        if (function->getName().equals("malloc")) {
            originalSizeView = AllocatedSizeView(call->getOperand(0), 1);
        }

        if (function->getName().equals("calloc")) {
            auto size = llvm::cast<llvm::ConstantInt>(call->getOperand(1));
            originalSizeView = AllocatedSizeView(call->getOperand(0), size->getZExtValue());
        }

        if (function->getName().equals("realloc")) {
            originalSizeView = AllocatedSizeView(call->getOperand(0), 1);
            reallocatedPtr = call->getOperand(0);
        }
    }

    const llvm::Value* getPtr() const { return ptr; }
    const llvm::Value* getReallocatedPtr() const { return reallocatedPtr; }

    std::vector<AllocatedSizeView> getAllocatedSizeViews() const {
        std::vector<AllocatedSizeView> result;
        result.emplace_back(originalSizeView);

        AllocatedSizeView currentView = originalSizeView;

        while (auto op = llvm::dyn_cast<llvm::BinaryOperator>(stripCasts(currentView.elementCount))) {
            uint64_t size = currentView.elementSize;

            if (op->getOpcode() != llvm::Instruction::Add
             && op->getOpcode() != llvm::Instruction::Mul)
                // TODO could also handle subtraction of negative constant
                break;

            auto c1 = llvm::dyn_cast<llvm::ConstantInt>(op->getOperand(0));
            auto c2 = llvm::dyn_cast<llvm::ConstantInt>(op->getOperand(1));

            if (c1 && c2) {
                llvm::APInt newCount;
                llvm::APInt newSize;
                switch (op->getOpcode()) {

                    case llvm::Instruction::Add:
                        newCount = c1->getValue() + c2->getValue();
                        result.emplace_back(llvm::ConstantInt::get(c1->getType(), newCount), size);
                        break;

                    case llvm::Instruction::Mul:
                        newSize = c1->getValue() * size;
                        result.emplace_back(c2, newSize.getZExtValue());
                        newSize = c2->getValue() * size;
                        result.emplace_back(c1, newSize.getZExtValue());

                        newCount = c1->getValue() * c2->getValue();
                        result.emplace_back(llvm::ConstantInt::get(c1->getType(), newCount), size);
                        break;

                    default:
                        assert (0 && "unreachable");
                }
                // if we found two-constant operation, non of them can be binary
                // operator to further unwrap
                break;
            }

            // TODO use more info here
            if (! c1 && ! c2) break;

            // else one of c1, c2 is constant and the other is variable
            const llvm::Value* param = nullptr;
            if (c2) { c1 = c2; param = op->getOperand(0); }
            else param = op->getOperand(1);

            // now c1 is constant and param is variable
            assert (c1 && param);

            switch(op->getOpcode()) {

                case llvm::Instruction::Add:
                    result.emplace_back(param, size);
                    break;

                case llvm::Instruction::Mul:
                    result.emplace_back(param, size * c1->getZExtValue());
                    break;

                default:
                    assert (0 && "unreachable");
            }
            currentView = result.back();
            // reachable only in this last c1 && param case
        }
        return result;
    }

#ifndef NDEBUG
    void ddump() const {
        std::cerr << "Allocated area:" << std::endl;
        std::cerr << "    ptr " << debug::getValName(ptr) << std::endl;
        std::cerr << "    count " << debug::getValName(originalSizeView.elementCount) << std::endl;
        std::cerr << "    size " << originalSizeView.elementSize << std::endl;
        std::cerr << std::endl;
    }
#endif
};


class StructureAnalyzer {

    using LocationMap = std::map<const llvm::Instruction*, VRLocation*>;
    using BlockMap = std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>;

    // holds vector of instructions, which are processed on any path back to given location
    // is computed only for locations with more than one predecessor
    std::map<VRLocation*, std::vector<const llvm::Instruction*>> inloopValues;

    // holds vector of values, which are defined at given location
    std::map<VRLocation*, std::set<const llvm::Value*>> defined;

    const std::vector<unsigned> collected = { llvm::Instruction::Add,
                                              llvm::Instruction::Sub,
                                              llvm::Instruction::Mul };
    std::map<unsigned, std::set<const llvm::Instruction*>> instructionSets;

    std::vector<AllocatedArea>& allocatedAreas;
    const std::vector<std::string> handledAllocationFunctions = { "malloc",
                                                                  "realloc",
                                                                  "calloc" };

    void categorizeEdges(const llvm::Module& module,
                         const BlockMap& blockMapping) {
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

                // if successor was already searched, we can at least categorize the edge
                if (found.find(successor) != found.end()) {
                    std::vector<VRLocation*> mockStack;
                    for (auto& locIndex : stack)
                        mockStack.push_back(locIndex.first);

                    if (std::find(mockStack.begin(), mockStack.end(), successor) != mockStack.end()) // TODO find_if
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

    void findLoops(const LocationMap& locationMapping) {
        for (auto& pair : locationMapping) {
            auto& location = pair.second;
            std::vector<VREdge*>& predEdges = location->predecessors;
            if (location->isJustLoopJoin()) {

                // remove the incoming tree edge, so that backwardReach would
                // really go only backwards
                VREdge* treePred = nullptr;
                for (auto it = predEdges.begin(); it != predEdges.end(); ++it) {
                    if ((*it)->type == EdgeType::TREE) {
                        treePred = *it;
                        predEdges.erase(it);
                        break;
                    }
                }
                assert(treePred); // every join has to have exactly one tree predecessor
                
                auto forwardReach = genericReach(location, true);
                auto backwardReach = genericReach(location, false);

                // put the tree edge back in
                predEdges.emplace_back(treePred);

                auto inloopValuesIt = inloopValues.emplace(location,
                                std::vector<const llvm::Instruction*>()).first;

                for (auto edge : forwardReach) {
                    if (std::find(backwardReach.begin(), backwardReach.end(), edge)
                            != backwardReach.end()) {
                        edge->target->inLoop = true;
                        if (edge->op->isInstruction()) {
                            auto* op = static_cast<VRInstruction*>(edge->op.get());
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

    void initializeDefined(const llvm::Module& module, const BlockMap& blockMapping) {

        for (const llvm::Function& function : module) {
            if (function.isDeclaration()) continue;

            auto& block = function.getEntryBlock();
            VRBBlock* vrblock = blockMapping.at(&block).get();

            std::list<VRLocation*> toVisit = { vrblock->first() };

            // prepare sets of defined values for each location
            for (auto& blockVrblockPair : blockMapping) {
                for (auto& locationUPtr : *blockVrblockPair.second)
                    defined.emplace(locationUPtr.get(), std::set<const llvm::Value*>());
            }

            while (! toVisit.empty()) {
                VRLocation* current = toVisit.front();
                toVisit.pop_front();

                for (VREdge* succEdge : current->getSuccessors()) {

                    // if edge leads to nowhere, just continue
                    VRLocation* succLoc = succEdge->target;
                    if (! succLoc) continue;

                    // if edge leads back, we would add values we exactly dont want
                    if (succEdge->type == EdgeType::BACK) continue;

                    auto& definedSucc = defined.at(succLoc);
                    auto& definedHere = defined.at(current);

                    // copy from this location to its successor
                    definedSucc.insert(definedHere.begin(), definedHere.end());

                    // add instruction, if edge carries any
                    if (succEdge->op->isInstruction()) {
                        auto* op = static_cast<VRInstruction*>(succEdge->op.get());
                        definedSucc.emplace(op->getInstruction());
                    }

                    toVisit.push_back(succLoc);
                }
            }
        }
    }

    void collectInstructionSet(const llvm::Module& module) {
        for (unsigned opcode : collected)
            instructionSets.emplace(opcode, std::set<const llvm::Instruction*>());

        for (const llvm::Function& function : module) {
            for (const llvm::BasicBlock& block : function) {
                for (const llvm::Instruction& inst : block) {

                    // if we collect instructions with this opcode
                    // add it to its set
                    auto found = instructionSets.find(inst.getOpcode());
                    if (found != instructionSets.end())
                        found->second.emplace(&inst);
                }
            }
        }
    }

    bool isValidAllocationCall(const llvm::Value* val) const {
        if (! llvm::isa<llvm::CallInst>(val)) return false;

        const llvm::CallInst* call = llvm::cast<llvm::CallInst>(val);
        auto function = call->getCalledFunction();

        return function && contains(handledAllocationFunctions, function->getName())
            && (! function->getName().equals("calloc") || llvm::isa<llvm::ConstantInt>(call->getOperand(1)));

    }

    void collectAllocatedAreas(const llvm::Module& module) {
        // compute allocated areas throughout the code
        for (const llvm::Function& function : module) {
            for (const llvm::BasicBlock& block : function) {
                for (const llvm::Instruction& inst : block) {

                    if (auto alloca = llvm::dyn_cast<llvm::AllocaInst>(&inst)) {
                        allocatedAreas.emplace_back(alloca);
                    }

                    else if (auto call = llvm::dyn_cast<llvm::CallInst>(&inst)) {
                        if (isValidAllocationCall(call)) {
                            allocatedAreas.emplace_back(call);
                        }
                    }
                }
            }
        }
    }

    void setValidAreasFromNoPredecessors(std::vector<bool>& validAreas) const {
        validAreas = std::vector<bool>(allocatedAreas.size(), false);
    }

    void setValidAreasByInstruction(VRLocation* location, std::vector<bool>& validAreas, VRInstruction* vrinst) const {
        const llvm::Instruction* inst = vrinst->getInstruction();
        unsigned index = 0;
        const AllocatedArea* area = nullptr;
        
        // every memory allocated on stack is considered allocated successfully
        if (llvm::isa<llvm::AllocaInst>(inst)) {
            std::tie(index, area) = getAllocatedAreaFor(allocatedAreas, inst); assert(area);
            validAreas[index] = true;
        }

        // if came across lifetime_end call, then mark memory whose scope ended invalid
        if (auto intrinsic = llvm::dyn_cast<llvm::IntrinsicInst>(inst)) {
            if (intrinsic->getIntrinsicID() == llvm::Intrinsic::lifetime_end) {

                for (auto* equal : location->relations.getEqual(intrinsic->getOperand(1))) {
                    if (llvm::isa<llvm::AllocaInst>(equal)) {
                        std::tie(index, area) = getAllocatedAreaFor(allocatedAreas, equal); assert(area);
                        validAreas[index] = false;
                    }
                }
            }
        }

        if (auto call = llvm::dyn_cast<llvm::CallInst>(inst)) {
            auto function = call->getCalledFunction();

            if (! function) return;

            if (function->getName().equals("realloc")) {
                // if realloc of memory occured, the reallocated memory cannot be considered valid
                // until the realloc is proven unsuccessful
                for (auto* equal : location->relations.getEqual(call->getOperand(0))) {
                    std::tie(index, area) = getAllocatedAreaFor(allocatedAreas, equal);
                    if (area) validAreas[index] = false;
                }
            }

            if (function->getName().equals("free")) {
                // if free occures, the freed memory cannot be considered valid anymore
                for (auto* equal : location->relations.getEqual(call->getOperand(0))) {
                    std::tie(index, area) = getAllocatedAreaFor(allocatedAreas, equal);
                    if (area) validAreas[index] = false;
                }
            }
        }
    }

    void setValidArea(std::vector<bool>& validAreas, const AllocatedArea* area, unsigned index, bool validateThis) const {
        unsigned preReallocIndex = 0;
        const AllocatedArea* preReallocArea = nullptr;
        if (area->getReallocatedPtr())
            std::tie(preReallocIndex, preReallocArea) = getAllocatedAreaFor(allocatedAreas, area->getReallocatedPtr());

        if (validateThis) {
            validAreas[index] = true;
            if (preReallocArea) assert (! validAreas[preReallocIndex]);
        
        // else the original area, if any, should be validated
        } else if (preReallocArea) {
            validAreas[preReallocIndex] = true;
            assert (! validAreas[index]);
        }
    }

    // if heap allocation call was just checked as successful, mark memory valid
    void setValidAreasByAssumeBool(VRLocation* location, std::vector<bool>& validAreas, VRAssumeBool* assume) const {
        auto icmp = llvm::dyn_cast<llvm::ICmpInst>(assume->getValue());
        if (! icmp) return;

        auto c1 = llvm::dyn_cast<llvm::ConstantInt>(icmp->getOperand(0));
        auto c2 = llvm::dyn_cast<llvm::ConstantInt>(icmp->getOperand(1));

        // pointer must be compared to zero // TODO? or greater
        if ((c1 && c2) || (! c1 && ! c2) || (! c1 && ! c2->isZero()) || (! c2 && ! c1->isZero())) return;

        // get the compared parameter
        const llvm::Value* param = c1 ? icmp->getOperand(1) : icmp->getOperand(0);

        unsigned index = 0;
        const AllocatedArea* area = nullptr;

        for (auto equal : location->relations.getEqual(param)) {
            std::tie(index, area) = getAllocatedAreaFor(allocatedAreas, equal);
            // if compared pointer or equal belong to allocated area, this area
            // can be marked valid
            if (area) break;
        }
        // the compared value is not a pointer to an allocated area
        if (! area) return;

        llvm::ICmpInst::Predicate pred = assume->getAssumption() ?
            icmp->getSignedPredicate() : icmp->getInversePredicate();

        // check that predicate implies wanted relation
        switch (pred) {
            case llvm::ICmpInst::Predicate::ICMP_EQ:
                // if reallocated pointer is equal to zero, then original memory is still valid
                setValidArea(validAreas, area, index, false);
                return;

            case llvm::ICmpInst::Predicate::ICMP_NE:
                // pointer is not equal to zero, therefore it a valid result of heap allocation
                setValidArea(validAreas, area, index, true);
                return;

            case llvm::ICmpInst::Predicate::ICMP_ULE:
            case llvm::ICmpInst::Predicate::ICMP_SLE:
            case llvm::ICmpInst::Predicate::ICMP_ULT:
            case llvm::ICmpInst::Predicate::ICMP_SLT:
                // if zero stands right to </<=, this proves invalidity
                if (c2) setValidArea(validAreas, area, index, false);
                else setValidArea(validAreas, area, index, true);
                return;

            case llvm::ICmpInst::Predicate::ICMP_UGE:
            case llvm::ICmpInst::Predicate::ICMP_SGE:
            case llvm::ICmpInst::Predicate::ICMP_UGT:
            case llvm::ICmpInst::Predicate::ICMP_SGT:
                // if zero stands left to >/>=, this proves invalidity
                if (c1) setValidArea(validAreas, area, index, false);
                else setValidArea(validAreas, area, index, true);
                return;

            default:
                assert(0 && "unreachable, would have failed in processICMP");
        }
    }

    void setValidAreasFromSinglePredecessor(VRLocation* location, std::vector<bool>& validAreas) {
        // copy predecessors valid areas
        VREdge* edge = location->predecessors[0];
        validAreas = edge->source->relations.getValidAreas();

        // and alter them according to info from edge
        if (edge->op->isInstruction())
            setValidAreasByInstruction(location, validAreas, static_cast<VRInstruction *>(edge->op.get()));

        if (edge->op->isAssumeBool())
            setValidAreasByAssumeBool(location, validAreas, static_cast<VRAssumeBool*>(edge->op.get()));
    }

    bool trueInAll(const std::vector<VREdge*>& predecessors, unsigned index) {
        for (VREdge* predecessor : predecessors) {
            if (predecessor->source->relations.getValidAreas().empty() && predecessor->type != EdgeType::BACK)
                return false;
            if (predecessor->source->relations.getValidAreas().empty() && predecessor->type == EdgeType::BACK)
                continue;

            if (! predecessor->source->relations.getValidAreas()[index])
                return false;
        }
        return true;
    }

    void setValidAreasFromMultiplePredecessors(VRLocation* location, std::vector<bool>& validAreas) {
        // intersect valid areas from predecessors
        for (unsigned i = 0; i < allocatedAreas.size(); ++i) {
            validAreas.push_back( trueInAll(location->predecessors, i) );
        }
    }

    void propagateAllocatedAreas(const llvm::Module& module, const BlockMap& blockMapping) {
        for (const llvm::Function& function : module) {
            for (const llvm::BasicBlock& block : function) {
                for (auto& location : blockMapping.at(&block)->locations) {

                    std::vector<bool>& validAreas = location->relations.getValidAreas();

                    switch (location->predecessors.size()) {
                        case 0:  setValidAreasFromNoPredecessors(validAreas); break;
                        case 1:  setValidAreasFromSinglePredecessor(location.get(), validAreas); break;
                        default: setValidAreasFromMultiplePredecessors(location.get(), validAreas); break;
                    }
                }
            }
        }
    }

public:
    StructureAnalyzer(std::vector<AllocatedArea>& areas): allocatedAreas(areas) {}

    void analyzeBeforeRelationsAnalysis(const llvm::Module& m, const LocationMap& locs, const BlockMap& blcs) {
        categorizeEdges(m, blcs);
        findLoops(locs);
        collectInstructionSet(m);
        //initializeDefined(m, blcs);
    }

    void analyzeAfterRelationsAnalysis(const llvm::Module& m, const BlockMap& blcs) {
        collectAllocatedAreas(m);
        propagateAllocatedAreas(m, blcs);
        // propagate twice because of loops, it the first pass it is not known
        // whether the loop invalidates any areas
        propagateAllocatedAreas(m, blcs);
    }

    bool isDefined(VRLocation* loc, const llvm::Value* val) const {
        if (llvm::isa<llvm::Constant>(val)) return true;

        auto definedHere = defined.at(loc);
        return definedHere.find(val) != definedHere.end();
    }

    // assumes that location is valid loop start (join of tree and back edges)
    const std::vector<const llvm::Instruction*>& getInloopValues(VRLocation* const location) const {
        return inloopValues.at(location);
    }

    const std::set<const llvm::Instruction*>& getInstructionSetFor(unsigned opcode) const {
        return instructionSets.at(opcode);
    }

    static std::pair<unsigned, const AllocatedArea*> getAllocatedAreaFor(
            const std::vector<AllocatedArea>& areas,
            const llvm::Value* ptr) {
        unsigned i = 0;
        for (auto& area : areas) {
            if (area.getPtr() == ptr) return { i, &area };
            ++i;
        }
        return { 0, nullptr };
    }
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_VALUE_RELATION_STRUCTURE_ANALYZER_HPP_

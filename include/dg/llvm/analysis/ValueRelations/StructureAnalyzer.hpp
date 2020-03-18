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

namespace dg {
namespace analysis {
namespace vr {


class StructureAnalyzer {

    // holds vector of instructions, which are processed on any path back to given location
    // is computed only for locations with more than one predecessor
    std::map<VRLocation*, std::vector<const llvm::Instruction*>> inloopValues;

    // holds vector of values, which are defined at given location
    std::map<VRLocation*, std::set<const llvm::Value*>> defined;

    const std::vector<unsigned> collected = { llvm::Instruction::Add,
                                              llvm::Instruction::Sub,
                                              llvm::Instruction::Mul };

    std::map<unsigned, std::set<const llvm::Instruction*>> instructionSets;

    void categorizeEdges(const llvm::Module& module, const std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blockMapping) {
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

    void findLoops(const std::map<const llvm::Instruction *, VRLocation *>& locationMapping) {
        for (auto& pair : locationMapping) {
            auto& location = pair.second;
            std::vector<VREdge*>& predEdges = location->predecessors;
            if (location->isJustLoopJoin()) {

                // remove all tree edges, so that backwarReach would
                // really go only backwards
                std::vector<VREdge*> treeEdges;
                for (auto it = predEdges.begin(); it != predEdges.end(); ++it) {
                    if ((*it)->type == EdgeType::TREE) {
                        treeEdges.emplace_back(*it);
                        predEdges.erase(it);
                    }
                }
                
                auto forwardReach = genericReach(location, true);
                auto backwardReach = genericReach(location, false);

                // put tree edges back in
                for (VREdge* predEdge : treeEdges)
                    predEdges.emplace_back(predEdge);

                auto inloopValuesIt = inloopValues.emplace(location,
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

    void initializeDefined(const llvm::Module& module, const std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blockMapping) {

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
                    if (auto op = dynamic_cast<VRInstruction*>(succEdge->op.get()))
                        definedSucc.emplace(op->getInstruction());

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


public:
    StructureAnalyzer(const llvm::Module& m,
                  std::map<const llvm::Instruction *, VRLocation *>& locs,
                  std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& blcs) {
        categorizeEdges(m, blcs);
        findLoops(locs);
        collectInstructionSet(m);
        //initializeDefined(m, blcs);
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
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_VALUE_RELATION_STRUCTURE_ANALYZER_HPP_

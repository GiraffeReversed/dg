#ifndef _DG_LLVM_ANALYSIS_GRAPH_HPP_
#define _DG_LLVM_ANALYSIS_GRAPH_HPP_

#include <llvm/IR/Module.h>

#include "GraphBuilder.hpp"
#include "RelationsAnalyzer.hpp"

#ifndef NDEBUG
#include "getValName.h"
#endif

namespace dg {
namespace analysis {
namespace vr {

class AnalysisGraph {

    const llvm::Module& module;

    // VRLocation corresponding to the state of the program BEFORE executing the instruction
    std::map<const llvm::Instruction *, VRLocation *> locationMapping;
    std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>> blockMapping;

    StructureAnalyzer structure;

    std::pair<const llvm::Value*, const llvm::Type*> getOnlyNonzeroIndex(
            const llvm::GetElementPtrInst* gep) const {
        const llvm::Value* firstIndex = nullptr;
        const llvm::Type* readType = gep->getSourceElementType();

        for (const llvm::Value* index : gep->indices()) {
            // consider only cases when nonzero index is the last
            if (firstIndex) return { nullptr, nullptr };

            if (auto constIndex = llvm::dyn_cast<llvm::ConstantInt>(index)) {
                if (constIndex->isZero()) {

                    if (! readType->isArrayTy()) return { nullptr, nullptr };
                    
                    readType = readType->getArrayElementType();
                    continue;
                };
            }

            firstIndex = index;
        }
        return { firstIndex, readType };
    }

    std::string isValidForGraph(
            const ValueRelations& relations,
            const std::vector<bool> validMemory,
            const llvm::GetElementPtrInst* gep,
            uint64_t readSize) const {
        //std::cerr << "==== PROOF BEGINS =====" << std::endl;
        //std::cerr << dg::debug::getValName(gep) << std::endl << std::endl;

        //relations.ddump(); // mark parameter const when deleting

        const AllocatedArea* area = nullptr;
        unsigned index = 0;

        for (const llvm::Value* equal : relations.getEqual(gep->getPointerOperand())) {
            std::tie(index, area) = structure.getAllocatedAreaFor(equal);
            if (area) break;
        }
        if (! area) return "maybe"; // memory was not allocated by ordinary means (or at all)
        if (! validMemory[index]) return "maybe"; // memory is not valid at given location

        const std::vector<AllocatedSizeView>& views = area->getAllocatedSizeViews();
        if (views.empty()) return "unknown"; // the size of allocated memory cannot be determined

        if (gep->hasAllZeroIndices()) return readSize <= views[0].elementSize ? "true" : "maybe";
        // maybe, because can read i64 from an array of two i32

        const llvm::Value* gepIndex;
        const llvm::Type* gepType;
        std::tie(gepIndex, gepType) = getOnlyNonzeroIndex(gep);
        // if gep has more indices than one, or there are zeros after
        if (! gepIndex) return "unknown";

        uint64_t gepElem = getBytes(gepType);

        //std::cerr << "[readSize] " << readSize << std::endl;
        //std::cerr << "[allocElem] " << allocElem << std::endl;
        //std::cerr << "[gepElem] " << gepElem << std::endl;
        //std::cerr << "[allocCount] " << dg::debug::getValName(allocCount) << std::endl;
        //std::cerr << "[gepIndex] " << dg::debug::getValName(gepIndex) << std::endl;

        // DANGER just an arbitrary type
        llvm::Type* i32 = llvm::Type::getInt32Ty(views[0].elementCount->getContext());
        const llvm::Constant* zero = llvm::ConstantInt::getSigned(i32, 0);

        // check if index doesnt point before memory
        if (relations.isLesser(gepIndex, zero))
            // we know that pointed memory is alloca because allocCount is not nullptr
            return "false";
        if (! relations.isLesserEqual(zero, gepIndex)) return "maybe";

        // check if index doesnt point after memory
        for (const AllocatedSizeView& view : views) {

            //std::cerr << "inloop" << std::endl;
            //std::cerr << "[elementCount] " << dg::debug::getValName(view.elementCount) << std::endl;
            //std::cerr << "[elementSize] " << view.elementSize << std::endl;
            //std::cerr << "[gepIndex] " << dg::debug::getValName(gepIndex) << std::endl;
            if (relations.isLesser(gepIndex, view.elementCount)) {
                if (gepElem <= view.elementSize) return readSize <= view.elementSize ? "true" : "maybe";
            }
            if (relations.isLesserEqual(view.elementCount, gepIndex) && gepElem >= view.elementSize)
                return "false";
        }

        return "maybe";
    }  

public:
    std::string isValidPointer(const llvm::Value* ptr, const llvm::Value* size) const {
        // ptr is not a pointer
        if (!ptr->getType()->isPointerTy()) return "false";

        uint64_t readSize = 0;
        if (auto* constant = llvm::dyn_cast<llvm::ConstantInt>(size)) {
            readSize = constant->getLimitedValue();

            // size cannot be expressed as uint64_t
            if (readSize == ~((uint64_t) 0)) return "maybe";
        } else {
            // size is not constant int
            return "maybe";
        }

        assert (readSize > 0 && readSize < ~((uint64_t) 0));

        auto gep = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr);
        if (! gep) return "unknown";

        const ValueRelations& relations = locationMapping.at(gep)->relations;
        if (relations.getCallRelations().empty())
            return isValidForGraph(relations, relations.getValidAreas(), gep, readSize);

        // else we have to check that access is valid in every case
        for (const ValueRelations::CallRelation& callRelation : relations.getCallRelations()) {
            ValueRelations merged = relations;

            bool hasConflict = false;
            for (auto& equalPair : callRelation.equalPairs) {
                if (merged.hasConflictingRelation(equalPair.first, equalPair.second, Relation::EQ)) {
                    hasConflict = true;
                    break; // this vrlocation is unreachable with given parameters
                }
                merged.setEqual(equalPair.first, equalPair.second);
            }

            const ValueRelations& callSiteRelations = *callRelation.callSiteRelations;

            // this vrlocation is unreachable with relations from given call relation
            hasConflict = hasConflict || ! merged.merge(callSiteRelations);
            merged.getCallRelations().clear();

            // since location is unreachable, it does not make sence to qualify the memory access
            if (hasConflict) continue;

            std::vector<bool> validMemory(structure.getNumberOfAllocatedAreas());

            if (relations.getValidAreas().empty() || callSiteRelations.getValidAreas().empty()) return "unknown";
            for (unsigned i = 0; i < structure.getNumberOfAllocatedAreas(); ++i)
                validMemory[i] = relations.getValidAreas()[i] || callSiteRelations.getValidAreas()[i];

            std::string result = isValidForGraph(merged, validMemory, gep, readSize);
            if (result != "true") return result;
        }
        return "true";
    }

    AnalysisGraph(const llvm::Module& M, unsigned maxPass) : module(M) {
        GraphBuilder gb(module, locationMapping, blockMapping);
        gb.build();

        structure.analyzeBeforeRelationsAnalysis(module, locationMapping, blockMapping);

        RelationsAnalyzer ra(module, locationMapping, blockMapping, structure);
        ra.analyze(maxPass);

        structure.analyzeAfterRelationsAnalysis(module, blockMapping);
    }

    const std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& getBlockMapping() const {
        return blockMapping;
    }
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_ANALYSIS_GRAPH_HPP_

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

    uint64_t getBytes(const llvm::Type* type) const {
        unsigned byteWidth = 8;
        assert(type->isSized());

        uint64_t size = type->getPrimitiveSizeInBits();
        assert (size % byteWidth == 0);

        return size / byteWidth;
    }

    std::pair<const llvm::Value*, uint64_t> getAllocatedCountAndSize(
            const ValueRelations& relations, 
            const llvm::GetElementPtrInst* gep) const {
        for (const llvm::Value* equal : relations.getEqual(gep->getPointerOperand())) {

            if (auto alloca = llvm::dyn_cast<llvm::AllocaInst>(equal)) {
                const llvm::Type* allocatedType = alloca->getAllocatedType();
                const llvm::Value* count = nullptr;
                uint64_t size = 0;
                
                if (allocatedType->isArrayTy()) {
                    const llvm::Type* elemType = allocatedType->getArrayElementType();
                    // DANGER just an arbitrary type
                    llvm::Type* i32 = llvm::Type::getInt32Ty(elemType->getContext());
                    uint64_t intCount = allocatedType->getArrayNumElements();
                    count = llvm::ConstantInt::get(i32, intCount);
                    size = getBytes(elemType);
                } else {
                    count = alloca->getOperand(0);
                    size = getBytes(allocatedType);
                }
                return { count, size };
            } else if (auto call = llvm::dyn_cast<llvm::CallInst>(equal)) {
                auto function = call->getCalledFunction();

                if (! function) return { nullptr, 0 };

                if (function->getName().equals("malloc"))
                    return { call->getOperand(0), 1};

                if (function->getName().equals("calloc")) {
                    if (auto size = llvm::dyn_cast<llvm::ConstantInt>(call->getOperand(1)))
                        return { call->getOperand(0), size->getZExtValue() };
                }

                if (function->getName().equals("realloc"))
                    return { call->getOperand(1), 1 };
            }
        }
        return { nullptr, 0 };
    }  

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

    std::pair<const llvm::Value*, uint64_t> stripArithmeticOp(const llvm::Value* allocCount, uint64_t allocElem) const {
        while (auto cast = llvm::dyn_cast<llvm::CastInst>(allocCount))
            allocCount = cast->getOperand(0);

        if (! llvm::isa<llvm::BinaryOperator>(allocCount)) return { nullptr, 0 };

        auto op = llvm::cast<llvm::BinaryOperator>(allocCount);
        if (op->getOpcode() != llvm::Instruction::Add
                && op->getOpcode() != llvm::Instruction::Mul)
            // TODO could also handle subtraction of negative constant
            return { nullptr, 0 };

        auto c1 = llvm::dyn_cast<llvm::ConstantInt>(op->getOperand(0));
        auto c2 = llvm::dyn_cast<llvm::ConstantInt>(op->getOperand(1));

        if (c1 && c2) {
            llvm::APInt result;
            switch (op->getOpcode()) {
                case llvm::Instruction::Add:
                    result = c1->getValue() + c2->getValue(); break;
                case llvm::Instruction::Mul:
                    result = c1->getValue() * c2->getValue(); break;
                default:
                    assert (0 && "stripArithmeticOp: unreachable");
            }
            return { llvm::ConstantInt::get(c1->getType(), result), allocElem };
        }

        // TODO use more info here
        if (! c1 && ! c2) return { nullptr, 0 };

        const llvm::Value* param = nullptr;
        if (c2) { c1 = c2; param = op->getOperand(0); }
        else param = op->getOperand(1);

        assert (c1 && param);

        switch(op->getOpcode()) {
            case llvm::Instruction::Add:
                return { param, allocElem };
            case llvm::Instruction::Mul:
                return { param, allocElem * c1->getZExtValue() };
            default:
                return { nullptr, 0 };
        }
    }

    std::string isValidForGraph(
            ValueRelations& relations,
            const llvm::GetElementPtrInst* gep,
            uint64_t readSize) const {
        std::cerr << "==== PROOF BEGINS =====" << std::endl;
        std::cerr << dg::debug::getValName(gep) << std::endl << std::endl;

        //relations.ddump(); // mark parameter const when deleting

        const llvm::Value* allocCount;
        uint64_t allocElem;
        std::tie(allocCount, allocElem) = getAllocatedCountAndSize(relations, gep);
        // if we do not know the size of allocated memory
        if (! allocCount) return "unknown";

        if (gep->hasAllZeroIndices()) return readSize <= allocElem ? "true" : "maybe";
        // maybe, because can read i64 from an array of two i32

        const llvm::Value* gepIndex;
        const llvm::Type* gepType;
        std::tie(gepIndex, gepType) = getOnlyNonzeroIndex(gep);
        // if gep has more indices than one, or there are zeros after
        if (! gepIndex) return "unknown";

        uint64_t gepElem = getBytes(gepType);

        std::cerr << "[readSize] " << readSize << std::endl;
        std::cerr << "[allocElem] " << allocElem << std::endl;
        std::cerr << "[gepElem] " << gepElem << std::endl;
        std::cerr << "[allocCount] " << dg::debug::getValName(allocCount) << std::endl;
        std::cerr << "[gepIndex] " << dg::debug::getValName(gepIndex) << std::endl;

        // DANGER just an arbitrary type
        llvm::Type* i32 = llvm::Type::getInt32Ty(allocCount->getContext());
        const llvm::Constant* zero = llvm::ConstantInt::getSigned(i32, 0);

        // check if index doesnt point before memory
        if (relations.isLesser(gepIndex, zero))
            // we know that pointed memory is alloca because allocCount is not nullptr
            return "false";
        if (! relations.isLesserEqual(zero, gepIndex)) return "maybe";

        // check if index doesnt point after memory
        do {
            std::cerr << "inloop" << std::endl;
            std::cerr << "[allocCount] " << dg::debug::getValName(allocCount) << std::endl;
            std::cerr << "[allocElem] " << allocElem << std::endl;
            std::cerr << "[gepIndex] " << dg::debug::getValName(gepIndex) << std::endl;
            if (relations.isLesser(gepIndex, allocCount)) {
                // TODO handle some cases where size and max index are both constants,
                // but type accessed is different from type allocated
                if (gepElem <= allocElem) return readSize <= allocElem ? "true" : "maybe";
            }
            if (relations.isLesserEqual(allocCount, gepIndex) && gepElem >= allocElem)
                return "false";

            std::tie(allocCount, allocElem) = stripArithmeticOp(allocCount, allocElem);
        } while (allocCount);

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

        auto& relations = locationMapping.at(gep)->relations;
        if (relations.getCallRelations().empty())
            return isValidForGraph(relations, gep, readSize);

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

            // this vrlocation is unreachable with relations from given call relation
            hasConflict = hasConflict || ! merged.merge(*callRelation.callSiteRelations);
            merged.getCallRelations().clear();

            // since location is unreachable, it does not make sence to qualify the memory access
            if (hasConflict) continue;

            std::string result = isValidForGraph(merged, gep, readSize);
            if (result != "true") return result;
        }
        return "true";
    }

    AnalysisGraph(const llvm::Module& M, unsigned maxPass) : module(M) {
        GraphBuilder gb(module, locationMapping, blockMapping);
        gb.build();

        StructureAnalyzer sa(module, locationMapping, blockMapping);        
        RelationsAnalyzer ra(module, locationMapping, blockMapping, sa);
        ra.analyze(maxPass);
    }

    const std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& getBlockMapping() const {
        return blockMapping;
    }
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_ANALYSIS_GRAPH_HPP_

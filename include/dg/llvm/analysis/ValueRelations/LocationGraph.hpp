#ifndef _DG_LLVM_VALUE_RELATIONS_LOCATIONS_GRAPH_H_
#define _DG_LLVM_VALUE_RELATIONS_LOCATIONS_GRAPH_H_

#include <list>
#include <llvm/IR/Value.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/CFG.h>
#include "llvm/IR/Type.h"
#include "llvm/IR/Constants.h"

#include "RelationsGraph.hpp"

#ifndef NDEBUG
#include "getValName.h"
#endif

namespace dg {
namespace analysis {
namespace vr {

class VROp {
protected:
    enum class VROpType { INSTRUCTION, ASSUME, NOOP } type;
    VROp(VROpType t) : type(t) {}

public:
    bool isInstruction() const { return type == VROpType::INSTRUCTION; }
    bool isAssume() const { return type == VROpType::ASSUME; }
    bool isNoop() const { return type == VROpType::NOOP; }

    virtual ~VROp() = default;

#ifndef NDEBUG
    virtual void dump() const = 0;
#endif
};

struct VRNoop : public VROp {
    VRNoop() : VROp(VROpType::NOOP) {}

#ifndef NDEBUG
    void dump() const override {
        std::cout << "(noop)";
    }
#endif
};

struct VRInstruction : public VROp {
    const llvm::Instruction* instruction;

    VRInstruction(const llvm::Instruction* I)
    : VROp(VROpType::INSTRUCTION), instruction(I) {}

    const llvm::Instruction* getInstruction() const { return instruction; }

#ifndef NDEBUG
    void dump() const override {
        std::cout << debug::getValName(instruction);
    }
#endif
};

struct VRAssume : public VROp {
    std::pair<const llvm::Value*, const llvm::Value*> equals;

    VRAssume(const llvm::Value* lt, const llvm::Value* rt)
    : VROp(VROpType::ASSUME), equals(lt, rt) {}

    std::pair<const llvm::Value*, const llvm::Value*> getAssumption() const {
        return equals;
    }

#ifndef NDEBUG
    void dump() const override {
        std::cout << "assuming " << debug::getValName(equals.first)
                  << " = " << debug::getValName(equals.second);
    }
#endif
};

struct VRLocation;

struct VREdge {
    VRLocation *source;
    VRLocation *target;

    std::unique_ptr<VROp> op;

    VREdge(VRLocation *s, VRLocation *t, std::unique_ptr<VROp>&& op)
    : source(s), target(t), op(std::move(op)) {}
};

struct VRLocation  {
    const unsigned id;

    dg::vr::RelationsGraph<const llvm::Instruction *> rg;

    std::vector<VREdge *> predecessors;
    std::vector<std::unique_ptr<VREdge>> successors;

    VRLocation(unsigned _id) : id(_id) {}

    void connect(std::unique_ptr<VREdge>&& edge) {
        if (edge->target)
            edge->target->predecessors.push_back(edge.get());
        successors.emplace_back(std::move(edge));
    }

#ifndef NDEBUG
    void dump() const {
        std::cout << id << std::endl;
    }
#endif
};

struct VRBBlock {
    std::list<std::unique_ptr<VRLocation>> locations;

    void prepend(VRLocation* loc) {
        locations.emplace(locations.begin(), loc);
    }

    void append(VRLocation* loc) {
        locations.emplace_back(loc);
    }

    VRLocation *last() { return locations.back().get(); }
    VRLocation *first() { return locations.front().get(); }
    const VRLocation *last() const { return locations.back().get(); }
    const VRLocation *first() const { return locations.front().get(); }
};

struct LocationGraph {
    const llvm::Module& module;
    unsigned last_node_id = 0;

    // VRLocation corresponding to the state of the program BEFORE executing the instruction
    std::map<const llvm::Instruction *, VRLocation *> locationMapping;
    std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>> blockMapping;

    LocationGraph(const llvm::Module& m): module(m) {
        for (const llvm::Function& f : module) {
            build(f);
        }
    }

    void build(const llvm::Function& function) {
        for (const llvm::BasicBlock& block : function) {
            assert(block.size() != 0);
            build(block);
        }

        for (const llvm::BasicBlock& block : function) {
            VRBBlock* vrblock = getVRBBlock(&block);
            assert(vrblock);

            const llvm::Instruction* terminator = block.getTerminator();
            if (llvm::isa<llvm::BranchInst>(terminator)) {
                buildBranch(llvm::cast<llvm::BranchInst>(terminator), vrblock);

            } else if (llvm::isa<llvm::SwitchInst>(terminator)) {
                buildSwitch(llvm::cast<llvm::SwitchInst>(terminator), vrblock);

            } else if (llvm::isa<llvm::ReturnInst>(terminator)) {
                buildReturn(llvm::cast<llvm::ReturnInst>(terminator), vrblock);

            } else if (llvm::succ_begin(&block) != llvm::succ_end(&block)) {
#ifndef NDEBUG
                std::cerr << "Unhandled  terminator: " << std::endl;
                llvm::errs() << "Unhandled terminator: " << *terminator << "\n";
#endif
                abort();
            }
        }
    }

    void buildSwitch(const llvm::SwitchInst* swtch, VRBBlock* vrblock) {
        for (auto& it : swtch->cases()) {
            VRBBlock* succ = getVRBBlock(it.getCaseSuccessor());
            assert(succ);

            auto op = std::unique_ptr<VROp>(new VRAssume(swtch->getCondition(), it.getCaseValue()));
            VREdge* edge = new VREdge(vrblock->last(), succ->first(), std::move(op));
            vrblock->last()->connect(std::unique_ptr<VREdge>(edge));
        }

        VRBBlock* succ = getVRBBlock(swtch->getDefaultDest());
        assert(succ);
        auto op = std::unique_ptr<VROp>(new VRNoop());
        VREdge* edge = new VREdge(vrblock->last(), succ->first(), std::move(op));
        vrblock->last()->connect(std::unique_ptr<VREdge>(edge));

    }

    void buildBranch(const llvm::BranchInst* inst, VRBBlock* vrblock) {
        if (inst->isUnconditional()) {
            VRBBlock* succ = getVRBBlock(inst->getSuccessor(0));
            assert(succ);

            auto op = std::unique_ptr<VROp>(new VRNoop());
            VREdge* edge = new VREdge(vrblock->last(), succ->first(), std::move(op));

            vrblock->last()->connect(std::unique_ptr<VREdge>(edge));
        } else {
            VRBBlock* trueSucc = getVRBBlock(inst->getSuccessor(0));
            VRBBlock* falseSucc = getVRBBlock(inst->getSuccessor(1));

            llvm::LLVMContext& context = inst->getContext();

            llvm::Value* llvmTrue = llvm::ConstantInt::getTrue(context);
            llvm::Value* llvmFalse = llvm::ConstantInt::getFalse(context);

            auto trueOp = std::unique_ptr<VROp>(new VRAssume(inst->getCondition(), llvmTrue));
            auto falseOp = std::unique_ptr<VROp>(new VRAssume(inst->getCondition(), llvmFalse));

            VREdge* trueEdge = new VREdge(vrblock->last(), trueSucc->first(), std::move(trueOp));
            VREdge* falseEdge = new VREdge(vrblock->last(), falseSucc->first(), std::move(falseOp));

            vrblock->last()->connect(std::unique_ptr<VREdge>(trueEdge));
            vrblock->last()->connect(std::unique_ptr<VREdge>(falseEdge));
        }
    }

    void buildReturn(const llvm::ReturnInst* inst, VRBBlock* vrblock) {
        auto op = std::unique_ptr<VROp>(new VRInstruction(inst));
        VREdge* edge = new VREdge(vrblock->last(), nullptr, std::move(op));

        vrblock->last()->connect(std::unique_ptr<VREdge>(edge));
    }

    void build(const llvm::BasicBlock& block) {
        VRBBlock* vrblock = newBBlock(&block);

        auto it = block.begin();
        const llvm::Instruction* previous = &(*it);
        vrblock->append(newLocation(previous));
        ++it;

        for (; it != block.end(); ++it) {
            const llvm::Instruction& inst = *it;
            VRLocation* newLoc = newLocation(&inst);

            VREdge* edge = new VREdge(vrblock->last(), newLoc,
                                   std::unique_ptr<VROp>(new VRInstruction(previous)));
            vrblock->last()->connect(std::unique_ptr<VREdge>(edge));

            vrblock->append(newLoc);
            previous = &inst;
        }
    }

    VRLocation *newLocation(const llvm::Instruction* inst) {
        assert(inst);
        assert(locationMapping.find(inst) == locationMapping.end());

        auto location = new VRLocation(++last_node_id);
        assert(location);

        locationMapping.emplace(inst, location);
        return location;
    }

    VRBBlock *newBBlock(const llvm::BasicBlock* B) {
        assert(B);
        assert(blockMapping.find(B) == blockMapping.end());

        auto block = new VRBBlock();
        assert(block);

        blockMapping.emplace(B, block);
        return block;
    }

    VRBBlock *getVRBBlock(const llvm::BasicBlock* B) {
        const LocationGraph* constThis = this;
        return const_cast<VRBBlock*>(constThis->getVRBBlock(B));
    }

    const VRBBlock *getVRBBlock(const llvm::BasicBlock* B) const {
        auto it = blockMapping.find(B);
        return it == blockMapping.end() ? nullptr : it->second.get();
    }

    VRLocation *getVRLocation(const llvm::Instruction* inst) {
        const LocationGraph* constThis = this;
        return const_cast<VRLocation*>(constThis->getVRLocation(inst));
    }

    const VRLocation *getVRLocation(const llvm::Instruction* inst) const {
        auto it = locationMapping.find(inst);
        return it == locationMapping.end() ? nullptr : it->second;
    }

};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif //_DG_LLVM_VALUE_RELATIONS_LOCATIONS_GRAPH_H_

#ifndef _DG_LLVM_VALUE_RELATIONS_LOCATIONS_GRAPH_H_
#define _DG_LLVM_VALUE_RELATIONS_LOCATIONS_GRAPH_H_

#include <list>
#include <llvm/IR/Value.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

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

    VRInstruction(const llvm::Instruction *I)
    : VROp(VROpType::INSTRUCTION), instruction(I) {}

    const llvm::Instruction* getInstruction() const { return instruction; }

#ifndef NDEBUG
    void dump() const override {
        std::cout << debug::getValName(instruction);
    }
#endif
};

struct VRAssume : public VROp {
    bool assumption;

    VRAssume(bool a)
    : VROp(VROpType::ASSUME), assumption(a) {}

    bool getAssumption() const { return assumption; }

#ifndef NDEBUG
    void dump() const override {
        std::cout << "[" << assumption << "]";
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

    RelationsGraph<const llvm::Instruction *> rg;

    std::vector<VREdge *> predecessors;
    std::vector<std::unique_ptr<VREdge>> successors;

    VRLocation(unsigned _id) : id(_id) {}

    void connect(std::unique_ptr<VREdge>&& edge) {
        edge->target->predecessors.push_back(edge.get());
        successors.emplace_back(std::move(edge));
    }

#ifndef NDEBUG
    void dump() const {
        std::cout << id << " ";
        std::cout << std::endl;
    }
#endif
};

struct VRBBlock {
    std::list<std::unique_ptr<VRLocation>> locations;

    void prepend(std::unique_ptr<VRLocation>&& loc) {
        locations.push_front(std::move(loc));
    }

    void append(std::unique_ptr<VRLocation>&& loc) {
        locations.push_back(std::move(loc));
    }

    VRLocation *last() { return locations.back().get(); }
    VRLocation *first() { return locations.front().get(); }
    const VRLocation *last() const { return locations.back().get(); }
    const VRLocation *first() const { return locations.front().get(); }
};

class LocationGraph {
    const llvm::Module& module;
    unsigned last_node_id = 0;

    // VRLocation corresponding to the state of the program BEFORE executing the instruction
    std::map<const llvm::Instruction *, VRLocation *> locationMapping;
    std::map<const llvm::BasicBlock *, std::unique_ptr<VRBlock>> blockMapping;

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
    }

    void build(const llvm::BasicBlock& block) {
        VRBBlock* vrblock = newBBlock(block);

        auto it = block.begin();
        const VRLocation * previous = std::unique_ptr<VRLocation>(newLocation(*it));
        vrblock->append(std::move(loc));
        ++it;

        for (; it != block.end(); ++it) {
            const llvm::Instruction& inst = *it;
            VRLocation * newLoc = std::unique_ptr<VRLocation>(newLocation(inst));

            VREdge* edge = new VREdge(vrblock->last(), newLoc.get(),
                                   std::unique_ptr<VROp>(new VRInstruction(inst)));
            vrblock->last()->connect(std::unique_ptr<VREdge>(edge));

            vrblock->append(std::move(newLoc));
        }
    }

    VRLocation *newLocation(const llvm::Instruction& inst) {
        assert(inst);
        assert(locationMapping.find(&inst) == locationMapping.end());

        auto location = new VRLocation(++last_node_id);
        assert(location);

        locationMapping.emplace(&v, location);
        return location;
    }

    VRBBlock *newBBlock(const llvm::BasicBlock& B) {
        assert(B);
        assert(blockMapping.find(&B) == blockMapping.end());

        auto block = new VRBBlock();
        assert(block);

        blockMapping.emplace(&B, block);
        return block;
    }

    VRBBlock *getVRBBlock(const llvm::BasicBlock& B) {
        const LocationGraph& constThis = this;
        return const_cast<VRLocation*> constThis.getVRBBlock(B);
    }

    const VRBBlock *getVRBBlock(const llvm::BasicBlock& B) const {
        auto it = blockMapping.find(&B);
        return it == blockMapping.end() ? nullptr : it->second.get();
    }

    VRLocation *getVRLocation(const llvm::Instruction& inst) {
        const LocationGraph& constThis = this;
        return const_cast<VRLocation*> constThis.getVRLocation(inst);
    }

    const VRLocation *getVRLocation(const llvm::Instruction& inst) const {
        auto it = locationMapping.find(&inst);
        return it == locationMapping.end() ? nullptr : it->second;
    }

};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif //_DG_LLVM_VALUE_RELATIONS_LOCATIONS_GRAPH_H_

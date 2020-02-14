#ifndef _DG_LLVM_VALUE_RELATIONS_GRAPH_ELEMENTS_HPP_
#define _DG_LLVM_VALUE_RELATIONS_GRAPH_ELEMENTS_HPP_

#include <list>
#include <llvm/IR/Instructions.h>

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

} // namespace vr
} // namespace analysis
} // namespace dg

#endif //_DG_LLVM_VALUE_RELATIONS_GRAPH_ELEMENTS_HPP_
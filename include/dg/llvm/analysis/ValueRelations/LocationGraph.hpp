#ifndef _DG_LLVM_VALUE_RELATIONS_LOCATIONS_GRAPH_H_
#define _DG_LLVM_VALUE_RELATIONS_LOCATIONS_GRAPH_H_

#include <list>
#include <llvm/IR/Instructions.h>

#include "RelationsGraph.hpp"

#ifndef NDEBUG
#include "getValName.h"
#endif

namespace dg {
namespace analysis {

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

    RelationsGraph<const llvm::Value *> rg;

    std::vector<VREdge *> predecessors;
    std::vector<std::unique_ptr<VREdge>> successors;

    VRLocation(unsigned _id) : id(_id) {}

    void addEdge(std::unique_ptr<VREdge>&& edge) {
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

} // namespace analysis
} // namespace dg

#endif //_DG_LLVM_VALUE_RELATIONS_LOCATIONS_GRAPH_H_
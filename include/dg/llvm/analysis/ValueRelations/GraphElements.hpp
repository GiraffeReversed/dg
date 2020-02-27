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
    enum class VROpType { NOOP, INSTRUCTION, ASSUME_BOOL, ASSUME_EQUAL } type;
    VROp(VROpType t) : type(t) {}

public:
    bool isNoop() const { return type == VROpType::NOOP; }
    bool isInstruction() const { return type == VROpType::INSTRUCTION; }
    bool isAssume() const { return isAssumeBool() || isAssumeEqual(); }
    bool isAssumeBool() const { return type == VROpType::ASSUME_BOOL; }
    bool isAssumeEqual() const { return type == VROpType::ASSUME_EQUAL; }

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
    const llvm::Value* val;

    const llvm::Value* getValue() const {
        return val;
    }

protected:
    VRAssume(VROpType type, const llvm::Value* v) : VROp(type), val(v) {}

    void dump() const override {
        std::cout << "assuming " << debug::getValName(val) << " is ";
    }
};

struct VRAssumeBool : public VRAssume {
    bool assumption;

    VRAssumeBool(const llvm::Value* v, bool b)
        : VRAssume(VROpType::ASSUME_BOOL, v), assumption(b) {}

    bool getAssumption() const {
        return assumption;
    }

#ifndef NDEBUG
    void dump() const override {
        VRAssume::dump();
        std::cout << (assumption ? "true" : "false") << std::endl;
    }
#endif
};

struct VRAssumeEqual : public VRAssume {
    const llvm::Value* assumption;

    VRAssumeEqual(const llvm::Value* v, const llvm::Value* a)
        : VRAssume(VROpType::ASSUME_EQUAL, v), assumption(a) {}

    const llvm::Value* getAssumption() const {
        return assumption;
    }

#ifndef NDEBUG
    void dump() const override {
        VRAssume::dump();
        std::cout << debug::getValName(assumption) << std::endl;
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

    RelationsGraph<const llvm::Value *> relations;

    std::vector<VREdge *> predecessors;
    std::vector<std::unique_ptr<VREdge>> successors;

    VRLocation(unsigned _id) : id(_id) {}

    void connect(std::unique_ptr<VREdge>&& edge) {
        if (edge->target)
            edge->target->predecessors.push_back(edge.get());
        successors.emplace_back(std::move(edge));
    }

    std::vector<VRLocation*> getPredLocations() {
        std::vector<VRLocation*> result;
        for (VREdge * edge : predecessors) {
            result.push_back(edge->source);
        }
        return result;
    }

    std::vector<VRLocation*> getSuccLocations() {
        std::vector<VRLocation*> result;
        for (auto& edge : successors) {
            result.push_back(edge->target);
        }
        return result;
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

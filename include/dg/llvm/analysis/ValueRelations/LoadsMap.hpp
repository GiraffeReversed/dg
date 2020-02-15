#ifndef _DG_LLVM_LOADS_MAP_HPP_
#define _DG_LLVM_LOADS_MAP_HPP_

#include <map>
#include <cassert>

#include <llvm/IR/Value.h>

#ifndef NDEBUG
#include "getValName.h"
#endif

namespace dg {
namespace analysis {
namespace vr {

class LoadsMap {
    // pair (a,b) such that a = load b in the future
    std::map<const llvm::Value *, const llvm::Value *> loads;

public:
    void setLoad(const llvm::Value *from, const llvm::Value *val) {
        assert(val && from);
        loads.emplace(val, from);
    }

    void unsetLoadByVal(const llvm::Value* val) {
        assert(val);
        loads.erase(val);
    }

    void unsetLoadByPtr(const llvm::Value* from) {
        assert(from);
        for (auto& pair : loads) {
            if (from == pair.second)
                loads.erase(pair.first);
        }
    }

    const llvm::Value* getValByPtr(const llvm::Value *from) const {
        for (const auto& pair : loads) {
            if (pair.second == from)
                return pair.first;
        }
        return nullptr;
    }

    const llvm::Value* getPtrByVal(const llvm::Value* val) const {
        auto result = loads.find(val);
        if (result == loads.end())
            return nullptr;
        return result->second;
    }

#ifndef NDEBUG
    void dump() const {
        for (const auto& pair : loads) {
            std::cout << debug::getValName(pair.first) << " = load "
                      << debug::getValName(pair.second);
        }
    }
#endif // NDEBUG
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_LOADS_MAP_HPP_

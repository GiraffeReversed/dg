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
    // pair (a,b) such that any of b = load a in the future
    std::map<const llvm::Value *, std::set<const llvm::Value *>> loads;

public:
    friend bool operator==(const LoadsMap& lt, const LoadsMap& rt) {
        return lt.loads == rt.loads;
    }

    friend bool operator!=(const LoadsMap& lt, const LoadsMap& rt) {
        return ! (lt == rt);
    }

    friend void swap(LoadsMap& lt, LoadsMap& rt) {
        lt.loads.swap(rt.loads);
    }

    void setLoad(const llvm::Value *val, const llvm::Value *from) {
        assert(val && from);

        auto found = loads.find(from);
        if (found != loads.end()) {
            found->second.insert(val);
            return;
        }

        std::set<const llvm::Value*> temp;
        temp.insert(val);
        loads.emplace(from, std::move(temp));
    }

    /*void unsetLoadByVal(const llvm::Value* val) {
        for (auto& pair : loads) {

        }
        assert(val);
        loads.erase(val);
    }

    void unsetLoadByPtr(const llvm::Value* from) {
        assert(from);
        for (auto& pair : loads) {
            if (from == pair.second)
                loads.erase(pair.first);
        }
    }*/

    void unsetAllLoadsByPtr(const llvm::Value* from) {
        loads.erase(from);
    }

    const llvm::Value* getValByPtr(const llvm::Value *from) const {
        return *(loads.find(from)->second.begin());
    }

    const llvm::Value* getPtrByVal(const llvm::Value* val) const {
        for (const auto& pair : loads) {
            if (pair.second.find(val) != pair.second.end()) return pair.first;
        }
        return nullptr;
    }

    const std::map<const llvm::Value*, std::set<const llvm::Value*>>& getAllLoads() const {
        return loads;
    }

    void clearAll() {
        loads.clear();
    }

#ifndef NDEBUG
    void dump() const {
        for (const auto& pair : loads) {
            std::cout << "{ ";
            for (const llvm::Value* val : pair.second) {
                std::cout << debug::getValName(val) << ", ";
            }
            std::cout << "} = load (" << debug::getValName(pair.first) << ")" << std::endl;
        }
    }
#endif // NDEBUG
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_LOADS_MAP_HPP_

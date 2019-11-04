#ifndef _DG_LLVM_RELATIONS_MAP_H_
#define _DG_LLVM_RELATIONS_MAP_H_

#include <set>
#include <map>

namespace dg {

template <typename T>
class IdentityBucket {
	std::set<T> identities;
};

template <typename T>
class EqualityBucket {
	std::map<T, IdentityBucket<T>> mapping;
};

template <typename T>
class RelationsGraph {
	std::map<T, EqualityBucket<T>> mapping;
};

} // namespace dg

#endif // _DG_LLVM_RELATIONS_MAP_H_

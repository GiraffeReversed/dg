#ifndef _DG_LLVM_RELATIONS_MAP_H_
#define _DG_LLVM_RELATIONS_MAP_H_

#include <set>
#include <map>

namespace {

template <typename Key, typename Val>
bool contains(const std::map<Key, Val>& map, const Key& key) {
	return map.find(key) != map.end();
}

template <typename Val>
bool contains(const std::set<Val>& set, const Val& val) {
	return set.find(val) != set.end();
}

} // namespace

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

	public:
		bool isIdentical(const T& lt, const T& rt) {
			if (!isEqual(lt, rt))
				return false;
			const auto& ltIdBucket = mapping.at(lt).at(lt);
			return contains(ltIdBucket, rt);
		}


		bool isEqual(const T& lt, const T& rt) {
			if (!contains(mapping, lt) || !contains(mapping, rt))
				return false;
			const auto& ltEqBucket = mapping.at(lt);
			return contains(ltEqBucket, rt);
		}
};

} // namespace dg

#endif // _DG_LLVM_RELATIONS_MAP_H_

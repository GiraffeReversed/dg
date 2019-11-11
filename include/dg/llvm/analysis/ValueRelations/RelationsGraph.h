#ifndef _DG_LLVM_RELATIONS_MAP_H_
#define _DG_LLVM_RELATIONS_MAP_H_

#include <set>
#include <map>
#include <stack>
#include <tuple>
#include <memory>

#include <iostream>

namespace {

template <typename Key, typename Val>
bool contains(const std::map<Key, Val>& map, const Key& key) {
	return map.find(key) != map.end();
}

template <typename Val>
bool contains(const std::set<Val>& set, const Val& val) {
	return set.find(val) != set.end();
}

template <typename T>
typename std::set<std::unique_ptr<T>>::iterator findPtr(std::set<std::unique_ptr<T>>& haystack,
														const T* const needle) {
	auto it = haystack.begin();
	
	while (it != haystack.end()) {
		if (it->get() == needle)
			return it;
		++it;
	}

	return it;
}

} // namespace

namespace dg {

template <typename T>
class EqualityBucket {

    template <typename S> friend class RelationsGraph;

    using BucketPtr = EqualityBucket<T>*;
	using BucketPtrSet = std::set<BucketPtr>;
	
	BucketPtrSet lesserEqual;
	BucketPtrSet lesser;
	BucketPtrSet parents;

	bool subtreeContains(const EqualityBucket<T>* needle, bool ignoreLE) const {

		using ConstBucketPtr = const EqualityBucket<T>*;
		using Frame = std::tuple<ConstBucketPtr, typename BucketPtrSet::const_iterator, bool>;

        std::set<const EqualityBucket<T>*> visited;
		std::stack<Frame> stack;

		visited.insert(this);
		stack.push(Frame(this, lesserEqual.begin(), ignoreLE));

		ConstBucketPtr bucketPtr;
		typename BucketPtrSet::iterator succIt;
		bool ignore;
		while (! stack.empty()) {
			std::tie(bucketPtr, succIt, ignore) = stack.top();
			stack.pop();

			if (bucketPtr == needle)
				return ! ignore;

			if (succIt == lesserEqual.end()) {
				succIt = lesser.begin();
				ignore = false;
			}

			if (succIt == lesser.end()) {
				continue;
			}

			stack.push({ bucketPtr, ++succIt, ignore });

			if (! contains<const EqualityBucket<T>*>(visited, *succIt)) {
				visited.insert(*succIt);
				stack.emplace(Frame(*succIt, (*succIt)->lesserEqual.begin(), ignore));
			}
		}

		return false;
	}


	void merge(const EqualityBucket<T>& other) {
		// set_union does't work in place
		lesserEqual.insert(other.lesserEqual.begin(), other.lesserEqual.end());
		lesser.insert(other.lesser.begin(), other.lesser.end());
		parents.insert(other.parents.begin(), other.parents.end());
	}

	void eraseFromParents() {
		for (auto* parent : parents) {
			parent->lesserEqual.erase(this);
			parent->lesser.erase(this);
		}
	}
	
};

template <typename T>
class RelationsGraph {

    std::set<std::unique_ptr<EqualityBucket<T>>> buckets;
    std::map<T, T*> loads;
	std::map<T, EqualityBucket<T>*> equalities;

	bool areInGraph(const T& lt, const T& rt) const {
		return contains(equalities, lt) && contains(equalities, rt);
	}
	
	public:
	bool add(const T& val) {
		EqualityBucket<T>* newBucketPtr = new EqualityBucket<T>;
		buckets.emplace(newBucketPtr);
		return equalities.emplace(val, newBucketPtr).second;
	}

	void setEqual(const T& lt, const T& rt) {
		EqualityBucket<T>* newBucketPtr = equalities.at(lt);
		EqualityBucket<T>* oldBucketPtr = equalities.at(rt);
		
		// make successors and parents of right belong to left too
		newBucketPtr->merge(*oldBucketPtr);

		// replace values' pointers to right with pointers to left
		for (auto& pair : equalities) {
			if (pair.second == oldBucketPtr)
				pair.second = newBucketPtr;
		}

		// remove right
		auto it = findPtr(buckets, oldBucketPtr);
		if (it != buckets.end())
			oldBucketPtr->eraseFromParents();
			buckets.erase(it);
	}

	void setLesser(const T& lt, const T& rt) {
		EqualityBucket<T>* ltBucketPtr = equalities.at(lt);
		EqualityBucket<T>* rtBucketPtr = equalities.at(rt);

		rtBucketPtr->lesser.insert(ltBucketPtr);
		ltBucketPtr->parents.insert(rtBucketPtr);
	}

	void setLesserEqual(const T& lt, const T& rt) {
		EqualityBucket<T>* ltBucketPtr = equalities.at(lt);
		EqualityBucket<T>* rtBucketPtr = equalities.at(rt);

		rtBucketPtr->lesserEqual.insert(ltBucketPtr);
		ltBucketPtr->parents.insert(rtBucketPtr);
	}

	void unsetRelations(const T& val) {
		EqualityBucket<T>* valBucketPtr = equalities.at(val);
		
		bool onlyReference = true;
		for (auto& pair : equalities) {
			if (pair.first != val && pair.second == valBucketPtr) {
				onlyReference = false;
				break;
			}
		}

		if (! onlyReference) {
			// val is no longer part of this equality bucket, it moves to its own
			equalities.erase(val);
			add(val);
		} else {
			// it severes all ties with the rest of the graph
			valBucketPtr->eraseFromParents();
			valBucketPtr->lesserEqual.clear();
			valBucketPtr->lesser.clear();
		}
	}

	void setLoad(const T& address, T& value) {
		loads.emplace(address, &value);
	}

	void unsetLoad(const T& address) {
		loads.erase(address);
	}

	bool isEqual(const T& lt, const T& rt) const {

		if (! areInGraph(lt, rt))
			return false;

		return equalities.at(lt) == equalities.at(rt);
	}

	bool isLesser(const T& lt, const T& rt) const {

		if (! areInGraph(lt, rt))
			return false;

		const auto& rtEqBucket = equalities.at(rt);
		return rtEqBucket->subtreeContains(equalities.at(lt), true);
	}

	bool isLesserEqual(const T& lt, const T& rt) const {

		if (! areInGraph(lt, rt))
			return false;

		const auto& rtEqBucket = equalities.at(rt);
		return rtEqBucket->subtreeContains(equalities.at(lt), false);
	}
};

} // namespace dg

#endif // _DG_LLVM_RELATIONS_MAP_H_

#ifndef _DG_LLVM_RELATIONS_MAP_H_
#define _DG_LLVM_RELATIONS_MAP_H_

#include <set>
#include <map>
#include <stack>
#include <tuple>
#include <memory>

#include <cassert>

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

	using Frame = std::tuple<BucketPtr, typename BucketPtrSet::iterator, bool>;

	std::pair<std::stack<Frame>, bool> subtreeContains(const EqualityBucket<T>* needle, bool ignoreLE) {

        std::set<const EqualityBucket<T>*> visited;
		std::stack<Frame> stack;

		visited.insert(this);
		stack.push(Frame(this, lesserEqual.begin(), ignoreLE));

		BucketPtr bucketPtr;
		typename BucketPtrSet::iterator successorIt;
		bool ignore;
		while (! stack.empty()) {
			std::tie(bucketPtr, successorIt, ignore) = stack.top();
			
			// we found searched bucket
			if (bucketPtr == needle) {
				if (ignore)	return { std::stack<Frame>(), false };
				return { stack, true };
			}

			stack.pop();

			// we searched all lesserEqual buckets, goiong on to lesser buckets
			if (successorIt == bucketPtr->lesserEqual.end()) {
				successorIt = bucketPtr->lesser.begin();
			}
			
			// we searched all successors
			if (successorIt == bucketPtr->lesser.end()) {
				continue;
			}

			// plan to return for next successor
			stack.push({ bucketPtr, ++successorIt, ignore });
			--successorIt;

			// plan visit to successor
			if (! contains<const EqualityBucket<T>*>(visited, *successorIt)) {
				visited.insert(*successorIt);
				stack.emplace(Frame(*successorIt, (*successorIt)->lesserEqual.begin(), ignore));
			}
		}

		return { std::stack<Frame>(), false };
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

	RelationsGraph() = default;
	
	RelationsGraph(const RelationsGraph& other)
		: loads(other.loads), equalities(other.equalities) {
	// doesnt work	
		for(const auto& bucketPtr : buckets) {
			assert(bucketPtr);
			
			EqualityBucket<T>* newBucketPtr = new EqualityBucket<T>(*bucketPtr);
			buckets.emplace(newBucketPtr);
		}
		
	}

	friend void swap(RelationsGraph& first, RelationsGraph& second) {
		using std::swap;

		swap(first.buckets, second.buckets);
		swap(first.loads, second.loads);
		swap(first.equalities, second.equalities);
	}

	RelationsGraph& operator=(RelationsGraph other) {
		swap(*this, other);

		return *this;
	}

	bool add(const T& val) {
		EqualityBucket<T>* newBucketPtr = new EqualityBucket<T>;
		buckets.emplace(newBucketPtr);
		
		return equalities.emplace(val, newBucketPtr).second;
	}

	void setEqual(const T& lt, const T& rt) {

		if (isEqual(lt, rt)) return;

		// assert no conflicting relations
		assert(! isLesser(lt, rt));
		assert(! isLesser(rt, lt));

		EqualityBucket<T>* newBucketPtr = equalities.at(lt);
		EqualityBucket<T>* oldBucketPtr = equalities.at(rt);
		
		// handle lesserEqual specializing to equal
		if (isLesserEqual(lt, rt) || isLesserEqual(rt, lt)) {
			// TODO merge all nodes on path between
		}

		// make successors and parents of right belong to left too
		newBucketPtr->merge(*oldBucketPtr);

		// replace values' pointers to right with pointers to left
		for (auto& pair : equalities) {
			if (pair.second == oldBucketPtr)
				pair.second = newBucketPtr;
		}

		// remove right
		auto it = findPtr(buckets, oldBucketPtr);
		if (it != buckets.end()) {
			oldBucketPtr->eraseFromParents();
			buckets.erase(it);
		}
	}

	void setLesser(const T& lt, const T& rt) {

		if (isLesser(lt, rt)) return;

		// assert no conflicting relations
		assert(! isEqual(lt, rt));
		assert(! isLesserEqual(rt, lt));
		assert(! isLesser(rt, lt));

		EqualityBucket<T>* ltBucketPtr = equalities.at(lt);
		EqualityBucket<T>* rtBucketPtr = equalities.at(rt);

		// handle lesserEqual specializing to lesser
		if (isLesserEqual(lt, rt)) {
			if (contains<EqualityBucket<T>*>(rtBucketPtr->lesserEqual, ltBucketPtr))
				rtBucketPtr->lesserEqual.erase(ltBucketPtr);
			else
				assert(0); // more buckets in between, cant decide this
		}

		rtBucketPtr->lesser.insert(ltBucketPtr);
		ltBucketPtr->parents.insert(rtBucketPtr);
	}

	void setLesserEqual(const T& lt, const T& rt) {

		if (isLesserEqual(lt, rt) || isEqual(lt, rt) || isLesser(lt, rt)) return;

		// assert no conflicting relations
		assert(! isLesser(rt, lt));

		// infer values being equal
		if (isLesserEqual(rt, lt)) {
			setEqual(lt, rt);
			return;
		}

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
			valBucketPtr->parents.clear();
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
		return rtEqBucket->subtreeContains(equalities.at(lt), true).second;
	}

	bool isLesserEqual(const T& lt, const T& rt) const {

		if (! areInGraph(lt, rt))
			return false;

		const auto& rtEqBucket = equalities.at(rt);
		return rtEqBucket->subtreeContains(equalities.at(lt), false).second;
	}
};

} // namespace dg

#endif // _DG_LLVM_RELATIONS_MAP_H_

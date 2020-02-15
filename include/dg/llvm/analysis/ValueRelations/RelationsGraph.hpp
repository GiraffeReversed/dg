#ifndef _DG_LLVM_RELATIONS_MAP_H_
#define _DG_LLVM_RELATIONS_MAP_H_

#include <set>
#include <map>
#include <stack>
#include <vector>
#include <tuple>
#include <memory>
#include <algorithm>

#include <cassert>

#ifndef NDEBUG
    #include <iostream>
	#include "getValName.h"
#endif

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


template <typename T>
void substitueInSet(const std::map<T, T>& mapping, std::set<T>& set) {
	std::set<T> newSet;

	for (auto& element : set) {
		newSet.insert(mapping.at(element));
	}
	set.swap(newSet);
}

} // namespace

namespace dg {
namespace analysis {
namespace vr {

class EqualityBucket {

    template <typename S> friend class RelationsGraph;

    using BucketPtr = EqualityBucket*;
	using BucketPtrSet = std::set<BucketPtr>;
	
	BucketPtrSet lesserEqual;
	BucketPtrSet lesser;
	BucketPtrSet parents;

	using Frame = std::tuple<BucketPtr, typename BucketPtrSet::iterator, bool>;

	std::pair<std::stack<Frame>, bool> subtreeContains(const EqualityBucket* needle, bool ignoreLE) {

        std::set<const EqualityBucket*> visited;
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

			// we searched all lesserEqual buckets, going on to lesser buckets
			if (successorIt == bucketPtr->lesserEqual.end()) {
				successorIt = bucketPtr->lesser.begin();
				ignore = false;
			}
			
			// we searched all successors
			if (successorIt == bucketPtr->lesser.end()) {
				continue;
			}

			// plan to return for next successor
			stack.push({ bucketPtr, ++successorIt, ignore });
			--successorIt;

			// plan visit to successor
			if (! contains<const EqualityBucket*>(visited, *successorIt)) {
				visited.insert(*successorIt);
				stack.emplace(Frame(*successorIt, (*successorIt)->lesserEqual.begin(), ignore));
			}
		}

		return { std::stack<Frame>(), false };
	}


	void merge(const EqualityBucket& other) {
		// set_union does't work in place
		lesserEqual.insert(other.lesserEqual.begin(), other.lesserEqual.end());
		lesser.insert(other.lesser.begin(), other.lesser.end());
		parents.insert(other.parents.begin(), other.parents.end());
	}

	void disconnectAll() {
		for (auto* parent : parents) {
			parent->lesserEqual.erase(this);
			parent->lesser.erase(this);
		}
		parents.clear();

		for (auto* bucketPtr : lesserEqual) {
			bucketPtr->parents.erase(this);
		}
		lesserEqual.clear();
		
		for (auto* bucketPtr : lesser) {
			bucketPtr->parents.erase(this);
		}
		lesser.clear();
	}

	void substitueAll(const std::map<EqualityBucket*, EqualityBucket*>& oldToNewPtr) {
		substitueInSet<EqualityBucket*>(oldToNewPtr, lesserEqual);
		substitueInSet<EqualityBucket*>(oldToNewPtr, lesser);
		substitueInSet<EqualityBucket*>(oldToNewPtr, parents);
	}

#ifndef NDEBUG
    void dump(std::map<const EqualityBucket*, int> numbering) const {

		for (const EqualityBucket* bucket : lesser) {
			std::cout << numbering.at(bucket) << " < " << numbering.at(this) << std::endl;
		}

		for (const EqualityBucket* bucket : lesserEqual) {
			std::cout << numbering.at(bucket) << " <= " << numbering.at(this) << std::endl;
		}
    }
#endif

};

template <typename T>
class RelationsGraph {

    std::set<std::unique_ptr<EqualityBucket>> buckets;
	std::map<T, EqualityBucket*> mapToBucket;

	bool areInGraph(T lt, T rt) const {
		return contains(mapToBucket, lt) && contains(mapToBucket, rt);
	}

	std::vector<T> getEqual(EqualityBucket* valBucket) const {
		for (const std::pair<T, EqualityBucket*>& valueToBucket : mapToBucket) {
			if (valBucket == valueToBucket.second)
				return getEqual(valueToBucket.first);
		}
		assert(0);
	}
	
public:

	RelationsGraph() = default;
	
	RelationsGraph(const RelationsGraph& other) {

		std::map<EqualityBucket*, EqualityBucket*> oldToNewPtr;

		// create new copies of buckets
		for(const std::unique_ptr<EqualityBucket>& bucketUniquePtr : other.buckets) {
			assert(bucketUniquePtr);
			assert(bucketUniquePtr.get());
			
			EqualityBucket* newBucketPtr = new EqualityBucket(*bucketUniquePtr);
			buckets.emplace(newBucketPtr);

			oldToNewPtr.emplace(bucketUniquePtr.get(), newBucketPtr);
		}

		// set successors to point to new copies
		for (const std::unique_ptr<EqualityBucket>& bucketUniquePtr : buckets)
			bucketUniquePtr->substitueAll(oldToNewPtr);

		// set map to use new copies
		for (auto& pair : other.mapToBucket)
			mapToBucket.emplace(pair.first, oldToNewPtr.at(pair.second));
		
	}

	friend void swap(RelationsGraph& first, RelationsGraph& second) {
		using std::swap;

		swap(first.buckets, second.buckets);
		swap(first.mapToBucket, second.mapToBucket);
	}

	RelationsGraph& operator=(RelationsGraph other) {
		swap(*this, other);

		return *this;
	}

	friend bool relationsEqual(const RelationsGraph& lt, const RelationsGraph& rt) {
		std::vector<T> ltVals = lt.getAllValues();
        std::vector<T> rtVals = rt.getAllValues();

        std::sort(ltVals.begin(), ltVals.end());
        std::sort(rtVals.begin(), rtVals.end());

        if (ltVals != rtVals) {
            return false;
        }

        for (auto& fst : ltVals) {
            for (auto& snd : ltVals) {
                if ((lt.isEqual(fst, snd) && ! rt.isEqual(fst, snd)) ||
				    (lt.isLesser(fst, snd) && ! rt.isLesser(fst, snd)) ||
					(lt.isLesser(snd, fst) && ! rt.isLesser(snd, fst)) ||
					(lt.isLesserEqual(fst, snd) && ! rt.isLesserEqual(fst, snd)) ||
					(lt.isLesserEqual(snd, fst) && ! rt.isLesserEqual(snd, fst)))
					return false;
            }
        }
		return true;
	}

	void add(T val) {
		if (mapToBucket.find(val) != mapToBucket.end()) return;

		EqualityBucket* newBucketPtr = new EqualityBucket;
		buckets.emplace(newBucketPtr);
		mapToBucket.emplace(val, newBucketPtr);
	}

	void setEqual(T lt, T rt) {

		// DANGER defined duplicitly (already in subtreeContains)
		using BucketPtr = EqualityBucket*;
		using BucketPtrSet = std::set<BucketPtr>;
		using Frame = std::tuple<BucketPtr, typename BucketPtrSet::iterator, bool>;

		add(lt);
		add(rt);

		if (isEqual(lt, rt)) return;

		// assert no conflicting relations
		assert(! isLesser(lt, rt));
		assert(! isLesser(rt, lt));

		EqualityBucket* newBucketPtr = mapToBucket.at(lt);
		EqualityBucket* oldBucketPtr = mapToBucket.at(rt);
		
		std::vector<BucketPtr> toMerge;

		// handle lesserEqual specializing to equal
		if (isLesserEqual(lt, rt) || isLesserEqual(rt, lt)) {

			std::pair<std::stack<Frame>, bool> pair;
			if (isLesserEqual(lt, rt)) {
				pair = oldBucketPtr->subtreeContains(newBucketPtr, false);
			} else {
				pair = newBucketPtr->subtreeContains(oldBucketPtr, false);
			}
			std::stack<Frame> frames = pair.first;

			Frame frame;
			while (! frames.empty()) {
				frame = frames.top();
				toMerge.push_back(std::get<0>(frame));
				frames.pop();
			}

		} else {
			toMerge = { newBucketPtr, oldBucketPtr };
		}

		newBucketPtr = toMerge[0];

		for (auto it = ++toMerge.begin(); it != toMerge.end(); ++it) {

			oldBucketPtr = *it;

			// replace values' pointers to right with pointers to left
			for (auto& pair : mapToBucket) {
				if (pair.second == oldBucketPtr)
					pair.second = newBucketPtr;
			}

			// make successors and parents of right belong to left too
			newBucketPtr->merge(*oldBucketPtr);

			// remove right
			auto ite = findPtr(buckets, oldBucketPtr);
			if (ite != buckets.end()) {
				oldBucketPtr->disconnectAll();
				buckets.erase(ite);
			}
		}
	}

	void setLesser(T lt, T rt) {

		add(lt); assert(mapToBucket.find(lt) != mapToBucket.end());
		add(rt); assert(mapToBucket.find(rt) != mapToBucket.end());

		if (isLesser(lt, rt)) return;

		// assert no conflicting relations
		assert(! isEqual(lt, rt));
		assert(! isLesserEqual(rt, lt));
		assert(! isLesser(rt, lt));

		EqualityBucket* ltBucketPtr = mapToBucket.at(lt);
		EqualityBucket* rtBucketPtr = mapToBucket.at(rt);

		// handle lesserEqual specializing to lesser
		if (isLesserEqual(lt, rt)) {
			if (contains<EqualityBucket*>(rtBucketPtr->lesserEqual, ltBucketPtr))
				rtBucketPtr->lesserEqual.erase(ltBucketPtr);
			else
				assert(0); // more buckets in between, can't decide this
		}

		rtBucketPtr->lesser.insert(ltBucketPtr);
		ltBucketPtr->parents.insert(rtBucketPtr);
	}

	void setLesserEqual(T lt, T rt) {

		add(lt);
		add(rt);

		if (isLesserEqual(lt, rt) || isEqual(lt, rt) || isLesser(lt, rt)) return;

		// assert no conflicting relations
		assert(! isLesser(rt, lt));

		// infer values being equal
		if (isLesserEqual(rt, lt)) {
			setEqual(lt, rt);
			return;
		}

		EqualityBucket* ltBucketPtr = mapToBucket.at(lt);
		EqualityBucket* rtBucketPtr = mapToBucket.at(rt);

		rtBucketPtr->lesserEqual.insert(ltBucketPtr);
		ltBucketPtr->parents.insert(rtBucketPtr);
	}

	void unsetRelations(T val) {
		EqualityBucket* valBucketPtr = mapToBucket.at(val);
		
		bool onlyReference = true;
		for (auto& pair : mapToBucket) {
			if (pair.first != val && pair.second == valBucketPtr) {
				onlyReference = false;
				break;
			}
		}

		if (! onlyReference) {
			// val moves to its own equality bucket
			mapToBucket.erase(val);
			add(val);
		} else {
			// overconnect parents to children
			for (EqualityBucket* parent : valBucketPtr->parents) {
				parent->lesserEqual.insert(valBucketPtr->lesserEqual.begin(),
										   valBucketPtr->lesserEqual.end());
				parent->lesser.insert(valBucketPtr->lesser.begin(),
									  valBucketPtr->lesser.end());
			}

			// it severes all ties with the rest of the graph
			valBucketPtr->disconnectAll();
		}
	}

	bool isEqual(T lt, T rt) const {

		if (! areInGraph(lt, rt))
			return false;

		return mapToBucket.at(lt) == mapToBucket.at(rt);
	}

	bool isLesser(T lt, T rt) const {

		if (! areInGraph(lt, rt))
			return false;

		const auto& rtEqBucket = mapToBucket.at(rt);
		return rtEqBucket->subtreeContains(mapToBucket.at(lt), true).second;
	}

	bool isLesserEqual(T lt, T rt) const {

		if (! areInGraph(lt, rt))
			return false;

		const auto& rtEqBucket = mapToBucket.at(rt);
		return rtEqBucket->subtreeContains(mapToBucket.at(lt), false).second;
	}

	std::vector<T> getEqual(T val) const {
		const auto* valBucket = mapToBucket.at(val);
		std::vector<T> result;

		T other;
		const EqualityBucket* otherBucket;
		for (const auto& valueToBucket : mapToBucket) {
			std::tie(other, otherBucket) = valueToBucket;
			if (valBucket == otherBucket) {
				result.push_back(other);
			}
		}
		
		return result;
	}

	std::vector<T> getAllValues() const {
		std::vector<T> result;
		for (auto& pair : mapToBucket)
			result.push_back(pair.first);
		return result;
	}

#ifndef NDEBUG
    void dump() const {
		std::map<const EqualityBucket*, int> numbering;

		int last_id = 0;
		for (const auto& bucketPtr : buckets) {
			numbering.emplace(bucketPtr.get(), ++last_id);

			std::cout << last_id << " = { ";
			for (T val : getEqual(bucketPtr.get()))
				std::cout << debug::getValName(val) << "; ";
			std::cout << " }" << std::endl;
		}

		for (const auto& bucketPtr : buckets) {
			bucketPtr->dump(numbering);
		}
    }
#endif

};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_RELATIONS_MAP_H_

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
auto findPtr(const std::vector<std::unique_ptr<T>>& haystack,
								const T* const needle) -> decltype(haystack.begin()) {
	auto it = haystack.begin();
	
	while (it != haystack.end()) {
		if (it->get() == needle)
			return it;
		++it;
	}

	return it;
}

template <typename T>
void eraseUniquePtr(std::vector<std::unique_ptr<T>>& set, const T* const value) {
	auto ite = findPtr(set, value);
	assert (ite != set.end());
	set.erase(ite);
}

template <typename T>
void substitueInSet(const std::map<T, T>& mapping, std::set<T>& set) {
	std::set<T> newSet;

	for (auto& element : set) {
		if (contains(mapping, element))
			newSet.insert(mapping.at(element));
		else newSet.insert(element);
	}
	set.swap(newSet);
}

template <typename T>
T findByKey(const std::map<T, T>& map, T key) {
	auto found = map.find(key);
	if (found == map.end()) return nullptr;
	return found->second;
}

template <typename T>
T findByValue(const std::map<T, T>& map, T value) {
	for (auto& pair : map) {
		if (pair.second == value) return pair.first;
	}
	return nullptr;
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

	void merge(EqualityBucket& other) { // TODO other should be const
		// set_union does't work in place
		lesserEqual.insert(other.lesserEqual.begin(), other.lesserEqual.end());
		for (EqualityBucket* bucketPtr : other.lesserEqual)
			bucketPtr->parents.insert(this);

		lesser.insert(other.lesser.begin(), other.lesser.end());
		for (EqualityBucket* bucketPtr : other.lesser)
			bucketPtr->parents.insert(this);

		parents.insert(other.parents.begin(), other.parents.end());
		for (EqualityBucket* parent : other.parents) {
			if (contains(parent->lesserEqual, &other)) parent->lesserEqual.insert(this);
			else if (contains(parent->lesser,      &other)) parent->lesser.insert(this);
			else assert(0); // was a parent so it must have been lesser or lesserEqual
		}
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

	void searchForGreater(std::vector<EqualityBucket*>& acc) {
		for (EqualityBucket* parentPtr : parents) {
			if (contains(parentPtr->lesser, this))
				acc.push_back(parentPtr);

			if (contains(parentPtr->lesserEqual, this)) {
				parentPtr->searchForGreater(acc);
			}
		}
	}

	void searchForLesser(std::vector<EqualityBucket*>& acc) {
		for (EqualityBucket* lesserPtr : lesser)
			acc.push_back(lesserPtr);

		for (EqualityBucket* lesserEqualPtr : lesserEqual)
			lesserEqualPtr->searchForLesser(acc);
	}

	void getRelatedBuckets(std::vector<EqualityBucket*>& acc, bool goDown) {
		BucketPtrSet nextBuckets;
		if (goDown) {
			nextBuckets.insert(lesserEqual.begin(), lesserEqual.end());
			nextBuckets.insert(lesser.begin(), lesser.end());
		} else {
			nextBuckets.insert(parents.begin(), parents.end());
		}

		acc.insert(acc.end(), nextBuckets.begin(), nextBuckets.end());

		for (EqualityBucket* bucket : nextBuckets) {
			bucket->getRelatedBuckets(acc, goDown);
		}		
	}
};

template <typename T>
class RelationsGraph {

    std::vector<std::unique_ptr<EqualityBucket>> buckets;
	std::map<T, EqualityBucket*> mapToBucket;

	std::map<EqualityBucket*, std::set<EqualityBucket*>> nonEqualities;

	// map of pairs (a, b) such that {any of b} = load {any of a}
	std::map<EqualityBucket*, EqualityBucket*> loads;

	std::vector<RelationsGraph> xorRelations;

	bool inGraph(T val) const {
		return contains(mapToBucket, val);
	}

	bool areInGraph(T lt, T rt) const {
		return contains(mapToBucket, lt) && contains(mapToBucket, rt);
	}

	std::vector<T> getEqual(const EqualityBucket* valBucket) const {
		assert(valBucket);

		T val = getAny(valBucket);
		return getEqual(val);
	}

	T getAny(const EqualityBucket* bucket) const {
		assert(bucket);

		for (auto& pair : mapToBucket) {
			if (pair.second == bucket) return pair.first;
		}
		assert(0 && "no value in passed bucket");
	}

	bool hasRelations(EqualityBucket* bucket) const {
		return getEqual(bucket).size() > 1
				|| nonEqualities.find(bucket) != nonEqualities.end()
				|| ! bucket->lesser.empty()
				|| ! bucket->lesserEqual.empty()
				|| ! bucket->parents.empty();
	}

	bool hasRelationsOrLoads(EqualityBucket* bucket) const {
		return hasRelations(bucket)
			|| findByKey(loads, bucket)
			|| findByValue(loads, bucket);
	}
	
public:

	RelationsGraph() = default;
	
	RelationsGraph(const RelationsGraph& other): xorRelations(other.xorRelations) {

		std::map<EqualityBucket*, EqualityBucket*> oldToNewPtr;

		// create new copies of buckets
		for(const std::unique_ptr<EqualityBucket>& bucketUniquePtr : other.buckets) {
			assert(bucketUniquePtr);
			assert(bucketUniquePtr.get());
			
			EqualityBucket* newBucketPtr = new EqualityBucket(*bucketUniquePtr);
			buckets.emplace_back(newBucketPtr);

			oldToNewPtr.emplace(bucketUniquePtr.get(), newBucketPtr);
		}

		// set successors to point to new copies
		for (const std::unique_ptr<EqualityBucket>& bucketUniquePtr : buckets)
			bucketUniquePtr->substitueAll(oldToNewPtr);

		// set map to use new copies
		for (auto& pair : other.mapToBucket)
			mapToBucket.emplace(pair.first, oldToNewPtr.at(pair.second));

		for (auto& pair : other.nonEqualities) {
			auto returnPair = nonEqualities.emplace(oldToNewPtr.at(pair.first), pair.second);
			substitueInSet(oldToNewPtr, returnPair.first->second);
		}

		for (auto& pair : other.loads)
			loads.emplace(oldToNewPtr.at(pair.first), oldToNewPtr.at(pair.second));
		
	}

	friend void swap(RelationsGraph& first, RelationsGraph& second) {
		using std::swap;

		swap(first.buckets, second.buckets);
		swap(first.mapToBucket, second.mapToBucket);
		swap(first.nonEqualities, second.nonEqualities);
		swap(first.loads, second.loads);
		swap(first.xorRelations, second.xorRelations);
	}

	RelationsGraph& operator=(RelationsGraph other) {
		swap(*this, other);

		return *this;
	}

	friend bool operator==(const RelationsGraph& lt, const RelationsGraph& rt) {
		if (lt.nonEqualities != rt.nonEqualities) return false;

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

		for (auto& fst : rtVals) {
            for (auto& snd : rtVals) {
                if ((rt.isEqual(fst, snd) && ! lt.isEqual(fst, snd)) ||
				    (rt.isLesser(fst, snd) && ! lt.isLesser(fst, snd)) ||
					(rt.isLesser(snd, fst) && ! lt.isLesser(snd, fst)) ||
					(rt.isLesserEqual(fst, snd) && ! lt.isLesserEqual(fst, snd)) ||
					(rt.isLesserEqual(snd, fst) && ! lt.isLesserEqual(snd, fst)))
					return false;
            }
        }

		std::set<std::pair<std::vector<T>, std::vector<T>>> ltLoads = lt.getAllLoads();
		std::set<std::pair<std::vector<T>, std::vector<T>>> rtLoads = rt.getAllLoads();

		if (ltLoads != rtLoads) return false;

		return lt.xorRelations == rt.xorRelations;
	}

	friend bool operator!=(const RelationsGraph& lt, const RelationsGraph& rt) {
		return ! (lt == rt);
	}

	void add(T val) {
		if (mapToBucket.find(val) != mapToBucket.end()) return;

		EqualityBucket* newBucketPtr = new EqualityBucket;
		buckets.emplace_back(newBucketPtr);
		mapToBucket.emplace(val, newBucketPtr);
	}

	// DANGER setEqual invalidates all EqualityBucket*
	void setEqual(T lt, T rt) {

		// DANGER defined duplicitly (already in subtreeContains)
		using BucketPtr = EqualityBucket*;
		using BucketPtrSet = std::set<BucketPtr>;
		using Frame = std::tuple<BucketPtr, typename BucketPtrSet::iterator, bool>;

		add(lt);
		add(rt);

		if (isEqual(lt, rt)) return;

		// assert no conflicting relations
		assert(! isNonEqual(lt, rt));
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
				BucketPtr bucket = std::get<0>(frame);
				toMerge.push_back(bucket);
				frames.pop();

				// also unset lesserEqual relation
				if (! frames.empty()) {
					BucketPtr above = std::get<0>(frames.top());
					above->lesserEqual.erase(bucket); bucket->parents.erase(above);
				}
			}

		} else {
			toMerge = { newBucketPtr, oldBucketPtr };
		}

		newBucketPtr = toMerge[0];

		for (auto it = ++toMerge.begin(); it != toMerge.end(); ++it) {

			oldBucketPtr = *it;

			// replace nonEquality info to regard only remaining bucket
			auto newNonEqIt = nonEqualities.find(newBucketPtr);
			for (auto pairIt = nonEqualities.begin(); pairIt != nonEqualities.end(); ++pairIt) {

				if (pairIt->first == oldBucketPtr) {
					if (newNonEqIt != nonEqualities.end()) {
						newNonEqIt->second.insert(pairIt->second.begin(), pairIt->second.end());
					} else {
						nonEqualities.emplace(newBucketPtr, pairIt->second);
					}
					pairIt = nonEqualities.erase(pairIt);
				}

				for (EqualityBucket* nonEqual : pairIt->second) {
					if (nonEqual == oldBucketPtr) {
						pairIt->second.emplace(newBucketPtr);
						pairIt->second.erase(oldBucketPtr);
						break;
					}
				}
			}

			// replace mapToBucket info to regard only remaining bucket
			for (auto& pair : mapToBucket) {
				if (pair.second == oldBucketPtr)
					pair.second = newBucketPtr;
			}

			// replace load info to regard only remaining bucket
			for (auto pairIt = loads.begin(); pairIt != loads.end(); ++pairIt) {
				if (pairIt->first == oldBucketPtr) {
					loads.emplace(newBucketPtr, pairIt->second);
					pairIt = loads.erase(pairIt);
				}

				if (pairIt->second == oldBucketPtr)
					pairIt->second = newBucketPtr;
			}

			// make successors and parents of right belong to left too
			newBucketPtr->merge(*oldBucketPtr);

			// make successors and parents of right forget it
			oldBucketPtr->disconnectAll();

			// remove right
			eraseUniquePtr(buckets, oldBucketPtr);
		}
	}

	void setNonEqual(T lt, T rt) {

		add(lt);
		add(rt);

		if (isNonEqual(lt, rt)) return;

		// assert no conflicting relations
		assert(! isEqual(lt, rt));

		EqualityBucket* ltBucketPtr = mapToBucket.at(lt);
		EqualityBucket* rtBucketPtr = mapToBucket.at(rt);

		// TODO? handle lesserEqual specializing to lesser

		auto foundLt = nonEqualities.find(ltBucketPtr);
		if (foundLt != nonEqualities.end()) foundLt->second.emplace(rtBucketPtr);
		else nonEqualities.emplace(ltBucketPtr, std::set<EqualityBucket*>{rtBucketPtr});

		auto foundRt = nonEqualities.find(rtBucketPtr);
		if (foundRt != nonEqualities.end()) foundRt->second.emplace(ltBucketPtr);
		else nonEqualities.emplace(rtBucketPtr, std::set<EqualityBucket*>{ltBucketPtr});
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
		if (isNonEqual(lt, rt)) {
			setLesser(lt, rt);
			return;
		}

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

	void setLoad(T from, T val) {

		add(val);
		add(from);

		if (isLoad(from, val)) return;

		EqualityBucket* valBucketPtr = mapToBucket.at(val);
		EqualityBucket* fromBucketPtr = mapToBucket.at(from);

		// get set of values that load from equal pointers
		EqualityBucket* valEqualBucketPtr = findByKey(loads, fromBucketPtr);

		// if there is such a set, we just add val to it
		if (valEqualBucketPtr) {
			setEqual(val, getAny(valEqualBucketPtr));
		} else {
			loads.emplace(fromBucketPtr, valBucketPtr);
		}
		// TODO can there be a situation, in which the fact, that i can load
		// same value from different pointer, means that the pointers are equal?
	}

	void unsetAllLoadsByPtr(T from) {
		if (! inGraph(from)) return;

		EqualityBucket* fromBucketPtr = mapToBucket.at(from);
		EqualityBucket* valBucketPtr = findByKey(loads, fromBucketPtr);
		if (! valBucketPtr) return; // from doesn't load anything

		loads.erase(fromBucketPtr);

		if (! hasRelationsOrLoads(valBucketPtr)) {
			T val = getAny(valBucketPtr);
			mapToBucket.erase(val);
			eraseUniquePtr(buckets, valBucketPtr);
		}
		if (! hasRelationsOrLoads(fromBucketPtr)) {
			mapToBucket.erase(from);
			eraseUniquePtr(buckets, fromBucketPtr);
		}
	}

	void unsetAllLoads() {
        loads.clear();
		
		for (auto it = buckets.begin(); it != buckets.end(); ) {
			if (! hasRelations(it->get())) {
				T val = getAny(it->get());
				mapToBucket.erase(val);
				it = buckets.erase(it);
			} else ++it;
		}
    }

	void unsetRelations(T val) {
		EqualityBucket* valBucketPtr = mapToBucket.at(val);

		bool onlyReference = getEqual(valBucketPtr).size() == 1;
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

		nonEqualities.erase(valBucketPtr);
		for (auto& pair : nonEqualities) {
			pair.second.erase(valBucketPtr);
		}
	}

	bool isEqual(T lt, T rt) const {

		if (! areInGraph(lt, rt))
			return false;

		return mapToBucket.at(lt) == mapToBucket.at(rt);
	}

	bool isNonEqual(T lt, T rt) const {

		if (! areInGraph(lt, rt))
			return false;

		const auto& ltEqBucket = mapToBucket.at(lt);
		const auto& rtEqBucket = mapToBucket.at(rt);

		auto found = nonEqualities.find(ltEqBucket);
		if (found == nonEqualities.end()) return false;

		return found->second.find(rtEqBucket) != found->second.end();
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

	bool isLoad(T from, T val) const {
		
		if (! areInGraph(val, from))
			return false;

		EqualityBucket* valBucketPtr = mapToBucket.at(val);
		EqualityBucket* fromBucketPtr = mapToBucket.at(from);

		auto found = loads.find(fromBucketPtr);
		return found != loads.end() && valBucketPtr == found->second;
	}

	bool hasLoad(T from) const {
		if (! inGraph(from)) return false;

		EqualityBucket* fromBucketPtr = mapToBucket.at(from);

		return loads.find(fromBucketPtr) != loads.end(); 
	}

	std::vector<T> getEqual(T val) const {
		std::vector<T> result;
		if (mapToBucket.find(val) == mapToBucket.end()) {
			result.push_back(val);
			return result;
		}
		
		const auto* valBucket = mapToBucket.at(val);

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

	std::vector<T> getSampleLesser(T val) const {
		if (! inGraph(val)) return {};
		EqualityBucket* bucketPtr = mapToBucket.at(val);

		std::vector<EqualityBucket*> acc;
		bucketPtr->searchForLesser(acc);

		std::vector<T> result;
		for (EqualityBucket* bucketPtr : acc) {
			result.push_back(getAny(bucketPtr));
		}
		return result;
	}

	std::vector<T> getSampleGreater(T val) const {
		if (! inGraph(val)) return {};
		EqualityBucket* bucketPtr = mapToBucket.at(val);

		std::vector<EqualityBucket*> acc;
		bucketPtr->searchForGreater(acc);

		std::vector<T> result;
		for (EqualityBucket* bucketPtr : acc) {
			result.push_back(getAny(bucketPtr));
		}
		return result;
	}

	std::vector<T> getAllRelated(T val) const {
		if (! inGraph(val)) return std::vector<T>();

		EqualityBucket* valBucket = mapToBucket.at(val);

		std::vector<T> result = getEqual(valBucket);

		auto found = nonEqualities.find(valBucket);
		if (found != nonEqualities.end()) {
			for (EqualityBucket* nonEqual : found->second) {
				std::vector<T> vals = getEqual(nonEqual);
				result.insert(result.end(), vals.begin(), vals.end());
			}
		}

		std::vector<EqualityBucket*> buckets;
		valBucket->getRelatedBuckets(buckets, true);
		valBucket->getRelatedBuckets(buckets, false);

		for (EqualityBucket* bucket : buckets) {
			std::vector<T> vals = getEqual(bucket);
			result.insert(result.end(), vals.begin(), vals.end());
		}

		return result;
	}

	std::vector<T> getAllValues() const {
		std::vector<T> result;
		for (auto& pair : mapToBucket)
			result.push_back(pair.first);
		return result;
	}

	std::vector<T> getPtrsByVal(T val) {
		if (! inGraph(val)) return std::vector<T>();
		EqualityBucket* valBucketPtr = mapToBucket.at(val);

		EqualityBucket* fromBucketPtr = findByValue(loads, valBucketPtr);
		return fromBucketPtr ? getEqual(fromBucketPtr) : std::vector<T>();
	}

	std::vector<T> getValsByPtr(T from) {
		if (! inGraph(from)) return std::vector<T>();
		EqualityBucket* fromBucketPtr = mapToBucket.at(from);

		EqualityBucket* valBucketPtr = findByKey(loads, fromBucketPtr);
		return valBucketPtr ? getEqual(valBucketPtr) : std::vector<T>();
	}

	std::set<std::pair<std::vector<T>, std::vector<T>>> getAllLoads() const {
		std::set<std::pair<std::vector<T>, std::vector<T>>> result;
		for (const auto& pair : loads) {
			result.emplace(getEqual(pair.first), getEqual(pair.second));
		}
		return result;
	}

	RelationsGraph& newXorRelation() {
		xorRelations.emplace_back();
		return xorRelations.back();
	}

	std::vector<RelationsGraph>& getXorRelations() {
		return xorRelations;
	}

	void addXorRelation(const RelationsGraph& otherGraph) {
		xorRelations.emplace_back(otherGraph);
	}

#ifndef NDEBUG
	std::string strip(std::string str) const {
		std::string result;
		int space_counter = 0;
		for (char c : str) {
			if (c != ' ' || ++space_counter <= 2) {
				result += c;
			} else break;
		}
		return result;
	}

	void printVals(std::ostream& stream, const std::vector<T>& vals) const {
		stream << "{ ";
		for (auto val : vals) {
			stream << strip(debug::getValName(val)) << "; ";
		}
		stream << "}";
	}

	void printInterleaved(std::ostream& stream, const std::vector<T>& v1,
						  std::string sep, const std::vector<T>& v2) const {
		printVals(stream, v1);
		stream << sep;
		printVals(stream, v2);
		if (&stream == &std::cout)
			stream << "\\r";
		else
			stream << std::endl;
	}

	void dump() {
		generalDump(std::cout);
	}

	void ddump() {
		//std::cerr << "debug dumping graph" << std::endl;
		generalDump(std::cerr);
		std::cerr << std::endl;
	}

	void ddump(EqualityBucket* bucket) {
		//std::cerr << "debug dumping bucket" << std::endl;
		dump(std::cerr, bucket);
		//std::cerr << std::endl;
	}

	void ddump(const llvm::Value* val) {
		if (! inGraph(val)) {
			std::cerr << "NIG" << debug::getValName(val) << std::endl << std::endl;
			return;
		}
		std::cerr << debug::getValName(val) << ":" << std::endl;
		dump(std::cerr, mapToBucket.at(val));
		std::cerr << std::endl;
	}

	void dump(std::ostream& stream, EqualityBucket* bucket) {
		const auto& values = getEqual(bucket);

		for (auto ptr : bucket->lesser)
			printInterleaved(stream, getEqual(ptr), " < ", values);

		for (auto ptr : bucket->lesserEqual)
			printInterleaved(stream, getEqual(ptr), " <= ", values);

		auto foundNonEqual = nonEqualities.find(bucket);
		if (foundNonEqual != nonEqualities.end()) {
			for (EqualityBucket* nonEqual : foundNonEqual->second)
				if (nonEqual < bucket)
					printInterleaved(stream, getEqual(nonEqual), " != ", values);
		}

		//EqualityBucket* foundKey = findByValue(loads, bucket);
		//if (foundKey)
		//	printInterleaved(stream, values, " = LOAD ", getEqual(foundKey));

		EqualityBucket* foundValue = findByKey(loads, bucket);
		if (foundValue)
			printInterleaved(stream, getEqual(foundValue), " = LOAD ", values);

		if (bucket->lesser.empty() // values just equal and nothing else
				&& bucket->lesserEqual.empty()
				&& bucket->parents.empty()
				&& foundNonEqual == nonEqualities.end()
				&& ! findByValue(loads, bucket)
				&& ! foundValue) {
			printVals(stream, values);
			stream << std::endl;
		}
	}

    void generalDump(std::ostream& stream) {

		for (const auto& bucketPtr : buckets) {
			dump(stream, bucketPtr.get());
		}

		for (auto& rg : xorRelations) {
			stream << std::endl << "    XOR relations" << std::endl;
			rg.generalDump(stream);
		}

    }
#endif

};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_RELATIONS_MAP_H_

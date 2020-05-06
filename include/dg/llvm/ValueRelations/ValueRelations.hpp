#ifndef _DG_LLVM_RELATIONS_MAP_H_
#define _DG_LLVM_RELATIONS_MAP_H_

#include <set>
#include <map>
#include <queue>
#include <vector>
#include <tuple>
#include <memory>
#include <algorithm>

#include <cassert>

#include <llvm/IR/Value.h>

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

class EqualityBucket;

using BucketPtr = EqualityBucket*;
using BucketPtrSet = std::set<BucketPtr>;

enum class Relation { EQ, NE, LE, LT, GE, GT, LOAD };

#ifndef NDEBUG
void dumpRelation(Relation r) {
	switch(r) {
		case Relation::EQ: std::cerr << "EQ"; break;
		case Relation::NE: std::cerr << "NE"; break;
		case Relation::LE: std::cerr << "LE"; break;
		case Relation::LT: std::cerr << "LT"; break;
		case Relation::GE: std::cerr << "GE"; break;
		case Relation::GT: std::cerr << "GT"; break;
		case Relation::LOAD: std::cerr << "LOAD"; break;
	}
}
#endif

class EqualityBucket {

	using T = const llvm::Value*;

    friend class ValueRelations;

    using BucketPtr = EqualityBucket*;
	using BucketPtrSet = std::set<BucketPtr>;
	
	BucketPtrSet lesserEqual;
	BucketPtrSet lesser;
	BucketPtrSet parents;

	std::vector<T> equalities;

	struct HeapElem {
		EqualityBucket* bucket;
		EqualityBucket* predecessor;
		unsigned distance;
		Relation relation;

		HeapElem() = default;
		HeapElem(EqualityBucket* b, EqualityBucket* p, unsigned d, Relation r)
			: bucket(b), predecessor(p), distance(d), relation(r) {}

		friend bool operator==(const HeapElem& lt, const HeapElem& rt) {
			return lt.distance == rt.distance;
		}

		friend bool operator!=(const HeapElem& lt, const HeapElem& rt) {
			return ! (lt == rt);
		}

		// the lowest HeapElem is the one with the highest distance
		friend bool operator<(const HeapElem& lt, const HeapElem& rt) {
			return lt.distance > rt.distance;
		}

		friend bool operator>=(const HeapElem& lt, const HeapElem& rt) {
			return ! (lt < rt);
		}

		friend bool operator>(const HeapElem& lt, const HeapElem& rt) {
			return rt < lt;
		}

		friend bool operator<=(const HeapElem& lt, const HeapElem& rt) {
			return ! (rt < lt);
		}

		friend void swap(HeapElem& lt, HeapElem& rt) {
			using std::swap;

			swap(lt.bucket, rt.bucket);
			swap(lt.predecessor, rt.predecessor);
			swap(lt.distance, rt.distance);
			swap(lt.relation, rt.relation);
		}
	};

	struct BucketIterator {

		using value_type = HeapElem;
		using iterator_category = std::forward_iterator_tag;
		using difference_type = std::ptrdiff_t;

		std::vector<HeapElem> heap;
		std::map<EqualityBucket*, EqualityBucket*> predecessors;
		std::map<EqualityBucket*, HeapElem> mapToElem;
		unsigned totalNodes;
		bool goDown = false;
		bool toFirstStrict = false;
		
		BucketIterator() = default;
		BucketIterator(EqualityBucket* start, unsigned total, bool down, bool strict, bool begin)
		: totalNodes(total), goDown(down), toFirstStrict(strict) {
			if (! begin) return;
			
			HeapElem elem(start, nullptr, 0, Relation::EQ);
			heap.emplace_back(elem);
			predecessors.emplace(start, nullptr);
		}

		friend bool operator==(const BucketIterator& lt, const BucketIterator& rt) {
			return lt.goDown == rt.goDown
				&& lt.toFirstStrict == rt.toFirstStrict
				&& lt.heap == rt.heap;
		}

		friend bool operator!=(const BucketIterator& lt, const BucketIterator& rt) {
			return ! (lt == rt);
		}

		const value_type& operator*() const { return heap[0]; }
		const value_type* operator->() const { return &heap[0]; }

		value_type operator*() { return heap[0]; }
		value_type* operator->() { return &heap[0]; }

		BucketIterator& operator++() {
			if (heap.empty()) return *this;

			HeapElem elem = heap[0];
			std::pop_heap(heap.begin(), heap.end()); heap.pop_back();

			// the element on top of the heap has to have predecessor set
			// so that predecessor would be valid upon dereferencing the iterator
			// not only after increment
			assert(predecessors.find(elem.bucket) != predecessors.end());

			// use discovered edges only if we do not go only to first strict or non-strictly related
			// bucket was found
			if (! toFirstStrict || (elem.relation != Relation::LT && elem.relation != Relation::GT)) {

				// add new distances to successors
				if (goDown) {

					for (EqualityBucket* lesserBucket : elem.bucket->lesser) {
						HeapElem newElem(lesserBucket, elem.bucket, elem.distance + 1, Relation::LT);
						updateHeap(lesserBucket, newElem);
					}

					for (EqualityBucket* lesserEqualBucket : elem.bucket->lesserEqual) {
						Relation newRelation = elem.relation == Relation::LT ? Relation::LT : Relation::LE;
						HeapElem newElem(lesserEqualBucket, elem.bucket, elem.distance + totalNodes, newRelation);
						updateHeap(lesserEqualBucket, newElem);
					}
				} else {

					for (EqualityBucket* parentBucket : elem.bucket->parents) {
						HeapElem newElem;
						if (contains(parentBucket->lesser, elem.bucket)) {
							newElem = HeapElem(parentBucket, elem.bucket, elem.distance + 1, Relation::GT);
						}
						
						else {
							Relation newRelation = elem.relation == Relation::GT ? Relation::GT : Relation::GE;
							newElem = HeapElem(parentBucket, elem.bucket, elem.distance + totalNodes, newRelation);
						}

						updateHeap(parentBucket, newElem);
					}
				}
			}

			// remove already found buckets from queue so that next top would again be valid
			while (! heap.empty() && predecessors.find(heap[0].bucket) != predecessors.end()) {
				std::pop_heap(heap.begin(), heap.end());
				heap.pop_back();
			}

			predecessors.emplace(heap[0].bucket, heap[0].predecessor);

			return *this;
		}

		void updateHeap(EqualityBucket* bucket, HeapElem& newElem) {
			auto found = mapToElem.find(bucket);
			if (found != mapToElem.end()) {
				HeapElem& original = found->second;
				if (original.distance > newElem.distance) {
					swap(newElem, original);
					std::make_heap(heap.begin(), heap.end());
				}
			} else {
				mapToElem.emplace(bucket, newElem);
				heap.emplace_back(newElem);
				std::push_heap(heap.begin(), heap.end());
			}
		}

		BucketIterator operator++(int) {
			auto preInc = *this;
			++(*this);
			return preInc;
		}

		EqualityBucket* getPredecessor(EqualityBucket* bucket) const {
			assert(bucket);
			auto found = predecessors.find(bucket);
			assert(found != predecessors.end());
			return found->second;
		}
	};

	BucketIterator begin_down(unsigned totalNodes) {
		return BucketIterator(this, totalNodes, true, false, true);
	}

	BucketIterator end_down() {
		return BucketIterator(this, 0, true, false, false);
	}

	BucketIterator begin_up(unsigned totalNodes) {
		return BucketIterator(this, totalNodes, false, false, true);
	}

	BucketIterator end_up() {
		return BucketIterator(this, 0, false, false, false);
	}

	// iterates over bucets up to the first strictly lesser on each path
	BucketIterator begin_strictDown(unsigned totalNodes) {
		return BucketIterator(this, totalNodes, true, true, true);
	}

	BucketIterator end_strictDown() {
		return BucketIterator(this, 0, true, true, false);
	}

	// iterates over buckets up to the first strictly greater on each path
	BucketIterator begin_strictUp(unsigned totalNodes) {
		return BucketIterator(this, totalNodes, false, true, true);
	}

	BucketIterator end_strictUp() {
		return BucketIterator(this, 0, false, true, false);
	}

	std::pair<std::vector<EqualityBucket*>, bool> subtreeContains(
			EqualityBucket* needle,
			unsigned totalNodes,
			bool ignoreLE) {

		for (auto it = begin_down(totalNodes); it != end_down(); ++it) {

			if (it->bucket == needle) {
				if (ignoreLE && it->relation != Relation::LT) break;
				// else we found searched bucket

				std::vector<EqualityBucket*> pathToThis;
				EqualityBucket* current = needle;
				do {
					pathToThis.emplace_back(current);
					current = it.getPredecessor(current);
				} while (current);

				return { pathToThis, true };
			}
		}

		return { std::vector<EqualityBucket*>(), false };
	}

	void mergeConnections(const EqualityBucket& other) {
		// set_union does't work in place
		lesserEqual.insert(other.lesserEqual.begin(), other.lesserEqual.end());
		for (EqualityBucket* bucketPtr : other.lesserEqual)
			bucketPtr->parents.insert(this);

		lesser.insert(other.lesser.begin(), other.lesser.end());
		for (EqualityBucket* bucketPtr : other.lesser)
			bucketPtr->parents.insert(this);

		parents.insert(other.parents.begin(), other.parents.end());
		for (EqualityBucket* parent : other.parents) {
			if (contains(parent->lesserEqual, const_cast<EqualityBucket*>(&other)))
				parent->lesserEqual.insert(this);
			else if (contains(parent->lesser, const_cast<EqualityBucket*>(&other)))
				parent->lesser.insert(this);
			else
				assert(0); // was a parent so it must have been lesser or lesserEqual
		}

		equalities.insert(equalities.end(),
						  other.equalities.begin(), other.equalities.end());
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

	std::vector<EqualityBucket*> getDirectlyRelated(unsigned totalNodes, bool goDown) {
		std::vector<EqualityBucket*> result;

		for (auto it = (goDown ? begin_strictDown(totalNodes) : begin_strictUp(totalNodes));
				  it != (goDown ? end_strictDown() : end_strictUp());
				  ++it) {

			if ((goDown && it->relation == Relation::LT) || (! goDown && it->relation == Relation::GT))
				result.emplace_back(it->bucket);
		}

		return result;
	}

	std::vector<T>& getEqual() {
		return equalities;
	}

	const std::vector<T>& getEqual() const {
		return equalities;
	}

	T getAny() const {
		assert(equalities.size() > 0);
		return equalities[0];
	}

	bool hasAllEqualitiesFrom(const EqualityBucket* other) const {
		for (T val : other->equalities) {
			if (std::find(equalities.begin(), equalities.end(), val) == equalities.end())
				return false;
		}
		return true;
	}
};

class ValueRelations {

	using T = const llvm::Value*;
	using C = const llvm::ConstantInt*;

private:
    std::vector<std::unique_ptr<EqualityBucket>> buckets;
	std::map<T, EqualityBucket*> mapToBucket;
	std::map<unsigned, EqualityBucket*> placeholderBuckets;
	unsigned lastPlaceholderId = 0;

	std::map<EqualityBucket*, std::set<EqualityBucket*>> nonEqualities;

	// map of pairs (a, b) such that {any of b} = load {any of a}
	std::map<EqualityBucket*, EqualityBucket*> loads;

	std::vector<bool> validAreas;

	struct ValueIterator {
		using value_type = std::pair<T, Relation>;

		enum Type { UP, DOWN, ALL, NONE };

		unsigned totalNodes;
		Type type = Type::NONE;
		bool strictOnly = false;
		EqualityBucket* start;
		EqualityBucket::BucketIterator it;
		unsigned index;
		
		ValueIterator(EqualityBucket* st, unsigned total, bool s, Type t, bool begin)
		: totalNodes(total), type(t), strictOnly(s), start(st), index(0) {
			if (begin) {
				if (type == Type::DOWN || type == Type::ALL)
					it = start->begin_down(totalNodes);
				if (type == Type::UP)
					it = start->begin_up(totalNodes);
				toNextValidValue();
			} else {
				if (type == Type::DOWN)
					it = start->end_down();
				if (type == Type::UP || type == Type::ALL)
					it = start->end_up();
			}
		}

		friend bool operator==(const ValueIterator& lt, const ValueIterator& rt) {
			return lt.type == rt.type
			    && lt.strictOnly == rt.strictOnly
				&& lt.it == rt.it;
		}

		friend bool operator!=(const ValueIterator& lt, const ValueIterator& rt) {
			return ! (lt == rt);
		}

		value_type operator*() const {
			if (strictOnly && it->relation != Relation::LT && it->relation != Relation::GT)
				assert(0 && "iterator always stops only at strict if demanded");
			return { it->bucket->getEqual()[index], it->relation };
		}

		// make iterator always point at valid value or end
		ValueIterator& operator++() {
			if (it == start->end_up() || it == start->end_down())
				return *this;
			// we dont have to check if type == ALL because code later
			// handles the jump between iterators

			if (index + 1 < it->bucket->equalities.size()) {
				++index;
				return *this;
			}

			// else we need to move on to the next bucket
			++it;
			index = 0;
			toNextValidValue();

			if (it == start->end_down() && type == Type::ALL) {
				it = ++(start->begin_up(totalNodes)); // ++ so that we would not pass equal again
				toNextValidValue();
			}

			return *this;
		}

		ValueIterator operator++(int) {
			auto preInc = *this;
			++(*this);
			return preInc;
		}
		
	private:
		void toNextValidValue() {
			while (it != start->end_down()
				&& it != start->end_up()
				&& (it->bucket->getEqual().empty()
					|| (strictOnly && it->relation != Relation::LT && it->relation != Relation::GT)))
				++it;
		}
	};

	bool inGraph(T val) const {
		return contains(mapToBucket, val);
	}

	bool hasComparativeRelations(EqualityBucket* bucket) const {
		return bucket->getEqual().size() > 1
			|| nonEqualities.find(bucket) != nonEqualities.end()
			|| ++bucket->begin_down(buckets.size()) != bucket->end_down()
			|| ++bucket->begin_up(buckets.size())   != bucket->end_up();
	}

	bool hasComparativeRelationsOrLoads(EqualityBucket* bucket) const {
		return hasComparativeRelations(bucket)
			|| findByKey(loads, bucket)
			|| findByValue(loads, bucket);
	}

	EqualityBucket* getCorrespondingBucket(const ValueRelations& other, EqualityBucket* otherBucket) const {
		if (! otherBucket->getEqual().empty()) {
			auto found = mapToBucket.find(otherBucket->getEqual()[0]);
			if (found != mapToBucket.end())
				return found->second;
			return nullptr;
		}

		// else this is placeholder bucket
		EqualityBucket* otherFromBucket = findByValue(other.loads, otherBucket);
		assert(otherFromBucket);
		assert(! otherFromBucket->getEqual().empty());
		// if bucket is empty, it surely has a nonempty load bucket,
		// they aren't created under different circumstances

		T from = otherFromBucket->getEqual()[0];
		if (hasLoad(from))
			return loads.at(mapToBucket.at(from));
		return nullptr;
	}

	EqualityBucket* getCorrespondingBucketOrNew(const ValueRelations& other, EqualityBucket* otherBucket) {
		if (! otherBucket->getEqual().empty()) {
			const auto& equalities = otherBucket->getEqual();

			for (T val : equalities) {
				auto found = mapToBucket.find(val);
				if (found != mapToBucket.end()) return found->second;
			}
			add(equalities[0]);
			return mapToBucket.find(equalities[0])->second;
		}

		// else this is placeholder bucket
		EqualityBucket* otherFromBucket = findByValue(other.loads, otherBucket);
		assert(otherFromBucket);
		assert(! otherFromBucket->getEqual().empty());
		// if bucket is empty, it surely has a nonempty load bucket,
		// they aren't created under different circumstances

		for (T from : otherFromBucket->getEqual()) {
			if (hasLoad(from)) return loads.at(mapToBucket.at(from));
		}
		unsigned placeholder = newPlaceholderBucket();
		setLoad(otherFromBucket->getEqual()[0], placeholder);
		return placeholderBuckets.at(placeholder);
	}

	std::vector<std::tuple<EqualityBucket*, EqualityBucket*, Relation>>
			getExtraRelationsIn(const ValueRelations& other) const {
		std::vector<std::tuple<EqualityBucket*, EqualityBucket*, Relation>> result;

		for (auto& bucketUniquePtr : other.buckets) {

			EqualityBucket* otherBucket = bucketUniquePtr.get();
			EqualityBucket* thisBucket = getCorrespondingBucket(other, otherBucket);

			if (! thisBucket || ! thisBucket->hasAllEqualitiesFrom(otherBucket))
				result.emplace_back(otherBucket, otherBucket, Relation::EQ);
			
			// find unrelated comparative buckets
			for (auto it = otherBucket->begin_down(buckets.size()); it != otherBucket->end_down(); ++it) {

				if (it->relation == Relation::EQ) continue; // already handled prior to loop

				EqualityBucket* otherRelatedBucket = it->bucket;
				EqualityBucket* thisRelatedBucket = getCorrespondingBucket(other, otherRelatedBucket);

				if (! thisBucket
				 || ! thisRelatedBucket
				 || (it->relation == Relation::LT && ! isLesser(thisRelatedBucket, thisBucket))
				 || (it->relation == Relation::LE && ! isLesserEqual(thisRelatedBucket, thisBucket)))
					result.emplace_back(otherRelatedBucket, otherBucket, it->relation);
			}

			// find urelated non-equal buckets
			auto foundNE = other.nonEqualities.find(otherBucket);
			if (foundNE != other.nonEqualities.end()) {
				for (EqualityBucket* otherRelatedBucket : foundNE->second) {
					EqualityBucket* thisRelatedBucket = getCorrespondingBucket(other, otherRelatedBucket);

					if (! thisBucket
					 || ! thisRelatedBucket
					 || ! isNonEqual(thisRelatedBucket, thisBucket))
						result.emplace_back(otherRelatedBucket, otherBucket, Relation::NE);
				}
			}

			// found unrelated load buckets
			auto foundLoad = other.loads.find(otherBucket);
			if (foundLoad != other.loads.end()) {
				EqualityBucket* otherRelatedBucket = foundLoad->second;
				EqualityBucket* thisRelatedBucket = getCorrespondingBucket(other, otherRelatedBucket);

				if (! thisBucket
				 || ! thisRelatedBucket
				 || ! isLoad(thisBucket, thisRelatedBucket))
				 	result.emplace_back(otherRelatedBucket, otherBucket, Relation::LOAD);
			}
		}

		return result;
	}

	std::vector<BucketPtr> getBucketsToMerge(BucketPtr newBucketPtr, BucketPtr oldBucketPtr) const {

		if (! isLesserEqual(newBucketPtr, oldBucketPtr) && ! isLesserEqual(oldBucketPtr, newBucketPtr))
			return { newBucketPtr, oldBucketPtr };

		// else handle lesserEqual specializing to equal
		std::vector<EqualityBucket*> toMerge;
		if (isLesserEqual(newBucketPtr, oldBucketPtr)) {
			toMerge = oldBucketPtr->subtreeContains(newBucketPtr, buckets.size(), false).first;
		} else {
			toMerge = newBucketPtr->subtreeContains(oldBucketPtr, buckets.size(), false).first;
		}

		// unset unnecessary lesserEqual relations
		for (auto it = ++toMerge.begin(); it != toMerge.end(); ++it) {
			EqualityBucket* below = *std::prev(it);
			EqualityBucket* above = *it;

			above->lesserEqual.erase(below);
			below->parents.erase(above);
		}

		return toMerge;
	}

	void setEqual(EqualityBucket* newBucketPtr, EqualityBucket* oldBucketPtr) {

		if (isEqual(newBucketPtr, oldBucketPtr)) return;

		assert(! hasConflictingRelation(newBucketPtr, oldBucketPtr, Relation::EQ));

		std::vector<BucketPtr> toMerge = getBucketsToMerge(newBucketPtr, oldBucketPtr);

		newBucketPtr = toMerge[0];

		for (auto it = ++toMerge.begin(); it != toMerge.end(); ++it) {

			oldBucketPtr = *it;

			// replace nonEquality info to regard only remaining bucket
			auto newNEIt = nonEqualities.find(newBucketPtr);
			auto oldNEIt = nonEqualities.find(oldBucketPtr);

			if (oldNEIt != nonEqualities.end()) {
				for (EqualityBucket* nonEqual : oldNEIt->second) {
					nonEqualities.at(nonEqual).emplace(newBucketPtr);
					nonEqualities.at(nonEqual).erase(oldBucketPtr);
				}

				oldNEIt->second.erase(newBucketPtr);
				if (newNEIt != nonEqualities.end())
					newNEIt->second.insert(oldNEIt->second.begin(), oldNEIt->second.end());
				else
					nonEqualities.emplace(newBucketPtr, oldNEIt->second);

				nonEqualities.erase(oldBucketPtr);
			}

			// replace mapToBucket info to regard only remaining bucket
			for (auto& pair : mapToBucket) {
				if (pair.second == oldBucketPtr)
					pair.second = newBucketPtr;
			}

			// replace load info to regard only remaining bucket
			for (auto pairIt = loads.begin(); pairIt != loads.end(); ++pairIt) {
				if (pairIt->first == oldBucketPtr) {
					loads.emplace(newBucketPtr,
								  pairIt->second == oldBucketPtr ? newBucketPtr : pairIt->second); // in case x = load x
					pairIt = loads.erase(pairIt);
				}

				if (pairIt->second == oldBucketPtr)
					pairIt->second = newBucketPtr;
			}

			// make successors and parents of right belong to left too
			newBucketPtr->mergeConnections(*oldBucketPtr);

			// make successors and parents of right forget it
			oldBucketPtr->disconnectAll();

			// replace placeholder info to disregard removed bucket
			for (auto pair : placeholderBuckets) {
				if (pair.second == oldBucketPtr) {
					placeholderBuckets.erase(pair.first);
					break;
				}
			}

			// remove right
			eraseUniquePtr(buckets, oldBucketPtr);
		}
	}

	void setNonEqual(EqualityBucket* ltBucketPtr, EqualityBucket* rtBucketPtr) {
		
		if (isNonEqual(ltBucketPtr, rtBucketPtr)) return;

		assert(! hasConflictingRelation(ltBucketPtr, rtBucketPtr, Relation::NE));

		// TODO? handle lesserEqual specializing to lesser

		auto foundLt = nonEqualities.find(ltBucketPtr);
		if (foundLt != nonEqualities.end()) foundLt->second.emplace(rtBucketPtr);
		else nonEqualities.emplace(ltBucketPtr, std::set<EqualityBucket*>{rtBucketPtr});

		auto foundRt = nonEqualities.find(rtBucketPtr);
		if (foundRt != nonEqualities.end()) foundRt->second.emplace(ltBucketPtr);
		else nonEqualities.emplace(rtBucketPtr, std::set<EqualityBucket*>{ltBucketPtr});
	}

	void setLesser(EqualityBucket* ltBucketPtr, EqualityBucket* rtBucketPtr) {
		if (isLesser(ltBucketPtr, rtBucketPtr)) return;

		assert(! hasConflictingRelation(ltBucketPtr, rtBucketPtr, Relation::LT));

		if (isLesserEqual(ltBucketPtr, rtBucketPtr)) {
			if (contains<EqualityBucket*>(rtBucketPtr->lesserEqual, ltBucketPtr))
				rtBucketPtr->lesserEqual.erase(ltBucketPtr);
			//else
			//	assert(0); // more buckets in between, can't decide this
		}

		rtBucketPtr->lesser.insert(ltBucketPtr);
		ltBucketPtr->parents.insert(rtBucketPtr);
	}

	void setLesserEqual(EqualityBucket* ltBucketPtr, EqualityBucket* rtBucketPtr) {
		if (isLesserEqual(ltBucketPtr, rtBucketPtr)) return;
		if (isNonEqual(ltBucketPtr, rtBucketPtr))
			return setLesser(ltBucketPtr, rtBucketPtr);

		assert(! hasConflictingRelation(ltBucketPtr, rtBucketPtr, Relation::LE));

		// infer values being equal
		if (isLesserEqual(rtBucketPtr, ltBucketPtr))
			return setEqual(ltBucketPtr, rtBucketPtr);

		rtBucketPtr->lesserEqual.insert(ltBucketPtr);
		ltBucketPtr->parents.insert(rtBucketPtr);
	}

	void setLoad(EqualityBucket* fromBucketPtr, EqualityBucket* valBucketPtr) {
		if (isLoad(fromBucketPtr, valBucketPtr)) return;

		// get set of values that load from equal pointers
		EqualityBucket* valEqualBucketPtr = findByKey(loads, fromBucketPtr);

		// if there is such a set, we just add val to it
		if (valEqualBucketPtr) {
			setEqual(valBucketPtr, valEqualBucketPtr);
		} else {
			loads.emplace(fromBucketPtr, valBucketPtr);
		}
	}

	bool isEqual(EqualityBucket* ltEqBucket, EqualityBucket* rtEqBucket) const {

		return ltEqBucket == rtEqBucket;
	}

	bool isNonEqual(EqualityBucket* ltEqBucket, EqualityBucket* rtEqBucket) const {
		auto found = nonEqualities.find(ltEqBucket);
		if (found == nonEqualities.end()) return false;

		return found->second.find(rtEqBucket) != found->second.end();
	}

	C getEqualConstant(EqualityBucket* ltEqBucket) const {
		C ltConst = nullptr;
		for (const llvm::Value* val : ltEqBucket->getEqual()) {
			if (auto constant = llvm::dyn_cast<llvm::ConstantInt>(val))
				ltConst = constant;
		}
		
		return ltConst;
	}

	bool isLesser(EqualityBucket* ltEqBucket, EqualityBucket* rtEqBucket) const {
		if (rtEqBucket->subtreeContains(ltEqBucket, buckets.size(), true).second) return true;

		C ltConst = getEqualConstant(ltEqBucket);
		C rtBound = getLesserEqualBound(rtEqBucket);

		return ltConst && rtBound && ltConst->getValue().slt(rtBound->getValue());
	}

	bool isLesserEqual(EqualityBucket* ltEqBucket, EqualityBucket* rtEqBucket) const {
		if (rtEqBucket->subtreeContains(ltEqBucket, buckets.size(), false).second) return true;

		C ltConst = getEqualConstant(ltEqBucket);
		C rtBound = getLesserEqualBound(rtEqBucket);

		return ltConst && rtBound && ltConst->getValue().sle(rtBound->getValue());
	}

	// in case of LOAD, rt is the from and lt is val
	bool hasConflictingRelation(
			EqualityBucket* ltBucketPtr,
			EqualityBucket* rtBucketPtr,
			Relation relation) const {
		switch (relation) {
			case Relation::EQ:
				return isNonEqual(ltBucketPtr, rtBucketPtr)
					|| isLesser(ltBucketPtr, rtBucketPtr)
					|| isLesser(rtBucketPtr, ltBucketPtr);

			case Relation::NE:
				return isEqual(ltBucketPtr, rtBucketPtr);

			case Relation::LT:
				return isLesserEqual(rtBucketPtr, ltBucketPtr);

			case Relation::LE:
				return isLesser(rtBucketPtr, ltBucketPtr);

			case Relation::GT:
				return hasConflictingRelation(rtBucketPtr, ltBucketPtr, Relation::LT);

			case Relation::GE:
				return hasConflictingRelation(rtBucketPtr, ltBucketPtr, Relation::LE);

			case Relation::LOAD:
				return hasLoad(rtBucketPtr)
					&& hasConflictingRelation(ltBucketPtr, loads.at(rtBucketPtr), Relation::EQ);
		}
		assert(0 && "unreachable");
	}

	bool isLoad(EqualityBucket* fromBucketPtr, EqualityBucket* valBucketPtr) const {
		auto found = loads.find(fromBucketPtr);
		return found != loads.end() && valBucketPtr == found->second;
	}

	bool hasLoad(EqualityBucket* fromBucketPtr) const {
		return loads.find(fromBucketPtr) != loads.end();
	}

	void eraseBucketIfUnrelated(EqualityBucket* bucket) {
		if (hasComparativeRelationsOrLoads(bucket)) return;

		for (auto& pair : mapToBucket) {
			if (pair.second == bucket) {
				mapToBucket.erase(pair.first);
				break;
			}
		}

		eraseUniquePtr(buckets, bucket);
	}

	void unsetComparativeRelations(EqualityBucket* valBucketPtr) {
		// save related buckets to check later
		BucketPtrSet allRelated;
		allRelated.insert(valBucketPtr->parents.begin(), valBucketPtr->parents.end());
		allRelated.insert(valBucketPtr->lesser.begin(), valBucketPtr->lesser.end());
		allRelated.insert(valBucketPtr->lesserEqual.begin(), valBucketPtr->lesserEqual.end());

		auto found = nonEqualities.find(valBucketPtr);
		if (found != nonEqualities.end())
			allRelated.insert(found->second.begin(), found->second.end());

		// overconnect parents to children
		for (EqualityBucket* parent : valBucketPtr->parents) {

			for (EqualityBucket* lesser : valBucketPtr->lesser) {
				parent->lesser.emplace(lesser);
				lesser->parents.emplace(parent);
			}

			for (EqualityBucket* lesserEqual : valBucketPtr->lesserEqual) {

				if (parent->lesserEqual.find(valBucketPtr) != parent->lesserEqual.end())
					parent->lesserEqual.emplace(lesserEqual);
				else
					parent->lesser.emplace(lesserEqual);
				lesserEqual->parents.emplace(parent);
			}
		}

		nonEqualities.erase(valBucketPtr);
		for (auto& pair : nonEqualities) {
			pair.second.erase(valBucketPtr);
		}

		// it severes all ties with the rest of the graph
		valBucketPtr->disconnectAll();

		// remove buckets that lost their only relation
		for (EqualityBucket* bucket : allRelated)
			eraseBucketIfUnrelated(bucket);
	}

	C getLesserEqualBound(EqualityBucket* bucket) const {

		C highest = nullptr;
		for (auto it = bucket->begin_down(buckets.size()); it != bucket->end_down(); ++it) {
			for (const llvm::Value* val : it->bucket->getEqual()) {

				if (auto constant = llvm::dyn_cast<llvm::ConstantInt>(val)) {
					if (! highest || constant->getValue().sgt(highest->getValue()))
						highest = constant;
				}
			}
		}
		return highest;
	}

	std::vector<T> getDirectlyRelated(T val, bool goDown) const {
		if (! inGraph(val)) return {};
		EqualityBucket* bucketPtr = mapToBucket.at(val);

		std::vector<EqualityBucket*> relatedBuckets = bucketPtr->getDirectlyRelated(buckets.size(), goDown);

		std::vector<T> result;
		for (EqualityBucket* bucketPtr : relatedBuckets) {
			if (! bucketPtr->getEqual().empty())
				result.emplace_back(bucketPtr->getAny());
		}
		return result;
	}
	
public:

	ValueRelations() = default;
	
	ValueRelations(const ValueRelations& other):
		lastPlaceholderId(other.lastPlaceholderId) {

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

		// set placeholder buckets to use new copies
		for (auto& pair : other.placeholderBuckets)
			placeholderBuckets.emplace(pair.first, oldToNewPtr.at(pair.second));

		// set nonEqualities to use new copies
		for (auto& pair : other.nonEqualities) {
			auto returnPair = nonEqualities.emplace(oldToNewPtr.at(pair.first), pair.second);
			substitueInSet(oldToNewPtr, returnPair.first->second);
		}

		// set loads to use new copies
		for (auto& pair : other.loads)
			loads.emplace(oldToNewPtr.at(pair.first), oldToNewPtr.at(pair.second));
		
	}

	friend void swap(ValueRelations& first, ValueRelations& second) {
		using std::swap;

		swap(first.buckets, second.buckets);
		swap(first.mapToBucket, second.mapToBucket);
		swap(first.placeholderBuckets, second.placeholderBuckets);
		swap(first.lastPlaceholderId, second.lastPlaceholderId);
		swap(first.nonEqualities, second.nonEqualities);
		swap(first.loads, second.loads);
	}

	ValueRelations& operator=(ValueRelations other) {
		swap(*this, other);

		return *this;
	}

	bool hasAllRelationsFrom(const ValueRelations& other) const {
		return getExtraRelationsIn(other).empty();
	}

	bool merge(const ValueRelations& other, bool relationsOnly = false) {
		ValueRelations original = *this;

		std::vector<std::tuple<EqualityBucket*, EqualityBucket*, Relation>> missingRelations;
		missingRelations = getExtraRelationsIn(other);

		EqualityBucket* otherBucket;
		EqualityBucket* otherRelatedBucket;
		Relation relation;
		for (auto& tuple : missingRelations) {
			std::tie(otherRelatedBucket, otherBucket, relation) = tuple;

			EqualityBucket* thisBucket = getCorrespondingBucketOrNew(other, otherBucket);
			EqualityBucket* thisRelatedBucket = getCorrespondingBucketOrNew(other, otherRelatedBucket);
			assert(thisBucket && thisRelatedBucket);

			if (hasConflictingRelation(thisRelatedBucket, thisBucket, relation)) {
				swap(*this, original);
				return false;
			}

			switch (relation) {
				case Relation::EQ:
					for (T val : otherRelatedBucket->getEqual()) {
						if (hasConflictingRelation(val, otherRelatedBucket->getEqual()[0], Relation::EQ)) {
							swap(*this, original);
							return false;
						}
						add(val);
						setEqual(thisRelatedBucket, mapToBucket.at(val));
					}
					break;
				case Relation::NE: setNonEqual(thisRelatedBucket, thisBucket); break;
				case Relation::LT: setLesser(thisRelatedBucket, thisBucket); break;
				case Relation::LE: setLesserEqual(thisRelatedBucket, thisBucket); break;
				case Relation::LOAD: if (! relationsOnly) setLoad(thisBucket, thisRelatedBucket); break;
				default: assert(0 && "GE and GT cannot occurr");
			}
		}

		return true;
	}

	void add(T val) {
		if (mapToBucket.find(val) != mapToBucket.end()) return;

		EqualityBucket* newBucketPtr = new EqualityBucket;
		buckets.emplace_back(newBucketPtr);
		mapToBucket.emplace(val, newBucketPtr);
		newBucketPtr->getEqual().push_back(val);
	}

	// DANGER setEqual invalidates all EqualityBucket*
	void setEqual(T lt, T rt) {
		add(lt);
		add(rt);
		setEqual(mapToBucket.at(lt), mapToBucket.at(rt));
	}

	void setEqual(T lt, unsigned rt) {
		add(lt);
		setEqual(mapToBucket.at(lt), placeholderBuckets.at(rt));
	}

	void setEqual(unsigned lt, T rt) {
		add(rt);
		setEqual(rt, lt);
	}

	void setNonEqual(T lt, T rt) {
		add(lt);
		add(rt);
		setNonEqual(mapToBucket.at(lt), mapToBucket.at(rt));
	}

	void setNonEqual(T lt, unsigned rt) {
		add(lt);
		setNonEqual(mapToBucket.at(lt), placeholderBuckets.at(rt));
	}

	void setNonEqual(unsigned lt, T rt) {
		add(rt);
		setNonEqual(placeholderBuckets.at(lt), mapToBucket.at(rt));
	}

	void setLesser(T lt, T rt) {
		add(lt);
		add(rt);
		setLesser(mapToBucket.at(lt), mapToBucket.at(rt));
	}

	void setLesser(T lt, unsigned rt) {
		add(lt);
		setLesser(mapToBucket.at(lt), placeholderBuckets.at(rt));
	}

	void setLesser(unsigned lt, T rt) {
		add(rt);
		setLesser(placeholderBuckets.at(lt), mapToBucket.at(rt));
	}

	void setLesserEqual(T lt, T rt) {
		add(lt);
		add(rt);
		setLesserEqual(mapToBucket.at(lt), mapToBucket.at(rt));
	}

	void setLesserEqual(T lt, unsigned rt) {
		add(lt);
		setLesserEqual(mapToBucket.at(lt), placeholderBuckets.at(rt));
	}

	void setLesserEqual(unsigned lt, T rt) {
		add(rt);
		setLesserEqual(placeholderBuckets.at(lt), mapToBucket.at(rt));
	}

	void setLoad(T from, T val) {
		add(val);
		add(from);
		setLoad(mapToBucket.at(from), mapToBucket.at(val));
	}

	void setLoad(T from, unsigned val) {
		add(from);
		setLoad(mapToBucket.at(from), placeholderBuckets.at(val));
	}

	void unsetAllLoadsByPtr(T from) {
		if (! inGraph(from)) return;

		EqualityBucket* fromBucketPtr = mapToBucket.at(from);
		EqualityBucket* valBucketPtr = findByKey(loads, fromBucketPtr);
		if (! valBucketPtr) return; // from doesn't load anything

		loads.erase(fromBucketPtr);

		for (auto& pair : placeholderBuckets) {
			if (pair.second == valBucketPtr) {
				unsetComparativeRelations(valBucketPtr);
				placeholderBuckets.erase(pair.first);
				break;
			}
		}

		if (! hasComparativeRelationsOrLoads(valBucketPtr)) {
			if (! valBucketPtr->getEqual().empty()) {
				T val = valBucketPtr->getAny();
				mapToBucket.erase(val);
			}
			eraseUniquePtr(buckets, valBucketPtr);
		}
		if (! hasComparativeRelationsOrLoads(fromBucketPtr)) {
			mapToBucket.erase(from);
			eraseUniquePtr(buckets, fromBucketPtr);
		}
	}

	void unsetAllLoads() {
        loads.clear();
		
		for (auto it = buckets.begin(); it != buckets.end(); ) {
			if (! hasComparativeRelations(it->get())) {
				if (! (*it)->getEqual().empty())
					mapToBucket.erase((*it)->getAny());

				it = buckets.erase(it);
			} else
				++it;
		}
    }

	void unsetComparativeRelations(T val) {
		if (! inGraph(val)) return;

		EqualityBucket* valBucketPtr = mapToBucket.at(val);
		bool onlyReference = valBucketPtr->getEqual().size() == 1;
		if (! onlyReference) {
			// val moves to its own equality bucket
			mapToBucket.erase(val);
			add(val);
		} else
			unsetComparativeRelations(valBucketPtr);
	}

	bool isEqual(T lt, T rt) const {

		if (! inGraph(lt) || ! inGraph(rt))
			return false;

		return isEqual(mapToBucket.at(lt), mapToBucket.at(rt));
	}

	bool isNonEqual(T lt, T rt) const {

		if (! inGraph(lt) || ! inGraph(rt))
			return false;

		return isNonEqual(mapToBucket.at(lt), mapToBucket.at(rt));
	}

	bool isLesser(T lt, T rt) const {

		if (! inGraph(rt)) return false;

		if (inGraph(lt)) {
			const auto& rtEqBucket = mapToBucket.at(rt);
			if (isLesser(mapToBucket.at(lt), rtEqBucket))
				return true;
		}
		
		if (auto constLt = llvm::dyn_cast<llvm::ConstantInt>(lt)) {
			C constBound = getLesserEqualBound(rt);
			if (constBound && constLt->getValue().slt(constBound->getValue()))
				return true;
		}

		return false;
	}

	bool isLesserEqual(T lt, T rt) const {

		if (! inGraph(rt)) return false;

		if (inGraph(lt)) {
			if (isLesserEqual(mapToBucket.at(lt), mapToBucket.at(rt)))
				return true;
		}
		
		if (auto constLt = llvm::dyn_cast<llvm::ConstantInt>(lt)) {
			C constBound = getLesserEqualBound(rt);
			if (constBound && constLt->getValue().sle(constBound->getValue()))
				return true;
		}

		return false;
	}

	bool hasConflictingRelation(T lt, T rt, Relation relation) const {
		switch (relation) {
			case Relation::EQ:
				return isNonEqual(lt, rt)
					|| isLesser(lt, rt)
					|| isLesser(rt, lt);

			case Relation::NE:
				return isEqual(lt, rt);

			case Relation::LT:
				return isLesserEqual(rt, lt);

			case Relation::LE:
				return isLesser(rt, lt);

			case Relation::GT:
				return hasConflictingRelation(rt, lt, Relation::LT);

			case Relation::GE:
				return hasConflictingRelation(rt, lt, Relation::LE);

			case Relation::LOAD:
				return hasLoad(rt) && inGraph(lt)
					&& hasConflictingRelation(mapToBucket.at(lt), loads.at(mapToBucket.at(rt)), Relation::EQ);
		}
		assert(0 && "unreachable");
	}

	bool isLoad(T from, T val) const {
		
		if (! inGraph(from) || ! inGraph(val))
			return false;
	
		return isLoad(mapToBucket.at(from), mapToBucket.at(val));
	}

	bool hasLoad(T from) const {
		if (! inGraph(from)) return false;

		return hasLoad(mapToBucket.at(from));
	}

	std::vector<T> getEqual(T val) const {
		std::vector<T> result;
		if (mapToBucket.find(val) == mapToBucket.end()) {
			result.push_back(val);
			return result;
		}
		
		const auto* valBucket = mapToBucket.at(val);
		return valBucket->getEqual();
	}

	ValueIterator begin_lesser(T val) const {
		return ValueIterator(mapToBucket.at(val), buckets.size(), true, ValueIterator::Type::DOWN, true);
	}

	ValueIterator end_lesser(T val) const {
		return ValueIterator(mapToBucket.at(val), buckets.size(), true, ValueIterator::Type::DOWN, false);
	}

	ValueIterator begin_lesserEqual(T val) const {
		return ValueIterator(mapToBucket.at(val), buckets.size(), false, ValueIterator::Type::DOWN, true);
	}

	ValueIterator end_lesserEqual(T val) const {
		return ValueIterator(mapToBucket.at(val), buckets.size(), false, ValueIterator::Type::DOWN, false);
	}

	ValueIterator begin_greater(T val) const {
		return ValueIterator(mapToBucket.at(val), buckets.size(), true, ValueIterator::Type::UP, true);
	}

	ValueIterator end_greater(T val) const {
		return ValueIterator(mapToBucket.at(val), buckets.size(), true, ValueIterator::Type::UP, false);
	}

	ValueIterator begin_greaterEqual(T val) const {
		return ValueIterator(mapToBucket.at(val), buckets.size(), false, ValueIterator::Type::UP, true);
	}

	ValueIterator end_greaterEqual(T val) const {
		return ValueIterator(mapToBucket.at(val), buckets.size(), false, ValueIterator::Type::UP, false);
	}

	ValueIterator begin_all(T val) const {
		// TODO add non-equal values
		return ValueIterator(mapToBucket.at(val), buckets.size(), false, ValueIterator::Type::ALL, true);
	}

	ValueIterator end_all(T val) const {
		return ValueIterator(mapToBucket.at(val), buckets.size(), false, ValueIterator::Type::ALL, false);
	}

	std::vector<T> getDirectlyLesser(T val) const {
		return getDirectlyRelated(val, true);
	}

	std::vector<T> getDirectlyGreater(T val) const {
		return getDirectlyRelated(val, false);
	}

	std::vector<T> getAllRelated(T val) const {
		std::vector<T> result;
		for (auto it = begin_all(val); it != end_all(val); ++it) {
			result.push_back((*it).first);
		}
		return result;
	}

	C getLesserEqualBound(T val) const {

		if (! inGraph(val)) return nullptr;
		return getLesserEqualBound(mapToBucket.at(val));
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
		return fromBucketPtr ? fromBucketPtr->getEqual() : std::vector<T>();
	}

	const std::vector<T> getValsByPtr(T from) const {
		if (! inGraph(from)) return std::vector<T>();
		EqualityBucket* fromBucketPtr = mapToBucket.at(from);

		EqualityBucket* valBucketPtr = findByKey(loads, fromBucketPtr);
		return valBucketPtr ? valBucketPtr->getEqual() : std::vector<T>();
	}

	std::set<std::pair<std::vector<T>, std::vector<T>>> getAllLoads() const {
		std::set<std::pair<std::vector<T>, std::vector<T>>> result;
		for (const auto& pair : loads) {
			result.emplace(pair.first->getEqual(), pair.second->getEqual());
		}
		return result;
	}

	const std::vector<bool>& getValidAreas() const {
		return validAreas;
	}

	std::vector<bool>& getValidAreas() {
		return validAreas;
	}

	bool hasComparativeRelations(unsigned placeholder) {
		if (placeholderBuckets.find(placeholder) == placeholderBuckets.end())
			return false;
		
		return hasComparativeRelations(placeholderBuckets.at(placeholder));
	}

	unsigned newPlaceholderBucket() {
		EqualityBucket* bucket = new EqualityBucket;
		buckets.emplace_back(bucket);
		placeholderBuckets.emplace(++lastPlaceholderId, bucket);
		return lastPlaceholderId;
	}

	void erasePlaceholderBucket(unsigned id) {
		// DANGER erases bucket for good, not just
		// the mention in placeholderBuckets
		EqualityBucket* bucket = placeholderBuckets.at(id);
		
		eraseUniquePtr(buckets, bucket);
		placeholderBuckets.erase(id);
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

	void printVals(std::ostream& stream, const EqualityBucket* bucket) const {
		stream << "{ ";
		stream.flush();

		for (auto pair : placeholderBuckets) {
			if (pair.second == bucket) stream << "placeholder " << pair.first << " ";
		}

		for (auto val : bucket->getEqual()) {
			stream << strip(debug::getValName(val)) << "; ";
		}

		stream << "}";
	}

	void printInterleaved(std::ostream& stream, const EqualityBucket* e1,
						  std::string sep, const EqualityBucket* e2) const {
		printVals(stream, e1);
		stream << sep;
		printVals(stream, e2);
		if (&stream == &std::cout)
			stream << "\\r";
		else
			stream << std::endl;
	}

	void dump() {
		generalDump(std::cout);
	}

	void ddump() {
		generalDump(std::cerr);
	}

	void ddump(EqualityBucket* bucket) {
		dump(std::cerr, bucket);
	}

	void ddump(const llvm::Value* val) {
		if (! inGraph(val)) return;

		std::cerr << debug::getValName(val) << ":" << std::endl;
		dump(std::cerr, mapToBucket.at(val));
		std::cerr << std::endl;
	}

	void dump(std::ostream& stream, EqualityBucket* bucket) {
		for (auto ptr : bucket->lesser)
			printInterleaved(stream, ptr, " < ", bucket);

		for (auto ptr : bucket->lesserEqual)
			printInterleaved(stream, ptr, " <= ", bucket);

		auto foundNonEqual = nonEqualities.find(bucket);
		if (foundNonEqual != nonEqualities.end()) {
			for (EqualityBucket* nonEqual : foundNonEqual->second)
				if (nonEqual < bucket)
					printInterleaved(stream, nonEqual, " != ", bucket);
		}

		EqualityBucket* foundValue = findByKey(loads, bucket);
		if (foundValue)
			printInterleaved(stream, foundValue, " = LOAD ", bucket);

		if (bucket->lesser.empty() // values just equal and nothing else
				&& bucket->lesserEqual.empty()
				&& bucket->parents.empty()
				&& foundNonEqual == nonEqualities.end()
				&& ! findByValue(loads, bucket)
				&& ! foundValue) {
			printVals(stream, bucket);
			stream << std::endl;
		}
	}

    void generalDump(std::ostream& stream) {

		for (const auto& bucketPtr : buckets) {
			dump(stream, bucketPtr.get());
		}

    }
#endif

};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_RELATIONS_MAP_H_

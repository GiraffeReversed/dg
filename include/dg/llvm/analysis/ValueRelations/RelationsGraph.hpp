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

class EqualityBucket;

using BucketPtr = EqualityBucket*;
using BucketPtrSet = std::set<BucketPtr>;

enum class Relation { EQ, LE, LT, GE, GT };

struct Frame {
	BucketPtr bucket;
	typename BucketPtrSet::iterator it;
	Relation relation;

	Frame(BucketPtr b, typename BucketPtrSet::iterator i, Relation r):
		bucket(b), it(i), relation(r) {}
	
	friend bool operator==(const Frame& lt, const Frame& rt) {
		return lt.bucket == rt.bucket
			&& lt.it == rt.it
			&& lt.relation == rt.relation;
	}

	friend bool operator!=(const Frame& lt, const Frame& rt) {
		return ! (lt == rt);
	}
};

class EqualityBucket {

	using T = const llvm::Value*;

    friend class RelationsGraph;
public:

    using BucketPtr = EqualityBucket*;
	using BucketPtrSet = std::set<BucketPtr>;
	
	BucketPtrSet lesserEqual;
	BucketPtrSet lesser;
	BucketPtrSet parents;

	std::vector<T> equalities;

	struct Iterator {

		using value_type = Frame;
		using iterator_category = std::forward_iterator_tag;
		using difference_type = std::ptrdiff_t;

		std::stack<Frame> stack;
		std::set<const EqualityBucket*> visited;
		bool goDown = false;
		
		Iterator() = default;
		Iterator(EqualityBucket* start, bool down, bool begin): goDown(down) {
			if (begin) {
				stack.push(Frame(start,
								 goDown ? start->lesserEqual.begin() : start->parents.begin(),
								 Relation::EQ));
				visited.insert(start);
			}
		}

		friend bool operator==(const Iterator& lt, const Iterator& rt) {
			return lt.goDown == rt.goDown && lt.stack == rt.stack;
		}

		friend bool operator!=(const Iterator& lt, const Iterator& rt) {
			return ! (lt == rt);
		}

		const value_type& operator*() const { return stack.top(); }
		const value_type* operator->() const { return &stack.top(); }

		value_type& operator*() { return stack.top(); }
		value_type* operator->() { return &stack.top(); }

		Iterator& operator++() {
			if (stack.empty()) return *this;

			Frame frame = stack.top();
			stack.pop();

			// we searched all lesserEqual buckets, going on to lesser buckets
			if (goDown && frame.it == frame.bucket->lesserEqual.end())
				frame.it = frame.bucket->lesser.begin();

			// we searched all successors
			if ((goDown && frame.it == frame.bucket->lesser.end())
					|| (! goDown && frame.it == frame.bucket->parents.end()))
				return *this;

			// plan to return for next successor
			stack.emplace(Frame(frame.bucket, ++frame.it, frame.relation));
			--frame.it;

			// we set relation for successor, so it can be no longer equal
			if (frame.relation == Relation::EQ && goDown) frame.relation = Relation::LE;
			if (frame.relation == Relation::EQ && ! goDown) frame.relation = Relation::GE;
			// we pass lesser / greater edge, we know now that the relation is strict
			if (goDown && contains(frame.bucket->lesser, (*frame.it))) frame.relation = Relation::LT;
			if (! goDown && contains((*frame.it)->lesser, frame.bucket)) frame.relation = Relation::GT;

			// plan visit to successor
			// TODO fix somehow
			//if (! contains<const EqualityBucket*>(visited, *frame.it)) {
				visited.insert(*frame.it);
				if (goDown)
					stack.emplace(Frame(*frame.it, (*frame.it)->lesserEqual.begin(), frame.relation));
				else
					stack.emplace(Frame(*frame.it, (*frame.it)->parents.begin(), frame.relation));
			//}
			return *this;
		}

		Iterator operator++(int) {
			auto preInc = *this;
			++(*this);
			return preInc;
		}

		std::stack<Frame>& getStack() {
			return stack;
		}
	};

	using iterator = Iterator;
	using const_iterator = Iterator;

	iterator begin_down() {
		return Iterator(this, true, true);
	}

	iterator end_down() {
		return Iterator(this, true, false);
	}

	iterator begin_up() {
		return Iterator(this, false, true);
	}

	iterator end_up() {
		return Iterator(this, false, false);
	}

	std::pair<std::stack<Frame>, bool> subtreeContains(const EqualityBucket* needle, bool ignoreLE) {

		for (auto it = begin_down(); it != end_down(); ++it) {

			if (it->bucket == needle) {
				if (ignoreLE && it->relation != Relation::LT) continue;
				return { it.getStack(), true };
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
};

class RelationsGraph {

	using T = const llvm::Value*;

public:
	struct CallRelation {
		std::vector<std::pair<const llvm::Value*, const llvm::Value*>> equalPairs;
		RelationsGraph* callSiteRelations = nullptr;

		friend bool operator==(const CallRelation& lt, const CallRelation& rt) {
			return lt.equalPairs == rt.equalPairs
				&& lt.callSiteRelations == rt.callSiteRelations;
		}
	};

private:
    std::vector<std::unique_ptr<EqualityBucket>> buckets;
	std::map<T, EqualityBucket*> mapToBucket;
	std::map<unsigned, EqualityBucket*> placeholderBuckets;
	unsigned lastPlaceholderId = 0;

	std::map<EqualityBucket*, std::set<EqualityBucket*>> nonEqualities;

	// map of pairs (a, b) such that {any of b} = load {any of a}
	std::map<EqualityBucket*, EqualityBucket*> loads;

	std::vector<CallRelation> callRelations;

	struct Iterator {
		using value_type = std::pair<T, Relation>;

		enum Type { UP, DOWN, ALL, NONE };

		Type type = Type::NONE;
		bool strictOnly = false;
		EqualityBucket* start;
		EqualityBucket::iterator it;
		unsigned index;
		
		Iterator(EqualityBucket* st, bool s, Type t, bool begin): type(t), strictOnly(s), start(st), index(0) {
			if (begin) {
				if (type == Type::DOWN || type == Type::ALL)
					it = start->begin_down();
				if (type == Type::UP)
					it = start->begin_up();
				toNextValidValue();
			} else {
				if (type == Type::DOWN)
					it = start->end_down();
				if (type == Type::UP || type == Type::ALL)
					it = start->end_up();
			}
		}

		friend bool operator==(const Iterator& lt, const Iterator& rt) {
			return lt.type == rt.type
			    && lt.strictOnly == rt.strictOnly
				&& lt.it == rt.it;
		}

		friend bool operator!=(const Iterator& lt, const Iterator& rt) {
			return ! (lt == rt);
		}

		value_type operator*() const {
			if (strictOnly && it->relation != Relation::LT && it->relation != Relation::GT)
				assert(0 && "iterator always stops only at strict if demanded");
			return { it->bucket->getEqual()[index], it->relation };
		}

		// make iterator always point at valid value or end
		Iterator& operator++() {
			if (it == start->end_up() || it == start->end_down()) return *this;
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
				// ++ so that we would not pass equal again
				it = ++(start->begin_up());
				toNextValidValue();
			}

			return *this;
		}

		Iterator operator++(int) {
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

	bool areInGraph(T lt, T rt) const {
		return contains(mapToBucket, lt) && contains(mapToBucket, rt);
	}

	bool hasRelations(EqualityBucket* bucket) const {
		return bucket->getEqual().size() > 1
			|| ++bucket->begin_down() != bucket->end_down()
			|| ++bucket->begin_up()   != bucket->end_up();
	}

	bool hasRelationsOrLoads(EqualityBucket* bucket) const {
		return hasRelations(bucket)
			|| findByKey(loads, bucket)
			|| findByValue(loads, bucket);
	}
	
public:

	RelationsGraph() = default;
	
	RelationsGraph(const RelationsGraph& other):
		lastPlaceholderId(other.lastPlaceholderId), callRelations(other.callRelations) {

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

		for (auto& pair : other.placeholderBuckets)
			placeholderBuckets.emplace(pair.first, oldToNewPtr.at(pair.second));

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
		swap(first.placeholderBuckets, second.placeholderBuckets);
		swap(first.lastPlaceholderId, second.lastPlaceholderId);
		swap(first.nonEqualities, second.nonEqualities);
		swap(first.loads, second.loads);
		swap(first.callRelations, second.callRelations);
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

        for (T val : ltVals) {
			for (auto it = lt.begin_lesserEqual(val); it != lt.end_lesserEqual(val); ++it) {
				T other; Relation relation;
				std::tie(other, relation) = *it;
				switch (relation) {
					case Relation::EQ: if (! rt.isEqual(other, val))       return false; break;
					case Relation::LE: if (! rt.isLesserEqual(other, val)) return false; break;
					case Relation::LT: if (! rt.isLesser(other, val))      return false; break;
					default: assert(0 && "going down, not up");
				}
			}
        }

		for (auto& val : rtVals) {
			for (auto it = rt.begin_lesserEqual(val); it != rt.end_lesserEqual(val); ++it) {
				T other; Relation relation;
				std::tie(other, relation) = *it;
				switch (relation) {
					case Relation::EQ: if (! lt.isEqual(other, val))       return false; break;
					case Relation::LE: if (! lt.isLesserEqual(other, val)) return false; break;
					case Relation::LT: if (! lt.isLesser(other, val))      return false; break;
					default: assert(0 && "going down, not up");
				}
			}
        }

		std::set<std::pair<std::vector<T>, std::vector<T>>> ltLoads = lt.getAllLoads();
		std::set<std::pair<std::vector<T>, std::vector<T>>> rtLoads = rt.getAllLoads();

		if (ltLoads != rtLoads) return false;

		for (auto& pair : lt.loads) {
			EqualityBucket* ltFromBucket = pair.first;
			EqualityBucket* rtFromBucket = rt.mapToBucket.at(ltFromBucket->getEqual()[0]);

			EqualityBucket* ltValBucket = pair.second;
			EqualityBucket* rtValBucket = rt.loads.at(rtFromBucket);

			for (auto it = ltValBucket->begin_down(); it != ltValBucket->end_down(); ++it) {
				auto& equals = it->bucket->getEqual();
				if (equals.empty()) continue;

				EqualityBucket* rtRelatedBucket = rt.mapToBucket.at(equals[0]);
				switch (it->relation) {
					case Relation::EQ: if (! rt.isEqual(rtRelatedBucket, rtValBucket)) return false; break;
					case Relation::LT: if (! rt.isLesser(rtRelatedBucket, rtValBucket)) return false; break;
					case Relation::LE: if (! rt.isLesserEqual(rtRelatedBucket, rtValBucket)) return false; break;
					default: assert(0 && "going down, not up");
				}
			}

			for (auto it = ltValBucket->begin_up(); it != ltValBucket->end_up(); ++it) {
				auto& equals = it->bucket->getEqual();
				if (equals.empty()) continue;

				EqualityBucket* rtRelatedBucket = rt.mapToBucket.at(equals[0]);
				switch (it->relation) {
					case Relation::EQ: break; // already been here on way down
					case Relation::GT: if (! rt.isLesser(rtValBucket, rtRelatedBucket)) return false; break;
					case Relation::GE: if (! rt.isLesserEqual(rtValBucket, rtRelatedBucket)) return false; break;
					default: assert(0 && "going down, not up");
				}
			}
		}

		for (auto& pair : rt.loads) {
			EqualityBucket* rtFromBucket = pair.first;
			EqualityBucket* ltFromBucket = lt.mapToBucket.at(rtFromBucket->getEqual()[0]);

			EqualityBucket* rtValBucket = pair.second;
			EqualityBucket* ltValBucket = lt.loads.at(ltFromBucket);

			for (auto it = rtValBucket->begin_down(); it != rtValBucket->end_down(); ++it) {
				auto& equals = it->bucket->getEqual();
				if (equals.empty()) continue;

				EqualityBucket* ltRelatedBucket = lt.mapToBucket.at(equals[0]);
				switch (it->relation) {
					case Relation::EQ: if (! lt.isEqual(ltRelatedBucket, ltValBucket)) return false; break;
					case Relation::LT: if (! lt.isLesser(ltRelatedBucket, ltValBucket)) return false; break;
					case Relation::LE: if (! lt.isLesserEqual(ltRelatedBucket, ltValBucket)) return false; break;
					default: assert(0 && "going down, not up");
				}
			}

			for (auto it = rtValBucket->begin_up(); it != rtValBucket->end_up(); ++it) {
				auto& equals = it->bucket->getEqual();
				if (equals.empty()) continue;

				EqualityBucket* ltRelatedBucket = lt.mapToBucket.at(equals[0]);
				switch (it->relation) {
					case Relation::EQ: break; // already been here on way down
					case Relation::GT: if (! rt.isLesser(ltValBucket, ltRelatedBucket)) return false; break;
					case Relation::GE: if (! rt.isLesserEqual(ltValBucket, ltRelatedBucket)) return false; break;
					default: assert(0 && "going down, not up");
				}
			}
		}

		return lt.callRelations == rt.callRelations;
	}

	friend bool operator!=(const RelationsGraph& lt, const RelationsGraph& rt) {
		return ! (lt == rt);
	}

	void merge(const RelationsGraph& other) {
		// DANGER fogets placeholder buckets
		std::vector<const llvm::Value*> values = other.getAllValues();

		for (auto valueIt = values.begin(); valueIt != values.end(); ++valueIt) {
            const llvm::Value* val = *valueIt;

            for (auto it = other.begin_lesserEqual(val);
                      it != other.end_lesserEqual(val);
                      ++it) {
                const llvm::Value* related; Relation relation;
                std::tie(related, relation) = *it;

                if (related == val) continue;

				//auto found = std::find(values.begin(), values.end(), related);
                switch (relation) {
                    case Relation::EQ: setEqual(related, val);

						if (true) { // cannot initialize found directly in case
							auto found = std::find(values.begin(), values.end(), related);
							if (found != values.end()) {
								values.erase(found);
								valueIt = std::find(values.begin(), values.end(), val);
							}
						}
                        break;

                    case Relation::LT: setLesser(related, val); break;

                    case Relation::LE: setLesserEqual(related, val); break;

					default: assert(0 && "going down, not up");
                }
            }
        }
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

		if (isEqual(lt, rt)) return;

		// assert no conflicting relations
		assert(! isNonEqual(lt, rt));
		assert(! isLesser(lt, rt));
		assert(! isLesser(rt, lt));

		add(lt);
		add(rt);

		setEqual(mapToBucket.at(lt), mapToBucket.at(rt));
	}

	void setEqual(T lt, unsigned rt) {
		add(lt);
		setEqual(mapToBucket.at(lt), placeholderBuckets.at(rt));
	}

	void setEqual(unsigned lt, T rt) {
		setEqual(rt, lt);
	}
	
	void setEqual(EqualityBucket* newBucketPtr, EqualityBucket* oldBucketPtr) {
		std::vector<BucketPtr> toMerge;

		// handle lesserEqual specializing to equal
		if (isLesserEqual(newBucketPtr, oldBucketPtr) || isLesserEqual(oldBucketPtr, newBucketPtr)) {

			std::pair<std::stack<Frame>, bool> pair;
			if (isLesserEqual(newBucketPtr, oldBucketPtr)) {
				pair = oldBucketPtr->subtreeContains(newBucketPtr, false);
			} else {
				pair = newBucketPtr->subtreeContains(oldBucketPtr, false);
			}
			std::stack<Frame> frames = pair.first;

			while (! frames.empty()) {
				Frame frame = frames.top();
				BucketPtr bucket = frame.bucket;
				toMerge.push_back(bucket);
				frames.pop();

				// also unset lesserEqual relation
				if (! frames.empty()) {
					BucketPtr above = frames.top().bucket;
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

	void setNonEqual(T lt, T rt) {

		if (isNonEqual(lt, rt)) return;

		add(lt);
		add(rt);

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

		if (isLesser(lt, rt)) return;

		// assert no conflicting relations
		assert(! isEqual(lt, rt));
		assert(! isLesserEqual(rt, lt));
		assert(! isLesser(rt, lt));

		add(lt); assert(mapToBucket.find(lt) != mapToBucket.end());
		add(rt); assert(mapToBucket.find(rt) != mapToBucket.end());

		EqualityBucket* ltBucketPtr = mapToBucket.at(lt);
		EqualityBucket* rtBucketPtr = mapToBucket.at(rt);

		// handle lesserEqual specializing to lesser
		if (isLesserEqual(lt, rt)) {
			if (contains<EqualityBucket*>(rtBucketPtr->lesserEqual, ltBucketPtr))
				rtBucketPtr->lesserEqual.erase(ltBucketPtr);
			else
				assert(0); // more buckets in between, can't decide this
		}
		setLesser(ltBucketPtr, rtBucketPtr);
	}

	void setLesser(T lt, unsigned rt) {
		add(lt);
		setLesser(mapToBucket.at(lt), placeholderBuckets.at(rt));
	}

	void setLesser(unsigned lt, T rt) {
		add(rt);
		setLesser(placeholderBuckets.at(lt), mapToBucket.at(rt));
	}

	void setLesser(EqualityBucket* ltBucketPtr, EqualityBucket* rtBucketPtr) {
		rtBucketPtr->lesser.insert(ltBucketPtr);
		ltBucketPtr->parents.insert(rtBucketPtr);
	}

	void setLesserEqual(T lt, T rt) {

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

	void setLesserEqual(EqualityBucket* ltBucketPtr, EqualityBucket* rtBucketPtr) {
		rtBucketPtr->lesserEqual.insert(ltBucketPtr);
		ltBucketPtr->parents.insert(rtBucketPtr);
	}

	void setLoad(T from, T val) {

		if (isLoad(from, val)) return;

		add(val);
		add(from);

		setLoad(mapToBucket.at(from), mapToBucket.at(val));
	}

	void setLoad(T from, unsigned val) {
		add(from);
		setLoad(mapToBucket.at(from), placeholderBuckets.at(val));
	}

	void setLoad(EqualityBucket* fromBucketPtr, EqualityBucket* valBucketPtr) {
		// get set of values that load from equal pointers
		EqualityBucket* valEqualBucketPtr = findByKey(loads, fromBucketPtr);

		// if there is such a set, we just add val to it
		if (valEqualBucketPtr) {
			setEqual(valBucketPtr, valEqualBucketPtr);
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
			if (! valBucketPtr->getEqual().empty()) {
				T val = valBucketPtr->getAny();
				mapToBucket.erase(val);
			}
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
				if (! it->get()->getEqual().empty()) {
					T val = it->get()->getAny();
					mapToBucket.erase(val);
				}
				it = buckets.erase(it);
			} else ++it;
		}
    }

	void unsetRelations(T val) {
		EqualityBucket* valBucketPtr = mapToBucket.at(val);

		bool onlyReference = valBucketPtr->getEqual().size() == 1;
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

		return isEqual(mapToBucket.at(lt), mapToBucket.at(rt));
	}

	bool isEqual(EqualityBucket* ltEqBucket, EqualityBucket* rtEqBucket) const {

		return ltEqBucket == rtEqBucket;
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

		if (! inGraph(rt)) return false;

		if (inGraph(lt)) {
			const auto& rtEqBucket = mapToBucket.at(rt);
			if (isLesser(mapToBucket.at(lt), rtEqBucket))
				return true;
		}
		
		if (auto constLt = llvm::dyn_cast<llvm::ConstantInt>(lt)) {
			const llvm::ConstantInt* constBound = getLesserEqualConstant(rt);
			if (constBound && constLt->getValue().slt(constBound->getValue()))
				return true;
		}

		return false;
	}

	bool isLesser(EqualityBucket* ltEqBucket, EqualityBucket* rtEqBucket) const {
		return rtEqBucket->subtreeContains(ltEqBucket, true).second;
	}

	bool isLesserEqual(T lt, T rt) const {

		if (! inGraph(rt)) return false;

		if (inGraph(lt)) {
			if (isLesserEqual(mapToBucket.at(lt), mapToBucket.at(rt)))
				return true;
		}
		
		if (auto constLt = llvm::dyn_cast<llvm::ConstantInt>(lt)) {
			const llvm::ConstantInt* constBound = getLesserEqualConstant(rt);
			if (constBound && constLt->getValue().sle(constBound->getValue()))
				return true;
		}

		return false;
	}

	bool isLesserEqual(EqualityBucket* ltEqBucket, EqualityBucket* rtEqBucket) const {
		return rtEqBucket->subtreeContains(ltEqBucket, false).second;
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
		return valBucket->getEqual();
	}

	Iterator begin_lesser(T val) const {
		return Iterator(mapToBucket.at(val), true, Iterator::Type::DOWN, true);
	}

	Iterator end_lesser(T val) const {
		return Iterator(mapToBucket.at(val), true, Iterator::Type::DOWN, false);
	}

	Iterator begin_lesserEqual(T val) const {
		return Iterator(mapToBucket.at(val), false, Iterator::Type::DOWN, true);
	}

	Iterator end_lesserEqual(T val) const {
		return Iterator(mapToBucket.at(val), false, Iterator::Type::DOWN, false);
	}

	Iterator begin_greater(T val) const {
		return Iterator(mapToBucket.at(val), true, Iterator::Type::UP, true);
	}

	Iterator end_greater(T val) const {
		return Iterator(mapToBucket.at(val), true, Iterator::Type::UP, false);
	}

	Iterator begin_greaterEqual(T val) const {
		return Iterator(mapToBucket.at(val), false, Iterator::Type::UP, true);
	}

	Iterator end_greaterEqual(T val) const {
		return Iterator(mapToBucket.at(val), false, Iterator::Type::UP, false);
	}

	Iterator begin_all(T val) const {
		return Iterator(mapToBucket.at(val), false, Iterator::Type::ALL, true);
	}

	Iterator end_all(T val) const {
		return Iterator(mapToBucket.at(val), false, Iterator::Type::ALL, false);
	}

	std::vector<T> getSampleLesser(T val) const {
		if (! inGraph(val)) return {};
		EqualityBucket* bucketPtr = mapToBucket.at(val);

		std::vector<EqualityBucket*> acc;
		bucketPtr->searchForLesser(acc);

		std::vector<T> result;
		for (EqualityBucket* bucketPtr : acc) {
			if (! bucketPtr->getEqual().empty())
				result.push_back(bucketPtr->getAny());
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
			if (! bucketPtr->getEqual().empty())
				result.push_back(bucketPtr->getAny());
		}
		return result;
	}

	std::vector<T> getAllRelated(T val) const {
		std::vector<T> result;
		for (auto it = begin_all(val); it != end_all(val); ++it) {
			result.push_back((*it).first);
		}
		return result;
	}

	const llvm::ConstantInt* getLesserEqualConstant(T val) const {

		const llvm::ConstantInt* highest = nullptr;
		for (auto it = begin_lesserEqual(val); it != end_lesserEqual(val); ++it) {
			if (auto constant = llvm::dyn_cast<llvm::ConstantInt>((*it).first)) {
				if (! highest || constant->getValue().sgt(highest->getValue()))
					highest = constant;
			}
		}
		return highest;
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

	CallRelation& newCallRelation() {
		callRelations.emplace_back();
		return callRelations.back();
	}

	const std::vector<CallRelation>& getCallRelations() const {
		return callRelations;
	}

	std::vector<CallRelation>& getCallRelations() {
		return callRelations;
	}

	void addXorRelation(const CallRelation& relation) {
		callRelations.emplace_back(relation);
	}

	void makePlaceholder(T val) {
		if (! contains(mapToBucket, val)) return;

		EqualityBucket* bucket = mapToBucket.at(val);

		for (T value : bucket->getEqual())
			mapToBucket.erase(value);
		bucket->getEqual().clear();
	}

	unsigned newPlaceholderBucket() {
		EqualityBucket* bucket = new EqualityBucket;
		buckets.emplace_back(bucket);
		placeholderBuckets.emplace(++lastPlaceholderId, bucket);
		return lastPlaceholderId;
	}

	void erasePlaceholderBucket(unsigned id) {
		// DANGER erases placeholder bucket for good, not just
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
		//const auto& values = bucket->getEqual();

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

		//EqualityBucket* foundKey = findByValue(loads, bucket);
		//if (foundKey)
		//	printInterleaved(stream, values, " = LOAD ", getEqual(foundKey));

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

		stream << " THE GRAPH" << std::endl;
		for (const auto& bucketPtr : buckets) {
			dump(stream, bucketPtr.get());
		}

		for (auto& callRelation : callRelations) {
			stream << std::endl << "    XOR relations" << std::endl;
			for (auto& equalPair : callRelation.equalPairs)
				stream << "{ " << debug::getValName(equalPair.first) << "; "
							   << debug::getValName(equalPair.second)
					   << " }" << std::endl;
			callRelation.callSiteRelations->generalDump(stream);
		}

    }
#endif

};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_RELATIONS_MAP_H_

#ifndef _DG_LLVM_RELATIONS_MAP_H_
#define _DG_LLVM_RELATIONS_MAP_H_

#include <set>
#include <map>
#include <stack>
#include <tuple>

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
class EqualityBucket {

    template <typename S> friend class RelationsGraph;

    using SuccessorPtr = const EqualityBucket<T>*;
	using SuccessorSet = std::set<SuccessorPtr>;
	
	SuccessorSet lesserEqual;
	SuccessorSet lesser;

	bool subtreeContains(const EqualityBucket<T>* needle, bool ignoreLE) const {

		using Frame = std::tuple<SuccessorPtr, typename SuccessorSet::iterator, bool>;

        std::set<const EqualityBucket<T>*> visited;
		std::stack<Frame> stack;

		visited.insert(this);
		stack.push(Frame(this, lesserEqual.begin(), ignoreLE));

		const EqualityBucket<T>* bucketPtr;
		typename SuccessorSet::iterator succIt;
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

			if (succIt == lesser.end())
				continue;

			stack.push({ bucketPtr, ++succIt, ignore });

			if (! ::contains<const EqualityBucket<T>*>(visited, *succIt)) {
				visited.insert(*succIt);
				stack.emplace(Frame(*succIt, (*succIt)->lesserEqual.begin(), ignore));
			}
		}

		return false;
	}
};

template <typename T>
class RelationsGraph {

    std::set<EqualityBucket<T>> buckets;
    std::map<T, T*> loads;
	std::map<T, EqualityBucket<T>*> equalities;

	bool areInGraph(const T& lt, const T& rt) const {
		return contains(equalities, lt) && contains(equalities, rt);
	}
	
	public:
	bool add(const T& val) {
		return equalities.insert({ val, nullptr }).second;
	}

	public:

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

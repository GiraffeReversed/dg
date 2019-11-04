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
class IdentityBucket {
	std::set<T> identities;
};

template <typename T>
class EqualityBucket {
	using SuccessorSet = std::set<EqualityBucket<T>*>;
	
	std::map<T, IdentityBucket<T>> mapping;
	SuccessorSet lesserEqual;
	SuccessorSet lesser;

	bool genericDFSContains(const T& val, bool ignoreLE) const {
		std::set<EqualityBucket<T>*> visited;
		std::stack<std::tuple<EqualityBucket<T>*, typename SuccessorSet::iterator, bool>> stack;

		visited.insert(&this);
		stack.emplace(&this, lesserEqual.begin(), ignoreLE);

		EqualityBucket<T>* bucketPtr;
		typename SuccessorSet::iterator it;
		bool ignore;
		while (! stack.empty()) {
			std::tie(bucketPtr, it, ignore) = stack.pop();

			bool firstPass = it == lesserEqual.begin();
			if (! ignore && firstPass && contains(*bucketPtr, val))
				return true;

			if (it == lesserEqual.end()) {
				it = lesser.being();
				ignore = false;
			}

			if (it == lesser.end())
				continue;

			stack.push(bucketPtr, ++it, ignore);

			if (! contains(visited, it)) {
				visited.insert(it);
				stack.emplace(it, it->lesserEqual.begin(), ignore);
			}
		}

		return false;
	}
};

template <typename T>
class RelationsGraph {
	std::map<T, EqualityBucket<T>> mapping;

	bool areInGraph(const T& lt, const T& rt) const {
		return contains(mapping, lt) && contains(mapping, rt);
	}

	public:
		bool isIdentical(const T& lt, const T& rt) const {

			if (! areInGraph(lt, rt))
				return false;

			const auto& ltIdBucket = mapping.at(lt).at(lt);
			return contains(ltIdBucket, rt);
		}


		bool isEqual(const T& lt, const T& rt) const {

			if (! areInGraph(lt, rt))
				return false;

			const auto& ltEqBucket = mapping.at(lt);
			return contains(ltEqBucket, rt);
		}

		bool isLesser(const T& lt, const T& rt) const {

			if (! areInGraph(lt, rt))
				return false;

			const auto& rtEqBucket = mapping.at(rt);
			return genericDFSContains(&rtEqBucket, lt, true);
		}

		bool isLesserEqual(const T& lt, const T& rt) const {

			if (! areInGraph(lt, rt))
				return false;

			const auto& rtEqBucket = mapping.at(rt);
			return genericDFSContains(rtEqBucket, lt, false);
		}
};

} // namespace dg

#endif // _DG_LLVM_RELATIONS_MAP_H_

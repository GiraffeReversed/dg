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
	template <typename S> friend class RelationsGraph;
	template <typename S> friend class EqualityBucket;
	std::set<T> identities;

	bool contains(const T& val) const {
		return ::contains<T>(identities, val); 
	}

	public:
		IdentityBucket(std::set<T>&& ids): identities(std::move(ids)) {}
		IdentityBucket(std::initializer_list<T> list): identities(list) {}
};

template <typename T>
class EqualityBucket {
	template <typename S> friend class RelationsGraph;
	using SuccessorPtr = const EqualityBucket<T>*;
	using SuccessorSet = std::set<SuccessorPtr>;
	
	std::map<T, IdentityBucket<T>> mapping;
	SuccessorSet lesserEqual;
	SuccessorSet lesser;

	bool genericContains(const T& val, bool ignoreLE) const {
		using Frame = std::tuple<SuccessorPtr, typename SuccessorSet::iterator, bool>;
		std::set<const EqualityBucket<T>*> visited;
		std::stack<Frame> stack;

		visited.insert(this);
		stack.push(Frame(this, lesserEqual.begin(), ignoreLE));

		const EqualityBucket<T>* bucketPtr;
		typename SuccessorSet::iterator it;
		bool ignore;
		while (! stack.empty()) {
			std::tie(bucketPtr, it, ignore) = stack.top();
			stack.pop();

			bool firstPass = it == lesserEqual.begin();
			if (! ignore && firstPass && bucketPtr->contains(val))
				return true;

			if (it == lesserEqual.end()) {
				it = lesser.begin();
				ignore = false;
			}

			if (it == lesser.end())
				continue;

			stack.push({ bucketPtr, ++it, ignore });

			if (! ::contains<const EqualityBucket<T>*>(visited, *it)) {
				visited.insert(*it);
				stack.emplace(Frame(*it, (*it)->lesserEqual.begin(), ignore));
			}
		}

		return false;
	}

	bool contains(const T& val) const {
		return ::contains<T>(mapping, val);
	}

	public:
		EqualityBucket(std::map<T, IdentityBucket<T>>&& mp): mapping(std::move(mp)) {}
		EqualityBucket(std::initializer_list<std::pair<const T, IdentityBucket<T>>> list): mapping(list) {}
};

template <typename T>
class RelationsGraph {
	std::map<T, EqualityBucket<T>> mapping;

	bool areInGraph(const T& lt, const T& rt) const {
		return contains(mapping, lt) && contains(mapping, rt);
	}
	
	public:
	bool add(const T& val) {
		return mapping.insert({val, {{ val, { val }}}}).second;
	}

	public:
		bool isIdentical(const T& lt, const T& rt) const {

			if (! areInGraph(lt, rt))
				return false;

			const auto& ltIdBucket = mapping.at(lt).at(lt);
			return ltIdBucket.contains(rt);
		}


		bool isEqual(const T& lt, const T& rt) const {

			if (! areInGraph(lt, rt))
				return false;

			const auto& ltEqBucket = mapping.at(lt);
			return ltEqBucket.contains(rt);
		}

		bool isLesser(const T& lt, const T& rt) const {

			if (! areInGraph(lt, rt))
				return false;

			const auto& rtEqBucket = mapping.at(rt);
			return rtEqBucket.genericContains(lt, true);
		}

		bool isLesserEqual(const T& lt, const T& rt) const {

			if (! areInGraph(lt, rt))
				return false;

			const auto& rtEqBucket = mapping.at(rt);
			return rtEqBucket.genericContains(lt, false);
		}
};

} // namespace dg

#endif // _DG_LLVM_RELATIONS_MAP_H_

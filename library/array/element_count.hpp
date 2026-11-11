#pragma once
#include <utility>
#include <vector>

namespace cp {

// Run-length counts (experiments/library/cpp/array/element_count.hpp `element_count`): splits v into its maximal runs
// of consecutive equal elements and returns (value, length) for each run in order. Equal values that are not adjacent
// form separate runs; an empty v gives an empty result. This is not a frequency table of the whole sequence.
// T is a container with value_type, size() and operator[] (std::vector, std::string, std::deque, ...); the element type
// must be copyable and comparable with ==, which must be an equivalence relation.
// Preconditions: v.size() <= INT_MAX (the length is stored in an int).
// Time O(n) element comparisons and copies; extra space O(number of runs) for the result.
// Fixed from the original: the original used T (the container type) as the element type in the result type and in
// `T pre = v[0]`, so it could not be instantiated with any standard container. The element type is now
// typename T::value_type; everything else is unchanged.
template <class T> std::vector<std::pair<typename T::value_type, int>> element_count(const T &v) {
  std::vector<std::pair<typename T::value_type, int>> ret;
  int n = v.size();
  if (n == 0) {
    return ret;
  }
  typename T::value_type pre = v[0];
  int cnt = 0;
  for (int i = 0; i < n; i++) {
    if (pre == v[i]) {
      cnt++;
    } else {
      ret.emplace_back(pre, cnt);
      pre = v[i];
      cnt = 1;
    }
  }
  ret.emplace_back(pre, cnt);
  return ret;
}

template std::vector<std::pair<long long, int>> element_count<std::vector<long long>>(const std::vector<long long> &);
template std::vector<std::pair<int, int>> element_count<std::vector<int>>(const std::vector<int> &);

} // namespace cp

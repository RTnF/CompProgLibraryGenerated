#pragma once
#include <cassert>
#include <climits>
#include <utility>
#include <vector>

namespace cp {

// Consecutive equal runs; input need not be sorted.
// Preconditions: size <= INT_MAX; equality is an equivalence relation.
// T supports copying/assignment. Allocation and T operations must succeed.
// With constant-cost T operations: O(n) time, O(number of runs) extra space.
template <class T>
std::vector<std::pair<T, int>> element_count(const std::vector<T> &v) {
  assert(v.size() <= static_cast<std::size_t>(INT_MAX));
  std::vector<std::pair<T, int>> ret;
  int n = static_cast<int>(v.size());
  if (n == 0) {
    return ret;
  }
  T pre = v[0];
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

} // namespace cp

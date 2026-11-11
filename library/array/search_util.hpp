#pragma once
#include <utility>
#include <vector>

namespace cp {

// Search utilities: count and counts (experiments/library/cpp/array/search_util.hpp) and lower_bound_index. Every
// function is a template over the element type.

// Number of positions i in [idx_begin, idx_end) with v[i] == value (the original `count`, with its default arguments).
// idx_end == -1 means v.size().
// Preconditions: v.size() < 2^31 and 0 <= idx_begin <= E <= v.size(), where E is idx_end (v.size() for -1).
template <class T> inline int count(const std::vector<T> &v, T value, int idx_begin = 0, int idx_end = -1) {
  if (idx_end == -1) {
    idx_end = v.size();
  }
  int cnt = 0;
  for (int i = idx_begin; i < idx_end; i++) {
    if (v[i] == value) {
      cnt++;
    }
  }
  return cnt;
}

template int count<int>(const std::vector<int> &, int, int, int);

// The values of a sorted vector with their numbers of occurrences, in increasing order of the value.
// Precondition: v_sorted is sorted (non-decreasing). Time O(n).
template <class T> inline std::vector<std::pair<T, int>> counts(const std::vector<T> &v_sorted) {
  std::vector<std::pair<T, int>> ret;
  int s = v_sorted.size();
  for (int i = 0; i < s; i++) {
    if (i == 0 || ret.back().first != v_sorted[i]) {
      ret.emplace_back(v_sorted[i], 1);
    } else {
      ret.back().second++;
    }
  }
  return ret;
}

template std::vector<std::pair<long long, int>> counts<long long>(const std::vector<long long> &);

// Index of the first element of the ascending vector `a` that is not less than `x` (a.size() when there is none):
// std::lower_bound(a.begin(), a.end(), x) - a.begin(), written as a binary search the verified expressions can follow.
// Preconditions: a.size() < 2^31 and `a` is ascending (a[i] <= a[j] for i <= j). Time O(log a.size()), extra space O(1).
template <class T> inline int lower_bound_index(const std::vector<T> &a, T x) {
  int lo = 0;
  int hi = (int)a.size();
  while (lo < hi) {
    int mid = lo + (hi - lo) / 2;
    if (a[mid] < x) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return lo;
}

template int lower_bound_index<long long>(const std::vector<long long> &, long long);

} // namespace cp

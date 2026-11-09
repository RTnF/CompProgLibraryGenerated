#pragma once
#include <algorithm>
#include <cassert>
#include <vector>

namespace cp {

// Sort utilities (experiments/library/cpp/array/sort_util.hpp): inv_perm, compress, and the std::sort / std::unique
// wrappers sort_vector and dedup_vector. Every function is a template over the element type; the instances listed
// after each definition are the verified ones.

// Derived from experiments/library/cpp/array/sort_util.hpp: the function template keeps its type parameter T (the
// verified instance is T = int, instantiated explicitly below).
// Inverse of a 0-indexed permutation, e.g. [2, 4, 0, 1, 3] -> [2, 3, 0, 4, 1].
// Preconditions: v.size() < 2^31, every v[i] is in [0, v.size()) and the values are pairwise distinct;
// a violation stops the program at an assert.
template <class T> std::vector<int> inv_perm(const std::vector<T> &v) {
  int n = v.size();
  std::vector<int> inv(n, -1);
  for (int i = 0; i < n; i++) {
    assert(0 <= v[i] && v[i] < n);
    assert(inv[v[i]] == -1);
    inv[v[i]] = i;
  }
  return inv;
}

template std::vector<int> inv_perm<int>(const std::vector<int> &);

// Coordinate compression into caller-provided buffers (experiments/library/cpp/array/sort_util.hpp `compress`
// without the allocation and the offset). unzip becomes the sorted distinct values of x; cmp[i] is the index of
// x[i] in unzip. Preconditions: x, unzip and cmp are three distinct vectors, x.size() == unzip.size() == cmp.size()
// < 2^31 (unzip is shrunk by the call; its contents on entry are overwritten). Time O(n log n), extra space O(1).
template <class T> inline void compress(const std::vector<T> &x, std::vector<T> &unzip, std::vector<int> &cmp) {
  int n = (int)x.size();
  for (int i = 0; i < n; i++) {
    unzip[i] = x[i];
  }
  std::sort(unzip.begin(), unzip.end());
  unzip.erase(std::unique(unzip.begin(), unzip.end()), unzip.end());
  int m = (int)unzip.size();
  for (int i = 0; i < n; i++) {
    int lo = 0;
    int hi = m;
    while (lo < hi) {
      int mid = lo + (hi - lo) / 2;
      if (unzip[mid] < x[i]) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    cmp[i] = lo;
  }
}

template void compress<long long>(const std::vector<long long> &, std::vector<long long> &, std::vector<int> &);

// Sorts x in ascending order (std::sort with the default operator<). Time O(x.size() log x.size()) comparisons,
// extra space O(1) in the model (the standard allows introsort's O(log n) stack; see docs/sort_util.md).
template <class T> inline void sort_vector(std::vector<T> &x) {
  std::sort(x.begin(), x.end());
}

template void sort_vector<long long>(std::vector<long long> &);

// Collapses each run of equal adjacent elements of x to its first element (the erase-unique idiom). On a sorted
// vector this removes all duplicates. Time O(x.size()), extra space O(1).
template <class T> inline void dedup_vector(std::vector<T> &x) {
  x.erase(std::unique(x.begin(), x.end()), x.end());
}

template void dedup_vector<long long>(std::vector<long long> &);

} // namespace cp

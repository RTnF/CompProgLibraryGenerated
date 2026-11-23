#pragma once
#include <algorithm>
#include <cassert>
#include <numeric>
#include <vector>

namespace cp {

// Sort utilities (experiments/library/cpp/array/sort_util.hpp): inv_perm, arg_sort, inv_arg_sort and the two
// compress overloads as in the original, plus the std::sort / std::unique wrappers sort_vector and dedup_vector.
// Every function is a template over the element type; the instances listed after each definition are the verified
// ones.

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

// Indices of v in sorted order (a stable sort: equal values keep their index order), e.g.
// [3, 3, 1, 5, 2] -> [2, 4, 0, 1, 3]. Precondition: v.size() < 2^31; < is a strict weak order on T.
// Time O(n log n) comparisons.
template <class T> std::vector<int> arg_sort(const std::vector<T> &v) {
  std::vector<int> arg(v.size());
  std::iota(arg.begin(), arg.end(), 0);
  std::stable_sort(arg.begin(), arg.end(), [&](int a, int b) { return v[a] < v[b]; });
  return arg;
}

template std::vector<int> arg_sort<long long>(const std::vector<long long> &);

// Where each index moves by the stable sort: the inverse of arg_sort(v), e.g. [3, 3, 1, 5, 2] -> [2, 3, 0, 4, 1].
// Precondition: v.size() < 2^31. Time O(n log n).
template <class T> std::vector<int> inv_arg_sort(const std::vector<T> &v) { return inv_perm(arg_sort(v)); }

template std::vector<int> inv_arg_sort<long long>(const std::vector<long long> &);

// Coordinate compression, e.g. [3, 3, 1, 5, 2] -> [2, 2, 0, 3, 1] + offset. unzip becomes the sorted distinct
// values of x ([1, 2, 3, 5]); the result has the index of x[i] in unzip plus offset. Preconditions: x.size() < 2^31;
// T is constructible from the index plus offset. Time O(n log n).
template <class T> std::vector<T> compress(const std::vector<T> &x, std::vector<T> &unzip, int offset = 0) {
  int n = x.size();
  std::vector<T> cmp(n);
  unzip = x;
  std::sort(unzip.begin(), unzip.end());
  unzip.erase(std::unique(unzip.begin(), unzip.end()), unzip.end());
  for (int i = 0; i < n; i++) {
    cmp[i] = std::lower_bound(unzip.begin(), unzip.end(), x[i]) - unzip.begin() + offset;
  }
  return cmp;
}

template std::vector<long long> compress<long long>(const std::vector<long long> &, std::vector<long long> &, int);

// Coordinate compression without the sorted distinct values. Time O(n log n).
template <class T> std::vector<T> compress(const std::vector<T> &x, int offset = 0) {
  auto tmp = std::vector<T>();
  return compress(x, tmp, offset);
}

template std::vector<long long> compress<long long>(const std::vector<long long> &, int);

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

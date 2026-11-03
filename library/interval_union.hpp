#pragma once
#include <vector>

namespace cp {

// Union of closed intervals [l[i], r[i]] (interval_union_inclusive in experiments/library/cpp/interval/interval_union.hpp,
// which takes and returns a vector<pair<T, T>>). Differences: the pairs are given as two parallel vectors l and r, the
// result is written to the caller's vectors ret_l and ret_r (the function returns the number m of result intervals), and
// the pairs are sorted by an insertion sort (O(n^2) instead of std::sort's O(n log n)). Like the original, the input
// (l, r) is sorted lexicographically as a side effect.
// Result: ret_l[k] <= ret_r[k] for k < m; ret_r[k] < ret_l[k + 1] (sorted, separated by gaps); and a point x lies in
// some [l[i], r[i]] if and only if it lies in some [ret_l[k], ret_r[k]].
// Preconditions: l, r, ret_l and ret_r are four distinct vectors, l.size() == r.size() == n, ret_l.size() >= n and
// ret_r.size() >= n, l[i] <= r[i] for every i, n < 2^31 - 1. Time O(n^2), extra space O(1).
template <class T>
inline int interval_union_inclusive(std::vector<T> &l, std::vector<T> &r, std::vector<T> &ret_l, std::vector<T> &ret_r) {
  int n = (int)l.size();
  for (int i = 1; i < n; i++) {
    int j = i;
    int go = 1;
    while (go != 0) {
      T a = l[j - 1];
      T b = l[j];
      T c = r[j - 1];
      T d = r[j];
      bool before = b < a || (a == b && d < c);
      if (before) {
        l[j - 1] = b;
        l[j] = a;
        r[j - 1] = d;
        r[j] = c;
        j--;
        if (j == 0) {
          go = 0;
        }
      } else {
        go = 0;
      }
    }
  }
  int m = 0;
  for (int i = 0; i < n; i++) {
    T a = l[i];
    T b = r[i];
    if (m == 0) {
      ret_l[m] = a;
      ret_r[m] = b;
      m++;
    } else {
      T pr = ret_r[m - 1];
      if (pr < a) {
        ret_l[m] = a;
        ret_r[m] = b;
        m++;
      } else {
        if (pr < b) {
          ret_r[m - 1] = b;
        }
      }
    }
  }
  return m;
}

template int interval_union_inclusive<long long>(std::vector<long long> &, std::vector<long long> &,
                                                 std::vector<long long> &, std::vector<long long> &);

} // namespace cp

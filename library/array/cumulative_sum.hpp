#pragma once
#include <cassert>
#include <vector>

namespace cp {

// One-dimensional cumulative sums (experiments/library/cpp/array/cumulative_sum.hpp, CumulativeSum): cs[i] is the
// sum of the first i elements of the array (so cs.size() == n + 1), built in O(n), static, and a range sum in O(1).
// The class template keeps its type parameter T (the verified instances are CumulativeSum<long long> and
// CumulativeSum<int>, instantiated explicitly below).
// Differences from the original: the field n is not kept (it is cs.size() - 1 at all times); the queries are const; the
// asserts of the original are kept as checks, written one condition at a time; the loop of the constructor starts at 0.
// Preconditions: v.size() < 2^31 - 1, every prefix sum and the difference of two prefix sums fits in T.
template <class T = long long> class CumulativeSum {
  std::vector<T> cs;

public:
  CumulativeSum(const std::vector<T> &v) : cs(v.size() + 1) {
    int n = (int)v.size();
    cs[0] = T(0);
    for (int i = 0; i < n; i++) {
      cs[i + 1] = cs[i] + v[i];
    }
  }
  // sum of [0, a)   0 <= a <= n
  T sum(int a) const {
    assert(0 <= a);
    assert(a < (int)cs.size());
    return cs[a];
  }
  // sum of [a, b)   0 <= a <= b <= n
  T sum(int a, int b) const {
    assert(0 <= a);
    assert(a <= b);
    assert(b < (int)cs.size());
    return cs[b] - cs[a];
  }
};


// Two-dimensional cumulative sums (CumulativeSum2D of the original): cs[a][b] is the sum of v[0, a) x [0, b) for the
// n x m matrix v, so cs has n + 1 rows of m + 1 elements.  Differences from the original: the fields n and m are not
// kept (n = cs.size() - 1, m = cs[0].size() - 1); the constructor fills the table in one pass over the rows (the running
// sum of the row plus the entry above) instead of a row-wise pass followed by a column-wise pass (the same table); the
// queries are const, and every row access is written as a separate declaration.  The constructor still requires a
// non-empty rectangular matrix (the asserts of the original).
// Preconditions: n, m < 2^31 - 1 and every prefix sum, running row sum and the table entries fit in T.
template <class T = long long> class CumulativeSum2D {
  std::vector<std::vector<T>> cs;

public:
  CumulativeSum2D(const std::vector<std::vector<T>> &v)
      : cs(v.size() + 1, std::vector<T>(v.empty() ? 1 : v[0].size() + 1, T(0))) {
    int n = (int)v.size();
    assert(n > 0);
    int m = (int)v[0].size();
    assert(m > 0);
    for (int i = 0; i < n; i++) {
      int len = (int)v[i].size();
      assert(len == m);
    }
    for (int i = 0; i < n; i++) {
      T run = T(0);
      for (int j = 0; j < m; j++) {
        T x = v[i][j];
        run = run + x;
        T up = cs[i][j + 1];
        cs[i + 1][j + 1] = up + run;
      }
    }
  }
  // sum of [0, a) x [0, b)
  T sum(int a, int b) const {
    assert(0 <= a);
    int rows = (int)cs.size();
    assert(a < rows);
    assert(0 <= b);
    int cols = (int)cs[a].size();
    assert(b < cols);
    T x = cs[a][b];
    return x;
  }
  // sum of [a1, a2) x [b1, b2)
  T sum(int a1, int b1, int a2, int b2) const {
    assert(0 <= a1);
    assert(a1 <= a2);
    int rows = (int)cs.size();
    assert(a2 < rows);
    assert(0 <= b1);
    assert(b1 <= b2);
    int cols = (int)cs[a2].size();
    assert(b2 < cols);
    T p = cs[a2][b2];
    T q = cs[a1][b2];
    T r = cs[a2][b1];
    T s = cs[a1][b1];
    return p - q - r + s;
  }
};
template class CumulativeSum<long long>;
template class CumulativeSum2D<long long>;
template class CumulativeSum<int>;
template class CumulativeSum2D<int>;

} // namespace cp

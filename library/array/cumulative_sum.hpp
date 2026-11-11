#pragma once
#include <cassert>
#include <vector>

namespace cp {

// One- and two-dimensional prefix sums (experiments/library/cpp/array/cumulative_sum.hpp). The element type T is a
// template parameter; the arrays cannot be updated after construction.
// Differences from the original: std:: qualification and the namespace only.

/**
 * @brief 1次元累積和
 * 構築 O(n)
 * 更新不可
 * 部分和 O(1)
 * @tparam T
 */
template <class T = long long> class CumulativeSum {
  std::vector<T> cs;
  int n;

public:
  CumulativeSum(const std::vector<T> &v) : cs(v.size() + 1), n(v.size()) {
    cs[0] = T(0);
    for (int i = 1; i <= n; i++) {
      cs[i] = cs[i - 1] + v[i - 1];
    }
  }
  // [0, a) 0-n
  T sum(int a) {
    assert(0 <= a && a <= n);
    return cs[a];
  }
  // [a, b) 0-a-b-n
  T sum(int a, int b) {
    assert(0 <= a && a <= b && b <= n);
    return cs[b] - cs[a];
  }
};

/**
 * @brief 2次元累積和
 * 構築 O(nm)
 * 更新不可
 * 部分和 O(1)
 * @tparam T
 */
template <class T = long long> class CumulativeSum2D {
  std::vector<std::vector<T>> cs;
  int n, m;

public:
  CumulativeSum2D(const std::vector<std::vector<T>> &v) {
    n = v.size();
    assert(n > 0);
    m = v[0].size();
    assert(m > 0);
    for (int i = 1; i < n; i++) {
      assert(int(v[i].size()) == m);
    }
    cs.resize(n + 1);
    cs[0] = std::vector<T>(m + 1, T(0));
    for (int i = 1; i <= n; i++) {
      cs[i].reserve(m + 1);
      cs[i].emplace_back(T(0));
      for (int j = 0; j < m; j++) {
        cs[i].emplace_back(cs[i].back() + v[i - 1][j]);
      }
    }
    for (int i = 2; i <= n; i++) {
      for (int j = 1; j <= m; j++)
        cs[i][j] += cs[i - 1][j];
    }
  }
  // [0, a) 0-n
  // [0, b) 0-m
  T sum(int a, int b) {
    assert(0 <= a && a <= n);
    assert(0 <= b && b <= m);
    return cs[a][b];
  }
  // [a1, a2) 0-a1-a2-n
  // [b1, b2) 0-b1-b2-m
  T sum(int a1, int b1, int a2, int b2) {
    assert(0 <= a1 && a1 <= a2 && a2 <= n);
    assert(0 <= b1 && b1 <= b2 && b2 <= m);
    return cs[a2][b2] - cs[a1][b2] - cs[a2][b1] + cs[a1][b1];
  }
};

template class CumulativeSum<long long>;
template class CumulativeSum2D<long long>;
template class CumulativeSum<int>;
template class CumulativeSum2D<int>;

} // namespace cp

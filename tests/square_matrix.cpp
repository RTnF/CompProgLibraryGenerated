#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number/square_matrix.hpp"
#include <array>
#include <cassert>
#include <climits>
#include <random>
#include <type_traits>
#include <utility>

using M2 = cp::SquareMatrix<long long, 2>;
using M3 = cp::SquareMatrix<long long, 3>;

// The original API: an aggregate with the public array, row references, pow(long long) const.
static_assert(std::is_aggregate_v<M2> && std::is_trivial_v<M2> && std::is_standard_layout_v<M2>);
static_assert(std::is_same_v<decltype(&M2::pow), M2 (M2::*)(long long) const>);
static_assert(std::is_same_v<decltype(std::declval<M2 &>()[0]), long long (&)[2]>);
static_assert(std::is_same_v<decltype(std::declval<const M2 &>()[0]), const long long (&)[2]>);
static_assert(std::is_same_v<decltype(M2::mat), long long[2][2]>);

template <int n> using Naive = std::array<std::array<long long, n>, n>;

template <int n> Naive<n> naive_mul(const Naive<n> &a, const Naive<n> &b) {
  Naive<n> c{};
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++)
      for (int k = 0; k < n; k++) c[i][j] += a[i][k] * b[k][j];
  return c;
}

template <int n, class V> void expect(const cp::SquareMatrix<long long, n> &m, const V &v) {
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) assert(m[i][j] == v[i][j]);
}

template <int n> void random_checks(std::mt19937_64 &random) {
  using M = cp::SquareMatrix<long long, n>;
  for (int round = 0; round < 200; round++) {
    M a, b;
    Naive<n> va, vb;
    for (int i = 0; i < n; i++)
      for (int j = 0; j < n; j++) {
        a[i][j] = va[i][j] = static_cast<long long>(random() % 7) - 3;
        b[i][j] = vb[i][j] = static_cast<long long>(random() % 7) - 3;
      }
    Naive<n> sum, diff, neg;
    for (int i = 0; i < n; i++)
      for (int j = 0; j < n; j++) {
        sum[i][j] = va[i][j] + vb[i][j];
        diff[i][j] = va[i][j] - vb[i][j];
        neg[i][j] = -va[i][j];
      }
    expect(a + b, sum);
    expect(a - b, diff);
    expect(-a, neg);
    expect(+a, va);
    expect(a * b, naive_mul<n>(va, vb));
    M c = a;
    c += b;
    expect(c, sum);
    c = a;
    c -= b;
    expect(c, diff);
    c = a;
    c *= b;
    expect(c, naive_mul<n>(va, vb));
    c = a;
    c *= c; // the operand aliases the receiver
    expect(c, naive_mul<n>(va, va));
    assert(a == a && !(a != a));
    assert((a == b) == (va == vb) && (a != b) == (va != vb));
    // pow by repeated squaring against repeated multiplication
    Naive<n> p{};
    for (int i = 0; i < n; i++) p[i][i] = 1;
    for (int e = 0; e <= 9; e++) {
      expect(a.pow(e), p);
      p = naive_mul<n>(p, va);
    }
  }
}

int main() {
  // O and I
  M3 o = M3::O(), id = M3::I();
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 3; j++) {
      assert(o[i][j] == 0);
      assert(id[i][j] == (i == j));
    }
  std::mt19937_64 random(20261123);
  random_checks<1>(random);
  random_checks<2>(random);
  random_checks<3>(random);
  // Fibonacci by pow; pow(0) is the identity; aggregate initialization
  M2 f{{{1, 1}, {1, 0}}};
  assert(f.pow(90)[0][1] == 2880067194370816120LL);
  assert(f.pow(0) == M2::I());
  // pow(1) of extreme values does not square after the last bit (fixed in the original)
  cp::SquareMatrix<long long, 1> big{{{LLONG_MAX}}};
  assert(big.pow(1)[0][0] == LLONG_MAX);
  cp::SquareMatrix<long long, 1> small{{{LLONG_MIN}}};
  assert(small.pow(1)[0][0] == LLONG_MIN);
  // another element type
  cp::SquareMatrix<double, 2> d{{{0.5, 0.0}, {0.0, 2.0}}};
  assert((d * d)[0][0] == 0.25 && (d * d)[1][1] == 4.0);
  return 0;
}

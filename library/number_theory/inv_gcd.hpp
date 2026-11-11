#pragma once
#include <utility>

#include "safe_mod.hpp"

namespace cp {

// The extended Euclidean algorithm of the AtCoder Library (inv_gcd in experiments/library/cpp/fps/convolution.hpp).
// Returns (g, x) with g = gcd(a, b) and x * a == g (mod b), 0 <= x < b / g (a is taken modulo b; g = b when b | a).
// Precondition: 1 <= b. Time O(log b), extra space O(1).
constexpr std::pair<long long, long long> inv_gcd(long long a, long long b) {
  a = safe_mod(a, b);
  if (a == 0)
    return {b, 0};

  // Contracts:
  // [1] s - m0 * a = 0 (mod b)
  // [2] t - m1 * a = 0 (mod b)
  // [3] s * |m1| + t * |m0| <= b
  long long s = b, t = a;
  long long m0 = 0, m1 = 1;

  while (t) {
    long long u = s / t;
    s -= t * u;
    m0 -= m1 * u; // |m1 * u| <= |m1| * s <= b

    // [3]:
    // (s - t * u) * |m1| + t * |m0 - m1 * u|
    // <= s * |m1| - t * u * |m1| + t * (|m0| + |m1| * u)
    // = s * |m1| + t * |m0| <= b

    auto tmp = s;
    s = t;
    t = tmp;
    tmp = m0;
    m0 = m1;
    m1 = tmp;
  }
  // by [3]: |m0| <= b/g
  // by g != b: |m0| < b/g
  if (m0 < 0)
    m0 += b / s;
  return {s, m0};
}

} // namespace cp

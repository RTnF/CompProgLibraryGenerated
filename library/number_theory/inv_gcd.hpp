#pragma once
#include <vector>

namespace cp {

// The extended Euclidean algorithm of the AtCoder Library (inv_gcd in experiments/library/cpp/fps/convolution.hpp).
// Differences: the pair (g, x) is written to out[0], out[1] instead of being returned, the case a == 0 (mod b) is not a
// separate return (the loop is skipped and the same pair (b, 0) results), and safe_mod(a, b) is written out.
// Results: with a' = a mod b in [0, b), g = out[0] = gcd(a', b) (g = b if a' == 0) and x = out[1] satisfies 0 <= x < b / g
// and x * a' == g (mod b).
// Preconditions: 1 <= b (<= 2^63 - 1), out.size() >= 2. No signed overflow occurs for any such a, b (every intermediate
// value has absolute value at most b). Time O(log b) iterations, extra space O(1).
inline void inv_gcd(std::vector<long long> &out, long long a, long long b) {
  a = a % b;
  if (a < 0) {
    a = a + b;
  }
  long long s = b;
  long long t = a;
  long long m0 = 0;
  long long m1 = 1;
  while (t != 0) {
    long long u = s / t;
    s = s - t * u;
    m0 = m0 - m1 * u;
    long long tmp = s;
    s = t;
    t = tmp;
    tmp = m0;
    m0 = m1;
    m1 = tmp;
  }
  if (m0 < 0) {
    m0 = m0 + b / s;
  }
  out[0] = s;
  out[1] = m0;
}

} // namespace cp

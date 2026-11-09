#pragma once
#include <cassert>
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// A rational number s * n / d in sign-magnitude form: s is 1 for a negative value and 0 otherwise, n and d are the
// numerator and denominator magnitudes. Derived from experiments/library/cpp/number/ratio.hpp (Ratio::normalize).
// Differences: the sign is a separate unsigned field (so every field is a 64 bit unsigned integer), and normalize is
// a friend function returning a new value instead of mutating the object.
// normalize(r) divides n and d by their greatest common divisor (Euclid's algorithm, written out in the function);
// a zero numerator gives (0, 0, 1) and otherwise the sign is kept. Precondition: d != 0 (checked by assert).
// Time O(log(min(n, d))) iterations (at most 2 * (bit width of d) + 2), extra space O(1).
struct Ratio {
  unsigned long long s, n, d;
  Ratio(unsigned long long s_, unsigned long long n_, unsigned long long d_) : s(s_), n(n_), d(d_) {}
  friend Ratio normalize(const Ratio &r) {
    assert(r.d != 0);
    unsigned long long x = r.n;
    unsigned long long y = r.d;
    while (y != 0) {
      unsigned long long t = x % y;
      x = y;
      y = t;
    }
    if (r.n == 0) {
      return Ratio(0, 0, 1);
    }
    return Ratio(r.s, r.n / x, r.d / x);
  }
};

} // namespace cp

#pragma once
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// Greatest common divisor by Euclid's algorithm; gcd(0, 0) = 0 and gcd(a, 0) = a (as std::gcd on unsigned values).
// Time O(log(min(a, b))) iterations (at most 2 * (bit width of b) + 2), extra space O(1).
inline unsigned long long gcd_u64(unsigned long long a, unsigned long long b) {
  while (b != 0) {
    unsigned long long t = a % b;
    a = b;
    b = t;
  }
  return a;
}

} // namespace cp

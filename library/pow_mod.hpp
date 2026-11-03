#pragma once
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// base^exp mod m by binary exponentiation, for 1 <= m <= 2^32 (so every product stays below 2^64).
// The result is below m; m == 1 gives 0, and exp == 0 gives 1 % m.
// Precondition: 1 <= m <= 4294967296 (violations are outside the verified contract). base is any 64 bit value.
// Time O(log exp) multiplications, extra space O(1).

inline unsigned long long pow_mod(unsigned long long base, unsigned long long exp, unsigned long long m) {
  unsigned long long result = 1 % m;
  unsigned long long b = base % m;
  unsigned long long e = exp;
  while (e != 0) {
    if ((e & 1) != 0) {
      result = result * b % m;
    }
    b = b * b % m;
    e = e >> 1;
  }
  return result;
}

} // namespace cp

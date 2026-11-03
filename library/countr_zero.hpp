#pragma once
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// Number of trailing zero bits, as std::countr_zero of C++20 on unsigned long long (countr_zero_constexpr in
// experiments/library/cpp/fps/convolution.hpp). Differences: the shift test n & (1 << x) is written as a division by 2 (the
// verified expression language has bitwise operators on unsigned types only, and 1 << x overflows int), the argument is
// unsigned long long (every unsigned int value is accepted too), and the result for n == 0 is 64 as in std::countr_zero
// (the original loops forever there).
// Returns the largest r with 2^r dividing n for n != 0 (so 0 <= r <= 63), and 64 for n == 0.
// Time O(r + 1) iterations (at most 64), extra space O(1).
inline int countr_zero_u64(unsigned long long n) {
  int x = 0;
  while (x < 64 && n % 2 == 0) {
    n = n / 2;
    x = x + 1;
  }
  return x;
}

} // namespace cp

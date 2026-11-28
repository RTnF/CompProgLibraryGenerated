#pragma once
#include <bit>

namespace cp {

// Number of trailing zero bits, or 64 for zero.
inline int countr_zero_u64(unsigned long long n) {
  return std::countr_zero(n);
}

} // namespace cp

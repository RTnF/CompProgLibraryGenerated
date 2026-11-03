#pragma once
#include <cassert>
#include "safe_mod.hpp"
#include "floor_sum_unsigned.hpp"

namespace cp {
// Requires 0 <= n < 2^32, 0 < m < 2^32. a,b may use all signed64 values.
// Returns the mathematical floor sum when representable in signed64.
// Otherwise GCC 13.3 LP64 conversion decodes the result modulo 2^64.
// Time O(log m), additional space O(1).
inline std::int64_t floor_sum(std::int64_t n, std::int64_t m, std::int64_t a, std::int64_t b) {
  assert(0 <= n && n < (1ll << 32));
  assert(1 <= m && m < (1ll << 32));
  std::uint64_t ans = 0;
  if (a < 0) {
    std::uint64_t a2 = safe_mod(a, m);
    ans -= (std::uint64_t)n * (n - 1) / 2 * ((a2 - a) / m);
    a = a2;
  }
  if (b < 0) {
    std::uint64_t b2 = safe_mod(b, m);
    ans -= (std::uint64_t)n * ((b2 - b) / m);
    b = b2;
  }
  return ans + floor_sum_unsigned(n, m, a, b);
}

} // namespace cp

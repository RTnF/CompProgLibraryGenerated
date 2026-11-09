#pragma once
#include <cstdint>

namespace cp {
// Requires m > 0. Returns the representative in [0, m).
// Constant time and constant additional space for fixed-width integers.
constexpr std::int64_t safe_mod(std::int64_t x, std::int64_t m) {
  x %= m;
  if (x < 0) {
    x += m;
  }
  return x;
}
}  // namespace cp

#pragma once
#include <cstdint>

namespace cp {

// C++17 replacement for bit_width on uint64_t, including zero.
inline constexpr int bit_width_u64(std::uint64_t value) {
  int result = 0;
  while (value != 0) {
    ++result;
    value /= 2;
  }
  return result;
}

} // namespace cp

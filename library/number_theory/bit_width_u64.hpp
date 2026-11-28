#pragma once
#include <bit>
#include <cstdint>

namespace cp {

// Number of bits needed to represent value, or zero for zero.
inline constexpr int bit_width_u64(std::uint64_t value) {
  return std::bit_width(value);
}

} // namespace cp

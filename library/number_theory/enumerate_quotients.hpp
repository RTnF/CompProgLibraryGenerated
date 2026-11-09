#pragma once
#include <cstdint>
#include <vector>

namespace cp {

// Ascending list of the positive values floor(n / x) over x >= 1 (empty for n = 0).
// Supported range: 1 <= n <= 2^64 - 2^32 (the specification and the tests cover this range).
inline std::vector<std::uint64_t> enumerate_quotients(std::uint64_t n) {
  std::uint64_t ok = 4294967296ull;
  std::uint64_t ng = 0;
  while (ok - ng > 1) {
    const std::uint64_t k = (ok + ng) / 2;
    if (k * (k + 1) >= n) {
      ok = k;
    } else {
      ng = k;
    }
  }
  const std::uint64_t p = n / ok;
  std::vector<std::uint64_t> ret;
  ret.reserve(p + ok - 1);
  for (std::uint64_t i = 1; i <= p; ++i) {
    ret.emplace_back(i);
  }
  for (std::uint64_t i = ok - 1; i >= 1; --i) {
    ret.emplace_back(n / i);
  }
  return ret;
}

} // namespace cp

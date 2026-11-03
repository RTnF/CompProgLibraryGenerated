#pragma once
#include "bit_width_u64.hpp"
#include <cassert>
#include <limits>
#include <vector>

namespace cp {

// Preconditions: kmax > 0, size <= INT_MAX, and all successors in [0,size).
inline std::vector<std::vector<int>> doubling(const std::vector<int> &v,
                                             std::uint64_t kmax) {
  assert(kmax > 0);
  assert(v.size() <= static_cast<std::size_t>(std::numeric_limits<int>::max()));
  const int n = static_cast<int>(v.size());
  for (int i = 0; i < n; ++i) {
    assert(0 <= v[i]);
    assert(v[i] < n);
  }
  const int w = bit_width_u64(kmax);
  std::vector<std::vector<int>> ret(w);
  ret[0].assign(v.begin(), v.end());
  for (int i = 1; i < w; ++i) {
    ret[i].reserve(n);
    for (int j = 0; j < n; ++j) {
      ret[i].emplace_back(ret[i - 1][ret[i - 1][j]]);
    }
  }
  return ret;
}

} // namespace cp

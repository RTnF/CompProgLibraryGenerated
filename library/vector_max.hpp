#pragma once
#include <cassert>
#include <vector>

namespace cp {

// Maximum element of a non-empty vector of long long.
// Preconditions: 0 < x.size() < 2^31; an empty vector stops the program at an assert.
// Time O(x.size()), extra space O(1).
template <class T> inline T vector_max(const std::vector<T> &x) {
  assert(x.size() != 0);
  T m = x[0];
  for (int i = 1; i < (int)x.size(); i++) {
    if (x[i] > m) {
      m = x[i];
    }
  }
  return m;
}

template long long vector_max<long long>(const std::vector<long long> &);

} // namespace cp

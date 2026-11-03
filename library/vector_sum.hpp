#pragma once
#include <vector>

namespace cp {

// Sum of all elements of a vector of long long (the empty vector gives 0).
// Preconditions: x.size() < 2^31 and every partial sum x[0] + ... + x[k] fits in long long
// (a signed overflow is outside the verified contract). Time O(x.size()), extra space O(1).
template <class T> inline T vector_sum(const std::vector<T> &x) {
  T s = 0;
  for (int i = 0; i < (int)x.size(); i++) {
    s += x[i];
  }
  return s;
}

template long long vector_sum<long long>(const std::vector<long long> &);

} // namespace cp

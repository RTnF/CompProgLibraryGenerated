#pragma once
#include <vector>

namespace cp {

// Sets every element of x to value. Precondition: x.size() < 2^31. Time O(x.size()), extra space O(1).
template <class T> inline void vector_fill(std::vector<T> &x, T value) {
  for (int i = 0; i < (int)x.size(); i++) {
    x[i] = value;
  }
}

template void vector_fill<long long>(std::vector<long long> &, long long);

} // namespace cp

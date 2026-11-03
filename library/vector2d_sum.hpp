#pragma once
#include <vector>

namespace cp {

// Sum of all elements of a vector of vectors (the empty vector and empty rows give 0). Time O(total size), extra space
// O(1). The accesses g.size(), g[i].size() and g[i][j] are written as separate declarations (the verified expression
// language allows a row access only as the right-hand side of a declaration or an assignment).
// Preconditions: g.size() < 2^31, every row has fewer than 2^31 elements, and every partial sum fits in T (a signed
// overflow is outside the verified contract).
template <class T> inline T vector2d_sum(const std::vector<std::vector<T>> &g) {
  T s = 0;
  int rows = (int)g.size();
  for (int i = 0; i < rows; i++) {
    int cols = (int)g[i].size();
    for (int j = 0; j < cols; j++) {
      T x = g[i][j];
      s += x;
    }
  }
  return s;
}

template long long vector2d_sum<long long>(const std::vector<std::vector<long long>> &);

} // namespace cp

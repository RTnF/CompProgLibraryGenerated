#pragma once
#include <vector>

namespace cp {

// All-pairs shortest paths (Warshall-Floyd) on a distance matrix stored row-major in `d` (d[i * n + j] is the length
// of the edge i -> j, d[i * n + i] == 0 for a graph without loops; "no edge" is a large value).
// (MatrixGraph::warshall_floyd in experiments/library/cpp/graph/warshall_floyd.hpp, without the parent matrix.)
// Preconditions: d.size() == n * n, n * n < 2^31, every entry is in [0, 2^62)
// (so the sum of two entries does not overflow). Time O(n^3), extra space O(1).
template <class T> inline void floyd_warshall(std::vector<T> &d, int n) {
  for (int k = 0; k < n; k++) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        T via = d[i * n + k] + d[k * n + j];
        if (via < d[i * n + j]) {
          d[i * n + j] = via;
        }
      }
    }
  }
}

template void floyd_warshall<long long>(std::vector<long long> &, int);

// The same on a square matrix stored as a vector of rows (`d[i][j]`, `d.size() == n`, every row has `n` elements); this
// is the form of MatrixGraph::mat in the original.  Every row access is written as a separate declaration.
// Preconditions: every row has d.size() elements, every entry is in [0, 2^62).  Time O(n^3), extra space O(1).
template <class T> inline void floyd_warshall(std::vector<std::vector<T>> &d) {
  int n = (int)d.size();
  for (int k = 0; k < n; k++) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        T dik = d[i][k];
        T dkj = d[k][j];
        T via = dik + dkj;
        T dij = d[i][j];
        if (via < dij) {
          d[i][j] = via;
        }
      }
    }
  }
}

template void floyd_warshall<long long>(std::vector<std::vector<long long>> &);

} // namespace cp

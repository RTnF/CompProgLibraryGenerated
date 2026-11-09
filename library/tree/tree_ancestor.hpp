#pragma once
#include <vector>

namespace cp {

// The i-th ancestor of v from a doubling table (Tree::ancestor in experiments/library/cpp/tree/tree.hpp). Differences: the
// table `anc` (anc[k][x] is the 2^k-th ancestor of x, as built by `doubling`) is a parameter instead of the member
// ancestor_, and the test of the bit j of i is written (i / j) % 2 == 1, which is the same for 0 <= i and j a power of two
// (the verified expression language has bitwise operators for unsigned types only).
// Returns the vertex reached from v after i steps to the parent. Preconditions: 0 <= i < 2^30, 0 <= v < n, and for every
// k with 2^k <= i the row anc[k] has n entries, all in [0, n); n < 2^31.
// Time O(log i), extra space O(1).
inline int tree_ancestor(const std::vector<std::vector<int>> &anc, int v, int i) {
  int k = 0;
  int j = 1;
  while (j <= i) {
    if ((i / j) % 2 == 1) {
      v = anc[k][v];
    }
    j = j * 2;
    k = k + 1;
  }
  return v;
}

} // namespace cp

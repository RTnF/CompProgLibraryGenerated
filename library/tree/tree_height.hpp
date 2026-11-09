#pragma once
#include <vector>

namespace cp {

// The distance from each vertex to its farthest vertex, from the costs of the root paths measured from the two ends of a
// diameter (the last loop of Tree::height in experiments/library/cpp/tree/tree.hpp): h[i] = max(cost_depth0[i],
// cost_depth1[i]). The caller computes cost_depth0 and cost_depth1 with `tree_root` rooted at the two ends of a diameter
// (the farthest vertex from any root is one end; the farthest vertex from that end is the other). Differences: the two
// cost-depth vectors and the output vector are parameters, and `std::max` is written as a comparison and a branch.
// Preconditions: n >= 0, n < 2^31, and cost_depth0, cost_depth1 and h have at least n entries. Time O(n), extra space O(1).
template <class Cost>
inline void tree_height(const std::vector<Cost> &cost_depth0, const std::vector<Cost> &cost_depth1, std::vector<Cost> &h,
                        int n) {
  for (int i = 0; i < n; i++) {
    Cost a = cost_depth0[i];
    Cost b = cost_depth1[i];
    if (a < b) {
      h[i] = b;
    } else {
      h[i] = a;
    }
  }
}

template void tree_height<long long>(const std::vector<long long> &, const std::vector<long long> &,
                                     std::vector<long long> &, int);

} // namespace cp

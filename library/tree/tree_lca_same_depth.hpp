#pragma once
#include <bit>
#include <vector>

namespace cp {

// Lowest common ancestor of two vertices of the same depth, from a doubling table (the second half of
// Tree::lowest_common_ancestor in experiments/library/cpp/tree/tree.hpp, after the deeper vertex was lifted with
// `tree_ancestor`). The table `anc` (anc[k][x] is the 2^k-th ancestor of x, as built by `doubling`) and the
// common depth are parameters. The descent starts at the highest level k with 2^k <= depth.
// `depth` is the depth of both u and v. Returns the vertex where the paths from u and v to the root first meet (u itself
// if u == v). Preconditions: 0 <= depth < 2^30, u and v are vertices of a rooted tree (root = its own parent) with the
// depth `depth`, and for every level k <= max(0, floor(log2(depth))) the row anc[k] has n entries, all in [0, n);
// 0 <= u, v < n; n < 2^31.
// Time O(1 + log(depth + 1)), extra space O(1).
inline int tree_lca_same_depth(const std::vector<std::vector<int>> &anc, int u, int v, int depth) {
  if (u == v) {
    return u;
  }
  const int width = std::bit_width(static_cast<unsigned>(depth));
  int k = width > 0 ? width - 1 : 0;
  while (k >= 0) {
    int nu = anc[k][u];
    int nv = anc[k][v];
    if (nu != nv) {
      u = nu;
      v = nv;
    }
    k = k - 1;
  }
  int result = anc[0][u];
  return result;
}

} // namespace cp

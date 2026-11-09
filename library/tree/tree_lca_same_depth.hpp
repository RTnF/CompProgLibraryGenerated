#pragma once
#include <vector>

namespace cp {

// Lowest common ancestor of two vertices of the same depth, from a doubling table (the second half of
// Tree::lowest_common_ancestor in experiments/library/cpp/tree/tree.hpp, after the deeper vertex was lifted with
// `tree_ancestor`). Differences: the table `anc` (anc[k][x] is the 2^k-th ancestor of x, as built by `doubling`) and the
// common depth are parameters, `bit_width` is replaced by a loop that finds the highest level top with 2^top <= depth
// (the original starts one level higher, where both jumps reach the root and nothing moves), and the descent over the
// levels is a `while` loop. The final table read is written as a declaration, because the verified expression language
// allows a row access only as the right-hand side of a declaration or an assignment.
// `depth` is the depth of both u and v. Returns the vertex where the paths from u and v to the root first meet (u itself
// if u == v). Preconditions: 0 <= depth < 2^30, u and v are vertices of a rooted tree (root = its own parent) with the
// depth `depth`, and for every level k <= max(0, floor(log2(depth))) the row anc[k] has n entries, all in [0, n);
// 0 <= u, v < n; n < 2^31.
// Time O(log depth), extra space O(1).
inline int tree_lca_same_depth(const std::vector<std::vector<int>> &anc, int u, int v, int depth) {
  int top = 0;
  int p = 1;
  while (p * 2 <= depth) {
    p = p * 2;
    top = top + 1;
  }
  if (u == v) {
    return u;
  }
  int k = top;
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

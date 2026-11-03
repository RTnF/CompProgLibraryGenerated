#pragma once
#include <vector>

namespace cp {

// The path between two vertices of a rooted tree (Tree::path in experiments/library/cpp/tree/tree.hpp). Differences: instead
// of a second depth-first search from `from` it follows the parent array of the tree rooted at `from` (as built by
// `tree_root(..., from, n)`) from `to` up to `from`, and it writes the vertices to the caller's vector `out` and returns their
// number instead of returning a vector. As in the original, the path lists the vertices from `to` to `from`:
// out[0] == to, out[i + 1] == parent[out[i]], out[len - 1] == from.
// Preconditions: following parent from `to` reaches `from` after exactly m >= 0 steps and not before (for the output of
// tree_root this holds for every `to` reachable from `from`, with m == depth[to] < n), every vertex on the way, including
// `to` and `from`, is in [0, parent.size()), and out.size() >= m + 1. m + 1 < 2^31.
// Returns len == m + 1; out[len ..] is not touched. Time O(m), extra space O(1).
inline int tree_path(const std::vector<int> &parent, std::vector<int> &out, int from, int to) {
  int k = 0;
  int v = to;
  while (v != from) {
    out[k] = v;
    k = k + 1;
    v = parent[v];
  }
  out[k] = from;
  return k + 1;
}

} // namespace cp

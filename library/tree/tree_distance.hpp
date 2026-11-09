#pragma once
#include <vector>

namespace cp {

// Distance between two vertices of a rooted tree from the costs of the root paths (Tree::distance in
// experiments/library/cpp/tree/tree.hpp): cost_depth[u] + cost_depth[v] - cost_depth[lca] * 2, where `lca` is the lowest
// common ancestor of u and v (computed by the caller, e.g. with `tree_ancestor` and `tree_lca_same_depth`). Differences: the
// cost-depth vector (as filled by `tree_root`) and the common ancestor are parameters instead of the members cost_depth_
// and root_, and the three table reads are separate declarations (the verified expression language allows a vector read
// only as the right-hand side of a declaration or an assignment).
// Preconditions: 0 <= u, v, lca < cost_depth.size() < 2^31, and no overflow: cost_depth[u] + cost_depth[v],
// cost_depth[lca] * 2 and the final difference fit in Cost. Time O(1), extra space O(1).
template <class Cost> inline Cost tree_distance(const std::vector<Cost> &cost_depth, int u, int v, int lca) {
  Cost a = cost_depth[u];
  Cost b = cost_depth[v];
  Cost c = cost_depth[lca];
  return a + b - c * 2;
}

template long long tree_distance<long long>(const std::vector<long long> &, int, int, int);

} // namespace cp

#pragma once
#include <vector>

namespace cp {

// The costs of the arcs of a tree given by an edge list (the cost part of the constructor Tree(int root, vector<int> &from,
// vector<int> &to, vector<Cost> &cost) in experiments/library/cpp/tree/tree.hpp). The cost of the edge i is the cost of both
// of its arcs, which `tree_arcs_from_list` writes to the positions 2 * i and 2 * i + 1: ac[2 * i] = ac[2 * i + 1] = cost[i]
// for i = 0, ..., m - 1. For the constructor without costs the original uses the cost 1 for every edge: pass a cost vector of
// ones. Differences: the costs are written to a caller-provided vector instead of the adjacency lists.
// Preconditions: 0 <= m < 2^29, cost.size() >= m and ac.size() >= 2 * m. Time O(m), extra space O(1).
template <class Cost> inline void tree_arc_costs(const std::vector<Cost> &cost, std::vector<Cost> &ac, int m) {
  for (int i = 0; i < m; i++) {
    Cost c = cost[i];
    ac[2 * i] = c;
    ac[2 * i + 1] = c;
  }
}

template void tree_arc_costs<long long>(const std::vector<long long> &, std::vector<long long> &, int);

} // namespace cp

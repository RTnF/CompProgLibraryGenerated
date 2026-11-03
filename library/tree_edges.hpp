#pragma once
#include <vector>

namespace cp {

// The arcs of the tree given by a parent array (the adjacency construction of the constructor Tree(int root, vector<int>
// &parent) in experiments/library/cpp/tree/tree.hpp). For every i with parent[i] != i and 0 <= parent[i] < n, in increasing
// order of i, the two arcs parent[i] -> i and i -> parent[i] are appended to the arc list (from[k], to[k]) in this order,
// exactly as the original appends them to the adjacency lists adj[parent[i]] and adj[i]. Differences: the arcs are written
// to two caller-provided vectors instead of adjacency lists (feed them to `csr_build` to get the CSR arrays that
// `tree_root` takes: the stable counting sort keeps the order of the arcs of each vertex), and the test of the parent is
// written as nested conditions. Returns the number m of arcs written.
// Preconditions: n >= 0, parent.size() >= n, from.size() >= 2 * n and to.size() >= 2 * n (at most two arcs per i), and
// n < 2^30. Time O(n), extra space O(1).
inline int tree_edges_from_parent(const std::vector<int> &parent, std::vector<int> &from, std::vector<int> &to, int n) {
  int m = 0;
  for (int i = 0; i < n; i++) {
    int p = parent[i];
    if (p != i) {
      if (0 <= p) {
        if (p < n) {
          from[m] = p;
          to[m] = i;
          m = m + 1;
          from[m] = i;
          to[m] = p;
          m = m + 1;
        }
      }
    }
  }
  return m;
}

} // namespace cp

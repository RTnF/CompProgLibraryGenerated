#pragma once
#include <vector>

namespace cp {

// The arcs of a tree given by an edge list (the adjacency construction of the constructors Tree(int root, vector<int>
// &from, vector<int> &to) and Tree(int root, vector<int> &from, vector<int> &to, vector<Cost> &cost) in
// experiments/library/cpp/tree/tree.hpp). For i = 0, ..., m - 1 (m = from.size() = n - 1 edges) the two arcs
// from[i] -> to[i] and to[i] -> from[i] are written to the positions 2 * i and 2 * i + 1 of the arc list (af, at), the
// order in which the original appends them to the adjacency lists. Differences: the arcs are written to two
// caller-provided vectors instead of adjacency lists (feed them to `csr_build`, which keeps the order of the arcs of each
// vertex), and the range assertions of the original are preconditions. The costs of the arcs (the cost of an edge for both
// of its arcs, or 1 for the constructor without costs) are not written here; copying them is a second loop of the same
// shape that is not verified yet.
// Preconditions: 0 <= m < 2^29, from.size() >= m, to.size() >= m, af.size() >= 2 * m and at.size() >= 2 * m.
// Time O(m), extra space O(1).
inline void tree_arcs_from_list(const std::vector<int> &from, const std::vector<int> &to, std::vector<int> &af,
                                std::vector<int> &at, int m) {
  for (int i = 0; i < m; i++) {
    int a = from[i];
    int b = to[i];
    af[2 * i] = a;
    at[2 * i] = b;
    af[2 * i + 1] = b;
    at[2 * i + 1] = a;
  }
}

} // namespace cp

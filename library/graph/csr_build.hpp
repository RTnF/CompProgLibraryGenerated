#pragma once
#include <vector>

namespace cp {

// Builds the CSR arrays used by the graph algorithms of this library from an edge list (the arcs of ListGraph::add_edge;
// for ListGraph::add_bidirectional_edge list both directions). Arc i goes from from[i] to to[i]. Afterwards the arcs
// leaving v are target[head[v] .. head[v + 1]), in the order of the input.
// Preconditions: from.size() == to.size() == target.size() == m, head.size() == n + 1 and every entry of head is 0,
// pos.size() == n (scratch), every from[i] and to[i] is in [0, n), n < 2^31 - 2, m < 2^31 - 1.
// Result: head[0] == 0, head is non-decreasing, head[n] == m, and for all u, w: there is an arc u -> w in the CSR
// arrays if and only if some i has from[i] == u and to[i] == w.
// Time O(n + m), extra space O(1) beyond `pos`.
inline void csr_build(const std::vector<int> &from, const std::vector<int> &to, std::vector<int> &head,
                      std::vector<int> &target, std::vector<int> &pos, int n) {
  int m = from.size();
  for (int i = 0; i < m; i++) {
    int f = from[i];
    head[f + 1] = head[f + 1] + 1;
  }
  for (int v = 0; v < n; v++) {
    head[v + 1] = head[v + 1] + head[v];
  }
  for (int v = 0; v < n; v++) {
    pos[v] = head[v];
  }
  for (int i = 0; i < m; i++) {
    int f = from[i];
    int p = pos[f];
    target[p] = to[i];
    pos[f] = p + 1;
  }
}

} // namespace cp

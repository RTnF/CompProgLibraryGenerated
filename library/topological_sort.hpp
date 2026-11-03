#pragma once
#include <vector>

namespace cp {

// Topological sort of a directed graph by Kahn's algorithm (ListGraph::topological_sort in
// experiments/library/cpp/graph/topological_sort.hpp). Differences: the graph is given by CSR arrays instead of adjacency
// lists (the edges leaving v are target[head[v] .. head[v + 1])), the queue replaces the stack, the order is written to
// the caller's vector `order`, and the function returns the number k of vertices written (n if and only if the graph has
// no cycle; the original returns an empty vector for a graph with a cycle).
// Preconditions: n >= 0, head.size() == n + 1, head[0] == 0, head is non-decreasing, head[n] == target.size(), every
// target[p] is in [0, n), indeg.size() == n and every entry of indeg is 0 (scratch space; it is overwritten),
// order.size() == n, n and target.size() < 2^31 - 2.
// Result: order[0..k) are distinct vertices; every in-neighbor of order[j] is some order[i] with i < j; and every vertex
// not in order[0..k) has an in-neighbor that is also not in order[0..k) (so k < n implies a cycle).
// Time O(n + m) for m edges, extra space O(1) beyond `indeg`.
inline int topological_sort(const std::vector<int> &head, const std::vector<int> &target, std::vector<int> &indeg,
                            std::vector<int> &order, int n) {
  int m = target.size();
  for (int p = 0; p < m; p++) {
    int w = target[p];
    indeg[w] = indeg[w] + 1;
  }
  int qt = 0;
  for (int i = 0; i < n; i++) {
    if (indeg[i] == 0) {
      order[qt] = i;
      qt++;
    }
  }
  for (int qh = 0; qh < n; qh++) {
    if (qh < qt) {
      int v = order[qh];
      int start = head[v];
      int cnt = head[v + 1] - start;
      for (int d = 0; d < cnt; d++) {
        int w = target[start + d];
        indeg[w] = indeg[w] - 1;
        if (indeg[w] == 0) {
          order[qt] = w;
          qt++;
        }
      }
    }
  }
  return qt;
}

} // namespace cp

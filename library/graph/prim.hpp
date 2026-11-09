#pragma once
#include <vector>

namespace cp {

// Minimum spanning forest of an undirected graph by Prim's algorithm; returns the total cost.
// Derived from ListGraph::prim in experiments/library/cpp/graph/prim.hpp. Differences: the graph is given by CSR arrays
// (the arcs leaving v are target[head[v] .. head[v + 1]) with costs cost[head[v] .. head[v + 1])), the next vertex is
// found by a linear scan instead of a priority_queue (so the running time is O(n^2 + m) instead of O((n + m) log n)),
// the visited flags and the best known costs are caller-provided scratch vectors, and the cost that brought each vertex
// into the forest is left in dist (dist[v] == 0 for the first vertex of every component), from which the total is summed.
// The graph is undirected: every arc u -> v of cost c must have the reverse arc v -> u of the same cost c (as in
// ListGraph, where an undirected edge is stored as two arcs). Like the original, every connected component is spanned
// from its first vertex in index order, and the costs must be non-negative.
// `dist` has n entries, all equal to `inf` ("no arc yet"), and `done` has n zeros.
// Preconditions: head.size() == n + 1, head[0] == 0, head is non-decreasing, head[n] == target.size() == cost.size(),
// every target[p] is in [0, n), every cost[p] is in [0, inf), 0 <= inf <= 2^62, dist.size() == done.size() == n,
// n < 2^31 - 2, target.size() < 2^31 - 1, and the total cost of the forest fits in Cost (it is at most (n - 1) * max cost).
// Result: the weight of a spanning forest of minimum total cost.
// Time O(n^2 + m), extra space O(1).
template <class Cost>
inline Cost prim(const std::vector<int> &head, const std::vector<int> &target, const std::vector<Cost> &cost,
                 std::vector<Cost> &dist, std::vector<int> &done, int n, Cost inf) {
  for (int it = 0; it < n; it++) {
    int best = -1;
    Cost bd = inf;
    for (int v = 0; v < n; v++) {
      if (done[v] == 0) {
        if (dist[v] < bd) {
          bd = dist[v];
          best = v;
        }
      }
    }
    if (best < 0) {
      for (int v = 0; v < n; v++) {
        if (best < 0) {
          if (done[v] == 0) {
            best = v;
            bd = 0;
          }
        }
      }
    }
    done[best] = 1;
    dist[best] = bd;
    int start = head[best];
    int cnt = head[best + 1] - start;
    for (int d = 0; d < cnt; d++) {
      int w = target[start + d];
      Cost c = cost[start + d];
      if (done[w] == 0) {
        if (c < dist[w]) {
          dist[w] = c;
        }
      }
    }
  }
  Cost total = 0;
  for (int v = 0; v < n; v++) {
    total = total + dist[v];
  }
  return total;
}

template long long prim<long long>(const std::vector<int> &, const std::vector<int> &, const std::vector<long long> &,
                                   std::vector<long long> &, std::vector<int> &, int, long long);

} // namespace cp

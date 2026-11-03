#pragma once
#include <vector>

namespace cp {

// Single-source shortest paths for non-negative edge costs (Dijkstra), array version.
// Derived from ListGraph::dijkstra in experiments/library/cpp/graph/dijkstra.hpp. Differences: the graph is given by CSR
// arrays (the edges leaving v are target[head[v] .. head[v + 1]) with costs cost[head[v] .. head[v + 1])), and the next
// vertex is found by a linear scan instead of a priority_queue, so the running time is O(n^2 + m) instead of
// O((n + m) log n).
// `parent` has n entries and is written only where `dist` improves: when the vertex `best` is finalised and the edge
// best -> w lowers dist[w], parent[w] = best (as in the original). The caller sets parent[v] = -1 beforehand.
// `dist` has n entries; the caller sets dist[source] = 0 and every other entry to `inf` ("not reached yet") and
// `done` to n zeros beforehand. Entries may also start with other finite values (several sources).
// Preconditions: head.size() == n + 1, head[0] == 0, head is non-decreasing, head[n] == target.size(), every target[p]
// is in [0, n), every cost[p] is in [0, 2^61], dist.size() == done.size() == n, every entry of dist is in [lo, inf] with
// lo >= -2^62, inf <= 2^62, done is all zeros, parent.size() == n, n < 2^31 - 2, target.size() < 2^31 - 1.
// Result: each dist[v] != inf is d0[w] + the cost of a walk from some w with d0[w] != inf; and when inf exceeds
// d0[w] + the cost of every walk, dist[v] <= d0[w] + c for every walk of cost c from w to v (so dist[v] is the shortest
// distance). `done` marks the vertices reached.
// Time O(n^2 + m), extra space O(1).
template <class Cost>
inline void dijkstra(const std::vector<int> &head, const std::vector<int> &target, const std::vector<Cost> &cost,
                     std::vector<Cost> &dist, std::vector<int> &done, std::vector<int> &parent, int n, Cost inf) {
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
    if (best >= 0) {
      done[best] = 1;
      int start = head[best];
      int cnt = head[best + 1] - start;
      for (int d = 0; d < cnt; d++) {
        int w = target[start + d];
        Cost nd = bd + cost[start + d];
        if (nd < dist[w]) {
          dist[w] = nd;
          parent[w] = best;
        }
      }
    }
  }
}

template void dijkstra<long long>(const std::vector<int> &, const std::vector<int> &, const std::vector<long long> &,
                                  std::vector<long long> &, std::vector<int> &, std::vector<int> &, int, long long);

} // namespace cp

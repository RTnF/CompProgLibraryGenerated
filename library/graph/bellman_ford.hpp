#pragma once
#include <vector>

namespace cp {

// Single-source shortest paths by edge relaxation (Bellman-Ford); edges may have negative costs.
// Derived from ListGraph::bellman_ford in experiments/library/cpp/graph/bellman_ford.hpp: the edges are the parallel arrays
// from[e] -> to[e] with cost[e] instead of adjacency lists.
// `dist` has n entries; the caller sets dist[source] = 0 and every other entry to `inf` ("not reached yet"), `parent` has
// n entries set to -1; the marker -inf (below every finite distance) means "passes through a negative cycle".
// First, n - 1 passes over the edges in order relax dist[to[e]] with dist[from[e]] + cost[e] whenever dist[from[e]] != inf and
// the sum is smaller, and then parent[to[e]] = from[e] (the original's parent array).
// Then n more passes mark the negative cycles as in the original: when an edge could still relax (or its start is already
// marked), dist[to[e]] = -inf and parent[to[e]] = -1. (The original adds to the marker itself, which overflows; here a marked
// start simply marks its target.)
// Preconditions: n >= 1, dist.size() == parent.size() == n, from.size() == to.size() == cost.size() < 2^31 - 1, every from[e]
// and to[e] is in [0, n), n < 2^31 - 1, and no sum overflows: lo - (n - 1) * m * C > -inf for the lower bound lo of the
// entries of dist, the bound C >= |cost[e]|, C <= 2^61, 0 < inf <= 2^62, all entries of dist are in [lo, inf].
// Time O(n * m) for m edges, extra space O(1).
template <class Cost>
inline void bellman_ford(const std::vector<int> &from, const std::vector<int> &to, const std::vector<Cost> &cost,
                         std::vector<Cost> &dist, std::vector<int> &parent, int n, Cost inf) {
  int m = from.size();
  int rounds = n - 1;
  for (int i = 0; i < rounds; i++) {
    for (int e = 0; e < m; e++) {
      int u = from[e];
      int v = to[e];
      if (dist[u] != inf) {
        Cost nd = dist[u] + cost[e];
        if (nd < dist[v]) {
          dist[v] = nd;
          parent[v] = u;
        }
      }
    }
  }
  for (int i = 0; i < n; i++) {
    for (int e = 0; e < m; e++) {
      int u = from[e];
      int v = to[e];
      if (dist[u] != inf) {
        if (dist[u] == -inf) {
          dist[v] = -inf;
          parent[v] = -1;
        } else {
          Cost nd = dist[u] + cost[e];
          if (nd < dist[v]) {
            dist[v] = -inf;
            parent[v] = -1;
          }
        }
      }
    }
  }
}

template void bellman_ford<long long>(const std::vector<int> &, const std::vector<int> &, const std::vector<long long> &,
                                      std::vector<long long> &, std::vector<int> &, int, long long);

} // namespace cp

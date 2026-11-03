#pragma once
#include <vector>

namespace cp {

// Rooting of a tree by an iterative depth-first search (the part of Tree::build_depth in
// experiments/library/cpp/tree/tree.hpp that fills parent_, depth_ and cost_depth_). Differences: the tree is given by CSR
// arrays instead of adjacency lists (the arcs leaving v are target[head[v] .. head[v + 1]), cost[p] is the cost of the arc
// p), the results are written to the caller's vectors, and the height is not computed here.
// The farthest vertex (the vertex of the largest cost_depth among those reachable from root; as in the original, the first
// one that is popped from the stack wins a tie) is written to the extra last cell stk[n].
// Results: parent[root] == root, depth[root] == 0, cost_depth[root] == 0. For every vertex v reachable from root,
// other than root, parent[v] is a vertex u with an arc p = u -> v, depth[v] == depth[u] + 1 and cost_depth[v] ==
// cost_depth[u] + cost[p]; for every vertex not reachable from root parent[v] stays negative. If the graph is a symmetric
// tree (connected, no cycle, every arc u -> v has its reverse v -> u) this is the usual rooted tree: parent[v] is the
// neighbour of v on the path to root, depth[v] is the number of edges and cost_depth[v] the sum of costs on that path.
// Preconditions: n >= 1, head.size() == n + 1, head[0] == 0, head is non-decreasing, head[n] == target.size() ==
// cost.size() < 2^31 - 1, every target[p] is in [0, n), 0 <= root < n, parent.size() == depth.size() == cost_depth.size()
// == n and stk.size() == n + 1, parent[v] < 0 for every v (the original uses -1; depth, cost_depth and stk are scratch), n < 2^31 - 2,
// and no sum overflows: n * C < 2^63 for a bound C >= |cost[p]| of all costs.
// Time O(n + m) for m arcs, extra space O(1) beyond the caller's vectors.
template <class Cost>
inline void tree_root(const std::vector<int> &head, const std::vector<int> &target, const std::vector<Cost> &cost,
                      std::vector<int> &parent, std::vector<int> &depth, std::vector<Cost> &cost_depth,
                      std::vector<int> &stk, int root, int n) {
  parent[root] = root;
  depth[root] = 0;
  cost_depth[root] = 0;
  stk[0] = root;
  stk[n] = root;
  int sp = 1;
  for (int it = 0; it < n; it++) {
    if (sp > 0) {
      sp--;
      int v = stk[sp];
      int start = head[v];
      int cnt = head[v + 1] - start;
      for (int d = 0; d < cnt; d++) {
        int w = target[start + d];
        if (parent[w] < 0) {
          parent[w] = v;
          depth[w] = depth[v] + 1;
          cost_depth[w] = cost_depth[v] + cost[start + d];
          stk[sp] = w;
          sp++;
        }
      }
      Cost dv = cost_depth[v];
      int f = stk[n];
      Cost mx = cost_depth[f];
      if (mx < dv) {
        stk[n] = v;
      }
    }
  }
}

template void tree_root<long long>(const std::vector<int> &, const std::vector<int> &, const std::vector<long long> &,
                                   std::vector<int> &, std::vector<int> &, std::vector<long long> &, std::vector<int> &,
                                   int, int);

} // namespace cp

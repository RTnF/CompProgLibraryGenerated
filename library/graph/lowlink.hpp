#pragma once
#include <vector>

namespace cp {

// Lowlink (articulation points and bridges) of an undirected graph by an iterative depth-first search
// (ListGraph::lowlink in experiments/library/cpp/graph/lowlink.hpp). Differences: the graph is given by CSR arrays (the
// arcs leaving v are target[head[v] .. head[v + 1])), the recursion is replaced by an explicit stack `stk`, and the
// result is left in caller-provided vectors instead of the sorted lists the original returns:
//   ord[v]  the order in which v is first visited (0, 1, ... over all vertices; components in index order),
//   low[v]  the least ord reachable from the DFS subtree of v by one arc that is not the arc to the parent of its tail,
//   par[v]  the DFS parent of v (-1 for the root of a component),
//   sep[v]  the number of DFS children c of v with ord[v] <= low[c].
// Then the edge {par[v], v} is a bridge if and only if low[v] == ord[v] (v not a root), and v is an articulation point
// if and only if sep[v] >= 1 for a non-root v, or sep[v] >= 2 for a root. Like the original, parallel arcs are not
// supported: the graph must be simple (every arc u -> v has exactly one reverse arc v -> u, and no loops).
// Preconditions: head.size() == n + 1, head[0] == 0, head is non-decreasing, head[n] == target.size(), every target[p]
// is in [0, n), the graph is symmetric and simple, ord.size() == low.size() == par.size() == sep.size() == it.size()
// == stk.size() == n, ord[v] == -1, par[v] == -1, sep[v] == 0 for all v (low, it, stk are scratch), n < 2^31 - 2,
// target.size() < 2^31 - 1.
// Time O(n + m), extra space O(1) beyond the caller's vectors.
inline void lowlink(const std::vector<int> &head, const std::vector<int> &target, std::vector<int> &ord,
                    std::vector<int> &low, std::vector<int> &par, std::vector<int> &sep, std::vector<int> &it,
                    std::vector<int> &stk, int n) {
  int cnt = 0;
  for (int r = 0; r < n; r++) {
    if (ord[r] < 0) {
      ord[r] = cnt;
      low[r] = cnt;
      cnt++;
      it[r] = head[r];
      stk[0] = r;
      int sp = 1;
      while (sp > 0) {
        int v = stk[sp - 1];
        if (it[v] < head[v + 1]) {
          int e = it[v];
          int w = target[e];
          it[v] = e + 1;
          if (ord[w] < 0) {
            par[w] = v;
            ord[w] = cnt;
            low[w] = cnt;
            cnt++;
            it[w] = head[w];
            stk[sp] = w;
            sp++;
          } else {
            if (w != par[v]) {
              if (ord[w] < low[v]) {
                low[v] = ord[w];
              }
            }
          }
        } else {
          sp--;
          if (sp > 0) {
            int p = stk[sp - 1];
            if (low[v] < low[p]) {
              low[p] = low[v];
            }
            if (ord[p] <= low[v]) {
              sep[p] = sep[p] + 1;
            }
          }
        }
      }
    }
  }
}

} // namespace cp

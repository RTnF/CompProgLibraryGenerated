#pragma once
#include <vector>

namespace cp {

// Finds a directed cycle by an iterative depth-first search (ListGraph::find_cycle_directed in
// experiments/library/cpp/graph/find_cycle.hpp). Differences: the graph is given by CSR arrays (the arcs leaving v are
// target[head[v] .. head[v + 1])), the recursion is replaced by an explicit stack `stk`, and the cycle is written as a
// list of vertices to the caller's vector `cyc` (the original returns the list of edges): the function returns the number
// k of vertices written, `cyc[0 .. k)`, with an arc cyc[i] -> cyc[i + 1] for every i < k - 1 and an arc cyc[k - 1] -> cyc[0].
// It returns 0 if and only if the graph has no directed cycle (a loop v -> v is a cycle with k = 1).
// Preconditions: head.size() == n + 1, head[0] == 0, head is non-decreasing, head[n] == target.size(), every target[p]
// is in [0, n), state.size() == it.size() == stk.size() == cyc.size() == n, every entry of state is 0 (it, stk and cyc are
// scratch), n < 2^31 - 2, target.size() < 2^31 - 1.
// Result: the cycle consists of distinct vertices; 0 <= k <= n. Time O(n + m), extra space O(1) beyond the vectors.
inline int find_cycle(const std::vector<int> &head, const std::vector<int> &target, std::vector<int> &state,
                      std::vector<int> &it, std::vector<int> &stk, std::vector<int> &cyc, int n) {
  int fsp = 0;
  int fw = 0;
  for (int r = 0; r < n; r++) {
    if (fsp == 0) {
      if (state[r] == 0) {
        state[r] = 1;
        it[r] = head[r];
        stk[0] = r;
        int sp = 1;
        while (sp > 0) {
          int v = stk[sp - 1];
          if (it[v] < head[v + 1]) {
            int e = it[v];
            int w = target[e];
            it[v] = e + 1;
            if (state[w] == 0) {
              state[w] = 1;
              it[w] = head[w];
              stk[sp] = w;
              sp++;
            } else {
              if (state[w] == 1) {
                fsp = sp;
                fw = w;
                sp = 0;
              }
            }
          } else {
            state[v] = 2;
            sp--;
          }
        }
      }
    }
  }
  int k = 0;
  if (fsp > 0) {
    int j = fsp - 1;
    while (stk[j] != fw) {
      j--;
    }
    k = fsp - j;
    for (int t = 0; t < k; t++) {
      cyc[t] = stk[j + t];
    }
  }
  return k;
}

} // namespace cp

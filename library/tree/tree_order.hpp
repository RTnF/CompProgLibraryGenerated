#pragma once
#include <vector>

namespace cp {

// A breadth-first order of a rooted tree, for tree_full_dp: ord[0] = root, and every other vertex appears after its parent
// (the vertices appear by non-decreasing depth). The tree is given by CSR arrays (the neighbours of v are
// target[head[v] .. head[v + 1])) and by the parent array of the tree rooted at `root` (as written by tree_root:
// parent[root] == root and parent[w] is the neighbour of w on the path from w to root). The result is written to ord.
// Preconditions: n >= 1, n + 2 < 2^31, head.size() == n + 1, head[0] == 0, head is non-decreasing, head[n] == target.size() <
// 2^31 - 1, every target[p] is in [0, n), the graph is a symmetric tree (connected, no self loop, no cycle, no multiple edge,
// every arc u -> v has its reverse v -> u), 0 <= root < n, parent is the parent array described above (parent.size() == n),
// and ord.size() == n (its values on entry are arbitrary).
// Result: ord is a permutation of 0, ..., n - 1 with ord[0] == root in which every vertex other than root comes after its
// parent. Time O(n + m) for m arcs, extra space O(1) beyond the caller's vectors.
inline void tree_order(const std::vector<int> &head, const std::vector<int> &target, const std::vector<int> &parent,
                       std::vector<int> &ord, int root, int n) {
  ord[0] = root;
  int cnt = 1;
  for (int i = 0; i < n; i++) {
    if (i < cnt) {
      int v = ord[i];
      for (int p = head[v]; p < head[v + 1]; p++) {
        int w = target[p];
        if (parent[w] == v) {
          ord[cnt] = w;
          cnt++;
        }
      }
    }
  }
}

} // namespace cp

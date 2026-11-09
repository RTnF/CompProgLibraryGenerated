#pragma once
#include <vector>

namespace cp {

// Policy of a rerooting DP over a tree: the DP value of a vertex is sum_up(op(e(), dp(child_1), ..., dp(child_k))).
// This instance is the "height" DP: e() = 0, op = max, sum_up(x) = x + 1 (so the value of a vertex is the number of
// vertices on the longest downward path starting at it). op must be commutative and associative with identity e().
template <class T> struct DpHeight {
  using value_type = T;
  static T e() { return 0; }
  static T op(T a, T b) {
    T r = a;
    if (a < b) {
      r = b;
    }
    return r;
  }
  static T sum_up(T x) { return x + 1; }
};

// Full tree DP (rerooting) of the function Tree::full_tree_dp in experiments/library/cpp/tree/tree.hpp. The recursion of the
// original depth-first search is replaced by a pop order `ord` (a vertex is popped after its parent), the tree is given by
// CSR arrays (the neighbours of v are target[head[v] .. head[v + 1])), and the results are written to the caller's vectors.
// Results: full[v] is the DP value of the whole tree rooted at v, i.e. sum_up(op over all neighbours w of v of the DP value
// of the component of w when the edge (v, w) is removed, rooted at w); dp[v] is the DP value of the subtree of v when the
// tree is rooted at `root`. pre[p] / suf[p] (arc p = v -> w with w a child of v) are the products of the dp values of the
// children before / after w (suf is built from the right, so op must be commutative).
// Preconditions: n >= 1, n + 2 < 2^31, head.size() == n + 1, head[0] == 0, head is non-decreasing, head[n] == target.size() < 2^31 - 1,
// every target[p] is in [0, n), the graph is a symmetric tree (connected, no self loop, no cycle, no multiple edge, every
// arc u -> v has its reverse v -> u), 0 <= root < n, parent is the rooted-tree parent array of the tree for root (as written by
// tree_root: parent[root] == root and parent[w] is the neighbour of w on the path from w to root), ord is a permutation of
// 0, ..., n - 1 in which every vertex comes after its parent (for example the vertices sorted by depth), parent.size() ==
// ord.size() == dp.size() == up.size() == full.size() == n, pre.size() == suf.size() == target.size(), and dp and up hold
// values in [0, n] on entry (for example zero-initialised); pre, suf and full may hold anything on entry.
// Time O(n + m), extra space O(1) beyond the caller's vectors.
template <class P, class T = typename P::value_type>
inline void tree_full_dp(const std::vector<int> &head, const std::vector<int> &target, const std::vector<int> &parent,
                         const std::vector<int> &ord, std::vector<T> &dp, std::vector<T> &pre, std::vector<T> &suf,
                         std::vector<T> &up, std::vector<T> &full, int root, int n) {
  for (int k = n - 1; k >= 0; k--) {
    int v = ord[k];
    T acc = P::e();
    for (int p = head[v]; p < head[v + 1]; p++) {
      int w = target[p];
      if (parent[w] == v) {
        pre[p] = acc;
        acc = P::op(acc, dp[w]);
      }
    }
    full[v] = acc;
    dp[v] = P::sum_up(acc);
    T back = P::e();
    for (int p = head[v + 1] - 1; p >= head[v]; p--) {
      int w = target[p];
      if (parent[w] == v) {
        suf[p] = back;
        back = P::op(back, dp[w]);
      }
    }
  }
  up[root] = P::e();
  for (int k = 0; k < n; k++) {
    int v = ord[k];
    T total = full[v];
    full[v] = P::sum_up(P::op(up[v], total));
    for (int p = head[v]; p < head[v + 1]; p++) {
      int w = target[p];
      if (parent[w] == v) {
        up[w] = P::sum_up(P::op(P::op(up[v], pre[p]), suf[p]));
      }
    }
  }
}

template struct DpHeight<long long>;
template void tree_full_dp<DpHeight<long long>>(const std::vector<int> &, const std::vector<int> &, const std::vector<int> &,
                                                const std::vector<int> &, std::vector<long long> &, std::vector<long long> &,
                                                std::vector<long long> &, std::vector<long long> &, std::vector<long long> &,
                                                int, int);

} // namespace cp

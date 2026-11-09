#pragma once
#include <vector>

namespace cp {

// Iterative segment tree for sums modulo 2^64 over a std::vector<unsigned long long> `node`
// (SegmentTree in experiments/library/cpp/segment_tree/segment_tree.hpp with M = (unsigned long long, +, 0); the
// class fields n_node/h_node are derived from the vector). Unsigned addition wraps around by definition, so there is
// no overflow precondition.
// Layout: node.size() == 2 * N with N >= 1 (N need not be a power of two); the leaves are node[N + i] (i < N) and
// node[i] == node[2 * i] + node[2 * i + 1] for 1 <= i < N. Time O(log N), extra space O(1).

// The sum of the leaves [l, r)   (SegmentTree::product); requires 0 <= l <= r <= N, N < 2^30.
template <class T> inline T segtree_sum_product(const std::vector<T> &node, int l, int r) {
  int n_node = (int)node.size();
  n_node /= 2;
  T left = 0;
  T right = 0;
  l += n_node;
  r += n_node;
  while (l < r) {
    if (l % 2 != 0) {
      left += node[l];
      l++;
    }
    if (r % 2 != 0) {
      r--;
      right += node[r];
    }
    l /= 2;
    r /= 2;
  }
  return left + right;
}

// leaf[idx] = val   (SegmentTree::set); requires 0 <= idx < N, N < 2^30. Keeps the layout.
template <class T> inline void segtree_sum_set(std::vector<T> &node, int idx, T val) {
  int n_node = (int)node.size();
  n_node /= 2;
  int i = idx + n_node;
  node[i] = val;
  i /= 2;
  while (i >= 1) {
    node[i] = node[2 * i] + node[2 * i + 1];
    i /= 2;
  }
}

template unsigned long long segtree_sum_product<unsigned long long>(const std::vector<unsigned long long> &, int, int);
template void segtree_sum_set<unsigned long long>(std::vector<unsigned long long> &, int, unsigned long long);

} // namespace cp

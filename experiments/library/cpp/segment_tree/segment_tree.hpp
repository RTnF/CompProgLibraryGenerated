#pragma once
#include "template/small_template.hpp"

/**
 * @brief セグメント木 based on ACL
 * @tparam M モノイド
 */
template <class M> class SegmentTree {
  // ex. n=5, n_node=8, h_node=3
  //                 [1]
  //       [2]                 [3]
  //   [4]      [5]       [6]       [7]
  // (8) (9) (10) (11) (12) [13] [14] [15]
  int n, n_node, h_node;
  vector<M> node;
  void update(int i) { node[i] = op(node[i * 2], node[i * 2 + 1]); }

public:
  SegmentTree() : SegmentTree(0) {}
  SegmentTree(int n_) : SegmentTree(vector<M>(n_, M::e())) {}
  SegmentTree(const vector<M> &v) : n(v.size()) {
    h_node = 0;
    n_node = 0;
    while (n_node < n) {
      h_node++;
      n_node = 1 << h_node;
    }
    node = vector<M>(n_node * 2, M::e());
    for (int i = 0; i < n; i++) {
      node[n_node + i] = v[i];
    }
    for (int i = n_node - 1; i >= 1; i--) {
      update(i);
    }
  }

  // v[idx] = val
  void set(int idx, M val) {
    assert(0 <= idx && idx < n);
    idx += n_node;
    node[idx] = val;
    for (int i = 1; i <= h_node; i++) {
      update(idx >> i);
    }
  }

  // v[idx]
  M get(int idx) {
    assert(0 <= idx && idx < n);
    return node[idx + n_node];
  }

  /**
   * @brief 区間[l, r)の総積
   * @return op(v[l] ... v[r-1])
   */
  M product(int l, int r) {
    assert(0 <= l && l <= r && r <= n);
    M l_op = M::e(), r_op = M::e();
    l += n_node;
    r += n_node;

    while (l < r) {
      if (l & 1) {
        l_op = op(l_op, node[l++]);
      }
      if (r & 1) {
        r_op = op(node[--r], r_op);
      }
      l >>= 1;
      r >>= 1;
    }
    return op(l_op, r_op);
  }

  /**
   * @brief 総積
   *
   * @returns op(v[0] ... v[n-1])
   */
  M product_all() { return node[1]; }

  /**
   * @brief 二分探索 O(log n) lからの総積がfを満たさなくなるr
   * @tparam F
   * @param l [0, n], 探索区間[l, n)
   * @param f [](M x) -> bool {...}, f(e) == true
   * @return [l, n]から1つ, f(op(v[l] ... v[r-1])) == true && f(op(v[l] ...
   * v[r])) == false
   */
  template <class F> int search_prod_right(int l, F f) {
    assert(0 <= l && l <= n);
    assert(f(M::e()));
    if (l == n) {
      return n;
    }
    l += n_node;
    M sm = M::e();
    do {
      while (l % 2 == 0) {
        l >>= 1;
      }
      if (!f(op(sm, node[l]))) {
        while (l < n_node) {
          l = l * 2;
          if (f(op(sm, node[l]))) {
            sm = op(sm, node[l]);
            l++;
          }
        }
        return l - n_node;
      }
      sm = op(sm, node[l]);
      l++;
    } while ((l & -l) != l);
    return n;
  }

  /**
   * @brief 二分探索 O(log n) rからの総積がfを満たさなくなるl
   * @tparam F
   * @param r [0, n], 探索区間[0, r)
   * @param f [](M x) -> bool {...}, f(e) == true
   * @return [0, r]から1つ、f(op(v[l] ... v[r-1])) == true && f(op(v[l-1] ...
   * v[r-1])) == false
   */
  template <class F> int search_prod_left(int r, F f) {
    assert(0 <= r && r <= n);
    assert(f(M::e()));
    if (r == 0) {
      return 0;
    }
    r += n_node;
    M sm = M::e();
    do {
      r--;
      while (r > 1 && (r % 2)) {
        r >>= 1;
      }
      if (!f(op(node[r], sm))) {
        while (r < n_node) {
          r = r * 2 + 1;
          if (f(op(node[r], sm))) {
            sm = op(node[r], sm);
            r--;
          }
        }
        return r + 1 - n_node;
      }
      sm = op(node[r], sm);
    } while ((r & -r) != r);
    return 0;
  }
};

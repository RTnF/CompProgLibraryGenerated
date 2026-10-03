#pragma once
#include "template/small_template.hpp"

/**
 * @brief セグメント木 based on ACL
 * @tparam M モノイド
 */
template <class M, class F> class LazySegmentTree {
  // ex. n=5, n_node=8, h_node=3
  //                 [1]
  //       [2]                 [3]
  //   [4]      [5]       [6]       [7]
  // (8) (9) (10) (11) (12) [13] [14] [15]
  int n, n_node, h_node;
  vector<M> node;
  vector<F> lazy;
  void update(int i) { node[i] = op(node[i * 2], node[i * 2 + 1]); }
  void all_apply(int k, F f) {
    node[k] = f.apply(node[k]);
    if (k < n_node) {
      lazy[k] = compose(f, lazy[k]);
    }
  }
  void push(int k) {
    all_apply(2 * k, lazy[k]);
    all_apply(2 * k + 1, lazy[k]);
    lazy[k] = F::id();
  }

public:
  LazySegmentTree() : LazySegmentTree(0) {}
  LazySegmentTree(int n_) : LazySegmentTree(vector<M>(n_, M::e())) {}
  LazySegmentTree(const vector<M> &v) : n(v.size()) {
    h_node = 0;
    n_node = 0;
    while (n_node < n) {
      h_node++;
      n_node = 1 << h_node;
    }
    node = vector<M>(n_node * 2, M::e());
    lazy = vector<F>(n_node, F::id());
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
    for (int i = h_node; i >= 1; i--) {
      push(idx >> i);
    }
    node[idx] = val;
    for (int i = 1; i <= h_node; i++) {
      update(idx >> i);
    }
  }

  // v[idx]
  M get(int idx) {
    assert(0 <= idx && idx < n);
    idx += n_node;
    for (int i = h_node; i >= 1; i--) {
      push(idx >> i);
    }
    return node[idx];
  }

  /**
   * @brief 区間[l, r)の総積
   * @return op(v[l] ... v[r-1])
   */
  M product(int l, int r) {
    assert(0 <= l && l <= r && r <= n);
    if (l == r) {
      return M::e();
    }
    l += n_node;
    r += n_node;
    for (int i = h_node; i >= 1; i--) {
      if (((l >> i) << i) != l) {
        push(l >> i);
      }
      if (((r >> i) << i) != r) {
        push((r - 1) >> i);
      }
    }

    M l_op = M::e(), r_op = M::e();
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

  // 単一更新
  void update(int idx, F f) {
    assert(0 <= idx && idx < n);
    idx += n_node;
    for (int i = h_node; i >= 1; i--) {
      push(idx >> i);
    }
    node[idx] = f.apply(node[idx]);
    for (int i = 1; i <= h_node; i++) {
      update(idx >> i);
    }
  }
  // 範囲更新
  void update(int l, int r, F f) {
    assert(0 <= l && l <= r && r <= n);
    if (l == r) {
      return;
    }
    l += n_node;
    r += n_node;
    for (int i = h_node; i >= 1; i--) {
      if (((l >> i) << i) != l) {
        push(l >> i);
      }
      if (((r >> i) << i) != r) {
        push((r - 1) >> i);
      }
    }
    {
      int l2 = l, r2 = r;
      while (l < r) {
        if (l & 1) {
          all_apply(l++, f);
        }
        if (r & 1) {
          all_apply(--r, f);
        }
        l >>= 1;
        r >>= 1;
      }
      l = l2;
      r = r2;
    }
    for (int i = 1; i <= h_node; i++) {
      if (((l >> i) << i) != l) {
        update(l >> i);
      }
      if (((r >> i) << i) != r) {
        update((r - 1) >> i);
      }
    }
  }

  /**
   * @brief 二分探索 O(log n) lからの総積がfを満たさなくなるr
   * @tparam G
   * @param l [0, n], 探索区間[l, n)
   * @param f [](M x) -> bool {...}, f(e) == true
   * @return [l, n]から1つ, f(op(v[l] ... v[r-1])) == true && f(op(v[l] ...
   * v[r])) == false
   */
  template <class G> int search_prod_right(int l, G f) {
    assert(0 <= l && l <= n);
    assert(f(M::e()));
    if (l == n) {
      return n;
    }
    l += n_node;
    for (int i = h_node; i >= 1; i--) {
      push(l >> i);
    }
    M sm = M::e();
    do {
      while (l % 2 == 0) {
        l >>= 1;
      }
      if (!f(op(sm, node[l]))) {
        while (l < n_node) {
          push(l);
          l *= 2;
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
   * @tparam G
   * @param r [0, n], 探索区間[0, r)
   * @param f [](M x) -> bool {...}, f(e) == true
   * @return [0, r]から1つ、f(op(v[l] ... v[r-1])) == true && f(op(v[l-1] ...
   * v[r-1])) == false
   */
  template <class G> int search_prod_left(int r, G f) {
    assert(0 <= r && r <= n);
    assert(f(M::e()));
    if (r == 0) {
      return 0;
    }
    r += n_node;
    for (int i = h_node; i >= 1; i--) {
      push((r - 1) >> i);
    }
    M sm = M::e();
    do {
      r--;
      while (r > 1 && (r % 2)) {
        r >>= 1;
      }
      if (!f(op(node[r], sm))) {
        while (r < n_node) {
          push(r);
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

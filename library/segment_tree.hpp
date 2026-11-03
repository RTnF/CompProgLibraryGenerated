#pragma once
#include <limits>
#include <vector>

namespace cp {

// Iterative segment tree over a monoid (SegmentTree in experiments/library/cpp/segment_tree/segment_tree.hpp, based on ACL).
// The monoid M is a policy with `value_type`, a static `e()` (identity) and a static `apply(a, b)` (associative operation);
// the tree stores the values themselves (`std::vector<value_type>`) instead of objects of M, because the verified vector
// operations are those of std::vector of integers. `SegMax<T>` below is the policy of MonoidMax<T> (monoid.hpp):
// e() is the smallest value of T and apply is the maximum.
// Layout: n_node is the smallest power of two that is >= max(n, 2) (0 for n == 0), h_node = log2(n_node), and `node` has
// 2 * n_node entries: the leaves are node[n_node + i] (i < n), the remaining leaves hold e(), and
// node[i] == apply(node[2 * i], node[2 * i + 1]) for 1 <= i < n_node.
// Differences from the original: values instead of M objects (the original's M::x), the constructor builds `node` with
// the vector constructor in the member initializer list and `n_node`/`h_node` by static helpers (the original loops in the
// body), `1 << k` and `>>` are written as `* 2` and `/ 2`, `set` updates the ancestors by `idx = idx / 2`, and
// `search_prod_right/left` and the assertions are not included yet. All indices are ints, so n_node < 2^30.
template <class T> struct SegMax {
  using value_type = T;
  static T e() { return std::numeric_limits<T>::min(); }
  static T apply(T a, T b) {
    T r = a;
    if (a < b) {
      r = b;
    }
    return r;
  }
};

// the policy of MonoidMin<T>: e() is the largest value of T and apply is the minimum
template <class T> struct SegMin {
  using value_type = T;
  static T e() { return std::numeric_limits<T>::max(); }
  static T apply(T a, T b) {
    T r = a;
    if (b < a) {
      r = b;
    }
    return r;
  }
};

template <class M, class T = typename M::value_type> class SegmentTree {
  std::vector<T> node;  // declared first: the verified model passes the vector fields before the scalar ones
  int n, n_node, h_node;
  // the smallest power of two that is at least n (0 for n == 0); n_node of the original
  static int size_of(int n) {
    int size = 0;
    int p = 1;
    while (size < n) {
      p = p * 2;
      size = p;
    }
    return size;
  }
  static int height_of(int n) {
    int h = 0;
    int size = 0;
    int p = 1;
    while (size < n) {
      h++;
      p = p * 2;
      size = p;
    }
    return h;
  }
  void update(int i) { node[i] = M::apply(node[i * 2], node[i * 2 + 1]); }

public:
  SegmentTree(const std::vector<T> &v)
      : node(2 * size_of((int)v.size()), M::e()), n((int)v.size()), n_node(size_of((int)v.size())),
        h_node(height_of((int)v.size())) {
    for (int i = 0; i < n; i++) {
      node[n_node + i] = v[i];
    }
    for (int i = n_node - 1; i >= 1; i--) {
      update(i);
    }
  }

  // v[idx] = val
  void set(int idx, T val) {
    idx += n_node;
    node[idx] = val;
    for (int i = 1; i <= h_node; i++) {
      idx = idx / 2;
      update(idx);
    }
  }

  // v[idx]
  T get(int idx) { return node[idx + n_node]; }

  // the product of [l, r)
  T product(int l, int r) {
    T l_op = M::e();
    T r_op = M::e();
    l += n_node;
    r += n_node;
    while (l < r) {
      if (l % 2 == 1) {
        l_op = M::apply(l_op, node[l]);
        l++;
      }
      if (r % 2 == 1) {
        r--;
        r_op = M::apply(node[r], r_op);
      }
      l = l / 2;
      r = r / 2;
    }
    return M::apply(l_op, r_op);
  }

  // the product of all
  T product_all() { return node[1]; }
};

template struct SegMax<long long>;
template class SegmentTree<SegMax<long long>>;
template struct SegMin<long long>;
template class SegmentTree<SegMin<long long>>;

} // namespace cp

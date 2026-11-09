#pragma once
#include <limits>
#include <vector>

namespace cp {

// Policy of a range "chmin" (action) over a maximum (value): the value type T is the maximum monoid
// (e() = the smallest value, op = max) and an action c replaces every value x of a range by min(c, x).
// id() = the largest value (min(id, x) = x). The laws needed by the lazy propagation hold without overflow:
// mapping(f, op(a, b)) == op(mapping(f, a), mapping(f, b)), mapping(composition(f, g), x) == mapping(f, mapping(g, x)),
// mapping(id, x) == x, and composition is associative with id as the identity.
template <class T> struct LazyChminMax {
  using value_type = T;
  using action_type = T;
  static T e() { return std::numeric_limits<T>::min(); }
  static T id() { return std::numeric_limits<T>::max(); }
  static T op(T a, T b) {
    T r = a;
    if (a < b) {
      r = b;
    }
    return r;
  }
  static T mapping(T f, T x) {
    T r = x;
    if (f < x) {
      r = f;
    }
    return r;
  }
  static T composition(T f, T g) {
    T r = g;
    if (f < g) {
      r = f;
    }
    return r;
  }
};

template <class P, class T = typename P::value_type, class F = typename P::action_type> class LazySegmentTree {
  std::vector<T> node;
  std::vector<F> lazy;
  int n, n_node, h_node;
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
  void update(int i) { node[i] = P::op(node[i * 2], node[i * 2 + 1]); }
  void all_apply(int k, F f) {
    node[k] = P::mapping(f, node[k]);
    if (k < n_node) {
      lazy[k] = P::composition(f, lazy[k]);
    }
  }
  void push(int k) {
    all_apply(2 * k, lazy[k]);
    all_apply(2 * k + 1, lazy[k]);
    lazy[k] = P::id();
  }

public:
  LazySegmentTree(const std::vector<T> &v)
      : node(2 * size_of((int)v.size()), P::e()), lazy(size_of((int)v.size()), P::id()), n((int)v.size()),
        n_node(size_of((int)v.size())), h_node(height_of((int)v.size())) {
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
    int pw = n_node;
    for (int i = h_node; i >= 1; i--) {
      push(idx / pw);
      pw = pw / 2;
    }
    node[idx] = val;
    for (int i = 1; i <= h_node; i++) {
      idx = idx / 2;
      update(idx);
    }
  }

  // v[idx]
  T get(int idx) {
    idx += n_node;
    int pw = n_node;
    for (int i = h_node; i >= 1; i--) {
      push(idx / pw);
      pw = pw / 2;
    }
    return node[idx];
  }

  // the product of [l, r)
  T product(int l, int r) {
    l += n_node;
    r += n_node;
    int pw = n_node;
    for (int i = h_node; i >= 1; i--) {
      if (l / pw * pw != l) {
        push(l / pw);
      }
      if (r / pw * pw != r) {
        push((r - 1) / pw);
      }
      pw = pw / 2;
    }
    T l_op = P::e();
    T r_op = P::e();
    while (l < r) {
      if (l % 2 == 1) {
        l_op = P::op(l_op, node[l]);
        l++;
      }
      if (r % 2 == 1) {
        r--;
        r_op = P::op(node[r], r_op);
      }
      l = l / 2;
      r = r / 2;
    }
    return P::op(l_op, r_op);
  }

  // the product of all
  T product_all() { return node[1]; }

  // v[idx] = mapping(f, v[idx])
  void update(int idx, F f) {
    idx += n_node;
    int pw = n_node;
    for (int i = h_node; i >= 1; i--) {
      push(idx / pw);
      pw = pw / 2;
    }
    node[idx] = P::mapping(f, node[idx]);
    for (int i = 1; i <= h_node; i++) {
      idx = idx / 2;
      update(idx);
    }
  }

  // v[i] = mapping(f, v[i]) for l <= i < r
  void update(int l, int r, F f) {
    l += n_node;
    r += n_node;
    int pw = n_node;
    for (int i = h_node; i >= 1; i--) {
      if (l / pw * pw != l) {
        push(l / pw);
      }
      if (r / pw * pw != r) {
        push((r - 1) / pw);
      }
      pw = pw / 2;
    }
    int l2 = l;
    int r2 = r;
    while (l < r) {
      if (l % 2 == 1) {
        all_apply(l, f);
        l++;
      }
      if (r % 2 == 1) {
        r--;
        all_apply(r, f);
      }
      l = l / 2;
      r = r / 2;
    }
    l = l2;
    r = r2;
    pw = 2;
    for (int i = 1; i <= h_node; i++) {
      if (l / pw * pw != l) {
        update(l / pw);
      }
      if (r / pw * pw != r) {
        update((r - 1) / pw);
      }
      pw = pw * 2;
    }
  }
};

template struct LazyChminMax<long long>;
template class LazySegmentTree<LazyChminMax<long long>>;

} // namespace cp

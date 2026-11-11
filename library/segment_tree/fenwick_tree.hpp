#pragma once
#include <vector>

namespace cp {

// Binary indexed tree (Fenwick tree) over an array A of n elements, stored in a vector `tree` of size n + 1
// (1-indexed; tree[0] unused; tree[k] is the sum of A over [k - lowbit(k), k)).
// This is experiments/library/cpp/segment_tree/binary_indexed_tree.hpp (BinaryIndexedTree) with the same
// constructors and methods; the class template keeps the element type T, and the verified instance is
// FenwickTree<long long>.
// Differences from the original: std:: qualification and the namespace only.
// Preconditions: n >= 0 and v.size() < 2^31 - 1; for sum, 0 <= r < tree.size() and 0 <= l <= r; for add,
// 0 <= i < n; every intermediate sum fits in T.
template <class T = long long> class FenwickTree {
  std::vector<T> tree; // 1-indexed
public:
  FenwickTree() {}
  // an empty array of n elements (all zero), O(n)
  FenwickTree(int n) : tree(n + 1) {}
  // the tree of the array v, O(n)
  FenwickTree(const std::vector<T> &v) : tree(v.size() + 1) {
    for (int i = 0; i < (int)v.size(); i++) {
      tree[i + 1] = v[i];
    }
    for (int i = 1; i < (int)v.size(); i++) {
      if (i + (i & -i) < (int)tree.size()) {
        tree[i + (i & -i)] += tree[i];
      }
    }
  }
  // sum of A[0, r)   (O(log n))
  T sum(int r) const {
    T s = 0;
    for (; r > 0; r -= (r & -r)) {
      s += tree[r];
    }
    return s;
  }
  // sum of A[l, r)   (O(log n))
  T sum(int l, int r) const { return sum(r) - sum(l); }
  // A[i] += val   (O(log n))
  void add(int i, T val) {
    i++;
    for (; i < (int)tree.size(); i += (i & -i)) {
      tree[i] += val;
    }
  }
};

// The name of the original class (BinaryIndexedTree), kept for source compatibility.
template <class T = long long> using BinaryIndexedTree = FenwickTree<T>;

template class FenwickTree<long long>;

} // namespace cp

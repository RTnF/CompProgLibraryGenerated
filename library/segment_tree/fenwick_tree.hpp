#pragma once
#include <vector>

namespace cp {

// Binary indexed tree (Fenwick tree) over an array A of n elements, stored in a vector `tree` of size n + 1
// (1-indexed; tree[0] unused; tree[k] is the sum of A over [k - lowbit(k), k)).
// This is experiments/library/cpp/segment_tree/binary_indexed_tree.hpp (BinaryIndexedTree) with the same
// constructors and methods; the class template keeps the element type T, and the verified instance is
// FenwickTree<long long>.
// Differences from the original: i & -i is written with unsigned operands (the verified bit operations are
// unsigned; the value is the same). The vector constructor uses the same guarded += as the repaired original,
// without requiring a binary operator+ from T. Its loop bounds use v.size() (tree.size() is v.size() + 1 by the
// member initialiser); sum(l, r) takes the two prefix sums into locals first.
// Preconditions: tree.size() <= 2^30; for sum, 0 <= r < tree.size(); for add, 0 <= i < 2^31 - 1 (an index past the
// end changes nothing); every intermediate sum fits in T.
template <class T = long long> class FenwickTree {
  std::vector<T> tree; // 1-indexed
public:
  FenwickTree() {}
  // an empty array of n elements (all zero), O(n)
  FenwickTree(int n) : tree(n + 1) {}
  // the tree of the array v, O(n)
  FenwickTree(const std::vector<T> &v) : tree(v.size() + 1) {
    int n = (int)v.size();
    for (int k = 0; k < n; k++) {
      tree[k + 1] = v[k];
    }
    for (int k = 0; k < n; k++) {
      int i = k + 1;
      int j = i + (int)((unsigned)i & (0u - (unsigned)i));
      if (j <= n) {
        tree[j] += tree[i];
      }
    }
  }
  // sum of A[0, r)   (O(log n))
  T sum(int r) const {
    T s = 0;
    for (; r > 0; r -= (int)((unsigned)r & (0u - (unsigned)r))) {
      s += tree[r];
    }
    return s;
  }
  // sum of A[l, r) = sum(r) - sum(l)   (O(log n))
  T sum(int l, int r) const {
    T a = sum(r);
    T b = sum(l);
    return a - b;
  }
  // A[i] += val   (O(log n))
  void add(int i, T val) {
    i++;
    for (; i < (int)tree.size(); i += (int)((unsigned)i & (0u - (unsigned)i))) {
      tree[i] += val;
    }
  }
};

// The name of the original class (BinaryIndexedTree), kept for source compatibility.
template <class T = long long> using BinaryIndexedTree = FenwickTree<T>;

template class FenwickTree<long long>;

} // namespace cp

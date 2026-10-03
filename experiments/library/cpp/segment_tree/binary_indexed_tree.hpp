#pragma once
#include "template/small_template.hpp"

/**
 * @brief Binary Indexed Tree (Fenwick Tree)
 */
template <class T = ll> class BinaryIndexedTree {
  vector<T> tree; // 1-indexed
public:
  BinaryIndexedTree() {}
  BinaryIndexedTree(int n) : tree(n + 1) {}
  BinaryIndexedTree(const vector<T> &v) : tree(v.size() + 1) {
    for (int i = 0; i < (int)v.size(); i++) {
      tree[i + 1] = v[i];
    }
    for (int i = 1; i < (int)v.size(); i++) {
      tree[i + (i & -i)] += tree[i];
    }
  }
  // sum of A[0, r)
  T sum(int r) const {
    T s = 0;
    for (; r > 0; r -= (r & -r)) {
      s += tree[r];
    }
    return s;
  }
  // sum of A[l, r)
  T sum(int l, int r) const { return sum(r) - sum(l); }
  // A[i] += val
  void add(int i, T val) {
    i++;
    for (; i < (int)tree.size(); i += (i & -i)) {
      tree[i] += val;
    }
  }
};
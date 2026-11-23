#pragma once
#include <cassert>
#include <utility>
#include <vector>

namespace cp {

// Disjoint set union (experiments/library/cpp/union_find/union_find.hpp `UnionFind`; disjoint_set_union.hpp is the
// same file). Elements are 0 .. n-1; trees are joined by size and every root lookup compresses the path.
//
// UnionFind()     no elements.
// UnionFind(n)    n singleton trees; time O(n). Requires 0 <= n.
// unite(a, b)     joins the trees of a and b (the larger tree's root becomes the parent) and returns the root of the
//                 result; returns the common root if they are already joined.
// same(a, b)      whether a and b are in one tree.
// root(a)         the root of the tree of a; makes every node on the path from a point at the root.
// size(a)         the number of elements of the tree of a.
// num_groups()    the number of trees; time O(1).
// unite, same, root and size are O(log n) worst case (union by size bounds the height) and amortised nearly constant.
// Preconditions: 0 <= a, b < n (checked by assert); n < 2^31.
class UnionFind {
  // root: -1 * (tree size), otherwise: the parent
  std::vector<int> _ps;
  int _num_groups, _n;

public:
  UnionFind() : _num_groups(0), _n(0) {}
  UnionFind(int n) : _ps(n, -1), _num_groups(n), _n(n) { assert(n >= 0); }

  int unite(int a, int b) {
    assert(0 <= a && a < _n);
    assert(0 <= b && b < _n);
    int x = root(a), y = root(b);
    if (x == y) {
      return x;
    }
    if (-_ps[x] < -_ps[y]) {
      std::swap(x, y);
    }
    _ps[x] += _ps[y];
    _ps[y] = x;
    _num_groups--;
    return x;
  }

  bool same(int a, int b) {
    assert(0 <= a && a < _n);
    assert(0 <= b && b < _n);
    return root(a) == root(b);
  }

  int root(int a) {
    assert(0 <= a && a < _n);
    if (_ps[a] < 0) {
      return a;
    }
    return _ps[a] = root(_ps[a]);
  }

  int size(int a) {
    assert(0 <= a && a < _n);
    return -_ps[root(a)];
  }

  int num_groups() { return _num_groups; }
};

} // namespace cp

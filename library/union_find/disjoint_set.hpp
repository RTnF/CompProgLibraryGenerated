#pragma once
#include <cassert>
#include <utility>
#include <vector>

namespace cp {

// Disjoint set union with union by size and path compression.
// Requires n >= 0 and vertex arguments in [0, n).
class DisjointSet {
  // root: -1 * (tree size), otherwise: the parent
  std::vector<int> _ps;
  int _num_groups, _n;

public:
  DisjointSet(int n) : _ps(n, -1), _num_groups(n), _n(n) { assert(n >= 0); }

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

  int getNum() { return _num_groups; }
};

} // namespace cp

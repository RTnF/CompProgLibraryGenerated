#pragma once
#include <cassert>
#include <vector>

namespace cp {

// Candidate preserving the complete original UnionFind API and representation.
// Recursive root is replaced by two iterative passes, including path compression.
// This stays in experiments until its generated model and complete call proofs agree.
class UnionFind {
  std::vector<int> _ps;
  int _num_groups, _n;

public:
  UnionFind() : _num_groups(0), _n(0) {}
  UnionFind(int n) : _ps(n, -1), _num_groups(n), _n(n) { assert(n >= 0); }

  int unite(int a, int b) {
    assert(0 <= a && a < _n);
    assert(0 <= b && b < _n);
    int x = root(a), y = root(b);
    if (x == y) return x;
    if (-_ps[x] < -_ps[y]) {
      int t = x;
      x = y;
      y = t;
    }
    _ps[x] = _ps[x] + _ps[y];
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
    int r = a;
    while (_ps[r] >= 0) r = _ps[r];
    while (a != r) {
      int next = _ps[a];
      _ps[a] = r;
      a = next;
    }
    return r;
  }
  int size(int a) {
    assert(0 <= a && a < _n);
    return -_ps[root(a)];
  }
  int num_groups() { return _num_groups; }
};

} // namespace cp

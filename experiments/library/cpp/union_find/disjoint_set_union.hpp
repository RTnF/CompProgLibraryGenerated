#pragma once
#include "template/small_template.hpp"

// 素集合データ構造 (Union Find)
class UnionFind {
  // root: -1 * 連結成分サイズ, その他: 親
  vector<int> _ps;
  int _num_groups, _n;

public:
  UnionFind() : _num_groups(0), _n(0) {}
  UnionFind(int n) : _ps(n, -1), _num_groups(n), _n(n) { assert(n >= 0); }

  // a と b を結合する
  int unite(int a, int b) {
    assert(0 <= a && a < _n);
    assert(0 <= b && b < _n);
    int x = root(a), y = root(b);
    if (x == y) {
      return x;
    }
    if (-_ps[x] < -_ps[y]) {
      swap(x, y);
    }
    _ps[x] += _ps[y];
    _ps[y] = x;
    _num_groups--;
    return x;
  }

  // a と b が同じ木に属するか
  bool same(int a, int b) {
    assert(0 <= a && a < _n);
    assert(0 <= b && b < _n);
    return root(a) == root(b);
  }

  // a が属する木の根
  int root(int a) {
    assert(0 <= a && a < _n);
    if (_ps[a] < 0) {
      return a;
    }
    return _ps[a] = root(_ps[a]);
  }

  // a が属する木のサイズ
  int size(int a) {
    assert(0 <= a && a < _n);
    return -_ps[root(a)];
  }

  // 森の木の数
  int num_groups() { return _num_groups; }
};
#pragma once
#include "Template/SmallTemplate.hpp"

// based on ACL
class DisjointSet {
  int _n;
  // root: -1 * 連結成分サイズ
  // otherwise: parent
  vector<int> ps;
  int num_groups;

public:
  DisjointSet(int n): _n(n), ps(n, -1), num_groups(n) {}

  int unite(int a, int b) {
    int x = root(a), y = root(b);
    if(x == y) {
      return x;
    }
    if(-ps[x] < -ps[y]) {
      swap(x, y);
    }
    ps[x] += ps[y];
    ps[y] = x;
    num_groups--;
    return x;
  }
  bool same(int a, int b) { return root(a) == root(b); }
  int root(int a) {
    if(ps[a] < 0) {
      return a;
    }
    return ps[a] = root(ps[a]);
  }
  int size(int a) { return -ps[root(a)]; }
  int getNum() { return num_groups; }
};
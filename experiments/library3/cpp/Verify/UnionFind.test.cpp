#define PROBLEM "https://onlinejudge.u-aizu.ac.jp/courses/library/3/DSL/1/DSL_1_A"
#include "Graph/UnionFind.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int n, q;
  cin >> n >> q;
  DisjointSet uf(n);
  while(q--) {
    int com, x, y;
    cin >> com >> x >> y;
    if(com) {
      cout << uf.same(x, y) << '\n';
    } else {
      uf.unite(x, y);
    }
  }
}
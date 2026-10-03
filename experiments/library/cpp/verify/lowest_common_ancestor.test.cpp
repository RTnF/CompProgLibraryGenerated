#define PROBLEM "https://judge.yosupo.jp/problem/lca"
#include "tree/tree.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int n, q;
  cin >> n >> q;
  vector<int> p(n);
  p[0] = 0;
  for (int i = 1; i < n; i++) {
    cin >> p[i];
  }
  Tree t(p);
  t.build_ancestor();
  while (q--) {
    int u, v;
    cin >> u >> v;
    cout << t.lowest_common_ancestor(u, v) << '\n';
  }
}
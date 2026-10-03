#define PROBLEM "https://judge.yosupo.jp/problem/jump_on_tree"
#include "tree/tree.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int n, q;
  cin >> n >> q;
  vector<int> a(n - 1), b(n - 1);
  for (int i = 0; i < n - 1; i++) {
    cin >> a[i] >> b[i];
  }
  Tree<int> t(0, a, b);
  t.build_ancestor();
  while (q--) {
    int u, v, i;
    cin >> u >> v >> i;
    int lca = t.lowest_common_ancestor(u, v);
    int d1 = t.depth(u) - t.depth(lca);
    int d2 = t.depth(v) - t.depth(lca);
    if (i > d1 + d2) {
      cout << "-1\n";
    } else if (i < d1) {
      cout << t.ancestor(u, i) << '\n';
    } else {
      cout << t.ancestor(v, d1 + d2 - i) << '\n';
    }
  }
}
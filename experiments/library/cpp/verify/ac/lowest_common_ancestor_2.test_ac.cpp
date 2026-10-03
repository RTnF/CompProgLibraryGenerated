#define PROBLEM "https://atcoder.jp/contests/past201912-open/tasks/past201912_k"
#include "tree/tree.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  
  int n;
  cin >> n;
  vector<int> p(n);
  for (int i = 0; i < n; i++) {
    cin >> p[i];
    p[i]--;
  }
  Tree t(p);
  t.build_ancestor();
  int q;
  cin >> q;
  while (q--) {
    int a, b;
    cin >> a >> b;
    a--, b--;
    cout << (t.lowest_common_ancestor(a, b) == b ? "Yes\n" : "No\n");
  }
}
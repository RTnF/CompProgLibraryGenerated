#define PROBLEM "https://atcoder.jp/contests/dp/tasks/dp_v"
#include "tree/tree.hpp"
#include "modint/dynamic_modint.hpp"

void solve() {
  int n;
  cin >> n >> DynamicModInt::m;
  vector<int> x(n - 1), y(n - 1);
  for (int i = 0; i < n - 1; i++) {
    cin >> x[i] >> y[i];
    x[i]--;
    y[i]--;
  }
  Tree tree(0, x, y);
  auto dp = tree.full_tree_dp(DynamicModInt(1), [](DynamicModInt a, DynamicModInt b) -> auto {
    return a * b;
  }, [](DynamicModInt a) -> auto { return a + 1; });
  for (auto &&e: dp) {
    cout << e - 1 << '\n';
  }
}

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  cout << fixed << setprecision(20);
  //*
  solve();
  /*/
  ll _cases;
  cin >> _cases;
  while (_cases--) solve();
  //*/
}
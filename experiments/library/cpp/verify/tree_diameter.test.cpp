#define PROBLEM "https://judge.yosupo.jp/problem/tree_diameter"
#include "tree/tree.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int N;
  cin >> N;
  vector<int> a(N - 1), b(N - 1);
  vector<ll> c(N - 1);
  for (int i = 0; i < N - 1; i++) {
    cin >> a[i] >> b[i] >> c[i];
  }
  Tree t(0, a, b, c);
  auto [df, dt, d] = t.diameter();
  auto path = t.path(df, dt);
  cout << d << ' ' << path.size() << '\n';
  for (int i = 0; i < (int)path.size(); i++) {
    cout << path[i] << " \n"[i + 1 == (int)path.size()];
  }
}
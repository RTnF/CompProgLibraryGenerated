#define PROBLEM "https://atcoder.jp/contests/past202203-open/tasks/past202203_j"
#include "modint/modint.hpp"

int main() {
  init();
  cin.tie(0);
  ios::sync_with_stdio(false);
  int n, k;
  cin >> n >> k;
  vector<int> at(n);
  for (int i = 0; i < n; i++) {
    cin >> at[i];
  }
  sort(at.begin(), at.end());
  vector<mint> a(n);
  for (int i = 0; i < n; i++) {
    a[i] = at[i];
  }

  mint ans = 0;
  for (int i = k - 1; i < n; i++) {
    ans += C(i, k - 1) * a[i];
    ans -= C(i, k - 1) * a[n - 1 - i];
  }
  ans /= C(n, k);
  cout << ans << '\n';
}
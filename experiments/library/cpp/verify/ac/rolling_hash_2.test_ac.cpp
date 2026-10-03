#define PROBLEM "https://atcoder.jp/contests/abc141/tasks/abc141_e"
#include "string/rolling_hash.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);

  int n;
  cin >> n;
  string s;
  cin >> s;
  SimpleRollingHash rh(s);

  int ans = 0;
  for (int sz = 1; sz <= n / 2; sz++) {
    unordered_set<ull> hashes;
    for (int i = 0; i <= n - sz * 2; i++) {
      hashes.emplace(rh.hash(i, i + sz));
      if (hashes.contains(rh.hash(i + sz, i + sz * 2)) && ans < sz) {
        ans = sz;
      }
    }
  }
  cout << ans << "\n";
}
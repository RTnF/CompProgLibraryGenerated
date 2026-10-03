#define PROBLEM "https://atcoder.jp/contests/past202203-open/tasks/past202203_n"
#include "fps/convolution.hpp"

const int MAX = 200003;

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int n;
  cin >> n;
  vector<ll> a(MAX, 0);
  for (int i = 0; i < n; i++) {
    int m;
    cin >> m;
    a[m]++;
  }
  vector<ll> b = a;
  reverse(b.begin(), b.end());
  auto conv = convolution_ll(a, b);
  ll ans = 0;
  for (int i = 0; i < MAX - 1; i++) {
    if (conv[i] > 0) {
      ans++;
    }
  }
  cout << ans * 2 + 1 << '\n';
}
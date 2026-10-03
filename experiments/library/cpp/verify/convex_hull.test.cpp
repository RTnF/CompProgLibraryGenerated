#define PROBLEM "https://judge.yosupo.jp/problem/static_convex_hull"
#include "geometry/polygon.hpp"

void solve() {
  int n;
  cin >> n;
  Points<ll> ps;
  ps.reserve(n);
  while (n--) {
    ll x, y;
    cin >> x >> y;
    ps.emplace_back(x, y);
  }
  sort(ps.begin(), ps.end(), Vec2<ll>::compare_x);
  ps.erase(unique(ps.begin(), ps.end()), ps.end());
  auto ch = convex_hull(ps);
  cout << ch.size() << '\n';
  for (auto &&e : ch) {
    cout << e.x << ' ' << e.y << '\n';
  }
}

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int n;
  cin >> n;
  while (n--) {
    solve();
  }
}
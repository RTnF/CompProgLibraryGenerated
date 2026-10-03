#define PROBLEM "https://judge.yosupo.jp/problem/sort_points_by_argument"
#include "geometry/vector.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int n;
  cin >> n;
  vector<Vec2<ll>> ps;
  ps.reserve(n);
  while (n--) {
    ll x, y;
    cin >> x >> y;
    ps.emplace_back(x, y);
  }
  sort(ps.begin(), ps.end(), Vec2<ll>::compare_arg);
  for (auto &&p : ps) {
    cout << p.x << ' ' << p.y << '\n';
  }
}
#define PROBLEM "https://atcoder.jp/contests/past202112-open/tasks/past202112_n"
#define ERROR 1e-8
#include "geometry/polygon.hpp"

void solve() {
  int n, m;
  cin >> n >> m;
  Polygon<ld> S(n), T(m);
  for (int i = 0; i < n; i++) {
    ld x, y;
    cin >> x >> y;
    S[i] = Vec2<ld>(x, y);
  }
  for (int i = 0; i < m; i++) {
    ld x, y;
    cin >> x >> y;
    T[i] = Vec2<ld>(x, y);
  }
  vector<Vec2<ld>> ps;
  for (int i = 0; i < n; i++) {
    int ii = i + 1 == n ? 0 : i + 1;
    for (int j = 0; j < m; j++) {
      int jj = j + 1 == m ? 0 : j + 1;
      auto seg_inter =
          segment_intersection(Line{S[i], S[ii]}, Line{T[j], T[jj]});
      if (seg_inter) {
        ps.emplace_back(seg_inter.value());
      }
    }
  }
  for (int i = 0; i < n; i++) {
    if (in_polygon(S[i], T)) {
      ps.emplace_back(S[i]);
    }
  }
  for (int i = 0; i < m; i++) {
    if (in_polygon(T[i], S)) {
      ps.emplace_back(T[i]);
    }
  }
  auto ch = convex_hull(ps);
  cout << area(ch) << '\n';
}

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  cout << fixed << setprecision(20);
  solve();
}
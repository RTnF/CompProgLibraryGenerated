#define PROBLEM "https://atcoder.jp/contests/past202303-open/tasks/past202303_j"
#include "string/rolling_hash.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);

  int h, w;
  cin >> h >> w;
  vector<string> s(h), t(h);
  for (int i = 0; i < h; i++) {
    cin >> s[i];
  }
  for (int i = 0; i < h; i++) {
    cin >> t[i];
  }

  string ss, tt;
  for (int j = 0; j < w; j++) {
    for (int i = 0; i < h; i++) {
      ss += s[i][j];
      tt += t[i][j];
    }
  }
  ss += ss;
  RollingHash r(ss, 3);
  vector<int> v;
  for (int i = 0; i < w; i++) {
    v.emplace_back(i * h);
  }
  cout << (r.match_custom(tt, v) != string::npos ? "Yes\n" : "No\n");
}
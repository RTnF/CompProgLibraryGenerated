#define PROBLEM "https://onlinejudge.u-aizu.ac.jp/courses/lesson/1/ALDS1/1/ALDS1_1_D"
#include "template/small_template.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);

  int n;
  cin >> n;
  ll R;
  cin >> R;

  ll maxv = -INF;
  ll minv = R;
  for (int i = 1; i < n; i++) {
    cin >> R;
    maxv = max(maxv, R - minv);
    minv = min(minv, R);
  }

  cout << maxv << endl;
}
#define PROBLEM                                                                \
  "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/5/GRL_5_A"
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
  cout << get<2>(t.diameter()) << '\n';
}
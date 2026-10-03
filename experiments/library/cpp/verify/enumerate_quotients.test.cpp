#define PROBLEM "https://judge.yosupo.jp/problem/enumerate_quotients"
#include "number_theory/enumerate_quotients.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);

  ull x;
  cin >> x;
  auto q = enumerate_quotients(x);
  cout << q.size() << '\n';
  for (ull y : q) {
    cout << y << ' ';
  }
}
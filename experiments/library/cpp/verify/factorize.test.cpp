#define PROBLEM "https://onlinejudge.u-aizu.ac.jp/courses/library/6/NTL/1/NTL_1_A"
#include "number_theory/factorize.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  ull n;
  cin >> n;
  auto f = factorize(n);
  cout << n << ':';
  for (auto p: f) {
    cout << ' ' << p;
  }
  cout << '\n';
}
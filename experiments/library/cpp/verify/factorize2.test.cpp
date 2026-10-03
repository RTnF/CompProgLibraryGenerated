#define PROBLEM "https://judge.yosupo.jp/problem/factorize"
#include "number_theory/factorize.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int q;
  cin >> q;
  while (q--) {
    ull n;
    cin >> n;
    auto f = factorize(n);
    cout << f.size();
    for (auto p: f) {
      cout << ' ' << p;
    }
    cout << '\n';
  }
}
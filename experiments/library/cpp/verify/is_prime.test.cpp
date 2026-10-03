#define PROBLEM "https://judge.yosupo.jp/problem/primality_test"
#include "number_theory/is_prime.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int n;
  cin >> n;
  while (n--) {
    ull x;
    cin >> x;
    cout << (is_prime(x) ? "Yes" : "No") << '\n';
  }
}
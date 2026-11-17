#include "template/small_template.hpp"
#include "modint/modint.hpp"
#include <cassert>
#include <cstdint>

int main() {
  static_assert(MAX_FAC == 20000003);
  static_assert(std::is_same_v<mint, ModInt<998244353u>>);
  static_assert(std::is_same_v<mint17, ModInt<1000000007u>>);
  assert(fac[0].get() == 0 && fac[MAX_FAC - 1].get() == 0);
  init();
  // Check every table entry against plain integer arithmetic, including the
  // last entry. Neither the bound nor the original global API is replaced.
  std::uint64_t expected = 1;
  for (int n = 0; n < MAX_FAC; ++n) {
    if (n != 0) expected = expected * n % 998244353u;
    assert(fac[n].get() == expected);
  }
  const int rows[] = {0, 1, 2, 7, 100, MAX_FAC - 1};
  for (int n : rows) {
    assert(C(n, 0).get() == 1 && C(n, n).get() == 1);
    if (n >= 1) assert(C(n, 1).get() == static_cast<unsigned>(n));
    if (n >= 2) {
      const auto pairs = std::uint64_t(n) * (n - 1) / 2 % 998244353u;
      assert(C(n, 2).get() == pairs && C(n, n - 2).get() == pairs);
    }
    if (n >= 7) {
      assert(C(n, 3).get() == C(n, n - 3).get());
      assert(C(n, 3).get() == (C(n - 1, 2) + C(n - 1, 3)).get());
    }
  }
}

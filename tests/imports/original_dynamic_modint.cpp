#include "template/small_template.hpp"
#include "modint/dynamic_modint.hpp"
#include <cassert>
#include <sstream>
#include <vector>

int main() {
  DynamicModInt::m = 7;
  assert(DynamicModInt(-7).get() == 0);
  assert(DynamicModInt(static_cast<__int128>(-1)).get() == 6);
  DynamicModInt value(-1);
  value.set(-14);
  assert(value.get() == 0);
  value.set<const __int128>(-1);
  assert(value.get() == 6);
  assert(DynamicModInt(2).pow(INT64_MIN).get() == 2);
  DynamicModInt::m = 4294967291u;
  assert((DynamicModInt(4294967290u) + DynamicModInt(10)).get() == 9);
  assert((DynamicModInt(0) - DynamicModInt(4294967290u)).get() == 1);
  // An inverse cache initialized under one large prime must not survive a change.
  DynamicModInt::m = 1000000007u;
  assert(factorial_inv(2).get() == 500000004u);
  DynamicModInt::m = 998244353u;
  assert(factorial_inv(2).get() == 499122177u);
  DynamicModInt::m = 7;
  assert(factorial_inv(0).get() == 1);

  for (unsigned modulus : {2u, 3u, 7u, 11u, 101u, 7u, 2u}) {
    DynamicModInt::m = modulus;
    std::vector<unsigned> row{1};
    unsigned long long factorial_value = 1;
    for (unsigned n = 0; n < 2 * modulus - 1; ++n) {
      if (n) factorial_value = factorial_value * n % modulus;
      assert(factorial(n).get() == factorial_value);
      if (n < modulus) {
        assert(factorial_inv(n).get() * factorial_value % modulus == 1);
      }
      for (unsigned k = 0; k <= n; ++k) {
        if (k < modulus && n - k < modulus) {
          assert(C(n, k).get() == row[k]);
        }
      }
      row.push_back(0);
      for (unsigned k = n + 1; k > 0; --k) {
        row[k] = (row[k] + row[k - 1]) % modulus;
      }
    }
  }
  for (unsigned modulus : {998244353u, 1000000007u, 998244353u}) {
    DynamicModInt::m = modulus;
    unsigned long long expected = 1;
    for (unsigned n = 1; n <= 100001; ++n) {
      expected = expected * n % modulus;
      if (n == 99999 || n == 100000 || n == 100001) {
        assert(factorial(n).get() == expected);
        assert(factorial_inv(n).get() * expected % modulus == 1);
      }
    }
  }
  value.set(123);
  std::istringstream empty;
  assert(&(empty >> value) == &empty && empty.fail() && value.get() == 0);
}

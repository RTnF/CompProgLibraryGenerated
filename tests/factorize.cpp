#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number_theory/factorize.hpp"
#include <cassert>
#include <numeric>
#include <random>

// A copy of the original experiments/library/cpp/number_theory/factorize.hpp (lambdas, std::gcd, __uint128_t and the
// counts of array/search_util.hpp), with is_prime from the library.
namespace orig {
std::vector<ull> factorize_in(ull n) {
  auto f = [n](ull x, ull c) -> ull { return ((__uint128_t)x * x + c) % n; };
  auto rho = [f](ull m, ull c) -> ull {
    ull x = 2, y = 2, d = 1;
    while (d == 1) {
      x = f(x, c);
      y = f(f(y, c), c);
      d = std::gcd(x > y ? x - y : y - x, m);
    }
    return d == m ? 0 : d;
  };
  std::vector<ull> factor;
  while (!(n & 1)) {
    factor.emplace_back(2);
    n >>= 1;
  }
  if (n <= 1) return factor;
  if (cp::is_prime(n)) {
    factor.emplace_back(n);
    return factor;
  }
  ull r = 0;
  for (int i = 1; !r && i <= 3; ++i) r = rho(n, i);
  if (r) {
    auto f1 = factorize_in(r);
    auto f2 = factorize_in(n / r);
    factor.insert(factor.end(), f1.begin(), f1.end());
    factor.insert(factor.end(), f2.begin(), f2.end());
    return factor;
  }
  for (ull i = 3; i * i <= n; i += 2) {
    while (n % i == 0) {
      factor.emplace_back(i);
      n /= i;
    }
  }
  if (n > 1) factor.emplace_back(n);
  return factor;
}
std::vector<ull> factorize(ull n) {
  auto f = factorize_in(n);
  std::sort(f.begin(), f.end());
  return f;
}
std::vector<std::pair<ull, int>> factorize_count(ull n) {
  auto v = factorize(n);
  std::vector<std::pair<ull, int>> ret;
  for (int i = 0; i < (int)v.size(); i++) {
    if (i == 0 || ret.back().first != v[i]) ret.emplace_back(v[i], 1);
    else ret.back().second++;
  }
  return ret;
}
std::vector<ull> divisors(ull n) {
  if (n == 1) return {1};
  auto factor = factorize_count(n);
  int num_factor = factor.size();
  std::vector<ull> div;
  auto dfs = [&](auto &Self, ull f, int i) -> void {
    ull p = 1;
    if (i == num_factor - 1) {
      for (int j = 0; j <= factor[i].second; j++) {
        div.emplace_back(f * p);
        p *= factor[i].first;
      }
    } else {
      for (int j = 0; j <= factor[i].second; j++) {
        Self(Self, f * p, i + 1);
        p *= factor[i].first;
      }
    }
  };
  dfs(dfs, 1, 0);
  std::sort(div.begin(), div.end());
  return div;
}
}  // namespace orig

static void check(ull n) {
  std::vector<ull> f = cp::factorize(n);
  assert(f == orig::factorize(n));
  ull prod = 1;
  for (size_t i = 0; i < f.size(); i++) {
    assert(cp::is_prime(f[i]));
    assert(i == 0 || f[i - 1] <= f[i]);
    prod *= f[i];
  }
  assert(prod == n);
  assert(cp::factorize_count(n) == orig::factorize_count(n));
  if (n <= (1ULL << 40) || f.size() <= 6) assert(cp::divisors(n) == orig::divisors(n));
}

int main() {
  std::mt19937_64 rng(20261122);
  for (ull n = 1; n <= 3000; n++) {
    check(n);
    std::vector<ull> bf;
    ull m = n;
    for (ull p = 2; p * p <= m; p++)
      while (m % p == 0) bf.push_back(p), m /= p;
    if (m > 1) bf.push_back(m);
    assert(cp::factorize(n) == bf);
    std::vector<ull> dv;
    for (ull d = 1; d <= n; d++)
      if (n % d == 0) dv.push_back(d);
    assert(cp::divisors(n) == dv);
  }
  for (int t = 0; t < 2000; t++) check(rng() % 1000000000000ULL + 1);
  for (int t = 0; t < 300; t++) check(rng() | 1);
  const ull ps[] = {2, 3, 1000000007ULL, 998244353ULL, 4294967291ULL, 4294967311ULL, 18446744073709551557ULL};
  for (ull a : ps)
    for (ull b : ps)
      if (b <= ~0ULL / a) check(a * b);
  check(1ULL << 63);
  check(~0ULL);
  check(4294967291ULL * 4294967291ULL);
  // direct calls of the parts
  assert(cp::factorize_f(5, 1, 7) == 5);
  assert(cp::factorize_rho(8051, 1, 8051) == 97 || cp::factorize_rho(8051, 1, 8051) == 83);
  std::vector<std::pair<ull, int>> fc = {{2, 2}, {3, 1}};
  std::vector<ull> div;
  cp::divisors_dfs(fc, div, 1, 0);
  assert((div == std::vector<ull>{1, 3, 2, 6, 4, 12}));
  return 0;
}

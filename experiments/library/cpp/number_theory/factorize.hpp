#pragma once
#include "array/search_util.hpp"
#include "number_theory/is_prime.hpp"
#include "template/small_template.hpp"

namespace in {
vector<ull> factorize(ull n) {
  auto f = [n](ull x, ull c) -> ull { return ((__uint128_t)x * x + c) % n; };
  auto rho = [f](ull m, ull c) -> ull {
    ull x = 2, y = 2, d = 1;
    while (d == 1) {
      x = f(x, c);
      y = f(f(y, c), c);
      d = gcd(x > y ? x - y : y - x, m);
    }
    return d == m ? 0 : d;
  };
  vector<ull> factor;
  while (!(n & 1)) {
    factor.emplace_back(2);
    n >>= 1;
  }
  if (n <= 1) {
    return factor;
  }
  if (is_prime(n)) {
    factor.emplace_back(n);
    return factor;
  }
  ull r = 0;
  for (int i = 1; !r && i <= 3; ++i) {
    r = rho(n, i);
  }
  if (r) {
    auto f1 = factorize(r);
    auto f2 = factorize(n / r);
    factor.insert(factor.end(), f1.begin(), f1.end());
    factor.insert(factor.end(), f2.begin(), f2.end());
    return factor;
  } else {
    // fallback O(sqrt(n))
    for (ull i = 3; i * i <= n; i += 2) {
      while (n % i == 0) {
        factor.emplace_back(i);
        n /= i;
      }
    }
    if (n > 1) {
      factor.emplace_back(n);
    }
    return factor;
  }
  return factor;
}
}; // namespace in

vector<ull> factorize(ull n) {
  auto f = in::factorize(n);
  sort(f.begin(), f.end());
  return f;
}

vector<pair<ull, int>> factorize_count(ull n) { return counts(factorize(n)); }

vector<ull> divisors(ull n) {
  if (n == 1) {
    return {1};
  }
  auto factor = factorize_count(n);
  int num_factor = factor.size();
  vector<ull> div;
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
  sort(div.begin(), div.end());
  return div;
}

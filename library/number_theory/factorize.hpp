#pragma once
#include <algorithm>
#include <cstdint>
#include <utility>
#include <vector>
#include "gcd_u64.hpp"
#include "is_prime.hpp"

namespace cp {

// Prime factorization by Pollard's rho method (experiments/library/cpp/number_theory/factorize.hpp): factorize,
// factorize_count and divisors with the original signatures. The lambdas of the original are the functions
// factorize_f, factorize_rho (x^2 + c and the rho walk), factorize_unsorted (in::factorize) and divisors_dfs.
// Preconditions: n >= 1 (the original loops forever at n = 0). The prime factors are prime under the hypothesis
// MRWitnessSet of is_prime (the 12 bases decide every 64 bit integer); without it the factors still multiply to n.
// Time: O(n) proved for every n (Pollard's rho has no proved sublinear bound); the expected O(n^{1/4}) of rho is
// not proved. divisors: O(n) proved, the number of divisors times O(log n) in practice.

// x^2 + c (mod n), the step of Pollard's rho method. Precondition: n >= 1.
inline std::uint64_t factorize_f(std::uint64_t x, std::uint64_t c, std::uint64_t n) {
  return (std::uint64_t)(((__uint128_t)x * x + c) % n);
}

// Pollard's rho with Floyd's cycle detection: a divisor 1 < d < m of m, or 0 when the walk closes first.
// Preconditions: n >= 3, m >= 2 (factorize_unsorted calls it with m = n); at most n iterations.
inline std::uint64_t factorize_rho(std::uint64_t m, std::uint64_t c, std::uint64_t n) {
  std::uint64_t x = 2, y = 2, d = 1;
  while (d == 1) {
    x = factorize_f(x, c, n);
    y = factorize_f(factorize_f(y, c, n), c, n);
    d = gcd_u64(x > y ? x - y : y - x, m);
  }
  return d == m ? 0 : d;
}

// The prime factors of n (with repetition, unsorted). Precondition: n >= 1.
// The trial division of the fallback tests i <= n / i instead of the original i * i <= n (the same value whenever
// i * i does not wrap, which the original never reaches; docs/factorize.md).
inline std::vector<std::uint64_t> factorize_unsorted(std::uint64_t n) {
  std::vector<std::uint64_t> factor;
  while (!(n & 1)) {
    factor.push_back(2);
    n >>= 1;
  }
  if (n <= 1) {
    return factor;
  }
  if (is_prime(n)) {
    factor.push_back(n);
    return factor;
  }
  std::uint64_t r = 0;
  for (int i = 1; !r && i <= 3; ++i) {
    r = factorize_rho(n, i, n);
  }
  if (r) {
    std::vector<std::uint64_t> f1 = factorize_unsorted(r);
    std::vector<std::uint64_t> f2 = factorize_unsorted(n / r);
    for (int j = 0; j < (int)f1.size(); j++) factor.push_back(f1[j]);
    for (int j = 0; j < (int)f2.size(); j++) factor.push_back(f2[j]);
    return factor;
  }
  for (std::uint64_t i = 3; i <= n / i; i += 2) {
    while (n % i == 0) {
      factor.push_back(i);
      n /= i;
    }
  }
  if (n > 1) {
    factor.push_back(n);
  }
  return factor;
}

// The prime factors of n with repetition in increasing order. Precondition: n >= 1.
inline std::vector<std::uint64_t> factorize(std::uint64_t n) {
  std::vector<std::uint64_t> f = factorize_unsorted(n);
  std::sort(f.begin(), f.end());
  return f;
}

// (p, e) for each distinct prime factor p of n with its exponent e, in increasing order of p.
inline std::vector<std::pair<std::uint64_t, int>> factorize_count(std::uint64_t n) {
  std::vector<std::uint64_t> f = factorize(n);
  std::vector<std::pair<std::uint64_t, int>> res;
  for (int i = 0; i < (int)f.size(); i++) {
    if (res.empty() || res.back().first != f[i]) {
      res.emplace_back(f[i], 1);
    } else {
      res.back().second++;
    }
  }
  return res;
}

// Appends f * p_i^{j_i} * ... * p_k^{j_k} (0 <= j_l <= e_l) for the runs i..k of factor to div, in lexicographic order
// of (j_i, ..., j_k) (the recursive lambda of the original). Preconditions: 0 <= i < factor.size(), 0 < e_l < 64,
// p_l >= 1, f >= 1 and f * prod_{l >= i} p_l^{e_l} < 2^64.
inline void divisors_dfs(const std::vector<std::pair<std::uint64_t, int>> &factor, std::vector<std::uint64_t> &div,
                         std::uint64_t f, int i) {
  int num_factor = factor.size();
  std::uint64_t p = 1;
  if (i == num_factor - 1) {
    for (int j = 0; j <= factor[i].second; j++) {
      div.push_back(f * p);
      p *= factor[i].first;
    }
  } else {
    for (int j = 0; j <= factor[i].second; j++) {
      divisors_dfs(factor, div, f * p, i + 1);
      p *= factor[i].first;
    }
  }
}

// The divisors of n in increasing order. Precondition: n >= 1.
inline std::vector<std::uint64_t> divisors(std::uint64_t n) {
  if (n == 1) {
    return std::vector<std::uint64_t>(1, 1);
  }
  std::vector<std::pair<std::uint64_t, int>> factor = factorize_count(n);
  std::vector<std::uint64_t> div;
  divisors_dfs(factor, div, 1, 0);
  std::sort(div.begin(), div.end());
  return div;
}

}  // namespace cp

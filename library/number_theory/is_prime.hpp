#pragma once
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// Deterministic Miller-Rabin primality test for 64 bit integers (is_prime in experiments/library/cpp/number_theory/is_prime.hpp).
// The original multiplies with __uint128_t; here the products are computed by modular doubling, so every intermediate value
// stays below 2^64 and the results are the same. The bases are the first twelve primes 2, 3, ..., 37, taken in this order
// while base <= n - 2, as in the original.

// (a * b) mod m for a, b < m by binary doubling: the sums r + x and x + x (both below 2m) are reduced without overflow because
// u + v wraps around 2^64 only when u >= m - v. Time O(64), extra space O(1).
[[gnu::always_inline]] inline unsigned long long mul_mod_u64(unsigned long long a, unsigned long long b, unsigned long long m) {
  unsigned long long r = 0;
  unsigned long long x = a;
  unsigned long long y = b;
  while (y != 0) {
    if (y % 2 == 1) {
      unsigned long long t = r + x;
      if (r >= m - x) {
        t = r - (m - x);
      }
      r = t;
    }
    unsigned long long u = x + x;
    if (x >= m - x) {
      u = x - (m - x);
    }
    x = u;
    y = y / 2;
  }
  return r;
}

// x^y mod m for x < m and 2 <= m by binary exponentiation. Time O(64 * 64), extra space O(1).
[[gnu::always_inline]] inline unsigned long long pow_mod_u64(unsigned long long x, unsigned long long y, unsigned long long m) {
  unsigned long long pm = 1;
  unsigned long long b = x;
  unsigned long long e = y;
  while (e != 0) {
    if (e % 2 == 1) {
      unsigned long long npm = mul_mod_u64(pm, b, m);
      pm = npm;
    }
    unsigned long long nb = mul_mod_u64(b, b, m);
    b = nb;
    e = e / 2;
  }
  return pm;
}

// The i-th Miller-Rabin base: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 for i = 0, ..., 11 (37 for any larger i).
[[gnu::always_inline]] inline unsigned long long mr_base(int i) {
  unsigned long long p = 37;
  if (i == 0) {
    p = 2;
  }
  if (i == 1) {
    p = 3;
  }
  if (i == 2) {
    p = 5;
  }
  if (i == 3) {
    p = 7;
  }
  if (i == 4) {
    p = 11;
  }
  if (i == 5) {
    p = 13;
  }
  if (i == 6) {
    p = 17;
  }
  if (i == 7) {
    p = 19;
  }
  if (i == 8) {
    p = 23;
  }
  if (i == 9) {
    p = 29;
  }
  if (i == 10) {
    p = 31;
  }
  return p;
}

// True when `a` is a Miller-Rabin witness of the compositeness of n, for odd n >= 3 with n - 1 = d * 2^r (d odd) and
// 1 <= a <= n - 2: a^d != 1 and a^(d * 2^i) != n - 1 for all 0 <= i < r (modular products as above). Time O(64 * 64).
[[gnu::always_inline]] inline bool mr_witness(unsigned long long n, unsigned long long d, int r, unsigned long long a) {
  bool witness = false;
  unsigned long long x = pow_mod_u64(a, d, n);
  if (x != 1) {
    if (x != n - 1) {
      bool cf = true;
      int i = 0;
      while (i < r - 1 && cf) {
        unsigned long long nx = mul_mod_u64(x, x, n);
        x = nx;
        if (x == n - 1) {
          cf = false;
        }
        i = i + 1;
      }
      if (cf) {
        witness = true;
      }
    }
  }
  return witness;
}

// Miller-Rabin test with the bases above. true for every prime. For a composite n the test returns false when one of the
// bases is a witness; the bases 2, ..., 37 are a witness set for every n < 318665857834031151167461 (so for all 64 bit
// integers), which is a published computation and is NOT proved here (the Lean theorem assumes it as a hypothesis).
// Time O(12 * 64 * 64), extra space O(1).
inline bool is_prime(unsigned long long n) {
  bool result = true;
  if (n == 2) {
    result = true;
  } else if (n % 2 == 0 || n <= 1) {
    result = false;
  } else {
    int r = 0;
    unsigned long long d = n - 1;
    while (d % 2 == 0) {
      d = d / 2;
      r = r + 1;
    }
    for (int bi = 0; bi < 12; bi++) {
      unsigned long long p = mr_base(bi);
      if (p <= n - 2) {
        bool w = mr_witness(n, d, r, p);
        if (w) {
          result = false;
        }
      }
    }
  }
  return result;
}

} // namespace cp

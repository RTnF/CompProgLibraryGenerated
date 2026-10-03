#pragma once
#include "template/small_template.hpp"

// Miller test for 64bit
// https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test
bool is_prime(ull n) {
  if (n == 2) {
    return true;
  }
  if (!(n & 1) || n <= 1) {
    return false;
  }
  auto powmod64 = [](ull x, ull y, ull mod) -> ull {
    ull pm = 1;
    while (y) {
      if (y & 1) {
        pm = (__uint128_t)pm * x % mod;
      }
      x = (__uint128_t)x * x % mod;
      y >>= 1;
    }
    return pm;
  };
  int r = 0;
  ull d = n - 1;
  while (!(d & 1)) {
    d >>= 1;
    ++r;
  }
  for (const ull p : {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}) {
    if (p > n - 2) {
      break;
    }
    ull x = powmod64(p, d, n);
    if (x == 1 || x == n - 1) {
      continue;
    }
    bool cf = true;
    for (int i = 0; i < r - 1; ++i) {
      x = powmod64(x, 2, n);
      if (x == n - 1) {
        cf = false;
        break;
      }
    }
    if (cf) {
      return false;
    }
  }
  return true;
}
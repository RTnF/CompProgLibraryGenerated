#pragma once
#include "template/small_template.hpp"

constexpr ll safe_mod(ll x, ll m) {
  x %= m;
  if (x < 0) {
    x += m;
  }
  return x;
}

// ACL
// sum[i=0 .. n-1] floor((a*i + b) / m)
ull floor_sum_unsigned(ull n, ull m, ull a, ull b) {
  ull ans = 0;
  while (true) {
    if (a >= m) {
      ans += n * (n - 1) / 2 * (a / m);
      a %= m;
    }
    if (b >= m) {
      ans += n * (b / m);
      b %= m;
    }

    ull y_max = a * n + b;
    if (y_max < m) {
      break;
    }
    n = (ull)(y_max / m);
    b = (ull)(y_max % m);
    swap(m, a);
  }
  return ans;
}

// ACL
// sum[i=0 .. n-1] floor((a*i + b) / m)
// 0 <= n < 2^32
// 1 <= m < 2^32
ll floor_sum(ll n, ll m, ll a, ll b) {
  assert(0 <= n && n < (1ll << 32));
  assert(1 <= m && m < (1ll << 32));
  ull ans = 0;
  if (a < 0) {
    ull a2 = safe_mod(a, m);
    ans -= (ull)n * (n - 1) / 2 * ((a2 - a) / m);
    a = a2;
  }
  if (b < 0) {
    ull b2 = safe_mod(b, m);
    ans -= (ull)n * ((b2 - b) / m);
    b = b2;
  }
  return ans + floor_sum_unsigned(n, m, a, b);
}

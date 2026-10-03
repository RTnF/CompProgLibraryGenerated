#pragma once
#include "modint/modint.hpp"

// AtCoder Library

// @param m `1 <= m`
// @return x mod m
constexpr ll safe_mod(ll x, ll m) {
  x %= m;
  if (x < 0)
    x += m;
  return x;
}
// @param b `1 <= b`
// @return pair(g, x) s.t. g = gcd(a, b), xa = g (mod b), 0 <= x < b/g
constexpr pair<ll, ll> inv_gcd(ll a, ll b) {
  a = safe_mod(a, b);
  if (a == 0)
    return {b, 0};

  // Contracts:
  // [1] s - m0 * a = 0 (mod b)
  // [2] t - m1 * a = 0 (mod b)
  // [3] s * |m1| + t * |m0| <= b
  ll s = b, t = a;
  ll m0 = 0, m1 = 1;

  while (t) {
    ll u = s / t;
    s -= t * u;
    m0 -= m1 * u; // |m1 * u| <= |m1| * s <= b

    // [3]:
    // (s - t * u) * |m1| + t * |m0 - m1 * u|
    // <= s * |m1| - t * u * |m1| + t * (|m0| + |m1| * u)
    // = s * |m1| + t * |m0| <= b

    auto tmp = s;
    s = t;
    t = tmp;
    tmp = m0;
    m0 = m1;
    m1 = tmp;
  }
  // by [3]: |m0| <= b/g
  // by g != b: |m0| < b/g
  if (m0 < 0)
    m0 += b / s;
  return {s, m0};
}

// @param n `0 <= n`
// @param m `1 <= m`
// @return `(x ** n) % m`
constexpr long long pow_mod_constexpr(long long x, long long n, int m) {
  if (m == 1)
    return 0;
  unsigned int _m = (unsigned int)(m);
  unsigned long long r = 1;
  unsigned long long y = safe_mod(x, m);
  while (n) {
    if (n & 1)
      r = (r * y) % _m;
    y = (y * y) % _m;
    n >>= 1;
  }
  return r;
}

// Compile time primitive root
// @param m must be prime
// @return primitive root (and minimum in now)
constexpr int primitive_root_constexpr(int m) {
  if (m == 2)
    return 1;
  if (m == 167772161)
    return 3;
  if (m == 469762049)
    return 3;
  if (m == 754974721)
    return 11;
  if (m == 998244353)
    return 3;
  int divs[20] = {};
  divs[0] = 2;
  int cnt = 1;
  int x = (m - 1) / 2;
  while (x % 2 == 0)
    x /= 2;
  for (int i = 3; (long long)(i)*i <= x; i += 2) {
    if (x % i == 0) {
      divs[cnt++] = i;
      while (x % i == 0) {
        x /= i;
      }
    }
  }
  if (x > 1) {
    divs[cnt++] = x;
  }
  for (int g = 2;; g++) {
    bool ok = true;
    for (int i = 0; i < cnt; i++) {
      if (pow_mod_constexpr(g, (m - 1) / divs[i], m) == 1) {
        ok = false;
        break;
      }
    }
    if (ok)
      return g;
  }
}
template <int m> constexpr int primitive_root = primitive_root_constexpr(m);

// @param n `1 <= n`
// @return same with bit::countr_zero
constexpr int countr_zero_constexpr(unsigned int n) {
  int x = 0;
  while (!(n & (1 << x)))
    x++;
  return x;
}

template <class mint, int g = primitive_root<mint::mod()>> struct fft_info {
  static constexpr int rank2 = countr_zero_constexpr(mint::mod() - 1);
  array<mint, rank2 + 1> root;  // root[i]^(2^i) == 1
  array<mint, rank2 + 1> iroot; // root[i] * iroot[i] == 1

  array<mint, max(0, rank2 - 2 + 1)> rate2;
  array<mint, max(0, rank2 - 2 + 1)> irate2;

  array<mint, max(0, rank2 - 3 + 1)> rate3;
  array<mint, max(0, rank2 - 3 + 1)> irate3;

  fft_info() {
    root[rank2] = mint(g).pow((mint::mod() - 1) >> rank2);
    iroot[rank2] = root[rank2].inv();
    for (int i = rank2 - 1; i >= 0; i--) {
      root[i] = root[i + 1] * root[i + 1];
      iroot[i] = iroot[i + 1] * iroot[i + 1];
    }

    {
      mint prod = 1, iprod = 1;
      for (int i = 0; i <= rank2 - 2; i++) {
        rate2[i] = root[i + 2] * prod;
        irate2[i] = iroot[i + 2] * iprod;
        prod *= iroot[i + 2];
        iprod *= root[i + 2];
      }
    }
    {
      mint prod = 1, iprod = 1;
      for (int i = 0; i <= rank2 - 3; i++) {
        rate3[i] = root[i + 3] * prod;
        irate3[i] = iroot[i + 3] * iprod;
        prod *= iroot[i + 3];
        iprod *= root[i + 3];
      }
    }
  }
};

template <class mint> void butterfly(vector<mint> &a) {
  int n = int(a.size());
  int h = countr_zero((unsigned int)n);

  static const fft_info<mint> info;

  int len = 0; // a[i, i+(n>>len), i+2*(n>>len), ..] is transformed
  while (len < h) {
    if (h - len == 1) {
      int p = 1 << (h - len - 1);
      mint rot = 1;
      for (int s = 0; s < (1 << len); s++) {
        int offset = s << (h - len);
        for (int i = 0; i < p; i++) {
          auto l = a[i + offset];
          auto r = a[i + offset + p] * rot;
          a[i + offset] = l + r;
          a[i + offset + p] = l - r;
        }
        if (s + 1 != (1 << len))
          rot *= info.rate2[countr_zero(~(unsigned int)(s))];
      }
      len++;
    } else {
      // 4-base
      int p = 1 << (h - len - 2);
      mint rot = 1, imag = info.root[2];
      for (int s = 0; s < (1 << len); s++) {
        mint rot2 = rot * rot;
        mint rot3 = rot2 * rot;
        int offset = s << (h - len);
        for (int i = 0; i < p; i++) {
          auto mod2 = 1ULL * mint::mod() * mint::mod();
          auto a0 = 1ULL * a[i + offset].get();
          auto a1 = 1ULL * a[i + offset + p].get() * rot.get();
          auto a2 = 1ULL * a[i + offset + 2 * p].get() * rot2.get();
          auto a3 = 1ULL * a[i + offset + 3 * p].get() * rot3.get();
          auto a1na3imag = 1ULL * mint(a1 + mod2 - a3).get() * imag.get();
          auto na2 = mod2 - a2;
          a[i + offset] = a0 + a2 + a1 + a3;
          a[i + offset + 1 * p] = a0 + a2 + (2 * mod2 - (a1 + a3));
          a[i + offset + 2 * p] = a0 + na2 + a1na3imag;
          a[i + offset + 3 * p] = a0 + na2 + (mod2 - a1na3imag);
        }
        if (s + 1 != (1 << len))
          rot *= info.rate3[countr_zero(~(unsigned int)(s))];
      }
      len += 2;
    }
  }
}

template <class mint> void butterfly_inv(vector<mint> &a) {
  int n = int(a.size());
  int h = countr_zero((unsigned int)n);

  static const fft_info<mint> info;

  int len = h; // a[i, i+(n>>len), i+2*(n>>len), ..] is transformed
  while (len) {
    if (len == 1) {
      int p = 1 << (h - len);
      mint irot = 1;
      for (int s = 0; s < (1 << (len - 1)); s++) {
        int offset = s << (h - len + 1);
        for (int i = 0; i < p; i++) {
          auto l = a[i + offset];
          auto r = a[i + offset + p];
          a[i + offset] = l + r;
          a[i + offset + p] =
              (unsigned long long)(mint::mod() + l.get() - r.get()) *
              irot.get();
          ;
        }
        if (s + 1 != (1 << (len - 1)))
          irot *= info.irate2[countr_zero(~(unsigned int)(s))];
      }
      len--;
    } else {
      // 4-base
      int p = 1 << (h - len);
      mint irot = 1, iimag = info.iroot[2];
      for (int s = 0; s < (1 << (len - 2)); s++) {
        mint irot2 = irot * irot;
        mint irot3 = irot2 * irot;
        int offset = s << (h - len + 2);
        for (int i = 0; i < p; i++) {
          auto a0 = 1ULL * a[i + offset + 0 * p].get();
          auto a1 = 1ULL * a[i + offset + 1 * p].get();
          auto a2 = 1ULL * a[i + offset + 2 * p].get();
          auto a3 = 1ULL * a[i + offset + 3 * p].get();

          auto a2na3iimag =
              1ULL * mint((mint::mod() + a2 - a3) * iimag.get()).get();

          a[i + offset] = a0 + a1 + a2 + a3;
          a[i + offset + 1 * p] =
              (a0 + (mint::mod() - a1) + a2na3iimag) * irot.get();
          a[i + offset + 2 * p] =
              (a0 + a1 + (mint::mod() - a2) + (mint::mod() - a3)) * irot2.get();
          a[i + offset + 3 * p] =
              (a0 + (mint::mod() - a1) + (mint::mod() - a2na3iimag)) *
              irot3.get();
        }
        if (s + 1 != (1 << (len - 2)))
          irot *= info.irate3[countr_zero(~(unsigned int)(s))];
      }
      len -= 2;
    }
  }
}

template <class mint>
vector<mint> convolution_naive(const vector<mint> &a, const vector<mint> &b) {
  int n = int(a.size()), m = int(b.size());
  vector<mint> ans(n + m - 1);
  if (n < m) {
    for (int j = 0; j < m; j++) {
      for (int i = 0; i < n; i++) {
        ans[i + j] += a[i] * b[j];
      }
    }
  } else {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < m; j++) {
        ans[i + j] += a[i] * b[j];
      }
    }
  }
  return ans;
}

template <class mint>
vector<mint> convolution_fft(vector<mint> a, vector<mint> b) {
  int n = int(a.size()), m = int(b.size());
  int z = (int)bit_ceil((unsigned int)(n + m - 1));
  a.resize(z);
  butterfly(a);
  b.resize(z);
  butterfly(b);
  for (int i = 0; i < z; i++) {
    a[i] *= b[i];
  }
  butterfly_inv(a);
  a.resize(n + m - 1);
  mint iz = mint(z).inv();
  for (int i = 0; i < n + m - 1; i++)
    a[i] *= iz;
  return a;
}

template <class mint>
vector<mint> convolution(vector<mint> &&a, vector<mint> &&b) {
  int n = int(a.size()), m = int(b.size());
  if (!n || !m)
    return {};

  int z = (int)bit_ceil((unsigned int)(n + m - 1));
  assert((mint::mod() - 1) % z == 0);

  if (min(n, m) <= 60)
    return convolution_naive(a, b);
  return convolution_fft(a, b);
}

template <unsigned int mod = 998244353, class T>
vector<T> convolution(const vector<T> &a, const vector<T> &b) {
  int n = int(a.size()), m = int(b.size());
  if (!n || !m)
    return {};

  using Mint = ModInt<mod>;

  int z = (int)bit_ceil((unsigned int)(n + m - 1));
  assert((Mint::mod() - 1) % z == 0);

  vector<Mint> a2(n), b2(m);
  for (int i = 0; i < n; i++) {
    a2[i] = Mint(a[i]);
  }
  for (int i = 0; i < m; i++) {
    b2[i] = Mint(b[i]);
  }
  auto c2 = convolution(std::move(a2), std::move(b2));
  vector<T> c(n + m - 1);
  for (int i = 0; i < n + m - 1; i++) {
    c[i] = c2[i].get();
  }
  return c;
}

vector<ll> convolution_ll(const vector<ll> &a, const vector<ll> &b) {
  int n = int(a.size()), m = int(b.size());
  if (!n || !m)
    return {};

  static constexpr ull MOD1 = 754974721; // 2^24
  static constexpr ull MOD2 = 167772161; // 2^25
  static constexpr ull MOD3 = 469762049; // 2^26
  static constexpr ull M2M3 = MOD2 * MOD3;
  static constexpr ull M1M3 = MOD1 * MOD3;
  static constexpr ull M1M2 = MOD1 * MOD2;
  static constexpr ull M1M2M3 = MOD1 * MOD2 * MOD3;

  static constexpr ull i1 = inv_gcd(MOD2 * MOD3, MOD1).second;
  static constexpr ull i2 = inv_gcd(MOD1 * MOD3, MOD2).second;
  static constexpr ull i3 = inv_gcd(MOD1 * MOD2, MOD3).second;

  static constexpr int MAX_AB_BIT = 24;
  assert(n + m - 1 <= (1 << MAX_AB_BIT));

  auto c1 = convolution<MOD1>(a, b);
  auto c2 = convolution<MOD2>(a, b);
  auto c3 = convolution<MOD3>(a, b);

  vector<ll> c(n + m - 1);
  for (int i = 0; i < n + m - 1; i++) {
    ull x = 0;
    x += (c1[i] * i1) % MOD1 * M2M3;
    x += (c2[i] * i2) % MOD2 * M1M3;
    x += (c3[i] * i3) % MOD3 * M1M2;
    // B = 2^63, -B <= x, r(real value) < B
    // (x, x - M, x - 2M, or x - 3M) = r (mod 2B)
    // r = c1[i] (mod MOD1)
    // focus on MOD1
    // r = x, x - M', x - 2M', x - 3M' (M' = M % 2^64) (mod 2B)
    // r = x,
    //     x - M' + (0 or 2B),
    //     x - 2M' + (0, 2B or 4B),
    //     x - 3M' + (0, 2B, 4B or 6B) (without mod!)
    // (r - x) = 0, (0)
    //           - M' + (0 or 2B), (1)
    //           -2M' + (0 or 2B or 4B), (2)
    //           -3M' + (0 or 2B or 4B or 6B) (3) (mod MOD1)
    // we checked that
    //   ((1) mod MOD1) mod 5 = 2
    //   ((2) mod MOD1) mod 5 = 3
    //   ((3) mod MOD1) mod 5 = 4
    ll diff = c1[i] - safe_mod((ll)(x), (ll)(MOD1));
    if (diff < 0)
      diff += MOD1;
    static constexpr ull offset[5] = {0, 0, M1M2M3, 2 * M1M2M3, 3 * M1M2M3};
    x -= offset[diff % 5];
    c[i] = x;
  }

  return c;
}
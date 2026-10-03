#pragma once
#include "template/small_template.hpp"

/**
 * @brief 剰余を取り[0, mod)に収めるint
 * based on ACL
 * @tparam mod 素数に限る
 */
struct DynamicModInt {
  static uint32_t m;
  uint32_t x;

  DynamicModInt() : x(0) {}
  template <class T, enable_if_t<is_signed_v<T>> * = nullptr>
  DynamicModInt(T x_) : x(x_ < 0 ? x_ % (ll)m + (ll)m : x_ % (ll)m) {}
  template <class U, enable_if_t<!is_signed_v<U>> * = nullptr>
  DynamicModInt(U x_) : x(x_ % m) {}

  uint32_t get() const { return x; }
  template <class T, enable_if_t<is_signed_v<T>> * = nullptr> void set(T x_) {
    x = x_ < 0 ? x_ % (ll)m + (ll)m : x_ % (ll)m;
  }
  template <class U, enable_if_t<!is_signed_v<U>> * = nullptr> void set(U x_) {
    x = x_ % m;
  }

  DynamicModInt operator++(int) {
    DynamicModInt y = *this;
    ++*this;
    return y;
  }
  DynamicModInt &operator++() {
    x = x == m - 1 ? 0u : x + 1;
    return *this;
  }
  DynamicModInt operator--(int) {
    DynamicModInt y = *this;
    --*this;
    return y;
  }
  DynamicModInt &operator--() {
    x = x == 0u ? m - 1 : x - 1;
    return *this;
  }
  DynamicModInt &operator+=(const DynamicModInt &y) {
    x += y.x;
    if (x >= m) {
      x -= m;
    }
    return *this;
  }
  DynamicModInt &operator-=(const DynamicModInt &y) {
    x -= y.x;
    if (x >= m) {
      x += m;
    }
    return *this;
  }
  DynamicModInt &operator*=(const DynamicModInt &y) {
    x = (ull)x * (ull)y.x % m;
    return *this;
  }
  DynamicModInt &operator/=(const DynamicModInt &y) { return *this *= y.inv(); }
  DynamicModInt operator+() const { return *this; }
  DynamicModInt operator-() const { return DynamicModInt(m - x); }

  DynamicModInt pow(ll n) const {
    if (n < 0) {
      return pow(-n).inv();
    }
    DynamicModInt y = *this, r = 1;
    while (n) {
      if (n & 1) {
        r *= y;
      }
      y *= y;
      n >>= 1;
    }
    return r;
  }
  DynamicModInt inv() const {
    assert(x);
    return pow(m - 2);
  }

  friend DynamicModInt operator+(const DynamicModInt &a,
                                 const DynamicModInt &b) {
    return DynamicModInt(a) += b;
  }
  friend DynamicModInt operator-(const DynamicModInt &a,
                                 const DynamicModInt &b) {
    return DynamicModInt(a) -= b;
  }
  friend DynamicModInt operator*(const DynamicModInt &a,
                                 const DynamicModInt &b) {
    return DynamicModInt(a) *= b;
  }
  friend DynamicModInt operator/(const DynamicModInt &a,
                                 const DynamicModInt &b) {
    return DynamicModInt(a) /= b;
  }
  friend bool operator==(const DynamicModInt &a, const DynamicModInt &b) {
    return a.x == b.x;
  }
  friend bool operator!=(const DynamicModInt &a, const DynamicModInt &b) {
    return a.x != b.x;
  }

  friend istream &operator>>(istream &is, DynamicModInt &t) {
    ll y;
    is >> y;
    t.set(y);
    return is;
  }
  friend ostream &operator<<(ostream &os, const DynamicModInt &t) {
    os << t.x;
    return os;
  }
};
uint32_t DynamicModInt::m = 998244353;

DynamicModInt factorial(int n) {
  assert(0 <= n);
  static const int sz_ini = 100000;
  static int sz = 1;
  static vector<DynamicModInt> fac(1, 1);
  int sz_new = max(sz_ini, n + 1);
  if (sz_new > sz) {
    fac.resize(sz_new);
    for (int i = sz; i < sz_new; i++) {
      fac[i] = fac[i - 1] * i;
    }
    sz = sz_new;
  }
  return fac[n];
}

DynamicModInt factorial_inv(int n) {
  assert(0 <= n);
  static const int sz_ini = 100000;
  static int sz = 1;
  static vector<DynamicModInt> fac_inv(1, 1);
  int sz_new = max(sz_ini, n + 1);
  if (sz_new > sz) {
    fac_inv.resize(sz_new);
    for (int i = sz; i < sz_new; i++) {
      fac_inv[i] = fac_inv[i - 1] / i;
    }
    sz = sz_new;
  }
  return fac_inv[n];
}

// combination
DynamicModInt C(int n, int k) {
  assert(0 <= n);
  assert(0 <= k);
  assert(k <= n);
  return factorial(n) * factorial_inv(k) * factorial_inv(n - k);
}
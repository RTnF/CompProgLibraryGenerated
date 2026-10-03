#pragma once
#include "template/small_template.hpp"

/**
 * @brief 剰余を取り[0, mod)に収めるint
 * based on ACL
 * @tparam mod 素数に限る
 */
template <uint32_t m, enable_if_t<(2 <= m)> * = nullptr> class ModInt {
  uint32_t x;

public:
  constexpr ModInt() : x(0) {}
  template <class T, enable_if_t<is_signed_v<T>> * = nullptr>
  constexpr ModInt(T x_) : x(x_ < 0 ? x_ % (ll)m + (ll)m : x_ % (ll)m) {}
  template <class U, enable_if_t<!is_signed_v<U>> * = nullptr>
  constexpr ModInt(U x_) : x(x_ % m) {}

  uint32_t get() const { return x; }
  static constexpr uint32_t mod() { return m; }
  template <class T, enable_if_t<is_signed_v<T>> * = nullptr>
  constexpr void set(T x_) {
    x = x_ < 0 ? x_ % (ll)m + (ll)m : x_ % (ll)m;
  }
  template <class U, enable_if_t<!is_signed_v<U>> * = nullptr>
  constexpr void set(U x_) {
    x = x_ % m;
  }

  constexpr ModInt operator++(int) {
    ModInt y = *this;
    ++*this;
    return y;
  }
  constexpr ModInt &operator++() {
    x = x == m - 1 ? 0u : x + 1;
    return *this;
  }
  constexpr ModInt operator--(int) {
    ModInt y = *this;
    --*this;
    return y;
  }
  constexpr ModInt &operator--() {
    x = x == 0u ? m - 1 : x - 1;
    return *this;
  }
  constexpr ModInt &operator+=(const ModInt &y) {
    x += y.x;
    if (x >= m) {
      x -= m;
    }
    return *this;
  }
  constexpr ModInt &operator-=(const ModInt &y) {
    x -= y.x;
    if (x >= m) {
      x += m;
    }
    return *this;
  }
  constexpr ModInt &operator*=(const ModInt &y) {
    x = (ull)x * (ull)y.x % m;
    return *this;
  }
  constexpr ModInt &operator/=(const ModInt &y) { return *this *= y.inv(); }
  constexpr ModInt operator+() const { return *this; }
  constexpr ModInt operator-() const { return ModInt(m - x); }

  constexpr ModInt pow(ll n) const {
    if (n < 0) {
      return pow(-n).inv();
    }
    ModInt y = *this, r = 1;
    while (n) {
      if (n & 1) {
        r *= y;
      }
      y *= y;
      n >>= 1;
    }
    return r;
  }
  constexpr ModInt inv() const {
    assert(x);
    return pow(m - 2);
  }

  constexpr friend ModInt operator+(const ModInt &a, const ModInt &b) {
    return ModInt(a) += b;
  }
  constexpr friend ModInt operator-(const ModInt &a, const ModInt &b) {
    return ModInt(a) -= b;
  }
  constexpr friend ModInt operator*(const ModInt &a, const ModInt &b) {
    return ModInt(a) *= b;
  }
  constexpr friend ModInt operator/(const ModInt &a, const ModInt &b) {
    return ModInt(a) /= b;
  }
  constexpr friend bool operator==(const ModInt &a, const ModInt &b) {
    return a.x == b.x;
  }
  constexpr friend bool operator!=(const ModInt &a, const ModInt &b) {
    return a.x != b.x;
  }

  friend istream &operator>>(istream &is, ModInt &t) {
    ll y;
    is >> y;
    t.set(y);
    return is;
  }
  friend ostream &operator<<(ostream &os, const ModInt &t) {
    os << t.x;
    return os;
  }
};

using mint = ModInt<998244353u>;
using mint17 = ModInt<1000000007u>;

const int MAX_FAC = 20000003;
mint fac[MAX_FAC];

// combination
constexpr mint C(int n, int k) { return fac[n] / (fac[k] * fac[n - k]); }

constexpr void init() {
  fac[0] = 1;
  for (int i = 1; i < MAX_FAC; i++) {
    fac[i] = fac[i - 1] * i;
  }
}

#pragma once
#include "template/small_template.hpp"

static uint32_t dynamic_modint_pow_word(uint32_t base, ull exponent, uint32_t modulus) {
  ull result = (ull)1 % modulus;
  ull b = (ull)base % modulus;
  ull e = exponent;
  while (e != 0) {
    if ((e & 1) != 0) result = result * b % modulus;
    b = b * b % modulus;
    e = e >> 1;
  }
  return (uint32_t)result;
}

/**
 * @brief 剰余を取り[0, mod)に収めるint
 * based on ACL
 * m は 2 以上。逆元・除算・負冪では素数に限る。
 */
struct DynamicModInt {
  static uint32_t m;
  uint32_t x;

private:
  static uint32_t pow_nonnegative(uint32_t base, ull exponent) {
    return dynamic_modint_pow_word(base, exponent, m);
  }

public:
  DynamicModInt() : x(0) {}
  template <class T, enable_if_t<(is_signed_v<T> || std::is_same_v<std::remove_cv_t<T>, __int128>)> * = nullptr>
  DynamicModInt(T x_) : x((x_ % (ll)m + (ll)m) % (ll)m) {}
  template <class U, enable_if_t<!(is_signed_v<U> || std::is_same_v<std::remove_cv_t<U>, __int128>)> * = nullptr>
  DynamicModInt(U x_) : x(x_ % m) {}

  uint32_t get() const { return x; }
  template <class T, enable_if_t<(is_signed_v<T> || std::is_same_v<std::remove_cv_t<T>, __int128>)> * = nullptr> void set(T x_) {
    x = (x_ % (ll)m + (ll)m) % (ll)m;
  }
  template <class U, enable_if_t<!(is_signed_v<U> || std::is_same_v<std::remove_cv_t<U>, __int128>)> * = nullptr> void set(U x_) {
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
    ull z = (ull)x + y.x;
    x = z >= m ? z - m : z;
    return *this;
  }
  DynamicModInt &operator-=(const DynamicModInt &y) {
    ull z = (ull)x + m - y.x;
    x = z >= m ? z - m : z;
    return *this;
  }
  DynamicModInt &operator*=(const DynamicModInt &y) {
    x = (ull)x * (ull)y.x % m;
    return *this;
  }
  DynamicModInt &operator/=(const DynamicModInt &y) {
    const DynamicModInt inverse = y.inv();
    return *this *= inverse;
  }
  DynamicModInt operator+() const { return *this; }
  DynamicModInt operator-() const {
    const uint32_t negated = m - x;
    return DynamicModInt(negated);
  }

  DynamicModInt pow(ll n) const {
    if (n < 0) {
      ull magnitude = (ull)(-(n + 1)) + 1;
      const uint32_t powered = pow_nonnegative(x, magnitude);
      const DynamicModInt value(powered);
      return value.inv();
    }
    const uint32_t powered = pow_nonnegative(x, (ull)n);
    return DynamicModInt(powered);
  }
  DynamicModInt inv() const {
    assert(x);
    const ull exponent = m - 2;
    const uint32_t powered = pow_nonnegative(x, exponent);
    return DynamicModInt(powered);
  }

  friend DynamicModInt operator+(const DynamicModInt &a,
                                 const DynamicModInt &b) {
    DynamicModInt result(a);
    result += b;
    return result;
  }
  friend DynamicModInt operator-(const DynamicModInt &a,
                                 const DynamicModInt &b) {
    DynamicModInt result(a);
    result -= b;
    return result;
  }
  friend DynamicModInt operator*(const DynamicModInt &a,
                                 const DynamicModInt &b) {
    DynamicModInt result(a);
    result *= b;
    return result;
  }
  friend DynamicModInt operator/(const DynamicModInt &a,
                                 const DynamicModInt &b) {
    DynamicModInt result(a);
    result /= b;
    return result;
  }
  friend bool operator==(const DynamicModInt &a, const DynamicModInt &b) {
    return a.x == b.x;
  }
  friend bool operator!=(const DynamicModInt &a, const DynamicModInt &b) {
    return a.x != b.x;
  }

  friend istream &operator>>(istream &is, DynamicModInt &t) {
    ll y = 0;
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
  const uint32_t modulus = DynamicModInt::m;
  assert(2 <= modulus);
  static uint32_t cached_modulus = 0;
  static vector<DynamicModInt> fac;
  if (cached_modulus != modulus) {
    fac.resize(1, DynamicModInt());
    DynamicModInt one;
    one.x = 1u;
    fac[0] = one;
    cached_modulus = modulus;
  }
  const ll required = (ll)n + 1;
  const ll old_size = (ll)fac.size();
  if (required > old_size) {
    const ll new_size = required > 100000 ? required : 100000;
    fac.resize(new_size, DynamicModInt());
    for (ll i = old_size; i < new_size; i++) {
      const DynamicModInt previous = fac[i - 1];
      const uint32_t factor = (uint32_t)((ull)i % modulus);
      DynamicModInt value;
      value.x = (ull)previous.x * factor % modulus;
      fac[i] = value;
    }
  }
  return fac[n];
}

DynamicModInt factorial_inv(int n) {
  assert(0 <= n);
  const uint32_t modulus = DynamicModInt::m;
  assert(2 <= modulus);
  assert((ll)n < (ll)modulus);
  static uint32_t cached_modulus = 0;
  static vector<DynamicModInt> fac_inv;
  if (cached_modulus != modulus) {
    fac_inv.resize(1, DynamicModInt());
    DynamicModInt one;
    one.x = 1u;
    fac_inv[0] = one;
    cached_modulus = modulus;
  }
  const ll required = (ll)n + 1;
  const ll old_size = (ll)fac_inv.size();
  if (required > old_size) {
    const ll preferred = required > 100000 ? required : 100000;
    const ll new_size = preferred < (ll)modulus ? preferred : (ll)modulus;
    fac_inv.resize(new_size, DynamicModInt());
    for (ll i = old_size; i < new_size; i++) {
      const DynamicModInt previous = fac_inv[i - 1];
      const uint32_t factor = (uint32_t)i;
      const uint32_t inverse = dynamic_modint_pow_word(factor, modulus - 2, modulus);
      DynamicModInt value;
      value.x = (ull)previous.x * inverse % modulus;
      fac_inv[i] = value;
    }
  }
  return fac_inv[n];
}

DynamicModInt C(int n, int k) {
  assert(0 <= n);
  assert(0 <= k);
  assert(k <= n);
  DynamicModInt numerator = factorial(n);
  DynamicModInt left = factorial_inv(k);
  DynamicModInt right = factorial_inv(n - k);
  const DynamicModInt partial_product = numerator * left;
  return partial_product * right;
}

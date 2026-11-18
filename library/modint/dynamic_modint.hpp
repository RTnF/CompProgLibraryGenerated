#pragma once
#include <cassert>
#include <cstdint>
#include <istream>
#include <ostream>
#include <type_traits>
#include <vector>

namespace cp {

inline std::uint32_t dynamic_modint_pow_word(std::uint32_t base, std::uint64_t exponent, std::uint32_t modulus) {
  std::uint64_t result = (std::uint64_t)1 % modulus;
  std::uint64_t b = (std::uint64_t)base % modulus;
  std::uint64_t e = exponent;
  while (e != 0) {
    if ((e & 1) != 0) result = result * b % modulus;
    b = b * b % modulus;
    e = e >> 1;
  }
  return (std::uint32_t)result;
}

/**
 * @brief 剰余を取り[0, mod)に収めるint
 * based on ACL
 * m は 2 以上。逆元・除算・負冪では素数に限る。
 */
struct DynamicModInt {
  static std::uint32_t m;
  std::uint32_t x;

private:
  static std::uint32_t pow_nonnegative(std::uint32_t base, std::uint64_t exponent) {
    return dynamic_modint_pow_word(base, exponent, m);
  }

public:
  DynamicModInt() : x(0) {}
  template <class T, std::enable_if_t<(std::is_signed_v<T> || std::is_same_v<std::remove_cv_t<T>, __int128>)> * = nullptr>
  DynamicModInt(T x_) : x((x_ % (std::int64_t)m + (std::int64_t)m) % (std::int64_t)m) {}
  template <class U, std::enable_if_t<!(std::is_signed_v<U> || std::is_same_v<std::remove_cv_t<U>, __int128>)> * = nullptr>
  DynamicModInt(U x_) : x(x_ % m) {}

  std::uint32_t get() const { return x; }
  template <class T, std::enable_if_t<(std::is_signed_v<T> || std::is_same_v<std::remove_cv_t<T>, __int128>)> * = nullptr> void set(T x_) {
    x = (x_ % (std::int64_t)m + (std::int64_t)m) % (std::int64_t)m;
  }
  template <class U, std::enable_if_t<!(std::is_signed_v<U> || std::is_same_v<std::remove_cv_t<U>, __int128>)> * = nullptr> void set(U x_) {
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
    std::uint64_t z = (std::uint64_t)x + y.x;
    x = z >= m ? z - m : z;
    return *this;
  }
  DynamicModInt &operator-=(const DynamicModInt &y) {
    std::uint64_t z = (std::uint64_t)x + m - y.x;
    x = z >= m ? z - m : z;
    return *this;
  }
  DynamicModInt &operator*=(const DynamicModInt &y) {
    x = (std::uint64_t)x * (std::uint64_t)y.x % m;
    return *this;
  }
  DynamicModInt &operator/=(const DynamicModInt &y) {
    const DynamicModInt inverse = y.inv();
    return *this *= inverse;
  }
  DynamicModInt operator+() const { return *this; }
  DynamicModInt operator-() const {
    const std::uint32_t negated = m - x;
    return DynamicModInt(negated);
  }

  DynamicModInt pow(std::int64_t n) const {
    if (n < 0) {
      std::uint64_t magnitude = (std::uint64_t)(-(n + 1)) + 1;
      const std::uint32_t powered = pow_nonnegative(x, magnitude);
      const DynamicModInt value(powered);
      return value.inv();
    }
    const std::uint32_t powered = pow_nonnegative(x, (std::uint64_t)n);
    return DynamicModInt(powered);
  }
  DynamicModInt inv() const {
    assert(x);
    const std::uint64_t exponent = m - 2;
    const std::uint32_t powered = pow_nonnegative(x, exponent);
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

  friend std::istream &operator>>(std::istream &is, DynamicModInt &t) {
    std::int64_t y = 0;
    is >> y;
    t.set(y);
    return is;
  }
  friend std::ostream &operator<<(std::ostream &os, const DynamicModInt &t) {
    os << t.x;
    return os;
  }
};
inline std::uint32_t DynamicModInt::m = 998244353;

inline DynamicModInt factorial(int n) {
  assert(0 <= n);
  const std::uint32_t modulus = DynamicModInt::m;
  assert(2 <= modulus);
  static std::uint32_t cached_modulus = 0;
  static std::vector<DynamicModInt> fac;
  if (cached_modulus != modulus) {
    fac.resize(1, DynamicModInt());
    DynamicModInt one;
    one.x = 1u;
    fac[0] = one;
    cached_modulus = modulus;
  }
  const std::int64_t required = (std::int64_t)n + 1;
  const std::int64_t old_size = (std::int64_t)fac.size();
  if (required > old_size) {
    const std::int64_t new_size = required > 100000 ? required : 100000;
    fac.resize(new_size, DynamicModInt());
    for (std::int64_t i = old_size; i < new_size; i++) {
      const DynamicModInt previous = fac[i - 1];
      const std::uint32_t factor = (std::uint32_t)((std::uint64_t)i % modulus);
      DynamicModInt value;
      value.x = (std::uint64_t)previous.x * factor % modulus;
      fac[i] = value;
    }
  }
  return fac[n];
}

inline DynamicModInt factorial_inv(int n) {
  assert(0 <= n);
  const std::uint32_t modulus = DynamicModInt::m;
  assert(2 <= modulus);
  assert((std::int64_t)n < (std::int64_t)modulus);
  static std::uint32_t cached_modulus = 0;
  static std::vector<DynamicModInt> fac_inv;
  if (cached_modulus != modulus) {
    fac_inv.resize(1, DynamicModInt());
    DynamicModInt one;
    one.x = 1u;
    fac_inv[0] = one;
    cached_modulus = modulus;
  }
  const std::int64_t required = (std::int64_t)n + 1;
  const std::int64_t old_size = (std::int64_t)fac_inv.size();
  if (required > old_size) {
    const std::int64_t preferred = required > 100000 ? required : 100000;
    const std::int64_t new_size = preferred < (std::int64_t)modulus ? preferred : (std::int64_t)modulus;
    fac_inv.resize(new_size, DynamicModInt());
    for (std::int64_t i = old_size; i < new_size; i++) {
      const DynamicModInt previous = fac_inv[i - 1];
      const std::uint32_t factor = (std::uint32_t)i;
      const std::uint32_t inverse = dynamic_modint_pow_word(factor, modulus - 2, modulus);
      DynamicModInt value;
      value.x = (std::uint64_t)previous.x * inverse % modulus;
      fac_inv[i] = value;
    }
  }
  return fac_inv[n];
}

namespace dynamic_modint {

inline DynamicModInt C(int n, int k) {
  assert(0 <= n);
  assert(0 <= k);
  assert(k <= n);
  DynamicModInt numerator = factorial(n);
  DynamicModInt left = factorial_inv(k);
  DynamicModInt right = factorial_inv(n - k);
  const DynamicModInt partial_product = numerator * left;
  return partial_product * right;
}

} // namespace dynamic_modint

} // namespace cp

#pragma once
#include <cassert>
#include <cstdint>
#include <istream>
#include <ostream>
#include <type_traits>

namespace cp {

/**
 * @brief 剰余を取り[0, mod)に収めるint
 * based on ACL
 * @tparam mod 素数に限る
 */
template <std::uint32_t m, std::enable_if_t<(2 <= m)> * = nullptr> class ModInt {
  std::uint32_t x;

  static constexpr std::uint32_t pow_nonnegative(std::uint32_t base, std::uint64_t exponent) {
    std::uint64_t result = (std::uint64_t)1 % m;
    std::uint64_t b = (std::uint64_t)base % m;
    std::uint64_t e = exponent;
    while (e != 0) {
      if ((e & 1) != 0) result = result * b % m;
      b = b * b % m;
      e = e >> 1;
    }
    return (std::uint32_t)result;
  }

public:
  constexpr ModInt() : x(0) {}
  template <class T, std::enable_if_t<(std::is_signed_v<T> || std::is_same_v<std::remove_cv_t<T>, __int128>)> * = nullptr>
  constexpr ModInt(T x_) : x((x_ % (std::int64_t)m + (std::int64_t)m) % (std::int64_t)m) {}
  template <class U, std::enable_if_t<!(std::is_signed_v<U> || std::is_same_v<std::remove_cv_t<U>, __int128>)> * = nullptr>
  constexpr ModInt(U x_) : x(x_ % m) {}

  std::uint32_t get() const { return x; }
  static constexpr std::uint32_t mod() { return m; }
  template <class T, std::enable_if_t<(std::is_signed_v<T> || std::is_same_v<std::remove_cv_t<T>, __int128>)> * = nullptr>
  constexpr void set(T x_) {
    x = (x_ % (std::int64_t)m + (std::int64_t)m) % (std::int64_t)m;
  }
  template <class U, std::enable_if_t<!(std::is_signed_v<U> || std::is_same_v<std::remove_cv_t<U>, __int128>)> * = nullptr>
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
    std::uint64_t z = (std::uint64_t)x + y.x;
    x = z >= m ? z - m : z;
    return *this;
  }
  constexpr ModInt &operator-=(const ModInt &y) {
    std::uint64_t z = (std::uint64_t)x + m - y.x;
    x = z >= m ? z - m : z;
    return *this;
  }
  constexpr ModInt &operator*=(const ModInt &y) {
    x = (std::uint64_t)x * (std::uint64_t)y.x % m;
    return *this;
  }
  constexpr ModInt &operator/=(const ModInt &y) { return *this *= y.inv(); }
  constexpr ModInt operator+() const { return *this; }
  constexpr ModInt operator-() const { return ModInt(m - x); }

  constexpr ModInt pow(std::int64_t n) const {
    if (n < 0) {
      std::uint64_t magnitude = (std::uint64_t)(-(n + 1)) + 1;
      return ModInt(pow_nonnegative(x, magnitude)).inv();
    }
    return ModInt(pow_nonnegative(x, (std::uint64_t)n));
  }
  constexpr ModInt inv() const {
    assert(x);
    return ModInt(pow_nonnegative(x, m - 2));
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

  friend std::istream &operator>>(std::istream &is, ModInt &t) {
    std::int64_t y = 0;
    is >> y;
    t.set(y);
    return is;
  }
  friend std::ostream &operator<<(std::ostream &os, const ModInt &t) {
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

} // namespace cp

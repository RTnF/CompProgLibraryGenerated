#pragma once
#include <cassert>
#include <compare>
#include <cstdint>
#include <istream>
#include <ostream>

namespace cp {

template <typename T = std::int64_t> class Ratio {
static T numeric_gcd_nonnegative(T a, T b) {
  while (b != 0) {
    T r = a % b;
    a = b;
    b = r;
  }
  return a;
}

static T numeric_gcd(T a, T b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  return numeric_gcd_nonnegative(a, b);
}

static T numeric_lcm(T a, T b) {
  if (a == 0 || b == 0) return 0;
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  return a / numeric_gcd_nonnegative(a, b) * b;
}

  // n / d
  T n, d;

  void normalize() {
    if (n == 0) {
      d = 1;
      return;
    }
    if (d < 0) {
      n = -n;
      d = -d;
    }
    T g = numeric_gcd(n, d);
    n /= g;
    d /= g;
  }

public:
  Ratio(T nominator, T denominator) : n(nominator), d(denominator) {
    normalize();
  }
  Ratio(T nominator) : n(nominator), d(1) {}

  std::strong_ordering operator<=>(const Ratio &r) const {
    T g = numeric_gcd(d, r.d);
    return r.d / g * n <=> d / g * r.n;
  }
  bool operator==(const Ratio &r) const = default;

  Ratio operator++(int) {
    Ratio r = *this;
    ++*this;
    return r;
  }
  Ratio &operator++() {
    n += d;
    return *this;
  }
  Ratio operator--(int) {
    Ratio r = *this;
    --*this;
    return r;
  }
  Ratio &operator--() {
    n -= d;
    return *this;
  }
  Ratio &operator+=(const Ratio &r) {
    T l = numeric_lcm(d, r.d);
    n = l / d * n + l / r.d * r.n;
    d = l;
    normalize();
    return *this;
  }
  Ratio &operator-=(const Ratio &r) {
    T l = numeric_lcm(d, r.d);
    n = l / d * n - l / r.d * r.n;
    d = l;
    normalize();
    return *this;
  }
  Ratio &operator*=(const Ratio &r) {
    T g1 = numeric_gcd(n, r.d);
    T g2 = numeric_gcd(r.n, d);
    n = n / g1 * (r.n / g2);
    d = d / g2 * (r.d / g1);
    return *this;
  }
  Ratio &operator/=(const Ratio &r) {
    assert(r.n != 0);
    T g1 = numeric_gcd(n, r.n);
    T g2 = numeric_gcd(d, r.d);
    T new_n = n / g1 * (r.d / g2);
    T new_d = d / g2 * (r.n / g1);
    n = new_n;
    d = new_d;
    normalize();
    return *this;
  }
  Ratio operator+() const { return *this; }
  Ratio operator-() const { return Ratio(-n, d); }

  friend Ratio operator+(const Ratio &a, const Ratio &b) {
    return Ratio(a) += b;
  }
  friend Ratio operator-(const Ratio &a, const Ratio &b) {
    return Ratio(a) -= b;
  }
  friend Ratio operator*(const Ratio &a, const Ratio &b) {
    return Ratio(a) *= b;
  }
  friend Ratio operator/(const Ratio &a, const Ratio &b) {
    return Ratio(a) /= b;
  }
  friend Ratio operator+(const Ratio &a, const T &b) { return Ratio(a) += b; }
  friend Ratio operator-(const Ratio &a, const T &b) { return Ratio(a) -= b; }
  friend Ratio operator*(const Ratio &a, const T &b) { return Ratio(a) *= b; }
  friend Ratio operator/(const Ratio &a, const T &b) { return Ratio(a) /= b; }
  friend Ratio operator+(const T &a, const Ratio &b) { return Ratio(a) += b; }
  friend Ratio operator-(const T &a, const Ratio &b) { return Ratio(a) -= b; }
  friend Ratio operator*(const T &a, const Ratio &b) { return Ratio(a) *= b; }
  friend Ratio operator/(const T &a, const Ratio &b) { return Ratio(a) /= b; }

  friend std::istream &operator>>(std::istream &is, Ratio &r) {
    is >> r.n >> r.d;
    return is;
  }
  friend std::ostream &operator<<(std::ostream &os, const Ratio &r) {
    os << r.n;
    if (r.d > 1) {
      os << '/' << r.d;
    }
    return os;
  }
};
} // namespace cp

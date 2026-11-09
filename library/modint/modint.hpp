#pragma once
#include <cassert>
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// Integers modulo m (2 <= m < 2^32), always stored reduced in [0, m). The inverse and division need m prime.
// Derived from experiments/library/cpp/modint/modint.hpp. Differences: the signed constructor reduces a negative
// multiple of m to 0 (the original returned m), the constructor takes long long, pow takes an unsigned exponent
// (negative exponents are pow(unsigned) followed by inv()), and the binary operators are member functions.
// The class has one scalar field, so the generator treats a ModInt as its field `x` (see verifier/class_lowering.py).
template <unsigned int m> class ModInt {
  unsigned int x;

public:
  ModInt() : x(0) {}
  ModInt(long long v) : x((v % (long long)m + (long long)m) % (long long)m) {}
  unsigned int get() const { return x; }

  ModInt &operator++() {
    if (x == m - 1) {
      x = 0;
    } else {
      x = x + 1;
    }
    return *this;
  }
  ModInt &operator--() {
    if (x == 0) {
      x = m - 1;
    } else {
      x = x - 1;
    }
    return *this;
  }
  ModInt &operator+=(const ModInt &y) {
    x = x + y.x;
    if (x >= m) {
      x = x - m;
    }
    return *this;
  }
  ModInt &operator-=(const ModInt &y) {
    x = x - y.x;
    if (x >= m) {
      x = x + m;
    }
    return *this;
  }
  ModInt &operator*=(const ModInt &y) {
    x = (unsigned long long)x * (unsigned long long)y.x % m;
    return *this;
  }
  // Division for a prime m: *this * y.inv(). Requires y != 0 (checked by the assert of inv).
  ModInt &operator/=(const ModInt &y) {
    ModInt z = y.inv();
    *this *= z;
    return *this;
  }
  ModInt operator-() const {
    ModInt r;
    if (x != 0) {
      r.x = m - x;
    }
    return r;
  }
  ModInt pow(unsigned long long n) const {
    ModInt y = *this;
    ModInt r = 1;
    while (n) {
      if (n & 1) {
        r *= y;
      }
      y *= y;
      n >>= 1;
    }
    return r;
  }
  // The inverse for a prime m: x^(m - 2). Requires x != 0 (checked by assert).
  ModInt inv() const {
    assert(x != 0);
    return pow(m - 2);
  }
  bool operator==(const ModInt &y) const { return x == y.x; }
  bool operator!=(const ModInt &y) const { return x != y.x; }
};

template <unsigned int m> inline ModInt<m> operator+(ModInt<m> a, ModInt<m> b) {
  ModInt<m> r = a;
  r += b;
  return r;
}
template <unsigned int m> inline ModInt<m> operator-(ModInt<m> a, ModInt<m> b) {
  ModInt<m> r = a;
  r -= b;
  return r;
}
template <unsigned int m> inline ModInt<m> operator*(ModInt<m> a, ModInt<m> b) {
  ModInt<m> r = a;
  r *= b;
  return r;
}
template <unsigned int m> inline ModInt<m> operator/(ModInt<m> a, const ModInt<m> &b) {
  a /= b;
  return a;
}

template class ModInt<998244353u>;
template class ModInt<1000000007u>;
template ModInt<998244353u> operator+<998244353u>(ModInt<998244353u>, ModInt<998244353u>);
template ModInt<998244353u> operator-<998244353u>(ModInt<998244353u>, ModInt<998244353u>);
template ModInt<998244353u> operator*<998244353u>(ModInt<998244353u>, ModInt<998244353u>);
template ModInt<1000000007u> operator+<1000000007u>(ModInt<1000000007u>, ModInt<1000000007u>);
template ModInt<1000000007u> operator-<1000000007u>(ModInt<1000000007u>, ModInt<1000000007u>);
template ModInt<1000000007u> operator*<1000000007u>(ModInt<1000000007u>, ModInt<1000000007u>);
template ModInt<998244353u> operator/<998244353u>(ModInt<998244353u>, const ModInt<998244353u> &);
template ModInt<1000000007u> operator/<1000000007u>(ModInt<1000000007u>, const ModInt<1000000007u> &);

} // namespace cp

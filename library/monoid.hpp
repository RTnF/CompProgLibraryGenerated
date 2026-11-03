#pragma once
#include <limits>
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// Monoids for segment trees and similar structures. Each wraps one value `x`; the default constructor and the static
// member e() build the identity and `op(a, b)` is the associative operation. Derived from
// experiments/library/cpp/algebraic_structure/monoid.hpp: the class templates keep their type parameter T (the verified
// instances are the ones with T = long long, instantiated explicitly at the end of the file).
// Differences: `op` is a function template of the monoid instead of a friend function (a friend function defined in a
// class template is instantiated only when it is used, so it could not be checked for the instance); it is found by
// argument-dependent lookup exactly as the friend was. `std::max`/`std::min` are written as `if` statements, and the
// default constructors are written as the identity directly instead of delegating to e().
// MonoidMul wraps modulo 2^64 only if T is unsigned; for long long the product must not overflow (a signed overflow is
// outside the verified contract).
template <class T = long long> struct MonoidMul {
  T x;
  MonoidMul(T x_) : x(x_) {}
  MonoidMul() : x(1) {}
  static MonoidMul e() { return 1; }
};
template <class T> MonoidMul<T> op(const MonoidMul<T> &a, const MonoidMul<T> &b) { return MonoidMul<T>(a.x * b.x); }

template <class T = long long> struct MonoidMax {
  T x;
  MonoidMax(T x_) : x(x_) {}
  MonoidMax() : x(std::numeric_limits<T>::min()) {}
  static MonoidMax e() { return std::numeric_limits<T>::min(); }
};
template <class T> MonoidMax<T> op(const MonoidMax<T> &a, const MonoidMax<T> &b) {
  MonoidMax<T> r = a;
  if (a.x < b.x) {
    r.x = b.x;
  }
  return r;
}

template <class T = long long> struct MonoidMin {
  T x;
  MonoidMin(T x_) : x(x_) {}
  MonoidMin() : x(std::numeric_limits<T>::max()) {}
  static MonoidMin e() { return std::numeric_limits<T>::max(); }
};
template <class T> MonoidMin<T> op(const MonoidMin<T> &a, const MonoidMin<T> &b) {
  MonoidMin<T> r = a;
  if (b.x < a.x) {
    r.x = b.x;
  }
  return r;
}

template struct MonoidMul<long long>;
template struct MonoidMax<long long>;
template struct MonoidMin<long long>;
template MonoidMul<long long> op(const MonoidMul<long long> &, const MonoidMul<long long> &);
template MonoidMax<long long> op(const MonoidMax<long long> &, const MonoidMax<long long> &);
template MonoidMin<long long> op(const MonoidMin<long long> &, const MonoidMin<long long> &);

} // namespace cp

#pragma once
#include "template/small_template.hpp"

template <class T = ll> struct MonoidMul {
  T x;
  MonoidMul(T x_) : x(x_) {}
  MonoidMul() : MonoidMul(e()) {}
  static MonoidMul e() { return 1; }
  friend MonoidMul op(const MonoidMul &a, const MonoidMul &b) {
    return a.x * b.x;
  }
};

template <class T = ll> struct MonoidMax {
  T x;
  MonoidMax(T x_) : x(x_) {}
  MonoidMax() : MonoidMax(e()) {}
  static MonoidMax e() { if constexpr (std::is_floating_point_v<T>) { return numeric_limits<T>::has_infinity ? -numeric_limits<T>::infinity() : numeric_limits<T>::lowest(); } else { return numeric_limits<T>::min(); } }
  friend MonoidMax op(const MonoidMax &a, const MonoidMax &b) {
    return max(a.x, b.x);
  }
};

template <class T = ll> struct MonoidMin {
  T x;
  MonoidMin(T x_) : x(x_) {}
  MonoidMin() : MonoidMin(e()) {}
  static MonoidMin e() { if constexpr (std::is_floating_point_v<T>) { return numeric_limits<T>::has_infinity ? numeric_limits<T>::infinity() : numeric_limits<T>::max(); } else { return numeric_limits<T>::max(); } }
  friend MonoidMin op(const MonoidMin &a, const MonoidMin &b) {
    return min(a.x, b.x);
  }
};

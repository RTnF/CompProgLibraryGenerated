#pragma once
#include "template/small_template.hpp"

/**
 * @brief 区間 [start, end)
 *
 * @tparam T
 */
template <class T = ll> class Interval {
  T s, e;
  // 空の区間
  bool is_n;

public:
  constexpr Interval(T start_, T end_)
      : s(start_), e(end_), is_n(start_ == end_) {
    assert(start_ <= end_);
  }
  constexpr Interval() : s(0), e(0), is_n(true) {}
  constexpr auto operator<=>(const Interval &r) const = default;

  constexpr T start() { return s; }
  constexpr T end() { return e; }
  constexpr bool is_null() { return is_n; }
  constexpr T length() { return e - s; }

  Interval<T> intersection(const Interval<T> &b) const {
    if (b.s >= e || s >= b.e) {
      return Interval<T>();
    }
    return Interval(max(s, b.s), min(e, b.e));
  }

  friend istream &operator>>(istream &is, Interval &m) {
    is >> m.s >> m.e;
    return is;
  }
  friend ostream &operator<<(ostream &os, const Interval &m) {
    os << '[' << m.s << ", " << m.e << ')';
    return os;
  }
};
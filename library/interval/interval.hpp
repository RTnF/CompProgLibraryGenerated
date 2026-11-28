#pragma once
#include <algorithm>
#include <cassert>
#include <compare>
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// The half-open interval [start, end) of values of type T, with an `empty` flag (start == end).
// Derived from experiments/library/cpp/interval/interval.hpp: the class template keeps its type parameter T (the
// verified instance is Interval<long long>, instantiated explicitly below).
// The accessors are const.
// Preconditions: Interval(start, end) requires start <= end (checked by assert). Time O(1), extra space O(1).
template <class T = long long> struct Interval {
  T s, e;
  bool is_n;
  Interval(T start_, T end_) : s(start_), e(end_), is_n(start_ == end_) { assert(start_ <= end_); }
  Interval() : s(0), e(0), is_n(true) {}
  T start() const { return s; }
  T end() const { return e; }
  bool is_null() const { return is_n; }
  T length() const { return e - s; }
  auto operator<=>(const Interval &r) const = default;
  bool operator==(const Interval &r) const = default;
  // The common part of two intervals; the empty interval [0, 0) if they do not overlap.
  Interval intersection(const Interval &b) const {
    if (b.s >= e || s >= b.e) {
      return Interval();
    }
    return Interval(std::max(s, b.s), std::min(e, b.e));
  }
};

template struct Interval<long long>;

} // namespace cp

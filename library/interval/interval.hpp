#pragma once
#include <cassert>
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// The half-open interval [start, end) of values of type T, with an `empty` flag (start == end).
// Derived from experiments/library/cpp/interval/interval.hpp: the class template keeps its type parameter T (the
// verified instance is Interval<long long>, instantiated explicitly below).
// Differences: the accessors are const, the defaulted <=> and the stream operators are not included (the converter
// does not support them), and `intersection` is written with if statements instead of std::max / std::min.
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
  // The common part of two intervals; the empty interval [0, 0) if they do not overlap.
  Interval intersection(const Interval &b) const {
    if (b.s >= e || s >= b.e) {
      return Interval();
    }
    T ns = s;
    if (b.s > s) {
      ns = b.s;
    }
    T ne = e;
    if (b.e < e) {
      ne = b.e;
    }
    return Interval(ns, ne);
  }
};

template struct Interval<long long>;

} // namespace cp

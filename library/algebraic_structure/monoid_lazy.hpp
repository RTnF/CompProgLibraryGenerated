#pragma once
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// Actions and values for lazy segment trees. Derived from experiments/library/cpp/algebraic_structure/monoid_lazy.hpp.
// Differences: the classes are flat class templates over the value type T (the original nests them in
// RangeAddRangeSum<T> and friends, which the generator cannot express); `e()` and `id()` are the default constructors;
// `numeric_limits` is not needed. The verified instances are the ones with T = long long (explicit instantiations at the end). The value monoids RangeMax / RangeMin of the original are MonoidMax / MonoidMin of
// monoid.hpp (identical definitions), so only the sum of a segment (RangeSum) is repeated here. `apply` is one member
// function per value type: applyExtremum(m) for a maximum or minimum m (both original instantiations compute the same
// expression) and applySumX(x, size) for the new sum of a RangeSum (the length is unchanged).
// compose(f, g) is the action "g first, then f", exactly as in the original (RangeAdd adds the shifts; RangeSet keeps f
// unless f is the no-op): compose(f, g).apply(m) == f.apply(g.apply(m)). Sums and products must not overflow (a signed
// overflow is outside the verified contract).

// The sum of a segment together with its length.
template <class T = long long> struct RangeSum {
  T x;
  int size;
  RangeSum(T x_, int size_) : x(x_), size(size_) {}
  RangeSum() : x(0), size(0) {}
};
template <class T> RangeSum<T> op(const RangeSum<T> &a, const RangeSum<T> &b) {
  return RangeSum<T>(a.x + b.x, a.size + b.size);
}

template <class T = long long> struct RangeAdd {
  T v;
  RangeAdd(T v_) : v(v_) {}
  RangeAdd() : v(0) {}
  T applyExtremum(T m) const { return m + v; }
  T applySumX(T x, int size) const { return x + size * v; }
};
template <class T> RangeAdd<T> compose(const RangeAdd<T> &f, const RangeAdd<T> &g) { return RangeAdd<T>(f.v + g.v); }

template <class T = long long> struct RangeSet {
  T v;
  bool noop;
  RangeSet(T v_) : v(v_), noop(false) {}
  RangeSet(T v_, bool noop_) : v(v_), noop(noop_) {}
  RangeSet() : v(0), noop(true) {}
  T applyExtremum(T m) const {
    if (noop) {
      return m;
    }
    return v;
  }
  T applySumX(T x, int size) const {
    if (noop) {
      return x;
    }
    return v * size;
  }
};
template <class T> RangeSet<T> compose(const RangeSet<T> &f, const RangeSet<T> &g) {
  if (f.noop) {
    return RangeSet<T>(g.v, g.noop);
  }
  return RangeSet<T>(f.v, f.noop);
}

template struct RangeSum<long long>;
template struct RangeAdd<long long>;
template struct RangeSet<long long>;
template RangeSum<long long> op(const RangeSum<long long> &, const RangeSum<long long> &);
template RangeAdd<long long> compose(const RangeAdd<long long> &, const RangeAdd<long long> &);
template RangeSet<long long> compose(const RangeSet<long long> &, const RangeSet<long long> &);

} // namespace cp

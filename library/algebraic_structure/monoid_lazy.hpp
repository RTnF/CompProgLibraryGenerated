#pragma once
#include <algorithm>
#include <limits>
#include <type_traits>
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

// ---- The original nested API (RangeAddRangeMaxMin, RangeAddRangeSum, RangeSetRangeMaxMin, RangeSetRangeSum) ----
// Identical to experiments/library/cpp/algebraic_structure/monoid_lazy.hpp except for the standard-library
// qualification (`std::numeric_limits`, `std::max`, `std::min`) and `ll` spelled `long long`; tests/test_monoid_lazy_original_api.py
// compares the two token by token. The flat classes above remain as a convenience API.
// 遅延セグ木用の関数

template <class T = long long> struct RangeAddRangeMaxMin {
  struct RangeMax {
    T x;
    RangeMax(T x_) : x(x_) {}
    RangeMax() : RangeMax(e()) {}
    static RangeMax e() { if constexpr (std::is_floating_point_v<T>) { return std::numeric_limits<T>::has_infinity ? -std::numeric_limits<T>::infinity() : std::numeric_limits<T>::lowest(); } else { return std::numeric_limits<T>::min(); } }
    friend RangeMax op(const RangeMax &a, const RangeMax &b) {
      return std::max(a.x, b.x);
    }
  };
  struct RangeMin {
    T x;
    RangeMin(T x_) : x(x_) {}
    RangeMin() : RangeMin(e()) {}
    static RangeMin e() { if constexpr (std::is_floating_point_v<T>) { return std::numeric_limits<T>::has_infinity ? std::numeric_limits<T>::infinity() : std::numeric_limits<T>::max(); } else { return std::numeric_limits<T>::max(); } }
    friend RangeMin op(const RangeMin &a, const RangeMin &b) {
      return std::min(a.x, b.x);
    }
  };
  struct RangeAdd {
    T v;
    RangeAdd(T v_) : v(v_) {}
    static RangeAdd id() { return RangeAdd(0); }
    friend RangeAdd compose(RangeAdd f, RangeAdd g) {
      return RangeAdd(f.v + g.v);
    }
    template <class M> M apply(M x) { return x.x + v; }
  };
};

template <class T = long long> struct RangeAddRangeSum {
  struct RangeSum {
    T x;
    int size;
    RangeSum(T x_, int size_) : x(x_), size(size_) {}
    RangeSum() : RangeSum(e()) {}
    static RangeSum e() { return {0, 0}; }
    friend RangeSum op(const RangeSum &a, const RangeSum &b) {
      return {a.x + b.x, a.size + b.size};
    }
  };
  struct RangeAdd {
    T v;
    RangeAdd(T v_) : v(v_) {}
    static RangeAdd id() { return RangeAdd(0); }
    friend RangeAdd compose(RangeAdd f, RangeAdd g) {
      return RangeAdd(f.v + g.v);
    }
    RangeSum apply(RangeSum x) { return {x.x + x.size * v, x.size}; }
  };
};

template <class T = long long> struct RangeSetRangeMaxMin {
  struct RangeMax {
    T x;
    RangeMax(T x_) : x(x_) {}
    RangeMax() : RangeMax(e()) {}
    static RangeMax e() { if constexpr (std::is_floating_point_v<T>) { return std::numeric_limits<T>::has_infinity ? -std::numeric_limits<T>::infinity() : std::numeric_limits<T>::lowest(); } else { return std::numeric_limits<T>::min(); } }
    friend RangeMax op(const RangeMax &a, const RangeMax &b) {
      return std::max(a.x, b.x);
    }
  };
  struct RangeMin {
    T x;
    RangeMin(T x_) : x(x_) {}
    RangeMin() : RangeMin(e()) {}
    static RangeMin e() { if constexpr (std::is_floating_point_v<T>) { return std::numeric_limits<T>::has_infinity ? std::numeric_limits<T>::infinity() : std::numeric_limits<T>::max(); } else { return std::numeric_limits<T>::max(); } }
    friend RangeMin op(const RangeMin &a, const RangeMin &b) {
      return std::min(a.x, b.x);
    }
  };
  struct RangeSet {
    T v;
    bool noop;
    RangeSet(T v_) : v(v_), noop(false) {}
    RangeSet() : v(0), noop(true) {}
    static RangeSet id() { return {}; }
    friend RangeSet compose(RangeSet f, RangeSet g) { return f.noop ? g : f; }
    template <class M> M apply(M x) { return noop ? x : v; }
  };
};

template <class T = long long> struct RangeSetRangeSum {
  struct RangeSum {
    T x;
    int size;
    RangeSum(T x_, int size_) : x(x_), size(size_) {}
    RangeSum() : RangeSum(e()) {}
    static RangeSum e() { return {0, 0}; }
    friend RangeSum op(const RangeSum &a, const RangeSum &b) {
      return {a.x + b.x, a.size + b.size};
    }
  };
  struct RangeSet {
    T v;
    bool noop;
    RangeSet(T v_) : v(v_), noop(false) {}
    RangeSet() : v(0), noop(true) {}
    static RangeSet id() { return {}; }
    friend RangeSet compose(RangeSet f, RangeSet g) { return f.noop ? g : f; }
    RangeSum apply(RangeSum x) {
      if (!noop) {
        x.x = v * x.size;
      }
      return x;
    }
  };
};

template struct RangeSum<long long>;
template struct RangeAdd<long long>;
template struct RangeSet<long long>;
template RangeSum<long long> op(const RangeSum<long long> &, const RangeSum<long long> &);
template RangeAdd<long long> compose(const RangeAdd<long long> &, const RangeAdd<long long> &);
template RangeSet<long long> compose(const RangeSet<long long> &, const RangeSet<long long> &);

} // namespace cp

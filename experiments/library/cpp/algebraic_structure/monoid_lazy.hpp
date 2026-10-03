#pragma once
#include "template/small_template.hpp"

// 遅延セグ木用の関数

template <class T = ll> struct RangeAddRangeMaxMin {
  struct RangeMax {
    T x;
    RangeMax(T x_) : x(x_) {}
    RangeMax() : RangeMax(e()) {}
    static RangeMax e() { return numeric_limits<T>::min(); }
    friend RangeMax op(const RangeMax &a, const RangeMax &b) {
      return max(a.x, b.x);
    }
  };
  struct RangeMin {
    T x;
    RangeMin(T x_) : x(x_) {}
    RangeMin() : RangeMin(e()) {}
    static RangeMin e() { return numeric_limits<T>::max(); }
    friend RangeMin op(const RangeMin &a, const RangeMin &b) {
      return min(a.x, b.x);
    }
  };
  struct RangeAdd {
    T v;
    RangeAdd(T v_) : v(v_) {}
    static RangeAdd id() { return 0; }
    friend RangeAdd compose(RangeAdd f, RangeAdd g) {
      return RangeAdd(f.v + g.v);
    }
    template <class M> M apply(M x) { return x.x + v; }
  };
};

template <class T = ll> struct RangeAddRangeSum {
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
    static RangeAdd id() { return 0; }
    friend RangeAdd compose(RangeAdd f, RangeAdd g) {
      return RangeAdd(f.v + g.v);
    }
    RangeSum apply(RangeSum x) { return {x.x + x.size * v, x.size}; }
  };
};

template <class T = ll> struct RangeSetRangeMaxMin {
  struct RangeMax {
    T x;
    RangeMax(T x_) : x(x_) {}
    RangeMax() : RangeMax(e()) {}
    static RangeMax e() { return numeric_limits<T>::min(); }
    friend RangeMax op(const RangeMax &a, const RangeMax &b) {
      return max(a.x, b.x);
    }
  };
  struct RangeMin {
    T x;
    RangeMin(T x_) : x(x_) {}
    RangeMin() : RangeMin(e()) {}
    static RangeMin e() { return numeric_limits<T>::max(); }
    friend RangeMin op(const RangeMin &a, const RangeMin &b) {
      return min(a.x, b.x);
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

template <class T = ll> struct RangeSetRangeSum {
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

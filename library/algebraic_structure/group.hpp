#pragma once
#include <cassert>
#include <cstdint>

namespace cp {

template <class T> class GroupSum;
template <class T> GroupSum<T> op(const GroupSum<T> &a, const GroupSum<T> &b);
template <class T = std::int64_t> class GroupSum {
  T _x;

public:
  GroupSum(T x_) : _x(x_) {}
  GroupSum() : GroupSum(e()) {}
  T x() const { return _x; }
  static GroupSum e() { return 0; }
  friend GroupSum op<T>(const GroupSum &a, const GroupSum &b);
  friend GroupSum op(const GroupSum &a, const GroupSum &b) {
    return a._x + b._x;
  }
  GroupSum inv() const { return -_x; }
};

template <class T> class GroupMul;
template <class T> GroupMul<T> op(const GroupMul<T> &a, const GroupMul<T> &b);
template <class T = std::int64_t> class GroupMul {
  T _x;

public:
  GroupMul(T x) : _x(x) { assert(x != 0); }
  GroupMul() : GroupMul(e()) {}
  T x() const { return _x; }
  static GroupMul e() { return 1; }
  friend GroupMul op<T>(const GroupMul &a, const GroupMul &b);
  friend GroupMul op(const GroupMul &a, const GroupMul &b) {
    return a._x * b._x;
  }
  GroupMul inv() const { return 1 / _x; }
};

// アフィン写像 y = ax + b
template <class T> class GroupAffine;
template <class T> GroupAffine<T> op(const GroupAffine<T> &p, const GroupAffine<T> &q);
template <class T = std::int64_t> class GroupAffine {
  T _a, _b;

public:
  GroupAffine(T a, T b) : _a(a), _b(b) {}
  GroupAffine() : GroupAffine(e()) {}
  T a() const { return _a; }
  T b() const { return _b; }
  static GroupAffine e() { return {1, 0}; }
  friend GroupAffine op<T>(const GroupAffine &p, const GroupAffine &q);
  friend GroupAffine op(const GroupAffine &p, const GroupAffine &q) {
    return {p._a * q._a, p._b * q._a + q._b};
  }
  GroupAffine inv() const { return {1 / _a, -_b / _a}; }
  T apply(const T &x) const { return _a * x + _b; }
};

// Preserve the qualified cp::op API as well as the original hidden friends.
template <class T> GroupSum<T> op(const GroupSum<T> &a, const GroupSum<T> &b) {
  return GroupSum<T>(a._x + b._x);
}
template <class T> GroupMul<T> op(const GroupMul<T> &a, const GroupMul<T> &b) {
  return GroupMul<T>(a._x * b._x);
}
template <class T> GroupAffine<T> op(const GroupAffine<T> &p, const GroupAffine<T> &q) {
  return GroupAffine<T>(p._a * q._a, p._b * q._a + q._b);
}

} // namespace cp

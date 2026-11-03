#pragma once
#include <cassert>
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// Groups for data structures that need inverses. GroupSum and GroupMul wrap one value `_x`, GroupAffine two (`_a`, `_b`); the default constructor and the static
// member e() build the identity, `op(a, b)` is the group operation and `inv()` the inverse. Derived from
// experiments/library/cpp/algebraic_structure/group.hpp: the class templates keep their type parameter T (the verified
// instances are the ones with T = long long, instantiated explicitly at the end of the file).
// Differences: `op` is a function template that is a friend of the instance (a friend function defined in a class
// template is instantiated only when it is used, so it could not be checked for the instance); it is found by
// argument-dependent lookup exactly as the friend was. The default constructors write the identity directly instead of
// delegating to e(). Return values are written as explicit constructor calls.
// For long long, GroupMul::inv() is the integer division 1 / _x (as in the original, which expects a floating T): it is
// the true inverse only for _x = 1 and -1, and for any other value the constructor's assert fails.
// GroupSum needs a + b and -a to fit in the type T. GroupAffine keeps the original const T & argument of apply,
// the two fields and the same members as the original.
template <class T> class GroupSum;
template <class T> GroupSum<T> op(const GroupSum<T> &a, const GroupSum<T> &b);
template <class T = long long> class GroupSum {
  T _x;

public:
  GroupSum(T x_) : _x(x_) {}
  GroupSum() : _x(0) {}
  T x() const { return _x; }
  static GroupSum e() { return 0; }
  friend GroupSum op<T>(const GroupSum &a, const GroupSum &b);
  GroupSum inv() const { return GroupSum(-_x); }
};
template <class T> GroupSum<T> op(const GroupSum<T> &a, const GroupSum<T> &b) { return GroupSum<T>(a._x + b._x); }

template <class T> class GroupMul;
template <class T> GroupMul<T> op(const GroupMul<T> &a, const GroupMul<T> &b);
template <class T = long long> class GroupMul {
  T _x;

public:
  GroupMul(T x) : _x(x) { assert(x != 0); }
  GroupMul() : _x(1) {}
  T x() const { return _x; }
  static GroupMul e() { return 1; }
  friend GroupMul op<T>(const GroupMul &a, const GroupMul &b);
  GroupMul inv() const { return GroupMul(1 / _x); }
};
template <class T> GroupMul<T> op(const GroupMul<T> &a, const GroupMul<T> &b) { return GroupMul<T>(a._x * b._x); }

template <class T> class GroupAffine;
template <class T> GroupAffine<T> op(const GroupAffine<T> &p, const GroupAffine<T> &q);
// The affine map y = a * x + b; op(p, q) applies p first and then q: op(p, q).apply(x) == q.apply(p.apply(x)).
template <class T = long long> class GroupAffine {
  T _a, _b;

public:
  GroupAffine(T a, T b) : _a(a), _b(b) {}
  GroupAffine() : _a(1), _b(0) {}
  T a() const { return _a; }
  T b() const { return _b; }
  static GroupAffine e() { return GroupAffine(1, 0); }
  friend GroupAffine op<T>(const GroupAffine &p, const GroupAffine &q);
  GroupAffine inv() const { return GroupAffine(1 / _a, -_b / _a); }
  T apply(const T &x) const { return _a * x + _b; }
};
template <class T> GroupAffine<T> op(const GroupAffine<T> &p, const GroupAffine<T> &q) {
  return GroupAffine<T>(p._a * q._a, p._b * q._a + q._b);
}

template class GroupSum<long long>;
template class GroupMul<long long>;
template GroupSum<long long> op(const GroupSum<long long> &, const GroupSum<long long> &);
template GroupMul<long long> op(const GroupMul<long long> &, const GroupMul<long long> &);
template class GroupAffine<long long>;
template GroupAffine<long long> op(const GroupAffine<long long> &, const GroupAffine<long long> &);

} // namespace cp

#include "algebraic_structure/monoid_lazy.hpp"
#include <limits>
#include <vector>

template<template<class> class Family, class T> bool identities() {
  using Max = typename Family<T>::RangeMax;
  using Min = typename Family<T>::RangeMin;
  const Max max_default;
  const Min min_default;
  const auto max_identity = Max::e();
  const auto min_identity = Min::e();
  if (max_default.x != max_identity.x || min_default.x != min_identity.x) return false;
  std::vector<T> values = {std::numeric_limits<T>::lowest(), T(-7), T(-0.0), T(0), T(7), std::numeric_limits<T>::max()};
  if constexpr (std::numeric_limits<T>::has_infinity) {
    values.push_back(-std::numeric_limits<T>::infinity());
    values.push_back(std::numeric_limits<T>::infinity());
  }
  for (T value : values) {
    const Max a(value);
    const Min b(value);
    if (op(a,max_identity).x != value || op(max_identity,a).x != value) return false;
    if (op(b,min_identity).x != value || op(min_identity,b).x != value) return false;
  }
  return true;
}

// This type deliberately has no unary minus or ordering operators. The old
// e() API only needs the primary numeric_limits min()/max() and value copies.
struct Opaque {
  int marker;
  constexpr Opaque() : marker(42) {}
};
template<template<class> class Family> bool opaque_api() {
  const auto high = Family<Opaque>::RangeMax::e();
  const auto low = Family<Opaque>::RangeMin::e();
  return high.x.marker == 42 && low.x.marker == 42;
}
int main() {
  return identities<RangeAddRangeMaxMin,float>() && identities<RangeSetRangeMaxMin,float>() &&
    identities<RangeAddRangeMaxMin,double>() && identities<RangeSetRangeMaxMin,double>() &&
    identities<RangeAddRangeMaxMin,long double>() && identities<RangeSetRangeMaxMin,long double>() &&
    identities<RangeAddRangeMaxMin,long long>() && identities<RangeSetRangeMaxMin,long long>() &&
    opaque_api<RangeAddRangeMaxMin>() && opaque_api<RangeSetRangeMaxMin>() ? 0 : 1;
}

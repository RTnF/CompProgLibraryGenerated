#pragma once
// Standalone Euclidean helper fixture for frontend regression tests.

// Staging helpers for Ratio; not a public component. Inputs and intermediates,
// including magnitudes and the LCM, must fit T, as for the std numeric contract.
namespace cp {
template <typename T> T ratio_gcd_nonnegative(T a, T b) {
  while (b != 0) {
    T r = a % b;
    a = b;
    b = r;
  }
  return a;
}

template <typename T> T ratio_gcd(T a, T b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  return ratio_gcd_nonnegative(a, b);
}

template <typename T> T ratio_lcm(T a, T b) {
  if (a == 0 || b == 0) return 0;
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  return a / ratio_gcd_nonnegative(a, b) * b;
}
} // namespace cp

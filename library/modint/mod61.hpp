#pragma once
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// Arithmetic modulo the Mersenne prime 2^61 - 1, as used by the rolling hash.
// mod61 reduces any 64 bit value; mul61 multiplies two values below 2^61 and returns a
// representative congruent to the product that is below 2^64 (not necessarily fully reduced).

inline unsigned long long mod61(unsigned long long x) {
  const unsigned long long m = (1ull << 61) - 1;
  unsigned long long xu = x >> 61;
  unsigned long long xd = x & m;
  unsigned long long res = xu + xd;
  if (res >= m) {
    res = res - m;
  }
  return res;
}

inline unsigned long long mul61(unsigned long long a, unsigned long long b) {
  const unsigned long long m31 = (1ull << 31) - 1;
  const unsigned long long m30 = (1ull << 30) - 1;
  unsigned long long au = a >> 31;
  unsigned long long ad = a & m31;
  unsigned long long bu = b >> 31;
  unsigned long long bd = b & m31;
  unsigned long long mid = ad * bu + au * bd;
  unsigned long long midu = mid >> 30;
  unsigned long long midd = mid & m30;
  return au * bu * 2 + midu + (midd << 31) + ad * bd;
}

} // namespace cp

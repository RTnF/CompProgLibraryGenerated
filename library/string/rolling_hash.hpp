#pragma once
#include <vector>

namespace cp {

// Rolling hash modulo the Mersenne prime 2^61 - 1 with the base 131 (experiments/library/cpp/string/rolling_hash.hpp,
// SimpleRollingHash), over a vector of integers. hash_sum_[i] is the hash of the first i elements
// (hash_sum_[i + 1] = (hash_sum_[i] * 131 + s[i]) mod (2^61 - 1)) and pows[i] = 131^i mod (2^61 - 1), so
// hash_sum_.size() == pows.size() == n + 1. The class template keeps the element type T (the verified instance is
// RollingHash<int>, instantiated explicitly below).
// Differences from the original: the field n_ is not kept (it is hash_sum_.size() - 1); the constant base is a local
// of the constructor; mul and mod of the original (rh_in) are written inline with the same operations; the string
// overloads, match, match_custom, starts_with and ends_with are not included yet.
// hash(l, r) is the hash of s[l, r): (hash_sum_[r] - hash_sum_[l] * pows[r - l]) mod (2^61 - 1), in [0, 2^61 - 1).
// Preconditions: 0 <= s[i] < 2^31; s.size() < 2^31 - 1; 0 <= l <= r <= n.
template <class T = int> class RollingHash {
  std::vector<unsigned long long> hash_sum_;
  std::vector<unsigned long long> pows;

public:
  RollingHash(const std::vector<T> &s) : hash_sum_(s.size() + 1), pows(s.size() + 1) {
    unsigned long long b = 131;
    unsigned long long m = (1ull << 61) - 1;
    unsigned long long m31 = (1ull << 31) - 1;
    unsigned long long m30 = (1ull << 30) - 1;
    int n = (int)s.size();
    hash_sum_[0] = 0;
    pows[0] = 1;
    for (int i = 0; i < n; i++) {
      {
        unsigned long long a = hash_sum_[i];
        unsigned long long au = a >> 31;
        unsigned long long ad = a & m31;
        unsigned long long bu = b >> 31;
        unsigned long long bd = b & m31;
        unsigned long long mid = ad * bu + au * bd;
        unsigned long long midu = mid >> 30;
        unsigned long long midd = mid & m30;
        unsigned long long mulv = au * bu * 2 + midu + (midd << 31) + ad * bd;
        unsigned long long x = mulv + (unsigned long long)s[i];
        unsigned long long xu = x >> 61;
        unsigned long long xd = x & m;
        unsigned long long res = xu + xd;
        if (res >= m) {
          res = res - m;
        }
        hash_sum_[i + 1] = res;
      }
      {
        unsigned long long a = pows[i];
        unsigned long long au = a >> 31;
        unsigned long long ad = a & m31;
        unsigned long long bu = b >> 31;
        unsigned long long bd = b & m31;
        unsigned long long mid = ad * bu + au * bd;
        unsigned long long midu = mid >> 30;
        unsigned long long midd = mid & m30;
        unsigned long long mulv = au * bu * 2 + midu + (midd << 31) + ad * bd;
        unsigned long long x = mulv;
        unsigned long long xu = x >> 61;
        unsigned long long xd = x & m;
        unsigned long long res = xu + xd;
        if (res >= m) {
          res = res - m;
        }
        pows[i + 1] = res;
      }
    }
  }
  // [l, r)
  unsigned long long hash(int l, int r) const {
    unsigned long long m = (1ull << 61) - 1;
    unsigned long long m31 = (1ull << 31) - 1;
    unsigned long long m30 = (1ull << 30) - 1;
    unsigned long long a = hash_sum_[l];
    unsigned long long b = pows[r - l];
    unsigned long long au = a >> 31;
    unsigned long long ad = a & m31;
    unsigned long long bu = b >> 31;
    unsigned long long bd = b & m31;
    unsigned long long mid = ad * bu + au * bd;
    unsigned long long midu = mid >> 30;
    unsigned long long midd = mid & m30;
    unsigned long long mulv = au * bu * 2 + midu + (midd << 31) + ad * bd;
    unsigned long long x = hash_sum_[r] + 4 * m - mulv;
    unsigned long long xu = x >> 61;
    unsigned long long xd = x & m;
    unsigned long long res = xu + xd;
    if (res >= m) {
      res = res - m;
    }
    return res;
  }
  // [0, a)
  unsigned long long hash(int a) const { return hash(0, a); }
};

template class RollingHash<int>;

} // namespace cp

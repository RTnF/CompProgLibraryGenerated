#pragma once
#include <cassert>
#include <cstdint>
#include <string>
#include <vector>

namespace cp {

namespace rh_in {
constexpr std::uint64_t M30 = 1073741823ul;
constexpr std::uint64_t M31 = 2147483647ul;
constexpr std::uint64_t M61 = 2305843009213693951ul;
constexpr int SZ_BASE = 16;

constexpr std::uint64_t base[SZ_BASE] = {
    131ul, 137ul, 139ul, 149ul, 151ul, 157ul, 163ul, 167ul,
    173ul, 179ul, 181ul, 191ul, 193ul, 197ul, 199ul, 211ul};

constexpr std::uint64_t mul(std::uint64_t a, std::uint64_t b) {
  std::uint64_t au = a >> 31;
  std::uint64_t ad = a & M31;
  std::uint64_t bu = b >> 31;
  std::uint64_t bd = b & M31;
  std::uint64_t mid = ad * bu + au * bd;
  std::uint64_t midu = mid >> 30;
  std::uint64_t midd = mid & M30;
  return au * bu * 2 + midu + (midd << 31) + ad * bd;
}
constexpr std::uint64_t mod(std::uint64_t x) {
  std::uint64_t xu = x >> 61;
  std::uint64_t xd = x & M61;
  std::uint64_t res = xu + xd;
  if (res >= M61) {
    res -= M61;
  }
  return res;
}

inline std::vector<char> to_vec_char(const std::string &s) {
  std::vector<char> vc(s.size());
  for (int i = 0; i < (int)s.size(); i++) {
    vc[i] = s[i];
  }
  return vc;
}

} // namespace rh_in

constexpr std::uint64_t RH_NPOS = 18446744073709551615ul;
template <class T> std::uint64_t reduce_symbol(T value) {
  const std::int64_t signed_value = (std::int64_t)value;
  return signed_value < 0 ? (std::uint64_t)(signed_value + (std::int64_t)rh_in::M61) : (std::uint64_t)signed_value;
}
constexpr std::uint64_t base_at(int i) {
  assert(0 <= i && i < rh_in::SZ_BASE);
  return rh_in::base[i];
}
template <class T> std::uint64_t append_hash(std::uint64_t h, std::uint64_t b, T v) {
  const std::uint64_t product = rh_in::mul(h, b);
  const std::uint64_t symbol = reduce_symbol(v);
  return rh_in::mod(product + symbol);
}
inline std::uint64_t hash_interval(std::uint64_t left, std::uint64_t right, std::uint64_t power) {
  const std::uint64_t wide = rh_in::mul(left, power);
  const std::uint64_t product = rh_in::mod(wide);
  return (right + rh_in::M61 - product) % rh_in::M61;
}
// https://qiita.com/keymoon/items/11fac5627672a6d6a9f6
class MultiRollingHash {
  std::vector<std::uint64_t> hash_sum_;
  std::vector<std::uint64_t> pows;
  int n_;
  int strength_;

  template <class T> void build(const std::vector<T> &s, int i_base) {
    std::uint64_t b = base_at(i_base);
    const std::int64_t row = (std::int64_t)i_base * ((std::int64_t)n_ + 1);
    pows[row + 0] = 1;
    const int length = n_;
    for (int i = 0; i < length; i++) {
      hash_sum_[row + i + 1] =
          append_hash(hash_sum_[row + i], b, s[i]);
      pows[row + i + 1] = rh_in::mod(rh_in::mul(pows[row + i], b));
    }
  }

  template <class T> std::uint64_t hash_all(const std::vector<T> &t, int i_base) const {
    int n_t = t.size();
    std::uint64_t hash_t = 0;
    const std::uint64_t b = base_at(i_base);
    for (int i = 0; i < n_t; i++) {
      hash_t = append_hash(hash_t, b, t[i]);
    }
    return hash_t;
  }
  template <class T> std::vector<std::uint64_t> hash_all(const std::vector<T> &t) const {
    std::vector<std::uint64_t> h(strength_);
    const int active_bases = strength_;
    for (int i = 0; i < active_bases; i++) {
      const int index = i;
      h[i] = hash_all(t, index);
    }
    return h;
  }

  std::uint64_t hash(int l, int r, int i_base) const {
    const std::int64_t row = (std::int64_t)i_base * ((std::int64_t)n_ + 1);
    return hash_interval(hash_sum_[row + l], hash_sum_[row + r], pows[row + r - l]);
  }

  bool match(int l, int r, const std::vector<std::uint64_t> &h) const {
    const int active_bases = strength_;
    for (int i_base = 0; i_base < active_bases; i_base++) {
      const int index = i_base;
      if (hash(l, r, index) != h[i_base]) {
        return false;
      }
    }
    return true;
  }

public:
  MultiRollingHash(const std::string &s, int strength = 1)
      : n_(s.size()), strength_(strength) {
    assert(strength <= rh_in::SZ_BASE);
    const int rows = strength < 0 ? 0 : strength;
    const std::int64_t total = (std::int64_t)rows * ((std::int64_t)n_ + 1);
    hash_sum_.resize(total);
    pows.resize(total);
    for (int i = 0; i < rows; i++) {
      const int index = i;
      build(rh_in::to_vec_char(s), index);
    }
  }
  // T: 4バイト以下の整数型
  template <class T>
  MultiRollingHash(const std::vector<T> &s, int strength = 1)
      : n_(s.size()), strength_(strength) {
    assert(strength <= rh_in::SZ_BASE);
    const int rows = strength < 0 ? 0 : strength;
    const std::int64_t total = (std::int64_t)rows * ((std::int64_t)n_ + 1);
    hash_sum_.resize(total);
    pows.resize(total);
    for (int i = 0; i < rows; i++) {
      const int index = i;
      build(s, index);
    }
  }

  // [l, r)
  std::vector<std::uint64_t> hash(int l, int r) const {
    assert(0 <= l);
    assert(l <= r);
    assert(r <= n_);
    std::vector<std::uint64_t> h(strength_);
    const int active_bases = strength_;
    for (int i = 0; i < active_bases; i++) {
      const int index = i;
      h[i] = hash(l, r, index);
    }
    return h;
  }
  // [0,a)
  std::vector<std::uint64_t> hash(int a) const { return hash(0, a); }

  // ない場合はnpos
  std::size_t match(const std::string &t) const { return match_vector(rh_in::to_vec_char(t)); }
  // ない場合はnpos
  template <class T> std::size_t match(const std::vector<T> &t) const { return match_vector(t); }
private:
  template <class T> std::size_t match_vector(const std::vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return RH_NPOS;
    }
    std::vector<std::uint64_t> ht = hash_all(t);
    const int last = n_ - n_t;
    for (int i = 0; i <= last; i++) {
      const int index = i;
      if (match(index, index + n_t, ht)) {
        return i;
      }
    }
    return RH_NPOS;
  }

  // ない場合はnpos
public:
  std::size_t match_custom(const std::string &t, const std::vector<int> &idx) const {
    return match_custom_vector(rh_in::to_vec_char(t), idx);
  }
  // ない場合はnpos
  template <class T>
  std::size_t match_custom(const std::vector<T> &t, const std::vector<int> &idx) const { return match_custom_vector(t, idx); }
private:
  template <class T> std::size_t match_custom_vector(const std::vector<T> &t, const std::vector<int> &idx) const {
    int n_t = t.size();
    if (n_t > n_) {
      return RH_NPOS;
    }
    std::vector<std::uint64_t> ht = hash_all(t);
    for (int i = 0; i < (int)idx.size(); i++) {
      assert(0 <= idx[i]);
      assert(idx[i] <= n_ - n_t);
      if (match(idx[i], idx[i] + n_t, ht)) {
        return idx[i];
      }
    }
    return RH_NPOS;
  }

public:
  bool starts_with(const std::string &t) const {
    return starts_with_vector(rh_in::to_vec_char(t));
  }
  template <class T> bool starts_with(const std::vector<T> &t) const { return starts_with_vector(t); }
private:
  template <class T> bool starts_with_vector(const std::vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return false;
    }
    std::vector<std::uint64_t> ht = hash_all(t);
    return match(0, n_t, ht);
  }

public:
  bool ends_with(const std::string &t) const {
    return ends_with_vector(rh_in::to_vec_char(t));
  }
  template <class T> bool ends_with(const std::vector<T> &t) const { return ends_with_vector(t); }
private:
  template <class T> bool ends_with_vector(const std::vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return false;
    }
    std::vector<std::uint64_t> ht = hash_all(t);
    return match(n_ - n_t, n_, ht);
  }
};

// https://qiita.com/keymoon/items/11fac5627672a6d6a9f6
constexpr std::uint64_t SIMPLE_BASE = 131ul;

class SimpleRollingHash {
  std::vector<std::uint64_t> hash_sum_;
  std::vector<std::uint64_t> pows;
  int n_;

  template <class T> void build(const std::vector<T> &s) {
    hash_sum_.resize(n_ + 1);
    pows.resize(n_ + 1);
    pows[0] = 1;
    const int length = n_;
    for (int i = 0; i < length; i++) {
      hash_sum_[i + 1] = append_hash(hash_sum_[i], SIMPLE_BASE, s[i]);
      pows[i + 1] = rh_in::mod(rh_in::mul(pows[i], SIMPLE_BASE));
    }
  }

  template <class T> std::uint64_t hash_all(const std::vector<T> &t) const {
    int n_t = t.size();
    std::uint64_t hash_t = 0;
    for (int i = 0; i < n_t; i++) {
      hash_t = append_hash(hash_t, SIMPLE_BASE, t[i]);
    }
    return hash_t;
  }

public:
  SimpleRollingHash(const std::string &s) : n_(s.size()) {
    build(rh_in::to_vec_char(s));
  }
  // T: 4バイト以下の整数型
  template <class T> SimpleRollingHash(const std::vector<T> &s) : n_(s.size()) {
    build(s);
  }

  // [l, r)
  std::uint64_t hash(int l, int r) const {
    return hash_interval(hash_sum_[l], hash_sum_[r], pows[r - l]);
  }
  // [0,a)
  std::uint64_t hash(int a) const { return hash(0, a); }

  // ない場合はnpos
  std::size_t match(const std::string &t) const { return match_vector(rh_in::to_vec_char(t)); }
  // ない場合はnpos
  template <class T> std::size_t match(const std::vector<T> &t) const { return match_vector(t); }
private:
  template <class T> std::size_t match_vector(const std::vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return RH_NPOS;
    }
    std::uint64_t h_t = hash_all(t);
    const int last = n_ - n_t;
    for (int i = 0; i <= last; i++) {
      const int index = i;
      if (hash(index, index + n_t) == h_t) {
        return i;
      }
    }
    return RH_NPOS;
  }

  // ない場合はnpos
public:
  std::size_t match_custom(const std::string &t, const std::vector<int> &idx) const {
    return match_custom_vector(rh_in::to_vec_char(t), idx);
  }
  // ない場合はnpos
  template <class T>
  std::size_t match_custom(const std::vector<T> &t, const std::vector<int> &idx) const { return match_custom_vector(t, idx); }
private:
  template <class T> std::size_t match_custom_vector(const std::vector<T> &t, const std::vector<int> &idx) const {
    int n_t = t.size();
    if (n_t > n_) {
      return RH_NPOS;
    }
    std::uint64_t h_t = hash_all(t);
    for (int i = 0; i < (int)idx.size(); i++) {
      assert(0 <= idx[i]);
      assert(idx[i] <= n_ - n_t);
      if (hash(idx[i], idx[i] + n_t) == h_t) {
        return idx[i];
      }
    }
    return RH_NPOS;
  }

public:
  bool starts_with(const std::string &t) const {
    return starts_with_vector(rh_in::to_vec_char(t));
  }
  template <class T> bool starts_with(const std::vector<T> &t) const { return starts_with_vector(t); }
private:
  template <class T> bool starts_with_vector(const std::vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return false;
    }
    std::uint64_t h_t = hash_all(t);
    return hash(0, n_t) == h_t;
  }

public:
  bool ends_with(const std::string &t) const {
    return ends_with_vector(rh_in::to_vec_char(t));
  }
  template <class T> bool ends_with(const std::vector<T> &t) const { return ends_with_vector(t); }
private:
  template <class T> bool ends_with_vector(const std::vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return false;
    }
    std::uint64_t h_t = hash_all(t);
    return hash(n_ - n_t, n_) == h_t;
  }
};

// The previously published single-base template API.
template <class T = int> class RollingHash {
  SimpleRollingHash impl_;

public:
  RollingHash(const std::vector<T> &s) : impl_(s) {}
  unsigned long long hash(int l, int r) const { return impl_.hash(l, r); }
  unsigned long long hash(int r) const { return impl_.hash(r); }
};

namespace rolling_hash {
using RollingHash = cp::MultiRollingHash;
}

} // namespace cp

#pragma once
#include "template/small_template.hpp"

namespace rh_in {
constexpr ull M30 = (1ul << 30) - 1;
constexpr ull M31 = (1ul << 31) - 1;
constexpr ull M61 = (1ul << 61) - 1;
constexpr int SZ_BASE = 16;
constexpr ull base[SZ_BASE] = {131, 137, 139, 149, 151, 157, 163, 167,
                               173, 179, 181, 191, 193, 197, 199, 211};
constexpr ull mul(ull a, ull b) {
  ull au = a >> 31;
  ull ad = a & M31;
  ull bu = b >> 31;
  ull bd = b & M31;
  ull mid = ad * bu + au * bd;
  ull midu = mid >> 30;
  ull midd = mid & M30;
  return au * bu * 2 + midu + (midd << 31) + ad * bd;
}
constexpr ull mod(ull x) {
  ull xu = x >> 61;
  ull xd = x & M61;
  ull res = xu + xd;
  if (res >= M61) {
    res -= M61;
  }
  return res;
}
vector<char> to_vec_char(const string &s) {
  vector<char> vc(s.size());
  for (int i = 0; i < (int)s.size(); i++) {
    vc[i] = s[i];
  }
  return vc;
}
}; // namespace rh_in

// https://qiita.com/keymoon/items/11fac5627672a6d6a9f6
class RollingHash {
  vector<ull> hash_sum_[rh_in::SZ_BASE];
  vector<ull> pows[rh_in::SZ_BASE];
  int n_;
  int strength_;

  template <class T> void build(const vector<T> &s, int i_base) {
    ull b = rh_in::base[i_base];
    hash_sum_[i_base].resize(n_ + 1);
    pows[i_base].resize(n_ + 1);
    pows[i_base][0] = 1;
    for (int i = 0; i < n_; i++) {
      hash_sum_[i_base][i + 1] =
          rh_in::mod(rh_in::mul(hash_sum_[i_base][i], b) + s[i]);
      pows[i_base][i + 1] = rh_in::mod(rh_in::mul(pows[i_base][i], b));
    }
  }

  template <class T> ull hash_all(const vector<T> &t, int i_base) const {
    int n_t = t.size();
    ull hash_t = 0;
    for (int i = 0; i < n_t; i++) {
      hash_t = rh_in::mod(rh_in::mul(hash_t, rh_in::base[i_base]) + t[i]);
    }
    return hash_t;
  }
  template <class T> vector<ull> hash_all(const vector<T> &t) const {
    vector<ull> h(strength_);
    for (int i = 0; i < strength_; i++) {
      h[i] = hash_all(t, i);
    }
    return h;
  }

  ull hash(int l, int r, int i_base) const {
    return rh_in::mod(hash_sum_[i_base][r] + (rh_in::M61 << 2) -
                      rh_in::mul(hash_sum_[i_base][l], pows[i_base][r - l]));
  }

  bool match(int l, int r, const vector<ull> &h) const {
    for (int i_base = 0; i_base < strength_; i_base++) {
      if (hash(l, r, i_base) != h[i_base]) {
        return false;
      }
    }
    return true;
  }

public:
  RollingHash(const string &s, int strength = 1)
      : n_(s.size()), strength_(strength) {
    assert(strength <= rh_in::SZ_BASE);
    for (int i = 0; i < strength; i++) {
      build(rh_in::to_vec_char(s), i);
    }
  }
  // T: 4バイト以下の整数型
  template <class T>
  RollingHash(const vector<T> &s, int strength = 1)
      : n_(s.size()), strength_(strength) {
    assert(strength <= rh_in::SZ_BASE);
    for (int i = 0; i < strength; i++) {
      build(s, i);
    }
  }

  // [l, r)
  vector<ull> hash(int l, int r) const {
    assert(0 <= l);
    assert(l <= r);
    assert(r <= n_);
    vector<ull> h(strength_);
    for (int i = 0; i < strength_; i++) {
      h[i] = hash(l, r, i);
    }
    return h;
  }
  // [0,a)
  vector<ull> hash(int a) const { return hash(0, a); }

  // ない場合はnpos
  size_t match(const string &t) const { return match(rh_in::to_vec_char(t)); }
  // ない場合はnpos
  template <class T> size_t match(const vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return string::npos;
    }
    vector<ull> ht = hash_all(t);
    for (int i = 0; i <= n_ - n_t; i++) {
      if (match(i, i + n_t, ht)) {
        return i;
      }
    }
    return string::npos;
  }

  // ない場合はnpos
  size_t match_custom(const string &t, const vector<int> &idx) const {
    return match_custom(rh_in::to_vec_char(t), idx);
  }
  // ない場合はnpos
  template <class T>
  size_t match_custom(const vector<T> &t, const vector<int> &idx) const {
    int n_t = t.size();
    if (n_t > n_) {
      return string::npos;
    }
    vector<ull> ht = hash_all(t);
    for (int i = 0; i < (int)idx.size(); i++) {
      assert(0 <= idx[i]);
      assert(idx[i] <= n_ - n_t);
      if (match(idx[i], idx[i] + n_t, ht)) {
        return idx[i];
      }
    }
    return string::npos;
  }

  bool starts_with(const string &t) const {
    return starts_with(rh_in::to_vec_char(t));
  }
  template <class T> bool starts_with(const vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return false;
    }
    vector<ull> ht = hash_all(t);
    return match(0, n_t, ht);
  }

  bool ends_with(const string &t) const {
    return ends_with(rh_in::to_vec_char(t));
  }
  template <class T> bool ends_with(const vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return false;
    }
    vector<ull> ht = hash_all(t);
    return match(n_ - n_t, n_, ht);
  }
};

// https://qiita.com/keymoon/items/11fac5627672a6d6a9f6
class SimpleRollingHash {
  static constexpr ull base = 131;
  vector<ull> hash_sum_;
  vector<ull> pows;
  int n_;

  template <class T> void build(const vector<T> &s) {
    hash_sum_.resize(n_ + 1);
    pows.resize(n_ + 1);
    pows[0] = 1;
    for (int i = 0; i < n_; i++) {
      hash_sum_[i + 1] = rh_in::mod(rh_in::mul(hash_sum_[i], base) + s[i]);
      pows[i + 1] = rh_in::mod(rh_in::mul(pows[i], base));
    }
  }

  template <class T> ull hash_all(const vector<T> &t) const {
    int n_t = t.size();
    ull hash_t = 0;
    for (int i = 0; i < n_t; i++) {
      hash_t = rh_in::mod(rh_in::mul(hash_t, base) + t[i]);
    }
    return hash_t;
  }

public:
  SimpleRollingHash(const string &s) : n_(s.size()) {
    build(rh_in::to_vec_char(s));
  }
  // T: 4バイト以下の整数型
  template <class T> SimpleRollingHash(const vector<T> &s) : n_(s.size()) {
    build(s);
  }

  // [l, r)
  ull hash(int l, int r) const {
    return rh_in::mod(hash_sum_[r] + (rh_in::M61 << 2) -
                      rh_in::mul(hash_sum_[l], pows[r - l]));
  }
  // [0,a)
  ull hash(int a) const { return hash(0, a); }

  // ない場合はnpos
  size_t match(const string &t) const { return match(rh_in::to_vec_char(t)); }
  // ない場合はnpos
  template <class T> size_t match(const vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return string::npos;
    }
    ull h_t = hash_all(t);
    for (int i = 0; i <= n_ - n_t; i++) {
      if (hash(i, i + n_t) == h_t) {
        return i;
      }
    }
    return string::npos;
  }

  // ない場合はnpos
  size_t match_custom(const string &t, const vector<int> &idx) const {
    return match_custom(rh_in::to_vec_char(t), idx);
  }
  // ない場合はnpos
  template <class T>
  size_t match_custom(const vector<T> &t, const vector<int> &idx) const {
    int n_t = t.size();
    if (n_t > n_) {
      return string::npos;
    }
    ull h_t = hash_all(t);
    for (int i = 0; i < (int)idx.size(); i++) {
      assert(0 <= idx[i]);
      assert(idx[i] <= n_ - n_t);
      if (hash(idx[i], idx[i] + n_t) == h_t) {
        return idx[i];
      }
    }
    return string::npos;
  }

  bool starts_with(const string &t) const {
    return starts_with(rh_in::to_vec_char(t));
  }
  template <class T> bool starts_with(const vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return false;
    }
    ull h_t = hash_all(t);
    return hash(0, n_t) == h_t;
  }

  bool ends_with(const string &t) const {
    return ends_with(rh_in::to_vec_char(t));
  }
  template <class T> bool ends_with(const vector<T> &t) const {
    int n_t = t.size();
    if (n_t > n_) {
      return false;
    }
    ull h_t = hash_all(t);
    return hash(n_ - n_t, n_) == h_t;
  }
};
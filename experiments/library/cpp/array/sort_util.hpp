#pragma once
#include "template/small_template.hpp"

// 逆置換
// v: 0-indexed 順列
// 例：[2, 4, 0, 1, 3] -> [2, 3, 0, 4, 1]
template <class T> vector<int> inv_perm(const vector<T> &v) {
  int n = v.size();
  vector<int> inv(n, -1);
  for (int i = 0; i < n; i++) {
    assert(0 <= v[i] && v[i] < n);
    assert(inv[v[i]] == -1);
    inv[v[i]] = i;
  }
  return inv;
}

// ソート結果を配列のindexで得る O(n log n)
// 例：[3, 3, 1, 5, 2] -> [1(2), 2(4), 3(0), 3(1), 5(3)] -> [2, 4, 0, 1, 3]
template <class T> vector<int> arg_sort(const vector<T> &v) {
  vector<int> arg(v.size());
  iota(arg.begin(), arg.end(), 0);
  stable_sort(arg.begin(), arg.end(),
              [&](int a, int b) { return v[a] < v[b]; });
  return arg;
}

// ソートでindexがどこに移動するか O(n log n)
// 例：[3, 3, 1, 5, 2] -> [2, 3, 0, 4, 1]
template <class T> vector<int> inv_arg_sort(const vector<T> &v) {
  return inv_perm(arg_sort(v));
}

// @brief 座標圧縮 O(n log n)
// 例：[3, 3, 1, 5, 2] -> [2, 2, 0, 3, 1] + offset
// unzip: [1, 2, 3, 5]
template <class T>
vector<T> compress(const vector<T> &x, vector<T> &unzip, int offset = 0) {
  int n = x.size();
  vector<T> cmp(n);
  unzip = x;
  sort(unzip.begin(), unzip.end());
  unzip.erase(unique(unzip.begin(), unzip.end()), unzip.end());
  for (int i = 0; i < n; i++) {
    cmp[i] =
        lower_bound(unzip.begin(), unzip.end(), x[i]) - unzip.begin() + offset;
  }
  return cmp;
}

// 座標圧縮 O(n log n)
// 例：[3, 3, 1, 5, 2] -> [2, 2, 0, 3, 1] + offset
template <class T> vector<T> compress(const vector<T> &x, int offset = 0) {
  auto tmp = vector<T>();
  return compress(x, tmp, offset);
}
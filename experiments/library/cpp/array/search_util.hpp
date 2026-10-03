#pragma once
#include "template/small_template.hpp"

template <class T>
int count(const vector<T> &v, T value, int idx_begin = 0, int idx_end = -1) {
  if (idx_end == -1) {
    idx_end = v.size();
  }
  int cnt = 0;
  for (int i = idx_begin; i < idx_end; i++) {
    if (v[i] == value) {
      cnt++;
    }
  }
  return cnt;
}

/**
 * @brief 個数を数える
 *
 * @tparam T
 * @param v_sorted ソート済みでなければならない
 * @return vector<pair<T, int>> (値, 個数)
 */
template <class T> vector<pair<T, int>> counts(const vector<T> &v_sorted) {
  vector<pair<T, int>> ret;
  int s = v_sorted.size();
  for (int i = 0; i < s; i++) {
    if (i == 0 || ret.back().first != v_sorted[i]) {
      ret.emplace_back(v_sorted[i], 1);
    } else {
      ret.back().second++;
    }
  }
  return ret;
}
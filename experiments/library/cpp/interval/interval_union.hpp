#pragma once
#include "template/small_template.hpp"

/**
 * @brief 区間の和集合
 *
 * @tparam T
 * @param v [l, r] 途中でソートされる
 * @return vector<pair<T, T>> [l, r]
 */
template <class T>
vector<pair<T, T>> interval_union_inclusive(vector<pair<T, T>> &v) {
  sort(v.begin(), v.end());
  vector<pair<T, T>> ret;
  for (auto &&[l, r] : v) {
    if (ret.empty() || ret.back().second < l) {
      ret.emplace_back(l, r);
    } else if (ret.back().second < r) {
      ret.back().second = r;
    }
  }
  return ret;
}
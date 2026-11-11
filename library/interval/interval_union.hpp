#pragma once
#include <algorithm>
#include <utility>
#include <vector>

namespace cp {

/**
 * @brief 区間の和集合
 *
 * @tparam T
 * @param v [l, r] 途中でソートされる
 * @return vector<pair<T, T>> [l, r]
 */
// The union of closed intervals [l, r] (experiments/library/cpp/interval/interval_union.hpp). v is sorted in place.
// Precondition: l <= r for every interval. Time O(n log n).
template <class T>
std::vector<std::pair<T, T>> interval_union_inclusive(std::vector<std::pair<T, T>> &v) {
  std::sort(v.begin(), v.end());
  std::vector<std::pair<T, T>> ret;
  for (auto &&[l, r] : v) {
    if (ret.empty() || ret.back().second < l) {
      ret.emplace_back(l, r);
    } else if (ret.back().second < r) {
      ret.back().second = r;
    }
  }
  return ret;
}

template std::vector<std::pair<long long, long long>>
interval_union_inclusive<long long>(std::vector<std::pair<long long, long long>> &);

} // namespace cp

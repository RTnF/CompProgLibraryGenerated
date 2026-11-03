#pragma once
#include <vector>

namespace cp {

// Run-length encoding into caller-provided buffers (experiments/library/cpp/array/element_count.hpp `element_count`,
// `counts` of search_util.hpp and `char_count` of string/char_count.hpp, which return vector<pair<T, int>>): the k-th
// maximal run of equal values of v is stored as values[k] (its value) and counts[k] (its length). Returns the number of
// runs. Preconditions: v, values and counts are three distinct vectors, values.size() >= v.size() and
// counts.size() >= v.size(), v.size() < 2^31. Time O(n), extra space O(1).
template <class T>
inline int run_length(const std::vector<T> &v, std::vector<T> &values, std::vector<int> &counts) {
  int n = (int)v.size();
  if (n == 0) {
    return 0;
  }
  T pre = v[0];
  int cnt = 0;
  int m = 0;
  for (int i = 0; i < n; i++) {
    if (pre == v[i]) {
      cnt++;
    } else {
      values[m] = pre;
      counts[m] = cnt;
      m++;
      pre = v[i];
      cnt = 1;
    }
  }
  values[m] = pre;
  counts[m] = cnt;
  m++;
  return m;
}

template int run_length<long long>(const std::vector<long long> &, std::vector<long long> &, std::vector<int> &);

} // namespace cp

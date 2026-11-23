#pragma once
#include <string>
#include <utility>
#include <vector>

namespace cp {

// Run-length counts of a string (experiments/library/cpp/string/char_count.hpp `char_count`): splits s into its
// maximal runs of consecutive equal characters and returns (character, length) for each run in order. Equal
// characters that are not adjacent form separate runs; an empty s gives an empty result.
// Preconditions: s.size() <= INT_MAX (the length is stored in an int).
// Time O(n); extra space O(number of runs) for the result.
inline std::vector<std::pair<char, int>> char_count(const std::string &s) {
  std::vector<std::pair<char, int>> ret;
  int n = s.size();
  if (n == 0) {
    return ret;
  }
  char pre = s[0];
  int cnt = 0;
  for (int i = 0; i < n; i++) {
    if (pre == s[i]) {
      cnt++;
    } else {
      ret.emplace_back(pre, cnt);
      pre = s[i];
      cnt = 1;
    }
  }
  ret.emplace_back(pre, cnt);
  return ret;
}

} // namespace cp

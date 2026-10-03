#pragma once
#include "template/small_template.hpp"

// 文字、個数
vector<pair<char, int>> char_count(const string &s) {
  vector<pair<char, int>> ret;
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
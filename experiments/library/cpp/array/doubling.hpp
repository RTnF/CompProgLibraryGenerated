#pragma once
#include "template/small_template.hpp"

// ダブリング
// 値が[0, n)である配列のそれぞれで
// j = v[j] を 2**i 回繰り返した結果の2次元配列を作る
// O(n log kmax)
vector<vector<int>> doubling(vector<int> &v, uint64_t kmax) {
  // 0:0 1:1 2:2 4:3 8:4 ...
  assert(kmax > 0);
  int n = v.size();
  for (int i = 0; i < n; i++) {
    assert(0 <= v[i]);
    assert(v[i] < n);
  }
  int w = bit_width(kmax);
  vector<vector<int>> ret(w);
  ret[0].assign(v.begin(), v.end());
  for(int i = 1; i < w; i++){
    ret[i].reserve(n);
    for(int j = 0; j < n; j++){
      ret[i].emplace_back(ret[i-1][ret[i-1][j]]);
    }
  }
  return ret;
}
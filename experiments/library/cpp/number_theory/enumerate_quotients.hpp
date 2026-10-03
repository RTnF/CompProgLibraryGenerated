#pragma once
#include "template/small_template.hpp"

// 整数との商 floor(n / x) を列挙する
vector<ull> enumerate_quotients(ull n) {
  // N/k - N/(k+1) > 1
  // N/k(k+1) > 1
  // N > k(k+1)
  ull ok = 4294967295;
  ull ng = 0;
  ull k;
  while (ok - ng > 1) {
    k = (ok + ng) / 2;
    (k * (k + 1) >= n ? ok : ng) = k;
  }
  vector<ull> ret;
  ull p = n / ok;
  for (ull i = 1; i <= p; i++) {
    ret.emplace_back(i);
  }
  for (ull i = ok - 1; i >= 1; i--) {
    ret.emplace_back(n / i);
  }
  return ret;
}

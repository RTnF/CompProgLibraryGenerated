#define PROBLEM                                                                \
  "https://judge.yosupo.jp/problem/range_chmin_chmax_add_range_sum"
#include "segment_tree/segment_tree_beats_sum.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);

  int nn, Q;
  cin >> nn >> Q;
  vector<ll> a(nn);
  for (int i = 0; i < nn; i++) {
    cin >> a[i];
  }
  SegmentTreeBeatsSum segb(a);
  while (Q--) {
    int ty, l, r;
    cin >> ty >> l >> r;
    switch (ty) {
    case 0: {
      ll b;
      cin >> b;
      segb.chmin(l, r, b);
      break;
    }
    case 1: {
      ll b;
      cin >> b;
      segb.chmax(l, r, b);
      break;
    }
    case 2: {
      ll b;
      cin >> b;
      segb.add_val(l, r, b);
      break;
    }
    case 3: {
      cout << segb.calc_sum(l, r) << '\n';
      break;
    }
    }
  }
}
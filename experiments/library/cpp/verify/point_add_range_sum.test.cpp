#define PROBLEM "https://judge.yosupo.jp/problem/point_add_range_sum"
#include "algebraic_structure/group.hpp"
#include "segment_tree/segment_tree.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int N, Q;
  cin >> N >> Q;
  vector<GroupSum<ll>> a(N);
  for (int i = 0; i < N; i++) {
    ll x;
    cin >> x;
    a[i] = GroupSum(x);
  }
  SegmentTree<GroupSum<ll>> seg(a);
  while (Q--) {
    int cmd;
    ll x, y;
    cin >> cmd >> x >> y;
    if (cmd) {
      cout << seg.product(x, y).x() << '\n';
    } else {
      seg.set(x, seg.get(x).x() + y);
    }
  }
}
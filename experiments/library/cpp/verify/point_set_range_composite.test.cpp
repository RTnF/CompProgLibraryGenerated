#define PROBLEM "https://judge.yosupo.jp/problem/point_set_range_composite"
#include "algebraic_structure/group.hpp"
#include "modint/modint.hpp"
#include "segment_tree/segment_tree.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int N, Q;
  cin >> N >> Q;
  vector<GroupAffine<mint>> v(N);
  for (int i = 0; i < N; i++) {
    int a, b;
    cin >> a >> b;
    v[i] = {a, b};
  }
  SegmentTree<GroupAffine<mint>> sg(v);
  while (Q--) {
    int type;
    cin >> type;
    if (type) {
      int l, r;
      mint x;
      cin >> l >> r >> x;
      auto p = sg.product(l, r);
      cout << p.a() * x + p.b() << '\n';
    } else {
      int p;
      mint c, d;
      cin >> p >> c >> d;
      sg.set(p, {c, d});
    }
  }
}
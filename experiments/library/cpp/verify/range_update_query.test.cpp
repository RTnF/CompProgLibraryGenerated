#define PROBLEM                                                                \
  "https://onlinejudge.u-aizu.ac.jp/courses/library/3/DSL/all/DSL_2_D"
#include "algebraic_structure/monoid_lazy.hpp"
#include "segment_tree/lazy_segment_tree.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);

  int n, q;
  cin >> n >> q;
  vector<RangeSetRangeSum<int>::RangeSum> a(n, {(1ll << 31) - 1, 1});
  LazySegmentTree<RangeSetRangeSum<int>::RangeSum,
                  RangeSetRangeSum<int>::RangeSet>
      segtree(a);
  while (q--) {
    int qt;
    cin >> qt;
    if (qt == 0) {
      int l, r, x;
      cin >> l >> r >> x;
      r++;
      segtree.update(l, r, x);
    } else {
      int t;
      cin >> t;
      cout << segtree.get(t).x << '\n';
    }
  }
}
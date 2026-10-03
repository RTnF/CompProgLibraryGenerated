#define PROBLEM                                                                \
  "https://onlinejudge.u-aizu.ac.jp/courses/library/3/DSL/all/DSL_2_H"
#include "algebraic_structure/monoid_lazy.hpp"
#include "segment_tree/lazy_segment_tree.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);

  int n, q;
  cin >> n >> q;
  vector<RangeAddRangeMaxMin<int>::RangeMin> a(n, 0);
  LazySegmentTree<RangeAddRangeMaxMin<int>::RangeMin,
                  RangeAddRangeMaxMin<int>::RangeAdd>
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
      int l, r;
      cin >> l >> r;
      r++;
      cout << segtree.product(l, r).x << '\n';
    }
  }
}
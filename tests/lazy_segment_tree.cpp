#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/algebraic_structure/monoid_lazy.hpp"
#include "../library/segment_tree/lazy_segment_tree.hpp"
#include <cassert>
#include <random>
#include <vector>

// LazySegmentTree<M, F> against a plain vector, for the value/action families of monoid_lazy.hpp, including the
// binary searches with monotone and non-monotone predicates (the result must satisfy the two documented conditions).
template <class M> M fold(const std::vector<M> &v, int l, int r) {
  M x = M::e();
  for (int i = l; i < r; i++) x = op(x, v[i]);
  return x;
}

template <class M> bool same(const M &a, const M &b) { return a.x == b.x; }

template <class M, class F, class GenM, class GenF> void run(std::mt19937 &rng, GenM value, GenF action) {
  for (int round = 0; round < 200; round++) {
    int n = rng() % 34;
    std::vector<M> v;
    for (int i = 0; i < n; i++) v.push_back(value());
    bool fresh = round % 4 == 0;
    cp::LazySegmentTree<M, F> st = fresh ? cp::LazySegmentTree<M, F>(n) : cp::LazySegmentTree<M, F>(v);
    if (fresh) v.assign(n, M::e());
    for (int q = 0; q < 150; q++) {
      int t = rng() % 8;
      int l = rng() % (n + 1), r = l + rng() % (n - l + 1);
      if (t == 0 && n > 0) {
        int i = rng() % n;
        M x = value();
        st.set(i, x);
        v[i] = x;
      } else if (t == 1 && n > 0) {
        int i = rng() % n;
        assert(same(st.get(i), v[i]));
      } else if (t == 2) {
        assert(same(st.product(l, r), fold(v, l, r)));
        if (n > 0) assert(same(st.product_all(), fold(v, 0, n)));
      } else if (t == 3 && n > 0) {
        int i = rng() % n;
        F f = action();
        st.update(i, f);
        v[i] = f.apply(v[i]);
      } else if (t == 4 || t == 5) {
        F f = action();
        st.update(l, r, f);
        for (int i = l; i < r; i++) v[i] = f.apply(v[i]);
      } else {
        long long k = (long long)(rng() % 9) - 4;
        bool monotone = rng() % 2;
        auto g = [&](M x) {
          if (x.x == M::e().x) return true;
          return monotone ? x.x <= k : ((x.x % 3) + 3) % 3 != ((k % 3) + 3) % 3;
        };
        if (t == 6) {
          int res = st.search_prod_right(l, g);
          assert(l <= res && res <= n && g(fold(v, l, res)));
          assert(res == n || !g(fold(v, l, res + 1)));
        } else {
          int res = st.search_prod_left(r, g);
          assert(0 <= res && res <= r && g(fold(v, res, r)));
          assert(res == 0 || !g(fold(v, res - 1, r)));
        }
      }
    }
  }
}

int main() {
  std::mt19937 rng(20261120);
  using AS = cp::RangeAddRangeSum<long long>;
  run<AS::RangeSum, AS::RangeAdd>(rng, [&] { return AS::RangeSum((long long)(rng() % 7) - 3, 1); },
                                  [&] { return AS::RangeAdd((long long)(rng() % 5) - 2); });
  using SS = cp::RangeSetRangeSum<long long>;
  run<SS::RangeSum, SS::RangeSet>(rng, [&] { return SS::RangeSum((long long)(rng() % 7) - 3, 1); }, [&] {
    return rng() % 3 == 0 ? SS::RangeSet::id() : SS::RangeSet((long long)(rng() % 7) - 3);
  });
  // RangeAddRangeMaxMin is not used: push() applies the tags to padding leaves, whose value e() is the extreme
  // integer, and the addition overflows (docs/experiments_findings.md).
  using SM = cp::RangeSetRangeMaxMin<long long>;
  run<SM::RangeMax, SM::RangeSet>(rng, [&] { return SM::RangeMax((long long)(rng() % 21) - 10); }, [&] {
    return rng() % 3 == 0 ? SM::RangeSet::id() : SM::RangeSet((long long)(rng() % 21) - 10);
  });
  run<SM::RangeMin, SM::RangeSet>(rng, [&] { return SM::RangeMin((long long)(rng() % 21) - 10); }, [&] {
    return rng() % 3 == 0 ? SM::RangeSet::id() : SM::RangeSet((long long)(rng() % 21) - 10);
  });
  cp::LazySegmentTree<AS::RangeSum, AS::RangeAdd> empty;
  assert(empty.product(0, 0).x == 0);
  assert(empty.search_prod_right(0, [](AS::RangeSum) { return true; }) == 0);
  assert(empty.search_prod_left(0, [](AS::RangeSum) { return true; }) == 0);
  return 0;
}

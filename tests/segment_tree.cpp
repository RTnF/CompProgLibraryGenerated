#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/algebraic_structure/monoid.hpp"
#include "../library/segment_tree/segment_tree.hpp"
#include <cassert>
#include <random>
#include <vector>

// SegmentTree<M> against a direct fold, for the three monoids of monoid.hpp and the binary searches with monotone and
// non-monotone predicates (the result must satisfy the two documented conditions in every case).
template <class M> M fold(const std::vector<M> &v, int l, int r) {
  M x = M::e();
  for (int i = l; i < r; i++) x = op(x, v[i]);
  return x;
}

template <class M, class Gen> void run(std::mt19937 &rng, Gen value) {
  for (int round = 0; round < 300; round++) {
    int n = rng() % 40;
    std::vector<M> v(n);
    for (auto &x : v) x = M(value());
    cp::SegmentTree<M> st = (round % 3 == 0) ? cp::SegmentTree<M>(n) : cp::SegmentTree<M>(v);
    if (round % 3 == 0) v.assign(n, M::e());
    for (int q = 0; q < 200; q++) {
      int t = rng() % 5;
      if (t == 0 && n > 0) {
        int i = rng() % n;
        M x(value());
        st.set(i, x);
        v[i] = x;
      } else if (t == 1 && n > 0) {
        int i = rng() % n;
        assert(st.get(i).x == v[i].x);
      } else if (t == 2) {
        int l = rng() % (n + 1), r = l + rng() % (n - l + 1);
        assert(st.product(l, r).x == fold(v, l, r).x);
        if (n > 0) assert(st.product_all().x == fold(v, 0, n).x);
      } else {
        long long k = (long long)(rng() % 7) - 3;
        bool monotone = rng() % 2;
        auto f = [&](M x) {
          if (x.x == M::e().x) return true;
          return monotone ? x.x <= k : (x.x % 3 + 3) % 3 != (k + 3) % 3;
        };
        if (t == 3) {
          int l = rng() % (n + 1);
          int r = st.search_prod_right(l, f);
          assert(l <= r && r <= n && f(fold(v, l, r)));
          assert(r == n || !f(fold(v, l, r + 1)));
        } else {
          int r = rng() % (n + 1);
          int l = st.search_prod_left(r, f);
          assert(0 <= l && l <= r && f(fold(v, l, r)));
          assert(l == 0 || !f(fold(v, l - 1, r)));
        }
      }
    }
  }
}

int main() {
  std::mt19937 rng(20261119);
  run<cp::MonoidMax<long long>>(rng, [&] { return (long long)(rng() % 21) - 10; });
  run<cp::MonoidMin<long long>>(rng, [&] { return (long long)(rng() % 21) - 10; });
  run<cp::MonoidMul<long long>>(rng, [&] { return (long long)(rng() % 3) - 1; });
  cp::SegmentTree<cp::MonoidMax<long long>> empty;
  assert(empty.product(0, 0).x == cp::MonoidMax<long long>::e().x);
  assert(empty.search_prod_right(0, [](cp::MonoidMax<long long>) { return true; }) == 0);
  assert(empty.search_prod_left(0, [](cp::MonoidMax<long long>) { return true; }) == 0);
  return 0;
}

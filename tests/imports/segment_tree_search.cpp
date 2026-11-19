// search_prod_right / search_prod_left of the public SegmentTree with MonoidMax, compared with the generated Lean
// model by tests/test_segment_tree_search.py (tests/lean/segment_tree_search.lean runs the same cases).
#include "../../library/algebraic_structure/monoid.hpp"
#include "../../library/segment_tree/segment_tree.hpp"
#include <iostream>
#include <vector>

using M = cp::MonoidMax<long long>;
unsigned long long state = 1;
long long next(long long m) {
  state = (state * 1103515245ULL + 12345ULL) % 2147483648ULL;
  return (long long)(state % (unsigned long long)m);
}

int main() {
  for (int round = 0; round < 200; round++) {
    int n = (int)next(30);
    std::vector<M> v;
    for (int i = 0; i < n; i++) v.push_back(M(next(21) - 10));
    cp::SegmentTree<M> st(v);
    for (int q = 0; q < 20; q++) {
      long long k = next(7) - 3;
      bool mono = next(2) == 1;
      auto f = [&](M x) {
        if (x.x == M::e().x) return true;
        return mono ? x.x <= k : (x.x % 3 + 3) % 3 != (k + 3) % 3;
      };
      int a = (int)next(n + 1);
      std::cout << st.search_prod_right(a, f) << ' ' << st.search_prod_left(a, f) << '\n';
    }
  }
}

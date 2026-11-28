#pragma once

#include <algorithm>
#include <cassert>
#include <numeric>
#include <random>
#include <type_traits>
#include <vector>

template <class Set>
void check_disjoint_set() {
  static_assert(std::is_convertible_v<int, Set>);
  Set empty = 0;
  assert(empty.getNum() == 0);

  Set balanced = 16;
  for (int width = 1; width < 16; width *= 2) {
    for (int a = 0; a < 16; a += 2 * width) {
      assert(balanced.unite(a, a + width) == a);
    }
  }
  assert(balanced.root(15) == 0 && balanced.size(15) == 16);
  assert(balanced.unite(15, 0) == 0 && balanced.getNum() == 1);

  Set original = 4;
  assert(original.unite(0, 1) == 0);
  auto copy = original;
  assert(copy.unite(2, 1) == 0 && copy.size(2) == 3 && copy.getNum() == 2);
  assert(!original.same(1, 2) && original.size(0) == 2 && original.getNum() == 3);

  for (int n : {1, 2, 29, 128}) {
    Set set = n;
    std::vector<int> roots(n);
    std::iota(roots.begin(), roots.end(), 0);
    auto size = [&](int root) { return std::count(roots.begin(), roots.end(), root); };
    int groups = n;
    std::mt19937 rng(104);
    for (int step = 0; step < 2000; ++step) {
      int a = static_cast<int>(rng() % n);
      int b = static_cast<int>(rng() % n);
      int left = roots[a], right = roots[b];
      switch (rng() % 4) {
      case 0:
        if (size(left) < size(right)) {
          std::swap(left, right);
        }
        assert(set.unite(a, b) == left);
        if (left != right) {
          std::replace(roots.begin(), roots.end(), right, left);
          --groups;
        }
        break;
      case 1:
        assert(set.same(a, b) == (left == right));
        break;
      case 2:
        assert(set.root(a) == left);
        break;
      default:
        assert(set.size(a) == size(left));
        break;
      }
      assert(set.getNum() == groups);
    }
  }
}

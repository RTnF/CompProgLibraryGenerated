#pragma once
#include <vector>

namespace cp {

// The root of a tree given by a parent array without an explicit root (the root search of the constructor
// Tree(vector<int> &parent) in experiments/library/cpp/tree/tree.hpp): the last index i with parent[i] == i or
// parent[i] < 0, or -1 if there is none (the original then fails an assert). Differences: the test `parent[i] == i ||
// parent[i] < 0` is written as two nested conditions, and the missing-root case is reported by the return value -1
// instead of the assert.
// Preconditions: n >= 0, parent.size() >= n. Time O(n), extra space O(1).
inline int tree_find_root(const std::vector<int> &parent, int n) {
  int r = -1;
  for (int i = 0; i < n; i++) {
    int p = parent[i];
    if (p == i) {
      r = i;
    } else {
      if (p < 0) {
        r = i;
      }
    }
  }
  return r;
}

} // namespace cp

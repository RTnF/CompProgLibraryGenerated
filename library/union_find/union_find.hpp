#pragma once
#include <cassert>
#include <vector>

namespace cp {

// Disjoint set union (union-find) over the elements 0 .. n-1 (experiments/library/cpp/union_find/union_find.hpp,
// UnionFind) with union by size.
//
// Representation: ps has n + 1 entries. For i < n, ps[i] < 0 marks a root (its value is minus the size of its
// tree) and ps[i] >= 0 is the parent of i. The last entry ps[n] = -1 - (number of trees) is a sentinel root that no
// index below n reaches; it holds the tree count. The original keeps it in the separate field _num_groups.
// The current public proofs use this vector representation; a candidate restoring the separate fields and
// compression in every method is in experiments/verification/data_structure/union_find.hpp, pending full call proofs.
//
// unite(a, b)   joins the trees of a and b by size and returns the root of the result; time O(log n).
// same(a, b)    whether a and b are in one tree; time O(log n).
// root(a)       the root of the tree of a, compressing the path of a to the root; amortised near-constant time.
// size(a)       the number of elements of the tree of a; time O(log n).
// num_groups()  the number of trees; time O(1).
// Differences from the original: the tree count lives in ps[n]; unite, same and size find roots without compressing
// the path (the original compresses in every call; the height is at most log2 n by union by size, so a call costs
// O(log n) worst case, but the amortised bound of the original is not claimed). Argument asserts retain the
// original domain 0 <= a, b < n. The sentinel representation still requires n < 2^31 - 1.
class UnionFind {
  std::vector<int> ps;
  int find_root(int a) const {
    while (ps[a] >= 0) {
      a = ps[a];
    }
    return a;
  }

public:
  UnionFind() : ps(1, -1) {}
  UnionFind(int n) : ps(n + 1, -1) {
    assert(0 <= n);
    ps[n] = -1 - n;
  }
  int unite(int a, int b) {
    assert(0 <= a);
    assert(a < (int)ps.size() - 1);
    assert(0 <= b);
    assert(b < (int)ps.size() - 1);
    int x = find_root(a);
    int y = find_root(b);
    if (x == y) {
      return x;
    }
    if (0 - ps[x] < 0 - ps[y]) {
      int t = x;
      x = y;
      y = t;
    }
    ps[x] = ps[x] + ps[y];
    ps[y] = x;
    int last = (int)ps.size() - 1;
    ps[last] = ps[last] + 1;
    return x;
  }
  bool same(int a, int b) const {
    assert(0 <= a);
    assert(a < (int)ps.size() - 1);
    assert(0 <= b);
    assert(b < (int)ps.size() - 1);
    int x = find_root(a);
    int y = find_root(b);
    return x == y;
  }
  int root(int a) {
    assert(0 <= a);
    assert(a < (int)ps.size() - 1);
    int r = a;
    while (ps[r] >= 0) {
      r = ps[r];
    }
    while (a != r) {
      int next = ps[a];
      ps[a] = r;
      a = next;
    }
    return r;
  }
  int size(int a) const {
    assert(0 <= a);
    assert(a < (int)ps.size() - 1);
    while (ps[a] >= 0) {
      a = ps[a];
    }
    return 0 - ps[a];
  }
  int num_groups() const {
    int last = (int)ps.size() - 1;
    return -1 - ps[last];
  }
};

} // namespace cp

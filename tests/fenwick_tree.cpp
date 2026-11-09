#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/segment_tree/fenwick_tree.hpp"
#include <climits>
#include <random>
#include <vector>

// Preserve the original interface: operator+ is deliberately unavailable.
struct AdditiveWithoutPlus {
    long long value;
    AdditiveWithoutPlus(long long value = 0) : value(value) {}
    AdditiveWithoutPlus &operator+=(const AdditiveWithoutPlus &other) {
        value += other.value;
        return *this;
    }
    friend AdditiveWithoutPlus operator-(AdditiveWithoutPlus left, AdditiveWithoutPlus right) {
        return AdditiveWithoutPlus(left.value - right.value);
    }
};

namespace original {
// Verbatim copy of experiments/library/cpp/segment_tree/binary_indexed_tree.hpp (the test is compiled without -I, so the
// header cannot be included by its own relative include).
using std::vector;
using ll = long long;
/**
 * @brief Binary Indexed Tree (Fenwick Tree)
 */
template <class T = ll> class BinaryIndexedTree {
  vector<T> tree; // 1-indexed
public:
  BinaryIndexedTree() {}
  BinaryIndexedTree(int n) : tree(n + 1) {}
  BinaryIndexedTree(const vector<T> &v) : tree(v.size() + 1) {
    for (int i = 0; i < (int)v.size(); i++) {
      tree[i + 1] = v[i];
    }
    for (int i = 1; i < (int)v.size(); i++) {
      if (i + (i & -i) < (int)tree.size()) {
        tree[i + (i & -i)] += tree[i];
      }
    }
  }
  // sum of A[0, r)
  T sum(int r) const {
    T s = 0;
    for (; r > 0; r -= (r & -r)) {
      s += tree[r];
    }
    return s;
  }
  // sum of A[l, r)
  T sum(int l, int r) const { return sum(r) - sum(l); }
  // A[i] += val
  void add(int i, T val) {
    i++;
    for (; i < (int)tree.size(); i += (i & -i)) {
      tree[i] += val;
    }
  }
};
} // namespace original

// The original BinaryIndexedTree and the published FenwickTree (also reachable under the original name) answer every
// query identically over random constructions, updates and queries.
void check_against_original() {
    std::mt19937_64 random(20261110);
    for (int round = 0; round < 300; ++round) {
        const int n = static_cast<int>(random() % 40);
        std::vector<long long> v(n);
        for (auto &x : v) x = static_cast<long long>(random() % 2001) - 1000;
        original::BinaryIndexedTree<long long> expected(v);
        cp::BinaryIndexedTree<long long> published(v);
        cp::FenwickTree<long long> renamed(v);
        for (int step = 0; step < 60; ++step) {
            if (n > 0 && random() % 2 == 0) {
                const int i = static_cast<int>(random() % n);
                const long long delta = static_cast<long long>(random() % 2001) - 1000;
                expected.add(i, delta);
                published.add(i, delta);
                renamed.add(i, delta);
            }
            const int l = static_cast<int>(random() % (n + 1));
            const int r = l + static_cast<int>(random() % (n - l + 1));
            assert(published.sum(r) == expected.sum(r) && renamed.sum(r) == expected.sum(r));
            assert(published.sum(l, r) == expected.sum(l, r) && renamed.sum(l, r) == expected.sum(l, r));
        }
    }
    original::BinaryIndexedTree<long long> empty_expected(7);
    cp::BinaryIndexedTree<long long> empty_published(7);
    for (int r = 0; r <= 7; ++r) assert(empty_published.sum(r) == empty_expected.sum(r));
}

int main() {
    check_against_original();
    cp::FenwickTree<AdditiveWithoutPlus> genericEmpty;
    assert(genericEmpty.sum(0).value == 0);
    cp::FenwickTree<AdditiveWithoutPlus> genericZeros(3);
    assert(genericZeros.sum(3).value == 0);
    cp::FenwickTree<AdditiveWithoutPlus> genericBuilt(std::vector<AdditiveWithoutPlus>{1, 2, 3});
    assert(genericBuilt.sum(3).value == 6);
    genericBuilt.add(1, 4);
    assert(genericBuilt.sum(3).value == 10);
    assert(genericBuilt.sum(1, 3).value == 9);

    std::mt19937_64 random(20261008);
    // point additions and prefix sums against a plain array
    for (int n = 0; n <= 70; ++n) {
        std::vector<long long> a(n, 0);
        cp::FenwickTree<long long> tree(n);
        for (int step = 0; step < 300; ++step) {
            if (n > 0 && random() % 2 == 0) {
                const int i = static_cast<int>(random() % n);
                const long long val = static_cast<long long>(random() % 2001) - 1000;
                a[i] += val;
                tree.add(i, val);
            }
            const int r = static_cast<int>(random() % (n + 1));
            long long expected = 0;
            for (int j = 0; j < r; ++j) expected += a[j];
            assert(tree.sum(r) == expected);
        }
        for (int r = 0; r <= n; ++r) {
            long long expected = 0;
            for (int j = 0; j < r; ++j) expected += a[j];
            assert(tree.sum(r) == expected);
        }
    }
    // An index past the end changes nothing; large values.
    cp::FenwickTree<long long> small(7);
    small.add(100, 5);
    for (int r = 0; r < 8; ++r) assert(small.sum(r) == 0);
    small.add(0, LLONG_MAX / 4);
    small.add(6, LLONG_MAX / 4);
    assert(small.sum(7) == LLONG_MAX / 4 * 2);
    // A 2^20 element tree.
    cp::FenwickTree<long long> big(1 << 20);
    for (int i = 0; i < (1 << 20); i += 4099) big.add(i, i);
    long long total = 0;
    for (int i = 0; i < (1 << 20); i += 4099) total += i;
    assert(big.sum(1 << 20) == total);
    // range sums, and the reversed range gives the negated sum
    for (int n : {1, 2, 3, 7, 8, 100, 300}) {
        std::vector<long long> a(n);
        cp::FenwickTree<long long> tree(n);
        for (int i = 0; i < n; ++i) {
            a[i] = static_cast<long long>(random() % 2001) - 1000;
            tree.add(i, a[i]);
        }
        for (int l = 0; l <= n; ++l)
            for (int r = l; r <= n; ++r) {
                long long expected = 0;
                for (int i = l; i < r; ++i) expected += a[i];
                assert(tree.sum(l, r) == expected);
                assert(tree.sum(r, l) == -expected);
            }
    }
    // the constructor from a vector equals the tree made by point additions, for sizes around powers of two
    for (int n : {0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 100, 1000, 4097}) {
        std::vector<long long> a(n);
        for (int i = 0; i < n; ++i) a[i] = static_cast<long long>(random() % 2001) - 1000;
        cp::FenwickTree<long long> built(a);
        cp::FenwickTree<long long> added(n);
        for (int i = 0; i < n; ++i) added.add(i, a[i]);
        long long sum = 0;
        for (int r = 0; r <= n; ++r) {
            assert(built.sum(r) == sum);
            assert(added.sum(r) == sum);
            if (r < n) sum += a[r];
        }
        for (int l = 0; l <= n; l += 1 + n / 20)
            for (int r = l; r <= n; r += 1 + n / 20) assert(built.sum(l, r) == added.sum(l, r));
    }
    // the default-constructed tree is empty: no element can be added
    cp::FenwickTree<long long> empty;
    empty.add(0, 5);
    // the element type is a template parameter
    cp::FenwickTree<int> narrow(std::vector<int>{3, 1, 4, 1, 5, 9, 2, 6});
    assert(narrow.sum(8) == 31 && narrow.sum(2, 5) == 10);
    cp::FenwickTree<unsigned long long> wide(std::vector<unsigned long long>{1ull << 63, 1ull << 62});
    assert(wide.sum(2) == (3ull << 62));
    return 0;
}

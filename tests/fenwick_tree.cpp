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

int main() {
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

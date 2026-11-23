#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/array/sort_util.hpp"
#include <algorithm>
#include <climits>
#include <numeric>
#include <random>
#include <string>
#include <vector>

// Independent oracle: for every target p, search for the position holding p.
std::vector<int> oracle(const std::vector<int> &v) {
    const int n = static_cast<int>(v.size());
    std::vector<int> result(n, -2);
    for (int p = 0; p < n; ++p)
        for (int j = 0; j < n; ++j)
            if (v[j] == p) result[p] = j;
    return result;
}

void test_inv_perm() {
    // Every permutation of size at most 7.
    for (int n = 0; n <= 7; ++n) {
        std::vector<int> v(n);
        std::iota(v.begin(), v.end(), 0);
        do {
            const auto inv = cp::inv_perm(v);
            assert(inv == oracle(v));
            // The inverse of the inverse is the original.
            assert(cp::inv_perm(inv) == v);
        } while (std::next_permutation(v.begin(), v.end()));
    }
    // Larger random permutations.
    std::mt19937 random(20261008);
    for (int trial = 0; trial < 50; ++trial) {
        const int n = 1 + static_cast<int>(random() % 3000);
        std::vector<int> v(n);
        std::iota(v.begin(), v.end(), 0);
        std::shuffle(v.begin(), v.end(), random);
        const auto inv = cp::inv_perm(v);
        assert(static_cast<int>(inv.size()) == n);
        for (int j = 0; j < n; ++j) assert(inv[v[j]] == j);
    }
    // The example from the header comment.
    assert((cp::inv_perm(std::vector<int>{2, 4, 0, 1, 3}) == std::vector<int>{2, 3, 0, 4, 1}));
}

void test_compress() {
    std::mt19937_64 random(20261023);
    for (int n = 0; n <= 60; ++n) {
        for (int round = 0; round < 4; ++round) {
            std::vector<long long> x(n);
            for (long long &v : x) v = static_cast<long long>(random() % 15) - 7;
            const int offset = static_cast<int>(random() % 7) - 3;
            std::vector<long long> unzip(n, 99);
            const std::vector<long long> cmp = cp::compress(x, unzip, offset);
            std::vector<long long> expected = x;
            std::sort(expected.begin(), expected.end());
            expected.erase(std::unique(expected.begin(), expected.end()), expected.end());
            assert(unzip == expected);
            assert((int)cmp.size() == n);
            for (int i = 0; i < n; ++i) {
                const long long k = cmp[i] - offset;
                assert(0 <= k && k < (long long)unzip.size());
                assert(unzip[k] == x[i]);
            }
            // the overload without unzip, with and without the default offset
            assert(cp::compress(x, offset) == cmp);
            std::vector<long long> u2;
            assert(cp::compress(x) == cp::compress(x, u2, 0));
        }
    }
    // the extreme values of long long; the example from the header comment
    std::vector<long long> x = {LLONG_MAX, 0, LLONG_MIN, -1, LLONG_MAX, LLONG_MIN};
    std::vector<long long> unzip;
    assert((cp::compress(x, unzip) == std::vector<long long>{3, 2, 0, 1, 3, 0}));
    assert((unzip == std::vector<long long>{LLONG_MIN, -1, 0, LLONG_MAX}));
    assert((cp::compress(std::vector<long long>{3, 3, 1, 5, 2}, 10) == std::vector<long long>{12, 12, 10, 13, 11}));
    // the element type is a template parameter
    {
        std::vector<int> x = {5, 3, 5, 1}, u;
        const std::vector<int> id = cp::compress(x, u);
        assert(u.size() == 3 && u[0] == 1 && id[0] == 2 && id[1] == 1 && id[3] == 0);
    }
}

// Independent oracle of the stable index sort: insertion sort of the indices.
std::vector<int> arg_oracle(const std::vector<long long> &v) {
    std::vector<int> a;
    for (int i = 0; i < (int)v.size(); ++i) {
        int k = (int)a.size();
        while (k > 0 && v[i] < v[a[k - 1]]) --k;
        a.insert(a.begin() + k, i);
    }
    return a;
}

void test_arg_sort() {
    assert((cp::arg_sort(std::vector<long long>{3, 3, 1, 5, 2}) == std::vector<int>{2, 4, 0, 1, 3}));
    assert((cp::inv_arg_sort(std::vector<long long>{3, 3, 1, 5, 2}) == std::vector<int>{2, 3, 0, 4, 1}));
    assert(cp::arg_sort(std::vector<long long>{}).empty());
    std::mt19937_64 random(20261123);
    for (int n = 0; n <= 200; ++n) {
        std::vector<long long> v(n);
        const int range = n % 5 + 1;
        for (long long &x : v) x = (n % 2 ? LLONG_MIN : 0) + static_cast<long long>(random() % range);
        const auto a = cp::arg_sort(v);
        assert(a == arg_oracle(v));
        const auto b = cp::inv_arg_sort(v);
        for (int j = 0; j < n; ++j) assert(b[a[j]] == j);
    }
    // other element types
    assert((cp::arg_sort(std::vector<std::string>{"b", "a", "b", ""}) == std::vector<int>{3, 1, 0, 2}));
    assert((cp::arg_sort(std::vector<double>{0.5, -1.0, 0.5}) == std::vector<int>{1, 0, 2}));
}

void test_sort_vector() {
    std::mt19937_64 random(20261016);
    for (int n = 0; n <= 40; ++n) {
        std::vector<long long> x(n);
        for (long long &v : x) v = static_cast<long long>(random() % 21) - 10;
        std::vector<long long> expected = x;
        std::sort(expected.begin(), expected.end());
        cp::sort_vector(x);
        assert(x == expected);
    }
    std::vector<long long> extremes = {LLONG_MAX, 0, LLONG_MIN, -1, 1, LLONG_MIN, LLONG_MAX};
    cp::sort_vector(extremes);
    assert(std::is_sorted(extremes.begin(), extremes.end()));
    assert(extremes.front() == LLONG_MIN && extremes.back() == LLONG_MAX);
    std::vector<long long> big(200000);
    for (long long &v : big) v = static_cast<long long>(random());
    cp::sort_vector(big);
    assert(std::is_sorted(big.begin(), big.end()));
}

void test_dedup_vector() {
    std::mt19937_64 random(20261017);
    for (int n = 0; n <= 40; ++n) {
        std::vector<long long> x(n);
        for (long long &v : x) v = static_cast<long long>(random() % 5) - 2;
        // arbitrary (unsorted) input: adjacent runs collapse
        std::vector<long long> expected;
        for (long long v : x)
            if (expected.empty() || expected.back() != v) expected.push_back(v);
        std::vector<long long> y = x;
        cp::dedup_vector(y);
        assert(y == expected);
        // sorted input: strictly increasing, same set of values
        std::sort(x.begin(), x.end());
        std::vector<long long> sorted = x;
        cp::dedup_vector(x);
        assert(std::adjacent_find(x.begin(), x.end(), std::greater_equal<long long>()) == x.end());
        for (long long v : sorted) assert(std::binary_search(x.begin(), x.end(), v));
    }
    std::vector<long long> extremes = {LLONG_MIN, LLONG_MIN, LLONG_MAX, LLONG_MAX, LLONG_MAX};
    cp::dedup_vector(extremes);
    assert((extremes == std::vector<long long>{LLONG_MIN, LLONG_MAX}));
    std::vector<long long> empty;
    cp::dedup_vector(empty);
    assert(empty.empty());
}

int main() {
    test_inv_perm();
    test_compress();
    test_arg_sort();
    test_sort_vector();
    test_dedup_vector();
    return 0;
}

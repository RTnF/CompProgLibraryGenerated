#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/array/search_util.hpp"
#include <algorithm>
#include <climits>
#include <cstdint>
#include <random>
#include <vector>

// Independent oracle: std::count over the half-open iterator range (empty when begin >= end).
int oracle(const std::vector<int> &v, int value, int begin, int end) {
    if (end == -1) end = static_cast<int>(v.size());
    if (begin >= end) return 0;
    return static_cast<int>(std::count(v.begin() + begin, v.begin() + end, value));
}

void test_count() {
    // Every vector over {0,1,2} of length at most 6, every value and every valid range.
    for (int n = 0; n <= 6; ++n) {
        std::vector<int> v(n, 0);
        for (;;) {
            for (int value = -1; value <= 3; ++value) {
                for (int b = 0; b <= n; ++b) {
                    for (int e = -1; e <= n; ++e) {
                        assert(cp::count(v, value, b, e) == oracle(v, value, b, e));
                    }
                }
            }
            int index = 0;
            while (index < n && ++v[index] == 3) v[index++] = 0;
            if (index == n) break;
        }
    }
    // Extreme values and a larger random vector.
    std::mt19937 random(20261008);
    std::vector<int> big(5000);
    for (int &x : big) x = static_cast<int>(random() % 7) - 3;
    big[17] = INT_MIN;
    big[18] = INT_MAX;
    for (int trial = 0; trial < 2000; ++trial) {
        const int value = trial % 9 == 0 ? INT_MIN : trial % 9 == 1 ? INT_MAX : static_cast<int>(random() % 9) - 4;
        int b = static_cast<int>(random() % 5001);
        int e = trial % 5 == 0 ? -1 : static_cast<int>(random() % 5001);
        assert(cp::count(big, value, b, e) == oracle(big, value, b, e));
    }
    assert(cp::count(big, INT_MIN, 0, -1) >= 1);
    assert(cp::count(big, INT_MAX, 18, 19) == 1);
    assert(cp::count(big, INT_MAX, 19, 18) == 0);
}

void test_lower_bound_index() {
    std::mt19937_64 random(20261018);
    for (int n = 0; n <= 40; ++n) {
        for (int round = 0; round < 20; ++round) {
            std::vector<long long> a(n);
            for (long long &v : a) v = static_cast<long long>(random() % 15) - 7;
            std::sort(a.begin(), a.end());
            for (long long x = -9; x <= 9; ++x) {
                int expected = static_cast<int>(std::lower_bound(a.begin(), a.end(), x) - a.begin());
                assert(cp::lower_bound_index<long long>(a, x) == expected);
            }
        }
    }
    std::vector<long long> extremes = {LLONG_MIN, LLONG_MIN, -1, 0, 0, LLONG_MAX};
    assert(cp::lower_bound_index<long long>(extremes, LLONG_MIN) == 0);
    assert(cp::lower_bound_index<long long>(extremes, LLONG_MIN + 1) == 2);
    assert(cp::lower_bound_index<long long>(extremes, 0) == 3);
    assert(cp::lower_bound_index<long long>(extremes, 1) == 5);
    assert(cp::lower_bound_index<long long>(extremes, LLONG_MAX) == 5);
    std::vector<long long> empty;
    assert(cp::lower_bound_index<long long>(empty, 5) == 0);
    std::vector<long long> big(1000000);
    for (long long &v : big) v = static_cast<long long>(random() >> 1);
    std::sort(big.begin(), big.end());
    for (int i = 0; i < 1000; ++i) {
        long long x = static_cast<long long>(random() >> 1);
        assert(cp::lower_bound_index<long long>(big, x) == static_cast<int>(std::lower_bound(big.begin(), big.end(), x) - big.begin()));
    }
}

int main() {
    test_count();
    test_lower_bound_index();
    // the default arguments of the original `count`
    {
        std::vector<int> v = {1, 2, 1, 3, 1};
        assert(cp::count(v, 1) == 3);
        assert(cp::count(v, 1, 1) == 2);
        assert(cp::count(v, 1, 0, 3) == 2);
        assert(cp::count(std::vector<double>{0.5, 0.5, 2.0}, 0.5) == 2);
    }
    return 0;
}

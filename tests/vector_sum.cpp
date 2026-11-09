#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/array/vector_sum.hpp"
#include <climits>
#include <numeric>
#include <random>
#include <vector>

int main() {
    // Every vector over {-2,0,3} of length at most 7 against std::accumulate.
    const long long values[3] = {-2, 0, 3};
    for (int n = 0; n <= 7; ++n) {
        std::vector<int> digits(n, 0);
        for (;;) {
            std::vector<long long> v(n);
            for (int i = 0; i < n; ++i) v[i] = values[digits[i]];
            assert(cp::vector_sum(v) == std::accumulate(v.begin(), v.end(), 0LL));
            int index = 0;
            while (index < n && ++digits[index] == 3) digits[index++] = 0;
            if (index == n) break;
        }
    }
    assert(cp::vector_sum(std::vector<long long>()) == 0);
    // Extreme values whose partial sums stay in range.
    assert(cp::vector_sum(std::vector<long long>{LLONG_MAX, -1, 1, LLONG_MIN}) == -1);
    assert(cp::vector_sum(std::vector<long long>{LLONG_MIN, LLONG_MAX}) == -1);
    assert(cp::vector_sum(std::vector<long long>{LLONG_MIN}) == LLONG_MIN);
    std::mt19937_64 random(20261008);
    std::vector<long long> big(100000);
    for (long long &x : big) x = static_cast<long long>(random() % 2000001) - 1000000;
    assert(cp::vector_sum(big) == std::accumulate(big.begin(), big.end(), 0LL));
    // the element type is a template parameter
    assert(cp::vector_sum(std::vector<int>{3, 1, 4}) == 8);
    assert(cp::vector_sum(std::vector<double>{0.5, 1.5}) == 2.0);
    return 0;
}

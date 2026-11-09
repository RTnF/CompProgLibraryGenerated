#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/array/vector_max.hpp"
#include <algorithm>
#include <climits>
#include <random>
#include <vector>

int main() {
    // Every vector over {-2,0,3} of length 1..7 against std::max_element.
    const long long values[3] = {-2, 0, 3};
    for (int n = 1; n <= 7; ++n) {
        std::vector<int> digits(n, 0);
        for (;;) {
            std::vector<long long> v(n);
            for (int i = 0; i < n; ++i) v[i] = values[digits[i]];
            assert(cp::vector_max(v) == *std::max_element(v.begin(), v.end()));
            int index = 0;
            while (index < n && ++digits[index] == 3) digits[index++] = 0;
            if (index == n) break;
        }
    }
    assert(cp::vector_max(std::vector<long long>{LLONG_MIN}) == LLONG_MIN);
    assert(cp::vector_max(std::vector<long long>{LLONG_MIN, LLONG_MAX, 0}) == LLONG_MAX);
    assert(cp::vector_max(std::vector<long long>{LLONG_MAX, LLONG_MIN}) == LLONG_MAX);
    std::mt19937_64 random(20261008);
    std::vector<long long> big(100000);
    for (long long &x : big) x = static_cast<long long>(random());
    assert(cp::vector_max(big) == *std::max_element(big.begin(), big.end()));
    // the element type is a template parameter
    assert(cp::vector_max(std::vector<int>{3, 1, 4}) == 4);
    assert(cp::vector_max(std::vector<double>{0.5, -1.5}) == 0.5);
    return 0;
}

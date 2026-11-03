#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/vector_min.hpp"
#include <algorithm>
#include <climits>
#include <random>
#include <vector>

int main() {
    // Every vector over {-2,0,3} of length 1..7 against std::min_element.
    const long long values[3] = {-2, 0, 3};
    for (int n = 1; n <= 7; ++n) {
        std::vector<int> digits(n, 0);
        for (;;) {
            std::vector<long long> v(n);
            for (int i = 0; i < n; ++i) v[i] = values[digits[i]];
            assert(cp::vector_min(v) == *std::min_element(v.begin(), v.end()));
            int index = 0;
            while (index < n && ++digits[index] == 3) digits[index++] = 0;
            if (index == n) break;
        }
    }
    assert(cp::vector_min(std::vector<long long>{LLONG_MIN}) == LLONG_MIN);
    assert(cp::vector_min(std::vector<long long>{LLONG_MIN, LLONG_MAX, 0}) == LLONG_MIN);
    assert(cp::vector_min(std::vector<long long>{LLONG_MAX, LLONG_MIN}) == LLONG_MIN);
    std::mt19937_64 random(20261008);
    std::vector<long long> big(100000);
    for (long long &x : big) x = static_cast<long long>(random());
    assert(cp::vector_min(big) == *std::min_element(big.begin(), big.end()));
    // the element type is a template parameter
    assert(cp::vector_min(std::vector<int>{3, 1, 4}) == 1);
    assert(cp::vector_min(std::vector<double>{0.5, -1.5}) == -1.5);
    return 0;
}

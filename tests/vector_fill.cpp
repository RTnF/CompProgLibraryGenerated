#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/array/vector_fill.hpp"
#include <climits>
#include <random>
#include <vector>

int main() {
    const long long values[] = {LLONG_MIN, -1, 0, 1, 7, LLONG_MAX};
    for (int n = 0; n <= 20; ++n) {
        for (long long value : values) {
            std::vector<long long> x(n);
            for (int i = 0; i < n; ++i) x[i] = i * 31 - 5;
            cp::vector_fill<long long>(x, value);
            assert(static_cast<int>(x.size()) == n);
            for (long long y : x) assert(y == value);
        }
    }
    std::mt19937_64 random(20261008);
    std::vector<long long> big(100000);
    for (long long &x : big) x = static_cast<long long>(random());
    cp::vector_fill<long long>(big, -12345);
    for (long long y : big) assert(y == -12345);
    // the element type is a template parameter
    std::vector<int> narrow(3, 0);
    cp::vector_fill<int>(narrow, 7);
    for (int y : narrow) assert(y == 7);
    return 0;
}

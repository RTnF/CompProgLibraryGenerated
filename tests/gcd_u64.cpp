#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number_theory/gcd_u64.hpp"
#include <climits>
#include <numeric>
#include <random>

int main() {
    std::mt19937_64 random(20261019);
    for (unsigned long long a = 0; a <= 60; ++a)
        for (unsigned long long b = 0; b <= 60; ++b) assert(cp::gcd_u64(a, b) == std::gcd(a, b));
    const unsigned long long big = ULLONG_MAX;
    assert(cp::gcd_u64(big, big) == big);
    assert(cp::gcd_u64(big, 0) == big);
    assert(cp::gcd_u64(0, big) == big);
    assert(cp::gcd_u64(big, 1) == 1);
    // consecutive Fibonacci numbers are the worst case (F93 < 2^64 < F94)
    unsigned long long f1 = 1, f2 = 1;
    for (int i = 0; i < 90; ++i) {
        unsigned long long f3 = f1 + f2;
        f1 = f2;
        f2 = f3;
    }
    assert(cp::gcd_u64(f2, f1) == 1);
    for (int i = 0; i < 200000; ++i) {
        unsigned long long g = random() % 1000 + 1, x = random() >> 20, y = random() >> 20;
        assert(cp::gcd_u64(x * g, y * g) == std::gcd(x * g, y * g));
        unsigned long long u = random(), v = random();
        assert(cp::gcd_u64(u, v) == std::gcd(u, v));
    }
    return 0;
}

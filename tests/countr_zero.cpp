#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number_theory/countr_zero.hpp"
#include <random>

// The original countr_zero_constexpr of experiments/library/cpp/fps/convolution.hpp (valid for 1 <= n < 2^32).
static int original_countr_zero(unsigned int n) {
    int x = 0;
    while (!(n & (1 << x))) x++;
    return x;
}

int main() {
    assert(cp::countr_zero_u64(0) == 64);  // as std::countr_zero in C++20
    for (int k = 0; k < 64; ++k) {
        unsigned long long p = 1ULL << k;
        assert(cp::countr_zero_u64(p) == k);
        assert(cp::countr_zero_u64(p | (1ULL << 63)) == (k == 63 ? 63 : k));
        if (k < 63) assert(cp::countr_zero_u64(p * 3) == k);
        if (k > 0) assert(cp::countr_zero_u64(p - 1) == 0);
    }
    assert(cp::countr_zero_u64(~0ULL) == 0);
    for (unsigned long long n = 1; n < 5000; ++n) {
        assert(cp::countr_zero_u64(n) == __builtin_ctzll(n));
        assert(cp::countr_zero_u64(n) == original_countr_zero((unsigned int)n));
    }
    std::mt19937_64 random(20261109);
    for (int round = 0; round < 200000; ++round) {
        unsigned long long n = random() >> (random() % 64);
        if (n == 0) continue;
        int r = cp::countr_zero_u64(n);
        assert(r == __builtin_ctzll(n));
        assert(n % (1ULL << r) == 0);
        if (r < 63) assert((n >> r) % 2 == 1);
        if (n < (1ULL << 32)) assert(r == original_countr_zero((unsigned int)n));
    }
    return 0;
}

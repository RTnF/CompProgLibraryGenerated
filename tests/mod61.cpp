#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/modint/mod61.hpp"
#include <cstdint>
#include <random>

constexpr unsigned long long M61 = (1ull << 61) - 1;

// Independent oracle: 128 bit remainder.
unsigned long long mod_oracle(unsigned long long x) { return x % M61; }
unsigned long long mul_oracle(unsigned long long a, unsigned long long b) {
    return static_cast<unsigned long long>(static_cast<__uint128_t>(a) * b % M61);
}

int main() {
    std::mt19937_64 random(20261008);
    const unsigned long long edges[] = {0, 1, 2, M61 - 1, M61, M61 + 1, 2 * M61, 2 * M61 + 1, (1ull << 61),
                                        (1ull << 61) + 1, (1ull << 62) - 1, (1ull << 63), ~0ull - 1, ~0ull};
    for (auto x : edges) assert(cp::mod61(x) == mod_oracle(x));
    for (int i = 0; i < 100000; ++i) {
        const unsigned long long x = random() >> (random() % 64);
        assert(cp::mod61(x) == mod_oracle(x));
    }
    // mul61 requires both factors below 2^61; its result is congruent to the product, not necessarily reduced.
    const unsigned long long factors[] = {0, 1, 2, 131, M61 - 1, M61, (1ull << 30), (1ull << 31), (1ull << 31) - 1,
                                          (1ull << 31) + 1, (1ull << 60), (1ull << 61) - 2};
    for (auto a : factors)
        for (auto b : factors) {
            const auto r = cp::mul61(a, b);
            assert(r % M61 == mul_oracle(a, b));
            assert(cp::mod61(r) == mul_oracle(a, b));
        }
    for (int i = 0; i < 100000; ++i) {
        const unsigned long long a = random() >> (3 + random() % 61);
        const unsigned long long b = random() >> (3 + random() % 61);
        assert(a < (1ull << 61) && b < (1ull << 61));
        const auto r = cp::mul61(a, b);
        assert(r % M61 == mul_oracle(a, b));
    }
    return 0;
}

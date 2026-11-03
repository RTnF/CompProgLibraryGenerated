#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/pow_mod.hpp"
#include <cstdint>
#include <random>

// Independent oracle: repeated multiplication with 128 bit intermediates (small exponents) and Fermat checks.
unsigned long long slow_pow(unsigned long long base, unsigned long long exp, unsigned long long m) {
    unsigned long long result = 1 % m;
    base %= m;
    for (unsigned long long i = 0; i < exp; ++i) result = static_cast<unsigned long long>(static_cast<__uint128_t>(result) * base % m);
    return result;
}

unsigned long long wide_pow(unsigned long long base, unsigned long long exp, unsigned long long m) {
    __uint128_t result = 1 % m, b = base % m;
    while (exp) {
        if (exp & 1) result = result * b % m;
        b = b * b % m;
        exp >>= 1;
    }
    return static_cast<unsigned long long>(result);
}

int main() {
    std::mt19937_64 random(20261008);
    const unsigned long long moduli[] = {1, 2, 3, 4, 7, 10, 998244353, 1000000007, 4294967291ull, 4294967295ull, 4294967296ull};
    for (auto m : moduli)
        for (unsigned long long base = 0; base < 12; ++base)
            for (unsigned long long exp = 0; exp < 40; ++exp) assert(cp::pow_mod(base, exp, m) == slow_pow(base, exp, m));
    const unsigned long long big[] = {0, 1, 2, 3, 12345678901234567ull, ~0ull - 1, ~0ull};
    for (auto m : moduli)
        for (auto base : big)
            for (auto exp : big) {
                const auto r = cp::pow_mod(base, exp, m);
                assert(r < m && r == wide_pow(base, exp, m));
            }
    // Fermat's little theorem for the primes in the table.
    for (auto p : {998244353ull, 1000000007ull, 4294967291ull})
        for (int i = 0; i < 1000; ++i) {
            const unsigned long long a = 1 + random() % (p - 1);
            assert(cp::pow_mod(a, p - 1, p) == 1);
        }
    for (int i = 0; i < 100000; ++i) {
        const unsigned long long m = 1 + random() % 4294967296ull;
        const unsigned long long base = random(), exp = random() >> (random() % 64);
        assert(cp::pow_mod(base, exp, m) == wide_pow(base, exp, m));
    }
    return 0;
}

#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number_theory/bit_width_u64.hpp"
#include <cstdint>
#include <random>

// Independent oracle: the position of the highest set bit.
int oracle(std::uint64_t x) { return x == 0 ? 0 : 64 - __builtin_clzll(x); }

int main() {
    static_assert(cp::bit_width_u64(0) == 0);
    static_assert(cp::bit_width_u64(1) == 1);
    static_assert(cp::bit_width_u64(2) == 2);
    static_assert(cp::bit_width_u64(3) == 2);
    static_assert(cp::bit_width_u64(255) == 8);
    static_assert(cp::bit_width_u64(256) == 9);
    static_assert(cp::bit_width_u64(~std::uint64_t{0}) == 64);
    for (std::uint64_t x = 0; x < 100000; ++x) assert(cp::bit_width_u64(x) == oracle(x));
    for (int bit = 0; bit < 64; ++bit)
        for (std::uint64_t delta : {std::uint64_t{0}, std::uint64_t{1}, std::uint64_t{2}}) {
            const std::uint64_t power = std::uint64_t{1} << bit;
            assert(cp::bit_width_u64(power - 1 + delta) == oracle(power - 1 + delta));
            assert(cp::bit_width_u64(power + delta) == oracle(power + delta));
        }
    std::mt19937_64 random(20261007);
    for (int i = 0; i < 100000; ++i) {
        const std::uint64_t x = random() >> (random() % 64);
        assert(cp::bit_width_u64(x) == oracle(x));
    }
}

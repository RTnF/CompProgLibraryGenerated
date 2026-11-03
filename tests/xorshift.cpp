#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/xorshift.hpp"
#include <cstdint>

// Independent oracle written as a free function over a plain state.
unsigned long long oracle_next(unsigned long long &state) {
    unsigned long long x = state;
    x ^= x << 7;
    x ^= x >> 9;
    state = x;
    return x;
}

int main() {
    const unsigned long long seeds[] = {0, 1, 2, 88172645463325252ull, 0x8000000000000000ull, ~0ull, 123456789ull};
    for (auto seed : seeds) {
        cp::Xor64 generator(seed);
        unsigned long long state = seed;
        for (int i = 0; i < 100000; ++i) {
            const auto expected = oracle_next(state);
            assert(generator.get() == expected);
        }
    }
    // The all-zero state is a fixed point; any other state never reaches it in the first million steps.
    cp::Xor64 zero(0);
    for (int i = 0; i < 10; ++i) assert(zero.get() == 0);
    cp::Xor64 live(88172645463325252ull);
    for (int i = 0; i < 1000000; ++i) assert(live.get() != 0);
    return 0;
}

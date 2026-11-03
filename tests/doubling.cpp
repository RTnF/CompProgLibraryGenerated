#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/doubling.hpp"
#include <cstdint>
#include <random>
#include <vector>

// Independent oracle: apply the map one step at a time (no table recurrence).
int iterate(const std::vector<int> &v, int start, std::uint64_t steps) {
    int x = start;
    for (std::uint64_t s = 0; s < steps; ++s) x = v[x];
    return x;
}

int width_oracle(std::uint64_t x) { return x == 0 ? 0 : 64 - __builtin_clzll(x); }

void check_table(const std::vector<int> &v, std::uint64_t kmax) {
    const auto table = cp::doubling(v, kmax);
    const int w = width_oracle(kmax);
    assert(static_cast<int>(table.size()) == w);
    for (int i = 0; i < w; ++i) {
        assert(table[i].size() == v.size());
        for (std::size_t j = 0; j < v.size(); ++j) {
            if (i <= 12) {
                assert(table[i][j] == iterate(v, static_cast<int>(j), std::uint64_t{1} << i));
            } else {
                // Rows beyond the brute-force range: compose the previous row with itself.
                assert(table[i][j] == table[i - 1][table[i - 1][j]]);
            }
            assert(0 <= table[i][j] && table[i][j] < static_cast<int>(v.size()));
        }
    }
}

int main() {
    static_assert(cp::bit_width_u64(0) == 0);
    static_assert(cp::bit_width_u64(1) == 1);
    static_assert(cp::bit_width_u64(255) == 8);
    static_assert(cp::bit_width_u64(256) == 9);
    static_assert(cp::bit_width_u64(~std::uint64_t{0}) == 64);
    std::mt19937_64 random(20261007);
    for (int i = 0; i < 5000; ++i) {
        const std::uint64_t x = random() >> (random() % 64);
        assert(cp::bit_width_u64(x) == width_oracle(x));
    }
    for (int bit = 0; bit < 64; ++bit)
        for (std::uint64_t d : {std::uint64_t{0}, std::uint64_t{1}}) {
            const std::uint64_t x = (std::uint64_t{1} << bit) - 1 + d;
            assert(cp::bit_width_u64(x) == width_oracle(x));
        }
    // Every successor array of size at most 3, with several kmax values.
    const std::uint64_t maxima[] = {1, 2, 3, 4, 5, 7, 8, 9, 31, 32, 33, 4096, 4097,
                                    std::uint64_t{1} << 32, std::uint64_t{1} << 63, ~std::uint64_t{0}};
    check_table({}, 1);
    check_table({}, ~std::uint64_t{0});
    for (int n = 1; n <= 3; ++n) {
        std::vector<int> v(n, 0);
        for (;;) {
            for (auto kmax : maxima) check_table(v, kmax);
            int index = 0;
            while (index < n && ++v[index] == n) v[index++] = 0;
            if (index == n) break;
        }
    }
    for (int n : {4, 8, 20, 100}) {
        for (int round = 0; round < 20; ++round) {
            std::vector<int> v(n);
            for (auto &x : v) x = static_cast<int>(random() % n);
            for (auto kmax : maxima) check_table(v, kmax);
        }
    }
}

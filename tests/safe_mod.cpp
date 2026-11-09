#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number_theory/safe_mod.hpp"
#include <cstdint>
#include <limits>
#include <random>

// Independent unsigned-magnitude normalization, including INT64_MIN.
std::int64_t reference(std::int64_t x, std::int64_t m) {
    const auto magnitude = x < 0 ? std::uint64_t{0} - std::uint64_t(x) : std::uint64_t(x);
    const auto r = magnitude % std::uint64_t(m);
    return x < 0 && r != 0 ? m - std::int64_t(r) : std::int64_t(r);
}

void check(std::int64_t x, std::int64_t m) {
    const auto actual = cp::safe_mod(x, m);
    assert(actual == reference(x, m));
    assert(0 <= actual && actual < m);
}

int main() {
    static_assert(cp::safe_mod(-17, 3) == 1);
    static_assert(cp::safe_mod(0, 1) == 0);
    for (std::int64_t x = -100; x <= 100; ++x)
        for (std::int64_t m = 1; m <= 50; ++m) check(x, m);
    const auto low = std::numeric_limits<std::int64_t>::min();
    const auto high = std::numeric_limits<std::int64_t>::max();
    for (auto x : {low, low + 1, std::int64_t{-1}, std::int64_t{0}, std::int64_t{1}, high - 1, high})
        for (auto m : {std::int64_t{1}, std::int64_t{2}, std::int64_t{3}, high - 1, high}) check(x, m);
    std::mt19937_64 random(20261004);
    for (int i = 0; i < 10000; ++i) {
        // Avoid implementation-defined unsigned-to-signed conversion.
        const auto raw = random();
        const auto x = raw <= std::uint64_t(high) ? std::int64_t(raw)
            : low + std::int64_t(raw - (std::uint64_t{1} << 63));
        const auto m = std::int64_t(random() % std::uint64_t(high)) + 1;
        check(x, m);
    }
}

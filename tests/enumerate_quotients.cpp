#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number_theory/enumerate_quotients.hpp"
#include <cstdint>
#include <random>
#include <set>
#include <vector>

// Independent oracle: collect floor(n / x) by brute force over every divisor-sized x.
std::vector<std::uint64_t> brute(std::uint64_t n) {
    std::set<std::uint64_t> values;
    for (std::uint64_t x = 1; x <= n; ++x) values.insert(n / x);
    return {values.begin(), values.end()};
}

// For large n: every listed value must be attained and the list must be complete.
void check_large(std::uint64_t n) {
    const auto list = cp::enumerate_quotients(n);
    for (std::size_t i = 1; i < list.size(); ++i) assert(list[i - 1] < list[i]);
    if (n == 0) { assert(list.empty()); return; }
    assert(list.front() == 1 && list.back() == n);
    // Each value q is attained: x = n / q gives floor(n / x) == q.
    for (auto q : list) {
        assert(q >= 1);
        assert(n / (n / q) == q);
    }
    // Completeness: the smallest x attaining q is n / (q + 1) + 1, so the next larger
    // quotient is n / (n / (q + 1)); nothing lies strictly between consecutive entries.
    for (std::size_t i = 0; i + 1 < list.size(); ++i) {
        const std::uint64_t y = n / (list[i] + 1);
        assert(y >= 1 && n / y == list[i + 1]);
    }
}

int main() {
    for (std::uint64_t n = 0; n <= 3000; ++n) assert(cp::enumerate_quotients(n) == brute(n));
    std::mt19937_64 random(20261007);
    for (int i = 0; i < 300; ++i) {
        const std::uint64_t n = random() >> (24 + random() % 40);
        check_large(n);
    }
    // The list has about 2 * sqrt(n) entries, so keep n below 2^42 for memory.
    const std::uint64_t edges[] = {
        std::uint64_t{1} << 32, (std::uint64_t{1} << 32) - 1, (std::uint64_t{1} << 32) + 1,
        std::uint64_t{1} << 40, (std::uint64_t{1} << 40) - 1, (std::uint64_t{1} << 42)};
    for (auto n : edges) check_large(n);
    return 0;
}

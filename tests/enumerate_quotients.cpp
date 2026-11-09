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

namespace original {
// Verbatim copy of experiments/library/cpp/number_theory/enumerate_quotients.hpp (the test is compiled without -I, so the
// header cannot be included by its own relative include).
// 整数との商 floor(n / x) を列挙する
vector<ull> enumerate_quotients(ull n) {
  // N/k - N/(k+1) > 1
  // N/k(k+1) > 1
  // N > k(k+1)
  ull ok = 4294967295;
  ull ng = 0;
  ull k;
  while (ok - ng > 1) {
    k = (ok + ng) / 2;
    (k * (k + 1) >= n ? ok : ng) = k;
  }
  vector<ull> ret;
  ull p = n / ok;
  for (ull i = 1; i <= p; i++) {
    ret.emplace_back(i);
  }
  for (ull i = ok - 1; i >= 1; i--) {
    ret.emplace_back(n / i);
  }
  return ret;
}
} // namespace original

// The original (global ::enumerate_quotients with the ull / ternary-assignment spelling) and the published version
// return the same list wherever the original is correct (n <= 2^64 - 2^32; the list has about 2 sqrt(n) entries,
// so the comparison is limited to n < 2^44).
void check_against_original(std::uint64_t n) {
    const std::vector<ull> original = original::enumerate_quotients(n);
    const std::vector<std::uint64_t> published = cp::enumerate_quotients(n);
    assert(original.size() == published.size());
    for (std::size_t i = 0; i < original.size(); ++i) assert(original[i] == published[i]);
}

int main() {
    for (std::uint64_t n = 0; n <= 3000; ++n) check_against_original(n);
    {
        std::mt19937_64 differential(20261110);
        for (int i = 0; i < 40; ++i) check_against_original(differential() >> (20 + differential() % 40));
        check_against_original((1ull << 44) - 1);
        check_against_original(1ull << 40);
    }
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

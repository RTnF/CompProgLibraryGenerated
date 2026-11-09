#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/array/doubling.hpp"
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

namespace original {
// std::bit_width is C++20 and this test is compiled as C++17: the same value from the compiler builtin.
inline int bit_width(std::uint64_t x) { return x == 0 ? 0 : 64 - __builtin_clzll(x); }
// Verbatim copy of experiments/library/cpp/array/doubling.hpp (the test is compiled without -I, so the header cannot
// be included by its own relative include).
using std::vector;
using std::uint64_t;
// ダブリング
// 値が[0, n)である配列のそれぞれで
// j = v[j] を 2**i 回繰り返した結果の2次元配列を作る
// O(n log kmax)
vector<vector<int>> doubling(vector<int> &v, uint64_t kmax) {
  // 0:0 1:1 2:2 4:3 8:4 ...
  assert(kmax > 0);
  int n = v.size();
  for (int i = 0; i < n; i++) {
    assert(0 <= v[i]);
    assert(v[i] < n);
  }
  int w = bit_width(kmax);
  vector<vector<int>> ret(w);
  ret[0].assign(v.begin(), v.end());
  for(int i = 1; i < w; i++){
    ret[i].reserve(n);
    for(int j = 0; j < n; j++){
      ret[i].emplace_back(ret[i-1][ret[i-1][j]]);
    }
  }
  return ret;
}
} // namespace original

// The original and the published version build the same table (the published parameter is const, which also accepts
// the original's non-const lvalues).
void check_against_original(std::vector<int> v, std::uint64_t kmax) {
    const auto published = cp::doubling(v, kmax);
    const auto expected = original::doubling(v, kmax);
    assert(published == expected);
}

int main() {
    {
        std::mt19937_64 differential(20261110);
        for (int round = 0; round < 200; ++round) {
            const int n = 1 + static_cast<int>(differential() % 40);
            std::vector<int> v(n);
            for (int &x : v) x = static_cast<int>(differential() % n);
            check_against_original(v, 1 + (differential() >> (differential() % 64)));
        }
        check_against_original({0}, 1);
        check_against_original({0}, ~std::uint64_t{0});
    }
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

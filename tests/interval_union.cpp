#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/interval/interval_union.hpp"
#include <algorithm>
#include <random>
#include <utility>
#include <vector>

int main() {
    std::mt19937_64 random(20261012);
    for (int n = 0; n <= 40; ++n) {
        for (int round = 0; round < 20; ++round) {
            long long span = 1 + (long long)(random() % 30);
            std::vector<std::pair<long long, long long>> pairs;
            for (int i = 0; i < n; ++i) {
                long long l = (long long)(random() % (2 * span + 1)) - span;
                pairs.emplace_back(l, l + (long long)(random() % 6));
            }
            // reference: the original implementation (experiments/library/cpp/interval/interval_union.hpp)
            std::vector<std::pair<long long, long long>> sorted = pairs;
            std::sort(sorted.begin(), sorted.end());
            std::vector<std::pair<long long, long long>> expected;
            for (auto &&[a, b] : sorted) {
                if (expected.empty() || expected.back().second < a) {
                    expected.emplace_back(a, b);
                } else if (expected.back().second < b) {
                    expected.back().second = b;
                }
            }
            std::vector<std::pair<long long, long long>> v = pairs;
            auto ret = cp::interval_union_inclusive(v);
            assert(ret == expected);
            assert(v == sorted);  // the argument is sorted in place
            // independent check: the same points are covered, and the result is separated and sorted
            for (long long x = -span - 1; x <= span + 7; ++x) {
                bool in_input = false, in_ret = false;
                for (auto &[a, b] : pairs) in_input = in_input || (a <= x && x <= b);
                for (auto &[a, b] : ret) in_ret = in_ret || (a <= x && x <= b);
                assert(in_input == in_ret);
            }
            for (size_t k = 0; k < ret.size(); ++k) {
                assert(ret[k].first <= ret[k].second);
                if (k + 1 < ret.size()) assert(ret[k].second < ret[k + 1].first);
            }
        }
    }
    // the element type is a template parameter
    std::vector<std::pair<int, int>> w = {{5, 7}, {1, 2}, {2, 4}};
    auto r = cp::interval_union_inclusive(w);
    assert((r == std::vector<std::pair<int, int>>{{1, 4}, {5, 7}}));
    return 0;
}

#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/interval_union.hpp"
#include <algorithm>
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261012);
    for (int n = 0; n <= 40; ++n) {
        for (int round = 0; round < 20; ++round) {
            long long span = 1 + (long long)(random() % 30);
            std::vector<long long> l(n), r(n);
            std::vector<std::pair<long long, long long>> pairs;
            for (int i = 0; i < n; ++i) {
                l[i] = (long long)(random() % (2 * span + 1)) - span;
                r[i] = l[i] + (long long)(random() % 6);
                pairs.emplace_back(l[i], r[i]);
            }
            // reference: the original implementation on a vector of pairs
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
            std::vector<long long> ret_l(n + 2, -999), ret_r(n + 2, -999);
            std::vector<long long> l2 = l, r2 = r;
            int m = cp::interval_union_inclusive(l2, r2, ret_l, ret_r);
            assert(m == (int)expected.size());
            for (int k = 0; k < m; ++k) {
                assert(ret_l[k] == expected[k].first && ret_r[k] == expected[k].second);
                assert(ret_l[k] <= ret_r[k]);
                if (k + 1 < m) assert(ret_r[k] < ret_l[k + 1]);
            }
            // the input is sorted lexicographically, like the original
            for (int i = 0; i < n; ++i) assert(l2[i] == sorted[i].first && r2[i] == sorted[i].second);
            // entries beyond the result are untouched
            for (int k = m; k < n + 2; ++k) assert(ret_l[k] == -999 && ret_r[k] == -999);
            // coverage of every point
            for (long long x = -span - 1; x <= span + 7; ++x) {
                bool inInput = false, inResult = false;
                for (int i = 0; i < n; ++i) inInput = inInput || (l[i] <= x && x <= r[i]);
                for (int k = 0; k < m; ++k) inResult = inResult || (ret_l[k] <= x && x <= ret_r[k]);
                assert(inInput == inResult);
            }
        }
    }
    // large values
    {
        std::vector<long long> l = {1LL << 62, -(1LL << 62), 5}, r = {(1LL << 62) + 1, 0, 6};
        std::vector<long long> rl(3), rr(3);
        int m = cp::interval_union_inclusive(l, r, rl, rr);
        assert(m == 3 && rl[0] == -(1LL << 62) && rr[0] == 0 && rl[1] == 5 && rr[1] == 6 && rl[2] == (1LL << 62));
    }
    // the element type is a template parameter
    {
        std::vector<int> l = {3, 1, 2}, r = {4, 2, 3};
        std::vector<int> rl(3), rr(3);
        int m = cp::interval_union_inclusive(l, r, rl, rr);
        assert(m == 1 && rl[0] == 1 && rr[0] == 4);
    }
    return 0;
}

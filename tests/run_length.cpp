#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/run_length.hpp"
#include <climits>
#include <random>
#include <utility>
#include <vector>

int main() {
    std::mt19937_64 random(20261024);
    for (int n = 0; n <= 60; ++n) {
        for (int round = 0; round < 6; ++round) {
            std::vector<long long> v(n);
            int alphabet = round % 3 + 1;
            for (long long &x : v) x = static_cast<long long>(random() % alphabet) - 1;
            std::vector<long long> values(n, 77);
            std::vector<int> counts(n, -5);
            int m = cp::run_length(v, values, counts);
            // reference: split into maximal runs of equal values
            std::vector<std::pair<long long, int>> expected;
            for (int i = 0; i < n; ++i) {
                if (i > 0 && v[i] == v[i - 1]) expected.back().second++;
                else expected.emplace_back(v[i], 1);
            }
            assert(m == (int)expected.size());
            for (int k = 0; k < m; ++k) {
                assert(values[k] == expected[k].first);
                assert(counts[k] == expected[k].second);
            }
            // untouched beyond the runs
            for (int k = m; k < n; ++k) assert(values[k] == 77 && counts[k] == -5);
        }
    }
    std::vector<long long> v = {LLONG_MIN, LLONG_MIN, LLONG_MAX, LLONG_MAX, LLONG_MAX, 0};
    std::vector<long long> values(6);
    std::vector<int> counts(6);
    assert(cp::run_length(v, values, counts) == 3);
    assert(values[0] == LLONG_MIN && counts[0] == 2 && values[1] == LLONG_MAX && counts[1] == 3 && values[2] == 0 && counts[2] == 1);
    return 0;
}

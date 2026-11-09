#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/array/vector2d_sum.hpp"
#include <climits>
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261020);
    assert(cp::vector2d_sum(std::vector<std::vector<long long>>()) == 0);
    assert(cp::vector2d_sum(std::vector<std::vector<long long>>(5)) == 0);  // empty rows
    for (int rows : {1, 2, 3, 10, 50}) {
        for (int trial = 0; trial < 20; ++trial) {
            std::vector<std::vector<long long>> g(rows);
            long long expected = 0;
            for (auto &row : g) {
                row.resize(random() % 12);  // ragged, possibly empty
                for (long long &x : row) {
                    x = static_cast<long long>(random() % 2001) - 1000;
                    expected += x;
                }
            }
            assert(cp::vector2d_sum(g) == expected);
        }
    }
    // the extreme values: the partial sums stay in range
    std::vector<std::vector<long long>> big = {{LLONG_MAX}, {}, {LLONG_MIN, 1}, {-1}};
    assert(cp::vector2d_sum(big) == LLONG_MAX + (LLONG_MIN + 1) - 1);
    // the element type is a template parameter
    assert(cp::vector2d_sum(std::vector<std::vector<int>>{{1, 2}, {3}, {}}) == 6);
    assert(cp::vector2d_sum(std::vector<std::vector<double>>{{0.5}, {1.5, 2.0}}) == 4.0);
    return 0;
}

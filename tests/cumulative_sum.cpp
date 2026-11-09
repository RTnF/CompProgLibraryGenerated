#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/array/cumulative_sum.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261014);
    for (int n : {0, 1, 2, 3, 10, 100, 1000}) {
        std::vector<long long> a(n);
        for (int i = 0; i < n; ++i) a[i] = static_cast<long long>(random() % 2001) - 1000;
        cp::CumulativeSum<long long> cs(a);
        for (int x = 0; x <= n; x += 1 + n / 30) {
            long long expected = 0;
            for (int i = 0; i < x; ++i) expected += a[i];
            assert(cs.sum(x) == expected);
            for (int y = x; y <= n; y += 1 + n / 30) {
                long long range = 0;
                for (int i = x; i < y; ++i) range += a[i];
                assert(cs.sum(x, y) == range);
            }
        }
    }
    // large values: the prefix sums stay in range and so does the difference
    std::vector<long long> big = {1LL << 62, 5, 0};
    cp::CumulativeSum<long long> bigsum(big);
    assert(bigsum.sum(1) == (1LL << 62) && bigsum.sum(1, 3) == 5 && bigsum.sum(3) == (1LL << 62) + 5);
    // the element type is a template parameter
    cp::CumulativeSum<int> narrow(std::vector<int>{3, 1, 4, 1, 5});
    assert(narrow.sum(5) == 14 && narrow.sum(1, 4) == 6);
    cp::CumulativeSum<double> real(std::vector<double>{0.5, 1.5, 2.0});
    assert(real.sum(2, 3) == 2.0 && real.sum(3) == 4.0);
    // two-dimensional sums against the naive block sums
    for (int n : {1, 2, 3, 7, 20}) {
        for (int m : {1, 2, 5, 13}) {
            std::vector<std::vector<long long>> v(n, std::vector<long long>(m));
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < m; ++j) v[i][j] = static_cast<long long>(random() % 2001) - 1000;
            cp::CumulativeSum2D<long long> cs2(v);
            for (int a = 0; a <= n; ++a)
                for (int b = 0; b <= m; ++b) {
                    long long expected = 0;
                    for (int i = 0; i < a; ++i)
                        for (int j = 0; j < b; ++j) expected += v[i][j];
                    assert(cs2.sum(a, b) == expected);
                }
            for (int a1 = 0; a1 <= n; ++a1)
                for (int a2 = a1; a2 <= n; ++a2)
                    for (int b1 = 0; b1 <= m; ++b1)
                        for (int b2 = b1; b2 <= m; ++b2) {
                            long long expected = 0;
                            for (int i = a1; i < a2; ++i)
                                for (int j = b1; j < b2; ++j) expected += v[i][j];
                            assert(cs2.sum(a1, b1, a2, b2) == expected);
                        }
        }
    }
    cp::CumulativeSum2D<int> narrow2(std::vector<std::vector<int>>{{1, 2, 3}, {4, 5, 6}});
    assert(narrow2.sum(2, 3) == 21 && narrow2.sum(1, 1, 2, 3) == 11 && narrow2.sum(0, 1, 2, 2) == 7);
    cp::CumulativeSum2D<double> real2(std::vector<std::vector<double>>{{0.5, 1.5}, {2.0, 4.0}});
    assert(real2.sum(2, 2) == 8.0 && real2.sum(1, 0, 2, 1) == 2.0);
    return 0;
}

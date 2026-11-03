#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/floyd_warshall.hpp"
#include <algorithm>
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261021);
    const long long INF = 1LL << 60;
    for (int n = 0; n <= 25; ++n) {
        for (int round = 0; round < 8; ++round) {
            std::vector<long long> d(n * n, INF);
            for (int i = 0; i < n; ++i) d[i * n + i] = 0;
            int edges = n == 0 ? 0 : (int)(random() % (3 * n + 1));
            for (int e = 0; e < edges; ++e) {
                int u = (int)(random() % n), v = (int)(random() % n);
                d[u * n + v] = std::min<long long>(d[u * n + v], (long long)(random() % 20));
            }
            // reference: repeated relaxation over all intermediate vertices (Bellman-Ford style on the matrix)
            std::vector<long long> expected = d;
            for (int pass = 0; pass < n; ++pass)
                for (int i = 0; i < n; ++i)
                    for (int j = 0; j < n; ++j)
                        for (int m = 0; m < n; ++m)
                            expected[i * n + j] = std::min(expected[i * n + j], expected[i * n + m] + expected[m * n + j]);
            std::vector<long long> got = d;
            cp::floyd_warshall(got, n);
            assert(got == expected);
        }
    }
    // entries up to the allowed bound 2^62 - 1 are fine: the sum of two entries does not overflow
    const long long top = (1LL << 62) - 1;
    std::vector<long long> big = {0, top, top, 0};
    cp::floyd_warshall(big, 2);
    assert(big[1] == top && big[2] == top);
    // the element type is a template parameter
    {
        std::vector<int> d = {0, 5, 1, 9, 0, 1, 1, 1, 0};
        cp::floyd_warshall(d, 3);
        assert(d[1] == 2 && d[3] == 2 && d[2] == 1);
    }
    // the vector-of-rows form agrees with the flat form
    for (int n = 0; n <= 20; ++n) {
        for (int round = 0; round < 6; ++round) {
            std::vector<long long> flat(n * n, INF);
            std::vector<std::vector<long long>> rows(n, std::vector<long long>(n, INF));
            for (int i = 0; i < n; ++i) flat[i * n + i] = rows[i][i] = 0;
            int edges = n == 0 ? 0 : (int)(random() % (3 * n + 1));
            for (int e = 0; e < edges; ++e) {
                int u = (int)(random() % n), v = (int)(random() % n);
                long long c = (long long)(random() % 20);
                flat[u * n + v] = std::min(flat[u * n + v], c);
                rows[u][v] = std::min(rows[u][v], c);
            }
            cp::floyd_warshall(flat, n);
            cp::floyd_warshall(rows);
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < n; ++j) assert(rows[i][j] == flat[i * n + j]);
        }
    }
    {
        std::vector<std::vector<int>> d = {{0, 5, 1}, {9, 0, 1}, {1, 1, 0}};
        cp::floyd_warshall(d);
        assert(d[0][1] == 2 && d[1][0] == 2 && d[0][2] == 1);
    }
    return 0;
}

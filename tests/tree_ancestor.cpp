#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/tree/tree_ancestor.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261030);
    for (int round = 0; round < 20000; ++round) {
        int n = 1 + random() % 12;
        std::vector<int> f(n);
        for (int x = 0; x < n; ++x) f[x] = random() % n;  // any map [0, n) -> [0, n)
        int rows = random() % 9;  // the table has rows for 2^0 .. 2^(rows - 1)
        std::vector<std::vector<int>> anc(rows, std::vector<int>(n));
        for (int x = 0; x < n; ++x)
            if (rows > 0) anc[0][x] = f[x];
        for (int k = 1; k < rows; ++k)
            for (int x = 0; x < n; ++x) anc[k][x] = anc[k - 1][anc[k - 1][x]];
        int limit = rows == 0 ? 1 : (1 << rows);  // every i < limit needs only the rows 2^k <= i
        int i = random() % limit;
        int v = random() % n;
        int expect = v;
        for (int s = 0; s < i; ++s) expect = f[expect];
        assert(cp::tree_ancestor(anc, v, i) == expect);
    }
    // a large step count with a table of 30 rows
    {
        int n = 5;
        std::vector<int> f = {1, 2, 3, 4, 0};  // a cycle
        std::vector<std::vector<int>> anc(30, std::vector<int>(n));
        for (int x = 0; x < n; ++x) anc[0][x] = f[x];
        for (int k = 1; k < 30; ++k)
            for (int x = 0; x < n; ++x) anc[k][x] = anc[k - 1][anc[k - 1][x]];
        for (int v = 0; v < n; ++v) {
            int i = (1 << 30) - 1;
            assert(cp::tree_ancestor(anc, v, i) == (int)((v + (long long)i) % n));
        }
    }
    return 0;
}

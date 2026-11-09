#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/tree/tree_lca_same_depth.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261031);
    for (int round = 0; round < 20000; ++round) {
        int n = 1 + random() % 14;
        // a random rooted tree on [0, n): the parent of i > 0 is a smaller vertex; the parent of 0 is 0
        std::vector<int> parent(n, 0), depth(n, 0);
        for (int i = 1; i < n; ++i) {
            parent[i] = random() % i;
            depth[i] = depth[parent[i]] + 1;
        }
        int max_depth = 0;
        for (int i = 0; i < n; ++i) max_depth = std::max(max_depth, depth[i]);
        int rows = 1;
        while ((1 << rows) <= max_depth) ++rows;  // rows 0 .. floor(log2(max_depth)) at least
        rows += random() % 2;                     // sometimes one more row than needed
        std::vector<std::vector<int>> anc(rows, std::vector<int>(n));
        for (int x = 0; x < n; ++x) anc[0][x] = parent[x];
        for (int k = 1; k < rows; ++k)
            for (int x = 0; x < n; ++x) anc[k][x] = anc[k - 1][anc[k - 1][x]];
        int u = random() % n;
        // pick v of the same depth as u
        std::vector<int> same;
        for (int x = 0; x < n; ++x)
            if (depth[x] == depth[u]) same.push_back(x);
        int v = same[random() % same.size()];
        int a = u, b = v;
        while (a != b) {
            a = parent[a];
            b = parent[b];
        }
        assert(cp::tree_lca_same_depth(anc, u, v, depth[u]) == a);
    }
    return 0;
}

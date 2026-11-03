#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/tree_distance.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261101);
    for (int round = 0; round < 20000; ++round) {
        int n = 1 + random() % 14;
        // a random rooted tree: the parent of i > 0 is a smaller vertex; edge costs may be negative
        std::vector<int> parent(n, 0), depth(n, 0);
        std::vector<long long> edge(n, 0), cost_depth(n, 0);
        for (int i = 1; i < n; ++i) {
            parent[i] = random() % i;
            edge[i] = (long long)(random() % 2001) - 1000;
            depth[i] = depth[parent[i]] + 1;
            cost_depth[i] = cost_depth[parent[i]] + edge[i];
        }
        int u = random() % n, v = random() % n;
        // the lowest common ancestor by climbing
        int a = u, b = v;
        while (depth[a] > depth[b]) a = parent[a];
        while (depth[b] > depth[a]) b = parent[b];
        while (a != b) {
            a = parent[a];
            b = parent[b];
        }
        long long expect = 0;  // the cost of the path u - lca - v
        for (int x = u; x != a; x = parent[x]) expect += edge[x];
        for (int x = v; x != a; x = parent[x]) expect += edge[x];
        assert(cp::tree_distance(cost_depth, u, v, a) == expect);
    }
    return 0;
}

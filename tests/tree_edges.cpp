#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/csr_build.hpp"
#include "../library/tree_edges.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261103);
    for (int round = 0; round < 20000; ++round) {
        int n = random() % 14;
        std::vector<int> parent(n);
        for (int i = 0; i < n; ++i) {
            int kind = random() % 8;
            if (kind == 0) parent[i] = i;                     // a root (self parent)
            else if (kind == 1) parent[i] = -1;               // a root (no parent)
            else if (kind == 2) parent[i] = n + random() % 3;  // out of range
            else parent[i] = n == 0 ? 0 : (int)(random() % n);
        }
        // the adjacency lists exactly as the original constructor Tree(root, parent) builds them
        std::vector<std::vector<int>> adj(n);
        int expect_m = 0;
        for (int i = 0; i < n; i++) {
            if (i != parent[i] && 0 <= parent[i] && parent[i] < n) {
                adj[parent[i]].push_back(i);
                adj[i].push_back(parent[i]);
                expect_m += 2;
            }
        }
        std::vector<int> from(2 * n, -7), to(2 * n, -7);
        int m = cp::tree_edges_from_parent(parent, from, to, n);
        assert(m == expect_m);
        for (int k = m; k < 2 * n; ++k) assert(from[k] == -7 && to[k] == -7);  // the rest is untouched
        from.resize(m);
        to.resize(m);
        std::vector<int> head(n + 1, 0), target(m, 0), pos(n, 0);
        cp::csr_build(from, to, head, target, pos, n);
        for (int v = 0; v < n; ++v) {
            assert(head[v + 1] - head[v] == (int)adj[v].size());
            for (int d = 0; d < (int)adj[v].size(); ++d) assert(target[head[v] + d] == adj[v][d]);
        }
    }
    return 0;
}

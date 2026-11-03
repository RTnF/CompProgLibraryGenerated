#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/csr_build.hpp"
#include "../library/tree_arcs.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261105);
    for (int round = 0; round < 20000; ++round) {
        int n = 1 + random() % 12;
        int m = n - 1;  // the edge list of a tree on n vertices (any endpoints in [0, n) are accepted)
        std::vector<int> from(m), to(m);
        for (int i = 0; i < m; ++i) {
            from[i] = random() % n;
            to[i] = random() % n;
        }
        // the adjacency lists exactly as the original constructor builds them
        std::vector<std::vector<int>> adj(n);
        for (int i = 0; i < m; i++) {
            adj[from[i]].push_back(to[i]);
            adj[to[i]].push_back(from[i]);
        }
        int size = 2 * m + random() % 3;
        std::vector<int> af(size, -7), at(size, -7);
        cp::tree_arcs_from_list(from, to, af, at, m);
        for (int i = 0; i < m; ++i) {
            assert(af[2 * i] == from[i] && at[2 * i] == to[i]);
            assert(af[2 * i + 1] == to[i] && at[2 * i + 1] == from[i]);
        }
        for (int k = 2 * m; k < size; ++k) assert(af[k] == -7 && at[k] == -7);  // the rest is untouched
        af.resize(2 * m);
        at.resize(2 * m);
        std::vector<int> head(n + 1, 0), target(2 * m, 0), pos(n, 0);
        cp::csr_build(af, at, head, target, pos, n);
        for (int v = 0; v < n; ++v) {
            assert(head[v + 1] - head[v] == (int)adj[v].size());
            for (int d = 0; d < (int)adj[v].size(); ++d) assert(target[head[v] + d] == adj[v][d]);
        }
    }
    return 0;
}

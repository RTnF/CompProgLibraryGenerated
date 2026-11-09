#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/topological_sort.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261028);
    for (int round = 0; round < 6000; ++round) {
        int n = random() % 9;
        int m = n == 0 ? 0 : random() % 20;
        bool dag = random() % 2 == 0;
        std::vector<std::vector<int>> adj(n);
        for (int e = 0; e < m; ++e) {
            int u = random() % n, v = random() % n;
            if (dag) {
                if (u == v) continue;
                if (u > v) std::swap(u, v);  // edges only go from smaller to larger numbers
            }
            adj[u].push_back(v);
        }
        std::vector<int> head(n + 1, 0), target;
        for (int v = 0; v < n; ++v) {
            head[v + 1] = head[v] + (int)adj[v].size();
            for (int w : adj[v]) target.push_back(w);
        }
        std::vector<int> indeg(n, 0), order(n, -1);
        int k = cp::topological_sort(head, target, indeg, order, n);
        assert(0 <= k && k <= n);
        std::vector<int> pos(n, -1);
        for (int i = 0; i < k; ++i) {
            assert(0 <= order[i] && order[i] < n && pos[order[i]] == -1);
            pos[order[i]] = i;
        }
        // reachability closure decides whether the graph has a cycle
        std::vector<std::vector<char>> reach(n, std::vector<char>(n, 0));
        for (int u = 0; u < n; ++u)
            for (int w : adj[u]) reach[u][w] = 1;
        for (int t = 0; t < n; ++t)
            for (int a = 0; a < n; ++a)
                for (int b = 0; b < n; ++b)
                    if (reach[a][t] && reach[t][b]) reach[a][b] = 1;
        bool cyclic = false;
        for (int u = 0; u < n; ++u) cyclic |= reach[u][u];
        assert((k == n) == !cyclic);
        // every in-neighbor of an ordered vertex comes earlier
        for (int u = 0; u < n; ++u)
            for (int w : adj[u])
                if (pos[w] != -1) assert(pos[u] != -1 && pos[u] < pos[w]);
        // every unordered vertex has an unordered in-neighbor
        for (int w = 0; w < n; ++w) {
            if (pos[w] != -1) continue;
            bool found = false;
            for (int u = 0; u < n; ++u)
                for (int x : adj[u]) found |= (x == w && pos[u] == -1);
            assert(found);
        }
    }
    return 0;
}

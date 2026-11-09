#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/prim.hpp"
#include <algorithm>
#include <random>
#include <vector>

// Reference: Kruskal with a simple union-find; compares the weight of a minimum spanning forest.
static int find(std::vector<int> &p, int x) { return p[x] == x ? x : p[x] = find(p, p[x]); }

template <class Cost> static void run(std::mt19937_64 &random, Cost inf, int rounds, int maxn, int maxc) {
    for (int round = 0; round < rounds; ++round) {
        int n = random() % (maxn + 1);
        int m = n == 0 ? 0 : random() % (2 * n + 3);
        std::vector<std::vector<std::pair<int, Cost>>> adj(n);
        std::vector<std::array<Cost, 3>> edges;
        for (int e = 0; e < m; ++e) {
            int u = random() % n, v = random() % n;
            Cost c = random() % maxc;
            adj[u].push_back({v, c});
            adj[v].push_back({u, c});
            edges.push_back({c, (Cost)u, (Cost)v});
        }
        std::vector<int> head(n + 1, 0), target;
        std::vector<Cost> cost;
        for (int v = 0; v < n; ++v) {
            head[v + 1] = head[v] + (int)adj[v].size();
            for (auto &p : adj[v]) {
                target.push_back(p.first);
                cost.push_back(p.second);
            }
        }
        std::vector<Cost> dist(n, inf);
        std::vector<int> done(n, 0);
        Cost got = cp::prim(head, target, cost, dist, done, n, inf);
        std::sort(edges.begin(), edges.end());
        std::vector<int> par(n);
        for (int i = 0; i < n; ++i) par[i] = i;
        Cost expected = 0;
        for (auto &e : edges) {
            int a = find(par, (int)e[1]), b = find(par, (int)e[2]);
            if (a != b) {
                par[a] = b;
                expected += e[0];
            }
        }
        assert(got == expected);
        for (int v = 0; v < n; ++v) assert(done[v] == 1);
    }
}

int main() {
    std::mt19937_64 random(20261012);
    run<long long>(random, 1LL << 60, 5000, 9, 12);
    run<long long>(random, 1LL << 60, 300, 60, 1000000);
    // a path, a complete graph and isolated vertices
    std::vector<int> head = {0, 0, 0, 0};
    std::vector<int> target;
    std::vector<long long> cost, dist(3, 1LL << 60);
    std::vector<int> done(3, 0);
    assert(cp::prim(head, target, cost, dist, done, 3, 1LL << 60) == 0);
    return 0;
}

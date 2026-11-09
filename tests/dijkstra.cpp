#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/dijkstra.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261029);
    const long long inf = 1LL << 60;
    for (int round = 0; round < 4000; ++round) {
        int n = 1 + random() % 9;
        int m = random() % 25;
        std::vector<std::vector<std::pair<int, long long>>> adj(n);
        for (int e = 0; e < m; ++e) adj[random() % n].push_back({(int)(random() % n), (long long)(random() % 12)});
        std::vector<int> head(n + 1, 0), target;
        std::vector<long long> cost;
        for (int v = 0; v < n; ++v) {
            head[v + 1] = head[v] + (int)adj[v].size();
            for (auto &p : adj[v]) {
                target.push_back(p.first);
                cost.push_back(p.second);
            }
        }
        // one or several sources with small start values
        std::vector<long long> dist(n, inf);
        int sources = 1 + random() % 2;
        for (int s = 0; s < sources; ++s) dist[random() % n] = (long long)(random() % 5);
        std::vector<long long> d0 = dist;
        std::vector<int> done(n, 0), parent(n, -1);
        cp::dijkstra(head, target, cost, dist, done, parent, n, inf);
        // reference: Floyd-Warshall over the same edges, then the minimum over the sources
        std::vector<std::vector<long long>> fw(n, std::vector<long long>(n, inf));
        for (int i = 0; i < n; ++i) fw[i][i] = 0;
        for (int v = 0; v < n; ++v)
            for (auto &p : adj[v]) fw[v][p.first] = std::min(fw[v][p.first], p.second);
        for (int k = 0; k < n; ++k)
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < n; ++j)
                    if (fw[i][k] != inf && fw[k][j] != inf) fw[i][j] = std::min(fw[i][j], fw[i][k] + fw[k][j]);
        for (int v = 0; v < n; ++v) {
            long long expected = inf;
            for (int w = 0; w < n; ++w)
                if (d0[w] != inf && fw[w][v] != inf) expected = std::min(expected, d0[w] + fw[w][v]);
            assert(dist[v] == expected);
            if (expected != inf) assert(done[v] == 1);
        }
        // parent: unchanged (-1) or an edge from a finished vertex u that realises dist[v]; following parents ends at a vertex
        // whose dist is its initial value
        for (int v = 0; v < n; ++v) {
            if (parent[v] < 0) {
                assert(dist[v] == d0[v] || dist[v] == inf);
                continue;
            }
            int u = parent[v];
            assert(done[u] == 1 && dist[u] != inf);
            bool ok = false;
            for (auto &p : adj[u]) ok |= (p.first == v && dist[u] + p.second == dist[v]);
            assert(ok);
        }
        for (int v = 0; v < n; ++v) {
            int u = v, steps = 0;
            while (parent[u] >= 0) {
                u = parent[u];
                assert(++steps <= n);
            }
            if (dist[v] != inf) assert(dist[u] == d0[u]);
        }
    }
    return 0;
}

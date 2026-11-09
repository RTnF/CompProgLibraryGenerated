#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/bellman_ford.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261027);
    const long long inf = 1LL << 60;
    for (int round = 0; round < 3000; ++round) {
        int n = 1 + random() % 9;
        int m = random() % 25;
        // potentials make negative edges possible without negative cycles: cost = w + p[u] - p[v], w >= 0
        std::vector<long long> p(n);
        for (auto &x : p) x = (long long)(random() % 41) - 20;
        std::vector<int> from(m), to(m);
        std::vector<long long> cost(m);
        for (int e = 0; e < m; ++e) {
            from[e] = random() % n;
            to[e] = random() % n;
            cost[e] = (long long)(random() % 10) + p[from[e]] - p[to[e]];
        }
        int source = random() % n;
        std::vector<long long> dist(n, inf);
        dist[source] = 0;
        std::vector<int> parent(n, -1);
        cp::bellman_ford(from, to, cost, dist, parent, n, inf);
        // reference: Floyd-Warshall (no negative cycle exists)
        std::vector<std::vector<long long>> fw(n, std::vector<long long>(n, inf));
        for (int i = 0; i < n; ++i) fw[i][i] = 0;
        for (int e = 0; e < m; ++e) fw[from[e]][to[e]] = std::min(fw[from[e]][to[e]], cost[e]);
        for (int k = 0; k < n; ++k)
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < n; ++j)
                    if (fw[i][k] != inf && fw[k][j] != inf) fw[i][j] = std::min(fw[i][j], fw[i][k] + fw[k][j]);
        for (int v = 0; v < n; ++v) assert(dist[v] == fw[source][v]);
        for (int v = 0; v < n; ++v) {
            if (v == source || dist[v] == inf) { assert(parent[v] == -1 || v != source); continue; }
            int u = parent[v];
            assert(u >= 0);
            bool ok = false;
            for (int e = 0; e < m; ++e) ok |= (from[e] == u && to[e] == v && dist[u] + cost[e] <= dist[v]);
            assert(ok);
        }
    }
    // negative cycles: the result never exceeds the layered value over walks of at most n - 1 edges
    for (int round = 0; round < 3000; ++round) {
        int n = 1 + random() % 7;
        int m = random() % 14;
        std::vector<int> from(m), to(m);
        std::vector<long long> cost(m);
        for (int e = 0; e < m; ++e) {
            from[e] = random() % n;
            to[e] = random() % n;
            cost[e] = (long long)(random() % 21) - 10;
        }
        std::vector<long long> d0(n, inf);
        d0[random() % n] = 0;
        std::vector<long long> layered = d0;
        for (int k = 0; k + 1 < n; ++k) {
            std::vector<long long> next = layered;
            for (int e = 0; e < m; ++e)
                if (layered[from[e]] != inf) next[to[e]] = std::min(next[to[e]], layered[from[e]] + cost[e]);
            layered = next;
        }
        std::vector<long long> dist = d0;
        std::vector<int> parent(n, -1);
        cp::bellman_ford(from, to, cost, dist, parent, n, inf);
        for (int v = 0; v < n; ++v) assert(dist[v] <= layered[v]);
    }
    // n == 1 and no edges leave the array unchanged
    std::vector<int> nf, nt;
    std::vector<long long> nc, one = {0};
    std::vector<int> onep = {-1};
    cp::bellman_ford(nf, nt, nc, one, onep, 1, inf);
    assert(one[0] == 0 && onep[0] == -1);
    // negative cycles: a vertex is marked (-inf, parent -1) iff it is reachable from the source and from a negative cycle that
    // is reachable from the source; every other reached vertex has its shortest distance and a parent edge realising it
    const long long neg = -inf, BIG = 1LL << 50;
    for (int round = 0; round < 20000; ++round) {
        int n = 1 + random() % 7, m = random() % 14;
        std::vector<int> from(m), to(m);
        std::vector<long long> cost(m);
        for (int e = 0; e < m; ++e) {
            from[e] = random() % n;
            to[e] = random() % n;
            cost[e] = (long long)(random() % 15) - 5;
        }
        int s = random() % n;
        std::vector<long long> dist(n, inf);
        std::vector<int> parent(n, -1);
        dist[s] = 0;
        cp::bellman_ford(from, to, cost, dist, parent, n, inf);
        std::vector<std::vector<long long>> fw(n, std::vector<long long>(n, BIG));
        for (int i = 0; i < n; ++i) fw[i][i] = 0;
        for (int e = 0; e < m; ++e) fw[from[e]][to[e]] = std::min(fw[from[e]][to[e]], cost[e]);
        for (int k = 0; k < n; ++k)
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < n; ++j)
                    if (fw[i][k] < BIG && fw[k][j] < BIG) fw[i][j] = std::min(fw[i][j], fw[i][k] + fw[k][j]);
        std::vector<bool> reach(n), cyc(n);
        for (int v = 0; v < n; ++v) reach[v] = fw[s][v] < BIG;
        for (int x = 0; x < n; ++x) {
            std::vector<long long> d(n, BIG);
            d[x] = 0;
            for (int it = 0; it < 3 * n; ++it)
                for (int e = 0; e < m; ++e)
                    if (d[from[e]] < BIG && d[from[e]] > -BIG && d[from[e]] + cost[e] < d[to[e]]) d[to[e]] = d[from[e]] + cost[e];
            cyc[x] = d[x] < 0;
        }
        for (int v = 0; v < n; ++v) {
            if (!reach[v]) {
                assert(dist[v] == inf && parent[v] == -1);
                continue;
            }
            bool marked = false;
            for (int x = 0; x < n; ++x) marked |= (cyc[x] && reach[x] && fw[x][v] < BIG);
            if (marked) {
                assert(dist[v] == neg && parent[v] == -1);
            } else {
                assert(dist[v] == fw[s][v]);
                if (v != s) {
                    int u = parent[v];
                    assert(u >= 0);
                    bool ok = false;
                    for (int e = 0; e < m; ++e) ok |= (from[e] == u && to[e] == v && dist[u] + cost[e] == dist[v]);
                    assert(ok);
                }
            }
        }
    }
    return 0;
}

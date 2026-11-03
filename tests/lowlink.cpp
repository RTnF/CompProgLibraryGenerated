#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/lowlink.hpp"
#include <random>
#include <vector>

// Number of connected components after removing vertex `rv` (-1: none) and the undirected edge {ea, eb} (-1: none).
static int components(int n, const std::vector<std::vector<int>> &adj, int rv, int ea, int eb) {
    std::vector<int> seen(n, 0);
    int count = 0;
    for (int s = 0; s < n; ++s) {
        if (s == rv || seen[s]) continue;
        ++count;
        std::vector<int> stack = {s};
        seen[s] = 1;
        while (!stack.empty()) {
            int v = stack.back();
            stack.pop_back();
            for (int w : adj[v]) {
                if (w == rv || seen[w]) continue;
                if ((v == ea && w == eb) || (v == eb && w == ea)) continue;
                seen[w] = 1;
                stack.push_back(w);
            }
        }
    }
    return count;
}

int main() {
    std::mt19937_64 random(20261013);
    for (int round = 0; round < 6000; ++round) {
        int n = random() % 11;
        std::vector<std::vector<int>> adj(n);
        int tries = n == 0 ? 0 : random() % (2 * n + 2);
        std::vector<std::vector<int>> has(n, std::vector<int>(n, 0));
        for (int e = 0; e < tries; ++e) {
            int u = random() % n, v = random() % n;
            if (u == v || has[u][v]) continue;
            has[u][v] = has[v][u] = 1;
            adj[u].push_back(v);
            adj[v].push_back(u);
        }
        std::vector<int> head(n + 1, 0), target;
        for (int v = 0; v < n; ++v) {
            head[v + 1] = head[v] + (int)adj[v].size();
            for (int w : adj[v]) target.push_back(w);
        }
        std::vector<int> ord(n, -1), low(n, 0), par(n, -1), sep(n, 0), it(n, 0), stk(n, 0);
        cp::lowlink(head, target, ord, low, par, sep, it, stk, n);
        int base = components(n, adj, -1, -1, -1);
        // ord is a permutation of 0..n-1
        std::vector<int> seen(n, 0);
        for (int v = 0; v < n; ++v) {
            assert(0 <= ord[v] && ord[v] < n && !seen[ord[v]]);
            seen[ord[v]] = 1;
            assert(low[v] <= ord[v]);
        }
        for (int v = 0; v < n; ++v) {
            bool art = par[v] < 0 ? sep[v] >= 2 : sep[v] >= 1;
            // removing v also removes it from the count when it is isolated
            bool expected = components(n, adj, v, -1, -1) > base - (adj[v].empty() ? 1 : 0);
            assert(art == expected);
            if (par[v] >= 0) {
                bool bridge = low[v] == ord[v];
                bool exp_bridge = components(n, adj, -1, par[v], v) > base;
                assert(bridge == exp_bridge);
            }
        }
    }
    return 0;
}

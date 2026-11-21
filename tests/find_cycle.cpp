#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/find_cycle.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261014);
    for (int round = 0; round < 8000; ++round) {
        int n = random() % 9;
        int m = n == 0 ? 0 : random() % (2 * n + 2);
        std::vector<std::vector<int>> adj(n);
        for (int e = 0; e < m; ++e) adj[random() % n].push_back(random() % n);
        std::vector<int> head(n + 1, 0), target;
        for (int v = 0; v < n; ++v) {
            head[v + 1] = head[v] + (int)adj[v].size();
            for (int w : adj[v]) target.push_back(w);
        }
        std::vector<int> state(n, 0), it(n, 0), stk(n, 0), cyc(n, 0);
        int k = cp::find_cycle(head, target, state, it, stk, cyc, n);
        // reference: reachability closure
        std::vector<std::vector<int>> reach(n, std::vector<int>(n, 0));
        for (int v = 0; v < n; ++v) for (int w : adj[v]) reach[v][w] = 1;
        for (int c = 0; c < n; ++c)
            for (int a = 0; a < n; ++a)
                for (int b = 0; b < n; ++b)
                    if (reach[a][c] && reach[c][b]) reach[a][b] = 1;
        bool cyclic = false;
        for (int v = 0; v < n; ++v) cyclic = cyclic || reach[v][v];
        assert((k > 0) == cyclic);
        if (k > 0) {
            assert(k <= n);
            std::vector<int> seen(n, 0);
            for (int i = 0; i < k; ++i) {
                assert(0 <= cyc[i] && cyc[i] < n && !seen[cyc[i]]);
                seen[cyc[i]] = 1;
                int a = cyc[i], b = cyc[(i + 1) % k];
                bool arc = false;
                for (int w : adj[a]) arc = arc || w == b;
                assert(arc);
            }
        }
    }
    return 0;
}

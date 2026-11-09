#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/tree/tree_full_dp.hpp"
#include "../library/tree/tree_order.hpp"
#include <algorithm>
#include <cassert>
#include <random>
#include <vector>

// number of vertices on the longest path that starts at v and does not enter `from` (from = -1: no restriction)
static int heightFrom(const std::vector<std::vector<int>> &g, int v, int from) {
    int best = 0;
    for (int w : g[v]) {
        if (w != from) best = std::max(best, heightFrom(g, w, v));
    }
    return best + 1;
}

int main() {
    std::mt19937_64 random(20261028);
    for (int round = 0; round < 3000; ++round) {
        int n = 1 + random() % 12;
        std::vector<std::vector<int>> g(n);
        for (int v = 1; v < n; ++v) {
            int u = random() % v;
            g[u].push_back(v);
            g[v].push_back(u);
        }
        // a random relabelling so that the root is not always 0
        std::vector<int> label(n);
        for (int i = 0; i < n; ++i) label[i] = i;
        std::shuffle(label.begin(), label.end(), random);
        std::vector<std::vector<int>> h(n);
        for (int v = 0; v < n; ++v)
            for (int w : g[v]) h[label[v]].push_back(label[w]);
        for (auto &row : h) std::shuffle(row.begin(), row.end(), random);
        std::vector<int> head(n + 1, 0), target;
        for (int v = 0; v < n; ++v) {
            for (int w : h[v]) target.push_back(w);
            head[v + 1] = (int)target.size();
        }
        int root = random() % n;
        // breadth-first order and parents
        std::vector<int> parent(n, -1), ord;
        parent[root] = root;
        ord.push_back(root);
        for (int i = 0; i < (int)ord.size(); ++i) {
            int v = ord[i];
            for (int w : h[v]) {
                if (parent[w] < 0) {
                    parent[w] = v;
                    ord.push_back(w);
                }
            }
        }
        assert((int)ord.size() == n);
        std::vector<int> generatedOrder(n, -1);
        cp::tree_order(head, target, parent, generatedOrder, root, n);
        assert(generatedOrder == ord);
        int m = (int)target.size();
        std::vector<long long> dp(n, 0), pre(m, 0), suf(m, 0), up(n, 0), full(n, 0);
        cp::tree_full_dp<cp::DpHeight<long long>>(head, target, parent, generatedOrder, dp, pre, suf, up, full, root, n);
        for (int v = 0; v < n; ++v) {
            assert(full[v] == heightFrom(h, v, -1));
            // dp[v]: the subtree of v when the tree is rooted at root
            int from = (v == root) ? -1 : parent[v];
            assert(dp[v] == heightFrom(h, v, from));
            if (v != root) {
                // up[v]: the component of parent[v] when the edge (parent[v], v) is removed, rooted at parent[v]
                assert(up[v] == heightFrom(h, parent[v], v));
            }
        }
        assert(up[root] == 0);
    }
    return 0;
}

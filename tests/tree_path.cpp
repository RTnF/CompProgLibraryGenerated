#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/tree_path.hpp"
#include "../library/tree_root.hpp"
#include <random>
#include <vector>

// The reference: Tree::path of experiments/library/cpp/tree/tree.hpp (a depth-first search from `from`).
static std::vector<int> original_path(const std::vector<std::vector<int>> &adj, int from, int to) {
    int n = adj.size();
    std::stack<int> s;
    s.emplace(from);
    std::vector<int> path_parent(n, -1);
    path_parent[from] = from;
    while (s.size()) {
        int node = s.top();
        if (node == to) {
            std::vector<int> path;
            for (int i = node; i != path_parent[i]; i = path_parent[i]) path.emplace_back(i);
            path.emplace_back(from);
            return path;
        }
        s.pop();
        for (auto &&e : adj[node]) {
            if (path_parent[e] == -1) {
                path_parent[e] = node;
                s.emplace(e);
            }
        }
    }
    return {};
}

int main() {
    std::mt19937_64 random(20261107);
    for (int round = 0; round < 20000; ++round) {
        int n = 1 + random() % 14;
        std::vector<std::vector<int>> adj(n);
        std::vector<int> label(n);
        for (int i = 0; i < n; ++i) label[i] = i;
        for (int i = n - 1; i > 0; --i) std::swap(label[i], label[random() % (i + 1)]);
        for (int i = 1; i < n; ++i) {
            int p = random() % i;
            adj[label[i]].push_back(label[p]);
            adj[label[p]].push_back(label[i]);
        }
        for (auto &a : adj) std::shuffle(a.begin(), a.end(), random);
        std::vector<int> head(n + 1, 0), target;
        for (int v = 0; v < n; ++v) {
            head[v + 1] = head[v] + (int)adj[v].size();
            for (int u : adj[v]) target.push_back(u);
        }
        std::vector<long long> cost(target.size(), 1), cost_depth(n, 0);
        int from = random() % n, to = random() % n;
        std::vector<int> parent(n, -1), depth(n, 0), stk(n + 1, 0);
        cp::tree_root(head, target, cost, parent, depth, cost_depth, stk, from, n);
        int slack = random() % 3;
        std::vector<int> out(depth[to] + 1 + slack, -7);
        int len = cp::tree_path(parent, out, from, to);
        std::vector<int> expected = original_path(adj, from, to);
        assert(len == depth[to] + 1);
        assert(len == (int)expected.size());
        for (int i = 0; i < len; ++i) assert(out[i] == expected[i]);
        assert(out[0] == to && out[len - 1] == from);
        for (int i = 0; i + 1 < len; ++i) assert(out[i + 1] == parent[out[i]]);
        for (int i = len; i < (int)out.size(); ++i) assert(out[i] == -7);  // the rest is untouched
    }
    return 0;
}

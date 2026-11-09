#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/tree/tree_root.hpp"
#include <random>
#include <vector>

// Builds CSR arrays from adjacency lists of (target, cost).
static void build_csr(const std::vector<std::vector<std::pair<int, long long>>> &adj, std::vector<int> &head,
                      std::vector<int> &target, std::vector<long long> &cost) {
    int n = adj.size();
    head.assign(n + 1, 0);
    target.clear();
    cost.clear();
    for (int v = 0; v < n; ++v) {
        head[v + 1] = head[v] + (int)adj[v].size();
        for (auto &e : adj[v]) {
            target.push_back(e.first);
            cost.push_back(e.second);
        }
    }
}

int main() {
    std::mt19937_64 random(20261029);
    // symmetric random trees: parent, depth and cost_depth agree with the path from the root
    for (int round = 0; round < 4000; ++round) {
        int n = 1 + random() % 12;
        std::vector<std::vector<std::pair<int, long long>>> adj(n);
        std::vector<int> label(n);
        for (int i = 0; i < n; ++i) label[i] = i;
        for (int i = n - 1; i > 0; --i) std::swap(label[i], label[random() % (i + 1)]);
        for (int i = 1; i < n; ++i) {
            int p = random() % i;
            long long c = (long long)(random() % 2001) - 1000;
            adj[label[i]].push_back({label[p], c});
            adj[label[p]].push_back({label[i], c});
        }
        for (auto &a : adj) std::shuffle(a.begin(), a.end(), random);
        std::vector<int> head, target;
        std::vector<long long> cost;
        build_csr(adj, head, target, cost);
        int root = random() % n;
        std::vector<int> parent(n, -1), depth(n, 7), stk(n + 1, 5);
        std::vector<long long> cost_depth(n, 9);
        cp::tree_root(head, target, cost, parent, depth, cost_depth, stk, root, n);
        assert(parent[root] == root && depth[root] == 0 && cost_depth[root] == 0);
        // reference: a plain recursive search
        std::vector<int> rp(n, -1), rd(n, 0);
        std::vector<long long> rc(n, 0);
        rp[root] = root;
        std::vector<int> order = {root};
        for (size_t i = 0; i < order.size(); ++i) {
            int v = order[i];
            for (auto &e : adj[v])
                if (rp[e.first] == -1) {
                    rp[e.first] = v;
                    rd[e.first] = rd[v] + 1;
                    rc[e.first] = rc[v] + e.second;
                    order.push_back(e.first);
                }
        }
        for (int v = 0; v < n; ++v) {
            assert(parent[v] == rp[v] && depth[v] == rd[v] && cost_depth[v] == rc[v]);
        }
        // the farthest vertex as the original computes it: the first popped vertex of the largest cost_depth
        {
            std::vector<char> seen(n, 0);
            std::vector<std::pair<int, long long>> st;
            long long max_cost = -1;
            int farthest = -1;
            st.push_back({root, 0});
            seen[root] = 1;
            while (!st.empty()) {
                auto [node, dc] = st.back();
                st.pop_back();
                if (max_cost < dc) {
                    max_cost = dc;
                    farthest = node;
                }
                for (auto &e : adj[node])
                    if (!seen[e.first]) {
                        seen[e.first] = 1;
                        st.push_back({e.first, dc + e.second});
                    }
            }
            assert(stk[n] == farthest);
        }
    }
    // arbitrary directed graphs: reachability and the edge relations of the specification
    for (int round = 0; round < 4000; ++round) {
        int n = 1 + random() % 9;
        int m = random() % 25;
        std::vector<std::vector<std::pair<int, long long>>> adj(n);
        for (int e = 0; e < m; ++e) {
            int u = random() % n, v = random() % n;
            adj[u].push_back({v, (long long)(random() % 2001) - 1000});
        }
        std::vector<int> head, target;
        std::vector<long long> cost;
        build_csr(adj, head, target, cost);
        int root = random() % n;
        std::vector<int> parent(n, -1), depth(n, 3), stk(n + 1, 4);
        std::vector<long long> cost_depth(n, 11);
        cp::tree_root(head, target, cost, parent, depth, cost_depth, stk, root, n);
        std::vector<std::vector<char>> reach(n, std::vector<char>(n, 0));
        for (int v = 0; v < n; ++v) reach[v][v] = 1;
        for (int u = 0; u < n; ++u)
            for (auto &e : adj[u]) reach[u][e.first] = 1;
        for (int t = 0; t < n; ++t)
            for (int a = 0; a < n; ++a)
                for (int b = 0; b < n; ++b)
                    if (reach[a][t] && reach[t][b]) reach[a][b] = 1;
        assert(parent[root] == root && depth[root] == 0 && cost_depth[root] == 0);
        for (int v = 0; v < n; ++v) {
            assert((parent[v] >= 0) == (bool)reach[root][v]);
            if (parent[v] < 0 || v == root) continue;
            int u = parent[v];
            assert(0 <= u && u < n && parent[u] >= 0);
            bool found = false;  // some arc u -> v with the right cost difference
            for (int p = head[u]; p < head[u + 1]; ++p)
                if (target[p] == v && depth[v] == depth[u] + 1 && cost_depth[v] == cost_depth[u] + cost[p]) found = true;
            assert(found);
            assert(0 <= depth[v] && depth[v] < n);
        }
        // the farthest vertex is reachable and has the largest cost_depth among the reachable vertices
        int far = stk[n];
        assert(0 <= far && far < n && reach[root][far]);
        for (int v = 0; v < n; ++v)
            if (reach[root][v]) assert(cost_depth[v] <= cost_depth[far]);
    }
    return 0;
}

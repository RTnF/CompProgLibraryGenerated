#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/tree_order.hpp"
#include <algorithm>
#include <cassert>
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261029);
    for (int round = 0; round < 3000; ++round) {
        int n = 1 + random() % 14;
        std::vector<std::vector<int>> h(n);
        std::vector<int> label(n);
        for (int i = 0; i < n; ++i) label[i] = i;
        std::shuffle(label.begin(), label.end(), random);
        for (int v = 1; v < n; ++v) {
            int u = random() % v;
            h[label[u]].push_back(label[v]);
            h[label[v]].push_back(label[u]);
        }
        for (auto &row : h) std::shuffle(row.begin(), row.end(), random);
        std::vector<int> head(n + 1, 0), target;
        for (int v = 0; v < n; ++v) {
            for (int w : h[v]) target.push_back(w);
            head[v + 1] = (int)target.size();
        }
        int root = random() % n;
        // parent array of the tree rooted at root (depth-first, as tree_root writes it)
        std::vector<int> parent(n, -1), stack;
        parent[root] = root;
        stack.push_back(root);
        while (!stack.empty()) {
            int v = stack.back();
            stack.pop_back();
            for (int w : h[v]) {
                if (parent[w] < 0) {
                    parent[w] = v;
                    stack.push_back(w);
                }
            }
        }
        std::vector<int> ord(n);
        for (auto &x : ord) x = (int)(random() % 1000) - 500;  // arbitrary contents on entry
        cp::tree_order(head, target, parent, ord, root, n);
        assert(ord[0] == root);
        std::vector<int> position(n, -1);
        for (int j = 0; j < n; ++j) {
            assert(0 <= ord[j] && ord[j] < n);
            assert(position[ord[j]] < 0);  // a permutation
            position[ord[j]] = j;
        }
        for (int v = 0; v < n; ++v) {
            if (v != root) assert(position[parent[v]] < position[v]);
        }
    }
    return 0;
}

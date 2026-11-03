#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/segtree_sum.hpp"
#include <climits>
#include <random>
#include <vector>


// Builds the layout: node.size() == 2 * n, leaves node[n + i], node[i] = node[2i] + node[2i+1] (mod 2^64).
static std::vector<unsigned long long> build(const std::vector<unsigned long long> &leaves) {
    int n = (int)leaves.size();
    std::vector<unsigned long long> node(2 * n, 0);
    for (int i = 0; i < n; ++i) node[n + i] = leaves[i];
    for (int i = n - 1; i >= 1; --i) node[i] = node[2 * i] + node[2 * i + 1];
    return node;
}

int main() {
    std::mt19937_64 random(20261020);
    for (int n = 1; n <= 40; ++n) {  // every size, not only powers of two
        std::vector<unsigned long long> leaves(n);
        for (unsigned long long &x : leaves) x = (random() % 3 == 0) ? ULLONG_MAX - random() % 5 : random();
        std::vector<unsigned long long> node = build(leaves);
        for (int l = 0; l <= n; ++l)
            for (int r = l; r <= n; ++r) {
                unsigned long long expected = 0;
                for (int i = l; i < r; ++i) expected += leaves[i];
                assert(cp::segtree_sum_product(node, l, r) == expected);
            }
        for (int round = 0; round < 30; ++round) {
            int idx = (int)(random() % n);
            unsigned long long val = random();
            leaves[idx] = val;
            cp::segtree_sum_set(node, idx, val);
            assert(node == build(leaves));
            int l = (int)(random() % (n + 1)), r = (int)(random() % (n + 1));
            if (l > r) std::swap(l, r);
            unsigned long long expected = 0;
            for (int i = l; i < r; ++i) expected += leaves[i];
            assert(cp::segtree_sum_product(node, l, r) == expected);
        }
    }
    // a large tree
    int n = 1 << 17;
    std::vector<unsigned long long> leaves(n);
    for (unsigned long long &x : leaves) x = random();
    std::vector<unsigned long long> node = build(leaves);
    for (int round = 0; round < 1000; ++round) {
        int idx = (int)(random() % n);
        leaves[idx] = random();
        cp::segtree_sum_set(node, idx, leaves[idx]);
    }
    assert(node == build(leaves));
    // the element type is a template parameter
    {
        std::vector<unsigned> node(8, 0);
        for (int i = 0; i < 4; ++i) cp::segtree_sum_set(node, i, (unsigned)(i + 1));
        assert(cp::segtree_sum_product(node, 1, 4) == 9u);
    }
    return 0;
}

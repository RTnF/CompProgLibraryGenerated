#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/union_find/union_find.hpp"
#include <random>
#include <vector>

// A naive model: component labels with relabelling on every union.
struct Naive {
    std::vector<int> label;
    explicit Naive(int n) : label(n) {
        for (int i = 0; i < n; ++i) label[i] = i;
    }
    bool same(int a, int b) const { return label[a] == label[b]; }
    int size(int a) const {
        int count = 0;
        for (int l : label) count += l == label[a];
        return count;
    }
    int groups() const {
        int count = 0;
        for (int i = 0; i < (int)label.size(); ++i) count += label[i] == i;
        return count;
    }
    bool unite(int a, int b) {
        const int from = label[a], to = label[b];
        if (from == to) return false;
        for (int &l : label)
            if (l == from) l = to;
        return true;
    }
};

int main() {
    std::mt19937 random(20261011);
    // The default-constructed structure has no element and no group.
    cp::UnionFind empty;
    assert(empty.num_groups() == 0);
    cp::UnionFind zero(0);
    assert(zero.num_groups() == 0);
    // Random operations against the naive model, for many sizes.
    for (int n : {1, 2, 3, 4, 5, 7, 8, 40, 500}) {
        cp::UnionFind uf(n);
        Naive naive(n);
        assert(uf.num_groups() == n);
        for (int i = 0; i < n; ++i) assert(uf.root(i) == i && uf.size(i) == 1);
        for (int step = 0; step < 6 * n; ++step) {
            const int a = static_cast<int>(random() % n), b = static_cast<int>(random() % n);
            const bool same_before = uf.same(a, b);
            assert(same_before == naive.same(a, b));
            const int root_a = uf.root(a), root_b = uf.root(b);
            assert((root_a == root_b) == same_before);
            const int groups_before = uf.num_groups();
            const int result = uf.unite(a, b);
            const bool merged = naive.unite(a, b);
            // unite returns the root of the merged tree and the tree count drops by one exactly when two trees merge
            assert(result == uf.root(a) && result == uf.root(b));
            assert(uf.num_groups() == groups_before - (merged ? 1 : 0));
            assert(uf.num_groups() == naive.groups());
            assert(uf.same(a, b));
            if (step % 5 == 0)
                for (int i = 0; i < n; ++i) {
                    assert(uf.same(i, a) == naive.same(i, a));
                    assert(uf.size(i) == naive.size(i));
                }
        }
        for (int i = 0; i < n; ++i) {
            assert(uf.size(i) == naive.size(i));
            assert(uf.size(i) == uf.size(uf.root(i)));
            assert(uf.root(uf.root(i)) == uf.root(i));
        }
    }
    // Union by size: chaining n elements one after another keeps every call cheap, and the sizes add up.
    const int big = 200000;
    cp::UnionFind chain(big);
    for (int i = 1; i < big; ++i) chain.unite(i - 1, i);
    assert(chain.num_groups() == 1 && chain.size(0) == big && chain.same(0, big - 1));
    cp::UnionFind sparse(big);
    for (int t = 0; t < 3 * big; ++t) sparse.unite(static_cast<int>(random() % big), static_cast<int>(random() % big));
    int total = 0;
    for (int i = 0; i < big; ++i)
        if (sparse.root(i) == i) total += sparse.size(i);
    assert(total == big);
    return 0;
}

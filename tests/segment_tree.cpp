#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/segment_tree.hpp"
#include <climits>
#include <random>
#include <vector>

// The original SegmentTree of experiments/library/cpp/segment_tree/segment_tree.hpp (product, set, get, product_all), with the
// monoid MonoidMax<long long> written out, as the reference.
struct MonoidMaxRef {
    long long x;
    MonoidMaxRef(long long x_) : x(x_) {}
    MonoidMaxRef() : MonoidMaxRef(e()) {}
    static MonoidMaxRef e() { return std::numeric_limits<long long>::min(); }
    friend MonoidMaxRef op(const MonoidMaxRef &a, const MonoidMaxRef &b) { return std::max(a.x, b.x); }
};

struct MonoidMinRef {
    long long x;
    MonoidMinRef(long long x_) : x(x_) {}
    MonoidMinRef() : MonoidMinRef(e()) {}
    static MonoidMinRef e() { return std::numeric_limits<long long>::max(); }
    friend MonoidMinRef op(const MonoidMinRef &a, const MonoidMinRef &b) { return std::min(a.x, b.x); }
};

template <class M> class OriginalSegmentTree {
    int n, n_node, h_node;
    std::vector<M> node;
    void update(int i) { node[i] = op(node[i * 2], node[i * 2 + 1]); }

public:
    OriginalSegmentTree(const std::vector<M> &v) : n(v.size()) {
        h_node = 0;
        n_node = 0;
        while (n_node < n) {
            h_node++;
            n_node = 1 << h_node;
        }
        node = std::vector<M>(n_node * 2, M::e());
        for (int i = 0; i < n; i++) node[n_node + i] = v[i];
        for (int i = n_node - 1; i >= 1; i--) update(i);
    }
    void set(int idx, M val) {
        idx += n_node;
        node[idx] = val;
        for (int i = 1; i <= h_node; i++) update(idx >> i);
    }
    M get(int idx) { return node[idx + n_node]; }
    M product(int l, int r) {
        M l_op = M::e(), r_op = M::e();
        l += n_node;
        r += n_node;
        while (l < r) {
            if (l & 1) l_op = op(l_op, node[l++]);
            if (r & 1) r_op = op(node[--r], r_op);
            l >>= 1;
            r >>= 1;
        }
        return op(l_op, r_op);
    }
    M product_all() { return node[1]; }
};

static long long random_value(std::mt19937_64 &random) {
    switch (random() % 8) {
    case 0: return LLONG_MIN;
    case 1: return LLONG_MAX;
    case 2: return 0;
    default: return (long long)(random() % 2001) - 1000;
    }
}

int main() {
    std::mt19937_64 random(20261110);
    for (int n = 1; n <= 80; ++n) {
        std::vector<long long> a(n);
        for (auto &x : a) x = random_value(random);
        std::vector<MonoidMaxRef> ra(a.begin(), a.end());
        cp::SegmentTree<cp::SegMax<long long>> tree(a);
        OriginalSegmentTree<MonoidMaxRef> original(ra);
        for (int step = 0; step < 200; ++step) {
            if (random() % 2 == 0) {
                const int idx = random() % n;
                const long long val = random_value(random);
                a[idx] = val;
                tree.set(idx, val);
                original.set(idx, MonoidMaxRef(val));
            }
            int l = random() % (n + 1), r = random() % (n + 1);
            if (l > r) std::swap(l, r);
            long long expected = LLONG_MIN;
            for (int j = l; j < r; ++j) expected = std::max(expected, a[j]);
            assert(tree.product(l, r) == expected);
            assert(original.product(l, r).x == expected);
            const int idx = random() % n;
            assert(tree.get(idx) == a[idx] && original.get(idx).x == a[idx]);
            long long all = LLONG_MIN;
            for (int j = 0; j < n; ++j) all = std::max(all, a[j]);
            assert(tree.product_all() == all && original.product_all().x == all);
        }
        // every interval
        for (int l = 0; l <= n; ++l)
            for (int r = l; r <= n; ++r) {
                long long expected = LLONG_MIN;
                for (int j = l; j < r; ++j) expected = std::max(expected, a[j]);
                assert(tree.product(l, r) == expected);
            }
    }
    // the minimum
    for (int n = 1; n <= 80; ++n) {
        std::vector<long long> a(n);
        for (auto &x : a) x = random_value(random);
        std::vector<MonoidMinRef> ra(a.begin(), a.end());
        cp::SegmentTree<cp::SegMin<long long>> tree(a);
        OriginalSegmentTree<MonoidMinRef> original(ra);
        for (int step = 0; step < 200; ++step) {
            if (random() % 2 == 0) {
                const int idx = random() % n;
                const long long val = random_value(random);
                a[idx] = val;
                tree.set(idx, val);
                original.set(idx, MonoidMinRef(val));
            }
            int l = random() % (n + 1), r = random() % (n + 1);
            if (l > r) std::swap(l, r);
            long long expected = LLONG_MAX;
            for (int j = l; j < r; ++j) expected = std::min(expected, a[j]);
            assert(tree.product(l, r) == expected);
            assert(original.product(l, r).x == expected);
            const int idx = random() % n;
            assert(tree.get(idx) == a[idx] && original.get(idx).x == a[idx]);
            long long all = LLONG_MAX;
            for (int j = 0; j < n; ++j) all = std::min(all, a[j]);
            assert(tree.product_all() == all && original.product_all().x == all);
        }
    }
    // a larger tree (2^16 + 1 leaves)
    const int big = (1 << 16) + 1;
    std::vector<long long> a(big);
    for (auto &x : a) x = random_value(random);
    cp::SegmentTree<cp::SegMax<long long>> tree(a);
    for (int step = 0; step < 2000; ++step) {
        const int idx = random() % big;
        a[idx] = random_value(random);
        tree.set(idx, a[idx]);
        int l = random() % (big + 1), r = random() % (big + 1);
        if (l > r) std::swap(l, r);
        long long expected = LLONG_MIN;
        for (int j = l; j < r; j += 1 + (r - l) / 50) expected = std::max(expected, a[j]);
        assert(tree.product(l, r) >= expected);
    }
    return 0;
}

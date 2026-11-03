#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/lazy_segment_tree.hpp"
#include <cassert>
#include <climits>
#include <random>
#include <vector>

// The original LazySegmentTree of experiments/library/cpp/segment_tree/lazy_segment_tree.hpp (set, get, product, product_all,
// both updates), with the monoid "maximum" and the action "chmin" written out, as the reference.
struct MaxRef {
    long long x;
    MaxRef(long long x_) : x(x_) {}
    MaxRef() : MaxRef(e()) {}
    static MaxRef e() { return std::numeric_limits<long long>::min(); }
    friend MaxRef op(const MaxRef &a, const MaxRef &b) { return std::max(a.x, b.x); }
};

struct ChminRef {
    long long c;
    ChminRef(long long c_) : c(c_) {}
    ChminRef() : ChminRef(id()) {}
    static ChminRef id() { return std::numeric_limits<long long>::max(); }
    MaxRef apply(const MaxRef &m) const { return std::min(c, m.x); }
    friend ChminRef compose(const ChminRef &f, const ChminRef &g) { return std::min(f.c, g.c); }
};

template <class M, class F> class OriginalLazySegmentTree {
    int n, n_node, h_node;
    std::vector<M> node;
    std::vector<F> lazy;
    void update(int i) { node[i] = op(node[i * 2], node[i * 2 + 1]); }
    void all_apply(int k, F f) {
        node[k] = f.apply(node[k]);
        if (k < n_node) lazy[k] = compose(f, lazy[k]);
    }
    void push(int k) {
        all_apply(2 * k, lazy[k]);
        all_apply(2 * k + 1, lazy[k]);
        lazy[k] = F::id();
    }

public:
    OriginalLazySegmentTree(const std::vector<M> &v) : n(v.size()) {
        h_node = 0;
        n_node = 0;
        while (n_node < n) {
            h_node++;
            n_node = 1 << h_node;
        }
        node = std::vector<M>(n_node * 2, M::e());
        lazy = std::vector<F>(n_node, F::id());
        for (int i = 0; i < n; i++) node[n_node + i] = v[i];
        for (int i = n_node - 1; i >= 1; i--) update(i);
    }
    void set(int idx, M val) {
        idx += n_node;
        for (int i = h_node; i >= 1; i--) push(idx >> i);
        node[idx] = val;
        for (int i = 1; i <= h_node; i++) update(idx >> i);
    }
    M get(int idx) {
        idx += n_node;
        for (int i = h_node; i >= 1; i--) push(idx >> i);
        return node[idx];
    }
    M product(int l, int r) {
        if (l == r) return M::e();
        l += n_node;
        r += n_node;
        for (int i = h_node; i >= 1; i--) {
            if (((l >> i) << i) != l) push(l >> i);
            if (((r >> i) << i) != r) push((r - 1) >> i);
        }
        M l_op = M::e(), r_op = M::e();
        while (l < r) {
            if (l & 1) l_op = op(l_op, node[l++]);
            if (r & 1) r_op = op(node[--r], r_op);
            l >>= 1;
            r >>= 1;
        }
        return op(l_op, r_op);
    }
    M product_all() { return node[1]; }
    void update(int idx, F f) {
        idx += n_node;
        for (int i = h_node; i >= 1; i--) push(idx >> i);
        node[idx] = f.apply(node[idx]);
        for (int i = 1; i <= h_node; i++) update(idx >> i);
    }
    void update(int l, int r, F f) {
        if (l == r) return;
        l += n_node;
        r += n_node;
        for (int i = h_node; i >= 1; i--) {
            if (((l >> i) << i) != l) push(l >> i);
            if (((r >> i) << i) != r) push((r - 1) >> i);
        }
        {
            int l2 = l, r2 = r;
            while (l < r) {
                if (l & 1) all_apply(l++, f);
                if (r & 1) all_apply(--r, f);
                l >>= 1;
                r >>= 1;
            }
            l = l2;
            r = r2;
        }
        for (int i = 1; i <= h_node; i++) {
            if (((l >> i) << i) != l) update(l >> i);
            if (((r >> i) << i) != r) update((r - 1) >> i);
        }
    }
};

static long long random_value(std::mt19937_64 &random) {
    switch (random() % 8) {
    case 0: return LLONG_MIN;
    case 1: return LLONG_MAX;
    case 2: return 0;
    default: return (long long)(random() % 2001) - 1000;
    }
}

using Policy = cp::LazyChminMax<long long>;

int main() {
    // the policy
    assert(Policy::e() == LLONG_MIN && Policy::id() == LLONG_MAX);
    for (long long a : {LLONG_MIN, -5LL, 0LL, 7LL, LLONG_MAX})
        for (long long b : {LLONG_MIN, -5LL, 0LL, 7LL, LLONG_MAX}) {
            assert(Policy::op(a, b) == std::max(a, b));
            assert(Policy::mapping(a, b) == std::min(a, b));
            assert(Policy::composition(a, b) == std::min(a, b));
            assert(Policy::mapping(Policy::id(), b) == b);
            for (long long c : {LLONG_MIN, 3LL, LLONG_MAX}) {
                assert(Policy::mapping(c, Policy::op(a, b)) == Policy::op(Policy::mapping(c, a), Policy::mapping(c, b)));
                assert(Policy::mapping(Policy::composition(c, a), b) == Policy::mapping(c, Policy::mapping(a, b)));
            }
        }
    std::mt19937_64 random(20261111);
    for (int n = 1; n <= 80; ++n) {
        std::vector<long long> a(n);
        for (auto &x : a) x = random_value(random);
        std::vector<MaxRef> ra(a.begin(), a.end());
        cp::LazySegmentTree<Policy> tree(a);
        OriginalLazySegmentTree<MaxRef, ChminRef> original(ra);
        for (int step = 0; step < 300; ++step) {
            switch (random() % 4) {
            case 0: {
                const int idx = random() % n;
                const long long val = random_value(random);
                a[idx] = val;
                tree.set(idx, val);
                original.set(idx, MaxRef(val));
                break;
            }
            case 1: {
                const int idx = random() % n;
                const long long f = random_value(random);
                a[idx] = std::min(f, a[idx]);
                tree.update(idx, f);
                original.update(idx, ChminRef(f));
                break;
            }
            case 2: {
                int l = random() % (n + 1), r = random() % (n + 1);
                if (l > r) std::swap(l, r);
                const long long f = random_value(random);
                for (int j = l; j < r; ++j) a[j] = std::min(f, a[j]);
                tree.update(l, r, f);
                original.update(l, r, ChminRef(f));
                break;
            }
            default: break;
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
        // every interval, after a whole-array and an empty-range update
        tree.update(0, n, LLONG_MAX);
        tree.update(n / 2, n / 2, LLONG_MIN);
        for (int l = 0; l <= n; ++l)
            for (int r = l; r <= n; ++r) {
                long long expected = LLONG_MIN;
                for (int j = l; j < r; ++j) expected = std::max(expected, a[j]);
                assert(tree.product(l, r) == expected);
            }
    }
    // a larger tree (2^16 + 1 leaves)
    const int big = (1 << 16) + 1;
    std::vector<long long> a(big);
    for (auto &x : a) x = random_value(random);
    cp::LazySegmentTree<Policy> tree(a);
    for (int step = 0; step < 2000; ++step) {
        int l = random() % (big + 1), r = random() % (big + 1);
        if (l > r) std::swap(l, r);
        const long long f = random_value(random);
        if (step % 2 == 0) {
            for (int j = l; j < r; ++j) a[j] = std::min(f, a[j]);
            tree.update(l, r, f);
        }
        int ql = random() % (big + 1), qr = random() % (big + 1);
        if (ql > qr) std::swap(ql, qr);
        long long expected = LLONG_MIN;
        for (int j = ql; j < qr; ++j) expected = std::max(expected, a[j]);
        assert(tree.product(ql, qr) == expected);
        const int idx = random() % big;
        assert(tree.get(idx) == a[idx]);
    }
    return 0;
}

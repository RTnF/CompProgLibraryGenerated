#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/segment_tree_beats.hpp"
#include <cassert>
#include <climits>
#include <random>
#include <vector>

// Random operations (chmin, chmax, add_val, update_val, calc_max, calc_min) against a plain array. The values stay far
// from the sentinel +-4e18 of the structure.
int main() {
    std::mt19937_64 rng(1);
    for (int round = 0; round < 3000; ++round) {
        int n = 1 + rng() % 40;
        std::vector<long long> a(n);
        for (auto &x : a) x = (long long)(rng() % 41) - 20;
        cp::SegmentTreeBeats t(a);
        std::vector<long long> ref = a;
        for (int op = 0; op < 60; ++op) {
            int l = rng() % (n + 1), r = rng() % (n + 1);
            if (l > r) std::swap(l, r);
            long long x = (long long)(rng() % 41) - 20;
            int kind = rng() % 6;
            if (kind == 0) {
                t.chmin(l, r, x);
                for (int i = l; i < r; ++i) ref[i] = std::min(ref[i], x);
            } else if (kind == 1) {
                t.chmax(l, r, x);
                for (int i = l; i < r; ++i) ref[i] = std::max(ref[i], x);
            } else if (kind == 2) {
                t.add_val(l, r, x);
                for (int i = l; i < r; ++i) ref[i] += x;
            } else if (kind == 3) {
                t.update_val(l, r, x);
                for (int i = l; i < r; ++i) ref[i] = x;
            } else {
                long long mx = t.calc_max(l, r), mn = t.calc_min(l, r);
                long long em = -4000000000000000000LL, en = 4000000000000000000LL;
                for (int i = l; i < r; ++i) em = std::max(em, ref[i]), en = std::min(en, ref[i]);
                assert(mx == em && mn == en);
            }
        }
    }
    // Large values: sums of additions stay below the sentinel.
    {
        std::vector<long long> a = {1000000000000LL, -1000000000000LL, 5, 7};
        cp::SegmentTreeBeats t(a);
        t.add_val(0, 4, 1000000000000LL);
        assert(t.calc_max(0, 4) == 2000000000000LL && t.calc_min(0, 4) == 0);
        t.chmin(0, 4, 100);
        assert(t.calc_max(0, 4) == 100 && t.calc_min(0, 4) == 0);
    }
    return 0;
}

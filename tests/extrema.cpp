#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/extrema.hpp"
#include <climits>
#include <cstdint>
#include <random>

int main() {
    const long long values[] = {LLONG_MIN, LLONG_MIN + 1, -3, -1, 0, 1, 2, 5, LLONG_MAX - 1, LLONG_MAX};
    for (long long a0 : values)
        for (long long b0 : values) {
            long long a = a0;
            const long long b = b0;
            const bool raised = cp::chmax(a, b);
            assert(a == std::max(a0, b0));
            assert(raised == (a0 < b0));
            long long c = a0;
            const bool lowered = cp::chmin(c, b);
            assert(c == std::min(a0, b0));
            assert(lowered == (b0 < a0));
        }
    // `a` and `b` may be the same object.
    for (long long v : values) {
        long long x = v;
        assert(!cp::chmax(x, x) && x == v);
        assert(!cp::chmin(x, x) && x == v);
    }
    // A running maximum and minimum over a random sequence, and the change flags.
    std::mt19937_64 random(20261008);
    long long hi = LLONG_MIN, lo = LLONG_MAX;
    for (int i = 0; i < 100000; ++i) {
        const long long v = static_cast<long long>(random());
        const bool up = cp::chmax(hi, v);
        const bool down = cp::chmin(lo, v);
        assert(hi >= v && lo <= v);
        (void)up;
        (void)down;
    }
    // the types are template parameters: mixed and unsigned types work the same way
    int small = 3;
    assert(cp::chmax(small, 7LL) && small == 7 && !cp::chmax(small, 5LL) && small == 7);
    unsigned u = 5;
    assert(cp::chmin(u, 2u) && u == 2u && !cp::chmin(u, 9u));
    double d = 1.5;
    assert(cp::chmax(d, 2.5) && d == 2.5);
    return 0;
}

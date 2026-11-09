#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/modint/modint.hpp"
#include <cstdint>
#include <random>

using mint = cp::ModInt<998244353u>;
using mint17 = cp::ModInt<1000000007u>;

// Independent oracles over plain integers.
unsigned long long oracle_pow(unsigned long long base, unsigned long long exp, unsigned long long m) {
    unsigned long long result = 1 % m;
    base %= m;
    while (exp) {
        if (exp & 1) result = static_cast<unsigned long long>(static_cast<__uint128_t>(result) * base % m);
        base = static_cast<unsigned long long>(static_cast<__uint128_t>(base) * base % m);
        exp >>= 1;
    }
    return result;
}

template <class M, unsigned int m> void check_all(std::mt19937_64 &random) {
    const long long specials[] = {0, 1, 2, -1, -2, (long long)m - 1, (long long)m, (long long)m + 1, -(long long)m,
                                  -(long long)m - 1, 2LL * m, -2LL * m, (long long)1e18, -(long long)1e18,
                                  INT64_MAX, INT64_MIN};
    for (long long v : specials) {
        const M a(v);
        long long expected = v % (long long)m;
        if (expected < 0) expected += m;
        assert(a.get() == (unsigned)expected);  // includes negative multiples of m, which the original left at m
        assert(a.get() < m);
    }
    assert(M().get() == 0);
    for (int i = 0; i < 20000; ++i) {
        const long long u = (long long)(random() % m), v = (long long)(random() % m);
        const M a(u), b(v);
        M c = a;
        c += b;
        assert(c.get() == (u + v) % m);
        c = a;
        c -= b;
        assert(c.get() == (u - v + m) % m);
        c = a;
        c *= b;
        assert(c.get() == (unsigned)((unsigned long long)u * v % m));
        c = a;
        c += c;  // aliasing: both operands are the same object
        assert(c.get() == (2 * u) % m);
        c = a;
        c *= c;
        assert(c.get() == (unsigned)((unsigned long long)u * u % m));
        c = a;
        c -= c;
        assert(c.get() == 0);
        // the binary operators (free function templates, verified for both moduli)
        assert((a + b).get() == (u + v) % m);
        assert((a - b).get() == (u + m - v) % m);
        assert((a * b).get() == (unsigned)((unsigned long long)u * v % m));
        assert((a + a).get() == (2 * u) % m && (a - a).get() == 0);
        assert((-a).get() == (u == 0 ? 0u : m - (unsigned)u));
        assert((a == b) == (u == v));
        assert((a != b) == (u != v));
        M d = a;
        ++d;
        assert(d.get() == (u + 1) % m);
        d = a;
        --d;
        assert(d.get() == (u + m - 1) % m);
        const unsigned long long e = random() >> (random() % 64);
        assert(a.pow(e).get() == oracle_pow(u, e, m));
    }
    assert(M(0).pow(0).get() == 1);
    assert(M(5).pow(0).get() == 1);
    assert(M(0).pow(5).get() == 0);
    assert(M(2).pow(~0ull).get() == oracle_pow(2, ~0ull, m));
    // Fermat: a^(m-1) = 1 for the prime moduli.
    for (int i = 0; i < 100; ++i) {
        const M a(1 + (long long)(random() % (m - 1)));
        assert(a.pow(m - 1).get() == 1);
        const M inverse = a.inv();
        M product = a;
        product *= inverse;
        assert(product.get() == 1);
        assert(inverse.get() == a.pow(m - 2).get());
        // division: (b / a) * a == b, and b / a == b * inverse
        const M b(static_cast<long long>(random()));
        M quotient = b;
        quotient /= a;
        M check = quotient;
        check *= a;
        assert(check.get() == b.get());
        M viaInverse = b;
        viaInverse *= inverse;
        assert(quotient.get() == viaInverse.get());
        M self = a;
        self /= a;
        assert(self.get() == 1);
        // the binary operator / (verified for both moduli)
        assert((b / a).get() == quotient.get());
        assert((a / a).get() == 1);
        assert(((b / a) * a).get() == b.get());
    }
}

int main() {
    std::mt19937_64 random(20261008);
    check_all<mint, 998244353u>(random);
    check_all<mint17, 1000000007u>(random);
    return 0;
}

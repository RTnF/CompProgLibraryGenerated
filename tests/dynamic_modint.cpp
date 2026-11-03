#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/dynamic_modint.hpp"
#include <random>

int main() {
    using cp::DModInt;
    std::mt19937_64 random(20261025);
    const unsigned moduli[] = {1u, 2u, 3u, 7u, 998244353u, 1000000007u, 2147483647u, 2147483648u, 4294967291u, 4294967295u};
    for (unsigned m : moduli) {
        for (int round = 0; round < 3000; ++round) {
            unsigned long long x = round < 6 ? (round % 3 == 0 ? 0 : m - 1 - round % 3) % m : random() % m;
            unsigned long long y = round < 6 ? (round % 2 == 0 ? m - 1 : 0) : random() % m;
            DModInt a(m, (unsigned)x), b(m, (unsigned)y);
            assert(a.m == m && a.x == x);
            assert(add(a, b).m == m && add(a, b).x == (x + y) % m);
            assert(sub(a, b).m == m && sub(a, b).x == (x + m - y) % m);
            assert(mul(a, b).m == m && mul(a, b).x == (unsigned)(((unsigned __int128)x * y) % m));
            assert(neg(a).m == m && neg(a).x == (m - x) % m);
            assert(equal(a, b) == (x == y));
            // the constructor reduces: any 32 bit value maps to its residue
            unsigned big = (unsigned)random();
            assert(DModInt(m, big).x == big % m);
            // power / inverse / division (prime modulus for the last two)
            unsigned long long ee = random() % 1000;
            unsigned long long ref = 1 % m, bs = x % m;
            for (unsigned long long k = 0; k < ee; ++k) ref = (unsigned long long)(((unsigned __int128)ref * bs) % m);
            assert(power(a, ee).m == m && power(a, ee).x == ref);
            assert(power(a, 0).x == 1 % m);
            if (m == 2 || m == 3 || m == 7 || m == 998244353u || m == 1000000007u || m == 2147483647u || m == 4294967291u) {
                if (x != 0) {
                    DModInt ia = inv(a);
                    assert(ia.m == m && mul(a, ia).x == 1 % m);
                    if (y != 0) assert(mul(div(a, b), b).x == x && div(a, b).x == mul(a, inv(b)).x);
                }
            }
            // laws
            assert(add(a, neg(a)).x == 0);
            assert(sub(a, b).x == add(a, neg(b)).x);
        }
    }
    return 0;
}

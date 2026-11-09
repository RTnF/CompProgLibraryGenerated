#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/string/rolling_hash.hpp"
#include <random>
#include <vector>

namespace {
const unsigned long long M = (1ull << 61) - 1;

unsigned long long mulmod(unsigned long long a, unsigned long long b) {
    return (unsigned long long)((unsigned __int128)a * b % M);
}

// naive polynomial hash of s[l, r): sum s[i] * 131^(r - 1 - i) mod (2^61 - 1)
unsigned long long naive(const std::vector<int> &s, int l, int r) {
    unsigned long long h = 0;
    for (int i = l; i < r; ++i) h = (mulmod(h, 131) + (unsigned long long)s[i]) % M;
    return h;
}
} // namespace

int main() {
    std::mt19937_64 random(20261015);
    for (int n : {0, 1, 2, 3, 10, 100, 500}) {
        for (int kind = 0; kind < 3; ++kind) {
            std::vector<int> s(n);
            for (int i = 0; i < n; ++i) {
                if (kind == 0) s[i] = (int)(random() % 26);
                else if (kind == 1) s[i] = (int)(random() % 2147483648ull);
                else s[i] = 2147483647; // the largest allowed value
            }
            cp::RollingHash<int> rh(s);
            for (int l = 0; l <= n; l += 1 + n / 25) {
                for (int r = l; r <= n; r += 1 + n / 25) assert(rh.hash(l, r) == naive(s, l, r));
                assert(rh.hash(l) == naive(s, 0, l));
            }
            assert(rh.hash(n) == naive(s, 0, n));
        }
    }
    // equal substrings have equal hashes, and different positions of the same text agree
    std::vector<int> t = {1, 2, 3, 9, 1, 2, 3, 4};
    cp::RollingHash<int> rt(t);
    assert(rt.hash(0, 3) == rt.hash(4, 7));
    assert(rt.hash(0, 4) != rt.hash(4, 8));
    assert(rt.hash(2, 2) == 0);
    // the element type is a template parameter
    cp::RollingHash<int> empty(std::vector<int>{});
    assert(empty.hash(0, 0) == 0);
    return 0;
}

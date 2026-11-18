#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/string/rolling_hash.hpp"
#include <climits>
#include <random>
#include <type_traits>
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
    const std::vector<int> signed_source{1, -1};
    assert(cp::rolling_hash::RollingHash(signed_source).ends_with(std::vector<int>{-1}));
    assert(cp::SimpleRollingHash(signed_source).ends_with(std::vector<int>{-1}));

    // The original full API and the existing single-base API can be used together.
    const cp::RollingHash deduced(t);
    assert(deduced.hash(0, 3) == rt.hash(0, 3));
    static_assert(std::is_same_v<decltype(rt.hash(0, 3)), unsigned long long>);
    static_assert(cp::rh_in::SZ_BASE == 16 && cp::rh_in::base[15] == 211);
    const std::vector<int> source{1, -1, 0, 1, -1, 0, INT_MAX, INT_MIN};
    const std::vector<int> query{-1, 0};
    for (int strength = 0; strength <= 16; ++strength) {
        const cp::rolling_hash::RollingHash multi(source, strength);
        assert(multi.hash(0).size() == static_cast<std::size_t>(strength));
        assert(multi.hash(1, 3) == multi.hash(4, 6));
        assert(multi.match(query) == (strength == 0 ? 0 : 1));
        assert(multi.match_custom(query, {4, 1, -1}) == 4);
        assert(multi.match(std::vector<int>(source.size() + 1)) == std::string::npos);
    }
    const cp::SimpleRollingHash simple(source);
    assert(simple.match(query) == 1);
    assert(simple.match_custom(query, {4, 1, -1}) == 4);
    assert(!simple.starts_with(query));
    assert(simple.ends_with(std::vector<int>{INT_MAX, INT_MIN}));

    const std::string bytes("x\0\xff", 3);
    const std::string suffix("\0\xff", 2);
    const cp::rolling_hash::RollingHash multi_bytes(bytes);
    const cp::SimpleRollingHash simple_bytes(bytes);
    assert(multi_bytes.match(suffix) == 1 && multi_bytes.ends_with(suffix));
    assert(simple_bytes.match(suffix) == 1 && simple_bytes.ends_with(suffix));
    return 0;
}

#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/is_prime.hpp"
#include <random>

// The original is_prime of experiments/library/cpp/number_theory/is_prime.hpp (products through __uint128_t).
static bool original_is_prime(unsigned long long n) {
    if (n == 2) return true;
    if (!(n & 1) || n <= 1) return false;
    auto powmod64 = [](unsigned long long x, unsigned long long y, unsigned long long mod) -> unsigned long long {
        unsigned long long pm = 1;
        while (y) {
            if (y & 1) pm = (__uint128_t)pm * x % mod;
            x = (__uint128_t)x * x % mod;
            y >>= 1;
        }
        return pm;
    };
    int r = 0;
    unsigned long long d = n - 1;
    while (!(d & 1)) {
        d >>= 1;
        ++r;
    }
    for (const unsigned long long p : {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}) {
        if (p > n - 2) break;
        unsigned long long x = powmod64(p, d, n);
        if (x == 1 || x == n - 1) continue;
        bool cf = true;
        for (int i = 0; i < r - 1; ++i) {
            x = powmod64(x, 2, n);
            if (x == n - 1) {
                cf = false;
                break;
            }
        }
        if (cf) return false;
    }
    return true;
}

static bool trial_division(unsigned long long n) {
    if (n < 2) return false;
    for (unsigned long long q = 2; q * q <= n; ++q)
        if (n % q == 0) return false;
    return true;
}

int main() {
    // mul_mod_u64 and pow_mod_u64 against __uint128_t.
    std::mt19937_64 random(20261110);
    for (int round = 0; round < 200000; ++round) {
        unsigned long long m = (random() >> (random() % 64)) | 1;
        if (m < 2) continue;
        unsigned long long a = random() % m, b = random() % m;
        assert(cp::mul_mod_u64(a, b, m) == (unsigned long long)((__uint128_t)a * b % m));
        unsigned long long e = random() >> (random() % 64);
        unsigned long long expected = 1 % m, base = a;
        for (unsigned long long k = e; k; k >>= 1) {
            if (k & 1) expected = (unsigned long long)((__uint128_t)expected * base % m);
            base = (unsigned long long)((__uint128_t)base * base % m);
        }
        assert(cp::pow_mod_u64(a, e, m) == expected || m == 1);
    }
    assert(cp::mul_mod_u64(~0ULL - 1, ~0ULL - 1, ~0ULL) == 1);  // (-1)^2 mod (2^64 - 1)
    assert(cp::mul_mod_u64(0, 0, 1) == 0);
    assert(cp::pow_mod_u64(5, 0, 7) == 1);
    // mr_base
    const unsigned long long bases[12] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (int i = 0; i < 12; ++i) assert(cp::mr_base(i) == bases[i]);
    assert(cp::mr_base(12) == 37 && cp::mr_base(1000) == 37);
    // mr_witness: 91 = 7 * 13 (90 = 45 * 2) has witness 2; 2047 is a strong pseudoprime to base 2 (2046 = 1023 * 2).
    for (int round = 0; round < 100000; ++round) {
        unsigned long long n = (random() >> (random() % 62)) | 1;
        if (n < 5) continue;
        int r = 0;
        unsigned long long d = n - 1;
        while (d % 2 == 0) d /= 2, ++r;
        unsigned long long a = 1 + random() % (n - 2);
        unsigned long long x = 1, base = a;
        for (unsigned long long k = d; k; k >>= 1) {
            if (k & 1) x = (unsigned long long)((__uint128_t)x * base % n);
            base = (unsigned long long)((__uint128_t)base * base % n);
        }
        bool witness = !(x == 1 || x == n - 1);
        for (int i = 0; witness && i < r - 1; ++i) {
            x = (unsigned long long)((__uint128_t)x * x % n);
            if (x == n - 1) witness = false;
        }
        assert(cp::mr_witness(n, d, r, a) == witness);
    }
    assert(cp::mr_witness(2047, 1023, 1, 2) == false);
    assert(cp::mr_witness(2047, 1023, 1, 3) == true);
    assert(cp::mr_witness(13, 3, 2, 2) == false);  // a prime has no witness
    // is_prime against trial division for small n and against the original everywhere.
    for (unsigned long long n = 0; n < 300000; ++n) {
        assert(cp::is_prime(n) == trial_division(n));
        assert(cp::is_prime(n) == original_is_prime(n));
    }
    const unsigned long long primes[] = {998244353ULL, 1000000007ULL, 2305843009213693951ULL, 18446744073709551557ULL,
                                         4294967291ULL, 4611686018427387847ULL};
    for (unsigned long long p : primes) assert(cp::is_prime(p) && original_is_prime(p));
    const unsigned long long composites[] = {561ULL, 1105ULL, 2047ULL, 3277ULL, 4033ULL, 4681ULL, 8321ULL, 3215031751ULL,
                                             3825123056546413051ULL, 18446744073709551615ULL, 18446744030759878681ULL,
                                             4294967291ULL * 4294967279ULL, 1000000007ULL * 998244353ULL};
    for (unsigned long long c : composites) assert(!cp::is_prime(c) && !original_is_prime(c));
    for (int round = 0; round < 100000; ++round) {
        unsigned long long n = random() >> (random() % 64);
        assert(cp::is_prime(n) == original_is_prime(n));
        unsigned long long odd = n | 1;
        assert(cp::is_prime(odd) == original_is_prime(odd));
    }
    // numbers around 2^64 and around the primes above
    for (unsigned long long k = 0; k < 2000; ++k) {
        assert(cp::is_prime(~0ULL - k) == original_is_prime(~0ULL - k));
        assert(cp::is_prime(18446744073709551557ULL - k) == original_is_prime(18446744073709551557ULL - k));
    }
    return 0;
}

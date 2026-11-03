#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/inv_gcd.hpp"
#include <climits>
#include <numeric>
#include <random>
#include <utility>
#include <vector>

// The original (AtCoder Library) inv_gcd of experiments/library/cpp/fps/convolution.hpp, with safe_mod written out.
static std::pair<long long, long long> original_inv_gcd(long long a, long long b) {
    a %= b;
    if (a < 0) a += b;
    if (a == 0) return {b, 0};
    long long s = b, t = a;
    long long m0 = 0, m1 = 1;
    while (t) {
        long long u = s / t;
        s -= t * u;
        m0 -= m1 * u;
        auto tmp = s;
        s = t;
        t = tmp;
        tmp = m0;
        m0 = m1;
        m1 = tmp;
    }
    if (m0 < 0) m0 += b / s;
    return {s, m0};
}

static void check(long long a, long long b) {
    std::vector<long long> out(2 + (b & 1), -7);
    cp::inv_gcd(out, a, b);
    auto expected = original_inv_gcd(a, b);
    assert(out[0] == expected.first && out[1] == expected.second);
    // the specification: g = gcd(a mod b, b), 0 <= x < b / g, x * a == g (mod b)
    long long an = a % b;
    if (an < 0) an += b;
    long long g = std::gcd(an, b);
    assert(out[0] == g);
    assert(0 <= out[1] && out[1] < b / g);
    __int128 prod = (__int128)out[1] * (__int128)an;
    assert(((prod - g) % b) == 0);
    for (size_t i = 2; i < out.size(); ++i) assert(out[i] == -7);  // the rest is untouched
}

int main() {
    // every pair of small values (including negative a)
    for (long long b = 1; b <= 60; ++b)
        for (long long a = -130; a <= 130; ++a) check(a, b);
    std::mt19937_64 random(20261108);
    // random values over the whole range of long long, and moduli near 2^63 - 1
    for (int round = 0; round < 200000; ++round) {
        long long b = 1 + (long long)(random() % (long long)LLONG_MAX);
        if (round % 4 == 0) b = LLONG_MAX - (long long)(random() % 1000);
        if (round % 4 == 1) b = 1 + (long long)(random() % 1000000);
        long long a = (long long)random();
        if (round % 5 == 0) a = LLONG_MIN + (long long)(random() % 3);
        if (round % 5 == 1) a = LLONG_MAX - (long long)(random() % 3);
        if (round % 5 == 2) a = (long long)(random() % 2000) - 1000;
        check(a, b);
    }
    // consecutive Fibonacci numbers (the slowest case of the Euclidean algorithm)
    long long f0 = 1, f1 = 2;
    while (f1 > 0 && f1 <= LLONG_MAX / 2) {
        check(f0, f1);
        check(-f0, f1);
        long long f2 = f0 + f1;
        f0 = f1;
        f1 = f2;
    }
    return 0;
}

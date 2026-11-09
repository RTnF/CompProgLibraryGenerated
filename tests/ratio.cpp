#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number/ratio.hpp"
#include <numeric>
#include <random>

int main() {
    using cp::Ratio;
    std::mt19937_64 random(20261026);
    const unsigned long long edge[] = {0ull, 1ull, 2ull, 3ull, 6ull, 12ull, 1000000007ull, 4294967296ull,
                                       18446744073709551557ull, 18446744073709551614ull, 18446744073709551615ull};
    auto check = [](unsigned long long s, unsigned long long n, unsigned long long d) {
        Ratio r = normalize(Ratio(s, n, d));
        if (n == 0) {
            assert(r.s == 0 && r.n == 0 && r.d == 1);
        } else {
            unsigned long long g = std::gcd(n, d);
            assert(r.s == s && r.n == n / g && r.d == d / g);
            assert(std::gcd(r.n, r.d) == 1);
        }
    };
    for (unsigned long long n : edge)
        for (unsigned long long d : edge)
            if (d != 0) {
                check(0, n, d);
                check(1, n, d);
            }
    for (int round = 0; round < 20000; ++round) {
        unsigned long long g = (random() >> (random() % 64)) | 1;
        unsigned long long lim = ~0ull / g;
        unsigned long long a = lim == ~0ull ? random() : random() % (lim + 1);
        unsigned long long b = lim == ~0ull ? random() : random() % (lim + 1);
        if (b == 0) b = 1;
        check(random() & 1, a * g, b * g);
        check(random() & 1, random(), random() | 1);
    }
    return 0;
}

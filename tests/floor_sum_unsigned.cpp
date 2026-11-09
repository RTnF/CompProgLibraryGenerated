#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number_theory/floor_sum_unsigned.hpp"
#include <cstdint>
#include <limits>
#include <numeric>
#include <random>

using U64 = std::uint64_t;
using U128 = __uint128_t;

// Direct summation in a wider integer; no Euclidean recurrence is reused.
U64 reference(U64 n, U64 m, U64 a, U64 b) {
    U128 sum = 0;
    for (U64 i = 0; i < n; ++i) sum += (U128(a) * i + b) / m;
    return U64(sum);
}

void check(U64 n, U64 m, U64 a, U64 b, U64 expected) {
    assert(cp::floor_sum_unsigned(n, m, a, b) == expected);
}

int main() {
    U64 cases = 0;
    for (U64 n = 0; n <= 12; ++n)
        for (U64 m = 1; m <= 12; ++m)
            for (U64 a = 0; a <= 24; ++a)
                for (U64 b = 0; b <= 24; ++b) {
                    check(n, m, a, b, reference(n, m, a, b));
                    ++cases;
                }
    const U64 high = std::numeric_limits<U64>::max();
    const U64 bound = (U64{1} << 32) - 1;
    for (U64 n : {U64{0}, U64{1}, U64{2}, U64{31}})
        for (U64 m : {U64{1}, U64{2}, U64{3}, bound})
            for (U64 a : {U64{0}, U64{1}, m - 1, m, high})
                for (U64 b : {U64{0}, U64{1}, m - 1, m, high}) {
                    check(n, m, a, b, reference(n, m, a, b));
                    ++cases;
                }
    std::mt19937_64 random(20261004);
    for (int i = 0; i < 10000; ++i) {
        const U64 n = random() % 1001;
        const U64 m = random() % bound + 1;
        const U64 a = random(), b = random();
        check(n, m, a, b, reference(n, m, a, b));
        ++cases;
    }
    // Closed forms exercise billions of summands without enumerating them.
    check(bound, 1, high, high, U64(U128(bound) * (bound - 1) / 2 * high + U128(bound) * high));
    check(bound, bound, 0, high, U64(U128(bound) * (high / bound)));
    check(bound, bound, bound, high,
          U64(U128(bound) * (bound - 1) / 2 + U128(bound) * (high / bound)));
    for (U64 m : {bound, U64{1836311903}, U64{2971215073}})
        for (U64 a : {high, m - 1, U64{1134903170}, U64{1836311903}}) {
            const U128 twice = U128(a - 1) * (m - 1) + std::gcd(a, m) - 1;
            assert(twice % 2 == 0);
            check(m, m, a, 0, U64(twice / 2));
            ++cases;
        }
    std::cout << "floor_sum_unsigned comparisons passed: " << cases + 3 << '\n';
}

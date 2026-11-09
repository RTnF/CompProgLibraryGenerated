#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number_theory/floor_sum.hpp"
#include <cstdint>
#include <limits>
#include <numeric>
#include <random>

using I64 = std::int64_t;
using U64 = std::uint64_t;
using I128 = __int128_t;

I128 floor_div(I128 x, I128 m) {
    return x / m - (x % m < 0 ? 1 : 0);
}

I128 reference(I64 n, I64 m, I64 a, I64 b) {
    I128 result = 0;
    for (I64 i = 0; i < n; ++i) result += floor_div(I128(a) * i + b, m);
    return result;
}

// Decode without relying on an out-of-range unsigned-to-signed cast.
I64 decode(U64 bits) {
    const U64 high = std::numeric_limits<I64>::max();
    return bits <= high ? I64(bits) : -I64(~bits) - 1;
}

U64 exact_cases = 0, wrapped_cases = 0;
void check(I64 n, I64 m, I64 a, I64 b, I128 expected) {
    const auto actual = cp::floor_sum(n, m, a, b);
    assert(actual == decode(U64(expected)));
    if (std::numeric_limits<I64>::min() <= expected && expected <= std::numeric_limits<I64>::max()) {
        assert(actual == I64(expected));
        ++exact_cases;
    } else {
        ++wrapped_cases;
    }
}

int main() {
    for (I64 n = 0; n <= 10; ++n)
        for (I64 m = 1; m <= 10; ++m)
            for (I64 a = -12; a <= 12; ++a)
                for (I64 b = -12; b <= 12; ++b) check(n, m, a, b, reference(n, m, a, b));
    const I64 low = std::numeric_limits<I64>::min();
    const I64 high = std::numeric_limits<I64>::max();
    const I64 bound = (I64{1} << 32) - 1;
    const I64 values[] = {low, low + 1, -1, 0, 1, high - 1, high};
    for (I64 n : {I64{0}, I64{1}, I64{2}, I64{31}})
        for (I64 m : {I64{1}, I64{2}, I64{3}, bound})
            for (I64 a : values)
                for (I64 b : values) check(n, m, a, b, reference(n, m, a, b));
    std::mt19937_64 random(20261004);
    for (int i = 0; i < 5000; ++i) {
        const I64 n = I64(random() % 1001), m = I64(random() % U64(bound)) + 1;
        const I64 a = decode(random()), b = decode(random());
        check(n, m, a, b, reference(n, m, a, b));
    }
    for (I64 a : values)
        for (I64 b : values)
            check(bound, 1, a, b, I128(bound) * (bound - 1) / 2 * a + I128(bound) * b);
    // Pair i with m-i: valid for negative coefficients and billions of terms.
    const I64 paired[] = {low, low + 1, -1836311903, -1134903170, -1, 0, 1, high - 1, high};
    for (I64 m : {bound, I64{1836311903}, I64{2971215073}})
        for (I64 a : paired) {
            const U64 magnitude = a < 0 ? U64{0} - U64(a) : U64(a);
            const I128 twice = (I128(a) - 1) * (m - 1) + std::gcd(magnitude, U64(m)) - 1;
            assert(twice % 2 == 0);
            check(m, m, a, 0, twice / 2);
        }
    assert(cp::floor_sum(2, 1, 0, high) == -2);
    assert(exact_cases != 0 && wrapped_cases != 0);
    std::cout << "signed floor_sum comparisons passed: " << exact_cases + wrapped_cases
              << " (exact=" << exact_cases << ", wrapped=" << wrapped_cases << ")\n";
}

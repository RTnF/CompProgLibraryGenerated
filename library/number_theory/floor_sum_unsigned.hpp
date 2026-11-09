#pragma once
#include <cstdint>
#include <utility>

namespace cp {

// sum_{i=0}^{n-1} floor((a*i+b)/m), modulo 2^64.
// Requires n < 2^32 and 0 < m < 2^32. a,b may use all 64 bits.
// Imported ACL algorithm; unsigned intermediate operations intentionally wrap.
// Time O(log m), additional space O(1).
inline std::uint64_t floor_sum_unsigned(std::uint64_t n, std::uint64_t m,
                                       std::uint64_t a, std::uint64_t b) {
    std::uint64_t ans = 0;
    while (true) {
        if (a >= m) {
            ans += n * (n - 1) / 2 * (a / m);
            a %= m;
        }
        if (b >= m) {
            ans += n * (b / m);
            b %= m;
        }
        std::uint64_t y_max = a * n + b;
        if (y_max < m) {
            break;
        }
        n = y_max / m;
        b = y_max % m;
        std::swap(m, a);
    }
    return ans;
}

} // namespace cp

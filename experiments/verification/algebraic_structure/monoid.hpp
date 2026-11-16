#pragma once
#include <algorithm>
#include <cstdint>
#include <limits>
#include <type_traits>
#include <vector>

// Pending pure-model migration of the complete original monoid.hpp API.
// Signed multiplication requires representable intermediate values.
namespace cp {
template<class T> struct MonoidMul;
template<class T> MonoidMul<T> op(const MonoidMul<T>& a, const MonoidMul<T>& b);
template<class T = std::int64_t> struct MonoidMul {
    T x;
    MonoidMul(T value): x(value) {}
    MonoidMul(): MonoidMul(e()) {}
    static MonoidMul e() { return 1; }
    friend MonoidMul op(const MonoidMul& a, const MonoidMul& b) {
        return a.x * b.x;
    }
};
template<class T> MonoidMul<T> op(const MonoidMul<T>& a, const MonoidMul<T>& b) {
    return a.x * b.x;
}

template<class T> struct MonoidMax;
template<class T> MonoidMax<T> op(const MonoidMax<T>& a, const MonoidMax<T>& b);
template<class T = std::int64_t> struct MonoidMax {
    T x;
    MonoidMax(T value): x(value) {}
    MonoidMax(): MonoidMax(e()) {}
    static MonoidMax e() { if constexpr (std::is_floating_point_v<T>) { return std::numeric_limits<T>::has_infinity ? -std::numeric_limits<T>::infinity() : std::numeric_limits<T>::lowest(); } else { return std::numeric_limits<T>::min(); } }
    friend MonoidMax op(const MonoidMax& a, const MonoidMax& b) {
        using std::max;
        return max(a.x, b.x);
    }
};
template<class T> MonoidMax<T> op(const MonoidMax<T>& a, const MonoidMax<T>& b) {
    using std::max;
        return max(a.x, b.x);
}

template<class T> struct MonoidMin;
template<class T> MonoidMin<T> op(const MonoidMin<T>& a, const MonoidMin<T>& b);
template<class T = std::int64_t> struct MonoidMin {
    T x;
    MonoidMin(T value): x(value) {}
    MonoidMin(): MonoidMin(e()) {}
    static MonoidMin e() { if constexpr (std::is_floating_point_v<T>) { return std::numeric_limits<T>::has_infinity ? std::numeric_limits<T>::infinity() : std::numeric_limits<T>::max(); } else { return std::numeric_limits<T>::max(); } }
    friend MonoidMin op(const MonoidMin& a, const MonoidMin& b) {
        using std::min;
        return min(a.x, b.x);
    }
};
template<class T> MonoidMin<T> op(const MonoidMin<T>& a, const MonoidMin<T>& b) {
    using std::min;
        return min(a.x, b.x);
}

} // namespace cp

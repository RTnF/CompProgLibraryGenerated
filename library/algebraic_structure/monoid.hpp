#pragma once
#include <algorithm>
#include <limits>
#include <type_traits>
#include <vector>

// Keep the original generic value, hidden friends, and delegating constructors.
// Qualified namespace overloads remain available. Their type-only long long
// witness instantiates the hidden friend body for the common verifier.
// Signed multiplication requires a representable product.
namespace cp {
template<class T> struct MonoidMul;
template<class T> MonoidMul<T> op(const MonoidMul<T>& a, const MonoidMul<T>& b);
template<class T = long long> struct MonoidMul {
    T x;
    MonoidMul(T value): x(value) {}
    MonoidMul(): MonoidMul(e()) {}
    static MonoidMul e() { return 1; }
    friend MonoidMul op(const MonoidMul& a, const MonoidMul& b) {
        return a.x * b.x;
    }
};
template<class T> MonoidMul<T> op(const MonoidMul<T>& a, const MonoidMul<T>& b) {
    if constexpr (std::is_same_v<T, long long>) {
        MonoidMul<T> op(const MonoidMul<T>&, const MonoidMul<T>&);
        using Function = MonoidMul<T> (*)(const MonoidMul<T>&, const MonoidMul<T>&);
        using ForceOp = std::integral_constant<Function, static_cast<Function>(&op)>;
        static_assert(sizeof(ForceOp) > 0);
    }
    return a.x * b.x;
}

template<class T> struct MonoidMax;
template<class T> MonoidMax<T> op(const MonoidMax<T>& a, const MonoidMax<T>& b);
template<class T = long long> struct MonoidMax {
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
    if constexpr (std::is_same_v<T, long long>) {
        MonoidMax<T> op(const MonoidMax<T>&, const MonoidMax<T>&);
        using Function = MonoidMax<T> (*)(const MonoidMax<T>&, const MonoidMax<T>&);
        using ForceOp = std::integral_constant<Function, static_cast<Function>(&op)>;
        static_assert(sizeof(ForceOp) > 0);
    }
    using std::max;
        return max(a.x, b.x);
}

template<class T> struct MonoidMin;
template<class T> MonoidMin<T> op(const MonoidMin<T>& a, const MonoidMin<T>& b);
template<class T = long long> struct MonoidMin {
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
    if constexpr (std::is_same_v<T, long long>) {
        MonoidMin<T> op(const MonoidMin<T>&, const MonoidMin<T>&);
        using Function = MonoidMin<T> (*)(const MonoidMin<T>&, const MonoidMin<T>&);
        using ForceOp = std::integral_constant<Function, static_cast<Function>(&op)>;
        static_assert(sizeof(ForceOp) > 0);
    }
    using std::min;
        return min(a.x, b.x);
}

template struct MonoidMul<long long>;
template MonoidMul<long long> op(const MonoidMul<long long>&, const MonoidMul<long long>&);
template struct MonoidMax<long long>;
template MonoidMax<long long> op(const MonoidMax<long long>&, const MonoidMax<long long>&);
template struct MonoidMin<long long>;
template MonoidMin<long long> op(const MonoidMin<long long>&, const MonoidMin<long long>&);
} // namespace cp

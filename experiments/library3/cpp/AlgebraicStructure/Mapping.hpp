#pragma once
#include "Template/SmallTemplate.hpp"

/**
 * @brief 写像は X -> X なら結合的なので変換モノイドをなす
 * 恒等写像：static Mapping ide()
 * 適用：U apply(U x) const
 * 合成：friend Mapping compose(const Mappint &, const Mappint &)
 */

/**
 * @brief アフィン写像 y = ax + b
 * @tparam T 
 */
template<class T>
struct Affine {
    T a, b;
    Affine(T a_, T b_): a(a_), b(b_) {}
    Affine(): Affine(ide()) {}
    static Affine ide() { return {1, 0}; }
    template<class U>
    U apply(U x) const {
        return a * x + b;
    }
    friend Affine compose(const Affine &p, const Affine &q) { return {p.a * q.a, p.b * q.a + q.b}; }
    Affine inv() const { return {1 / a, -b / a}; }
};

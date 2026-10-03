#pragma once
#include "Template/SmallTemplate.hpp"

template<class T>
struct MonoidMul {
    T x;
    MonoidMul(T x_): x(x_) {}
    MonoidMul(): MonoidMul(e()) {}
    static MonoidMul e() { return 1; }
    friend MonoidMul op(const MonoidMul &a, const MonoidMul &b) { return a.x * b.x; }
};

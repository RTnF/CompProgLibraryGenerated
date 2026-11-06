#include <cassert>
#include <iostream>
#include <limits>
#include <vector>
#ifdef PUBLIC_MONOID
using cp::MonoidMax;
using cp::MonoidMin;
#endif
static std::vector<int> events;
struct Traced {
    int value;
    Traced(int n) : value(n) { events.push_back(n); }
    Traced(const Traced& x) : value(x.value) { events.push_back(100+value); }
    Traced& operator=(const Traced&) = delete;
    ~Traced() { events.push_back(200+value); }
    friend bool operator<(const Traced& a, const Traced& b) { events.push_back(300); return a.value < b.value; }
};
namespace std {
template<> class numeric_limits<Traced> {
public:
    static Traced min() { return Traced(-50); }
    static Traced max() { return Traced(50); }
};
}
template<template<class> class M> static std::vector<int> construction_trace(int identityValue, int resultValue) {
    events.clear();
    {
        M<Traced> identity, a(Traced(2)), b(Traced(3));
        auto result = op(a,b);
        assert(identity.x.value == identityValue && result.x.value == resultValue);
    }
    return events;
}

int main() {
    for (auto x : construction_trace<MonoidMax>(-50,3)) std::cout << x << ',';
    std::cout << '\n';
    for (auto x : construction_trace<MonoidMin>(50,2)) std::cout << x << ',';
    std::cout << '\n';
}

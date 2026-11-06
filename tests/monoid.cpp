#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/monoid.hpp"
#include <climits>
#include <random>
#include <vector>

struct CopyOnly {
    int value;
    explicit CopyOnly(int n) : value(n) {}
    CopyOnly(const CopyOnly&) = default;
    CopyOnly& operator=(const CopyOnly&) = delete;
    friend bool operator<(const CopyOnly& a, const CopyOnly& b) { return a.value < b.value; }
};

namespace custom_choice {
struct Value {
    int value;
    explicit Value(int x) : value(x) {}
    Value(const Value&) = default;
    Value& operator=(const Value&) = delete;
};
// ADL must retain the original custom selection, including qualified cp::op.
const Value& max(const Value& a, const Value&) { return a; }
const Value& min(const Value&, const Value& b) { return b; }
}

int main() {
    using MonoidMax = cp::MonoidMax<long long>;
    using MonoidMin = cp::MonoidMin<long long>;
    using MonoidMul = cp::MonoidMul<long long>;
    // Identities.
    assert(MonoidMul().x == 1);
    assert(MonoidMax().x == LLONG_MIN);
    assert(MonoidMin().x == LLONG_MAX);
    assert(MonoidMul::e().x == 1 && MonoidMax::e().x == LLONG_MIN && MonoidMin::e().x == LLONG_MAX);
    assert(MonoidMul(5).x == 5);
    assert(MonoidMax(-5).x == -5);
    assert(MonoidMin(7).x == 7);
    const long long values[] = {LLONG_MIN, LLONG_MIN + 1, -1000000007, -2, -1, 0, 1, 2, 3, 1000000007, LLONG_MAX - 1, LLONG_MAX};
    for (long long a : values) {
        for (long long b : values) {
            assert(op(MonoidMax(a), MonoidMax(b)).x == std::max(a, b));
            assert(op(MonoidMin(a), MonoidMin(b)).x == std::min(a, b));
            long long product;
            if (!__builtin_mul_overflow(a, b, &product)) assert(op(MonoidMul(a), MonoidMul(b)).x == product);
        }
        // identity laws
        assert(op(MonoidMax(), MonoidMax(a)).x == a && op(MonoidMax(a), MonoidMax()).x == a);
        assert(op(MonoidMin(), MonoidMin(a)).x == a && op(MonoidMin(a), MonoidMin()).x == a);
        assert(op(MonoidMul(), MonoidMul(a)).x == a && op(MonoidMul(a), MonoidMul()).x == a);
    }
    // Associativity on a random sample.
    std::mt19937_64 random(20261008);
    for (int trial = 0; trial < 10000; ++trial) {
        long long a = static_cast<long long>(random()), b = static_cast<long long>(random()), c = static_cast<long long>(random());
        assert(op(op(MonoidMax(a), MonoidMax(b)), MonoidMax(c)).x == op(MonoidMax(a), op(MonoidMax(b), MonoidMax(c))).x);
        assert(op(op(MonoidMin(a), MonoidMin(b)), MonoidMin(c)).x == op(MonoidMin(a), op(MonoidMin(b), MonoidMin(c))).x);
        a %= 1000; b %= 1000; c %= 1000;
        assert(op(op(MonoidMul(a), MonoidMul(b)), MonoidMul(c)).x == op(MonoidMul(a), op(MonoidMul(b), MonoidMul(c))).x);
    }
    // the element type is a template parameter
    assert(cp::MonoidMax<int>::e().x == INT_MIN && cp::MonoidMin<unsigned>::e().x == 0xFFFFFFFFu);
    assert(op(cp::MonoidMax<int>(3), cp::MonoidMax<int>(8)).x == 8 && op(cp::MonoidMul<double>(1.5), cp::MonoidMul<double>(4)).x == 6.0);
    // Hidden friends accept conversions in either argument position.
    assert(op(cp::MonoidMul<int>(2),3).x == 6 && op(3,cp::MonoidMul<int>(2)).x == 6);
    assert(op(cp::MonoidMax<int>(2),3).x == 3 && op(3,cp::MonoidMax<int>(2)).x == 3);
    assert(op(cp::MonoidMin<int>(2),3).x == 2 && op(3,cp::MonoidMin<int>(2)).x == 2);
    cp::MonoidMax<CopyOnly> low(CopyOnly(2)), high(CopyOnly(7));
    cp::MonoidMin<CopyOnly> first(CopyOnly(7)), second(CopyOnly(2));
    assert(op(low,high).x.value == 7 && cp::op(low,high).x.value == 7);
    assert(op(first,second).x.value == 2 && cp::op(first,second).x.value == 2);
    assert(cp::op(MonoidMul(2),MonoidMul(3)).x == 6);
    assert(cp::op(MonoidMax(2),MonoidMax(7)).x == 7);
    assert(cp::op(MonoidMin(7),MonoidMin(2)).x == 2);
    using V = custom_choice::Value;
    cp::MonoidMax<V> va(V(2)), vb(V(7));
    cp::MonoidMin<V> vc(V(7)), vd(V(2));
    assert(op(va,vb).x.value == 2 && cp::op(va,vb).x.value == 2);
    assert(op(vc,vd).x.value == 2 && cp::op(vc,vd).x.value == 2);
    return 0;
}

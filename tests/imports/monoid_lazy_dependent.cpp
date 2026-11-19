#include "algebraic_structure/monoid_lazy.hpp"
#include "../../library/algebraic_structure/monoid_lazy.hpp"
#include <cassert>
#include <cmath>

struct Field {
    long long value;
};

struct Sum {
    long long value;
};

Sum operator+(Field field, long long increment) {
    return {2 * field.value + increment};
}

struct Custom {
    Field x;
    Custom(Field value) : x(value) {}
    Custom(Sum value) : x{3 * value.value} {}
};

struct MultiplyLeft {
    int value;
};

struct MultiplyRight {
    int value;
};

struct CustomScalar {
    int value;
    CustomScalar &operator=(MultiplyRight product) {
        value += product.value;
        return *this;
    }
};

MultiplyLeft operator*(int count, CustomScalar v) { return {count * v.value + 1}; }
MultiplyRight operator*(CustomScalar v, int count) { return {count * v.value - 1}; }
CustomScalar operator+(CustomScalar x, MultiplyLeft y) { return {x.value + y.value}; }

template <class Original, class Port, class T>
void additive_sum() {
    using A = typename Original::RangeAdd;
    using B = typename Port::RangeAdd;
    using X = typename Original::RangeSum;
    using Y = typename Port::RangeSum;
    for (int count : {-5, 0, 8}) {
        for (T value : {-T(2), T(0), T(7)}) {
            A a(value);
            B b(value);
            auto reference = a.apply(X(T(16), count));
            auto actual = b.apply(Y(T(16), count));
            assert(reference.x == actual.x && reference.size == actual.size);
            assert(compose(a, A::id()).v == compose(b, B::id()).v);
            assert(op(X(value, count), X::e()).x == op(Y(value, count), Y::e()).x);
        }
    }
}

template <class Original, class Port, class T>
void assignment_sum() {
    using A = typename Original::RangeSet;
    using B = typename Port::RangeSet;
    using X = typename Original::RangeSum;
    using Y = typename Port::RangeSum;
    for (bool noop : {false, true}) {
        for (int count : {-5, 0, 8}) {
            A a = noop ? A::id() : A(T(2));
            B b = noop ? B::id() : B(T(2));
            auto reference = a.apply(X(T(16), count));
            auto actual = b.apply(Y(T(16), count));
            assert(reference.x == actual.x && reference.size == actual.size);
            assert(compose(a, A(T(5))).v == compose(b, B(T(5))).v);
            assert(compose(a, A(T(5))).noop == compose(b, B(T(5))).noop);
        }
    }
}

int main() {
    RangeAddRangeMaxMin<long long>::RangeAdd original_add(7);
    cp::RangeAddRangeMaxMin<long long>::RangeAdd port_add(7);
    Custom input(Field{5});
    assert(original_add.apply(input).x.value == 51);
    assert(port_add.apply(input).x.value == 51);
    using OriginalSet = RangeSetRangeMaxMin<double>::RangeSet;
    using PortSet = cp::RangeSetRangeMaxMin<double>::RangeSet;
    auto original_set = OriginalSet::id();
    auto port_set = PortSet::id();
    constexpr long long not_exact_as_double = (1LL << 53) + 1;
    assert(original_set.apply(not_exact_as_double) == (1LL << 53));
    assert(original_set.apply(not_exact_as_double) == port_set.apply(not_exact_as_double));
    assert(OriginalSet(7.5).apply(3LL) == PortSet(7.5).apply(3LL));

    using OriginalMax = RangeAddRangeMaxMin<double>::RangeMax;
    using PortMax = cp::RangeAddRangeMaxMin<double>::RangeMax;
    assert(std::isinf(OriginalMax::e().x) && OriginalMax::e().x == PortMax::e().x);
    assert(op(OriginalMax(3), OriginalMax()).x == op(PortMax(3), PortMax()).x);
    using OriginalMin = RangeSetRangeMaxMin<long long>::RangeMin;
    using PortMin = cp::RangeSetRangeMaxMin<long long>::RangeMin;
    assert(OriginalMin::e().x == PortMin::e().x);
    assert(op(OriginalMin(3), OriginalMin()).x == op(PortMin(3), PortMin()).x);

    using OriginalAddSum = RangeAddRangeSum<CustomScalar>;
    using PortAddSum = cp::RangeAddRangeSum<CustomScalar>;
    OriginalAddSum::RangeAdd original_add_sum(CustomScalar{5});
    PortAddSum::RangeAdd port_add_sum(CustomScalar{5});
    auto original_added = original_add_sum.apply(OriginalAddSum::RangeSum(CustomScalar{8}, 3));
    auto port_added = port_add_sum.apply(PortAddSum::RangeSum(CustomScalar{8}, 3));
    assert(original_added.x.value == 24 && port_added.x.value == 24);

    using OriginalSetSum = RangeSetRangeSum<CustomScalar>;
    using PortSetSum = cp::RangeSetRangeSum<CustomScalar>;
    OriginalSetSum::RangeSet original_set_sum(CustomScalar{5});
    PortSetSum::RangeSet port_set_sum(CustomScalar{5});
    auto original_assigned = original_set_sum.apply(OriginalSetSum::RangeSum(CustomScalar{8}, 3));
    auto port_assigned = port_set_sum.apply(PortSetSum::RangeSum(CustomScalar{8}, 3));
    assert(original_assigned.x.value == 22 && port_assigned.x.value == 22);

    additive_sum<RangeAddRangeSum<int>, cp::RangeAddRangeSum<int>, int>();
    additive_sum<RangeAddRangeSum<double>, cp::RangeAddRangeSum<double>, double>();
    assignment_sum<RangeSetRangeSum<int>, cp::RangeSetRangeSum<int>, int>();
    assignment_sum<RangeSetRangeSum<double>, cp::RangeSetRangeSum<double>, double>();

    std::cout << port_add.apply(input).x.value << '\n';
    std::cout << port_set.apply(not_exact_as_double) << '\n';
    std::cout << PortSet(7.5).apply(3LL) << '\n';
    std::cout << port_added.x.value << '\n';
    std::cout << port_assigned.x.value << '\n';
}

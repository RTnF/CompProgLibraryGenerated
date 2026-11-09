#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/algebraic_structure/group.hpp"
#include <climits>
#include <random>
#include <type_traits>

// Copying this value is observable; apply must preserve the original const-reference API.
struct TrackedValue {
    long long value;
    static int copies;
    TrackedValue(long long value) : value(value) {}
    TrackedValue(const TrackedValue &other) : value(other.value) { ++copies; }
    friend TrackedValue operator*(const TrackedValue &a, const TrackedValue &b) {
        return TrackedValue(a.value * b.value);
    }
    friend TrackedValue operator+(const TrackedValue &a, const TrackedValue &b) {
        return TrackedValue(a.value + b.value);
    }
};
int TrackedValue::copies = 0;

// The original braced return and delegating constructor have observable effects for generic T.
struct ConstructionEvent {
    int value;
    static std::vector<int> events;
    ConstructionEvent(int x) : value(x) { events.push_back(x); }
    ConstructionEvent(const ConstructionEvent &other) : value(other.value) { events.push_back(100 + value); }
};
std::vector<int> ConstructionEvent::events;

template <template <class> class Affine> std::vector<int> default_events() {
    ConstructionEvent::events.clear();
    Affine<ConstructionEvent> value;
    auto events = ConstructionEvent::events;
    assert(value.a().value == 1 && value.b().value == 0);
    return events;
}

template <template <class> class Affine> std::vector<int> identity_events() {
    ConstructionEvent::events.clear();
    auto value = Affine<ConstructionEvent>::e();
    auto events = ConstructionEvent::events;
    assert(value.a().value == 1 && value.b().value == 0);
    return events;
}

void check_original_api() {
    const auto identity = identity_events<cp::GroupAffine>();
    assert(identity.size() >= 2 && identity[0] == 1 && identity[1] == 0);
    assert(default_events<cp::GroupAffine>() == identity);
    cp::GroupSum<long long> sum(2);
    cp::GroupMul<long long> mul(2);
    assert(op(sum, 3LL).x() == 5 && op(3LL, sum).x() == 5);
    assert(op(mul, 3LL).x() == 6 && op(3LL, mul).x() == 6);
    assert(op(sum, 3).x() == 5 && op(cp::GroupSum<int>(2), 3L).x() == 5);
    assert(cp::op(sum, sum).x() == 4 && cp::op(mul, mul).x() == 4);
    struct AffineProxy {
        cp::GroupAffine<long long> value;
        operator cp::GroupAffine<long long>() const { return value; }
    };
    cp::GroupAffine<long long> a(2, 3);
    AffineProxy b{{5, 7}};
    assert(op(a, b).a() == 10 && op(a, b).b() == 22);
    assert(op(b, a).a() == 10 && op(b, a).b() == 17);
    struct Local {
        int value;
        Local(int x) : value(x) {}
        Local operator+(const Local &other) const { return Local(value + other.value); }
    };
    cp::GroupSum<Local> local(Local(2));
    assert(op(local, local).x().value == 4 && cp::op(local, local).x().value == 4);
}

int main() {
    check_original_api();
    using GroupMul = cp::GroupMul<long long>;
    using GroupSum = cp::GroupSum<long long>;
    using GroupAffine = cp::GroupAffine<long long>;
    static_assert(std::is_same_v<decltype(&GroupAffine::apply),
                                long long (GroupAffine::*)(const long long &) const>);
    const cp::GroupAffine<TrackedValue> tracked(TrackedValue(2), TrackedValue(3));
    const TrackedValue argument(5);
    TrackedValue::copies = 0;
    const auto tracked_result = tracked.apply(argument);
    assert(tracked_result.value == 13 && TrackedValue::copies == 0);
    assert(GroupSum::e().x() == 0 && GroupMul::e().x() == 1);
    assert(GroupAffine::e().a() == 1 && GroupAffine::e().b() == 0);
    assert(GroupSum().x() == 0);
    assert(GroupMul().x() == 1);
    assert(GroupSum(-7).x() == -7);
    assert(GroupMul(5).x() == 5);
    const long long values[] = {LLONG_MIN + 1, -1000000007, -2, -1, 0, 1, 2, 3, 1000000007, LLONG_MAX - 1, LLONG_MAX};
    for (long long a : values) {
        // GroupSum: inverse and identity laws
        assert(op(GroupSum(a), GroupSum(a).inv()).x() == 0);
        assert(op(GroupSum(), GroupSum(a)).x() == a && op(GroupSum(a), GroupSum()).x() == a);
        assert(GroupSum(a).inv().x() == -a);
        for (long long b : values) {
            long long sum;
            if (!__builtin_add_overflow(a, b, &sum)) assert(op(GroupSum(a), GroupSum(b)).x() == sum);
            long long product;
            if (a != 0 && b != 0 && !__builtin_mul_overflow(a, b, &product) && product != 0)
                assert(op(GroupMul(a), GroupMul(b)).x() == product);
        }
        if (a != 0) assert(op(GroupMul(), GroupMul(a)).x() == a && op(GroupMul(a), GroupMul()).x() == a);
    }
    // inv of GroupMul is the integer division 1 / x: the true inverse only for 1 and -1.
    assert(GroupMul(1).inv().x() == 1);
    assert(GroupMul(-1).inv().x() == -1);
    assert(op(GroupMul(1), GroupMul(-1).inv()).x() == -1);
    // GroupAffine: y = a * x + b; op(p, q) applies p first and then q.
    assert(GroupAffine().a() == 1 && GroupAffine().b() == 0);
    assert(GroupAffine(3, -4).a() == 3 && GroupAffine(3, -4).b() == -4);
    const long long small[] = {-1000, -7, -1, 0, 1, 2, 9, 1000};
    for (long long pa : small) for (long long pb : small) {
        GroupAffine p(pa, pb);
        for (long long x : small) assert(p.apply(x) == pa * x + pb);
        const GroupAffine id = GroupAffine::e();
        assert(op(id, p).a() == pa && op(id, p).b() == pb && op(p, id).a() == pa && op(p, id).b() == pb);
        for (long long qa : small) for (long long qb : small) {
            GroupAffine q(qa, qb);
            GroupAffine c = op(p, q);
            assert(c.a() == pa * qa && c.b() == pb * qa + qb);
            for (long long x : small) assert(c.apply(x) == q.apply(p.apply(x)));
        }
        // the inverse (integer divisions, as in the original): exact for a = 1 and a = -1
        if (pa == 1 || pa == -1) {
            GroupAffine inverse = p.inv();
            assert(inverse.a() == 1 / pa && inverse.b() == -pb / pa);
            assert(op(p, inverse).a() == 1 && op(p, inverse).b() == 0);
            for (long long x : small) assert(inverse.apply(p.apply(x)) == x);
        }
    }
    const long long big[] = {LLONG_MIN + 1, -1000000007, 1000000007, LLONG_MAX - 1};
    for (long long a : big) for (long long b : big) for (long long x : small) {
        long long m, t;
        if (__builtin_mul_overflow(a, x, &m) || __builtin_add_overflow(m, b, &t)) continue;
        assert(GroupAffine(a, b).apply(x) == t);
    }
    // the element type is a template parameter
    assert(op(cp::GroupSum<int>(3), cp::GroupSum<int>(4)).x() == 7 && cp::GroupSum<double>(1.5).inv().x() == -1.5);
    assert(cp::GroupMul<double>(4).inv().x() == 0.25 && cp::GroupAffine<double>(2, 1).inv().a() == 0.5);
    return 0;
}

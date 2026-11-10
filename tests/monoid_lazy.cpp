#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/algebraic_structure/monoid_lazy.hpp"
#include <climits>
#include <vector>

int main() {
    using RangeAdd = cp::RangeAdd<long long>;
    using RangeSet = cp::RangeSet<long long>;
    using RangeSum = cp::RangeSum<long long>;
    // RangeSum: a sum together with a length.
    assert(RangeSum().x == 0 && RangeSum().size == 0);
    assert(RangeSum(5, 3).x == 5 && RangeSum(5, 3).size == 3);
    const long long xs[] = {-1000000007, -3, 0, 1, 7, 1000000007};
    for (long long a : xs) for (long long b : xs) for (int sa = 0; sa < 4; sa++) for (int sb = 0; sb < 4; sb++) {
        RangeSum r = op(RangeSum(a, sa), RangeSum(b, sb));
        assert(r.x == a + b && r.size == sa + sb);
    }
    // RangeAdd: shifts add up, applied to a maximum or to a sum.
    assert(RangeAdd().v == 0 && RangeAdd(9).v == 9);
    for (long long f : xs) for (long long g : xs) for (long long m : xs) {
        RangeAdd c = compose(RangeAdd(f), RangeAdd(g));
        assert(c.v == f + g);
        assert(c.applyExtremum(m) == RangeAdd(f).applyExtremum(RangeAdd(g).applyExtremum(m)));
        for (int size = 0; size < 5; size++) {
            assert(RangeAdd(f).applySumX(m, size) == m + (long long)size * f);
            // adding g then f to a segment of the given size equals adding f + g
            assert(c.applySumX(m, size) == RangeAdd(f).applySumX(RangeAdd(g).applySumX(m, size), size));
        }
    }
    assert(RangeAdd(3).applyExtremum(-3) == 0);
    // RangeSet: the identity keeps the value, the others replace it; compose keeps f unless f is the no-op.
    assert(RangeSet().noop && !RangeSet(4).noop && RangeSet(4).v == 4 && RangeSet(4, true).noop);
    for (long long m : xs) {
        assert(RangeSet().applyExtremum(m) == m);
        assert(RangeSet(5).applyExtremum(m) == 5);
        for (int size = 0; size < 5; size++) {
            assert(RangeSet().applySumX(m, size) == m);
            assert(RangeSet(5).applySumX(m, size) == 5LL * size);
        }
    }
    for (long long fv : xs) for (long long gv : xs) for (int fn = 0; fn < 2; fn++) for (int gn = 0; gn < 2; gn++) {
        RangeSet f(fv, fn), g(gv, gn);
        RangeSet c = compose(f, g);
        assert(c.noop == (fn ? gn : fn) && (fn ? c.v == gv : c.v == fv));
        for (long long m : xs) {
            // g first, then f: a no-op f leaves the result of g alone
            assert(c.applyExtremum(m) == f.applyExtremum(g.applyExtremum(m)));
            for (int size = 0; size < 4; size++) assert(c.applySumX(m, size) == f.applySumX(g.applySumX(m, size), size));
        }
    }
    RangeSet id;
    RangeSet s(8);
    assert(compose(id, s).v == 8 && !compose(id, s).noop);
    assert(compose(s, id).v == 8 && !compose(s, id).noop);
    // the value type is a template parameter
    {
        cp::RangeSum<int> a(3, 2), b(4, 5);
        assert(op(a, b).x == 7 && op(a, b).size == 7);
        cp::RangeAdd<int> f(2), g(5);
        assert(compose(f, g).v == 7 && f.applyExtremum(10) == 12 && f.applySumX(10, 3) == 16);
        cp::RangeSet<double> set(1.5);
        assert(set.applyExtremum(9.0) == 1.5 && set.applySumX(9.0, 4) == 6.0);
    }
    // The original nested API (RangeAddRangeMaxMin, RangeAddRangeSum, RangeSetRangeMaxMin, RangeSetRangeSum).
    {
        using AddSum = cp::RangeAddRangeSum<long long>;
        AddSum::RangeSum x(7, 4), y(2, 1), z;
        auto s = op(x, y);
        assert(z.x == 0 && z.size == 0 && AddSum::RangeSum::e().size == 0 && s.x == 9 && s.size == 5);
        AddSum::RangeAdd f(3), g(2);
        auto h = compose(f, g);
        assert(AddSum::RangeAdd::id().v == 0 && h.v == 5);
        auto a = f.apply(x);
        assert(a.x == 19 && a.size == 4 && x.x == 7);
        using AddMax = cp::RangeAddRangeMaxMin<long long>;
        assert(AddMax::RangeMax().x == LLONG_MIN && AddMax::RangeMin().x == LLONG_MAX);
        assert(op(AddMax::RangeMax(3), AddMax::RangeMax(9)).x == 9 && op(AddMax::RangeMin(3), AddMax::RangeMin(9)).x == 3);
        assert(AddMax::RangeAdd(4).apply(AddMax::RangeMax(10)).x == 14 && AddMax::RangeAdd(4).apply(AddMax::RangeMin(10)).x == 14);
        using SetSum = cp::RangeSetRangeSum<long long>;
        SetSum::RangeSum q(5, 3);
        SetSum::RangeSet keep, assign(8);
        assert(keep.noop && !assign.noop && keep.apply(q).x == 5 && assign.apply(q).x == 24 && assign.apply(q).size == 3);
        assert(compose(keep, assign).v == 8 && compose(assign, keep).v == 8);
        using SetMax = cp::RangeSetRangeMaxMin<long long>;
        assert(SetMax::RangeSet().apply(SetMax::RangeMax(6)).x == 6 && SetMax::RangeSet(2).apply(SetMax::RangeMin(6)).x == 2);
        // the value type is a template parameter: unsigned wrap-around and int
        cp::RangeAddRangeSum<unsigned>::RangeAdd u(1);
        auto w = u.apply(cp::RangeAddRangeSum<unsigned>::RangeSum(4294967295u, 2));
        assert(w.x == 4294967295u + 2u && w.size == 2);
        assert(cp::RangeAddRangeMaxMin<int>::RangeMax().x == INT_MIN && cp::RangeSetRangeMaxMin<double>::RangeMin().x > 1e300);
    }
    return 0;
}

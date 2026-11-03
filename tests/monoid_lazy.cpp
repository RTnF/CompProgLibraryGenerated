#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/monoid_lazy.hpp"
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
    return 0;
}

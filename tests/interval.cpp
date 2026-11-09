#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/interval/interval.hpp"
#include <climits>

int main() {
    using Interval = cp::Interval<long long>;
    assert(Interval().is_null() && Interval().start() == 0 && Interval().end() == 0 && Interval().length() == 0);
    assert(Interval(3, 3).is_null() && !Interval(3, 4).is_null());
    assert(Interval(-5, 7).start() == -5 && Interval(-5, 7).end() == 7 && Interval(-5, 7).length() == 12);
    const long long values[] = {-100, -3, -1, 0, 1, 2, 5, 100};
    for (long long a : values)
        for (long long b : values) {
            if (a > b) continue;
            for (long long c : values)
                for (long long d : values) {
                    if (c > d) continue;
                    Interval x(a, b), y(c, d);
                    Interval z = x.intersection(y);
                    // reference: the result is [0, 0) when the intervals do not overlap (c >= b or a >= d), and
                    // [max(a, c), min(b, d)) otherwise (which is empty, with is_null, when one interval is empty)
                    long long lo = a > c ? a : c, hi = b < d ? b : d;
                    if (c >= b || a >= d) {
                        assert(z.is_null() && z.start() == 0 && z.end() == 0);
                    } else {
                        assert(z.start() == lo && z.end() == hi && z.length() == hi - lo && z.is_null() == (lo == hi));
                    }
                    Interval w = y.intersection(x);
                    assert(w.start() == z.start() && w.end() == z.end() && w.is_null() == z.is_null());
                }
        }
    return 0;
}

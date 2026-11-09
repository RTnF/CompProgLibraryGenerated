#include <limits>
#include <vector>
#ifdef PUBLIC_MONOID
using cp::MonoidMax;
using cp::MonoidMin;
#endif

template<class T> bool identities() {
    const auto hi = MonoidMax<T>::e();
    const auto lo = MonoidMin<T>::e();
    if (MonoidMax<T>().x != hi.x || MonoidMin<T>().x != lo.x) return false;
    std::vector<T> values = {std::numeric_limits<T>::lowest(), T(-7), T(-0.0), T(0), T(7), std::numeric_limits<T>::max()};
    if constexpr (std::numeric_limits<T>::has_infinity) {
        values.push_back(-std::numeric_limits<T>::infinity());
        values.push_back(std::numeric_limits<T>::infinity());
    }
    for (T value : values) {
        const MonoidMax<T> a(value);
        const MonoidMin<T> b(value);
        if (op(a,hi).x != value || op(hi,a).x != value) return false;
        if (op(b,lo).x != value || op(lo,b).x != value) return false;
#ifdef PUBLIC_MONOID
        if (cp::op(a,hi).x != value || cp::op(hi,a).x != value) return false;
        if (cp::op(b,lo).x != value || cp::op(lo,b).x != value) return false;
#endif
    }
    return true;
}

// Neither type has ordering or unary minus. LimitsOnly's specialization also
// omits lowest/has_infinity/infinity, retaining the original e() requirements.
struct Opaque { int marker = 42; };
struct LimitsOnly { int marker; };
namespace std {
template<> class numeric_limits<LimitsOnly> {
public:
    static LimitsOnly min() { return {-23}; }
    static LimitsOnly max() { return {29}; }
};
}
int main() {
    const bool opaque = MonoidMax<Opaque>::e().x.marker == 42 &&
        MonoidMin<Opaque>::e().x.marker == 42 &&
        MonoidMax<LimitsOnly>::e().x.marker == -23 &&
        MonoidMin<LimitsOnly>::e().x.marker == 29;
    return identities<float>() && identities<double>() && identities<long double>() &&
        identities<long long>() && identities<int>() && identities<unsigned>() && opaque ? 0 : 1;
}

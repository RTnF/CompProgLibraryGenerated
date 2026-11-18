#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/modint/dynamic_modint.hpp"
#include "../library/modint/modint.hpp"
#include <cassert>
#include <limits>
#include <sstream>
#include <type_traits>

using cp::DynamicModInt;

static_assert(std::is_same_v<decltype(&DynamicModInt::pow), DynamicModInt (DynamicModInt::*)(std::int64_t) const>);
static_assert(std::is_same_v<decltype(DynamicModInt::m), std::uint32_t>);

int main() {
  cp::init();
  DynamicModInt::m = 7;
  assert(cp::C(7, 2).get() == 21);
  assert(cp::dynamic_modint::C(7, 2).get() == 0);
  assert(cp::factorial(4).get() == 3);
  assert(cp::factorial_inv(2).get() == 4);
  DynamicModInt::m = 11;
  assert(cp::dynamic_modint::C(7, 2).get() == 10);
  assert(cp::factorial(4).get() == 2);
  assert(cp::factorial_inv(2).get() == 6);

  for (std::uint32_t m : {2u, 3u, 7u, 11u, 101u, 998244353u, 4294967291u}) {
    DynamicModInt::m = m;
    const DynamicModInt a(m - 1), b(1);
    DynamicModInt t;
    assert(t.get() == 0);
    t.set(-static_cast<std::int64_t>(m));
    assert(t.get() == 0);
    const auto unsigned_max = std::numeric_limits<std::uint64_t>::max();
    t.set(unsigned_max);
    assert(t.get() == unsigned_max % m);
    assert(t == DynamicModInt(unsigned_max));
    const __int128 signed_wide = -(static_cast<__int128>(1) << 96);
    const auto remainder = (signed_wide % m + m) % m;
    assert(DynamicModInt(signed_wide).get() == remainder);
    assert(DynamicModInt(-1) == a);
    assert((a + b).get() == 0);
    assert((b - a).get() == 2 % m);
    assert((a * a) == b);
    assert((b / a) == a);
    assert((a.inv()) == a);
    assert((+a) == a && (-a) == b);
    assert(a.pow(std::numeric_limits<std::int64_t>::min()) == b);
    assert(a.pow(-3) == a && a.pow(0) == b && a.pow(3) == a);

    t = a;
    assert(t++ == a && t.get() == 0);
    assert(&++t == &t && t == b);
    assert(t-- == b && t.get() == 0);
    assert(&--t == &t && t == a);
    assert(&(t += b) == &t && t.get() == 0);
    assert(&(t -= b) == &t && t == a);
    assert(&(t *= a) == &t && t == b);
    assert(&(t /= a) == &t && t == a);

    std::istringstream input("-1");
    std::ostringstream output;
    assert(&(input >> t) == &input && t == a);
    assert(&(output << t) == &output && output.str() == std::to_string(m - 1));
    std::istringstream empty;
    assert(&(empty >> t) == &empty && empty.fail() && t.get() == 0);
  }

  DynamicModInt::m = 8;
  assert((DynamicModInt(7) + DynamicModInt(5)).get() == 4);
  assert(DynamicModInt(2).pow(3).get() == 0);
  assert(cp::factorial(4).get() == 0);
}

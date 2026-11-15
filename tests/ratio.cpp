#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number/ratio.hpp"
#include <cassert>
#include <numeric>
#include <sstream>
#include <type_traits>

namespace {
template <class T> std::string text(const cp::Ratio<T> &r) {
  std::ostringstream out;
  out << r;
  return out.str();
}

template <class T> void expect(const cp::Ratio<T> &r, long long n, long long d) {
  if (d < 0) { n = -n; d = -d; }
  if (n == 0) d = 1;
  const auto g = std::gcd(n, d);
  n /= g; d /= g;
  std::ostringstream wanted;
  wanted << static_cast<T>(n);
  if (d > 1) wanted << '/' << static_cast<T>(d);
  assert(text(r) == wanted.str());
}

template <class T> void check() {
  using R = cp::Ratio<T>;
  const R a(3, 2), b(1, 2);
  expect(a, 3, 2); expect(R(6, 4), 3, 2); expect(R(0, 5), 0, 1);
  expect(R(2), 2, 1); expect(+a, 3, 2);
  expect(a + b, 2, 1); expect(a - b, 1, 1);
  expect(a * b, 3, 4); expect(a / b, 3, 1);
  const T one = 1;
  expect(a + one, 5, 2); expect(a - one, 1, 2);
  expect(a * one, 3, 2); expect(a / one, 3, 2);
  expect(one + b, 3, 2); expect(one - b, 1, 2);
  expect(one * b, 1, 2); expect(one / b, 2, 1);
  R r = a;
  assert(&(r += b) == &r); expect(r, 2, 1);
  r = a; assert(&(r -= b) == &r); expect(r, 1, 1);
  r = a; assert(&(r *= b) == &r); expect(r, 3, 4);
  r = a; assert(&(r /= b) == &r); expect(r, 3, 1);
  r = a; expect(r /= r, 1, 1); expect(r, 1, 1);
  r = a; expect(r++, 3, 2); expect(r, 5, 2);
  assert(&(++r) == &r); expect(r, 7, 2);
  expect(r--, 7, 2); expect(r, 5, 2);
  assert(&(--r) == &r); expect(r, 3, 2);
  assert(a == R(6, 4)); assert(a != b);
  assert(a > b && b < a && a >= a && a <= a);
  assert((a <=> R(6, 4)) == std::strong_ordering::equal);
  std::istringstream input("2 4");
  R raw(7, 3);
  assert(&(input >> raw) == &input);
  assert(text(raw) == "2/4");
  constexpr bool chars = std::is_same_v<T, char> || std::is_same_v<T, signed char>
                          || std::is_same_v<T, unsigned char>;
  const R canonical(chars ? static_cast<T>('2') : T(2), chars ? static_cast<T>('4') : T(4));
  assert(raw != canonical && (raw <=> canonical) == std::strong_ordering::equal);
  if constexpr (std::is_signed_v<T>) {
    expect(-a, -3, 2); expect(R(-6, -4), 3, 2);
    expect(a / R(-1, 2), -3, 1);
    r = R(-3, 2); expect(r /= r, 1, 1);
  } else {
    expect(-R(0, 1), 0, 1);
  }
}
} // namespace

int main() {
  check<char>(); check<signed char>(); check<unsigned char>();
  check<short>(); check<unsigned short>(); check<int>(); check<unsigned>();
  check<long>(); check<long long>(); check<unsigned long long>();
  cp::Ratio<> default_type(6, 4);
  assert(text(default_type) == "3/2");
}

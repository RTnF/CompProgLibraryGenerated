#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/array/element_count.hpp"
#include <cassert>
#include <climits>
#include <deque>
#include <random>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

// Reference: maximal runs of equal adjacent elements, as (value, length).
template <class C> std::vector<std::pair<typename C::value_type, int>> reference(const C &v) {
  std::vector<std::pair<typename C::value_type, int>> runs;
  for (std::size_t i = 0; i < v.size(); ++i) {
    if (i > 0 && v[i] == v[i - 1]) runs.back().second++;
    else runs.emplace_back(v[i], 1);
  }
  return runs;
}

template <class C> void check(const C &v) {
  const auto runs = cp::element_count(v);
  static_assert(std::is_same<decltype(runs), const std::vector<std::pair<typename C::value_type, int>>>::value,
                "result type");
  assert(runs == reference(v));
}

int main() {
  // Every sequence over three values of length at most 8, for each verified instance and other containers.
  for (int length = 0, limit = 1; length <= 8; ++length, limit *= 3) {
    for (int code = 0; code < limit; ++code) {
      std::vector<int> vi(length);
      std::vector<long long> vl(length);
      std::string s(length, 'a');
      std::deque<int> d(length);
      int digits = code;
      for (int i = 0; i < length; ++i, digits /= 3) {
        vi[i] = digits % 3 - 1;
        vl[i] = (digits % 3 - 1) * (1LL << 40);
        s[i] = static_cast<char>('a' + digits % 3);
        d[i] = digits % 3;
      }
      check(vi);
      check(vl);
      check(s);
      check(d);
    }
  }
  std::mt19937_64 random(20261111);
  for (int n = 0; n <= 300; ++n) {
    std::vector<long long> v(n);
    const int alphabet = n % 4 + 1;
    for (long long &x : v) x = LLONG_MAX - static_cast<long long>(random() % alphabet);
    check(v);
  }
  // Boundaries: extreme values, one long run, empty input, the explicit result of a small case.
  check(std::vector<int>{INT_MIN, INT_MIN, INT_MAX, 0, INT_MIN});
  check(std::vector<long long>{LLONG_MIN, LLONG_MIN, LLONG_MAX, LLONG_MAX, LLONG_MAX, 0});
  assert(cp::element_count(std::vector<int>(100000, 7)) == (std::vector<std::pair<int, int>>{{7, 100000}}));
  assert(cp::element_count(std::vector<long long>{}).empty());
  assert(cp::element_count(std::vector<int>{1, 1, 2, 1}) == (std::vector<std::pair<int, int>>{{1, 2}, {2, 1}, {1, 1}}));
  check(std::vector<std::string>{"a", "a", "", "a"});
  check(std::string{'\0', '\0', '\xff', '\0'});
  return 0;
}

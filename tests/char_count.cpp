#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/string/char_count.hpp"
#include <cassert>
#include <random>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

// Reference: maximal runs of equal adjacent characters, as (character, length).
std::vector<std::pair<char, int>> reference(const std::string &s) {
  std::vector<std::pair<char, int>> runs;
  for (std::size_t i = 0; i < s.size(); ++i) {
    if (i > 0 && s[i] == s[i - 1]) runs.back().second++;
    else runs.emplace_back(s[i], 1);
  }
  return runs;
}

void check(const std::string &s) {
  const auto runs = cp::char_count(s);
  static_assert(std::is_same<decltype(runs), const std::vector<std::pair<char, int>>>::value, "result type");
  assert(runs == reference(s));
}

int main() {
  // Every string over three characters of length at most 9.
  for (int length = 0, limit = 1; length <= 9; ++length, limit *= 3) {
    for (int code = 0; code < limit; ++code) {
      std::string s(length, 'a');
      int digits = code;
      for (int i = 0; i < length; ++i, digits /= 3) s[i] = static_cast<char>('a' + digits % 3);
      check(s);
    }
  }
  std::mt19937_64 random(20261123);
  for (int n = 0; n <= 300; ++n) {
    std::string s(n, '\0');
    const int alphabet = n % 5 + 1;
    for (char &c : s) c = static_cast<char>(static_cast<unsigned char>(250 + random() % alphabet));
    check(s);
  }
  // Boundaries: empty, one character, NUL and high bytes, one long run, the explicit result of a small case.
  assert(cp::char_count("").empty());
  assert(cp::char_count("x") == (std::vector<std::pair<char, int>>{{'x', 1}}));
  check(std::string{'\0', '\0', '\xff', '\0', '\x7f', '\x80', '\x80'});
  assert(cp::char_count(std::string(100000, 'z')) == (std::vector<std::pair<char, int>>{{'z', 100000}}));
  assert(cp::char_count("aabca") ==
         (std::vector<std::pair<char, int>>{{'a', 2}, {'b', 1}, {'c', 1}, {'a', 1}}));
  return 0;
}

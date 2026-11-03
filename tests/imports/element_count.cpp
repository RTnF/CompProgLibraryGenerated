#include "experiments/library/cpp/template/small_template.hpp"
#include "experiments/verification/array/element_count.hpp"
#include "experiments/library/cpp/string/char_count.hpp"

template <class T>
std::vector<std::pair<T, int>> reference(const std::vector<T> &input) {
  std::vector<std::size_t> boundaries{0};
  for (std::size_t i = 1; i < input.size(); ++i) {
    if (!(input[i] == input[i - 1]))
      boundaries.push_back(i);
  }
  if (!input.empty())
    boundaries.push_back(input.size());
  std::vector<std::pair<T, int>> result;
  for (std::size_t i = 1; i < boundaries.size(); ++i)
    result.emplace_back(input[boundaries[i - 1]],
                        static_cast<int>(boundaries[i] - boundaries[i - 1]));
  return result;
}

int main() {
  for (int length = 0, limit = 1; length <= 8; ++length, limit *= 3) {
    for (int code = 0; code < limit; ++code) {
      std::vector<int> input(length);
      std::string chars(length, 'a');
      int digits = code;
      for (int i = 0; i < length; ++i, digits /= 3) {
        input[i] = digits % 3 - 1;
        chars[i] += digits % 3;
      }
      assert(cp::element_count(input) == reference(input));
      std::vector<char> char_input(chars.begin(), chars.end());
      assert(char_count(chars) == reference(char_input));
    }
  }
  const std::vector<int> extremes{INT_MIN, INT_MIN, INT_MAX, 0, INT_MIN};
  assert(cp::element_count(extremes) == reference(extremes));
  const std::vector<std::string> words{"a", "a", "", "a"};
  assert(cp::element_count(words) == reference(words));
  const std::string bytes{'\0', '\0', '\xff', '\0'};
  assert(char_count(bytes) == reference(std::vector<char>(bytes.begin(), bytes.end())));
}

#include "../library/merge_sort.hpp"

#include <cassert>
#include <climits>
#include <map>
#include <random>
#include <vector>

static void check_case(std::vector<int> input) {
  std::map<int, std::size_t> counts;
  for (int x : input) ++counts[x];

  input = cp::merge_sort(input);
  for (std::size_t i = 1; i < input.size(); ++i) assert(input[i - 1] <= input[i]);
  for (int x : input) {
    auto it = counts.find(x);
    assert(it != counts.end() && it->second != 0);
    --it->second;
  }
  for (const auto& [_, count] : counts) assert(count == 0);
}

int main() {
  check_case({});
  check_case({INT_MIN, INT_MAX, 0, INT_MIN, INT_MAX});
  for (int n = 0; n <= 8; ++n) {
    int cases = 1;
    for (int i = 0; i < n; ++i) cases *= 3;
    for (int code = 0; code < cases; ++code) {
      std::vector<int> input(n);
      int digits = code;
      for (int& x : input) {
        x = (digits % 3) - 1;
        digits /= 3;
      }
      check_case(input);
    }
  }
  std::mt19937_64 engine(20260928);
  std::uniform_int_distribution<int> distribution(INT_MIN, INT_MAX);
  std::vector<int> large(300000);
  for (int& x : large) x = distribution(engine);
  check_case(large);
}

#include "experiments/library/cpp/template/small_template.hpp"
#include "experiments/library/cpp/array/element_count.hpp"

// The original uninstantiated header compiles, but this use does not.
int main() {
  const auto runs = element_count(vector<int>{1, 1, 2});
  return runs.size() != 2;
}

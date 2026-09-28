#include "../library/associative_array.hpp"

#include <cstdint>
#include <iostream>

int main() {
  std::ios::sync_with_stdio(false);
  std::cin.tie(nullptr);
  int q;
  std::cin >> q;
  cp::AssociativeArray a;
  for (int i = 0; i < q; ++i) {
    int type;
    std::uint64_t key;
    std::cin >> type >> key;
    if (type == 0) {
      std::uint64_t value;
      std::cin >> value;
      cp::associative_array_set(a, key, value);
    } else {
      std::cout << cp::associative_array_get(a, key) << '\n';
    }
  }
}

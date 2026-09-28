#include "../library/associative_array.hpp"

#include <cstdint>
#include <iostream>

int main() {
  cp::AssociativeArray a;
  std::uint64_t checksum = 0;
  for (int i = 0; i < 1000000; ++i) {
    const auto key = ((static_cast<std::uint64_t>(i / 2) * 377011ULL)
                      % (1ULL << 20)) * 900000000000ULL;
    if (i % 2 == 0) {
      cp::associative_array_set(a, key, static_cast<std::uint64_t>(i));
    } else {
      checksum += cp::associative_array_get(a, key);
    }
  }
  std::cout << checksum << ' ' << a.size() << '\n';
}

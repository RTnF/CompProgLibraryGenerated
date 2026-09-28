#include "../library/associative_array.hpp"

#include <array>
#include <cassert>
#include <cstdint>
#include <random>

int main() {
  cp::AssociativeArray a;
  assert(cp::associative_array_get(a, 0) == 0);
  assert(cp::associative_array_get(a, 1000000000000000000ULL) == 0);
  cp::associative_array_set(a, 0, 1000000000000000000ULL);
  cp::associative_array_set(a, 1000000000000000000ULL, 7);
  assert(cp::associative_array_get(a, 0) == 1000000000000000000ULL);
  assert(cp::associative_array_get(a, 1000000000000000000ULL) == 7);
  cp::associative_array_set(a, 0, 0);
  assert(cp::associative_array_get(a, 0) == 0);
  assert(cp::associative_array_get(a, 1) == 0);

  std::array<std::uint64_t, 1000> oracle{};
  std::mt19937_64 rng(1234567);
  for (int i = 0; i < 10000; ++i) {
    const auto key = rng() % 1000;
    if ((rng() & 1) == 0) {
      const auto value = rng() % 1000000000000000001ULL;
      cp::associative_array_set(a, key, value);
      oracle[key] = value;
    } else {
      assert(cp::associative_array_get(a, key) == oracle[key]);
    }
  }
}

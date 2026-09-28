#include "../library/merge_sort.hpp"

#include <chrono>
#include <climits>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <random>
#include <vector>

int main() {
  constexpr std::size_t n = 300000;
  constexpr std::uint64_t seed = 20260928;
  constexpr int runs = 5;

  std::cout << "n=" << n << " first_seed=" << seed << " runs=" << runs << '\n';
  for (int run = 0; run < runs; ++run) {
    const std::uint64_t run_seed = seed + run;
    std::mt19937_64 engine(run_seed);
    std::uniform_int_distribution<int> distribution(INT_MIN, INT_MAX);
    std::vector<int> values(n);
    for (int& x : values) x = distribution(engine);
    std::uint64_t input_hash = 1469598103934665603ULL;
    for (int x : values) {
      input_hash ^= static_cast<std::uint32_t>(x);
      input_hash *= 1099511628211ULL;
    }
    const auto start = std::chrono::steady_clock::now();
    values = cp::merge_sort(values);
    const auto end = std::chrono::steady_clock::now();
    for (std::size_t i = 1; i < values.size(); ++i) {
      if (values[i - 1] > values[i]) return 1;
    }
    const auto elapsed = std::chrono::duration<double, std::milli>(end - start).count();
    std::cout << "run=" << run + 1 << " seed=" << run_seed << " input_hash=" << input_hash
              << " ms=" << std::fixed << std::setprecision(3) << elapsed << '\n';
    if (elapsed >= 2000.0) return 2;
  }
}

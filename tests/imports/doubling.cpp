#include "../../experiments/library/cpp/template/small_template.hpp"
#include "../../library/doubling.hpp"
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>

// Follow the functional graph until its first cycle, then reduce the exponent.
// This reference does not build or use a doubling table.
int follow(const std::vector<int> &v, int start, std::uint64_t steps) {
  std::vector<int> position(v.size(), -1), path;
  int vertex = start;
  while (position[vertex] == -1) {
    position[vertex] = static_cast<int>(path.size());
    path.push_back(vertex);
    vertex = v[vertex];
  }
  if (steps < path.size()) return path[static_cast<std::size_t>(steps)];
  const auto prefix = static_cast<std::uint64_t>(position[vertex]);
  const auto cycle = static_cast<std::uint64_t>(path.size()) - prefix;
  return path[static_cast<std::size_t>(prefix + (steps - prefix) % cycle)];
}

int reference_width(std::uint64_t value) {
  return value == 0 ? 0 : 64 - __builtin_clzll(value);
}

void check_graph(const std::vector<int> &v) {
  const std::array<std::uint64_t, 14> maxima = {
    1, 2, 3, 4, 5, 7, 8, 9, 31, 32, 33,
    std::uint64_t(1) << 32, std::uint64_t(1) << 63, UINT64_MAX};
  for (const auto maximum : maxima) {
    const auto before = v;
    const auto table = cp::doubling(v, maximum);
    assert(v == before);
    assert(table.size() == static_cast<std::size_t>(reference_width(maximum)));
    for (std::size_t level = 0; level < table.size(); ++level) {
      assert(table[level].size() == v.size());
      for (std::size_t vertex = 0; vertex < v.size(); ++vertex) {
        assert(table[level][vertex] == follow(v, static_cast<int>(vertex), std::uint64_t(1) << level));
      }
    }
  }
}

int main() {
  for (std::uint64_t value = 0; value < 4096; ++value)
    assert(cp::bit_width_u64(value) == reference_width(value));
  for (unsigned shift = 0; shift < 64; ++shift) {
    const auto power = std::uint64_t(1) << shift;
    for (const auto value : {power - 1, power, power + 1})
      assert(cp::bit_width_u64(value) == reference_width(value));
  }
  std::uint64_t seed = 0x57a43a98538efed1ULL;
  for (int trial = 0; trial < 20000; ++trial) {
    seed ^= seed << 13;
    seed ^= seed >> 7;
    seed ^= seed << 17;
    assert(cp::bit_width_u64(seed) == reference_width(seed));
  }
  std::size_t graphs = 0;
  for (int n = 0; n <= 5; ++n) {
    int encodings = 1;
    for (int i = 0; i < n; ++i) encodings *= n;
    for (int encoding = 0; encoding < encodings; ++encoding) {
      int rest = encoding;
      std::vector<int> successors(n);
      for (int &vertex : successors) { vertex = rest % n; rest /= n; }
      check_graph(successors);
      ++graphs;
    }
  }
  assert(graphs == 3414);
  std::cout << "doubling functional graphs passed: " << graphs << '\n';
}

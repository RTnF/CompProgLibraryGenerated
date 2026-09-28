#include <cstdint>
#include <map>

namespace cp {

// Keys and values are in [0, 10^18] for Library Checker.
using AssociativeArray = std::map<std::uint64_t, std::uint64_t>;

inline void associative_array_set(AssociativeArray& data,
                                  std::uint64_t key, std::uint64_t value) {
  data.insert_or_assign(key, value);
}

inline std::uint64_t associative_array_get(const AssociativeArray& data,
                                           std::uint64_t key) {
  const auto it = data.find(key);
  return it == data.end() ? 0 : it->second;
}

}  // namespace cp

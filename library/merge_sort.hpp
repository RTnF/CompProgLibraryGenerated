#include <cstddef>
#include <vector>

namespace cp {

// Merge sort for signed int values; verified for at most 300000 elements.
inline std::vector<int> merge_sort(std::vector<int> values) {
  const std::size_t n = values.size();
  if (n < 2) return values;

  const std::size_t mid = n / 2 + n % 2;
  const std::vector<int> left = merge_sort(
      std::vector<int>(values.begin(), values.begin() + mid));
  const std::vector<int> right = merge_sort(
      std::vector<int>(values.begin() + mid, values.end()));

  std::vector<int> merged;
  merged.reserve(n);
  std::size_t i = 0, j = 0;
  while (i < left.size() && j < right.size()) {
    if (left[i] <= right[j]) {
      merged.push_back(left[i++]);
    } else {
      merged.push_back(right[j++]);
    }
  }
  while (i < left.size()) merged.push_back(left[i++]);
  while (j < right.size()) merged.push_back(right[j++]);
  return merged;
}

}  // namespace cp

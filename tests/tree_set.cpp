#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/set/tree_set.hpp"
#include <algorithm>
#include <array>
#include <cassert>
#include <iterator>
#include <limits>
#include <random>
#include <type_traits>
#include <vector>

static_assert(std::is_same_v<cp::TreeSet<>, cp::TreeSet<ll>>);

namespace {

struct Key {
  static inline int live = 0;
  int value;
  explicit Key(int value) : value(value) { ++live; }
  Key(Key &other) : Key(other.value) {}
  Key &operator=(const Key &) = delete;
  ~Key() { --live; }
  friend bool operator<(Key &left, Key &right) { return left.value < right.value; }
};

void check_custom_key() {
  {
    cp::TreeSet<Key> tree;
    tree.add(Key(9));
    tree.add(Key(3));
    tree.add(Key(9));
    tree.remove(Key(5));
    assert(Key::live == 2);
    assert(tree.size() == 2 && tree.min().value == 3 && tree.max().value == 9);
    assert(tree.find(Key(9)));
    assert(tree.get_kth(1).value == 9);
    assert((tree.rank(Key(9)) == std::pair<int, int>{1, 2}));
    assert(tree.find_lower(Key(6))->value == 3);
    assert(tree.find_upper(Key(6))->value == 9);
    auto copy = tree;
    assert(Key::live == 4);
    copy.remove(Key(3));
    assert(Key::live == 3);
    assert(copy.size() == 1 && !copy.find(Key(3)));
    assert(tree.size() == 2 && tree.find(Key(3)));
    copy = tree;
    auto moved = std::move(copy);
    assert(moved.size() == 2 && moved.get_kth(0).value == 3);
    copy = std::move(moved);
    copy.remove(Key(9));
    assert(copy.size() == 1 && tree.size() == 2);
  }
  assert(Key::live == 0);
}

void check_integer_keys() {
  std::mt19937 random(20261126);
  cp::TreeSet<> tree;
  std::array<bool, 128> present{};
  assert(tree.size() == 0);
  assert(!tree.find_lower(0) && !tree.find_upper(0));
  assert((tree.rank(0) == std::pair<int, int>{-1, -1}));
  for (int step = 0; step < 4000; ++step) {
    const int index = static_cast<int>(random() % present.size());
    const int key = index - 64;
    if (random() % 2 != 0) {
      tree.add(key);
      present[index] = true;
    } else {
      tree.remove(key);
      present[index] = false;
    }
    std::vector<int> sorted;
    for (int i = 0; i < static_cast<int>(present.size()); ++i) {
      assert(tree.find(i - 64) == present[i]);
      if (present[i]) sorted.push_back(i - 64);
    }
    assert(tree.size() == static_cast<int>(sorted.size()));
    const auto upper = std::lower_bound(sorted.begin(), sorted.end(), key);
    const auto after_lower = std::upper_bound(sorted.begin(), sorted.end(), key);
    const auto actual_upper = tree.find_upper(key);
    const auto actual_lower = tree.find_lower(key);
    assert(actual_upper.has_value() == (upper != sorted.end()));
    assert(actual_lower.has_value() == (after_lower != sorted.begin()));
    if (actual_upper) assert(*actual_upper == *upper);
    if (actual_lower) assert(*actual_lower == *std::prev(after_lower));
    std::pair<int, int> rank{-1, -1};
    if (present[index]) {
      const int position = static_cast<int>(upper - sorted.begin());
      rank = {position, position + 1};
    }
    assert(tree.rank(key) == rank);
    if (!sorted.empty()) {
      const std::size_t position = random() % sorted.size();
      assert(tree.get_kth(position) == sorted[position]);
      assert(tree.min() == sorted.front());
      assert(tree.max() == sorted.back());
    }
  }
}

void check_ordered_updates() {
  constexpr int count = 4096;
  for (bool ascending : {false, true}) {
    cp::TreeSet<int> tree;
    for (int i = 0; i < count; ++i) tree.add(ascending ? i : count - i - 1);
    for (int i = 0; i < count; ++i) {
      assert((tree.rank(i) == std::pair<int, int>{i, i + 1}));
      assert(tree.get_kth(i) == i);
    }
    assert(!tree.find_lower(std::numeric_limits<int>::min()));
    assert(!tree.find_upper(std::numeric_limits<int>::max()));
    for (int i = 0; i < count; i += 2) tree.remove(i);
    for (int i = 0; i < count / 2; ++i) assert(tree.get_kth(i) == 2 * i + 1);
    for (int i = 1; i < count; i += 2) tree.remove(i);
    assert(tree.size() == 0);
  }
}

} // namespace

int main() {
  check_custom_key();
  check_integer_keys();
  check_ordered_updates();
}

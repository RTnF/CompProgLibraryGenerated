#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/set/tree_set.hpp"
#include <array>
#include <cassert>
#include <random>

namespace {

struct Key {
  static inline int live = 0;
  int value;
  explicit Key(int value) : value(value) { ++live; }
  Key(Key &other) : Key(other.value) {}
  ~Key() { --live; }
  friend bool operator<(Key &left, Key &right) { return left.value < right.value; }
  friend bool operator==(Key &left, Key &right) { return left.value == right.value; }
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
    auto copy = tree;
    assert(Key::live == 4);
    copy.remove(Key(3));
    assert(Key::live == 3);
    assert(copy.size() == 1 && !copy.find(Key(3)));
    assert(tree.size() == 2 && tree.find(Key(3)));
  }
  assert(Key::live == 0);
}

void check_integer_keys() {
  std::mt19937 random(20261126);
  cp::TreeSet<> tree;
  std::array<bool, 128> present{};
  assert(tree.size() == 0);
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
    int first = 0;
    int last = 0;
    int count = 0;
    for (int i = 0; i < static_cast<int>(present.size()); ++i) {
      assert(tree.find(i - 64) == present[i]);
      if (present[i]) {
        if (count == 0) first = i - 64;
        last = i - 64;
        ++count;
      }
    }
    assert(tree.size() == count);
    if (count != 0) {
      assert(tree.min() == first);
      assert(tree.max() == last);
    }
  }
}

} // namespace

int main() {
  check_custom_key();
  check_integer_keys();
}

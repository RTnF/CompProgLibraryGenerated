#include "template/small_template.hpp"
#include "set/set.hpp"
#include <cassert>

struct Key {
  static inline int live = 0;
  int value;

  explicit Key(int value) : value(value) { ++live; }
  Key(Key &other) : Key(other.value) {}
  ~Key() { --live; }

  friend bool operator<(Key &left, Key &right) { return left.value < right.value; }
  friend bool operator==(Key &left, Key &right) { return left.value == right.value; }
};

int main() {
  {
    TreeSet<Key> source;
    source.remove(Key(8));
    assert(source.size() == 0);
    source.add(Key(7));
    source.add(Key(8));
    source.add(Key(7));
    source.remove(Key(9));
    assert(Key::live == 2 && source.size() == 2);
    assert(source.find(Key(7)) && source.min().value == 7 && source.max().value == 8);
    auto copy = source;
    copy.remove(Key(7));
    assert(Key::live == 3 && copy.size() == 1);
    assert(!copy.find(Key(7)) && source.find(Key(7)) && source.size() == 2);
  }
  assert(Key::live == 0);
}

#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/set/tree_multiset.hpp"
#ifdef TEST_ORIGINAL_TREE_MULTISET
#include "../experiments/library/cpp/set/multiset.hpp"
#endif

#include <array>
#include <cassert>
#include <limits>
#include <map>
#include <random>
#include <sstream>
#include <type_traits>
#include <utility>

namespace {

void check_updates_against_map() {
#ifdef TEST_ORIGINAL_TREE_MULTISET
  std::array<TreeMultiSet<long long>, 2> original;
#endif
  std::array<cp::TreeMultiSet<long long>, 2> candidate;
  std::array<std::map<long long, std::size_t>, 2> expected;
  std::mt19937_64 random(277);
  for (int i = 0; i < 2400; ++i) {
    const auto instance = random() % candidate.size();
#ifdef TEST_ORIGINAL_TREE_MULTISET
    auto &old = original[instance];
#endif
    auto &now = candidate[instance];
    auto &keys = expected[instance];
    const auto key = static_cast<long long>(random() % 41) - 20;
    const auto count = static_cast<std::size_t>(random() % 7);
    const auto it = keys.find(key);
    const auto before = it == keys.end() ? 0 : it->second;
    switch (random() % 4) {
    case 0:
    case 1:
#ifdef TEST_ORIGINAL_TREE_MULTISET
      assert(old.add(key, count) == before + count);
#endif
      assert(now.add(key, count) == before + count);
      if (count != 0) keys[key] = before + count;
      break;
    case 2: {
      const bool removed = it != keys.end() && before >= count;
#ifdef TEST_ORIGINAL_TREE_MULTISET
      assert(old.remove(key, count) == removed);
#endif
      assert(now.remove(key, count) == removed);
      if (removed && before == count) keys.erase(it);
      else if (removed) it->second -= count;
      break;
    }
    default:
#ifdef TEST_ORIGINAL_TREE_MULTISET
      assert(old.remove_all(key) == before);
#endif
      assert(now.remove_all(key) == before);
      keys.erase(key);
      break;
    }
#ifdef TEST_ORIGINAL_TREE_MULTISET
    assert(old.enumerate_all() == now.enumerate_all());
    assert(old.count(key) == now.count(key));
#endif
    std::size_t total = 0;
    for (const auto &[k, multiplicity] : keys) {
      assert(now.count(k) == multiplicity);
      total += multiplicity;
    }
    assert(now.size() == total);
  }
  assert(candidate[0].add(100) == 1);
  assert(candidate[0].remove(100));
#ifdef TEST_ORIGINAL_TREE_MULTISET
  assert(original[0].add(100) == 1);
  assert(original[0].remove(100));
#endif
}

struct ConvertedKey {
  int id = 0;
  ConvertedKey() = default;
  explicit ConvertedKey(int value) : id(value) {}
  operator int() const { return id + 1000; }

  friend bool operator<(const ConvertedKey &left, const ConvertedKey &right) { return left.id < right.id; }
  friend bool operator==(const ConvertedKey &left, const ConvertedKey &right) { return left.id == right.id; }
};

void check_converted_parent() {
#ifdef TEST_ORIGINAL_TREE_MULTISET
  TreeMultiSet<ConvertedKey> original;
#endif
  cp::TreeMultiSet<ConvertedKey> candidate;
  for (int i : {4, 5, -2, 7, 0, 3, 6, -1, 10, 34, 27}) {
#ifdef TEST_ORIGINAL_TREE_MULTISET
    original.add(ConvertedKey(i), 2);
#endif
    candidate.add(ConvertedKey(i), 2);
  }
#ifdef TEST_ORIGINAL_TREE_MULTISET
  assert(original.enumerate_all() == candidate.enumerate_all());
  assert(original.enumerate(ConvertedKey(0), ConvertedKey(10)) == candidate.enumerate(ConvertedKey(0), ConvertedKey(10)));
#endif
  const auto all = candidate.enumerate_all();
  bool sawConvertedParent = false;
  for (const auto &[key, count, parent] : all) {
    assert(count == 2);
    if (parent.id > 900) sawConvertedParent = true;
  }
  assert(sawConvertedParent);
}

struct MutableKey {
  static int alive;
  long long value = 0;

  MutableKey() { ++alive; }
  explicit MutableKey(long long initial) : value(initial) { ++alive; }
  MutableKey(MutableKey &other) : value(other.value) { ++alive; }
  MutableKey(const MutableKey &) = delete;
  MutableKey(MutableKey &&) = delete;
  ~MutableKey() { --alive; }

  friend bool operator<(MutableKey &left, MutableKey &right) { return left.value < right.value; }
  friend bool operator==(MutableKey &left, MutableKey &right) { return left.value == right.value; }
};

int MutableKey::alive = 0;

void check_ownership() {
  using Tree = cp::TreeMultiSet<MutableKey>;
  static_assert(std::is_nothrow_default_constructible_v<Tree>);
  static_assert(std::is_copy_constructible_v<Tree>);
  static_assert(std::is_nothrow_move_constructible_v<Tree>);
  static_assert(!std::is_copy_assignable_v<Tree>);
  static_assert(!std::is_move_assignable_v<Tree>);
  {
    Tree original;
    for (long long i : {5, 3, 7, 2, 4, 6, 8}) assert(original.add(MutableKey(i), 2) == 2);
    assert(original.remove_all(MutableKey(4)) == 2);
    assert(MutableKey::alive == 6);
    const Tree &view = original;
    Tree copy(view);
    assert(MutableKey::alive == 12);
    assert(copy.remove_all(MutableKey(2)) == 2);
    assert(original.count(MutableKey(2)) == 2);
    assert(MutableKey::alive == 11);
    Tree moved(std::move(copy));
    assert(MutableKey::alive == 11);
    assert(copy.size() == 0 && moved.size() == 10);
    assert(copy.add(MutableKey(12)) == 1);
    assert(moved.count(MutableKey(12)) == 0);
    assert(original.count(MutableKey(12)) == 0);
    assert(moved.add(MutableKey(13), 3) == 3);
    assert(moved.count(MutableKey(13)) == 3);
    original.verify();
    copy.verify();
    moved.verify();
  }
  assert(MutableKey::alive == 0);
}

#ifdef TEST_ORIGINAL_TREE_MULTISET
void check_original_repairs() {
  TreeMultiSet<double> original;
  assert(original.add(1.75, 0) == 0);
  original.add(1.5, 2);
  original.add(1.75, 2);
  assert(original.enumerate(1.5, 2.0).size() == 2);
  TreeMultiSet<double> copy(original);
  assert(copy.remove(1.75, 2));
  assert(copy.count(1.75) == 0 && original.count(1.75) == 2);
  TreeMultiSet<double> moved(std::move(copy));
  assert(copy.size() == 0 && moved.size() == 2);
  copy.add(3.0);
  assert(moved.count(3.0) == 0);
  original.verify();
  moved.verify();
}
#endif

void check_ranges_and_order() {
  cp::TreeMultiSet<double> values;
  assert(values.enumerate(1.0, 3.0).empty());
  assert(values.add(2.5, 0) == 0);
  assert(!values.remove(2.5, 0));
  values.add(2.0, 2);
  values.add(2.5, 3);
  values.add(3.0);
  assert(values.min() == 2.0 && values.max() == 3.0);
  assert(values.get_kth(0) == 2.0 && values.get_kth(2) == 2.5);
  assert(values.get_kth(5) == 3.0);
  assert((values.rank(2.5) == std::pair<int, int>(2, 5)));
  assert((values.rank(2.75) == std::pair<int, int>(-1, -1)));
  assert(values.find_lower(2.75) == 2.5 && values.find_upper(2.75) == 3.0);
  assert(!values.find_lower(1.0) && !values.find_upper(4.0));
  const auto range = values.enumerate(2.0, 3.0);
  assert(range.size() == 2);
  assert(std::get<0>(range[0]) == 2.0 && std::get<1>(range[0]) == 2);
  assert(std::get<0>(range[1]) == 2.5 && std::get<1>(range[1]) == 3);
  assert(values.enumerate(3.0, 2.0).empty());

  std::ostringstream output;
  auto *saved = std::cout.rdbuf(output.rdbuf());
  values.aoj_dump(2.5, 3.0);
  std::cout.rdbuf(saved);
  assert(output.str() == "2.5\n2.5\n2.5\n3\n");
  assert(values.remove(2.5, 3));
  assert(values.count(2.5) == 0);
  values.verify();

  cp::TreeMultiSet<int> limits;
  for (int key : {std::numeric_limits<int>::min(), 0, std::numeric_limits<int>::max()}) {
    limits.add(key);
  }
  assert(limits.enumerate(std::numeric_limits<int>::min(), 0).size() == 1);
  assert(limits.enumerate(1, std::numeric_limits<int>::min()).empty());
}

} // namespace

int main() {
  static_assert(std::is_same_v<cp::TreeMultiSet<>, cp::TreeMultiSet<std::int64_t>>);
#ifdef TEST_ORIGINAL_TREE_MULTISET
  static_assert(std::is_same_v<TreeMultiSet<>, TreeMultiSet<std::int64_t>>);
  static_assert(std::is_nothrow_default_constructible_v<TreeMultiSet<>>);
  static_assert(std::is_nothrow_move_constructible_v<TreeMultiSet<>>);
#endif
  check_updates_against_map();
  check_converted_parent();
  check_ownership();
  check_ranges_and_order();
#ifdef TEST_ORIGINAL_TREE_MULTISET
  check_original_repairs();
#endif
}

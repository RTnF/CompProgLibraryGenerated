#pragma once
#include <cassert>
#include <cstdint>
#include <deque>
#include <iostream>
#include <memory>
#include <optional>
#include <tuple>
#include <utility>
#include <vector>

namespace cp {

// Store the xorshift state relative to the original fixed seed.
static std::uint64_t multiset_priority_offset;

static inline std::uint64_t multiset_next_priority() {
  std::uint64_t x = multiset_priority_offset ^ 192865741288175612ull;
  x ^= x << 7;
  x ^= x >> 9;
  multiset_priority_offset = x ^ 192865741288175612ull;
  return x;
}

template <class T = std::int64_t> class TreeMultiSet {
  static const std::size_t none;

  struct Slot {
    mutable std::optional<T> key;
    std::uint64_t priority;
    std::size_t count;
    std::size_t total;
    std::size_t left;
    std::size_t right;
  };

  // Allocate storage on the first insertion so moving a tree does not allocate.
  std::unique_ptr<std::deque<Slot>> slots;
  std::size_t root;
  std::size_t free_head;

  std::size_t allocate(T key, std::size_t count, std::uint64_t priority) {
    if (free_head == none) {
      if (slots.get() == nullptr) slots = std::make_unique<std::deque<Slot>>();
      (*slots).emplace_back();
      free_head = (slots.get() == nullptr ? 0 : (*slots).size()) - 1;
      (*slots)[free_head].left = none;
    }
    std::size_t index = free_head;
    (*slots)[index].key.emplace(key);
    free_head = (*slots)[index].left;
    (*slots)[index].priority = priority;
    (*slots)[index].count = count;
    (*slots)[index].total = count;
    (*slots)[index].left = none;
    (*slots)[index].right = none;
    return index;
  }

  void release(std::size_t index) {
    (*slots)[index].key.reset();
    (*slots)[index].left = free_head;
    free_head = index;
  }

  std::size_t weight(std::size_t index) const {
    return index == none ? 0 : (*slots)[index].total;
  }

  void update(std::size_t index) {
    (*slots)[index].total = (*slots)[index].count + weight((*slots)[index].left) + weight((*slots)[index].right);
  }

  std::pair<std::size_t, std::size_t> split(std::size_t index, T key) {
    if (index == none) return {none, none};
    if (key < (*slots)[index].key.value()) {
      auto [lower, upper] = split((*slots)[index].left, key);
      (*slots)[index].left = upper;
      update(index);
      return {lower, index};
    }
    auto [lower, upper] = split((*slots)[index].right, key);
    (*slots)[index].right = lower;
    update(index);
    return {index, upper};
  }

  std::size_t merge(std::size_t left, std::size_t right) {
    if (left == none) return right;
    if (right == none) return left;
    if ((*slots)[left].priority > (*slots)[right].priority) {
      (*slots)[left].right = merge((*slots)[left].right, right);
      update(left);
      return left;
    }
    (*slots)[right].left = merge(left, (*slots)[right].left);
    update(right);
    return right;
  }

  std::size_t insert(std::size_t index, std::size_t item) {
    if (index == none) return item;
    if ((*slots)[item].priority > (*slots)[index].priority) {
      auto [lower, upper] = split(index, (*slots)[item].key.value());
      (*slots)[item].left = lower;
      (*slots)[item].right = upper;
      update(item);
      return item;
    }
    if ((*slots)[item].key.value() < (*slots)[index].key.value()) {
      (*slots)[index].left = insert((*slots)[index].left, item);
    } else {
      (*slots)[index].right = insert((*slots)[index].right, item);
    }
    update(index);
    return index;
  }

  std::size_t erase(std::size_t index, T key) {
    if ((*slots)[index].key.value() == key) {
      const std::size_t replacement = merge((*slots)[index].left, (*slots)[index].right);
      release(index);
      return replacement;
    }
    if (key < (*slots)[index].key.value()) {
      (*slots)[index].left = erase((*slots)[index].left, key);
    } else {
      (*slots)[index].right = erase((*slots)[index].right, key);
    }
    update(index);
    return index;
  }

  std::size_t locate(T key) {
    std::size_t index = root;
    while (index != none) {
      if (key == (*slots)[index].key.value()) return index;
      index = key < (*slots)[index].key.value() ? (*slots)[index].left : (*slots)[index].right;
    }
    return none;
  }

  void replace_count(std::size_t index, T key, std::size_t count) {
    if (key == (*slots)[index].key.value()) {
      (*slots)[index].count = count;
    } else if (key < (*slots)[index].key.value()) {
      replace_count((*slots)[index].left, key, count);
    } else {
      replace_count((*slots)[index].right, key, count);
    }
    update(index);
  }

  void enumerate_in(std::vector<std::tuple<T, std::size_t, T>> &out,
                    std::size_t index, const T &lo, const T &hi, std::size_t parent) {
    if (index == none) return;
    if (lo < (*slots)[index].key.value()) enumerate_in(out, (*slots)[index].left, lo, hi, index);
    if (!((*slots)[index].key.value() < lo)) {
      if ((*slots)[index].key.value() < hi) {
        auto parentKey = parent != none ? (*slots)[parent].key.value() : -1;
        out.emplace_back((*slots)[index].key.value(), (*slots)[index].count, std::move(parentKey));
      }
    }
    if ((*slots)[index].key.value() < hi) enumerate_in(out, (*slots)[index].right, lo, hi, index);
  }

  void enumerate_all_in(std::vector<std::tuple<T, std::size_t, T>> &out,
                        std::size_t index, std::size_t parent) {
    if (index == none) return;
    enumerate_all_in(out, (*slots)[index].left, index);
    auto parentKey = parent != none ? (*slots)[parent].key.value() : -1;
    out.emplace_back((*slots)[index].key.value(), (*slots)[index].count, std::move(parentKey));
    enumerate_all_in(out, (*slots)[index].right, index);
  }

  void dump_in(std::size_t index, T lo, T hi, std::ostream &output) {
    if (index == none) return;
    if (lo < (*slots)[index].key.value()) dump_in((*slots)[index].left, lo, hi, output);
    if (lo <= (*slots)[index].key.value()) {
      if ((*slots)[index].key.value() <= hi) {
        for (std::size_t i = 0; i < (*slots)[index].count; ++i) output << (*slots)[index].key.value() << '\n';
      }
    }
    if ((*slots)[index].key.value() < hi) dump_in((*slots)[index].right, lo, hi, output);
  }

  void add_distinct(T key, std::size_t count, std::uint64_t priority) {
    std::size_t item = allocate(key, count, priority);
    root = insert(root, item);
  }

  std::size_t check_total(std::size_t index) const {
    if (index == none) return 0;
    const std::size_t left = check_total((*slots)[index].left);
    const std::size_t right = check_total((*slots)[index].right);
    const std::size_t actual = (*slots)[index].count + left + right;
    assert(actual == (*slots)[index].total);
    return actual;
  }

public:
  TreeMultiSet() noexcept : slots(), root(none), free_head(none) {}

  TreeMultiSet(const TreeMultiSet &other) : slots(), root(other.root), free_head(other.free_head) {
    for (std::size_t i = 0; i < (other.slots.get() == nullptr ? 0 : (*other.slots).size()); ++i) {
      if (slots.get() == nullptr) slots = std::make_unique<std::deque<Slot>>();
      (*slots).emplace_back();
      if ((*other.slots)[i].key.has_value()) (*slots)[i].key.emplace((*other.slots)[i].key.value());
      (*slots)[i].priority = (*other.slots)[i].priority;
      (*slots)[i].count = (*other.slots)[i].count;
      (*slots)[i].total = (*other.slots)[i].total;
      (*slots)[i].left = (*other.slots)[i].left;
      (*slots)[i].right = (*other.slots)[i].right;
    }
  }

  TreeMultiSet(TreeMultiSet &&other) noexcept : slots(), root(other.root), free_head(other.free_head) {
    slots.swap(other.slots);
    other.root = none;
    other.free_head = none;
  }

  TreeMultiSet &operator=(const TreeMultiSet &) = delete;
  TreeMultiSet &operator=(TreeMultiSet &&) = delete;

  std::size_t add(T key, std::size_t n = 1) {
    const std::size_t found = locate(key);
    if (n == 0) return found == none ? 0 : (*slots)[found].count;
    if (found == none) {
      const std::uint64_t priority = multiset_next_priority();
      add_distinct(key, n, priority);
      return n;
    }
    const std::size_t count = (*slots)[found].count + n;
    replace_count(root, key, count);
    return count;
  }

  bool remove(T key, std::size_t n = 1) {
    const std::size_t found = locate(key);
    if (found == none) return false;
    const std::size_t count = (*slots)[found].count;
    if (count < n) return false;
    if (count == n) root = erase(root, key);
    else replace_count(root, key, count - n);
    return true;
  }

  std::size_t remove_all(T key) {
    const std::size_t found = locate(key);
    if (found == none) return 0;
    const std::size_t count = (*slots)[found].count;
    root = erase(root, key);
    return count;
  }

  std::size_t count(T key) {
    const std::size_t found = locate(key);
    return found == none ? 0 : (*slots)[found].count;
  }

  std::size_t size() { return weight(root); }

  std::optional<T> find_lower(T key) {
    std::size_t index = root;
    std::size_t lower = none;
    while (index != none) {
      if (key == (*slots)[index].key.value()) return std::optional<T>(key);
      if (key < (*slots)[index].key.value()) {
        index = (*slots)[index].left;
      } else {
        lower = index;
        index = (*slots)[index].right;
      }
    }
    if (lower == none) return std::optional<T>();
    return std::optional<T>((*slots)[lower].key.value());
  }

  std::optional<T> find_upper(T key) {
    std::size_t index = root;
    std::size_t upper = none;
    while (index != none) {
      if (key == (*slots)[index].key.value()) return std::optional<T>(key);
      if (key < (*slots)[index].key.value()) {
        upper = index;
        index = (*slots)[index].left;
      } else {
        index = (*slots)[index].right;
      }
    }
    if (upper == none) return std::optional<T>();
    return std::optional<T>((*slots)[upper].key.value());
  }

  std::pair<int, int> rank(T key) {
    std::size_t index = root;
    std::size_t offset = 0;
    while (index != none) {
      if (key == (*slots)[index].key.value()) {
        const std::size_t first = offset + weight((*slots)[index].left);
        return {static_cast<int>(first), static_cast<int>(first + (*slots)[index].count)};
      }
      if (key < (*slots)[index].key.value()) {
        index = (*slots)[index].left;
      } else {
        offset += weight((*slots)[index].left) + (*slots)[index].count;
        index = (*slots)[index].right;
      }
    }
    return {-1, -1};
  }

  T min() {
    std::size_t index = root;
    assert(index != none);
    while ((*slots)[index].left != none) index = (*slots)[index].left;
    return (*slots)[index].key.value();
  }

  T max() {
    std::size_t index = root;
    assert(index != none);
    while ((*slots)[index].right != none) index = (*slots)[index].right;
    return (*slots)[index].key.value();
  }

  T get_kth(std::size_t position) {
    assert(position < weight(root));
    std::size_t index = root;
    for (;;) {
      const std::size_t less = weight((*slots)[index].left);
      if (position < less) {
        index = (*slots)[index].left;
      } else if (position < less + (*slots)[index].count) {
        return (*slots)[index].key.value();
      } else {
        position -= less + (*slots)[index].count;
        index = (*slots)[index].right;
      }
    }
  }

  std::vector<std::tuple<T, std::size_t, T>> enumerate(const T &lo, const T &hi) {
    std::vector<std::tuple<T, std::size_t, T>> rows;
    enumerate_in(rows, root, lo, hi, none);
    return rows;
  }

  std::vector<std::tuple<T, std::size_t, T>> enumerate_all() {
    std::vector<std::tuple<T, std::size_t, T>> rows;
    enumerate_all_in(rows, root, none);
    return rows;
  }

  void aoj_dump(const T &lo, const T &hi) {
    if (root != none) dump_in(root, lo, hi, std::cout);
  }

  void verify() {
    if (root != none) {
      const std::size_t actual = check_total(root);
      assert(actual == weight(root));
    }
  }
};

template<class T> const std::size_t TreeMultiSet<T>::none = ~std::size_t(0);

} // namespace cp

#pragma once
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <memory>
#include <optional>
#include <utility>

namespace cp {

template <class T = std::int64_t> class TreeSet {
  static const std::size_t none;

  struct Slot {
    mutable std::optional<T> key;
    std::size_t left;
    std::size_t right;
    std::size_t height;
    std::size_t size;
    std::size_t first;
    std::size_t last;
  };

  std::unique_ptr<std::deque<Slot>> slots;
  std::size_t root;
  std::size_t free_head;

  std::size_t subtree_size(std::size_t index) const {
    return index == none ? 0 : (*slots)[index].size;
  }

  std::size_t subtree_height(std::size_t index) const {
    return index == none ? 0 : (*slots)[index].height;
  }

  std::size_t allocate(T key) {
    if (free_head == none) {
      if (slots.get() == nullptr) slots = std::make_unique<std::deque<Slot>>();
      (*slots).emplace_back();
      free_head = (slots.get() == nullptr ? 0 : (*slots).size()) - 1;
      (*slots)[free_head].left = none;
    }
    const std::size_t index = free_head;
    (*slots)[index].key.emplace(key);
    free_head = (*slots)[index].left;
    (*slots)[index].left = none;
    (*slots)[index].right = none;
    (*slots)[index].height = 1;
    (*slots)[index].size = 1;
    (*slots)[index].first = index;
    (*slots)[index].last = index;
    return index;
  }

  void release(std::size_t index) {
    (*slots)[index].key.reset();
    (*slots)[index].left = free_head;
    free_head = index;
  }

  void refresh(std::size_t index) {
    const std::size_t left = (*slots)[index].left;
    const std::size_t right = (*slots)[index].right;
    const std::size_t a = subtree_height(left);
    const std::size_t b = subtree_height(right);
    (*slots)[index].height = 1 + (a < b ? b : a);
    (*slots)[index].size = 1 + subtree_size(left) + subtree_size(right);
    (*slots)[index].first = left == none ? index : (*slots)[left].first;
    (*slots)[index].last = right == none ? index : (*slots)[right].last;
  }

  std::size_t rotate_left(std::size_t index) {
    const std::size_t pivot = (*slots)[index].right;
    (*slots)[index].right = (*slots)[pivot].left;
    (*slots)[pivot].left = index;
    refresh(index);
    refresh(pivot);
    return pivot;
  }

  std::size_t rotate_right(std::size_t index) {
    const std::size_t pivot = (*slots)[index].left;
    (*slots)[index].left = (*slots)[pivot].right;
    (*slots)[pivot].right = index;
    refresh(index);
    refresh(pivot);
    return pivot;
  }

  std::size_t rebalance(std::size_t index) {
    const std::size_t left = (*slots)[index].left;
    const std::size_t right = (*slots)[index].right;
    const std::size_t a = subtree_height(left);
    const std::size_t b = subtree_height(right);
    if (b + 1 < a) {
      const std::size_t outer = subtree_height((*slots)[left].left);
      const std::size_t inner = subtree_height((*slots)[left].right);
      if (outer < inner) (*slots)[index].left = rotate_left(left);
      return rotate_right(index);
    }
    if (a + 1 < b) {
      const std::size_t outer = subtree_height((*slots)[right].right);
      const std::size_t inner = subtree_height((*slots)[right].left);
      if (outer < inner) (*slots)[index].right = rotate_right(right);
      return rotate_left(index);
    }
    refresh(index);
    return index;
  }

  std::size_t insert(std::size_t index, T key) {
    if (index == none) return allocate(key);
    if (key < (*slots)[index].key.value()) {
      (*slots)[index].left = insert((*slots)[index].left, key);
    } else if ((*slots)[index].key.value() < key) {
      (*slots)[index].right = insert((*slots)[index].right, key);
    } else {
      return index;
    }
    return rebalance(index);
  }

  // Detach the minimum by index so deleting a key never assigns a stored T.
  std::pair<std::size_t, std::size_t> detach_first(std::size_t index) {
    const std::size_t left = (*slots)[index].left;
    if (left == none) return {index, (*slots)[index].right};
    auto [first, replacement] = detach_first(left);
    (*slots)[index].left = replacement;
    const std::size_t top = rebalance(index);
    return {first, top};
  }

  std::size_t erase(std::size_t index, T key) {
    if (index == none) return none;
    if (key < (*slots)[index].key.value()) {
      (*slots)[index].left = erase((*slots)[index].left, key);
      return rebalance(index);
    }
    if ((*slots)[index].key.value() < key) {
      (*slots)[index].right = erase((*slots)[index].right, key);
      return rebalance(index);
    }
    const std::size_t left = (*slots)[index].left;
    const std::size_t right = (*slots)[index].right;
    release(index);
    if (left == none) return right;
    if (right == none) return left;
    auto [first, replacement] = detach_first(right);
    (*slots)[first].left = left;
    (*slots)[first].right = replacement;
    return rebalance(first);
  }

  void copy_contents(const TreeSet &other) {
    root = other.root;
    free_head = other.free_head;
    for (std::size_t i = 0; i < (other.slots.get() == nullptr ? 0 : (*other.slots).size()); ++i) {
      if (slots.get() == nullptr) slots = std::make_unique<std::deque<Slot>>();
      (*slots).emplace_back();
      if ((*other.slots)[i].key.has_value()) (*slots)[i].key.emplace((*other.slots)[i].key.value());
      (*slots)[i].left = (*other.slots)[i].left;
      (*slots)[i].right = (*other.slots)[i].right;
      (*slots)[i].height = (*other.slots)[i].height;
      (*slots)[i].size = (*other.slots)[i].size;
      (*slots)[i].first = (*other.slots)[i].first;
      (*slots)[i].last = (*other.slots)[i].last;
    }
  }


  void swap_contents(TreeSet &other) {
    slots.swap(other.slots);
    const std::size_t old_root = root;
    const std::size_t old_free = free_head;
    root = other.root;
    free_head = other.free_head;
    other.root = old_root;
    other.free_head = old_free;
  }

public:
  TreeSet() noexcept : slots(), root(none), free_head(none) {}

  TreeSet(const TreeSet &other) : slots(), root(none), free_head(none) {
    copy_contents(other);
  }

  TreeSet(TreeSet &&other) noexcept : slots(), root(other.root), free_head(other.free_head) {
    slots.swap(other.slots);
    other.root = none;
    other.free_head = none;
  }

  TreeSet &operator=(const TreeSet &other) {
    TreeSet copy{};
    copy.copy_contents(other);
    swap_contents(copy);
    return *this;
  }

  TreeSet &operator=(TreeSet &&other) noexcept {
    slots.swap(other.slots);
    const std::size_t old_root = root;
    const std::size_t old_free = free_head;
    root = other.root;
    free_head = other.free_head;
    other.root = old_root;
    other.free_head = old_free;
    return *this;
  }

  void add(T key) { root = insert(root, key); }
  void remove(T key) { root = erase(root, key); }

  bool find(T key) {
    std::size_t index = root;
    while (index != none) {
      if (key < (*slots)[index].key.value()) index = (*slots)[index].left;
      else if ((*slots)[index].key.value() < key) index = (*slots)[index].right;
      else return true;
    }
    return false;
  }

  T min() {
    assert(root != none);
    const std::size_t index = (*slots)[root].first;
    return (*slots)[index].key.value();
  }

  T max() {
    assert(root != none);
    const std::size_t index = (*slots)[root].last;
    return (*slots)[index].key.value();
  }

  int size() { return static_cast<int>(subtree_size(root)); }

  std::pair<int, int> rank(T key) const {
    std::size_t index = root;
    std::size_t before = 0;
    while (index != none) {
      if (key < (*slots)[index].key.value()) {
        index = (*slots)[index].left;
      } else if ((*slots)[index].key.value() < key) {
        before += 1 + subtree_size((*slots)[index].left);
        index = (*slots)[index].right;
      } else {
        const std::size_t first = before + subtree_size((*slots)[index].left);
        return {static_cast<int>(first), static_cast<int>(first + 1)};
      }
    }
    return {-1, -1};
  }

  T get_kth(std::size_t position) const {
    assert(position < subtree_size(root));
    std::size_t index = root;
    for (;;) {
      const std::size_t left_size = subtree_size((*slots)[index].left);
      if (position < left_size) {
        index = (*slots)[index].left;
      } else if (position == left_size) {
        return (*slots)[index].key.value();
      } else {
        position -= left_size + 1;
        index = (*slots)[index].right;
      }
    }
  }

  std::optional<T> find_lower(T key) const {
    std::size_t index = root;
    std::size_t candidate = none;
    while (index != none) {
      if (key < (*slots)[index].key.value()) {
        index = (*slots)[index].left;
      } else {
        candidate = index;
        index = (*slots)[index].right;
      }
    }
    if (candidate == none) return std::optional<T>();
    return std::optional<T>((*slots)[candidate].key.value());
  }

  std::optional<T> find_upper(T key) const {
    std::size_t index = root;
    std::size_t candidate = none;
    while (index != none) {
      if ((*slots)[index].key.value() < key) {
        index = (*slots)[index].right;
      } else {
        candidate = index;
        index = (*slots)[index].left;
      }
    }
    if (candidate == none) return std::optional<T>();
    return std::optional<T>((*slots)[candidate].key.value());
  }
};

template <class T> const std::size_t TreeSet<T>::none = ~std::size_t(0);

} // namespace cp

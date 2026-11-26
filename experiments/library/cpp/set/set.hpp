#pragma once
#include <set>
#include "template/small_template.hpp"

template <class T = ll> class TreeSet {
  struct Entry {
    mutable T key;

    explicit Entry(T &value) : key(value) {}
    Entry(const Entry &other) : key(other.key) {}

    friend bool operator<(const Entry &a, const Entry &b) {
      return a.key < b.key;
    }
  };

  std::set<Entry> values;

public:
  TreeSet() noexcept : values() {}

  void add(T key) { values.emplace(key); }
  void remove(T key) { values.erase(Entry(key)); }
  bool find(T key) { return values.count(Entry(key)) != 0; }
  T min() { return values.begin()->key; }
  T max() { return values.rbegin()->key; }
  int size() { return (int)values.size(); }
};

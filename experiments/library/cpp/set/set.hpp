#pragma once
#include "random/xorshift.hpp"
#include "template/small_template.hpp"

/**
 * @brief 重複なしの集合
 * 挿入 O(log n)
 * 削除 O(log n)
 * 検索 O(log n)
 * 実装：Treap https://xuzijian629.hatenablog.com/entry/2018/12/08/000452
 * @tparam T 要素の型
 */
template <typename T = ll> class TreeSet {
  static inline Xor64 rnd = Xor64(192865741288375612ull);
  struct Node {
    T k;
    ull p = rnd.get();
    Node *l = nullptr, *r = nullptr;
    Node(T key) : k(key) {}
  };
  using Tree = Node *;
  Tree root = nullptr;
  int n = 0;

  void split(Tree t, T key, Tree &l, Tree &r) {
    if (!t) {
      l = r = nullptr;
    } else if (key < t->k) {
      split(t->l, key, l, t->l);
      r = t;
    } else {
      split(t->r, key, t->r, r);
      l = t;
    }
  }

  void merge(Tree &t, Tree l, Tree r) {
    if (!l || !r) {
      t = l ? l : r;
    } else if (l->p > r->p) {
      merge(l->r, l->r, r);
      t = l;
    } else {
      merge(r->l, l, r->l);
      t = r;
    }
  }

  void insert(Tree &t, Tree item) {
    if (!t) {
      t = item;
    } else if (item->p > t->p) {
      split(t, item->k, item->l, item->r);
      t = item;
    } else {
      insert(item->k < t->k ? t->l : t->r, item);
    }
  }

  void remove(Tree &t, T key) {
    if (t->k == key) {
      merge(t, t->l, t->r);
    } else {
      remove(key < t->k ? t->l : t->r, key);
    }
  }

  bool find(Tree &t, T key) {
    if (!t) {
      return false;
    } else if (t->k == key) {
      return true;
    } else {
      return find(key < t->k ? t->l : t->r, key);
    }
  }

public:
  TreeSet() = default;
  void add(T key) {
    n++;
    insert(root, new Node(key));
  }
  void remove(T key) {
    n--;
    remove(root, key);
  }
  bool find(T key) { return find(root, key); }
  T min() {
    Tree t = root;
    while (t->l) {
      t = t->l;
    }
    return t->k;
  }
  T max() {
    Tree t = root;
    while (t->r) {
      t = t->r;
    }
    return t->k;
  }

  int size() { return n; }
};

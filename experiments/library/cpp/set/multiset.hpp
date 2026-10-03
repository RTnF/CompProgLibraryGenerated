#pragma once
#include "template/small_template.hpp"

namespace in {
// https://ja.wikipedia.org/wiki/Xorshift
class Xor64 {
  ull s;

public:
  Xor64(ull s_) : s(s_) {}
  // [0, 2**64)
  ull get() {
    ull x = s;
    x ^= x << 7;
    return s = x ^ (x >> 9);
  }
};
static inline Xor64 rnd = Xor64(192865741288175612ull);
template <class T = ll> struct Node {
  T k;
  ull p = rnd.get();
  size_t c = 1;  // 個数
  size_t cr = 1; // 部分木を合わせた個数
  Node *l, *r;
  static int node_count;
  static Node *const nil;
  Node(T key, size_t c_ = 1) : k(key), c(c_), cr(c_), l(nil), r(nil) {}
  // nil用
  Node(T key, ull p_, size_t c_)
      : k(key), p(p_), c(c_), cr(c_), l(nullptr), r(nullptr) {}
  friend ostream &operator<<(ostream &os, const Node &t) {
    os << "[" << &t << "](k=" << t.k << ", p=" << t.p << ", c=" << t.c
       << ", cr=" << t.cr << ", l=" << t.l << ", r=" << t.r << ")";
    return os;
  }
};
template <class T> Node<T> *const Node<T>::nil = new Node<T>({}, 0, 0);
} // namespace in

/**
 * @brief 重複ありの集合
 * 挿入 O(log n)
 * 削除 O(log n)
 * 検索 O(log n)
 * 実装：Treap https://xuzijian629.hatenablog.com/entry/2018/12/08/000452
 * @tparam T 要素の型
 */
template <class T = ll> class TreeMultiSet {
  using Tree = in::Node<T> *;
  const Tree nil = in::Node<T>::nil;
  Tree root = in::Node<T>::nil;
  size_t n_ = 0;

  void update_cr(Tree t) {
    if (t != nil) {
      t->cr = t->c;
      t->cr += t->l->cr;
      t->cr += t->r->cr;
    }
  }

  void split(Tree t, T key, Tree &l, Tree &r) {
    if (t == nil) {
      l = r = nil;
    } else if (key < t->k) {
      split(t->l, key, l, t->l);
      r = t;
    } else {
      split(t->r, key, t->r, r);
      l = t;
    }
    update_cr(t);
  }

  void merge(Tree &t, Tree l, Tree r) {
    if (l == nil) {
      t = r;
    } else if (r == nil) {
      t = l;
    } else if (l->p > r->p) {
      merge(l->r, l->r, r);
      t = l;
    } else {
      merge(r->l, l, r->l);
      t = r;
    }
    update_cr(t);
  }

  void insert(Tree &t, Tree item) {
    if (t == nil) {
      t = item;
    } else if (item->p > t->p) {
      split(t, item->k, item->l, item->r);
      t = item;
    } else {
      insert(item->k < t->k ? t->l : t->r, item);
    }
    update_cr(t);
  }

  void remove(Tree &t, T key) {
    if (t->k == key) {
      merge(t, t->l, t->r);
    } else {
      remove(key < t->k ? t->l : t->r, key);
    }
    update_cr(t);
  }

  // AOJ
  void aoj_dump(Tree &t, T l, T r) {
    if (t->l != nil && t->k > l) {
      aoj_dump(t->l, l, r);
    }
    if (l <= t->k && t->k <= r) {
      for (size_t i = 0; i < t->c; i++) {
        cout << t->k << '\n';
      }
    }
    if (t->r != nil && t->k < r) {
      aoj_dump(t->r, l, r);
    }
  }

  void print(Tree t) {
    if (t != nil) {
      cout << (*t) << "\n";
      if (t->l) {
        print(t->l);
      }
      if (t->r) {
        print(t->r);
      }
    }
  }

  // 検証
  void verify(Tree t, size_t &n_v) {
    if (t != nil) {
      n_v += t->c;
      size_t cr = t->c;
      if (t->l) {
        cr += t->l->cr;
      }
      if (t->r) {
        cr += t->r->cr;
      }
      if (cr != t->cr) {
        print(root);
        cout.flush();
        assert(false);
      }
      if (t->l) {
        verify(t->l, n_v);
      }
      if (t->r) {
        verify(t->r, n_v);
      }
    }
  }

  T find_by_order(Tree t, size_t k) {
    assert(t != nil);
    size_t sz_l = t->l ? t->l->cr : 0;
    if (k < sz_l) {
      return find_by_order(t->l, k);
    } else if (k < sz_l + t->c) {
      return t->k;
    } else {
      return find_by_order(t->r, k - sz_l - t->c);
    }
  }

  void enumerate_in(vector<tuple<T, size_t, T>> &v, Tree t, const T &l,
                    const T &r, Tree parent) {
    if (t->l != nil && l < t->k) {
      enumerate_in(v, t->l, l, r, t);
    }
    if (l <= t->k && t->k < r) {
      v.emplace_back(t->k, t->c, parent ? parent->k : -1);
    }
    if (t->r != nil && t->k < r - 1) {
      enumerate_in(v, t->r, l, r, t);
    }
  }

  void enumerate_all_in(vector<tuple<T, size_t, T>> &v, Tree t, Tree parent) {
    if (t->l != nil) {
      enumerate_all_in(v, t->l, t);
    }
    v.emplace_back(t->k, t->c, parent ? parent->k : -1);
    if (t->r != nil) {
      enumerate_all_in(v, t->r, t);
    }
  }

public:
  TreeMultiSet() = default;

  /**
   * @brief 要素のn個追加
   *
   * @param key
   * @return size_t 追加後の同じ要素の数
   */
  size_t add(T key, size_t n = 1) {
    n_ += n;
    Tree t = root;
    bool found = false;
    while (t != nil) {
      if (key == t->k) {
        found = true;
        break;
      }
      t = key < t->k ? t->l : t->r;
    }
    if (found) {
      t = root;
      while (t != nil) {
        t->cr += n;
        if (key == t->k) {
          t->c += n;
          return t->c;
        }
        t = key < t->k ? t->l : t->r;
      }
    } else {
      in::Node<T> *node = new in::Node<T>(key, n);
      insert(root, node);
    }
    return n;
  }

  /**
   * @brief 指定した要素のn個削除
   * 要素がn個を下回る場合は何もしない
   *
   * @param key
   * @return bool 削除出来た場合true
   */
  bool remove(T key, size_t n = 1) {
    Tree t = root;
    bool found = false;
    while (t != nil) {
      if (key == t->k) {
        if (t->c == n) {
          n_ -= n;
          remove(root, key);
        } else if (t->c > n) {
          n_ -= n;
          t->c -= n;
          found = true;
          break;
        } else {
          return false;
        }
        return false;
      }
      t = key < t->k ? t->l : t->r;
    }
    if (found) {
      t = root;
      while (t != nil) {
        t->cr -= n;
        if (key == t->k) {
          return true;
        }
        t = key < t->k ? t->l : t->r;
      }
    }
    return false;
  }

  /**
   * @brief 指定した要素の全削除
   *
   * @param key
   * @return size_t 削除した要素数
   */
  size_t remove_all(T key) {
    Tree t = root;
    while (t != nil) {
      if (key == t->k) {
        size_t ret = t->c;
        n_ -= ret;
        remove(root, key);
        return ret;
      }
      t = key < t->k ? t->l : t->r;
    }
    return 0;
  }

  // 検索 個数を返す O(log n)
  size_t count(T key) {
    Tree t = root;
    while (t != nil) {
      if (key == t->k) {
        return t->c;
      }
      t = key < t->k ? t->l : t->r;
    }
    return 0;
  }

  // 検索 ない場合、検索値より小さい中で最大の要素または無効値
  optional<T> find_lower(T key) {
    Tree t = root;
    Tree lower = nil;

    while (t != nil) {
      if (key == t->k) {
        return key;
      } else if (key < t->k) {
        t = t->l;
      } else {
        lower = t;
        t = t->r;
      }
    }
    return lower != nil ? optional(lower->k) : nullopt;
  }

  // 検索 ない場合、検索値より大きい中で最小の要素または無効値
  optional<T> find_upper(T key) {
    Tree t = root;
    Tree upper = nil;
    while (t != nil) {
      if (key == t->k) {
        return key;
      } else if (key < t->k) {
        upper = t;
        t = t->l;
      } else {
        t = t->r;
      }
    }
    return upper != nil ? optional(upper->k) : nullopt;
  }

  // 検索 順位(0-indexed)の区間を返す O(log n)
  // 存在しない場合、-1,-1
  pair<int, int> rank(T key) {
    Tree t = root;
    int rnk = 0;
    while (t != nil) {
      if (key == t->k) {
        rnk += t->l ? t->l->cr : 0;
        return {rnk, rnk + t->c};
      } else if (key < t->k) {
        t = t->l;
      } else {
        rnk += t->c;
        rnk += t->l ? t->l->cr : 0;
        t = t->r;
      }
    }
    return {-1, -1};
  }

  T min() {
    Tree t = root;
    assert(root);
    while (t->l != nil) {
      t = t->l;
    }
    return t->k;
  }

  T max() {
    Tree t = root;
    assert(root);
    while (t->r != nil) {
      t = t->r;
    }
    return t->k;
  }

  // K番目の要素(0-indexed)
  T get_kth(size_t k) {
    assert(k < n_);
    return find_by_order(root, k);
  }

  // l <= k < r を満たす要素の列挙
  vector<tuple<T, size_t, T>> enumerate(const T &l, const T &r) {
    vector<tuple<T, size_t, T>> ret;
    if (root != nil) {
      enumerate_in(ret, root, l, r);
    }
    return ret;
  }

  // 全要素の列挙
  vector<tuple<T, size_t, T>> enumerate_all() {
    vector<tuple<T, size_t, T>> ret;
    if (root != nil) {
      enumerate_all_in(ret, root, nullptr);
    }
    return ret;
  }

  // AOJ
  void aoj_dump(const T &l, const T &r) {
    if (root != nil) {
      aoj_dump(root, l, r);
    }
  }

  size_t size() { return n_; }

  void verify() {
    if (root != nil) {
      // 総数がn_に一致
      size_t n_v = 0;
      verify(root, n_v);
      assert(n_ == n_v);
    }
  }
};
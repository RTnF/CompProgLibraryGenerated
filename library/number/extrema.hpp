#pragma once
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// Raises `a` to `b` when `a < b` and reports whether `a` changed. `a` and `b` may refer to the same object.
// Derived from experiments/library/cpp/template/template.cpp: the function templates keep their type parameters S and T
// (the verified instance is S = T = long long, instantiated explicitly below). The `return` inside the `if` is written
// as a local `changed` and one final `return`.
template <class S, class T> bool chmax(S &a, const T &b) {
  bool changed = false;
  if (a < b) {
    a = b;
    changed = true;
  }
  return changed;
}

// Lowers `a` to `b` when `b < a` and reports whether `a` changed. `a` and `b` may refer to the same object.
template <class S, class T> bool chmin(S &a, const T &b) {
  bool changed = false;
  if (b < a) {
    a = b;
    changed = true;
  }
  return changed;
}

template bool chmax<long long, long long>(long long &, const long long &);
template bool chmin<long long, long long>(long long &, const long long &);

} // namespace cp

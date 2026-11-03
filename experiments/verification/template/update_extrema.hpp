#pragma once

namespace cp {

// Preserved bodies of the two imported templates' chmax/chmin helpers.
// The supported type instances and remaining generic proof are documented.
template <class S, class T> constexpr bool chmax(S &a, const T &b) {
  if (a < b) {
    a = b;
    return 1;
  }
  return 0;
}
template <class S, class T> constexpr bool chmin(S &a, const T &b) {
  if (b < a) {
    a = b;
    return 1;
  }
  return 0;
}

} // namespace cp

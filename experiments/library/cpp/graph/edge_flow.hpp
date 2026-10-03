#pragma once
#include "template/small_template.hpp"

// 辺
template <class T> class FlowEdge {
  static int next_id;

public:
  int from, to, rev, id;
  T cap, cost;
  FlowEdge(int from_, int to_, int rev_, T cap_, T cost_)
      : from(from_), to(to_), rev(rev_), id(next_id++), cap(max(cap_, (T)0)),
        cost(cost_) {}
  FlowEdge(int from_, int to_, int rev_, T cap_)
      : from(from_), to(to_), rev(rev_), id(next_id++), cap(max(cap_, (T)0)),
        cost(0) {}
  FlowEdge(int from_, int to_, int rev_)
      : from(from_), to(to_), rev(rev_), id(next_id++), cap(0), cost(0) {}
};

template <class T> int FlowEdge<T>::next_id = 0;

template <class T> ostream &operator<<(ostream &os, const FlowEdge<T> &e) {
  os << e.id << ": " << e.from << " -> " << e.to << " (" << e.cap << ", "
     << e.cost << ")";
  return os;
}
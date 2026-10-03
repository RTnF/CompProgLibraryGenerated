#pragma once
#include "template/small_template.hpp"

// 辺
template <class T> class Edge {
  static int next_id;

public:
  int from, to, id;
  T cost;
  Edge(int from_, int to_, T cost_)
      : from(from_), to(to_), id(next_id++), cost(cost_) {}
  Edge(int from_, int to_) : from(from_), to(to_), id(next_id++), cost(1) {}
};

template <class T> int Edge<T>::next_id = 0;

template <class T> ostream &operator<<(ostream &os, const Edge<T> &edge) {
  os << edge.id << ": " << edge.from << " -> " << edge.to << " (" << edge.cost
     << ")";
  return os;
}
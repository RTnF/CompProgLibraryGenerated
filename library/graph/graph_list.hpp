#pragma once
#include <algorithm>
#include <limits>
#include <ostream>
#include <unordered_map>
#include <utility>
#include <vector>

#include "edge.hpp"

namespace cp {

// グラフ(隣接リスト) (experiments/library/cpp/graph/graph_list.hpp)
// The algorithms (dijkstra, bellman_ford, prim, lowlink, find_cycle_directed, topological_sort,
// topological_sort_minimum) are members of this class; in the original they are declared here and defined in
// their own headers. Each is added here, with its body, when its header is ported (docs/graph_list.md).
template <class Cost = long long, class E = Edge<Cost>> class ListGraph {
  int n_, m_;
  std::vector<std::vector<E>> adj;
  std::unordered_map<int, std::vector<Cost>> shortest_path_dist;
  std::unordered_map<int, std::vector<int>> shortest_path_parent;

public:
  static const Cost UNREACHABLE;
  static const Cost NEGATIVE_CYCLE;
  ListGraph() : n_(0), m_(0), adj(0) {}
  ListGraph(int n) : n_(n), m_(0), adj(n) {}

  std::vector<E> &operator[](int i) { return adj[i]; }

  void add_node() {
    adj.emplace_back();
    n_++;
    reset_shortest();
  }
  template <class... Args> void add_edge(int from, int to, Args... args) {
    adj[from].emplace_back(from, to, args...);
    m_++;
    reset_shortest();
  }
  template <class... Args>
  void add_bidirectional_edge(int from, int to, Args... args) {
    adj[from].emplace_back(from, to, args...);
    adj[to].emplace_back(to, from, args...);
    m_ += 2;
    reset_shortest();
  }
  void reset_shortest() {
    shortest_path_dist.clear();
    shortest_path_parent.clear();
  }
  Cost distance(int from, int to) { return shortest_path_dist[from][to]; }
  std::vector<Cost> distance(int from) { return shortest_path_dist[from]; }
  std::vector<int> shortest_path(int from, int to) {
    std::vector<int> path;
    for (int cur = to; cur != -1; cur = shortest_path_parent[from][cur]) {
      path.emplace_back(cur);
    }
    std::reverse(path.begin(), path.end());
    return path;
  }

  template <class C_, class E_>
  friend std::ostream &operator<<(std::ostream &, const ListGraph<C_, E_> &);
};

template <class Cost, class E>
const Cost ListGraph<Cost, E>::UNREACHABLE = std::numeric_limits<Cost>::max() >> 2;
template <class Cost, class E>
const Cost ListGraph<Cost, E>::NEGATIVE_CYCLE = std::numeric_limits<Cost>::min() >> 2;

template <class C_, class E_>
std::ostream &operator<<(std::ostream &os, const ListGraph<C_, E_> &graph) {
  os << "N = " << graph.n_ << ", M = " << graph.m_ << '\n';
  for (const auto &ev : graph.adj) {
    for (const auto &e : ev) {
      os << e << '\n';
    }
  }
  return os;
}

} // namespace cp

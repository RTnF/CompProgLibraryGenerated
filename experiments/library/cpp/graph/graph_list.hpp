#pragma once
#include "graph/edge.hpp"

// グラフ(隣接リスト)
template <class Cost = ll, class E = Edge<Cost>> class ListGraph {
  int n_, m_;
  vector<vector<E>> adj;
  unordered_map<int, vector<Cost>> shortest_path_dist;
  unordered_map<int, vector<int>> shortest_path_parent;

public:
  static const Cost UNREACHABLE;
  static const Cost NEGATIVE_CYCLE;
  // 頂点数 0
  ListGraph() : n_(0), m_(0), adj(0) {}
  // 頂点数 n
  ListGraph(int n) : n_(n), m_(0), adj(n) {}

  vector<E> &operator[](int i) { return adj[i]; }

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
  // 双方向
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

  // 最短距離
  void dijkstra(int start_node);
  void bellman_ford(int start_node);
  Cost distance(int from, int to) { return shortest_path_dist[from][to]; }
  vector<Cost> distance(int from) { return shortest_path_dist[from]; }
  vector<int> shortest_path(int from, int to) {
    vector<int> path;
    for (int cur = to; cur != -1; cur = shortest_path_parent[from][cur]) {
      path.emplace_back(cur);
    }
    reverse(path.begin(), path.end());
    return path;
  }

  // 最小全域森
  Cost prim();

  // 関節点・橋
  pair<vector<int>, vector<pair<int, int>>> lowlink();

  // トポロジカルソート
  vector<E> find_cycle_directed();
  vector<int> topological_sort();
  vector<int> topological_sort_minimum();

  template <class C_, class E_>
  friend ostream &operator<<(ostream &, const ListGraph<C_, E_> &);
};

template <class Cost, class E>
const Cost ListGraph<Cost, E>::UNREACHABLE = numeric_limits<Cost>::max() >> 2;
template <class Cost, class E>
const Cost ListGraph<Cost, E>::NEGATIVE_CYCLE =
    numeric_limits<Cost>::min() >> 2;

template <class C_, class E_>
ostream &operator<<(ostream &os, const ListGraph<C_, E_> &graph) {
  os << "N = " << graph.n_ << ", M = " << graph.m_ << '\n';
  for (const auto &ev : graph.adj) {
    for (const auto &e : ev) {
      os << e << '\n';
    }
  }
  return os;
}
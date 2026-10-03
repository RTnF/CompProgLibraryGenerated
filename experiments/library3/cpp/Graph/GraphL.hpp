#pragma once
#include "Template/SmallTemplate.hpp"

// 辺
template<class T>
class Edge {
  static int nextId;

public:
  const int from, to, id;
  const T cost;
  Edge(int from_, int to_, T cost_): from(from_), to(to_), id(nextId++), cost(cost_) {}
  Edge(int from_, int to_): from(from_), to(to_), id(nextId++), cost(1) {}
};

template<class T>
int Edge<T>::nextId = 0;

template<class T>
ostream &operator<<(ostream &os, const Edge<T> &edge) {
  os << edge.id << ": " << edge.from << " -> " << edge.to << " (" << edge.cost << ")";
  return os;
}

// グラフ(隣接リスト)
template<class Cost = ll, class E = Edge<Cost>>
class GraphL {
  int n, m;
  vector<vector<E>> adj;
  unordered_map<int, vector<Cost>> shortest_path_dist;
  unordered_map<int, vector<int>> shortest_path_parent;

public:
  static const Cost UNREACHABLE = numeric_limits<Cost>::max();
  static const Cost NEGATIVE_CYCLE = numeric_limits<Cost>::min();
  GraphL() {}
  GraphL(int n_): n(n_), m(0), adj(n_) {}

  void addNode() {
    adj.emplace_back();
    n++;
    resetShortest();
  }
  template<class... Args>
  void addEdge(int from, int to, Args... args) {
    adj[from].emplace_back(from, to, args...);
    m++;
    resetShortest();
  }
  // 双方向
  template<class... Args>
  void addBidirectionalEdge(int from, int to, Args... args) {
    adj[from].emplace_back(from, to, args...);
    adj[to].emplace_back(to, from, args...);
    m += 2;
    resetShortest();
  }
  void resetShortest() {
    shortest_path_dist.clear();
    shortest_path_parent.clear();
  }
  vector<E> &operator[](int i) { return adj[i]; }

  // 最短距離
  void dijkstra(int start_node);
  void bellmanFord(int start_node);
  Cost getDist(int from, int to) { return shortest_path_dist[from][to]; }
  vector<int> getShortestPath(int from, int to) {
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
  vector<int> topologicalSort();
  vector<int> topologicalSortMinimum();

  template<class C_, class E_>
  friend ostream &operator<<(ostream &, const GraphL<C_, E_> &);
};

template<class C_, class E_>
ostream &operator<<(ostream &os, const GraphL<C_, E_> &graph) {
  os << "N = " << graph.n << ", M = " << graph.m << '\n';
  for (const auto &ev: graph.adj) {
    for (const auto &e: ev) {
      os << e << '\n';
    }
  }
  return os;
}
#pragma once
#include "template/small_template.hpp"

// グラフ(隣接行列)
template <class Cost = ll> class MatrixGraph {
  int n, m;
  vector<vector<Cost>> mat;
  vector<vector<Cost>> shortest_path_dist;
  vector<vector<int>> shortest_path_parent;
  bool negative_cycle = false;

public:
  static const Cost UNREACHABLE;

  MatrixGraph(int n_)
      : n(n_), m(0), mat(n_, vector<Cost>(n_, MatrixGraph::UNREACHABLE)) {
    for (int i = 0; i < n; ++i) {
      mat[i][i] = 0;
    }
  }

  void add_edge(int from, int to, Cost cost = 1) {
    mat[from][to] = cost;
    m++;
  }

  // 最短距離
  void warshall_floyd();
  Cost distance(int from, int to) { return shortest_path_dist[from][to]; }
  vector<int> get_shortest_path(int from, int to) {
    vector<int> path;
    for (int cur = to; cur != from; cur = shortest_path_parent[from][cur]) {
      path.emplace_back(cur);
      if (cur == -1) {
        return vector<int>();
      }
    }
    path.emplace_back(from);
    reverse(path.begin(), path.end());
    return path;
  }
  bool has_negative_cycle() const { return negative_cycle; }

  template <class T>
  friend std::ostream &operator<<(std::ostream &, const MatrixGraph<T> &);
};

template <class Cost>
const Cost MatrixGraph<Cost>::UNREACHABLE = numeric_limits<Cost>::max() >> 2;

template <class T>
ostream &operator<<(ostream &os, const MatrixGraph<T> &graph) {
  os << "N = " << graph.n << ", M = " << graph.m << '\n';
  for (int i = 0; i < graph.n; ++i) {
    for (int j = 0; j < graph.n; ++j) {
      os << graph.mat[i][j] << " \n"[j == graph.n - 1];
    }
  }
  return os;
}
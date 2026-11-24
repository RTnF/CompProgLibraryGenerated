#pragma once
#include <algorithm>
#include <limits>
#include <ostream>
#include <vector>

namespace cp {

// グラフ(隣接行列) (experiments/library/cpp/graph/graph_matrix.hpp and warshall_floyd.hpp in one class)
// Preconditions: 0 <= n_; vertices of add_edge/distance/get_shortest_path are in [0, n); distance and
// get_shortest_path are called after warshall_floyd; costs and every intermediate value of warshall_floyd fit in
// Cost (docs/graph_matrix.md). warshall_floyd: O(n^3) time; get_shortest_path: O(n) time without a negative cycle.
template <class Cost = long long> class MatrixGraph {
  int n, m;
  std::vector<std::vector<Cost>> mat;
  std::vector<std::vector<Cost>> shortest_path_dist;
  std::vector<std::vector<int>> shortest_path_parent;
  bool negative_cycle = false;

public:
  static const Cost UNREACHABLE;

  MatrixGraph(int n_)
      : n(n_), m(0), mat(n_, std::vector<Cost>(n_, MatrixGraph::UNREACHABLE)) {
    for (int i = 0; i < n; ++i) {
      mat[i][i] = 0;
    }
  }

  void add_edge(int from, int to, Cost cost = 1) {
    mat[from][to] = cost;
    m++;
  }

  // 最短距離
  void warshall_floyd() {
    if (shortest_path_dist.size()) {
      return;
    }
    shortest_path_dist = mat;
    shortest_path_parent = std::vector<std::vector<int>>(n, std::vector<int>(n, -1));
    for (int i = 0; i < n; ++i) {
      for (int j = 0; j < n; ++j) {
        if (mat[i][j] < MatrixGraph<Cost>::UNREACHABLE || i == j) {
          shortest_path_parent[i][j] = i;
        }
      }
    }
    for (int k = 0; k < n; ++k) {
      for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
          if (shortest_path_dist[i][k] + shortest_path_dist[k][j] <
              shortest_path_dist[i][j]) {
            shortest_path_dist[i][j] =
                shortest_path_dist[i][k] + shortest_path_dist[k][j];
            shortest_path_parent[i][j] = shortest_path_parent[k][j];
          }
        }
      }
    }
    for (int i = 0; i < n; ++i) {
      for (int j = 0; j < n; ++j) {
        if (shortest_path_dist[i][j] > MatrixGraph<Cost>::UNREACHABLE / 2) {
          shortest_path_dist[i][j] = MatrixGraph<Cost>::UNREACHABLE;
        }
      }
    }
    for (int i = 0; i < n; ++i) {
      if (shortest_path_dist[i][i] < 0) {
        negative_cycle = true;
        break;
      }
    }
  }
  Cost distance(int from, int to) { return shortest_path_dist[from][to]; }
  std::vector<int> get_shortest_path(int from, int to) {
    std::vector<int> path;
    for (int cur = to; cur != from; cur = shortest_path_parent[from][cur]) {
      path.emplace_back(cur);
      if (cur == -1) {
        return std::vector<int>();
      }
    }
    path.emplace_back(from);
    std::reverse(path.begin(), path.end());
    return path;
  }
  bool has_negative_cycle() const { return negative_cycle; }

  friend std::ostream &operator<<(std::ostream &os, const MatrixGraph &graph) {
    os << "N = " << graph.n << ", M = " << graph.m << '\n';
    for (int i = 0; i < graph.n; ++i) {
      for (int j = 0; j < graph.n; ++j) {
        os << graph.mat[i][j] << (j == graph.n - 1 ? '\n' : ' ');
      }
    }
    return os;
  }
};

template <class Cost>
const Cost MatrixGraph<Cost>::UNREACHABLE = std::numeric_limits<Cost>::max() >> 2;


} // namespace cp

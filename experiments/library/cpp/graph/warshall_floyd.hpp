#pragma once
#include "graph/graph_matrix.hpp"
#include "template/small_template.hpp"

/**
 * ワーシャルフロイド法
 * 有向グラフの全点対最短経路 O(V^3)
 * 到達不能：max
 * https://algo-logic.info/warshall-floyd/
 */
template <class Cost> void MatrixGraph<Cost>::warshall_floyd() {
  if (shortest_path_dist.size()) {
    return;
  }
  shortest_path_dist = mat;
  shortest_path_parent = vector<vector<int>>(n, vector<int>(n, -1));
  for (int i = 0; i < n; ++i) {
    shortest_path_parent[i][i] = i;
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

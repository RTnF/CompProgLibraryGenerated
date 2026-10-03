#pragma once
#include "graph/graph_list.hpp"
#include "template/small_template.hpp"

/**
 * ベルマンフォード法
 * 有向グラフの単一始点最短経路 O(EV)
 * 到達不能：max, 負閉路を通る：min
 * https://mhrb-minase.hatenablog.com/entry/2019/08/20/003915
 */
template <class Cost, class E>
void ListGraph<Cost, E>::bellman_ford(int start_node) {
  if (shortest_path_dist.count(start_node)) {
    return;
  }
  vector<Cost> dist(n_, ListGraph::UNREACHABLE);
  vector<int> parent(n_, -1);
  dist[start_node] = 0;
  for (int i = 0; i < n_ - 1; ++i) {
    for (auto &es : adj) {
      for (auto &e : es) {
        if (dist[e.from] != ListGraph::UNREACHABLE &&
            dist[e.from] + e.cost < dist[e.to]) {
          dist[e.to] = dist[e.from] + e.cost;
          parent[e.to] = e.from;
        }
      }
    }
  }
  for (int i = 0; i < n_; ++i) {
    for (auto &es : adj) {
      for (auto &e : es) {
        if (dist[e.from] != ListGraph::UNREACHABLE &&
            dist[e.from] + e.cost < dist[e.to]) {
          dist[e.to] = ListGraph::NEGATIVE_CYCLE;
          parent[e.to] = -1;
        }
      }
    }
  }
  shortest_path_dist[start_node] = std::move(dist);
  shortest_path_parent[start_node] = std::move(parent);
}
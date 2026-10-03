#pragma once
#include "graph/graph_list.hpp"
#include "template/small_template.hpp"

/**
 * プリム法
 * 無向グラフの最小全域森 O((E+V)logV)
 * 辺のコストが全て0以上
 * 返り値：コストの総和
 * https://algo-logic.info/prim-mst/
 */
template <class Cost, class E> Cost ListGraph<Cost, E>::prim() {
  Cost mst_dist = 0;
  using P = pair<Cost, int>;
  vector<Cost> dist(n_, ListGraph<Cost>::UNREACHABLE);
  vector<bool> used(n_, false);
  auto span = [&](int start_node) {
    dist[start_node] = 0;
    priority_queue<P, vector<P>, greater<P>> pq;
    pq.emplace(0, start_node);
    while (!pq.empty()) {
      P p = pq.top();
      pq.pop();
      Cost v = p.second;
      if (used[v] || dist[v] < p.first) {
        continue;
      }
      mst_dist += dist[v];
      used[v] = true;
      for (const auto &e : adj[v]) {
        if (!used[e.to] && e.cost < dist[e.to]) {
          dist[e.to] = e.cost;
          pq.emplace(dist[e.to], e.to);
        }
      }
    }
  };
  for (int i = 0; i < n_; ++i) {
    if (!used[i]) {
      span(i);
    }
  }
  return mst_dist;
}
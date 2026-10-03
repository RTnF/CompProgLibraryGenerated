#pragma once
#include "graph/graph_list.hpp"
#include "template/small_template.hpp"

/**
 * Lowlink 関節点・橋の列挙
 * 関節点 削除すると連結成分数が増加する頂点
 * 橋 削除すると連結成分数が増加する辺
 * 返り値：関節点, 橋(from, to)
 * O(V + E log E) (Lowlink + sort)
 * https://algo-logic.info/articulation-points/
 */
template <class Cost, class E>
pair<vector<int>, vector<pair<int, int>>> ListGraph<Cost, E>::lowlink() {
  using P = pair<int, int>;
  vector<bool> visited(n_, false);
  // ord: 頂点を探索した順番 low: DFS木にない辺を高々1回通って踏める最小のord
  vector<int> ord(n_, 0), low(n_, 0), articulation_points;
  vector<P> bridges;
  int visit_count = 0;

  auto dfs = [&](auto self, int v, int parent) -> void {
    visited[v] = true;
    low[v] = ord[v] = visit_count++;
    bool is_articular = false;
    int child_count = 0;
    for (auto &e : adj[v]) {
      if (!visited[e.to]) {
        child_count++;
        self(self, e.to, v);
        low[v] = min(low[v], low[e.to]);
        if (parent != -1 && ord[v] <= low[e.to]) {
          is_articular = true;
        }
        if (ord[v] < low[e.to]) {
          bridges.emplace_back(min(v, e.to), max(v, e.to));
        }
      } else if (e.to != parent) {
        low[v] = min(low[v], ord[e.to]);
      }
    }
    if (parent == -1 && child_count >= 2) {
      is_articular = true;
    }
    if (is_articular) {
      articulation_points.emplace_back(v);
    }
  };
  for (int i = 0; i < n_; ++i) {
    if (!visited[i]) {
      dfs(dfs, i, -1);
    }
  }
  sort(articulation_points.begin(), articulation_points.end());
  sort(bridges.begin(), bridges.end());
  return {articulation_points, bridges};
}
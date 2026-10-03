#pragma once
#include "graph/graph_list.hpp"

/**
 * サイクルを見つける
 */
template <class Cost, class E>
vector<E> ListGraph<Cost, E>::find_cycle_directed() {
  vector<char> visited(n_, 0);
  vector<E> in(n_, {-1, -1});
  vector<E> ret;
  auto dfs = [&](auto &Self, int node) -> void {
    visited[node] = 1;
    for (auto &&e : adj[node]) {
      if (ret.size()) {
        break;
      }
      if (!visited[e.to]) {
        in[e.to] = e;
        Self(Self, e.to);
      } else if (visited[e.to] == 1) {
        ret.emplace_back(e);
        for (int v = node; v != e.to; v = in[v].from) {
          ret.emplace_back(in[v]);
        }
        reverse(ret.begin(), ret.end());
        return;
      }
    }
    visited[node] = 2;
  };
  for (int i = 0; i < n_; i++) {
    if (!visited[i]) {
      dfs(dfs, i);
    }
  }
  return ret;
}
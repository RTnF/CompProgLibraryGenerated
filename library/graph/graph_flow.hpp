#pragma once
#include <algorithm>
#include <limits>
#include <ostream>
#include <queue>
#include <tuple>
#include <utility>
#include <vector>
#include "edge_flow.hpp"

namespace cp {

// グラフ(隣接リスト)
template <class Cost = long long, class E = FlowEdge<Cost>> class FlowGraph {
  int n_, m_;
  std::vector<std::vector<E>> adj;
  std::vector<int> level, iter;

  void bfs(int s) {
    level = std::vector<int>(n_, -1);
    level[s] = 0;
    std::queue<int> q;
    q.emplace(s);
    while (q.size()) {
      int v = q.front();
      q.pop();
      for (auto &&e : adj[v]) {
        if (e.cap > 0 && level[e.to] == -1) {
          level[e.to] = level[v] + 1;
          q.emplace(e.to);
        }
      }
    }
  }
  Cost dfs(int v, int t, Cost f) {
    if (v == t) {
      return f;
    }
    int sz_out = adj[v].size();
    for (int i = iter[v]; i < sz_out; i++) {
      if (!(adj[v][i].cap == 0 || level[v] >= level[adj[v][i].to])) {
        Cost d = dfs(adj[v][i].to, t, std::min(f, adj[v][i].cap));
        if (!(d == 0)) {
          adj[v][i].cap -= d;
          adj[adj[v][i].to][adj[v][i].rev].cap += d;
          return d;
        }
      }
      iter[v] = i + 1;
    }
    return 0;
  }
  std::tuple<std::vector<Cost>, std::vector<int>, std::vector<int>> bellman_ford(int s) {
    std::vector<Cost> dist(n_, F_MAX);
    std::vector<int> pv(n_, -1), pe(n_, 0);
    dist[s] = 0;
    pv[s] = s;
    while (true) {
      bool update = false;
      for (int v = 0; v < n_; v++) {
        if (pv[v] == -1) {
          continue;
        }
        for (int i = 0; i < (int)adj[v].size(); i++) {
          if (adj[v][i].cap > 0 &&
              (pv[adj[v][i].to] == -1 || dist[adj[v][i].to] > dist[v] + adj[v][i].cost)) {
            dist[adj[v][i].to] = dist[v] + adj[v][i].cost;
            update = true;
            pv[adj[v][i].to] = v;
            pe[adj[v][i].to] = i;
          }
        }
      }
      if (!update) {
        break;
      }
    }
    return {dist, pv, pe};
  }

public:
  static const Cost F_MAX;
  // 頂点数 0
  FlowGraph() : n_(0), m_(0), adj(0) {}
  // 頂点数 n
  FlowGraph(int n) : n_(n), m_(0), adj(n) {}

  std::vector<E> &operator[](int i) { return adj[i]; }

  void add_node() {
    n_++;
    adj.emplace_back();
    level.emplace_back();
  }
  void add_edge_max_flow(int from, int to, Cost cap) {
    int rev = (int)adj[to].size() + (from == to ? 1 : 0);
    adj[from].emplace_back(from, to, rev, cap);
    adj[to].emplace_back(to, from, (int)adj[from].size() - 1, 0);
    m_++;
  }
  void add_edge_min_cost_flow(int from, int to, Cost cap, Cost cost) {
    int rev = (int)adj[to].size() + (from == to ? 1 : 0);
    adj[from].emplace_back(from, to, rev, cap, cost);
    adj[to].emplace_back(to, from, (int)adj[from].size() - 1, 0, -cost);
    m_++;
  }

  // 最大流(Dinic)
  Cost max_flow(int source, int sink) {
    Cost flow = 0;
    while (true) {
      bfs(source);
      if (level[sink] == -1) {
        return flow;
      }
      iter = std::vector<int>(n_, 0);
      Cost current_flow = dfs(source, sink, F_MAX);
      while (current_flow > 0) {
        flow += current_flow;
        current_flow = dfs(source, sink, F_MAX);
      }
    }
  }

  // 最小費用流（Bellman–Ford による増加路）
  std::vector<std::pair<Cost, Cost>> min_cost_flow_slope(int source, int sink,
                                                       Cost flow_cutoff = F_MAX) {
    std::vector<std::pair<Cost, Cost>> result(1, {0, 0});
    if (flow_cutoff == 0) {
      return result;
    }
    Cost flow_total = 0;
    Cost cost_total = 0;
    while (true) {
      auto [dist, pv, pe] = bellman_ford(source);
      if (pv[sink] == -1) {
        return result;
      }
      Cost flow = F_MAX;
      int v = sink;
      while (v != source) {
        flow = std::min(flow, adj[pv[v]][pe[v]].cap);
        v = pv[v];
      }
      flow_total += flow;
      cost_total += flow * dist[sink];
      result.emplace_back(flow_total, cost_total);
      v = sink;
      while (v != source) {
        adj[pv[v]][pe[v]].cap -= flow;
        adj[v][adj[pv[v]][pe[v]].rev].cap += flow;
        v = pv[v];
      }
      if (flow_total >= flow_cutoff) {
        return result;
      }
    }
  }
  Cost min_cost_flow(int source, int sink, int flow) {
    if (flow == 0) {
      return 0;
    }
    auto slope = min_cost_flow_slope(source, sink, flow);
    int n = slope.size();
    if (slope[n - 1].first < flow) {
      return -1;
    }
    auto [x1, y1] = slope[n - 2];
    auto [x2, y2] = slope[n - 1];
    return (y2 - y1) / (x2 - x1) * (flow - x1) + y1;
  }

  template <class C_, class E_>
  friend std::ostream &operator<<(std::ostream &, const FlowGraph<C_, E_> &);
};

template <class Cost, class E>
const Cost FlowGraph<Cost, E>::F_MAX = std::numeric_limits<Cost>::max() >> 2;

template <class C_, class E_>
std::ostream &operator<<(std::ostream &os, const FlowGraph<C_, E_> &graph) {
  os << "N = " << graph.n_ << ", M = " << graph.m_ << '\n';
  for (const auto &ev : graph.adj) {
    for (const auto &e : ev) {
      os << e << '\n';
    }
  }
  return os;
}
} // namespace cp

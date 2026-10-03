#pragma once
#include "graph/edge_flow.hpp"

// グラフ(隣接リスト)
template <class Cost = ll, class E = FlowEdge<Cost>> class FlowGraph {
  int n_, m_;
  vector<vector<E>> adj;
  vector<int> level, iter;

  void bfs(int s) {
    level = vector<int>(n_, -1);
    level[s] = 0;
    queue<int> q;
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
      iter[v] = i;
      auto &e = adj[v][i];
      if (e.cap == 0 || level[v] >= level[e.to]) {
        continue;
      }
      Cost d = dfs(e.to, t, min(f, e.cap));
      if (d == 0) {
        continue;
      }
      e.cap -= d;
      adj[e.to][e.rev].cap += d;
      return d;
    }
    return 0;
  }
  tuple<vector<Cost>, vector<int>, vector<int>> bellman_ford(int s) {
    vector<Cost> dist(n_, F_MAX);
    vector<int> pv(n_, 0), pe(n_, 0);
    dist[s] = 0;
    while (true) {
      bool update = false;
      for (int v = 0; v < n_; v++) {
        if (dist[v] == F_MAX) {
          continue;
        }
        for (int i = 0; i < (int)adj[v].size(); i++) {
          auto &e = adj[v][i];
          if (e.cap > 0 && dist[e.to] > dist[v] + e.cost) {
            dist[e.to] = dist[v] + e.cost;
            update = true;
            pv[e.to] = v;
            pe[e.to] = i;
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

  vector<E> &operator[](int i) { return adj[i]; }

  void add_node() {
    n_++;
    adj.emplace_back();
    level.emplace_back();
  }
  void add_edge_max_flow(int from, int to, Cost cap) {
    adj[from].emplace_back(from, to, (int)adj[to].size(), cap);
    adj[to].emplace_back(to, from, (int)adj[from].size() - 1, 0);
    m_++;
  }
  void add_edge_min_cost_flow(int from, int to, Cost cap, Cost cost) {
    adj[from].emplace_back(from, to, (int)adj[to].size(), cap, cost);
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
      iter = vector<int>(n_, 0);
      Cost current_flow = dfs(source, sink, F_MAX);
      while (current_flow > 0) {
        flow += current_flow;
        current_flow = dfs(source, sink, F_MAX);
      }
    }
  }

  // 最小費用流 O(FVE)
  vector<pair<Cost, Cost>> min_cost_flow_slope(int source, int sink,
                                               Cost flow_cutoff = F_MAX) {
    vector<pair<Cost, Cost>> result(1, {0, 0});
    Cost flow_total = 0;
    Cost cost_total = 0;
    while (true) {
      auto [dist, pv, pe] = bellman_ford(source);
      if (dist[sink] == F_MAX) {
        return result;
      }
      Cost flow = F_MAX;
      int v = sink;
      while (v != source) {
        flow = min(flow, adj[pv[v]][pe[v]].cap);
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
  friend ostream &operator<<(ostream &, const FlowGraph<C_, E_> &);
};

template <class Cost, class E>
const Cost FlowGraph<Cost, E>::F_MAX = numeric_limits<Cost>::max() >> 2;

template <class C_, class E_>
ostream &operator<<(ostream &os, const FlowGraph<C_, E_> &graph) {
  os << "N = " << graph.n_ << ", M = " << graph.m_ << '\n';
  for (const auto &ev : graph.adj) {
    for (const auto &e : ev) {
      os << e << '\n';
    }
  }
  return os;
}
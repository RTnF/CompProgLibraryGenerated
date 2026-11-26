#pragma once
#include <algorithm>
#include <functional>
#include <limits>
#include <ostream>
#include <queue>
#include <unordered_map>
#include <utility>
#include <vector>

#include "edge.hpp"

namespace cp {

// グラフ(隣接リスト) (experiments/library/cpp/graph/graph_list.hpp)
// The algorithms (dijkstra, bellman_ford, prim, lowlink, find_cycle_directed, topological_sort,
// topological_sort_minimum) are members of this class; in the original they are declared here and defined in
// their own headers. Each is added here, with its body, when its header is ported (docs/graph_list.md).
template <class Cost = long long, class E = Edge<Cost>> class ListGraph {
  int n_, m_;
  std::vector<std::vector<E>> adj;
  std::unordered_map<int, std::vector<Cost>> shortest_path_dist;
  std::unordered_map<int, std::vector<int>> shortest_path_parent;

  // prim: the original lambda `span` (one tree of the forest from start_node)
  void prim_span(int start_node, Cost &mst_dist, std::vector<Cost> &dist, std::vector<bool> &used) const {
    using P = std::pair<Cost, int>;
    dist[start_node] = 0;
    std::priority_queue<P, std::vector<P>, std::greater<P>> pq;
    pq.emplace(0, start_node);
    while (!pq.empty()) {
      P p = pq.top();
      pq.pop();
      int v = p.second;
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
  }

  // lowlink: the original recursive lambda `dfs`
  void lowlink_dfs(int v, int parent, std::vector<bool> &visited, std::vector<int> &ord, std::vector<int> &low,
                   std::vector<int> &articulation_points, std::vector<std::pair<int, int>> &bridges,
                   int &visit_count) const {
    visited[v] = true;
    low[v] = ord[v] = visit_count++;
    bool is_articular = false;
    bool skipped_parent_edge = false;
    int child_count = 0;
    for (auto &e : adj[v]) {
      if (!visited[e.to]) {
        child_count++;
        lowlink_dfs(e.to, v, visited, ord, low, articulation_points, bridges, visit_count);
        low[v] = std::min(low[v], low[e.to]);
        if (parent != -1 && ord[v] <= low[e.to]) {
          is_articular = true;
        }
        if (ord[v] < low[e.to]) {
          bridges.emplace_back(std::min(v, e.to), std::max(v, e.to));
        }
      } else if (e.to == parent && !skipped_parent_edge) {
        // Ignore one reverse tree edge. Additional edges to the parent are back edges.
        skipped_parent_edge = true;
      } else {
        low[v] = std::min(low[v], ord[e.to]);
      }
    }
    if (parent == -1 && child_count >= 2) {
      is_articular = true;
    }
    if (is_articular) {
      articulation_points.emplace_back(v);
    }
  }

  // find_cycle_directed: the original recursive lambda `dfs`
  void find_cycle_dfs(int node, std::vector<char> &visited, std::vector<E> &in, std::vector<E> &cycle) {
    visited[node] = 1;
    for (auto &&e : adj[node]) {
      if (cycle.size()) {
        break;
      }
      if (!visited[e.to]) {
        in[e.to] = e;
        find_cycle_dfs(e.to, visited, in, cycle);
      } else if (visited[e.to] == 1) {
        cycle.emplace_back(e);
        for (int v = node; v != e.to; v = in[v].from) {
          cycle.emplace_back(in[v]);
        }
        std::reverse(cycle.begin(), cycle.end());
        return;
      }
    }
    visited[node] = 2;
  }

public:
  static const Cost UNREACHABLE;
  static const Cost NEGATIVE_CYCLE;
  ListGraph() : n_(0), m_(0), adj(0) {}
  ListGraph(int n) : n_(n), m_(0), adj(n) {}

  std::vector<E> &operator[](int i) { return adj[i]; }

  void add_node() {
    adj.emplace_back();
    n_++;
    reset_shortest();
  }
  template <class... Args> void add_edge(int from, int to, Args... args) {
    adj[from].emplace_back(from, to, args...);
    m_++;
    reset_shortest();
  }
  template <class... Args>
  void add_bidirectional_edge(int from, int to, Args... args) {
    adj[from].emplace_back(from, to, args...);
    adj[to].emplace_back(to, from, args...);
    m_ += 2;
    reset_shortest();
  }
  void reset_shortest() {
    shortest_path_dist.clear();
    shortest_path_parent.clear();
  }
  Cost distance(int from, int to) { return shortest_path_dist[from][to]; }
  std::vector<Cost> distance(int from) { return shortest_path_dist[from]; }
  std::vector<int> shortest_path(int from, int to) {
    std::vector<int> path;
    for (int cur = to; cur != -1; cur = shortest_path_parent[from][cur]) {
      path.emplace_back(cur);
    }
    std::reverse(path.begin(), path.end());
    return path;
  }

  // ダイクストラ法 (experiments/library/cpp/graph/dijkstra.hpp)
  void dijkstra(int start_node) {
    if (shortest_path_dist.count(start_node)) {
      return;
    }
    using P = std::pair<Cost, int>;
    std::vector<Cost> dist(n_, ListGraph::UNREACHABLE);
    std::vector<int> parent(n_, -1);
    dist[start_node] = 0;
    std::priority_queue<P, std::vector<P>, std::greater<P>> pq;
    pq.emplace(0, start_node);
    while (!pq.empty()) {
      P p = pq.top();
      pq.pop();
      int v = p.second;
      if (dist[v] < p.first) {
        continue;
      }
      for (const auto &e : adj[v]) {
        if (dist[v] + e.cost < dist[e.to]) {
          dist[e.to] = dist[v] + e.cost;
          parent[e.to] = v;
          pq.emplace(dist[e.to], e.to);
        }
      }
    }
    shortest_path_dist[start_node] = std::move(dist);
    shortest_path_parent[start_node] = std::move(parent);
  }

  // ベルマンフォード法 (experiments/library/cpp/graph/bellman_ford.hpp)
  void bellman_ford(int start_node) {
    if (shortest_path_dist.count(start_node)) {
      return;
    }
    std::vector<Cost> dist(n_, ListGraph::UNREACHABLE);
    std::vector<int> parent(n_, -1);
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

  // プリム法 (experiments/library/cpp/graph/prim.hpp)
  Cost prim() {
    Cost mst_dist = 0;
    std::vector<Cost> dist(n_, ListGraph<Cost>::UNREACHABLE);
    std::vector<bool> used(n_, false);
    for (int i = 0; i < n_; ++i) {
      if (!used[i]) {
        prim_span(i, mst_dist, dist, used);
      }
    }
    return mst_dist;
  }

  // 関節点・橋 (experiments/library/cpp/graph/lowlink.hpp)
  std::pair<std::vector<int>, std::vector<std::pair<int, int>>> lowlink() {
    using P = std::pair<int, int>;
    std::vector<bool> visited(n_, false);
    std::vector<int> ord(n_, 0), low(n_, 0), articulation_points;
    std::vector<P> bridges;
    int visit_count = 0;
    for (int i = 0; i < n_; ++i) {
      if (!visited[i]) {
        lowlink_dfs(i, -1, visited, ord, low, articulation_points, bridges, visit_count);
      }
    }
    std::sort(articulation_points.begin(), articulation_points.end());
    std::sort(bridges.begin(), bridges.end());
    return {articulation_points, bridges};
  }

  // サイクルを見つける (experiments/library/cpp/graph/find_cycle.hpp)
  std::vector<E> find_cycle_directed() {
    std::vector<char> visited(n_, 0);
    std::vector<E> in(n_, {-1, -1});
    std::vector<E> ret;
    for (int i = 0; i < n_; i++) {
      if (!visited[i]) {
        find_cycle_dfs(i, visited, in, ret);
      }
    }
    return ret;
  }

  template <class C_, class E_>
  friend std::ostream &operator<<(std::ostream &, const ListGraph<C_, E_> &);
};

template <class Cost, class E>
const Cost ListGraph<Cost, E>::UNREACHABLE = std::numeric_limits<Cost>::max() >> 2;
template <class Cost, class E>
const Cost ListGraph<Cost, E>::NEGATIVE_CYCLE = std::numeric_limits<Cost>::min() >> 2;

template <class C_, class E_>
std::ostream &operator<<(std::ostream &os, const ListGraph<C_, E_> &graph) {
  os << "N = " << graph.n_ << ", M = " << graph.m_ << '\n';
  for (const auto &ev : graph.adj) {
    for (const auto &e : ev) {
      os << e << '\n';
    }
  }
  return os;
}

} // namespace cp

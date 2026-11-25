#include "template/small_template.hpp"
#ifdef VERIFY_PUBLIC_LOWLINK
#include "../../library/graph/graph_list.hpp"
using LowlinkGraph = cp::ListGraph<>;
#else
#include "graph/lowlink.hpp"
using LowlinkGraph = ListGraph<>;
#endif

using UndirectedEdge = std::pair<int, int>;

// Merge component labels after removing one vertex or one edge occurrence.
static int components(int n, const std::vector<UndirectedEdge> &edges,
                      int removed_vertex = -1, int removed_edge = -1) {
  std::vector<int> label(n);
  std::iota(label.begin(), label.end(), 0);
  int count = n - (removed_vertex != -1);
  for (int i = 0; i < static_cast<int>(edges.size()); ++i) {
    auto [u, v] = edges[i];
    if (i == removed_edge || u == removed_vertex || v == removed_vertex ||
        label[u] == label[v]) {
      continue;
    }
    const int previous = label[v];
    for (int &component : label) {
      if (component == previous) {
        component = label[u];
      }
    }
    --count;
  }
  return count;
}

static void check(int n, const std::vector<UndirectedEdge> &edges) {
  LowlinkGraph graph(n);
  for (auto [u, v] : edges) {
    graph.add_bidirectional_edge(u, v);
  }
  const int original_count = components(n, edges);
  std::vector<int> articulation_points;
  std::vector<UndirectedEdge> bridges;
  for (int v = 0; v < n; ++v) {
    if (components(n, edges, v) > original_count) {
      articulation_points.push_back(v);
    }
  }
  for (int i = 0; i < static_cast<int>(edges.size()); ++i) {
    if (components(n, edges, -1, i) > original_count) {
      auto [u, v] = edges[i];
      bridges.emplace_back(std::min(u, v), std::max(u, v));
    }
  }
  std::sort(bridges.begin(), bridges.end());
  assert(graph.lowlink() == std::make_pair(articulation_points, bridges));
}

int main() {
  check(0, {});
  check(2, {{0, 1}, {0, 1}});
  check(3, {{2, 1}, {1, 0}, {1, 2}, {2, 2}, {0, 0}});

  constexpr int n = 4;
  constexpr int edge_patterns = 3 * 3 * 3 * 3 * 3 * 3;
  for (int pattern = 0; pattern < edge_patterns; ++pattern) {
    for (int loops = 0; loops < (1 << n); ++loops) {
      std::vector<UndirectedEdge> edges;
      int multiplicities = pattern;
      for (int u = 0; u < n; ++u) {
        if ((loops >> u) & 1) {
          edges.emplace_back(u, u);
        }
        for (int v = u + 1; v < n; ++v) {
          edges.insert(edges.end(), multiplicities % 3, {u, v});
          multiplicities /= 3;
        }
      }
      check(n, edges);
      std::reverse(edges.begin(), edges.end());
      check(n, edges);
    }
  }
}

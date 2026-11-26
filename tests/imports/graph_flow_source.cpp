#include "template/small_template.hpp"
#include "graph/graph_flow.hpp"

#include <cassert>

void check_reverse_slots() {
  FlowGraph<int> graph(2);
  graph.add_edge_max_flow(0, 0, 7);
  graph.add_edge_min_cost_flow(0, 0, 3, 2);
  graph.add_edge_max_flow(0, 1, 4);
  graph.add_edge_min_cost_flow(0, 1, 5, 1);
  for (int u = 0; u < 2; ++u) {
    for (int i = 0; i < static_cast<int>(graph[u].size()); ++i) {
      const auto &edge = graph[u][i];
      assert(edge.rev >= 0 && edge.rev < static_cast<int>(graph[edge.to].size()));
      if (edge.to == u) {
        assert(edge.rev != i);
      }
      const auto &reverse = graph[edge.to][edge.rev];
      assert(reverse.to == u && reverse.rev == i);
      assert(reverse.cost == -edge.cost);
    }
  }
  assert(graph.max_flow(0, 1) == 9);
}

void check_zero_flow() {
  FlowGraph<int> graph(2);
  assert(graph.min_cost_flow(0, 1, 0) == 0);
  graph.add_edge_min_cost_flow(0, 1, 3, 5);
  const auto points = graph.min_cost_flow_slope(0, 1, 0);
  assert(points.size() == 1 && points.front() == std::make_pair(0, 0));
  assert(graph.min_cost_flow(0, 1, 0) == 0);
  assert(graph[0][0].cap == 3 && graph[1][0].cap == 0);
  assert(graph.min_cost_flow(0, 1, 1) == 5);
  assert(graph[0][0].cap == 0 && graph[1][0].cap == 3);
}

void check_large_distances() {
  const int limit = FlowGraph<int>::F_MAX;
  for (int cost : {limit, limit + 1, 2 * limit}) {
    FlowGraph<int> direct(2);
    direct.add_edge_min_cost_flow(0, 1, 1, cost);
    assert(direct.min_cost_flow(0, 1, 1) == cost);
    FlowGraph<int> path(3);
    path.add_edge_min_cost_flow(0, 1, 1, cost);
    path.add_edge_min_cost_flow(1, 2, 1, -limit);
    assert(path.min_cost_flow(0, 2, 1) == cost - limit);
  }
  FlowGraph<int> disconnected(2);
  assert(disconnected.min_cost_flow(0, 1, 1) == -1);
}

int main() {
  check_reverse_slots();
  check_zero_flow();
  check_large_distances();
}

#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/graph_flow.hpp"
#include <cassert>
#include <map>
#include <random>
#include <sstream>
#include <type_traits>

struct Arc {
  int u;
  int v;
  int capacity;
  int cost;
};

using Graph = cp::FlowGraph<long long>;
using Minima = std::map<int, long long>;

void enumerate(const std::vector<Arc> &arcs, int from, int to, std::size_t index,
               long long cost, std::vector<int> &balance, Minima &minimum) {
  if (index == arcs.size()) {
    if (balance[from] < 0 || balance[from] != -balance[to]) {
      return;
    }
    for (std::size_t v = 0; v < balance.size(); ++v) {
      if (v != static_cast<std::size_t>(from) && v != static_cast<std::size_t>(to) && balance[v] != 0) {
        return;
      }
    }
    const auto [it, inserted] = minimum.try_emplace(balance[from], cost);
    if (!inserted) {
      it->second = std::min(it->second, cost);
    }
    return;
  }
  const Arc e = arcs[index];
  for (int flow = 0; flow <= e.capacity; ++flow) {
    balance[e.u] += flow;
    balance[e.v] -= flow;
    enumerate(arcs, from, to, index + 1, cost + flow * e.cost, balance, minimum);
    balance[e.u] -= flow;
    balance[e.v] += flow;
  }
}

void check_against_enumeration() {
  std::mt19937 random(20261126);
  for (int trial = 0; trial < 3000; ++trial) {
    const int vertices = 2 + random() % 4;
    std::vector<Arc> arcs;
    const int count = random() % 9;
    for (int i = 0; i < count; ++i) {
      int u = random() % vertices;
      int v = random() % vertices;
      int cost = random() % 12;
      if (trial % 2 == 0) {
        if (u == v) {
          continue;
        }
        if (u > v) {
          std::swap(u, v);
        }
        cost -= 6;
      }
      arcs.push_back({u, v, static_cast<int>(random() % 4), cost});
    }
    Graph maxGraph(vertices), costGraph(vertices);
    for (const Arc e : arcs) {
      maxGraph.add_edge_max_flow(e.u, e.v, e.capacity);
      costGraph.add_edge_min_cost_flow(e.u, e.v, e.capacity, e.cost);
    }
    std::vector<int> balance(vertices);
    Minima oracle;
    enumerate(arcs, 0, vertices - 1, 0, 0, balance, oracle);
    const int max = oracle.rbegin()->first;
    assert(maxGraph.max_flow(0, vertices - 1) == max);
    auto costCopy = costGraph;
    const auto slope = costCopy.min_cost_flow_slope(0, vertices - 1);
    assert(slope.front() == std::make_pair(0LL, 0LL) && slope.back().first == max);
    for (std::size_t j = 1; j < slope.size(); ++j) {
      const auto [left, leftCost] = slope[j - 1];
      const auto [right, rightCost] = slope[j];
      assert(left < right);
      assert((rightCost - leftCost) % (right - left) == 0);
      for (int amount = left; amount <= right; ++amount) {
        assert(oracle.at(amount) == leftCost + (rightCost - leftCost) / (right - left) * (amount - left));
      }
    }
    for (int want = 0; want <= max + 1; ++want) {
      auto copy = costGraph;
      const auto expected = oracle.find(want);
      assert(copy.min_cost_flow(0, vertices - 1, want) == (expected == oracle.end() ? -1 : expected->second));
    }
  }
}

struct CapacityEdge {
  int from;
  int to;
  int rev;
  int cap;

  CapacityEdge(int from, int to, int rev, int cap)
      : from(from), to(to), rev(rev), cap(cap) {}
};

void check_public_interface() {
  static_assert(std::is_same_v<cp::FlowGraph<>, Graph>);
  assert(Graph::F_MAX == (std::numeric_limits<long long>::max() >> 2));
  Graph g;
  g.add_node();
  g.add_node();
  g.add_edge_min_cost_flow(0, 0, 2, 3);
  assert(g[0][0].rev == 1 && g[0][1].rev == 0);
  g.add_edge_min_cost_flow(0, 1, 3, 5);
  auto &row = g[0];
  row[2].cap = 2;
  assert(g[0][2].cap == 2);
  const std::vector<std::pair<long long, long long>> origin{{0, 0}};
  assert(g.min_cost_flow(1, 0, 0) == 0);
  assert(g.min_cost_flow_slope(1, 0, 0) == origin);
  assert(g[0][2].cap == 2 && g[1][0].cap == 0);
  auto cutoff = g;
  assert(cutoff.min_cost_flow(0, 1, 1) == 5);
  assert(cutoff[0][2].cap == 0 && cutoff[1][0].cap == 2);
  std::ostringstream output;
  output << g;
  assert(output.str() ==
         "N = 2, M = 2\n"
         "0: 0 -> 0 (2, 3)\n"
         "1: 0 -> 0 (0, -3)\n"
         "2: 0 -> 1 (2, 5)\n"
         "3: 1 -> 0 (0, -5)\n");

  for (long long cost : {Graph::F_MAX, Graph::F_MAX + 1, 2 * Graph::F_MAX}) {
    Graph bound(3);
    bound.add_edge_min_cost_flow(0, 1, 1, cost);
    bound.add_edge_min_cost_flow(1, 2, 1, -Graph::F_MAX);
    assert(bound.min_cost_flow(0, 2, 1) == cost - Graph::F_MAX);
  }

  cp::FlowGraph<int, CapacityEdge> custom(2);
  custom.add_edge_max_flow(0, 0, 2);
  custom.add_edge_max_flow(0, 1, 7);
  assert(custom[0][0].rev == 1 && custom[0][1].rev == 0);
  assert(custom.max_flow(0, 1) == 7);
  assert(custom.max_flow(0, 1) == 0);
}

int main() {
  check_public_interface();
  check_against_enumeration();
}

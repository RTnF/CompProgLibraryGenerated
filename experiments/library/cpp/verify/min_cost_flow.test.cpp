#define PROBLEM                                                                \
  "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/6/GRL_6_B"
#include "graph/graph_flow.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int V, E, F;
  cin >> V >> E >> F;
  FlowGraph g(V);
  for (int i = 0; i < E; i++) {
    int u, v;
    cin >> u >> v;
    ll c, d;
    cin >> c >> d;
    g.add_edge_min_cost_flow(u, v, c, d);
  }
  cout << g.min_cost_flow(0, V - 1, F) << '\n';
}
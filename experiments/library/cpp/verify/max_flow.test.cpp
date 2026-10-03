#define PROBLEM                                                                \
  "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/6/GRL_6_A"
#include "graph/graph_flow.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int V, E;
  cin >> V >> E;
  FlowGraph g(V);
  for (int i = 0; i < E; i++) {
    int u, v;
    cin >> u >> v;
    ll c;
    cin >> c;
    g.add_edge_max_flow(u, v, c);
  }
  cout << g.max_flow(0, V - 1) << '\n';
}
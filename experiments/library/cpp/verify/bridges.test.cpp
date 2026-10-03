#define PROBLEM "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/3/GRL_3_B"
#include "graph/lowlink.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int V, E;
  cin >> V >> E;
  ListGraph graph(V);
  for (int i = 0; i < E; ++i) {
    int s, t;
    cin >> s >> t;
    graph.add_bidirectional_edge(s, t);
  }
  auto [aps, bridges] = graph.lowlink();
  for (auto &&b: bridges) {
    cout << b.first << ' ' << b.second << '\n';
  }
}
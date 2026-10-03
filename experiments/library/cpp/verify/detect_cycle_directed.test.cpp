#define PROBLEM "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/4/GRL_4_A"
#include "graph/topological_sort.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int V, E;
  cin >> V >> E;
  ListGraph graph(V);
  for (int i = 0; i < E; ++i) {
    int s, t;
    cin >> s >> t;
    graph.add_edge(s, t);
  }
  cout << !graph.topological_sort_minimum().size() << '\n';
}
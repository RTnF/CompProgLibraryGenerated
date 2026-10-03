#define PROBLEM "https://judge.yosupo.jp/problem/shortest_path"
#include "graph/dijkstra.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int V, E, start, goal;
  cin >> V >> E >> start >> goal;
  ListGraph graph(V);
  for (int i = 0; i < E; ++i) {
    int s, t, d;
    cin >> s >> t >> d;
    graph.add_edge(s, t, d);
  }
  graph.dijkstra(start);
  ll dist = graph.distance(start, goal);
  if (dist == ListGraph<>::UNREACHABLE) {
    cout << "-1\n";
  } else {
    auto ans = graph.shortest_path(start, goal);
    int n = (int)ans.size() - 1;
    cout << dist << ' ' << n << '\n';
    for (int i = 0; i < n; ++i) {
      cout << ans[i] << ' ' << ans[i + 1] << '\n';
    }
  }
}
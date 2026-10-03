#define PROBLEM                                                                \
  "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_C"
#include "graph/warshall_floyd.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int V, E;
  cin >> V >> E;
  MatrixGraph g(V);
  for (int i = 0; i < E; ++i) {
    int s, t;
    ll d;
    cin >> s >> t >> d;
    g.add_edge(s, t, d);
  }
  g.warshall_floyd();
  if (g.has_negative_cycle()) {
    cout << "NEGATIVE CYCLE\n";
  } else {
    for (int i = 0; i < V; ++i) {
      for (int j = 0; j < V; ++j) {
        if (g.distance(i, j) >= MatrixGraph<>::UNREACHABLE) {
          cout << "INF";
        } else {
          cout << g.distance(i, j);
        }
        cout << " \n"[j == V - 1];
      }
    }
  }
}
#define PROBLEM "https://judge.yosupo.jp/problem/cycle_detection"
#include "graph/find_cycle.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int N, M;
  cin >> N >> M;
  ListGraph graph(N);
  for (int i = 0; i < M; ++i) {
    int s, t;
    cin >> s >> t;
    graph.add_edge(s, t);
  }
  auto ans = graph.find_cycle_directed();
  if (ans.size()) {
    cout << ans.size() << '\n';
    for (auto &&e : ans) {
      cout << e.id << '\n';
    }
  } else {
    cout << "-1\n";
  }
}
#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/graph_list.hpp"
#include <cassert>
#include <random>
#include <sstream>
#include <tuple>

// A user edge type: ListGraph<Cost, E> forwards the extra arguments of add_edge to E's constructor.
struct Labeled {
  int from, to;
  long long cost;
  char label;
  Labeled(int f, int t, long long c, char l) : from(f), to(t), cost(c), label(l) {}
};

// ListGraph::dijkstra against Bellman-Ford on random graphs with nonnegative costs: the distances, UNREACHABLE for
// the unreachable vertices, and shortest_path (a walk along real edges whose cost is the distance).
static void test_dijkstra() {
  std::mt19937 rng(20261125);
  for (int iter = 0; iter < 300; ++iter) {
    int n = rng() % 9 + 1;
    cp::ListGraph<long long> g(n);
    std::vector<std::vector<long long>> w(n, std::vector<long long>(n, -1));
    int m = rng() % (n * n + 1);
    std::vector<std::tuple<int, int, long long>> edges;
    for (int k = 0; k < m; ++k) {
      int a = rng() % n, b = rng() % n;
      long long c = rng() % 20;
      g.add_edge(a, b, c);
      edges.emplace_back(a, b, c);
    }
    for (int s = 0; s < n; ++s) {
      g.dijkstra(s);
      g.dijkstra(s);  // a second call keeps the cached result
      const long long INF = cp::ListGraph<long long>::UNREACHABLE;
      std::vector<long long> d(n, INF);
      d[s] = 0;
      for (int r = 0; r < n; ++r)
        for (auto [a, b, c] : edges)
          if (d[a] != INF && d[a] + c < d[b]) d[b] = d[a] + c;
      auto dist = g.distance(s);
      assert((int)dist.size() == n);
      for (int t = 0; t < n; ++t) {
        assert(dist[t] == d[t] && g.distance(s, t) == d[t]);
        if (d[t] == INF) continue;
        auto path = g.shortest_path(s, t);
        assert(!path.empty() && path.front() == s && path.back() == t);
        long long cost = 0;
        for (size_t i = 0; i + 1 < path.size(); ++i) {
          long long best = -1;
          for (auto [a, b, c] : edges)
            if (a == path[i] && b == path[i + 1] && (best < 0 || c < best)) best = c;
          assert(best >= 0);
          cost += best;
        }
        assert(cost == d[t]);
      }
    }
    // adding an edge clears the caches
    g.add_edge(0, 0, 1LL);
    assert(g.distance(0).empty());
  }
}

int main() {
  // ListGraph<long long, Edge<long long>>: the default arguments
  cp::ListGraph<> g(3);
  g.add_edge(0, 1, 5LL);
  g.add_edge(1, 2);
  g.add_bidirectional_edge(2, 0, -3LL);
  assert(g[0].size() == 2 && g[1].size() == 1 && g[2].size() == 1);
  assert(g[0][0].from == 0 && g[0][0].to == 1 && g[0][0].cost == 5 && g[0][0].id == 0);
  assert(g[1][0].to == 2 && g[1][0].cost == 1 && g[1][0].id == 1);
  assert(g[2][0].to == 0 && g[2][0].cost == -3 && g[2][0].id == 2);
  // add_bidirectional_edge(2, 0) appends 2 -> 0 to row 2, then 0 -> 2 to row 0
  assert(g[0][1].from == 0 && g[0][1].to == 2 && g[0][1].cost == -3 && g[0][1].id == 3);
  g.add_node();
  g.add_edge(3, 0, 7LL);
  assert(g[3].size() == 1 && g[3][0].id == 4);
  // distance(from) of a start without computed distances: an empty vector (the map inserts it)
  assert(g.distance(0).empty());
  g.reset_shortest();
  // the static members
  assert(cp::ListGraph<>::UNREACHABLE == (std::numeric_limits<long long>::max() >> 2));
  assert(cp::ListGraph<>::NEGATIVE_CYCLE == (std::numeric_limits<long long>::min() >> 2));
  assert(cp::ListGraph<int>::UNREACHABLE == (std::numeric_limits<int>::max() >> 2));
  // operator<<
  std::ostringstream os;
  os << g;
  assert(os.str() == "N = 4, M = 5\n0: 0 -> 1 (5)\n3: 0 -> 2 (-3)\n1: 1 -> 2 (1)\n2: 2 -> 0 (-3)\n4: 3 -> 0 (7)\n");
  // a default-constructed graph
  cp::ListGraph<int> h;
  h.add_node();
  h.add_node();
  h.add_edge(0, 1, 2);
  assert(h[0][0].id == 0 && h[0][0].cost == 2);
  // a user edge type with an extra constructor argument
  cp::ListGraph<long long, Labeled> u(2);
  u.add_edge(0, 1, 9LL, 'x');
  u.add_bidirectional_edge(1, 0, 4LL, 'y');
  assert(u[0].size() == 2 && u[0][0].label == 'x' && u[0][1].label == 'y' && u[0][1].to == 1);
  assert(u[1].size() == 1 && u[1][0].cost == 4);
  // writing through operator[]
  g[1][0].cost = 10;
  assert(g[1][0].cost == 10);
  // after the id checks above (the ids come from the shared Edge<long long> counter)
  test_dijkstra();
  return 0;
}

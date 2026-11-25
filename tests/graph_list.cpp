#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/graph_list.hpp"
#include <cassert>
#include <climits>
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

// ListGraph::bellman_ford against a reference: Floyd-Warshall reachability and distances on small graphs with
// negative costs; a vertex reachable from s through a vertex on a negative cycle is NEGATIVE_CYCLE, an unreachable
// one UNREACHABLE, the others the shortest distance with a shortest path.
static void test_bellman_ford() {
  std::mt19937 rng(20261126);
  using G = cp::ListGraph<long long>;
  for (int iter = 0; iter < 300; ++iter) {
    int n = rng() % 7 + 1;
    G g(n);
    std::vector<std::tuple<int, int, long long>> edges;
    int m = rng() % (2 * n + 1);
    for (int k = 0; k < m; ++k) {
      int a = rng() % n, b = rng() % n;
      long long c = (long long)(rng() % 21) - 6;
      g.add_edge(a, b, c);
      edges.emplace_back(a, b, c);
    }
    std::vector<std::vector<bool>> reach(n, std::vector<bool>(n, false));
    for (int i = 0; i < n; ++i) reach[i][i] = true;
    for (auto [a, b, c] : edges) reach[a][b] = true;
    for (int k = 0; k < n; ++k)
      for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j)
          if (reach[i][k] && reach[k][j]) reach[i][j] = true;
    // x is on a negative cycle iff the n-round Bellman-Ford from x still improves x (closed walks from x)
    auto on_neg = [&](int x) {
      const long long INF = std::numeric_limits<long long>::max() / 4;
      std::vector<long long> d(n, INF);
      d[x] = 0;
      for (int r = 0; r < 2 * n; ++r)
        for (auto [a, b, c] : edges)
          if (d[a] != INF && d[a] + c < d[b]) d[b] = d[a] + c;
      return d[x] < 0;
    };
    std::vector<bool> neg(n);
    for (int x = 0; x < n; ++x) neg[x] = on_neg(x);
    for (int s = 0; s < n; ++s) {
      g.bellman_ford(s);
      g.bellman_ford(s);
      for (int t = 0; t < n; ++t) {
        bool negreach = false;
        for (int x = 0; x < n; ++x) negreach = negreach || (reach[s][x] && neg[x] && reach[x][t]);
        long long dt = g.distance(s, t);
        if (!reach[s][t]) {
          assert(dt == G::UNREACHABLE);
        } else if (negreach) {
          assert(dt == G::NEGATIVE_CYCLE);
        } else {
          // the shortest distance: Bellman-Ford with n rounds over the walks avoiding negative cycles
          const long long INF = G::UNREACHABLE;
          std::vector<long long> d(n, INF);
          d[s] = 0;
          for (int r = 0; r < n; ++r)
            for (auto [a, b, c] : edges)
              if (d[a] != INF && d[a] + c < d[b]) d[b] = d[a] + c;
          assert(dt == d[t]);
          auto path = g.shortest_path(s, t);
          assert(path.front() == s && path.back() == t);
          long long cost = 0;
          for (size_t i = 0; i + 1 < path.size(); ++i) {
            long long best = LLONG_MAX;
            for (auto [a, b, c] : edges)
              if (a == path[i] && b == path[i + 1]) best = std::min(best, c);
            assert(best != LLONG_MAX);
            cost += best;
          }
          assert(cost == dt);
        }
      }
    }
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
  test_bellman_ford();
  return 0;
}

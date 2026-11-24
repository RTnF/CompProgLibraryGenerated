#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/graph_matrix.hpp"
#include <random>
#include <sstream>
#include <vector>

// A naive model on the real edges (entries below UNREACHABLE): Bellman-Ford from each vertex, and a negative cycle
// when some distance still improves after n rounds.
template <class Cost> struct Naive {
  int n;
  std::vector<std::vector<Cost>> w;
  std::vector<std::vector<bool>> edge;
  explicit Naive(int n_) : n(n_), w(n_, std::vector<Cost>(n_, 0)), edge(n_, std::vector<bool>(n_, false)) {}
  void add(int a, int b, Cost c) { w[a][b] = c, edge[a][b] = true; }
  // dist[s][t]: the shortest real walk weight (0 for s == t); reach[s][t]; negative: some negative cycle.
  bool negative = false;
  std::vector<std::vector<Cost>> dist;
  std::vector<std::vector<bool>> reach;
  void solve() {
    dist.assign(n, std::vector<Cost>(n, 0));
    reach.assign(n, std::vector<bool>(n, false));
    for (int s = 0; s < n; ++s) {
      std::vector<Cost> d(n, 0);
      std::vector<bool> r(n, false);
      r[s] = true;
      for (int round = 0; round < n; ++round) {
        bool changed = false;
        for (int a = 0; a < n; ++a) {
          if (!r[a]) continue;
          for (int b = 0; b < n; ++b) {
            if (edge[a][b] && (!r[b] || d[a] + w[a][b] < d[b])) d[b] = d[a] + w[a][b], r[b] = true, changed = true;
          }
        }
        if (changed && round == n - 1) negative = true;
      }
      for (int t = 0; t < n; ++t) dist[s][t] = d[t], reach[s][t] = r[t];
    }
  }
};

template <class Cost> void check_random(std::mt19937 &random, int n, int edges, int low, int high) {
  using G = cp::MatrixGraph<Cost>;
  G g(n);
  Naive<Cost> naive(n);
  for (int e = 0; e < edges; ++e) {
    const int a = static_cast<int>(random() % n), b = static_cast<int>(random() % n);
    if (a == b) continue;  // self loops are checked separately
    const Cost c = static_cast<Cost>(low + static_cast<int>(random() % (high - low + 1)));
    g.add_edge(a, b, c);
    naive.add(a, b, c);
  }
  g.warshall_floyd();
  naive.solve();
  assert(g.has_negative_cycle() == naive.negative);
  if (naive.negative) return;
  for (int s = 0; s < n; ++s) {
    for (int t = 0; t < n; ++t) {
      const std::vector<int> path = g.get_shortest_path(s, t);
      if (!naive.reach[s][t]) {
        assert(g.distance(s, t) == G::UNREACHABLE);
        assert(path.empty());
        continue;
      }
      assert(g.distance(s, t) == naive.dist[s][t]);
      if (s == t) {
        assert(path == std::vector<int>{s});
        continue;
      }
      // a walk from s to t along real edges whose weight is the distance
      assert(!path.empty() && path.front() == s && path.back() == t);
      Cost sum = 0;
      for (size_t k = 0; k + 1 < path.size(); ++k) {
        assert(naive.edge[path[k]][path[k + 1]]);
        sum += naive.w[path[k]][path[k + 1]];
      }
      assert(sum == g.distance(s, t));
      assert(static_cast<int>(path.size()) <= n);
    }
  }
}

int main() {
  std::mt19937 random(20261125);
  // The constants and the empty graph.
  assert(cp::MatrixGraph<>::UNREACHABLE == (std::numeric_limits<long long>::max() >> 2));
  assert(cp::MatrixGraph<int>::UNREACHABLE == (std::numeric_limits<int>::max() >> 2));
  {
    cp::MatrixGraph<> g(0);
    g.warshall_floyd();
    assert(!g.has_negative_cycle());
  }
  // A path graph: distances, unreachable pairs, the paths of the original example.
  {
    cp::MatrixGraph<> g(4);
    g.add_edge(0, 1, 5);
    g.add_edge(1, 2, 7);
    g.add_edge(0, 2, 20);
    g.warshall_floyd();
    assert(g.distance(0, 2) == 12 && g.distance(2, 0) == cp::MatrixGraph<>::UNREACHABLE);
    assert(g.distance(0, 3) == cp::MatrixGraph<>::UNREACHABLE && g.distance(3, 3) == 0);
    assert((g.get_shortest_path(0, 1) == std::vector<int>{0, 1}));
    assert((g.get_shortest_path(0, 2) == std::vector<int>{0, 1, 2}));
    assert(g.get_shortest_path(2, 0).empty() && g.get_shortest_path(0, 3).empty());
    assert((g.get_shortest_path(3, 3) == std::vector<int>{3}));
    // a second call keeps the computed result
    g.add_edge(0, 2, 1);
    g.warshall_floyd();
    assert(g.distance(0, 2) == 12);
  }
  // Negative edges without a negative cycle, and a negative cycle (also through a self loop).
  {
    cp::MatrixGraph<> g(3);
    g.add_edge(0, 1, 4);
    g.add_edge(1, 2, -3);
    g.add_edge(0, 2, 2);
    g.warshall_floyd();
    assert(!g.has_negative_cycle() && g.distance(0, 2) == 1);
    assert((g.get_shortest_path(0, 2) == std::vector<int>{0, 1, 2}));
  }
  {
    cp::MatrixGraph<> g(3);
    g.add_edge(0, 1, 1);
    g.add_edge(1, 0, -2);
    g.warshall_floyd();
    assert(g.has_negative_cycle());
  }
  {
    cp::MatrixGraph<> g(2);
    g.add_edge(1, 1, -1);
    g.warshall_floyd();
    assert(g.has_negative_cycle());
  }
  // Random graphs against the naive model, for long long and int.
  for (int n : {1, 2, 3, 4, 5, 6, 8, 12}) {
    for (int rep = 0; rep < 40; ++rep) {
      check_random<long long>(random, n, static_cast<int>(random() % (n * n + 1)), 0, 30);
      check_random<long long>(random, n, static_cast<int>(random() % (n * n + 1)), -5, 30);
      check_random<int>(random, n, static_cast<int>(random() % (n * n + 1)), -3, 20);
    }
  }
  // The output operator of the original.
  {
    cp::MatrixGraph<int> g(2);
    g.add_edge(0, 1, 3);
    std::ostringstream os;
    os << g;
    const int u = cp::MatrixGraph<int>::UNREACHABLE;
    assert(os.str() == "N = 2, M = 1\n0 3\n" + std::to_string(u) + " 0\n");
  }
  return 0;
}

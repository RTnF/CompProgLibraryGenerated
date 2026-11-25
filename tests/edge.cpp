#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/edge.hpp"
#include <cassert>
#include <sstream>

// Edge<T>: both constructors, the per-specialization id counter, and operator<<.
int main() {
  cp::Edge<long long> a(0, 1, 5);
  assert(a.from == 0 && a.to == 1 && a.id == 0 && a.cost == 5);
  cp::Edge<long long> b(2, 3);
  assert(b.from == 2 && b.to == 3 && b.id == 1 && b.cost == 1);
  // another specialization has its own counter
  cp::Edge<int> c(4, 5, -7);
  assert(c.id == 0 && c.cost == -7);
  cp::Edge<double> d(1, 0, 2.5);
  assert(d.id == 0 && d.cost == 2.5);
  cp::Edge<long long> e(7, 7, -3);
  assert(e.id == 2);
  // copies keep the id; only construction takes a new one
  cp::Edge<long long> f = e;
  assert(f.id == 2);
  cp::Edge<long long> g(1, 2);
  assert(g.id == 3);
  std::ostringstream os;
  os << a << '|' << b << '|' << c << '|' << d;
  assert(os.str() == "0: 0 -> 1 (5)|1: 2 -> 3 (1)|0: 4 -> 5 (-7)|0: 1 -> 0 (2.5)");
  std::vector<cp::Edge<int>> v;
  for (int i = 0; i < 1000; ++i) {
    v.emplace_back(i, i + 1, i);
    assert(v.back().id == i + 1);
  }
  return 0;
}

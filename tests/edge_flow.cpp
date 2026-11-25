#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/graph/edge_flow.hpp"
#include <cassert>
#include <sstream>

// FlowEdge<T>: the three constructors, the clamped capacity, the per-specialization id counter, and operator<<.
int main() {
  cp::FlowEdge<long long> a(0, 1, 2, 5, 7);
  assert(a.from == 0 && a.to == 1 && a.rev == 2 && a.id == 0 && a.cap == 5 && a.cost == 7);
  cp::FlowEdge<long long> b(1, 0, 3, -4);
  assert(b.id == 1 && b.cap == 0 && b.cost == 0 && b.rev == 3);
  cp::FlowEdge<long long> c(2, 3, 0);
  assert(c.id == 2 && c.cap == 0 && c.cost == 0);
  cp::FlowEdge<long long> d(2, 3, 1, 9, -2);
  assert(d.id == 3 && d.cap == 9 && d.cost == -2);
  // another specialization has its own counter
  cp::FlowEdge<int> e(4, 5, 0, -1, 3);
  assert(e.id == 0 && e.cap == 0 && e.cost == 3);
  cp::FlowEdge<double> f(1, 0, 0, 2.5, 1.5);
  assert(f.id == 0 && f.cap == 2.5 && f.cost == 1.5);
  cp::FlowEdge<long long> g = d;
  assert(g.id == 3);
  std::ostringstream os;
  os << a << '|' << b << '|' << e << '|' << f;
  assert(os.str() == "0: 0 -> 1 (5, 7)|1: 1 -> 0 (0, 0)|0: 4 -> 5 (0, 3)|0: 1 -> 0 (2.5, 1.5)");
  return 0;
}

#include "experiments/library/cpp/template/small_template.hpp"
#include "experiments/library/cpp/number/square_matrix.hpp"

int main() {
  const SquareMatrix<int, 1> a{{{1}}};
  const auto minus = -a;
  return minus[0][0] == -1 ? 0 : 1;
}

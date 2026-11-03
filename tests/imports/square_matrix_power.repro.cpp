#include "experiments/library/cpp/template/small_template.hpp"
#include "experiments/library/cpp/number/square_matrix.hpp"

int main() {
  const SquareMatrix<long long, 1> a{{{LLONG_MAX}}};
  return a.pow(1)[0][0] != LLONG_MAX;
}

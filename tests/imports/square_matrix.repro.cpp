#include "experiments/library/cpp/template/small_template.hpp"
#include "experiments/library/cpp/number/square_matrix.hpp"

int main() {
  const SquareMatrix<int, 2> a{}, b{};
  return a == b;
}

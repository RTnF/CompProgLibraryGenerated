#include "../../experiments/library/cpp/number/ratio.hpp"

using Scalar = RATIO_TEST_TYPE;

int main() {
  long long a, p, d;
  while (std::cin >> a >> p >> d) {
    const Scalar x = static_cast<Scalar>(a);
    const Ratio<Scalar> r(static_cast<Scalar>(p), static_cast<Scalar>(d));
    Ratio<Scalar> self = r;
    self /= self;
    std::cout << (x + r) << ' ' << (x - r) << ' ' << (x * r) << ' ' << (x / r) << ' ' << self << '\n';
  }
}

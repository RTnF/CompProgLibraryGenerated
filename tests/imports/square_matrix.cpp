#include "experiments/library/cpp/template/small_template.hpp"
#include "experiments/verification/array/element_count.hpp"
#include "experiments/verification/number/square_matrix.hpp"

using Matrix = cp::SquareMatrix<long long, 2>;
static_assert(std::is_same_v<decltype(&Matrix::pow), Matrix (Matrix::*)(long long) const>);
static_assert(std::is_aggregate_v<Matrix>);
static_assert(std::is_trivial_v<Matrix>);
static_assert(std::is_standard_layout_v<Matrix>);
using Flat = std::array<long long, 4>;

Matrix matrix(const Flat &v) {
  Matrix result;
  for (int i = 0; i < 4; ++i)
    result[i / 2][i % 2] = v[i];
  return result;
}

void expect(const Matrix &m, const Flat &values) {
  for (int i = 0; i < 4; ++i)
    assert(m[i / 2][i % 2] == values[i]);
}

Flat multiply(const Flat &a, const Flat &b) {
  return {a[0] * b[0] + a[1] * b[2], a[0] * b[1] + a[1] * b[3],
          a[2] * b[0] + a[3] * b[2], a[2] * b[1] + a[3] * b[3]};
}

Flat decode(int code) {
  Flat values{};
  for (auto &value : values) {
    value = code % 3 - 1;
    code /= 3;
  }
  return values;
}

int main() {
  expect(Matrix{}, {0, 0, 0, 0});
  expect(Matrix::O(), {0, 0, 0, 0});
  expect(Matrix::I(), {1, 0, 0, 1});
  for (int i = 0; i < 81; ++i) {
    const Flat av = decode(i);
    const Matrix a = matrix(av);
    expect(+a, av);
    Flat neg{}, twice{}, zero{};
    for (int k = 0; k < 4; ++k) {
      neg[k] = -av[k];
      twice[k] = 2 * av[k];
    }
    expect(-a, neg);
    Matrix alias = a;
    assert(&(alias += alias) == &alias);
    expect(alias, twice);
    alias = a;
    assert(&(alias -= alias) == &alias);
    expect(alias, zero);
    alias = a;
    assert(&(alias *= alias) == &alias);
    expect(alias, multiply(av, av));
    Flat power{1, 0, 0, 1};
    for (int exponent = 0; exponent <= 8; ++exponent) {
      expect(a.pow(exponent), power);
      power = multiply(power, av); // repeated multiplication reference
    }
    for (int j = 0; j < 81; ++j) {
      const Flat bv = decode(j);
      const Matrix b = matrix(bv);
      assert((a == b) == (av == bv));
      assert((a != b) == (av != bv));
      Flat sum{}, difference{};
      for (int k = 0; k < 4; ++k) {
        sum[k] = av[k] + bv[k];
        difference[k] = av[k] - bv[k];
      }
      expect(a + b, sum);
      expect(a - b, difference);
      expect(a * b, multiply(av, bv));
      Matrix changed = a;
      assert(&(changed += b) == &changed);
      expect(changed, sum);
      changed = a;
      assert(&(changed -= b) == &changed);
      expect(changed, difference);
      changed = a;
      assert(&(changed *= b) == &changed);
      expect(changed, multiply(av, bv));
    }
  }
  cp::SquareMatrix<long long, 1> large{};
  large[0][0] = LLONG_MAX;
  assert(large.pow(1)[0][0] == LLONG_MAX); // no discarded, overflowing square
  large[0][0] = LLONG_MIN;
  assert(large.pow(0)[0][0] == 1);
  assert(large.pow(1)[0][0] == LLONG_MIN);
  cp::SquareMatrix<long long, 1> minus_one{};
  minus_one[0][0] = -1;
  assert(minus_one.pow(LLONG_MAX)[0][0] == -1);
  assert(minus_one.pow(LLONG_MAX - 1)[0][0] == 1);
  cp::SquareMatrix<long long, 3> nilpotent{};
  nilpotent[0][1] = 1;
  nilpotent[1][2] = 1;
  assert(nilpotent.pow(0) == decltype(nilpotent)::I());
  assert(nilpotent.pow(1) == nilpotent);
  assert(nilpotent.pow(2)[0][2] == 1);
  assert(nilpotent.pow(3) == decltype(nilpotent)::O());
  assert(cp::element_count(vector<int>{1, 1, 2}).size() == 2);
}

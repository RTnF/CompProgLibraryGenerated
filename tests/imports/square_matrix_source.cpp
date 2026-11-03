#include "experiments/library/cpp/template/small_template.hpp"
#include "experiments/verification/array/element_count.hpp"
#include "experiments/library/cpp/number/square_matrix.hpp"

using Matrix = SquareMatrix<long long, 2>;
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

#include <type_traits>
#include <utility>
using SignatureMatrix = SquareMatrix<long long, 2>;
static_assert(std::is_same_v<decltype(&SignatureMatrix::pow), SignatureMatrix (SignatureMatrix::*)(ll) const>);
static_assert(std::is_same_v<decltype(std::declval<SignatureMatrix &>()[0]), long long (&)[2]>);
static_assert(std::is_same_v<decltype(std::declval<const SignatureMatrix &>()[0]), const long long (&)[2]>);
static_assert(std::is_same_v<decltype(SignatureMatrix::mat), long long [2][2]>);
static_assert(std::is_aggregate_v<SignatureMatrix>);
static_assert(std::is_trivial_v<SignatureMatrix>);
static_assert(std::is_standard_layout_v<SignatureMatrix>);
struct Counted {
  long long value;
  static inline int products = 0;
  Counted(long long value = 0) : value(value) {}
  Counted &operator+=(Counted other) { value = (value + other.value) % 17; return *this; }
  friend Counted operator*(Counted a, Counted b) {
    ++products;
    return Counted(a.value * b.value % 17);
  }
};
void check_product_counts() {
  for (ll exponent : {0LL, 1LL, 2LL, 3LL, 4LL, 8LL, 31LL, LLONG_MAX}) {
    SquareMatrix<Counted, 1> a{{{3}}};
    Counted::products = 0;
    const auto result = a.pow(exponent);
    int bit_products = 0, squares = 0;
    long long reference = 1, base = 3;
    for (ll remaining = exponent; remaining != 0; remaining >>= 1) {
      if (remaining & 1) { reference = reference * base % 17; ++bit_products; }
      if ((remaining >> 1) != 0) { base = base * base % 17; ++squares; }
    }
    assert(result[0][0].value == reference);
    assert(Counted::products == bit_products + squares);
  }
}


struct EqualityOnly {
  int value;
  friend bool operator==(EqualityOnly a, EqualityOnly b) { return a.value == b.value; }
};
int main() {
  check_product_counts();
  SquareMatrix<EqualityOnly,1> left{},right{};
  left[0][0].value=7;
  right[0][0].value=7;
  assert(left == right && !(left != right));
  right[0][0].value=8;
  assert(left != right && !(left == right));

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
  SquareMatrix<long long, 1> large{};
  large[0][0] = LLONG_MAX;
  assert(large.pow(1)[0][0] == LLONG_MAX); // no discarded, overflowing square
  large[0][0] = LLONG_MIN;
  assert(large.pow(0)[0][0] == 1);
  assert(large.pow(1)[0][0] == LLONG_MIN);
  SquareMatrix<long long, 1> minus_one{};
  minus_one[0][0] = -1;
  assert(minus_one.pow(LLONG_MAX)[0][0] == -1);
  assert(minus_one.pow(LLONG_MAX - 1)[0][0] == 1);
  SquareMatrix<long long, 3> nilpotent{};
  nilpotent[0][1] = 1;
  nilpotent[1][2] = 1;
  assert(nilpotent.pow(0) == decltype(nilpotent)::I());
  assert(nilpotent.pow(1) == nilpotent);
  assert(nilpotent.pow(2)[0][2] == 1);
  assert(nilpotent.pow(3) == decltype(nilpotent)::O());
  assert(cp::element_count(vector<int>{1, 1, 2}).size() == 2);
}

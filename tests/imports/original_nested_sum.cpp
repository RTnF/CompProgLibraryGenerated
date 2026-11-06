int main() {
  using S = RangeAddRangeSum<long long>::RangeSum;
  S zero, a(4, 2), b(7, 3);
  auto e = S::e();
  auto sum = op(a, b);
  return zero.x == 0 && zero.size == 0 && e.x == 0 && e.size == 0 &&
         sum.x == 11 && sum.size == 5 ? 0 : 1;
}

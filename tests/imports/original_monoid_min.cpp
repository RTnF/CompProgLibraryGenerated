// Concrete witness and native regression for the unchanged original class.
int main() {
  using M = MonoidMin<long long>;
  M identity, a(4), b(3);
  if (identity.x != std::numeric_limits<long long>::max() || M::e().x != identity.x) return 1;
  if (op(a,b).x != 3 || op(a,a).x != 4) return 2;
  if (op(a,3LL).x != 3 || op(3LL,a).x != 3) return 3;
  long long values[] = {std::numeric_limits<long long>::min(),-1,0,std::numeric_limits<long long>::max()};
  for (auto x : values) for (auto y : values)
    if (op(M(x),M(y)).x != (x < y ? x : y)) return 4;
  std::cout << "ok\n";
}

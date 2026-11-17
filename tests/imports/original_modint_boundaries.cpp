#include "template/small_template.hpp"
#include "modint/modint.hpp"
#include <iostream>
#include <string>
template<std::uint32_t M> int run() {
  std::string op;
  while (std::cin >> op) {
    if (op == "signed128" || op == "set128" || op == "unsigned128" || op == "qualified128") {
      const __int128 half = (__int128)1 << 126;
      const __int128 minimum = -half - half;
      const __int128 maximum = half - 1 + half;
      if (op == "unsigned128") {
        const unsigned __int128 values[] = {0, 1, (unsigned __int128)1 << 127, ~(unsigned __int128)0};
        for (auto value : values) std::cout << ModInt<M>(value).get() << '\n';
      } else if (op == "qualified128") {
        const __int128 value = -1;
        ModInt<M> a;
        a.template set<const __int128>(value);
        std::cout << a.get() << '\n';
        a.template set<volatile __int128>(value);
        std::cout << a.get() << '\n';
      } else {
        const __int128 values[] = {minimum, minimum + 1, -(__int128)M, -1, 0, 1, maximum};
        for (auto value : values) {
          ModInt<M> a;
          if (op == "signed128") a = ModInt<M>(value); else a.set(value);
          std::cout << a.get() << '\n';
        }
      }
    } else if (op == "signed" || op == "set") {
      long long x; std::cin >> x;
      ModInt<M> a;
      if (op == "signed") a = ModInt<M>(x); else a.set(x);
      std::cout << a.get() << '\n';
    } else if (op == "unsigned") {
      unsigned long long x; std::cin >> x;
      std::cout << ModInt<M>(x).get() << '\n';
    } else if (op == "pow") {
      unsigned long long a; long long n; std::cin >> a >> n;
      std::cout << ModInt<M>(a).pow(n).get() << '\n';
    } else {
      unsigned long long x, y; std::cin >> x >> y;
      ModInt<M> a(x), b(y);
      if (op == "add") a += b;
      else if (op == "sub") a -= b;
      else if (op == "mul") a *= b;
      else if (op == "alias_add") a += a;
      else if (op == "alias_sub") a -= a;
      else return 3;
      std::cout << a.get() << '\n';
    }
  }
  return 0;
}
int main(int argc, char** argv) {
  if (argc != 2) return 4;
  const auto m = std::stoull(argv[1]);
  switch (m) {
    case 2: return run<2>();
    case 7: return run<7>();
    case 998244353: return run<998244353>();
    case 2147483647: return run<2147483647>();
    case 4294967291: return run<4294967291>();
    default: return 5;
  }
}

#include <iostream>
int main() {
    MonoidMul<long long> identity, a(4), b(3);
    auto product = op(a, b);
    a.x = 9;
    std::cout << identity.x << ' ' << product.x << ' ' << a.x << '\n';
}

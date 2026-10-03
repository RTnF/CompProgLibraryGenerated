#define PROBLEM "https://yukicoder.me/problems/no/3030"
#include "NumberTheory/IsPrime.hpp"

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);
    int n;
    cin >> n;
    while(n--) {
        ull x;
        cin >> x;
        cout << x << ' ' << isPrime(x) << '\n';
    }
}
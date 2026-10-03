#define PROBLEM "https://judge.yosupo.jp/problem/many_aplusb"
#include "Template/SmallTemplate.hpp"

// tie, sync, endlの不使用のみ
int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);
    int t;
    cin >> t;
    while(t--) {
        ll a, b;
        cin >> a >> b;
        cout << a + b << '\n';
    }
}
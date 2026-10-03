#define PROBLEM "https://judge.yosupo.jp/problem/sort_points_by_argument"
#include "Template/SmallTemplate.hpp"
#include "Geometry/Point.hpp"

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);
    int n;
    cin >> n;
    vector<Point<ll>> ps;
    ps.reserve(n);
    while(n--) {
        ll x, y;
        cin >> x >> y;
        ps.emplace_back(x, y);
    }
    sort(ps.begin(), ps.end());
    for(auto &&p: ps) {
        cout << p << '\n';
    }
}
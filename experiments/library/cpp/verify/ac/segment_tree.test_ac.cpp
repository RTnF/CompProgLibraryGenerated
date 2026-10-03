#define PROBLEM "https://atcoder.jp/contests/practice2/tasks/practice2_j"
#include "segment_tree/segment_tree.hpp"
#include "algebraic_structure/monoid.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);
  int N, Q;
  cin >> N >> Q;
  vector<MonoidMax<>> A(N);
  for (int i = 0; i < N; i++) {
    ll a;
    cin >> a;
    A[i] = MonoidMax(a);
  }
  SegmentTree<MonoidMax<>> sg(A);
  while (Q--) {
    int T;
    cin >> T;
    ll X, V;
    int L, R;
    switch (T) {
    case 1:
      cin >> X >> V;
      sg.set(X - 1, MonoidMax(V));
      break;
    case 2:
      cin >> L >> R;
      cout << sg.product(L - 1, R).x << '\n';
      break;
    case 3:
      cin >> X >> V;
      cout << sg.search_prod_right(
                  X - 1, [&](MonoidMax<ll> m) -> bool { return m.x < V; }) +
                  1
           << '\n';
      break;
    }
  }
}
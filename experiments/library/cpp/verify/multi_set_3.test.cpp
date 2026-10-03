#define PROBLEM "https://judge.yosupo.jp/problem/double_ended_priority_queue"
#include "set/multiset.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);

  TreeMultiSet<int> ms;
  int n, q;
  cin >> n >> q;
  for (int i = 0; i < n; i++) {
    int s;
    cin >> s;
    ms.add(s);
  }
  while (q--) {
    int c;
    cin >> c;
    switch (c) {
    case 0:
      int x;
      cin >> x;
      ms.add(x);
      break;
    case 1: {
      int m = ms.min();
      cout << m << '\n';
      ms.remove(m);
      break;
    }
    case 2: {
      int m = ms.max();
      cout << m << '\n';
      ms.remove(m);
      break;
    }
    }
  }
}
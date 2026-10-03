#define PROBLEM "https://judge.yosupo.jp/problem/predecessor_problem"
#include "set/multiset.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);

  TreeMultiSet<int> ms;
  int n, q;
  cin >> n >> q;
  string s;
  cin >> s;
  for (int i = 0; i < (int)s.size(); i++) {
    if (s[i] == '1') {
      ms.add(i);
    }
  }
  while (q--) {
    int c, k;
    cin >> c >> k;
    switch (c) {
    case 0:
      if (!ms.count(k)) {
        ms.add(k);
      }
      break;
    case 1:
      if (ms.count(k)) {
        ms.remove(k);
      }
      break;
    case 2:
      cout << ms.count(k) << '\n';
      break;
    case 3: {
      auto m = ms.find_upper(k);
      cout << (m ? *m : -1) << '\n';
      break;
    }
    case 4: {
      auto m = ms.find_lower(k);
      cout << (m ? *m : -1) << '\n';
      break;
    }
    }
  }
}
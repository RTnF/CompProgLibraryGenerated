#define PROBLEM                                                                \
  "https://onlinejudge.u-aizu.ac.jp/courses/lesson/8/ITP2/all/ITP2_7_D"
#include "set/multiset.hpp"

int main() {
  cin.tie(0);
  ios::sync_with_stdio(false);

  TreeMultiSet ms;
  int q;
  cin >> q;
  while (q--) {
    int type;
    cin >> type;
    int x, l, r;
    switch (type) {
    case 0: // insert
      cin >> x;
      ms.add(x);
      cout << ms.size() << "\n";
      break;
    case 1: // find
      cin >> x;
      cout << ms.count(x) << "\n";
      break;
    case 2: // delete
      cin >> x;
      ms.remove_all(x);
      break;
    case 3: // dump
      cin >> l >> r;
      ms.aoj_dump(l, r);
      break;
    }
    if (ms.size() < 3000) {
      ms.verify();
    }
  }
}
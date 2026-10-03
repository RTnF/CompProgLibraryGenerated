#define PROBLEM "https://judge.yosupo.jp/problem/many_aplusb"
#include "template/small_template.hpp"

// https://qiita.com/nojima/items/57b9d39d7d73362ac883
ll read_ll() {
  ll ret = 0, sgn = 1;
  int ch = getchar_unlocked();
  while (isspace(ch)) {
    ch = getchar_unlocked();
  }
  if (ch == '-') {
    sgn = -1;
    ch = getchar_unlocked();
  }
  for (; isdigit(ch); ch = getchar_unlocked())
    ret = (ret * 10) + (ch - '0');
  ungetc(ch, stdin);
  return sgn * ret;
}

// https://qiita.com/nojima/items/57b9d39d7d73362ac883
int read_int() {
  int ret = 0, sgn = 1;
  int ch = getchar_unlocked();
  while (isspace(ch)) {
    ch = getchar_unlocked();
  }
  if (ch == '-') {
    sgn = -1;
    ch = getchar_unlocked();
  }
  for (; isdigit(ch); ch = getchar_unlocked())
    ret = (ret * 10) + (ch - '0');
  ungetc(ch, stdin);
  return sgn * ret;
}

int main() {
  // cin.tie(0);
  // ios::sync_with_stdio(false);

  int T = read_int();

  while (T--) {
    ll A = read_ll();
    ll B = read_ll();
    cout << A + B << '\n';
  }
}
#include <bits/stdc++.h>
using namespace std;
using ll = int64_t;
using vi = vector<int>;
using vvi = vector<vi>;
using vvvi = vector<vvi>;
using vd = vector<double>;
using vvd = vector<vd>;
using vvvd = vector<vvd>;
using pii = pair<int, int>;
using vpii = vector<pii>;
using vs = vector<string>;
template <typename T> using pqrev = priority_queue<T, vector<T>, greater<T>>;
#define rep(i, n) for (int i = 0, i##_end = (n); i < i##_end; i++)
#define repb(i, n) for (int i = (n) - 1; i >= 0; i--)
#define repr(i, a, b) for (int i = (a), i##_end = (b); i < i##_end; i++)
#define reprb(i, a, b) for (int i = (b) - 1, i##_end = (a); i >= i##_end; i--)
#define ALL(a) (a).begin(), (a).end()
#define SZ(x) ((int)(x).size())
constexpr int INF = 1e9;
constexpr double EPS = 1e-12;
template <typename S, typename T> inline bool chmax(S &a, const T &b) {
  if (a < b) {
    a = b;
    return 1;
  }
  return 0;
}
template <typename S, typename T> inline bool chmin(S &a, const T &b) {
  if (b < a) {
    a = b;
    return 1;
  }
  return 0;
}
template <typename T> T max(const vector<T> &x) { return *max_element(ALL(x)); }
template <typename T> T min(const vector<T> &x) { return *min_element(ALL(x)); }
template <typename T> T sum(const vector<T> &x) {
  return accumulate(ALL(x), T(0));
}
namespace in {
template <typename T> bool print(const T &a) {
  cout << a;
  return true;
}
template <typename T> bool print(const vector<T> &vec) {
  for (auto &a : vec) {
    cout << a;
    if (&a != &vec.back())
      cout << ' ';
  }
  return false;
}
template <typename T> bool print(const vector<vector<T>> &vv) {
  for (auto &v : vv) {
    for (auto &a : v) {
      cout << a;
      if (&a != &v.back())
        cout << ' ';
    }
    if (&v != &vv.back())
      cout << '\n';
  }
  return false;
}
}; // namespace in
void print() { cout << '\n'; }
template <typename Head, typename... Tail>
void print(Head &&head, Tail &&...tail) {
  bool f = in::print(head);
  if (sizeof...(tail) != 0) {
    cout << (f ? ' ' : '\n');
  }
  print(std::forward<Tail>(tail)...);
}

struct Timer {
  chrono::high_resolution_clock::time_point start, now;
  chrono::nanoseconds nano;
  ll threshold = 1930000000; // 1.93 s
  Timer() { reset(); }
  void reset() { start = chrono::high_resolution_clock::now(); }
  int get_ns() {
    now = chrono::high_resolution_clock::now();
    nano = chrono::duration_cast<chrono::nanoseconds>(now - start);
    return nano.count();
  }
  int get_us() { return get_ns() / 1000; }
  int get_ms() { return get_ns() / 1000000; }
  int get_s() { return get_ns() / 1000000000; }
  int getRemain_ns() { return threshold - get_ns(); }
  int getRemain_us() { return getRemain_ns() / 1000; }
  int getRemain_ms() { return getRemain_ns() / 1000000; }
  int getRemain_s() { return getRemain_ns() / 1000000000; }
  int getLimit_ms() { return threshold / 1000000; }
  bool intime() { return get_ns() <= threshold; }
} timer;

// https://ja.wikipedia.org/wiki/Xorshift
class XorShift64 {
  uint64_t s;

public:
  XorShift64(uint64_t s_) : s(s_) {}
  // [0, 2**64)
  uint64_t get() {
    uint64_t x = s;
    x ^= x << 7;
    return s = x ^ (x >> 9);
  }
  // [min, max)
  int getInt(int mi, int ma) { return mi + get() % (ma - mi); }
  // [min, max)
  ll getLL(ll mi, ll ma) { return mi + get() % (ma - mi); }
  // [0, 1)
  double getDouble() { return get() / pow(2.0, 64); }
  // [min, max)
  double getDouble(double mi, double ma) {
    return mi + getDouble() * (ma - mi);
  }
  // normal
  double getNormal() {
    double x = getDouble(), y = getDouble();
    return sqrt(-2.0 * log(x)) * cos(2.0 * M_PI * y);
  }
} rnd(720759665484242684ull);

void solve() {}

int main() { solve(); }
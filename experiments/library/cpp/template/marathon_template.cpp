#include <bits/stdc++.h>
using namespace std;
using ll = int64_t;
using ull = uint64_t;
using ld = long double;
using vi = vector<int>;
using vvi = vector<vi>;
using vvvi = vector<vvi>;
using vll = vector<ll>;
using vvll = vector<vll>;
using vvvll = vector<vvll>;
using vld = vector<ld>;
using vvld = vector<vld>;
using vvvld = vector<vvld>;
using vs = vector<string>;
using pii = pair<int, int>;
using pll = pair<ll, ll>;
using pdd = pair<double, double>;
using pld = pair<ld, ld>;
using vpii = vector<pii>;
using vp = vector<pll>;
using vpdd = vector<pdd>;
using vpld = vector<pld>;
template <class T> using pqrev = priority_queue<T, vector<T>, greater<T>>;
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
template <class T> T max(const vector<T> &x) { return *max_element(ALL(x)); }
template <class T> T min(const vector<T> &x) { return *min_element(ALL(x)); }
template <class T> T sum(const vector<T> &x) {
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
  ll get_ns() {
    now = chrono::high_resolution_clock::now();
    nano = chrono::duration_cast<chrono::nanoseconds>(now - start);
    return nano.count();
  }
  int get_us() { return get_ns() / 1000; }
  int get_ms() { return get_ns() / 1000000; }
  int get_s() { return get_ns() / 1000000000; }
  ll get_remain_ns() { return threshold - get_ns(); }
  int get_remain_us() { return get_remain_ns() / 1000; }
  int get_remain_ms() { return get_remain_ns() / 1000000; }
  int get_remain_s() { return get_remain_ns() / 1000000000; }
  int get_limit_ms() { return threshold / 1000000; }
  bool intime() { return get_ns() <= threshold; }
} timer;

// https://ja.wikipedia.org/wiki/Xorshift
class Xor64 {
  ull s;

public:
  Xor64(ull s_) : s(s_) {}
  // [0, 2**64)
  ull get() {
    ull x = s;
    x ^= x << 7;
    return s = x ^ (x >> 9);
  }
  // [min, max)
  int get_int(int mi, int ma) { return mi + get() % (ma - mi); }
  // [min, max)
  ll get_ll(ll mi, ll ma) { return mi + get() % (ma - mi); }
  // [0, 1)
  double get_double() { return get() / pow(2.0, 64); }
  // [min, max)
  double get_double(double mi, double ma) {
    return mi + get_double() * (ma - mi);
  }
  // normal
  double get_normal() {
    double x = get_double(), y = get_double();
    return sqrt(-2.0 * log(x)) * cos(2.0 * M_PI * y);
  }
} rnd(720759665484242684ull);

void solve() {}

int main() { solve(); }
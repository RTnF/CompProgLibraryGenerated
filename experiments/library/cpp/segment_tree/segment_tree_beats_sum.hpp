#include "template/small_template.hpp"

// https://tjkendev.github.io/procon-library/cpp/range_query/segment_tree_beats_2.html
// sumがあるのでINFは積めない
class SegmentTreeBeatsSum {
  int n, n0;
  vector<ll> max_v, smax_v, max_c;
  vector<ll> min_v, smin_v, min_c;
  vector<ll> sum;
  vector<ll> len, ladd, lval;

  void update_node_max(int k, ll x) {
    sum[k] += (x - max_v[k]) * max_c[k];
    if (max_v[k] == min_v[k]) {
      max_v[k] = min_v[k] = x;
    } else if (max_v[k] == smin_v[k]) {
      max_v[k] = smin_v[k] = x;
    } else {
      max_v[k] = x;
    }
    if (lval[k] != INF && x < lval[k]) {
      lval[k] = x;
    }
  }

  void update_node_min(int k, ll x) {
    sum[k] += (x - min_v[k]) * min_c[k];
    if (max_v[k] == min_v[k]) {
      max_v[k] = min_v[k] = x;
    } else if (smax_v[k] == min_v[k]) {
      min_v[k] = smax_v[k] = x;
    } else {
      min_v[k] = x;
    }
    if (lval[k] != INF && lval[k] < x) {
      lval[k] = x;
    }
  }

  void push(int k) {
    if (n0 - 1 <= k) {
      return;
    }
    if (lval[k] != INF) {
      update_all(2 * k + 1, lval[k]);
      update_all(2 * k + 2, lval[k]);
      lval[k] = INF;
      return;
    }
    if (ladd[k] != 0) {
      add_all(2 * k + 1, ladd[k]);
      add_all(2 * k + 2, ladd[k]);
      ladd[k] = 0;
    }
    if (max_v[k] < max_v[2 * k + 1]) {
      update_node_max(2 * k + 1, max_v[k]);
    }
    if (min_v[2 * k + 1] < min_v[k]) {
      update_node_min(2 * k + 1, min_v[k]);
    }
    if (max_v[k] < max_v[2 * k + 2]) {
      update_node_max(2 * k + 2, max_v[k]);
    }
    if (min_v[2 * k + 2] < min_v[k]) {
      update_node_min(2 * k + 2, min_v[k]);
    }
  }

  void update(int k) {
    sum[k] = sum[2 * k + 1] + sum[2 * k + 2];
    if (max_v[2 * k + 1] < max_v[2 * k + 2]) {
      max_v[k] = max_v[2 * k + 2];
      max_c[k] = max_c[2 * k + 2];
      smax_v[k] = max(max_v[2 * k + 1], smax_v[2 * k + 2]);
    } else if (max_v[2 * k + 1] > max_v[2 * k + 2]) {
      max_v[k] = max_v[2 * k + 1];
      max_c[k] = max_c[2 * k + 1];
      smax_v[k] = max(smax_v[2 * k + 1], max_v[2 * k + 2]);
    } else {
      max_v[k] = max_v[2 * k + 1];
      max_c[k] = max_c[2 * k + 1] + max_c[2 * k + 2];
      smax_v[k] = max(smax_v[2 * k + 1], smax_v[2 * k + 2]);
    }
    if (min_v[2 * k + 1] < min_v[2 * k + 2]) {
      min_v[k] = min_v[2 * k + 1];
      min_c[k] = min_c[2 * k + 1];
      smin_v[k] = min(smin_v[2 * k + 1], min_v[2 * k + 2]);
    } else if (min_v[2 * k + 1] > min_v[2 * k + 2]) {
      min_v[k] = min_v[2 * k + 2];
      min_c[k] = min_c[2 * k + 2];
      smin_v[k] = min(min_v[2 * k + 1], smin_v[2 * k + 2]);
    } else {
      min_v[k] = min_v[2 * k + 1];
      min_c[k] = min_c[2 * k + 1] + min_c[2 * k + 2];
      smin_v[k] = min(smin_v[2 * k + 1], smin_v[2 * k + 2]);
    }
  }

  void _chmin(ll x, int a, int b, int k, int l, int r) {
    if (b <= l || r <= a || max_v[k] <= x) {
      return;
    }
    if (a <= l && r <= b && smax_v[k] < x) {
      update_node_max(k, x);
      return;
    }
    push(k);
    _chmin(x, a, b, 2 * k + 1, l, (l + r) / 2);
    _chmin(x, a, b, 2 * k + 2, (l + r) / 2, r);
    update(k);
  }

  void _chmax(ll x, int a, int b, int k, int l, int r) {
    if (b <= l || r <= a || x <= min_v[k]) {
      return;
    }
    if (a <= l && r <= b && x < smin_v[k]) {
      update_node_min(k, x);
      return;
    }
    push(k);
    _chmax(x, a, b, 2 * k + 1, l, (l + r) / 2);
    _chmax(x, a, b, 2 * k + 2, (l + r) / 2, r);
    update(k);
  }

  void add_all(int k, ll x) {
    max_v[k] += x;
    if (smax_v[k] != -INF) {
      smax_v[k] += x;
    }
    min_v[k] += x;
    if (smin_v[k] != INF) {
      smin_v[k] += x;
    }

    sum[k] += len[k] * x;
    (lval[k] == INF ? ladd[k] : lval[k]) += x;
  }

  void update_all(int k, ll x) {
    max_v[k] = x;
    smax_v[k] = -INF;
    min_v[k] = x;
    smin_v[k] = INF;
    max_c[k] = min_c[k] = len[k];

    sum[k] = x * len[k];
    lval[k] = x;
    ladd[k] = 0;
  }

  void _add_val(ll x, int a, int b, int k, int l, int r) {
    if (b <= l || r <= a) {
      return;
    }
    if (a <= l && r <= b) {
      add_all(k, x);
      return;
    }

    push(k);
    _add_val(x, a, b, 2 * k + 1, l, (l + r) / 2);
    _add_val(x, a, b, 2 * k + 2, (l + r) / 2, r);
    update(k);
  }

  void _update_val(ll x, int a, int b, int k, int l, int r) {
    if (b <= l || r <= a) {
      return;
    }
    if (a <= l && r <= b) {
      update_all(k, x);
      return;
    }
    push(k);
    _update_val(x, a, b, 2 * k + 1, l, (l + r) / 2);
    _update_val(x, a, b, 2 * k + 2, (l + r) / 2, r);
    update(k);
  }

  ll _calc_max(int a, int b, int k, int l, int r) {
    if (b <= l || r <= a) {
      return -INF;
    }
    if (a <= l && r <= b) {
      return max_v[k];
    }
    push(k);
    ll lv = _calc_max(a, b, 2 * k + 1, l, (l + r) / 2);
    ll rv = _calc_max(a, b, 2 * k + 2, (l + r) / 2, r);
    return max(lv, rv);
  }

  ll _calc_min(int a, int b, int k, int l, int r) {
    if (b <= l || r <= a) {
      return INF;
    }
    if (a <= l && r <= b) {
      return min_v[k];
    }
    push(k);
    ll lv = _calc_min(a, b, 2 * k + 1, l, (l + r) / 2);
    ll rv = _calc_min(a, b, 2 * k + 2, (l + r) / 2, r);
    return min(lv, rv);
  }

  ll _calc_sum(int a, int b, int k, int l, int r) {
    if (b <= l || r <= a) {
      return 0;
    }
    if (a <= l && r <= b) {
      return sum[k];
    }
    push(k);
    ll lv = _calc_sum(a, b, 2 * k + 1, l, (l + r) / 2);
    ll rv = _calc_sum(a, b, 2 * k + 2, (l + r) / 2, r);
    return lv + rv;
  }

public:
  SegmentTreeBeatsSum(vector<ll> a) : n(a.size()) {
    max_v = smax_v = max_c = min_v = smin_v = min_c = sum = len = ladd = lval =
        vector<ll>(4 * n);
    n0 = 1;
    while (n0 < n)
      n0 <<= 1;

    for (int i = 0; i < 2 * n0; ++i)
      ladd[i] = 0, lval[i] = INF;
    len[0] = n0;
    for (int i = 0; i < n0 - 1; ++i)
      len[2 * i + 1] = len[2 * i + 2] = (len[i] >> 1);

    for (int i = 0; i < n; ++i) {
      max_v[n0 - 1 + i] = min_v[n0 - 1 + i] = sum[n0 - 1 + i] = a[i];
      smax_v[n0 - 1 + i] = -INF;
      smin_v[n0 - 1 + i] = INF;
      max_c[n0 - 1 + i] = min_c[n0 - 1 + i] = 1;
    }

    for (int i = n; i < n0; ++i) {
      max_v[n0 - 1 + i] = smax_v[n0 - 1 + i] = -INF;
      min_v[n0 - 1 + i] = smin_v[n0 - 1 + i] = INF;
      max_c[n0 - 1 + i] = min_c[n0 - 1 + i] = 0;
    }
    for (int i = n0 - 2; i >= 0; i--) {
      update(i);
    }
  }

  void chmin(int a, int b, ll x) { _chmin(x, a, b, 0, 0, n0); }
  void chmax(int a, int b, ll x) { _chmax(x, a, b, 0, 0, n0); }
  void add_val(int a, int b, ll x) { _add_val(x, a, b, 0, 0, n0); }
  void update_val(int a, int b, ll x) { _update_val(x, a, b, 0, 0, n0); }
  ll calc_max(int a, int b) { return _calc_max(a, b, 0, 0, n0); }
  ll calc_min(int a, int b) { return _calc_min(a, b, 0, 0, n0); }
  ll calc_sum(int a, int b) { return _calc_sum(a, b, 0, 0, n0); }
};

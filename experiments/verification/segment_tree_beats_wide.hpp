#pragma once
// Experimental range-preserving constructor arithmetic; public proof/model switch is pending.
#include <vector>
#include <algorithm>
namespace cp {

// https://tjkendev.github.io/procon-library/cpp/range_query/segment_tree_beats_2.html
// sumができない代わりにINFまで積める
class SegmentTreeBeats {
  std::vector<long long> max_v, smax_v, max_c;
  std::vector<long long> min_v, smin_v, min_c;
  std::vector<long long> len, ladd, lval;
  std::vector<int> lo, hi;
  std::vector<int> st_k, st_l, st_r, ent; // scratch: the explicit stack (depth <= 2 * 64; node arrays have 8n+8 entries so that the children of every node, also of a leaf, stay in range) and the entered nodes
  long long inf;
  int n;

  // The guarded node operations below do nothing when g != 1 (every condition carries g == 1 and the unconditional writes store back the old values).
  void update_node_max(int k, long long x, int g) {
    long long mx = max_v[k];
    long long mn = min_v[k];
    long long sn = smin_v[k];
    long long lv = lval[k];
    long long nmx = mx;
    long long nmn = mn;
    long long nsn = sn;
    long long nlv = lv;
    if (g == 1) {
      nmx = x;
    }
    if (g == 1 && mx == mn) {
      nmn = x;
    }
    if (g == 1 && mx != mn && mx == sn) {
      nsn = x;
    }
    if (g == 1 && lv != inf && x < lv) {
      nlv = x;
    }
    max_v[k] = nmx;
    min_v[k] = nmn;
    smin_v[k] = nsn;
    lval[k] = nlv;
  }

  void update_node_min(int k, long long x, int g) {
    long long mx = max_v[k];
    long long sx = smax_v[k];
    long long mn = min_v[k];
    long long lv = lval[k];
    long long nmn = mn;
    long long nmx = mx;
    long long nsx = sx;
    long long nlv = lv;
    if (g == 1) {
      nmn = x;
    }
    if (g == 1 && mx == mn) {
      nmx = x;
    }
    if (g == 1 && mx != mn && sx == mn) {
      nsx = x;
    }
    if (g == 1 && lv != inf && lv < x) {
      nlv = x;
    }
    min_v[k] = nmn;
    max_v[k] = nmx;
    smax_v[k] = nsx;
    lval[k] = nlv;
  }

  void push(int k, int g) {
    long long lv = lval[k];
    long long la = ladd[k];
    long long mx = max_v[k];
    long long mn = min_v[k];
    int s = 0;
    if (g == 1 && lv != inf) {
      s = 1;
    }
    long long a = 0;
    if (g == 1 && s == 0) {
      a = la;
    }
    int act = 0;
    if (g == 1 && s == 0) {
      act = 1;
    }
    int c1 = 2 * k + 1;
    int c2 = 2 * k + 2;
    long long m0_c1 = max_v[c1];
    long long sm0_c1 = smax_v[c1];
    long long mc0_c1 = max_c[c1];
    long long n0_c1 = min_v[c1];
    long long sn0_c1 = smin_v[c1];
    long long nc0_c1 = min_c[c1];
    long long la0_c1 = ladd[c1];
    long long lv0_c1 = lval[c1];
    long long ln_c1 = len[c1];
    long long m0_c2 = max_v[c2];
    long long sm0_c2 = smax_v[c2];
    long long mc0_c2 = max_c[c2];
    long long n0_c2 = min_v[c2];
    long long sn0_c2 = smin_v[c2];
    long long nc0_c2 = min_c[c2];
    long long la0_c2 = ladd[c2];
    long long lv0_c2 = lval[c2];
    long long ln_c2 = len[c2];
    long long m1_c1 = m0_c1;
    if (s == 1) {
      m1_c1 = lv;
    }
    long long sm1_c1 = sm0_c1;
    if (s == 1) {
      sm1_c1 = -inf;
    }
    long long mc1_c1 = mc0_c1;
    if (s == 1) {
      mc1_c1 = ln_c1;
    }
    long long n1_c1 = n0_c1;
    if (s == 1) {
      n1_c1 = lv;
    }
    long long sn1_c1 = sn0_c1;
    if (s == 1) {
      sn1_c1 = inf;
    }
    long long nc1_c1 = nc0_c1;
    if (s == 1) {
      nc1_c1 = ln_c1;
    }
    long long la1_c1 = la0_c1;
    if (s == 1) {
      la1_c1 = 0;
    }
    long long lv1_c1 = lv0_c1;
    if (s == 1 && ln_c1 != 1) {
      lv1_c1 = lv;
    }
    long long m2_c1 = m1_c1 + a;
    long long sm2_c1 = sm1_c1;
    if (sm1_c1 != -inf) {
      sm2_c1 = sm1_c1 + a;
    }
    long long n2_c1 = n1_c1 + a;
    long long sn2_c1 = sn1_c1;
    if (sn1_c1 != inf) {
      sn2_c1 = sn1_c1 + a;
    }
    long long la2_c1 = la1_c1;
    if (lv1_c1 == inf && ln_c1 != 1) {
      la2_c1 = la1_c1 + a;
    }
    long long lv2_c1 = lv1_c1;
    if (lv1_c1 != inf) {
      lv2_c1 = lv1_c1 + a;
    }
    int g1_c1 = 0;
    if (act == 1 && mx < m2_c1) {
      g1_c1 = 1;
    }
    long long m3_c1 = m2_c1;
    if (g1_c1 == 1) {
      m3_c1 = mx;
    }
    long long n3_c1 = n2_c1;
    if (g1_c1 == 1 && m2_c1 == n2_c1) {
      n3_c1 = mx;
    }
    long long sn3_c1 = sn2_c1;
    if (g1_c1 == 1 && m2_c1 != n2_c1 && m2_c1 == sn2_c1) {
      sn3_c1 = mx;
    }
    long long lv3_c1 = lv2_c1;
    if (g1_c1 == 1 && lv2_c1 != inf && mx < lv2_c1) {
      lv3_c1 = mx;
    }
    int g2_c1 = 0;
    if (act == 1 && n3_c1 < mn) {
      g2_c1 = 1;
    }
    long long n4_c1 = n3_c1;
    if (g2_c1 == 1) {
      n4_c1 = mn;
    }
    long long m4_c1 = m3_c1;
    if (g2_c1 == 1 && m3_c1 == n3_c1) {
      m4_c1 = mn;
    }
    long long sm4_c1 = sm2_c1;
    if (g2_c1 == 1 && m3_c1 != n3_c1 && sm2_c1 == n3_c1) {
      sm4_c1 = mn;
    }
    long long lv4_c1 = lv3_c1;
    if (g2_c1 == 1 && lv3_c1 != inf && lv3_c1 < mn) {
      lv4_c1 = mn;
    }
    long long m1_c2 = m0_c2;
    if (s == 1) {
      m1_c2 = lv;
    }
    long long sm1_c2 = sm0_c2;
    if (s == 1) {
      sm1_c2 = -inf;
    }
    long long mc1_c2 = mc0_c2;
    if (s == 1) {
      mc1_c2 = ln_c2;
    }
    long long n1_c2 = n0_c2;
    if (s == 1) {
      n1_c2 = lv;
    }
    long long sn1_c2 = sn0_c2;
    if (s == 1) {
      sn1_c2 = inf;
    }
    long long nc1_c2 = nc0_c2;
    if (s == 1) {
      nc1_c2 = ln_c2;
    }
    long long la1_c2 = la0_c2;
    if (s == 1) {
      la1_c2 = 0;
    }
    long long lv1_c2 = lv0_c2;
    if (s == 1 && ln_c2 != 1) {
      lv1_c2 = lv;
    }
    long long m2_c2 = m1_c2 + a;
    long long sm2_c2 = sm1_c2;
    if (sm1_c2 != -inf) {
      sm2_c2 = sm1_c2 + a;
    }
    long long n2_c2 = n1_c2 + a;
    long long sn2_c2 = sn1_c2;
    if (sn1_c2 != inf) {
      sn2_c2 = sn1_c2 + a;
    }
    long long la2_c2 = la1_c2;
    if (lv1_c2 == inf && ln_c2 != 1) {
      la2_c2 = la1_c2 + a;
    }
    long long lv2_c2 = lv1_c2;
    if (lv1_c2 != inf) {
      lv2_c2 = lv1_c2 + a;
    }
    int g1_c2 = 0;
    if (act == 1 && mx < m2_c2) {
      g1_c2 = 1;
    }
    long long m3_c2 = m2_c2;
    if (g1_c2 == 1) {
      m3_c2 = mx;
    }
    long long n3_c2 = n2_c2;
    if (g1_c2 == 1 && m2_c2 == n2_c2) {
      n3_c2 = mx;
    }
    long long sn3_c2 = sn2_c2;
    if (g1_c2 == 1 && m2_c2 != n2_c2 && m2_c2 == sn2_c2) {
      sn3_c2 = mx;
    }
    long long lv3_c2 = lv2_c2;
    if (g1_c2 == 1 && lv2_c2 != inf && mx < lv2_c2) {
      lv3_c2 = mx;
    }
    int g2_c2 = 0;
    if (act == 1 && n3_c2 < mn) {
      g2_c2 = 1;
    }
    long long n4_c2 = n3_c2;
    if (g2_c2 == 1) {
      n4_c2 = mn;
    }
    long long m4_c2 = m3_c2;
    if (g2_c2 == 1 && m3_c2 == n3_c2) {
      m4_c2 = mn;
    }
    long long sm4_c2 = sm2_c2;
    if (g2_c2 == 1 && m3_c2 != n3_c2 && sm2_c2 == n3_c2) {
      sm4_c2 = mn;
    }
    long long lv4_c2 = lv3_c2;
    if (g2_c2 == 1 && lv3_c2 != inf && lv3_c2 < mn) {
      lv4_c2 = mn;
    }
    max_v[c1] = m4_c1;
    smax_v[c1] = sm4_c1;
    max_c[c1] = mc1_c1;
    min_v[c1] = n4_c1;
    smin_v[c1] = sn3_c1;
    min_c[c1] = nc1_c1;
    ladd[c1] = la2_c1;
    lval[c1] = lv4_c1;
    max_v[c2] = m4_c2;
    smax_v[c2] = sm4_c2;
    max_c[c2] = mc1_c2;
    min_v[c2] = n4_c2;
    smin_v[c2] = sn3_c2;
    min_c[c2] = nc1_c2;
    ladd[c2] = la2_c2;
    lval[c2] = lv4_c2;
    long long nlv = lv;
    long long nla = la;
    if (g == 1) {
      nlv = inf;
    }
    if (g == 1) {
      nla = 0;
    }
    lval[k] = nlv;
    ladd[k] = nla;
  }

  void update(int k) {
    int l = 2 * k + 1;
    int r = 2 * k + 2;
    long long lm = max_v[l];
    long long rm = max_v[r];
    long long lsm = smax_v[l];
    long long rsm = smax_v[r];
    long long lmc = max_c[l];
    long long rmc = max_c[r];
    int lt = 0;
    int gt = 0;
    int eq = 0;
    if (lm < rm) {
      lt = 1;
    }
    if (lm > rm) {
      gt = 1;
    }
    if (lm == rm) {
      eq = 1;
    }
    long long nm = lm;
    if (lt == 1) {
      nm = rm;
    }
    long long nmc = lmc;
    if (lt == 1) {
      nmc = rmc;
    }
    if (eq == 1) {
      nmc = lmc + rmc;
    }
    long long nsm = lsm;
    if (lt == 1) {
      nsm = lm;
    }
    if (gt == 1) {
      nsm = rm;
    }
    long long osm = rsm;
    if (gt == 1) {
      osm = lsm;
    }
    if (nsm < osm) {
      nsm = osm;
    }
    max_v[k] = nm;
    max_c[k] = nmc;
    smax_v[k] = nsm;
    long long ln = min_v[l];
    long long rn = min_v[r];
    long long lsn = smin_v[l];
    long long rsn = smin_v[r];
    long long lnc = min_c[l];
    long long rnc = min_c[r];
    int lt2 = 0;
    int gt2 = 0;
    int eq2 = 0;
    if (ln < rn) {
      lt2 = 1;
    }
    if (ln > rn) {
      gt2 = 1;
    }
    if (ln == rn) {
      eq2 = 1;
    }
    long long nn = ln;
    if (gt2 == 1) {
      nn = rn;
    }
    long long nnc = lnc;
    if (gt2 == 1) {
      nnc = rnc;
    }
    if (eq2 == 1) {
      nnc = lnc + rnc;
    }
    long long nsn = lsn;
    if (lt2 == 1) {
      nsn = rn;
    }
    if (gt2 == 1) {
      nsn = ln;
    }
    long long osn = rsn;
    if (lt2 == 1) {
      osn = lsn;
    }
    if (osn < nsn) {
      nsn = osn;
    }
    min_v[k] = nn;
    min_c[k] = nnc;
    smin_v[k] = nsn;
  }

  void add_all(int k, long long x) {
    max_v[k] += x;
    long long sm = smax_v[k];
    if (sm != -inf) {
      sm += x;
    }
    smax_v[k] = sm;
    min_v[k] += x;
    long long sn = smin_v[k];
    if (sn != inf) {
      sn += x;
    }
    smin_v[k] = sn;
    long long lv = lval[k];
    long long la = ladd[k];
    long long ln = len[k];
    if (lv == inf && ln != 1) {
      la += x;
    }
    if (lv != inf && ln != 1) {
      lv += x;
    }
    ladd[k] = la;
    lval[k] = lv;
  }

  void update_all(int k, long long x, int g) {
    long long mx = max_v[k];
    long long sx = smax_v[k];
    long long mn = min_v[k];
    long long sn = smin_v[k];
    long long mc = max_c[k];
    long long nc = min_c[k];
    long long lv = lval[k];
    long long la = ladd[k];
    long long ln = len[k];
    if (g == 1) {
      mx = x;
    }
    if (g == 1) {
      sx = -inf;
    }
    if (g == 1) {
      mn = x;
    }
    if (g == 1) {
      sn = inf;
    }
    if (g == 1) {
      mc = ln;
    }
    if (g == 1) {
      nc = ln;
    }
    if (g == 1 && ln != 1) {
      lv = x;
    }
    if (g == 1 && ln != 1) {
      la = 0;
    }
    max_v[k] = mx;
    smax_v[k] = sx;
    min_v[k] = mn;
    smin_v[k] = sn;
    max_c[k] = mc;
    min_c[k] = nc;
    lval[k] = lv;
    ladd[k] = la;
  }

public:
  // The tree has no padding: node k covers [lo[k], hi[k]) and splits at the midpoint; len[k] = hi[k] - lo[k]; children 2k+1, 2k+2.
  SegmentTreeBeats(const std::vector<long long> &a)
      : max_v(8ULL * a.size() + 8ULL, 0), smax_v(8ULL * a.size() + 8ULL, 0), max_c(8ULL * a.size() + 8ULL, 0),
        min_v(8ULL * a.size() + 8ULL, 0), smin_v(8ULL * a.size() + 8ULL, 0), min_c(8ULL * a.size() + 8ULL, 0),
        len(8ULL * a.size() + 8ULL, 0), ladd(8ULL * a.size() + 8ULL, 0), lval(8ULL * a.size() + 8ULL, 4000000000000000000LL),
        lo(8ULL * a.size() + 8ULL, 0), hi(8ULL * a.size() + 8ULL, 0), st_k(256, 0), st_l(256, 0), st_r(256, 0),
        ent(8ULL * a.size() + 8ULL, 0), inf(4000000000000000000LL), n((int)a.size()) {
    hi[0] = n;
    int ne = 0;
    int k = 0;
    while (k < 4 * n) {
      int lk = lo[k];
      int hk = hi[k];
      int used = 0;
      if (lk < hk) {
        used = 1;
      }
      long long ln = hk - lk;
      int leaf = 0;
      if (used == 1 && ln == 1) {
        leaf = 1;
      }
      int inner = 0;
      if (used == 1 && ln != 1) {
        inner = 1;
      }
      long long lv = len[k];
      if (used == 1) {
        lv = ln;
      }
      len[k] = lv;
      long long av = a[lk];
      long long t0 = max_v[k];
      long long t1 = min_v[k];
      long long t2 = smax_v[k];
      long long t3 = smin_v[k];
      long long t4 = max_c[k];
      long long t5 = min_c[k];
      if (leaf == 1) {
        t0 = av;
      }
      if (leaf == 1) {
        t1 = av;
      }
      if (leaf == 1) {
        t2 = -inf;
      }
      if (leaf == 1) {
        t3 = inf;
      }
      if (leaf == 1) {
        t4 = 1;
      }
      if (leaf == 1) {
        t5 = 1;
      }
      max_v[k] = t0;
      min_v[k] = t1;
      smax_v[k] = t2;
      smin_v[k] = t3;
      max_c[k] = t4;
      min_c[k] = t5;
      int m = (lk + hk) / 2;
      unsigned long long c1 = 2ULL * (unsigned long long)k + 1ULL;
      unsigned long long c2 = 2ULL * (unsigned long long)k + 2ULL;
      int u0 = lo[c1];
      int u1 = hi[c1];
      int u2 = lo[c2];
      int u3 = hi[c2];
      if (inner == 1) {
        u0 = lk;
      }
      if (inner == 1) {
        u1 = m;
      }
      if (inner == 1) {
        u2 = m;
      }
      if (inner == 1) {
        u3 = hk;
      }
      lo[c1] = u0;
      hi[c1] = u1;
      lo[c2] = u2;
      hi[c2] = u3;
      ent[ne] = k;
      ne += inner;
      k = k + 1;
    }
    while (ne > 0) {
      ne--;
      int e = ent[ne];
      update(e);
    }
  }

  // op 0: chmin, 1: chmax, 2: add, 3: assign on [a, b). An explicit stack replaces the recursion; every iteration
  // classifies the popped node (stop / whole / descend) into 0-1 flags and performs all guarded actions unconditionally.
  void apply_op(int op, int a, int b, long long x) {
    int sp = 0;
    int ne = 0;
    st_k[0] = 0;
    st_l[0] = 0;
    st_r[0] = n;
    sp = 1;
    while (sp > 0) {
      sp--;
      int fk = st_k[sp];
      int fl = st_l[sp];
      int fr = st_r[sp];
      long long mxk = max_v[fk];
      long long smk = smax_v[fk];
      long long mnk = min_v[fk];
      long long snk = smin_v[fk];
      int stop = 0;
      if (b <= fl || fr <= a) {
        stop = 1;
      }
      if (op == 0 && mxk <= x) {
        stop = 1;
      }
      if (op == 1 && x <= mnk) {
        stop = 1;
      }
      int cov = 0;
      if (a <= fl && fr <= b) {
        cov = 1;
      }
      int okc = 1;
      if (op == 0 && x <= smk) {
        okc = 0;
      }
      if (op == 1 && snk <= x) {
        okc = 0;
      }
      int whole = 0;
      if (stop == 0 && cov == 1 && okc == 1) {
        whole = 1;
      }
      int down = 0;
      if (stop == 0 && whole == 0) {
        down = 1;
      }
      int g0 = 0;
      int g1 = 0;
      int g2 = 0;
      int g3 = 0;
      if (whole == 1 && op == 0) {
        g0 = 1;
      }
      if (whole == 1 && op == 1) {
        g1 = 1;
      }
      if (whole == 1 && op == 2) {
        g2 = 1;
      }
      if (whole == 1 && op == 3) {
        g3 = 1;
      }
      long long y = 0;
      if (g2 == 1) {
        y = x;
      }
      update_node_max(fk, x, g0);
      update_node_min(fk, x, g1);
      add_all(fk, y);
      update_all(fk, x, g3);
      push(fk, down);
      ent[ne] = fk;
      ne += down;
      int m = (fl + fr) / 2;
      st_k[sp] = 2 * fk + 2;
      st_l[sp] = m;
      st_r[sp] = fr;
      st_k[sp + 1] = 2 * fk + 1;
      st_l[sp + 1] = fl;
      st_r[sp + 1] = m;
      sp += 2 * down;
    }
    while (ne > 0) {
      ne--;
      int e = ent[ne];
      update(e);
    }
  }

  // op 0: maximum, 1: minimum of [a, b).
  long long calc_op(int op, int a, int b) {
    long long res = -inf;
    if (op == 1) {
      res = inf;
    }
    int sp = 0;
    st_k[0] = 0;
    st_l[0] = 0;
    st_r[0] = n;
    sp = 1;
    while (sp > 0) {
      sp--;
      int fk = st_k[sp];
      int fl = st_l[sp];
      int fr = st_r[sp];
      long long mxk = max_v[fk];
      long long mnk = min_v[fk];
      int stop = 0;
      if (b <= fl || fr <= a) {
        stop = 1;
      }
      int cov = 0;
      if (a <= fl && fr <= b) {
        cov = 1;
      }
      int whole = 0;
      if (stop == 0 && cov == 1) {
        whole = 1;
      }
      int down = 0;
      if (stop == 0 && whole == 0) {
        down = 1;
      }
      if (whole == 1 && op == 0 && res < mxk) {
        res = mxk;
      }
      if (whole == 1 && op == 1 && mnk < res) {
        res = mnk;
      }
      push(fk, down);
      int m = (fl + fr) / 2;
      st_k[sp] = 2 * fk + 2;
      st_l[sp] = m;
      st_r[sp] = fr;
      st_k[sp + 1] = 2 * fk + 1;
      st_l[sp + 1] = fl;
      st_r[sp + 1] = m;
      sp += 2 * down;
    }
    return res;
  }

  void chmin(int a, int b, long long x) {
    apply_op(0, a, b, x);
  }

  void chmax(int a, int b, long long x) {
    apply_op(1, a, b, x);
  }

  void add_val(int a, int b, long long x) {
    apply_op(2, a, b, x);
  }

  void update_val(int a, int b, long long x) {
    apply_op(3, a, b, x);
  }

  long long calc_max(int a, int b) {
    return calc_op(0, a, b);
  }

  long long calc_min(int a, int b) {
    return calc_op(1, a, b);
  }
};

} // namespace cp

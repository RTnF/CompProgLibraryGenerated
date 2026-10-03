#pragma once
#include "geometry/line.hpp"
#include "geometry/vector.hpp"

template <class T> using Polygon = vector<Vec2<T>>;
template <class T> using Points = vector<Vec2<T>>;

template <class T> Polygon<T> convex_hull(Points<T> &p, bool strict = true) {
  int n = p.size();
  if (n <= 2) {
    return p;
  }
  int k = 0;
  sort(p.begin(), p.end(), Vec2<T>::compare_x);
  vector<Vec2<T>> ch(2 * n);
  auto check = [&](int i) {
    return sign(Vec2<T>::cross(ch[k - 1] - ch[k - 2], p[i] - ch[k - 1])) <=
           -1 + strict;
  };
  for (int i = 0; i < n; ch[k++] = p[i++]) {
    while (k >= 2 && check(i)) {
      --k;
    }
  }
  for (int i = n - 2, t = k + 1; i >= 0; ch[k++] = p[i--]) {
    while (k >= t && check(i)) {
      --k;
    }
  }
  ch.resize(k - 1);
  return ch;
}

template <class T> T area(const Polygon<T> &s) {
  ld ret = 0;
  int n = (int)s.size();
  for (int i = 0; i < n; i++) {
    int j = i == n - 1 ? 0 : i + 1;
    ret += (s[j].y + s[i].y) * (s[j].x - s[i].x);
  }
  return -ret / 2;
}

template<class T> bool in_polygon(const Vec2<T> &p, const Polygon<T> &poly) {
  // (px, py) - (px, -inf) とpolyの交点数
  int cnt = 0;
  int n = poly.size();
  for(int i = 0; i < n; i++) {
    int j = i + 1 == n ? 0 : i + 1;
    if (sign(poly[i].x - poly[j].x) == 0) {
      continue;
    }
    // 左にEPSずらす
    if (((poly[i].x - EPS < p.x && p.x < poly[j].x - EPS) ||
         (poly[j].x - EPS < p.x && p.x < poly[i].x - EPS)) &&
        find_point(Line{poly[i], poly[j]}, p.x) < p.y) {
      cnt++;
    }
  }
  return cnt & 1;
}
#pragma once
#include "geometry/vector.hpp"

template <class T> struct Line {
  Vec2<T> p, q;

  Line(const Vec2<T> &p_, const Vec2<T> &q_) : p(p_), q(q_) { assert(p != q); }
};

// 交差する
template <class T>
optional<pair<T, T>> vector_intersection(const Line<T> &l, const Line<T> &m) {
  T cross = Vec2<T>::cross(l.q - l.p, m.q - m.p);
  if (sign(cross) == 0) {
    return nullopt;
  }
  T a = l.q.x - l.p.x;
  T b = -(m.q.x - m.p.x);
  T c = l.q.y - l.p.y;
  T d = -(m.q.y - m.p.y);
  T e = m.p.x - l.p.x;
  T f = m.p.y - l.p.y;
  T g = a * d - b * c;
  return pair<T, T>((d * e - b * f) / g, (a * f - c * e) / g);
}

// 交差する
template <class T>
optional<Vec2<T>> line_intersection(const Line<T> &l, const Line<T> &m) {
  auto vec_inter = vector_intersection(l, m);
  if (!vec_inter) {
    return nullopt;
  }
  return l.p + (l.q - l.p) * vec_inter->first;
}

// 内部で交差する
template <class T>
optional<Vec2<T>> segment_intersection(const Line<T> &l, const Line<T> &m) {
  auto vec_inter = vector_intersection(l, m);
  if (!vec_inter || vec_inter->first < 0 || 1 < vec_inter->first ||
      vec_inter->second < 0 || 1 < vec_inter->second) {
    return nullopt;
  }
  return l.p + (l.q - l.p) * vec_inter->first;
}

template <class T> T find_point(const Line<T> &l, T x) {
  assert(sign(l.p.x - l.q.x));
  T a = (l.q.y - l.p.y) / (l.q.x - l.p.x);
  T b = l.p.y - a * l.p.x;
  return a * x + b;
}
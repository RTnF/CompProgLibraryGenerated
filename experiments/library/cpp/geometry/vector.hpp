#pragma once
#include "template/small_template.hpp"

template <class T> int sign(T x) { return x > EPS ? 1 : x < -EPS ? -1 : 0; }

template <class T = ld> struct Vec2 {
  T x, y;
  Vec2() : x(0), y(0) {}
  Vec2(T x_, T y_) : x(x_), y(y_) {}

  Vec2 operator+(const Vec2 &p) const { return {x + p.x, y + p.y}; }
  Vec2 operator-(const Vec2 &p) const { return {x - p.x, y - p.y}; }
  Vec2 operator*(T p) { return {x * p, y * p}; }
  Vec2 operator/(T p) { return {x / p, y / p}; }
  // 複素数
  Vec2 operator*(Vec2 p) {
    return {x * p.x - y * p.y, x * p.y + y * p.x};
  }
  Vec2 operator/(Vec2 p) {
    return {(x * p.x + y * p.y) / (p.x * p.x + p.y * p.y),
            (y * p.x - x * p.y) / (p.x * p.x + p.y * p.y)};
  }
  bool operator==(const Vec2 &p) {
    return sign(x - p.x) == 0 && sign(y - p.y) == 0;
  }
  bool operator!=(const Vec2 &p) { return !(*this == p); }

  //  3  2  1
  //  4  0  0
  // -3 -2 -1
  int arg_zone() const {
    static int q[3][3] = {{-3, 4, 3}, {-2, 0, 2}, {-1, 0, 1}};
    return q[sign(x) + 1][sign(y) + 1];
  }

  static T cross(const Vec2 &a, const Vec2 &b) { return a.x * b.y - a.y * b.x; }

  static bool compare_arg(const Vec2 &a, const Vec2 &b) {
    int az = a.arg_zone();
    int bz = b.arg_zone();
    if (az == bz) {
      return sign(cross(a, b)) > 0;
    }
    return az < bz;
  }

  static bool compare_x(const Vec2 &a, const Vec2 &b) {
    if (sign(a.x - b.x) == 0) {
      return a.y < b.y;
    }
    return a.x < b.x;
  }
};
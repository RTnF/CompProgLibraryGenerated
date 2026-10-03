#pragma once
#include "template/small_template.hpp"

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
};
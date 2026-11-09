#pragma once
#include <cassert>
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// An integer modulo a modulus m that is chosen at run time (1 <= m < 2^32), stored reduced in [0, m).
// Derived from experiments/library/cpp/modint/dynamic_modint.hpp (DynamicModInt). Differences: the modulus is not a
// static member but a field of every value (so two values of different moduli can coexist; the operations take the
// modulus of the left operand and require both operands to have the same modulus), and the operations are friend
// functions returning a new value instead of compound assignment operators.
// Preconditions: the operands are reduced (x < m) and have the same modulus. Time O(1), extra space O(1).
struct DModInt {
  unsigned int m, x;
  DModInt(unsigned int m_, unsigned int x_) : m(m_), x(x_ % m_) {}
  friend DModInt add(const DModInt &a, const DModInt &b) {
    return DModInt(a.m, (unsigned int)(((unsigned long long)a.x + (unsigned long long)b.x) % a.m));
  }
  friend DModInt sub(const DModInt &a, const DModInt &b) {
    return DModInt(a.m, (unsigned int)(((unsigned long long)a.x + (unsigned long long)a.m - (unsigned long long)b.x) % a.m));
  }
  friend DModInt mul(const DModInt &a, const DModInt &b) {
    return DModInt(a.m, (unsigned int)(((unsigned long long)a.x * (unsigned long long)b.x) % a.m));
  }
  friend DModInt neg(const DModInt &a) {
    return DModInt(a.m, (unsigned int)(((unsigned long long)a.m - (unsigned long long)a.x) % a.m));
  }
  friend bool equal(const DModInt &a, const DModInt &b) { return a.x == b.x; }
  // The inverse a^(m-2) of a nonzero value for a prime modulus m (Fermat). Preconditions: m >= 2 and a.x != 0.
  friend DModInt inv(const DModInt &a) {
    assert(a.x != 0);
    unsigned long long base = a.x;
    unsigned long long exp = (unsigned long long)a.m - 2;
    unsigned long long mm = a.m;
    unsigned long long result = 1 % mm;
    unsigned long long b = base % mm;
    unsigned long long ee = exp;
    while (ee != 0) {
      if ((ee & 1) != 0) {
        result = result * b % mm;
      }
      b = b * b % mm;
      ee = ee >> 1;
    }
    return DModInt(a.m, (unsigned int)result);
  }
  // a / b = a * b^(m-2) for a prime modulus m. Preconditions: m >= 2 and b.x != 0.
  friend DModInt div(const DModInt &a, const DModInt &b) {
    assert(b.x != 0);
    unsigned long long base = b.x;
    unsigned long long exp = (unsigned long long)a.m - 2;
    unsigned long long mm = a.m;
    unsigned long long result = 1 % mm;
    unsigned long long bb = base % mm;
    unsigned long long ee = exp;
    while (ee != 0) {
      if ((ee & 1) != 0) {
        result = result * bb % mm;
      }
      bb = bb * bb % mm;
      ee = ee >> 1;
    }
    return DModInt(a.m, (unsigned int)((unsigned long long)a.x * result % mm));
  }
  // a^e mod m by binary exponentiation (the loop of cp::pow_mod, written out because a verified function cannot call
  // another one). Precondition: none beyond 1 <= m < 2^32 (a.x need not be reduced). Time O(log e).
  friend DModInt power(const DModInt &a, unsigned long long e) {
    unsigned long long base = a.x;
    unsigned long long exp = e;
    unsigned long long mm = a.m;
    unsigned long long result = 1 % mm;
    unsigned long long b = base % mm;
    unsigned long long ee = exp;
    while (ee != 0) {
      if ((ee & 1) != 0) {
        result = result * b % mm;
      }
      b = b * b % mm;
      ee = ee >> 1;
    }
    return DModInt(a.m, (unsigned int)result);
  }
};

} // namespace cp

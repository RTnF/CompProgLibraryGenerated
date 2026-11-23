#pragma once
#include <cassert>

namespace cp {

// n x n matrix over T (experiments/library/cpp/number/square_matrix.hpp `SquareMatrix<T, n>`), an aggregate with the
// public array mat. O() is the zero matrix, I() the identity; operator[](i) is row i; +, -, * (and +=, -=, *=), unary
// + and -, ==, != and pow(e) (e >= 0, by repeated squaring).
// T is an arithmetic type (or one with 0, 1 from bool, +, -, * and ==); the values stay in the range of T.
// Time: O(n^2) for O, I, +, -, ==; O(n^3) for *; O(n^3 log e) for pow.

template <class T, int n> struct SquareMatrix {
  T mat[n][n];
  static SquareMatrix<T, n> O() {
    SquareMatrix<T, n> ret;
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        ret.mat[i][j] = 0;
      }
    }
    return ret;
  }
  static SquareMatrix<T, n> I() {
    SquareMatrix<T, n> ret;
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        ret.mat[i][j] = (i == j);
      }
    }
    return ret;
  }
  T (&operator[](int i))[n] { return mat[i]; }
  const T (&operator[](int i) const)[n] { return mat[i]; }
  SquareMatrix<T, n> &operator+=(const SquareMatrix<T, n> &y) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        mat[i][j] += y.mat[i][j];
      }
    }
    return *this;
  }
  SquareMatrix<T, n> &operator-=(const SquareMatrix<T, n> &y) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        mat[i][j] -= y.mat[i][j];
      }
    }
    return *this;
  }
  SquareMatrix<T, n> &operator*=(const SquareMatrix<T, n> &y) {
    SquareMatrix<T, n> tmp;
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        tmp.mat[i][j] = 0;
        for (int k = 0; k < n; k++) {
          tmp.mat[i][j] += mat[i][k] * y.mat[k][j];
        }
      }
    }
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        mat[i][j] = tmp.mat[i][j];
      }
    }
    return *this;
  }
  SquareMatrix<T, n> operator+() const { return *this; }
  SquareMatrix<T, n> operator-() const {
    SquareMatrix<T, n> minus;
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        minus.mat[i][j] = -mat[i][j];
      }
    }
    return minus;
  }
  SquareMatrix<T, n> pow(long long e) const {
    assert(e >= 0);
    SquareMatrix<T, n> y = *this, r = I();
    while (e) {
      if (e & 1) {
        r *= y;
      }
      e >>= 1;
      if (e) {
        y *= y;
      }
    }
    return r;
  }

  friend SquareMatrix<T, n> operator+(const SquareMatrix<T, n> &a,
                                      const SquareMatrix<T, n> &b) {
    return SquareMatrix<T, n>(a) += b;
  }
  friend SquareMatrix<T, n> operator-(const SquareMatrix<T, n> &a,
                                      const SquareMatrix<T, n> &b) {
    return SquareMatrix<T, n>(a) -= b;
  }
  friend SquareMatrix<T, n> operator*(const SquareMatrix<T, n> &a,
                                      const SquareMatrix<T, n> &b) {
    return SquareMatrix<T, n>(a) *= b;
  }
  friend bool operator==(const SquareMatrix<T, n> &a,
                         const SquareMatrix<T, n> &b) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (!(a.mat[i][j] == b.mat[i][j])) {
          return false;
        }
      }
    }
    return true;
  }
  friend bool operator!=(const SquareMatrix<T, n> &a,
                         const SquareMatrix<T, n> &b) {
    return !(a == b);
  }
};

} // namespace cp

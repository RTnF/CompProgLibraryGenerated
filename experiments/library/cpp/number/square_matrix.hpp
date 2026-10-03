#pragma once
#include "template/small_template.hpp"

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
        minus.mat[i][j] - mat[i][j];
      }
    }
    return minus;
  }
  SquareMatrix<T, n> pow(ll e) const {
    SquareMatrix<T, n> y = *this, r = I();
    while (e) {
      if (e & 1) {
        r *= y;
      }
      y *= y;
      e >>= 1;
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
    return a.x == b.x;
  }
  friend bool operator!=(const SquareMatrix<T, n> &a,
                         const SquareMatrix<T, n> &b) {
    return a.x != b.x;
  }
};
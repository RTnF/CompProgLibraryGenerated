#pragma once
#include <vector>

namespace cp {

// 行優先の n x n 行列（長さ n * n の vector）に対する演算。要素型 T は任意（検証した具体化は末尾の unsigned long long）。
// 前提: 各 vector の長さは n * n 以上で n * n < 2^31。a, b, c は互いに別の vector（mat_mul の a と b は同じでもよい。mat_equal は読むだけ）。

// c = a * b（成分は T の演算、unsigned long long なら 2^64 を法とする）。時間 O(n^3)、追加領域 O(1)。
template <class T>
inline void mat_mul(const std::vector<T> &a, const std::vector<T> &b, std::vector<T> &c, int n) {
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      T s = 0;
      for (int k = 0; k < n; k++) {
        s += a[i * n + k] * b[k * n + j];
      }
      c[i * n + j] = s;
    }
  }
}

// a += b（成分ごと）。時間 O(n^2)、追加領域 O(1)。
template <class T> inline void mat_add_assign(std::vector<T> &a, const std::vector<T> &b, int n) {
  int m = n * n;
  for (int i = 0; i < m; i++) {
    a[i] += b[i];
  }
}

// a -= b（成分ごと）。時間 O(n^2)、追加領域 O(1)。
template <class T> inline void mat_sub_assign(std::vector<T> &a, const std::vector<T> &b, int n) {
  int m = n * n;
  for (int i = 0; i < m; i++) {
    a[i] -= b[i];
  }
}

// a を零行列にする。時間 O(n^2)、追加領域 O(1)。
template <class T> inline void mat_zero(std::vector<T> &a, int n) {
  int m = n * n;
  for (int i = 0; i < m; i++) {
    a[i] = 0;
  }
}

// a = -a（成分ごと。T(0) - a[i]）。時間 O(n^2)、追加領域 O(1)。
template <class T> inline void mat_negate(std::vector<T> &a, int n) {
  int m = n * n;
  for (int i = 0; i < m; i++) {
    a[i] = T(0) - a[i];
  }
}

// a を単位行列にする（a[i * n + j] = (i == j)）。時間 O(n^2)、追加領域 O(1)。
template <class T> inline void mat_identity(std::vector<T> &a, int n) {
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      a[i * n + j] = 0;
      if (i == j) {
        a[i * n + j] = 1;
      }
    }
  }
}

// a と b が（先頭 n * n 要素で）等しいか。時間 O(n^2)、追加領域 O(1)。
template <class T> inline bool mat_equal(const std::vector<T> &a, const std::vector<T> &b, int n) {
  int m = n * n;
  bool same = true;
  for (int i = 0; i < m; i++) {
    if (a[i] != b[i]) {
      same = false;
    }
  }
  return same;
}

// r = a^e（行列の冪。e = 0 のとき単位行列）。y, t は作業用の vector で、a, r, y, t は互いに別の vector。a は変更しない。
// 繰り返し二乗法（元の `SquareMatrix::pow` と同じ手順: e の下位ビットが 1 のとき r *= y、毎回 y *= y、e を 2 で割る）。
// 前提は上と同じで、さらに r, y, t の長さも n * n 以上。a, r, y, t の n * n 個の要素は呼び出し前に任意の値でよい（r, y, t は上書きされる）。
// 時間 O(n^3 log e)、追加領域 O(1)。
template <class T>
inline void mat_pow(const std::vector<T> &a, std::vector<T> &r, std::vector<T> &y, std::vector<T> &t, int n,
                    unsigned long long e) {
  int m = n * n;
  for (int i = 0; i < m; i++) {
    y[i] = a[i];
  }
  for (int i = 0; i < m; i++) {
    r[i] = 0;
  }
  for (int i = 0; i < n; i++) {
    r[i * n + i] = 1;
  }
  while (e != 0) {
    if (e % 2 == 1) {
      mat_mul(r, y, t, n);
      for (int i = 0; i < m; i++) {
        r[i] = t[i];
      }
    }
    mat_mul(y, y, t, n);
    for (int i = 0; i < m; i++) {
      y[i] = t[i];
    }
    e /= 2;
  }
}

template void mat_mul<unsigned long long>(const std::vector<unsigned long long> &, const std::vector<unsigned long long> &,
                                          std::vector<unsigned long long> &, int);
template void mat_add_assign<unsigned long long>(std::vector<unsigned long long> &, const std::vector<unsigned long long> &, int);
template void mat_sub_assign<unsigned long long>(std::vector<unsigned long long> &, const std::vector<unsigned long long> &, int);
template void mat_zero<unsigned long long>(std::vector<unsigned long long> &, int);
template void mat_negate<unsigned long long>(std::vector<unsigned long long> &, int);
template void mat_identity<unsigned long long>(std::vector<unsigned long long> &, int);
template bool mat_equal<unsigned long long>(const std::vector<unsigned long long> &, const std::vector<unsigned long long> &, int);

template void mat_pow<unsigned long long>(const std::vector<unsigned long long> &, std::vector<unsigned long long> &,
                                          std::vector<unsigned long long> &, std::vector<unsigned long long> &, int,
                                          unsigned long long);

} // namespace cp

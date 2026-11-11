# pow_mod

`cp::pow_mod(base, exp, m)` は繰り返し二乗法で `base^exp mod m` を返す。元の `experiments/library/cpp/modint/modint.hpp` の `ModInt::pow` の中核に対応し、クラスの状態を持たない `unsigned long long` の関数に直した。

- 前提: `1 <= m <= 2^32`（このとき途中の積 `result * b` と `b * b` は `2^64` 未満）。`base` と `exp` は全値。
- 結果: `base^exp % m`（`m = 1` なら 0、`exp = 0` なら `1 % m`）。
- 計算量: O(log exp)（反復は `exp` のビット数）、追加領域 O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/PowMod.lean`（`UInt64` の演算）を生成する。`Proofs/Cpp/PowMod.lean` の `pow_mod_spec` が、前提のもとで結果が `base^exp % m` であり、tick 数がちょうど `bitWidth exp + 2` であることを証明する。ループ不変条件は `result * b^e ≡ base^exp (mod m)` と `result, b < m`。`UInt64` の積が折り返さないことは `result, b < m <= 2^32` から示す。

差分テスト（`tests/diff/pow_mod.py`、境界値と乱数）と C++ のテスト（`tests/pow_mod.cpp`、128 bit の参照計算）で翻訳と実装を確かめる。

## 元のソースからの変更

`ModInt::pow` の繰り返し二乗法を、法を引数に取る自由関数として書いた。

# inv_gcd

`cp::inv_gcd(a, b)` は拡張ユークリッドの互除法で、`gcd` と `a` の逆元に当たる値を求める。AtCoder Library の `inv_gcd`（`experiments/library/cpp/fps/convolution.hpp`）そのもので、`safe_mod`（`library/number_theory/safe_mod.hpp`）を使う。

`a' = a mod b`（`[0, b)` の代表元）として、`(g, x)` を返す。`g = gcd(a', b)`（`a' = 0` なら `g = b`）、`0 <= x < b / g`、`x * a ≡ g (mod b)`。`g = 1` なら `x` は `a` の `b` を法とする逆元である。

- 前提: `1 <= b`（`long long` の範囲）。`a` は `long long` の全値。途中の値の絶対値は `b` 以下で、符号付きオーバーフローは起きない（元のコメントの不変条件 [3]）。
- 計算量: O(log b)、追加領域 O(1)。`constexpr`。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/InvGcd.lean` を生成する（`safe_mod` の呼び出しは依存部品のモデル `Proofs/Cpp/Gen/SafeMod.lean` を呼ぶ）。`Proofs/Cpp/InvGcd.lean` の `inv_gcd_spec` が、`1 <= b < 2^63` の全入力について、結果が上の `(g, x)` の条件を満たすこと、tick 数が `gcdCost b a' + 4`（`log2 (a' b) + 6` 以下）以下であることを証明する。ループ不変条件は `Proofs/Math/InvGcdMath.lean` の `Inv`（元のコメントの契約 [1]〜[3] と `gcd` の保存）。`safe_mod` の呼び出しには `Proofs/Cpp/SafeMod.lean` の `safe_mod_wp` を使う。

差分テスト（`tests/diff/inv_gcd.py`）と C++ のテスト（`tests/inv_gcd.cpp`、元のソースの逐語コピーとの比較、仕様の条件、Fibonacci 数の最悪例）で翻訳と実装を確かめる。

## 元のソースからの変更

`std::` 修飾と名前空間のみ（`safe_mod` は別の部品として include する）。2026-11-12 までの公開版は結果を引数の vector に書く形に変えていたが、元の `pair` を返す形に戻した。

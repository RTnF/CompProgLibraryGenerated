# gcd_u64

`cp::gcd_u64(unsigned long long a, unsigned long long b)` は最大公約数をユークリッドの互除法で返す。`gcd(0, 0) = 0`、`gcd(a, 0) = a`（`std::gcd` と同じ）。`experiments/` の `Ratio`、`factorize` などが使う `gcd` の基礎部品。

前提: なし（`unsigned long long` の全値）。計算量: O(log(a b))、追加領域 O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/GcdU64.lean` を生成する（符号なし 64 bit は `UInt64`）。`Proofs/Cpp/GcdU64.lean` の `gcd_u64_spec` が、全入力について結果が `Nat.gcd a b` であること、tick 数が `gcdCost a b + 2`（`log2 (a b) + 4` 以下）以下であることを証明する。反復回数の上界は、`b ≤ a` の 1 反復で組の積が半分以下になることによる（`gcdCost_step`）。

差分テスト（`tests/diff/gcd_u64.py`、境界値と乱数）と C++ のテスト（`tests/gcd_u64.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

なし（`std::gcd` の符号なし 64 bit 版を新たに書いた部品）。

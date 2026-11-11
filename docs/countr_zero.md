# countr_zero

`cp::countr_zero_u64(n)` は `n` の末尾に連続する 0 ビットの個数を返す（C++20 の `std::countr_zero` の `unsigned long long` 版で、`n = 0` なら 64）。`experiments/library/cpp/fps/convolution.hpp` の `countr_zero_constexpr` に対応する。

前提: なし（`unsigned long long` の全値）。計算量: O(返り値)、追加領域 O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/CountrZero.lean` を生成する（符号なし 64 bit は `UInt64`）。`Proofs/Cpp/CountrZero.lean` の `countr_zero_u64_spec` が、全入力について返り値 `r` が `0 <= r <= 64`、`2^r ∣ n`、`r < 64` なら `¬ 2^(r+1) ∣ n` を満たすこと（`n = 0` なら `r = 64` になる）、tick 数がちょうど `r + 2` であることを証明する。

差分テスト（`tests/diff/countr_zero.py`、境界値と乱数）と C++ のテスト（`tests/countr_zero.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

- ビット判定 `n & (1 << x)` を、`n % 2 == 0` と `n = n / 2` の繰り返しに書き換えた（元の `1 << x` は `int` で `x = 31` のとき符号付きオーバーフロー。`docs/agent/fixes.md`）。結果は元と同じ。
- 引数を `unsigned int` から `unsigned long long` に広げた（`unsigned int` の値はすべてそのまま受け付ける）。
- 元の前提は `1 <= n`（`n = 0` では無限ループ）。`x < 64` の条件を足して `n = 0` では 64 を返す（`std::countr_zero(0)` と同じ）。
- `constexpr` は付けない。

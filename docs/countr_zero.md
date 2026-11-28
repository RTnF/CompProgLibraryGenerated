# countr_zero

`cp::countr_zero_u64(n)` は `std::countr_zero` を呼び出し、`n` の末尾に連続する 0 ビットの個数を返す。`n = 0` では 64 を返す。`experiments/library/cpp/fps/convolution.hpp` の `countr_zero_constexpr` に対応する。

前提: なし（`unsigned long long` の全値）。計算量: 固定幅整数に対して O(1)、追加領域 O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/CountrZero.lean` を生成する（符号なし 64 bit は `UInt64`）。`Proofs/Cpp/CountrZero.lean` の `countr_zero_u64_spec` が、全入力について返り値 `r` が `0 <= r <= 64`、`2^r ∣ n`、`r < 64` なら `¬ 2^(r+1) ∣ n` を満たすこと（`n = 0` なら `r = 64` になる）、tick 数がちょうど `2` であることを証明する。

差分テスト（`tests/diff/countr_zero.py`、境界値と乱数）と C++ のテスト（`tests/countr_zero.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

- ビットの走査を `std::countr_zero` に置き換えた。
- 引数を `unsigned int` から `unsigned long long` に広げた。入力が 0 のときは 64 を返す。
- 公開関数の宣言は `inline int`。

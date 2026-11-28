# bit_width_u64

`cp::bit_width_u64(std::uint64_t)` は `std::bit_width` を呼び出し、値 0 に対して 0、それ以外では 2 進表現の桁数を返す。

前提: なし（`uint64_t` の全値）。計算量: 固定幅整数に対して O(1)、追加領域 O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/BitWidthU64.lean` を生成する（符号なし 64 bit は `UInt64`）。`Proofs/Cpp/BitWidthU64.lean` の `bit_width_u64_spec` が、全入力について結果が `bitWidth value`（0 なら 0、それ以外は `log2 value + 1`）であり、tick 数がちょうど `2` であることを証明する。

差分テスト（`tests/diff/bit_width_u64.py`、境界値と乱数）と C++ のテスト（`tests/bit_width_u64.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

C++17 向けに実装していた除算ループを `std::bit_width` に置き換えた。公開関数名と引数型は従来どおり。

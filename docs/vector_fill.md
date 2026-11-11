# vector_fill

`cp::vector_fill<T>(std::vector<T> &x, T value)` は `x` の全要素を `value` にする。元の `experiments/library/cpp/template/template.cpp` の `fill(ALL(x), value)` に対応する。

前提: `x.size() < 2^31`。計算量: 時間 O(n)、追加領域 O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/VectorFill.lean` を生成する。`Proofs/Cpp/VectorFill.lean` の `vector_fill_spec` が、任意の `T` について、呼び出し後の `x` が `Array.replicate x.size value`（大きさは変わらず、全要素が `value`）であること、tick 数がちょうど `x.size + 1` であることを証明する。

差分テスト（`tests/diff/vector_fill.py`、`T = long long` と `T = int`）と C++ のテスト（`tests/vector_fill.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

`fill` を添字ループに書き換えた（結果は同じ）。

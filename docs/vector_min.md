# vector_min

`cp::vector_min<T>(const std::vector<T> &x)` は空でない `x` の最小要素を返す。元の `experiments/library/cpp/template/template.cpp` の `min<T>(const vector<T>&)`（`*min_element`）に対応する。

前提: `x.size() >= 1`（`assert` で確認する）、`x.size() < 2^31`。計算量: 時間 O(n)、追加領域 O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/VectorMin.lean` を生成する。`Proofs/Cpp/VectorMin.lean` の `vector_min_spec` が、任意の全順序 `T` と空でない `x` について、呼び出しが停止し、結果が `x` のある要素に等しく、どの要素もそれ以上であること、tick 数がちょうど `x.size` であることを証明する。

差分テスト（`tests/diff/vector_min.py`、`T = long long` と `T = int`）と C++ のテスト（`tests/vector_min.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

`*min_element` を添字ループに書き換えた（同じ入力に同じ値を返す）。

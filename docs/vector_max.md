# vector_max

`cp::vector_max<T>(const std::vector<T> &x)` は空でない `x` の最大要素を返す。元の `experiments/library/cpp/template/template.cpp` の `max<T>(const vector<T>&)`（`*max_element`）に対応する。

前提: `x.size() >= 1`（`assert` で確認する）、`x.size() < 2^31`。計算量: 時間 O(n)、追加領域 O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/VectorMax.lean` を生成する。`Proofs/Cpp/VectorMax.lean` の `vector_max_spec` が、任意の全順序 `T` と空でない `x` について、呼び出しが停止し、結果が `x` のある要素に等しく、どの要素もそれ以下であること、tick 数がちょうど `x.size` であることを証明する。

差分テスト（`tests/diff/vector_max.py`、`T = long long` と `T = int`）と C++ のテスト（`tests/vector_max.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

`*max_element` を添字ループに書き換えた（同じ入力に同じ値を返す）。

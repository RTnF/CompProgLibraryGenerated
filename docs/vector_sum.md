# vector_sum

`cp::vector_sum<T>(const std::vector<T> &x)` は `x` の全要素の和を返す（空なら `T` の 0）。元の `experiments/library/cpp/template/template.cpp` の `sum<T>`（`accumulate` を呼ぶテンプレート）に対応し、変換器が扱える形（添字ループ）に書き換えた。

- 前提: `x.size() < 2^31`、各部分和 `x[0] + ... + x[k]` が `T` に収まること（`T` が整数型のとき）。
- 結果: `x` の要素の総和。
- 計算量: 時間 O(x.size())、追加領域 O(1)。入力 vector は変更しない。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/VectorSum.lean` の `cp.vector_sum`（`T` の型変数と `[Inhabited T] [Zero T] [Add T]`）を生成する。`Proofs/Cpp/VectorSum.lean` の `vector_sum_spec` が、任意の加法モノイド `T` と任意の `x` について、呼び出しが停止して `x.toList.sum` を返し、tick 数がちょうど `x.size + 1` であること（したがって O(n)）を証明する。

差分テスト（`tests/diff/vector_sum.py`、`T = long long` と `T = int`）と C++ のテスト（`tests/vector_sum.cpp`、`std::accumulate` との照合）で翻訳と実装を確かめる。

## 元のソースからの変更

`accumulate` を添字ループに書き換えた（同じ入力に同じ結果を返す）。

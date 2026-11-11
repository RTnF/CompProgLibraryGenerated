# vector2d_sum

`cp::vector2d_sum<T>(const std::vector<std::vector<T>> &g)` は `g` の全要素の和を返す（空なら `T` の 0）。

前提: 行数と各行の長さが `2^31` 未満、`T` が整数型なら途中の和が `T` に収まること。計算量: 時間 O(行数 + 要素数)、追加領域 O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/Vector2dSum.lean` を生成する。`Proofs/Cpp/Vector2dSum.lean` の `vector2d_sum_spec` が、任意の加法モノイド `T` について、結果が各行の和の総和（`rowsSum g g.size`）であること、tick 数がちょうど `1 + 行数 + 要素数` であることを証明する。

差分テスト（`tests/diff/vector2d_sum.py`、`T = long long` と `T = int`）と C++ のテスト（`tests/vector2d_sum.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

なし（元の `template.cpp` にない補助関数）。

# doubling（`library/array/doubling.hpp`）

`cp::doubling(v, kmax)` は写像 `f(x) = v[x]` の累乗表を作る。行数 `w` は `std::bit_width(kmax)` で、行 `i` の頂点 `j` は `f` の `2^i` 回適用の結果。前提は `kmax > 0`、`v.size() <= INT_MAX`、全要素が `[0, v.size())` 内であること。空配列も受け付ける。

時間と返却表の領域は O((n + 1)w)、返却表を除く追加領域は O(1)。`n = 0` の場合も `w` 行を構築する。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` が `Proofs/Cpp/Gen/Doubling.lean` を生成する（`std::numeric_limits<int>::max()` はリテラル、`ret[0].assign(v.begin(), v.end())` は `v` のコピー）。`Proofs/Cpp/Doubling.lean` の `doubling_spec` は、`0 < kmax`、`v.size() < 2^31`、全要素が `[0, n)` のとき、返る表の行数が `bitWidth kmax`、各行の長さが `n`、行 `i` の `j` 番目が `F v i j = f^(2^i)(j)`（`f x = v[x]`）であり、tick 数が `3 + 2n + 3 bitWidth kmax + bitWidth kmax * (1 + 2n)` 以下であることを示す。行 `i` の要素は行 `i - 1` を 2 回引いて作る（`F_succ`、範囲は `F_range`）。差分テストは `tests/diff/doubling.py`。

## 元のソースからの変更

元の `experiments/library/cpp/array/doubling.hpp` の `doubling(vector<int> &v, uint64_t kmax)` に対し、公開版 `cp::doubling` は名前空間 `cp` に入れ、次の点だけを変えた。いずれも元と同じ入力に同じ表を返す。

- 引数 `v` を `const std::vector<int> &` にした（元の非 const 左辺値参照が受けるすべての引数を受け、右辺値や const な vector も受ける。`v` は読むだけ）。
- `int n = v.size()` の暗黙の縮小変換に対し、`v.size() <= INT_MAX` の assert を明示した。

`tests/doubling.cpp` の `check_against_original` が、元の関数の逐語コピー（`original::doubling`）と公開版の表を乱択と境界値（`kmax = 1`、`kmax = 2^64 - 1`）で比較して一致を確認する。

`tools/check_import_doubling.py` は原本ヘッダの C++23 構文確認と、公開版の通常実行・ASan/UBSan 実行を行う。全3,414写像（サイズ0〜5）を各14種類の `kmax` で独立オラクルと比較する。

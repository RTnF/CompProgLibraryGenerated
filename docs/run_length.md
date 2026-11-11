# run_length

`cp::run_length<T>(const std::vector<T> &v, std::vector<T> &values, std::vector<int> &counts)` は、`v` を同じ値が続く最大の連（run）に分け、`k` 番目の連の値を `values[k]`、長さを `counts[k]` に書いて、連の個数を返す。`experiments/library/cpp/array/element_count.hpp` の `element_count`、`search_util.hpp` の `counts`、`string/char_count.hpp` の `char_count`（どれも `vector<pair<T, int>>` を返す）をまとめて置き換える、結果を呼び出し側の 2 本の vector に書く形。vector を返す・伸ばす形は証明の枠組みがまだ対応していないので、`values` と `counts` は呼び出し側が `v.size()` 以上の大きさで用意する。


- 前提: `v`、`values`、`counts` は互いに別の vector で、`values.size() >= v.size()`、`counts.size() >= v.size()`、`v.size() < 2^31`。
- 結果: 返り値 `m` は連の個数。`k < m` の `(values[k], counts[k])` が `k` 番目の連。`k >= m` の要素は変えない。
- 計算量: O(n)、追加領域 O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/RunLength.lean` を生成する。`Proofs/Cpp/RunLength.lean` の `run_length_spec` が、等しさが決定可能な任意の型 `T` と前提を満たす入力について、`(values[k], counts[k])`（`k < m`）の列が `rle v`（`Proofs/Cpp/Lib/Rle.lean`）に等しいこと、両方の vector の大きさと `m` 以降の要素が変わらないこと、tick 数が `n + 1` 以下であることを証明する。

差分テスト（`tests/diff/run_length.py`、`T = long long` と `T = int`、余分な要素を持つ buffer）と C++ のテスト（`tests/run_length.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

この部品は元の `element_count`・`counts`・`char_count` の集計を呼び出し側の buffer に書く形で持つ補助部品である。`element_count` と `counts` は元の形でも公開している。

# search_util

`library/array/search_util.hpp` は元の `experiments/library/cpp/array/search_util.hpp` の `count` と `counts`、および二分探索 `lower_bound_index` をまとめた 1 つのヘッダーである。どれも要素型 `T` のテンプレートである。

## count

`cp::count<T>(const std::vector<T> &v, T value, int idx_begin = 0, int idx_end = -1)` は半開区間 `[idx_begin, E)` の位置 `i` のうち `v[i] == value` となるものの個数を返す。`E` は `idx_end`、`idx_end == -1` のときは `v.size()`。

- 前提: `v.size() < 2^31`、`0 <= idx_begin <= E <= v.size()`。
- 計算量: O(E - idx_begin)、追加領域 O(1)。

## counts

`cp::counts<T>(const std::vector<T> &v_sorted)` は、ソート済みの `v_sorted` に現れる値と個数の組を、値の昇順に返す。

- 前提: `v_sorted` が昇順（非減少）、`v_sorted.size() < 2^31`。
- 計算量: O(n)（`emplace_back` は償却 O(1)）、追加領域は結果の大きさ。

## lower_bound_index

`cp::lower_bound_index<T>(const std::vector<T> &a, T x)` は、昇順の `a` の中で `x` 以上である最初の要素の添字（なければ `a.size()`）を返す。`std::lower_bound(a.begin(), a.end(), x) - a.begin()` を二分探索で書いた補助関数で、元のソースにはない。

- 前提: `a` が昇順、`a.size() < 2^31`。
- 計算量: O(log n)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/SearchUtil.lean` を生成する。`Proofs/Cpp/SearchUtil.lean` が次を証明する。

- `count_spec`: 前提のもとで、結果は範囲の中で `v[i] = value` となる `i` の個数。tick 数はちょうど `1 + (E - idx_begin)`。
- `counts_spec`: 任意の入力について、結果は `v` のランレングス符号化 `rle v`（連続する等しい値の連と長さ。`Proofs/Cpp/Lib/Rle.lean`）。tick 数は `2 n + 1` 以下。`unrle_rle`（連を展開すると `v` に戻る）と `rle_ok`（各連は 1 個以上、隣り合う連の値は異なる）により、`v` が昇順なら結果は相異なる値と個数の組を昇順に並べたものになる。
- `lower_bound_index_spec`: 全順序 `T` と昇順の `a` について、結果 `r` は `0 <= r <= a.size()`、`r` 未満の添字の要素はすべて `x` 未満、`r` 以上はすべて `x` 以上（この 2 条件で `r` は一意）。tick 数は `bitWidth n + 2` 以下（O(log n)）。

差分テスト（`tests/diff/search_util.py`、`T = long long` と `T = int`）と C++ のテスト（`tests/search_util.cpp`、`std::count` と手書きの集計、全域の前提内の範囲）で翻訳と実装を確かめる。

## 元のソースからの変更

- `std::` 修飾と名前空間のみ。`counts` は 2026-11-12 に公開版へ戻した（それまで公開版から落ちていた）。
- `lower_bound_index` は元のソースにない補助関数。

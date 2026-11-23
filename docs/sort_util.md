# sort_util

`library/array/sort_util.hpp` は元の `experiments/library/cpp/array/sort_util.hpp` の関数をまとめた 1 つのヘッダーで、元の `inv_perm`・`arg_sort`・`inv_arg_sort`・`compress`（2 つのオーバーロード）と、追加の `sort_vector`・`dedup_vector` を持つ。すべて要素型 `T` のテンプレートのままで、検証した具体化はヘッダーの明示的な具体化に書いた型（`inv_perm<int>`、ほかは `long long`）。

元のソースからの変更: 本体は元と同じ（`namespace cp`、`std::` の明示）。`sort_vector`・`dedup_vector` は元のソースにはなく、`std::sort`・`std::unique` の契約を検証するための薄い包みである。2026-11-23 までの公開版の `compress(x, unzip, cmp)`（呼び出し側の vector に書く形、`offset` なし）は、元の 2 つの `compress` に置き換えた。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` が 4 つの関数テンプレートを型引数 `T` のまま `Proofs/Cpp/Gen/SortUtil.lean` に翻訳する（`std::sort` は `Cpp.sort`、erase-unique は `Cpp.unique`、`T` から添字への変換は `Cpp.Conv T Int`）。`Proofs/Cpp/SortUtil.lean` が次を示す。

- `sort_vector_spec`（全順序の任意の `T`）: 結果は `Cpp.sort x` で、昇順かつ `x` の並べ替え。tick 数は `1 + sortCost n`（`n log n` 程度）。
- `dedup_vector_spec`（`DecidableEq` の任意の `T`）: 結果は `Cpp.unique x`（隣り合う等しい要素の連を先頭 1 つに）、tick 数 `1 + n`。`unique_sorted`: 昇順の入力では狭義昇順で、要素の集合が変わらない。
- `inv_perm_spec`（具体化 `T = int`）: `v` が `[0, n)` の値を重複なく持つとき、結果は長さ `n` で `inv[v[j]] = j`、tick 数 `1 + 3n`。
- `arg_sort_spec`、`argSort_spec`（全順序の任意の `T`）: 結果は `argSort v`（`iota` の列を `v[a] < v[b]` で安定ソートしたもの）で、`0 .. n-1` の並べ替えであり、隣り合うとは限らない任意の 2 つ `a`（先）、`b`（後）について `v[a] < v[b]`、または `v[a] = v[b]` かつ `a < b`（安定性。`stable_index_sort`）。tick 数は `1 + 3n + sortCost n`。
- `inv_arg_sort_spec`（全順序の任意の `T`、`n < 2^31`）: 結果 `r` は長さ `n` で `r[argSort v [j]] = j`。tick 数は `3 + 6n + sortCost n`。
- `compress_spec`、`compress_offset_spec`（全順序で `IntCast` の任意の `T`、`n < 2^31`）: `unzip` は `Cpp.unique (Cpp.sort x)`（`x` の値の狭義昇順の列）、結果の `j` 番目は `lowerBound unzip x[j] + offset`（`T` に変換）で、`unzip` のその位置に `x[j]` がある（`lowerBound_found`）。tick 数は `1 + 3n + sortCost n + n (log2 n + 2)` 以下（引数 1 つ版は 1 多い）。

差分テストは `tests/diff/sort_util.py`。

## inv_perm

`cp::inv_perm<T>(const std::vector<T> &v)` は 0 始まりの順列 `v` の逆置換を返す（例: `[2, 4, 0, 1, 3]` → `[2, 3, 0, 4, 1]`）。

- 前提: `v.size() < 2^31`、すべての `v[i]` が `[0, v.size())` にあり、値が互いに異なる（`assert` で確かめる）。
- 結果: 戻り値 `inv` は長さ `v.size()` で `inv[v[j]] == j`（`inv_perm_spec`）。
- 時間: O(n)（tick 数 `1 + 3n`）。追加領域は結果の vector。

C++ のテストは `tests/sort_util.cpp`。

## arg_sort / inv_arg_sort

`cp::arg_sort<T>(const std::vector<T> &v)` はソート結果の添字の列（例: `[3, 3, 1, 5, 2]` → `[2, 4, 0, 1, 3]`）。等しい値は添字の順（`std::stable_sort`）。`cp::inv_arg_sort<T>(v)` はその逆置換で、各添字がソートでどこへ移るか（例: `[2, 3, 0, 4, 1]`）。

- 前提: `v.size() < 2^31`、`T` の `<` は狭義弱順序（Lean では全順序の型）。
- 時間: O(n log n)。`std::stable_sort` の計算量はドキュメントのとおりと認める（`docs/trust_policy.md`）。

## compress

`cp::compress<T>(const std::vector<T> &x, std::vector<T> &unzip, int offset = 0)` は座標圧縮（例: `[3, 3, 1, 5, 2]` → `[2, 2, 0, 3, 1] + offset`）。`unzip` に `x` の値を昇順・重複なしで置き、結果の `i` 番目に `x[i]` の `unzip` 中の位置に `offset` を足した値を返す。`cp::compress<T>(x, offset = 0)` は `unzip` を返さない版。

- 前提: `x.size() < 2^31`、`T` の `<` は全順序、`T` は位置 + `offset` の整数から作れる。
- 結果: `compress_spec`、`compress_offset_spec`。
- 時間: O(n log n)。

## sort_vector

`cp::sort_vector<T>(std::vector<T> &x)` は `std::sort(x.begin(), x.end())` で `x` を昇順に並べ替える。

- 前提: `T` の `<` は狭義弱順序（Lean では全順序の型）。
- 結果: 呼び出し後の `x` は `Cpp.sort x`（昇順かつ元の列の並べ替え、`sort_vector_spec`）。
- 時間: O(n log n)。`std::sort` の計算量はドキュメント（C++ 規格 [alg.sort]）のとおりと認め、翻訳表（`docs/translation.md`）で `sortCost n` の tick を加える。公理は置かない（`docs/trust_policy.md`）。

## dedup_vector

`cp::dedup_vector<T>(std::vector<T> &x)` は `x.erase(std::unique(x.begin(), x.end()), x.end())` で、隣り合う等しい要素の連を先頭の 1 個にする。整列済みの `x` に使えば重複が全部取り除かれる。

- 前提: `T` の `==` は同値関係（Lean では `DecidableEq`）。
- 結果: 呼び出し後の `x` は `Cpp.unique x`。`unique_sorted`: 入力が昇順なら結果は狭義昇順で、要素の集合が変わらない。
- 時間: O(n)（tick 数 `1 + n`）。

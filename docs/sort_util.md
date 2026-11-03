# sort_util

`library/sort_util.hpp` は元の `experiments/library/cpp/array/sort_util.hpp` の関数をまとめた 1 つのヘッダーで、`inv_perm`・`compress`・`sort_vector`・`dedup_vector` を持つ。すべて要素型 `T` のテンプレートのままで、検証した具体化はヘッダーの明示的な具体化に書いた型（`inv_perm<int>`、ほかは `long long`）。

元のソースからの変更: `arg_sort`・`inv_arg_sort`（`stable_sort` とラムダ比較）は未対応のため含めていない。`compress` は呼び出し側が用意した `unzip`・`cmp` に書き込む形で、元の「vector を返す版」と `offset` 引数は含めていない。`sort_vector`・`dedup_vector` は元のソースにはなく、`std::sort`・`std::unique` の契約を検証するための薄い包みである。

## inv_perm

`cp::inv_perm<T>(const std::vector<T> &v)` は 0 始まりの順列 `v` の逆置換を返す（例: `[2, 4, 0, 1, 3]` → `[2, 3, 0, 4, 1]`）。元の `experiments/library/cpp/array/sort_util.hpp` の `inv_perm<T>` と同じ関数テンプレートで、型パラメータ `T` は元のまま残した。検証した具体化は `T = int`（`template std::vector<int> inv_perm<int>(...)` で明示的に具体化している）。

- 前提: `v.size() < 2^31`、すべての `v[i]` が `[0, v.size())` にあり、値が互いに異なる。違反すると `assert` で停止する（異常終了）。
- 結果: 戻り値 `inv` は長さ `v.size()` で、`inv[v[j]] == j`。どの `v[j]` からも指されない添字は `-1` のまま。前提を満たす入力では `v` は順列なので `inv` も順列になる。
- 時間: O(n)（n = `v.size()`）。モデル上の仕事量は `320 n + 600` 以下、記憶領域は結果の vector に容量 n、その他は定数。

共通の入れ子 vector 生成器（`verifier/nested_ir.py`）が C++ の AST から Lean の本体を生成する。このとき `std::vector<int> inv(n, -1)`（fill 構築）を新しく扱う。`Proofs/InvPermCall.lean` の `inv_perm_correct` が前提を満たす全入力について、結果、停止、未定義動作の不在、仕事量と追加領域の上界、入力の保存、結果の根が呼び出し側の寿命に移ることを証明し、`inv_perm_spec` が結果の逆置換としての性質を述べる。`Proofs/InvPermMath.lean` が部分的に書き込んだ配列の数学的な記述、`Proofs/InvPermLoop.lean` がループ不変条件、`Proofs/FillWriteStmt.lean` が fill 構築と添字書き込みの文の補題である。

定理に含めていないこと: 前提違反が必ず `assert` で停止すること、呼び出し側の `v` 以外のオブジェクトが変化しないこと。C++ のテストは `tests/inv_perm.cpp` で、サイズ 7 以下の全順列と乱数順列を、全探索の基準と照合する。違反時の停止は `assert` 失敗なのでテストでは確認していない。

## compress

`cp::compress(const std::vector<long long> &x, std::vector<long long> &unzip, std::vector<int> &cmp)` は座標圧縮。`unzip` に `x` の値を昇順・重複なしで置き、`cmp[i]` に `x[i]` の `unzip` 中の位置を書く。`experiments/library/cpp/array/sort_util.hpp` の `compress` から、結果の vector の確保（戻り値）と `offset`・テンプレート化を除き、呼び出し側が用意した 3 本の vector に書く形にした（vector を返す関数は、証明の枠組みがまだ対応していない）。

- 前提: `x`、`unzip`、`cmp` は互いに別の vector で、`x.size() == unzip.size() == cmp.size() == n`、`n < 2^31 - 1`。`unzip` と `cmp` の元の内容は使わない（`unzip` は呼び出し後に `erase` で縮む）。
- 結果: `unzip` は `x` の値の集合を狭義昇順に並べたもの（`Proofs/CompressExec.lean` の `zipped x = uniqAdj (mergeSort x)`、`zipped_spec`）。各 `j < n` に対し `cmp[j] = q` で `unzip[q] = x[j]`（`compress_correct`）。
- 時間と領域: 要素のコピー、`std::sort`、`std::unique`、`n` 回の二分探索で `O(n log n)`。モデル上の仕事量は呼び出し側の引数評価を除いて高々 `costCmp n + 100`、vector への書き込みなど `sortComparisons n + 5 n` 回以下（`std::sort` の比較回数は契約公理 `sort_comparisons_bound` が与える `O(n log n)`）。追加領域は局所変数 6 個。

証明は `Proofs/CompressExec.lean`（実行の補題: コピーのループ `copy_loop`、`std::sort`/`std::unique` の 2 段 `exec_sortdedup`、二分探索 `iterYesC`/`iterNoC`/`loop_runC`、1 要素分 `b2_exec`、外側のループ `search_loop`、全体 `body_execCmp`）、`Proofs/CompressPrepare.lean`（3 本の vector の束縛 `prepare_cmp`）、`Proofs/CompressCall.lean`（呼び出し定理 `compress_correct`）。共有基盤は複数 vector の枠組み（`Proofs/MultiVec.lean`: `std::sort`/`std::unique` の段 `sort_stepM`/`dedup_stepM`、`FWM.replace` を今回追加）と `Proofs/ForLoopC.lean`。

定理に含めていないこと: `long long` 以外の要素型、`offset`、vector を返す形、`x`・`unzip`・`cmp` に同じ vector を渡す場合。C++ のテストは `tests/compress.cpp`（ランダムな列を `std::sort`・`std::unique`・`std::lower_bound` による参照と比較）。

型 `T` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化はヘッダー末尾の明示的な具体化（`template ... <型>(...)`）に書いた型だけ。

## sort_vector

`cp::sort_vector(std::vector<long long> &x)` は `x` を昇順に並べ替える（`std::sort(x.begin(), x.end())`、比較は既定の `operator<`）。

- 前提: `x.size() < 2^31`（`x` は呼び出し側が所有する書き込み可能な vector）。比較関数を取る形、整数以外の要素、vector 以外の範囲は扱わない。
- 結果: 呼び出し後の `x` は、`List.mergeSort`（`(· ≤ ·)`）で定義した昇順の並べ替え。昇順であることと元の列の並べ替えであることは、Lean の標準ライブラリの定理（`List.pairwise_mergeSort`、`List.mergeSort_perm`）から得られる。
- 時間と領域: 比較回数の上界は STL 契約公理 `Proofs.StlContracts.sort_comparisons_bound`（C++17 [alg.sort] の要求 O(n log n)）に依存する。モデル上の仕事量は `sortComparisons n + n`。定理 `sort_vector_work_bound` が、契約のもとで `sortComparisons n + n ≤ (c+1) n (log₂ n + 1)` を示す（契約に依存する唯一の定理）。追加領域は呼び出しの局所領域だけ（`std::sort` の実装が使う O(log n) の再帰の深さはモデルに入れていない）。

信頼の区分: この部品の定理は、STL 契約公理（`verification/stl_contracts.json`）に依存する。結果の値（`std::sort` が昇順の並べ替えを返すこと）は公理ではなく、`NStmt.sortVec` の意味（`Frame.sortAll` / `sortFlat`）の定義として与え、変換器が `std::sort(v.begin(), v.end())` の呼び出しを、システムヘッダーの `std::sort` の実体であることを確認したうえで `sortVec` に写す。比較関数が既定の `operator<` であり、`long long` の全順序であるため、結果は一意。

C++ のテストは `tests/sort_vector.cpp`（長さ 0〜40 の重複の多い乱数列、極値、20 万要素）。

## dedup_vector

`cp::dedup_vector(std::vector<long long> &x)` は `x.erase(std::unique(x.begin(), x.end()), x.end())` で、隣り合う等しい要素の連を先頭の 1 個にする。整列済みの `x` に使えば重複が全部取り除かれる（座標圧縮の部品）。

- 前提: `x.size() < 2^31`。比較は既定の `operator==`。述語を取る形、整数以外の要素は扱わない。
- 結果: 呼び出し後の `x` は `uniqAdj`（`Proofs/CppNestedVectorBindings.lean`）の結果。`uniqAdj_sorted_spec` が、入力が昇順なら結果は狭義昇順で、要素の集合が変わらないことを示す。`uniqAdj_mem`、`uniqAdj_length` で、結果の要素は入力の要素であり、長さは増えない。
- 時間と領域: モデル上の仕事量は `2 * x.size()` と定数。追加領域は局所領域だけ。契約公理には依存しない（結果も費用も定義で与える）。
- モデルの仮定: erase は消した位置以降のイテレータと参照を無効にするので、記憶域の epoch を進める。容量は変わらない。

C++ のテストは `tests/dedup_vector.cpp`（隣接の連、整列済みでの狭義昇順と集合の保存、極値、空）。

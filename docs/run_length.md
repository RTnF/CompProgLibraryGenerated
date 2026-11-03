# run_length

`cp::run_length<T>(const std::vector<T> &v, std::vector<T> &values, std::vector<int> &counts)` は、`v` を同じ値が続く最大の連（run）に分け、`k` 番目の連の値を `values[k]`、長さを `counts[k]` に書いて、連の個数を返す。`experiments/library/cpp/array/element_count.hpp` の `element_count`、`search_util.hpp` の `counts`、`string/char_count.hpp` の `char_count`（どれも `vector<pair<T, int>>` を返す）をまとめて置き換える、結果を呼び出し側の 2 本の vector に書く形。vector を返す・伸ばす形は証明の枠組みがまだ対応していないので、`values` と `counts` は呼び出し側が `v.size()` 以上の大きさで用意する。

- 前提: `v`、`values`、`counts` は互いに別の vector で、`values.size() == counts.size() == v.size() == n`、`n < 2^31 - 1`。`values` と `counts` の元の内容は、`k` 番目の連を書くまで使わない。
- 結果: 返り値 `m` は `(rle v).length ≤ n`。`k < m` に対し `(values[k], counts[k])` は `rle v` の `k` 番目（`pairsOf values counts m = rle v`）。`rle v` は、各対 `(a, c)` を `a` の `c` 個の並びに戻して連結すると `v` に戻り（`rleFlat (rle v) = v`）、すべての `c` が正で、隣り合う連の値が異なる（`AdjOK`）。`k ≥ m` の要素は変わらない。
- 時間と領域: 1 回の走査で `O(n)`。モデル上の仕事量は呼び出し側の引数評価を除いて高々 `420 * n + 300`、vector への書き込みは `2 * n + 2` 回以下。追加領域は局所変数 5 個。

証明は `Proofs/RunLengthMath.lean`（純粋な数学: `rle`・`rleAdd`・`rleExt`、仕様 `rle_spec`）、`Proofs/RunLengthExec.lean`（実行の補題: 1 反復の 2 つの場合 `iterEqR`/`iterNeR`、ループ `rl_loop`、全体 `body_execRL`）、`Proofs/RunLengthCall.lean`（呼び出し定理 `run_length_correct`）で行った。`compress` と同じ複数 vector の枠組み（`mvCm`、`fwC_init`、`prepare_vvv`）を使う。

型 `T` はテンプレート引数のままで、検証した具体化は `run_length<long long>`（ヘッダー末尾の明示的な具体化）。定理に含めていないこと: `long long` 以外の具体化（`char` など）、`pair` を返す形。C++ のテストは `tests/run_length.cpp`（ランダムな列を素朴な分割と比較）。

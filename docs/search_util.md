# search_util

`library/array/search_util.hpp` は元の `experiments/library/cpp/array/search_util.hpp` の `count` と、二分探索 `lower_bound_index` をまとめた 1 つのヘッダーである。どちらも要素型 `T` のテンプレートのままで、検証した具体化は `count<int>` と `lower_bound_index<long long>`。

元のソースからの変更: `count` の既定引数（`idx_begin = 0`、`idx_end = -1`）は元のまま残した。`counts`（ソート済みの値と個数の組を返す）は `pair` と vector の返却が未対応のため含めていない。`lower_bound_index` は元のソースにはなく、`std::lower_bound` と同じ結果を返す二分探索である。

## count

`cp::count<T>(const std::vector<T> &v, T value, int idx_begin = 0, int idx_end = -1)` は半開区間 `[idx_begin, idx_end)` の位置 `i` のうち `v[i] == value` となるものの個数を返す。`idx_end == -1` は `v.size()` を表す。元の `experiments/library/cpp/array/search_util.hpp` の `count<T>` と同じ関数テンプレートで、既定引数も残した。検証した具体化は `count<int>`。

- 前提: `v.size() < 2^31`、`idx_begin` は 0 以上の `int`、`idx_end` は `-1` か 0 以上の `int`。範囲が空または逆順（`idx_begin >= idx_end`）なら `v` を読まずに 0 を返す。そうでなければ `idx_end`（`-1` なら `v.size()`）が `v.size()` 以下であること。`idx_end < -1` の呼び出しは C++ では 0 を返すが、定理の対象外である。
- 結果: 位置 `j ∈ [idx_begin, E)`（`E` は `idx_end` または `v.size()`）で `v[j] == value` のものの個数。
- 時間: 範囲の長さを `E - idx_begin` として O(E - idx_begin)。モデル上の仕事量は呼び出し側の引数評価に加えて高々 `108 (E - idx_begin) + 300`。追加領域は定数（局所変数 3 個）。入力 vector は変更しない。

共通の入れ子 vector 生成器（`verifier/nested_ir.py`）が C++ の AST から Lean の本体を生成し、`Proofs/CountCall.lean` の `count_correct` が上の前提を満たす全入力について、結果、停止、未定義動作の不在、仕事量と追加領域の上界、入力 vector の保存を証明する。`Proofs/CountLoop.lean` に反復ごとの不変条件がある。定理にまだ含めていないこと: 呼び出し側の `v` 以外のオブジェクトが変化しないこと、前提違反が必ず異常終了すること。

C++ のテストは `tests/search_util.cpp` で、`std::count` を独立した基準として、長さ 6 以下の 3 値ベクタの全件と全範囲、`INT_MIN`/`INT_MAX` を含む大きなベクタの乱数範囲を照合する。

## lower_bound_index

`cp::lower_bound_index<T>(const std::vector<T> &a, T x)` は、昇順の `a` の中で `x` 以上である最初の要素の添字（なければ `a.size()`）を返す。`std::lower_bound(a.begin(), a.end(), x) - a.begin()` に対応し、変換器が扱える二分探索のループで書いた。座標圧縮（`experiments/library/cpp/array/sort_util.hpp` の `compress`）の `lower_bound` の部分に当たる。

- 前提: `a.size() < 2^31`、`a` は昇順（任意の `i <= j` で `a[i] <= a[j]`）。`x` は `long long` の全値。
- 結果: 返り値 `r` は `0 <= r <= a.size()`、`r` 未満の添字の要素はすべて `x` 未満、`r` 以上の添字の要素はすべて `x` 以上。この 2 条件で `r` は一意に決まるので、`std::lower_bound` の結果と一致する（C++ のテストで確認）。
- 時間と領域: ループの反復は `floor(log2(a.size())) + 1` 回以下。モデル上の仕事量は呼び出し側の引数評価を除いて高々 `157 * log2(a.size()) + 260`。追加領域は局所変数 3 個（`lo`、`hi`、`mid`）と引数 `x`。

`std::lower_bound` の呼び出しそのものではなく手書きの二分探索にしたのは、`lower_bound` を式として扱うモデル（入れ子 vector の読み取り式の拡張）を足さずに済ませるため。契約公理を使わず、結果も費用もループの証明から得る。

証明は `Proofs/LowerBoundIndexCall.lean`: `LInv`（`lo` 未満は `x` 未満、`hi` 以上は `x` 以上）が反復で保たれること（`LInv_yes`、`LInv_no`、昇順の仮定 `SortedL` を使う）、区間幅が毎回半分以下になること（`stepsL`、`stepsL_log`）、`iterYes`/`iterNo`（1 反復の実行）、`loop_runL`、`body_execL`、呼び出し定理 `lower_bound_index_correct`。

定理に含めていないこと: `a` が昇順でない場合の結果（前提で除く）。C++ のテストは `tests/search_util.cpp`（長さ 0〜40 の乱数列で全ての `x`、極値、空、100 万要素）。

# interval_union

`cp::interval_union_inclusive<T>(std::vector<T> &l, std::vector<T> &r, std::vector<T> &ret_l, std::vector<T> &ret_r)` は、閉区間 `[l[i], r[i]]` の和集合を求める。`experiments/library/cpp/interval/interval_union.hpp` の `interval_union_inclusive`（`vector<pair<T, T>> &` を受け取り、結果を `vector<pair<T, T>>` で返す）に対応する。入力の組 `(l[i], r[i])` を辞書順に並べ（元と同じく入力の `l`, `r` が並べ替えられる）、結果を `ret_l`, `ret_r` の先頭に書き、結果の区間の個数を返す。

元のソースからの変更（検証できる形にするために書き換えた。`docs/experiments_status.md` の違反一覧に載せている）:

- `pair` の vector を 2 本の vector `l`, `r` に分けた。結果も `pair` の vector を返さず、呼び出し側が用意した `ret_l`, `ret_r` に書く（`run_length` と同じ形）。
- 並べ替えは `std::sort`（`O(n log n)`）でなく挿入ソート（`O(n²)`）にした。並べ替えた結果（辞書順）は同じ。
- 構造化束縛 `auto &&[l, r]` と `ret.back().second` は、添字による読み書きに書き換えた（アルゴリズムは同じ）。

- 前提: `l`, `r`, `ret_l`, `ret_r` は互いに別の vector で、`l.size() == r.size() == n`、`ret_l.size() ≥ n`、`ret_r.size() ≥ n`、すべての `i` で `l[i] ≤ r[i]`、すべての要素が `long long` に収まる、`n < 2^31 - 1`、`ret_l.size()`, `ret_r.size() < 2^31`。
- 結果: 返り値 `m` について、`ret_l[k] ≤ ret_r[k]`（`k < m`）、`ret_r[k] < ret_l[k + 1]`（結果は昇順で、区間の間に隙間がある）、点 `x` が入力のある区間に入る必要十分条件は結果のある区間に入ること（`Cov M x ↔ Cov (l.zip r) x`）。呼び出し後の `l`, `r` は元の組の並べ替え（`Perm`）で、辞書順に整列している。`ret_l`, `ret_r` の `m` 番目以降は変わらない。
- 時間と領域: 挿入ソートが `O(n²)`、併合が `O(n)`。モデル上の仕事量は呼び出し側の引数評価を除いて高々 `(410 n + 120) n + 420 n + 140`、vector への書き込みは `4 n² + 2 n` 回以下。追加領域は局所変数 9 個以下。

証明は `Proofs/IntervalUnionMath.lean`（辞書順・整列の補題、併合の不変条件 `MInv` と `mfold_inv`）、`Proofs/IntervalUnionExec.lean`（実行の補題: 挿入ソートの内側のループ `sink_loop`、外側のループ `sort_exec`、併合のループ `merge_exec`、全体 `prog_exec`）、`Proofs/IntervalUnionCall.lean`（呼び出し定理 `interval_union_correct`）。component の定理は `Proofs/IntervalUnionComponent.lean` に再掲している。

型 `T` はテンプレート引数のままで、検証した具体化はヘッダー末尾の明示的な具体化 `interval_union_inclusive<long long>`。定理に含めていないこと: `pair` の vector を直接受け取る形、`l[i] > r[i]` の入力（元のコードは空の区間を未定義の形で扱う）、`long long` 以外の具体化。C++ のテストは `tests/interval_union.cpp`（元の実装を `std::sort` で書いたものとの比較、点ごとの被覆の確認、入力が整列される副作用、`ret_l`, `ret_r` の残りが変わらないこと、極値、`int` の具体化）。

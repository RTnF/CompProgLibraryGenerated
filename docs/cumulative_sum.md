# cumulative_sum

このヘッダーには 1 次元の `cp::CumulativeSum<T>` と 2 次元の `cp::CumulativeSum2D<T>` の 2 つのクラスがある（元のソースの `CumulativeSum` と `CumulativeSum2D`）。

## CumulativeSum（1 次元）

`cp::CumulativeSum<T>` は 1 次元の累積和（`experiments/library/cpp/array/cumulative_sum.hpp` の `CumulativeSum`）である。配列 `A`（`n` 要素）から vector `cs`（`cs[i]` は先頭 `i` 個の和、大きさ `n + 1`）を `O(n)` で作り、更新はできず、部分和は `O(1)` で返す。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `CumulativeSum(const std::vector<T> &v)` | `v` の累積和を作る | O(n) |
| `sum(a)` | `A[0, a)` の和（`0 <= a <= n`） | O(1) |
| `sum(a, b)` | `A[a, b)` の和（`0 <= a <= b <= n`） | O(1) |

型 `T` はテンプレート引数のままで、元と同じく任意の加法の型で使える。検証した具体化は `CumulativeSum<long long>` と `CumulativeSum2D<long long>`（`template class CumulativeSum<long long>;` で明示的に具体化している）。以前の公開版にあった `prefix_sums`（その場での累積和）は、構成子の核にあたるため、このクラスの構成子に統合した。

元のソースからの変更（検証できる形にするために書き換えた）:

- フィールド `n` は持たない（常に `cs.size() - 1` に等しい）。問い合わせは `const` にした。構成子の繰り返しは 1 ではなく 0 から始める（`cs[i + 1] = cs[i] + v[i]`。同じ値を作る）。
- 元の `assert` は検査として残した。`0 <= a && a <= n` は、検証済みの式に vector の大きさを含む `&&` がないため、`assert(0 <= a); assert(a < (int)cs.size());` と 1 つずつに分けた。

証明する内容（`Proofs/CumulativeSumComponent.lean` が `Proofs/CumulativeSumCall.lean` と `Proofs/CumulativeSum2DCall.lean` の定理を再掲する）。1 次元版（`Proofs/CumulativeSumCall.lean`、一般の入力について。すべて `T = long long`）:

- `cum_sum_prefix_correct`（`sum(a)`）: `a` が `cs` の範囲内（`a < cs.size()`）のとき、結果は `cs[a]`。
- `cum_sum_range_correct`（`sum(a, b)`）: `a <= b < cs.size()` で、`cs[b] - cs[a]` が `long long` に収まるとき、結果は `cs[b] - cs[a]`。
- `cum_sum_range_value`: `cs` が配列 `A` の累積和（`cs[i] = pre A i`）なら、結果は `A[a, b)` の和 `((A.drop a).take (b - a)).sum` に等しい（`pre_diff`）。
- `cumulative_sum_from_vector_correct`（構成子）: メンバー初期化子 `cs(v.size() + 1)` の後に実行される本体（`cs[0] = 0` と 1 つのループ）の後、`cs` は長さ `n + 1` で、`q <= n` のすべての `q` について `cs[q] = pre V q`（先頭 `q` 個の和）。前提は `n + 1 < 2^31 - 1` と、すべての累積和が `long long` に収まること。仕事量は `220 * n + 200` 以下、`cs` への書き込みは `n + 1` 回以下、追加領域は局所変数 2 個。

定理に含めていないこと: `CumulativeSum(v)` のメンバー初期化子 `cs(v.size() + 1)` は標準ライブラリの `std::vector<T>(size_type)` の契約による（`docs/trust_policy.md`）。構成子の定理は、`cs` がこの標準の構成子で作られた直後であることを前提にしている（`cs.size() == v.size() + 1`）。`assert` が失敗する入力での異常終了、`T` が `long long` 以外のときの検証。C++ のテストは `tests/cumulative_sum.cpp` で、素朴な累積和を基準として、長さ 0〜1000 の乱数配列、極値、`int`・`double` の具体化を確認する。


## CumulativeSum2D（2 次元）

`n × m` の行列 `v`（`vector<vector<T>>`）から表 `cs`（`n + 1` 行、各行 `m + 1` 要素、`cs[a][b]` は `v` の `[0, a) × [0, b)` の和）を作り、長方形の和を `O(1)` で返す。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `CumulativeSum2D(const std::vector<std::vector<T>> &v)` | 空でない長方形の行列 `v` の表を作る | O(n m) |
| `sum(a, b)` | `[0, a) × [0, b)` の和（`0 <= a <= n`, `0 <= b <= m`） | O(1) |
| `sum(a1, b1, a2, b2)` | `[a1, a2) × [b1, b2)` の和（`0 <= a1 <= a2 <= n`, `0 <= b1 <= b2 <= m`） | O(1) |

元のソースからの変更:

- フィールド `n`, `m` は持たない（`n = cs.size() - 1`, `m = cs[0].size() - 1`）。問い合わせは `const` にした。
- 構成子は、元の「行ごとの累積和のあとに列ごとの累積和」を、行を 1 回走査して（行の途中までの和 `run` と 1 つ上の行の表の値を足して）同じ表を作る形にした。結果の表は同じで、時間は `O(n m)` のまま。
- 行や要素へのアクセスは、検証できる形にするため別々の宣言に分けた（`int rows = (int)cs.size(); T x = cs[a][b];` など）。元の `assert` は検査として残した（構成子では `n > 0`, `m > 0`, すべての行の長さが `m`）。
- 型 `T` はテンプレート引数のまま。検証した具体化は `CumulativeSum2D<long long>`。

証明する内容（`Proofs/CumulativeSum2DCall.lean`、`Proofs/CumulativeSum2DExec.lean`、`Proofs/CumulativeSum2DMath.lean`。すべて `T = long long`）:

- `cs2_ctor_correct`（構成子）: `cs` が `n + 1` 行 `m + 1` 列の 0 の表（標準の構成子 `cs(v.size() + 1, vector<T>(v[0].size() + 1, T(0)))` の直後）、`v` が空でない長方形で、すべての行の累積和・行の途中までの和・表の要素が `long long` に収まるとき、実行後の `cs` は `cs[a][b] = P2 v a b`（`v` の `[0, a) × [0, b)` の和）。仕事量は `(80 m + 100) n + 110` 以下、`cs` への書き込みは `n m` 回以下。`cs` と `v` の根と行のオブジェクトが重ならないこと（`hd0`〜`hd2`）を前提にする。
- `cs2_ctor_table`: 実行後、`cs` の各行のオブジェクトの内容が表 `csRows v m` の行に等しい。この状態が `cs2_sum2_correct` と `cs2_sum4_correct` の前提になる。
- `cs2_sum2_correct`（`sum(a, b)`）: `a <= n`, `b <= m` のとき結果は `P2 v a b`。仕事量は引数の式の大きさ + 120 以下。
- `cs2_sum4_correct`（`sum(a1, b1, a2, b2)`）: `a1 <= a2 <= n`, `b1 <= b2 <= m` で、途中の差と和が `long long` に収まるとき、結果は `P2 v a2 b2 - P2 v a1 b2 - P2 v a2 b1 + P2 v a1 b1`。仕事量は引数の式の大きさ + 250 以下。

定理に含めていないこと: 構成子のメンバー初期化子 `cs(v.size() + 1, vector<T>(...))` は標準ライブラリの `std::vector` の契約による（`docs/trust_policy.md`）。構成子の定理は、`cs` がこの標準の構成子で作られた直後であることを前提にしている。`assert` が失敗する入力での異常終了、`T` が `long long` 以外のときの検証。C++ のテストは `tests/cumulative_sum.cpp` で、素朴な長方形の和を基準として、小さな行列のすべての `(a, b)` と `(a1, b1, a2, b2)`、`int`・`double` の具体化を確認する。

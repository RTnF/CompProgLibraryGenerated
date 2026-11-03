# vector2d_sum

`cp::vector2d_sum<T>(const std::vector<std::vector<T>> &g)` は `g` の全要素の和を行ごとに足して返す（`g` が空、または行が空なら 0）。`vector<vector<T>>` を読み取り専用の引数として検証する最初の部品で、`vector_sum`（平らな vector）の入れ子版である。

- 前提: `g.size() < 2^31 - 1`、各行の大きさ `< 2^31 - 1`、行ごとに足していく途中の和（先頭から数えたすべての部分和）が `T = long long` に収まること（符号付き桁あふれは検証済みの契約の外）。
- 結果: `sumRows g`（行の和の和）。時間は、行数を `R`、行の大きさの上界を `L` として `(50 L + 100) R + 定数` 以下（一様な上界なので、行の大きさがばらつくときは緩い）。追加領域は局所変数 6 個。
- 書き方の制約: 検証済みの式の言語では、行へのアクセス `g.size()`、`g[i].size()`、`g[i][j]` は、宣言または代入の右辺（`cast` の下も可）にだけ置ける。そのため `int rows = (int)g.size();`、`int cols = (int)g[i].size();`、`T x = g[i][j];` を別の宣言にしている。ループ条件や二項演算の中には直接書かない。

型 `T` はテンプレート引数のままで、検証した具体化は `long long`（`template long long vector2d_sum<long long>(...)`）。

証明（`Proofs/Vector2dSumCall.lean`、本体の実行は `Proofs/Vector2dSumExec.lean`）: `vector2d_sum_correct` は、呼び出し側が入れ子の根（行 `i` はオブジェクト `V + 1 + i`、内容は `rows[i]`）を持つとき、`prepare` と呼び出しが成功し、結果が `sumRows rows` で、呼び出し側の状態が保たれる（`ScalarPostM`）ことを示す。枠組みは `Proofs/MultiVecN.lean`（入れ子の根を持てる `pexecM` のフォーク）、行アクセスの評価は `Proofs/NestedReadOnly.lean`、`declare`/`assign` での一時 binding の解放は `Proofs/VecStmtX.lean`。

定理に含めていないこと: 行が `T` の範囲に収まらない場合の挙動、ループ条件に行アクセスを直接書く形。

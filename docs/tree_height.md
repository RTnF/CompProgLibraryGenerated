# tree_height

`cp::tree_height(cost_depth0, cost_depth1, h, n)` は、`h[i] = max(cost_depth0[i], cost_depth1[i])` を `i < n` について書く。`experiments/library/cpp/tree/tree.hpp` の `Tree::height`（各頂点から最も遠い頂点までの距離）の最後のループを、検証できる形に書き直した。`Cost` はテンプレートのまま残し、検証した具体化は `long long`。

`Tree::height` は、直径の両端 `f0`、`f1` を根にした 2 回の `build_depth` が作る `cost_depth` を使う。その 2 つの配列は呼び出し側が `tree_root` で求める: 任意の根（例えば 0）で `tree_root` を呼んだときの最遠点 `stk[n]` が一方の端 `f0`、`f0` を根にしたときの最遠点が他方の端 `f1`。`f0` と `f1` を根にした `cost_depth` を `cost_depth0`、`cost_depth1` として渡す。

元のソースからの変更:
- 2 本の `cost_depth` と出力 `h` を引数にする。元は `Tree` のメンバーの `cost_depth_[f0]`、`cost_depth_[f1]` を使い、`diameter()` と `build_depth` を内部で呼ぶ。
- `std::max(a, b)` を比較と分岐で書く（`a < b` なら `b`、そうでなければ `a`。同じ値）。
- `h` は呼び出し側が用意した長さ `n` 以上の vector で、先頭 `n` 個を書く（元は新しい vector を返す）。
- 元の関数全体としての検証（直径の両端を求め、距離の最大性を示すこと）は未完了。`Tree::diameter`、`Tree::height` は `docs/experiments_status.md` の違反一覧に残している。

前提: `0 <= n < 2^31 - 1`、`cost_depth0`、`cost_depth1`、`h` がどれも `n` 個以上の要素を持つ。

結果（`Proofs/TreeHeightCall.lean`、一般の入力について証明）: 終了後 `h[i] == max(cost_depth0[i], cost_depth1[i])`（`i < n`）、`n` 以降の要素と `h` の長さは変わらない。

時間と領域: モデル上の仕事量は呼び出し側の引数評価を除いて `120 * n + 200` 以下、書き込みは `n` 回以下、追加領域は局所変数だけ。

証明は `Proofs/TreeHeightExec.lean`（`pexecM` による 1 反復 `b_body` とループ全体 `body_exec`、途中状態 `hfill`）、`Proofs/TreeHeightPrepare.lean`/`Proofs/TreeHeightCall.lean`（呼び出し）。

定理に含めていないこと: 2 本の `cost_depth` が直径の両端を根にしたものであることと、そのとき `h[i]` が本当に最遠頂点までの距離であること。C++ のテストは `tests/tree_height.cpp`（ランダムな配列で先頭 `n` 個が最大値になり、残りが変わらないことを確認する）。

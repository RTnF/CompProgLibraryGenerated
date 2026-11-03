# tree_arcs

`cp::tree_arcs_from_list(from, to, af, at, m)` は、辺リストで与えられた木の辺（両方向）を弧のリストに並べる。`experiments/library/cpp/tree/tree.hpp` のコンストラクタ `Tree(int root, vector<int> &from, vector<int> &to)` と `Tree(int root, vector<int> &from, vector<int> &to, vector<Cost> &cost)` の、隣接リストを作る部分のうち、弧の端点を書き直した。

`i = 0, ..., m - 1`（`m = n - 1` 本の辺）について、弧 `from[i] -> to[i]` を位置 `2 * i` に、弧 `to[i] -> from[i]` を位置 `2 * i + 1` に、`(af, at)` へ書く。これは元が `adj[from[i]]` と `adj[to[i]]` に追加する順序と同じである。

元のソースからの変更:
- 隣接リストの代わりに 2 本の弧リスト（`af`、`at`）に書く。CSR 配列にするには `cp::csr_build(af, at, ...)` に渡す（計数ソートは安定なので、各頂点の弧の並びは元の隣接リストと同じになる。C++ のテストで確認している）。
- 元の範囲の `assert`（`0 <= from[i] < n` など）は前提条件とする。
- 弧の費用（辺の費用を 2 つの弧に写す。費用なしのコンストラクタでは 1）は `docs/tree_arc_costs.md` の `cp::tree_arc_costs` が担当する。根の指定と `build_depth` は `tree_root` に対応する。

前提: `0 <= m < 2^29`、`from.size() >= m`、`to.size() >= m`、`af.size() >= 2 * m`、`at.size() >= 2 * m`、`from`・`to` の要素が `int` の範囲にある。

結果（`Proofs/TreeArcsCall.lean`、一般の入力について証明）: 終了後 `af[2*i] == from[i]`、`at[2*i] == to[i]`、`af[2*i+1] == to[i]`、`at[2*i+1] == from[i]`（`i < m`）、`2 * m` 以降の要素は変わらない（`AFt`、`ATt`）。

時間と領域: モデル上の仕事量は呼び出し側の引数評価を除いて `320 * m + 200` 以下、書き込みは `4 * m` 回以下、追加領域は局所変数だけ。

証明は `Proofs/TreeArcsExec.lean`（添字式 `2 * i`、`2 * i + 1` の評価、途中状態 `AFt`/`ATt`、1 反復 `b_body`、全体 `body_exec`。2 要素の書き込みの補題 `pair_pad` は `Proofs/TreeEdgesExec.lean`）、`Proofs/TreeArcsPrepare.lean`/`Proofs/TreeArcsCall.lean`（呼び出し）。C++ のテストは `tests/tree_arcs.cpp`（`csr_build` との合成で、元の構築と同じ隣接順序になることを確認する）。

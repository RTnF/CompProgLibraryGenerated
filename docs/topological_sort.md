# topological_sort

`cp::topological_sort(head, target, indeg, order, n)` は、有向グラフのトポロジカルソート（カーンの方法）である。`experiments/library/cpp/graph/topological_sort.hpp` の `ListGraph::topological_sort` から、検証できる形に書き直した。

グラフは CSR 形式の配列で渡す: 頂点 `v` から出る辺の行き先は `target[head[v] .. head[v + 1])`。結果は呼び出し側の `order` に書き、並べた頂点の個数 `k` を返す。

元のソースからの変更:
- 隣接リスト（`vector<vector<E>>`）の代わりに CSR 配列を使う。検証器が扱えるのは平らな vector だけである。
- 元のスタックの代わりにキュー（`order` 自身）を使う。元は閉路があると空の vector を返すが、ここでは `k < n` で表す。
- 入次数の配列 `indeg` は呼び出し側が 0 で埋めて渡す（作業領域。関数が上書きする）。辞書順最小版（`topological_sort_minimum`、`priority_queue`）は含めない。

前提: `head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size()`、すべての `target[p]` が `[0, n)`、`indeg.size() == order.size() == n`、`indeg` の全要素が 0、`n < 2^31 - 2`、`target.size() < 2^31 - 1`。

結果（`Proofs/TopoSortCall.lean`、一般の入力について証明）: 返り値 `k` と `order` の先頭 `k` 個 `Q` について
- `Q` の要素は互いに異なり、すべて `[0, n)` で、`k ≤ n`。
- `Q[j]` の入ってくる辺の始点 `u`（`Q[j]` が `u` の行き先に含まれる）は、必ず `Q` の `j` 番目より前にある。
- `Q` に含まれない頂点 `w` には、`Q` に含まれない始点 `u` からの辺 `u → w` がある（したがって `k < n` ならグラフに閉路がある）。`k = n` なら `order` は全頂点の置換で、すべての辺は前から後ろへ向かう。
`order` の `k` 番目以降は元の値のまま、`indeg` は元の入次数から処理した辺の本数を引いた値になる。

時間と領域: 辺の数 `m` について、モデル上の仕事量は呼び出し側の引数評価を除いて高々 `420 * m * n + 840 * n + 120 * m + 400` に収まる（外側の `qh` のループが `n` 回、内側が処理した頂点の出辺の本数。実際の反復は `O(n + m)` 回だが、証明は「各反復の上限 × 反復回数」の粗い評価）。追加領域は局所変数だけ。

証明は `Proofs/TopoSortMath.lean`（アルゴリズムのリスト版 `kahnL` と不変条件 `Inv`: `indeg[w]` は「まだ処理していない頂点から `w` へ入る辺の本数」、`w` がキューにある ⇔ `indeg[w] = 0`、キューにある頂点の入ってくる辺の始点は先にある）、`Proofs/TopoSortExec.lean`（`pexecM` による各ループの実行）、`Proofs/TopoSortPrepare.lean`/`Proofs/TopoSortCall.lean`（呼び出し）。

定理に含めていないこと: 辞書順最小版、返り値が `n` であることと閉路が無いことの同値の Lean での定理（上の 3 点から従うが、証明はしていない。C++ のテストで確認している）、`indeg` が 0 でない入力（未定義の挙動ではなく単に結果が変わる）。C++ のテストは `tests/topological_sort.cpp`（頂点数 0〜8 のランダムな DAG と一般のグラフを、到達可能性の閉包による閉路判定と照合し、3 つの性質を直接確認する）。

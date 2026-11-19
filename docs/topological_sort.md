# topological_sort

`cp::topological_sort(head, target, indeg, order, n)` は、有向グラフのトポロジカルソート（カーンの方法）である。`experiments/library/cpp/graph/topological_sort.hpp` の `ListGraph::topological_sort` から、検証できる形に書き直した。

グラフは CSR 形式の配列で渡す: 頂点 `v` から出る辺の行き先は `target[head[v] .. head[v + 1])`。結果は呼び出し側の `order` に書き、並べた頂点の個数 `k` を返す。

元のソースからの変更:
- 隣接リスト（`vector<vector<E>>`）の代わりに CSR 配列を使う。検証器が扱えるのは平らな vector だけである。
- 元のスタックの代わりにキュー（`order` 自身）を使う。元は閉路があると空の vector を返すが、ここでは `k < n` で表す。
- 入次数の配列 `indeg` は呼び出し側が 0 で埋めて渡す（作業領域。関数が上書きする）。辞書順最小版（`topological_sort_minimum`、`priority_queue`）は含めない。

前提: `head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size()`、すべての `target[p]` が `[0, n)`、`indeg.size() == order.size() == n`、`indeg` の全要素が 0、`n < 2^31 - 2`、`target.size() < 2^31 - 1`。

結果（`Proofs/Cpp/TopologicalSort.lean` の `topological_sort_correct`、一般の入力について証明）: 返り値 `k` と `order` の先頭 `k` 個 `Q` について
- `Q` の要素は互いに異なり、すべて `[0, n)` で、`k ≤ n`。
- `Q[j]` の入ってくる辺の始点 `u`（`Q[j]` が `u` の行き先に含まれる）は、必ず `Q` の `j` 番目より前にある。
- `Q` に含まれない頂点 `w` には、`Q` に含まれない始点 `u` からの辺 `u → w` がある（したがって `k < n` ならグラフに閉路がある）。`k = n` なら `order` は全頂点の置換で、すべての辺は前から後ろへ向かう。
`order` の `k` 番目以降は元の値のまま、`indeg` は元の入次数から処理した辺の本数を引いた値になる。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/TopologicalSort.lean` を生成する。`Proofs/Cpp/TopologicalSort.lean` は、翻訳した 3 つのループの配列が純関数モデル（`Proofs/Math/TopoSortMath.lean` の `initSt`・`kahnL`・`decr`）の状態に常に一致することを示し（`Rel`。入次数の計数 `count_step`、入次数 0 の頂点の投入 `enq_step`、辺 1 本の処理 `decr_step`）、モデルの `kahn_final` から上の結果を導く。

- tick 数は `1 + m + n + n + W` で、`W`（取り出した頂点の出辺の数の和）は `m` 以下（`W_le`）。全体で `1 + 2n + 2m` 以下、`O(n + m)`。
- 定理に含めていないこと: 辞書順最小版、返り値が `n` であることと閉路が無いことの同値の Lean での定理（上の 3 点から従うが、証明はしていない。C++ のテストで確認している）、`indeg` が 0 でない入力（未定義の挙動ではなく単に結果が変わる）。

差分テスト（`tests/diff/topological_sort.py`、DAG と一般のグラフ）と C++ のテスト `tests/topological_sort.cpp`（頂点数 0〜8 のランダムな DAG と一般のグラフを、到達可能性の閉包による閉路判定と照合し、3 つの性質を直接確認する） で翻訳と実装を確かめる。

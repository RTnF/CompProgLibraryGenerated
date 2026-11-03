# bellman_ford

`cp::bellman_ford(from, to, cost, dist, parent, n, inf)` は、辺の緩和を `n - 1` 周繰り返したのち、負閉路から届く頂点に `-inf` の印を付ける単一始点最短経路（ベルマン–フォード法）である。`experiments/library/cpp/graph/bellman_ford.hpp` の `ListGraph::bellman_ford` から、検証できる形に書き直した。辺は平行な 3 本の配列（`from[e]` から `to[e]` へ、コスト `cost[e]`）で渡す。呼び出し側は `dist[始点] = 0`、それ以外を `inf`（まだ届いていない印）、`parent` の全要素を `-1` にしてから呼ぶ。

元のソースからの変更（検証できる形にするために書き換えた）:

- 隣接リストと `ListGraph` のクラスをやめ、辺の配列を引数にした。経路復元の親配列 `parent` を引数に持ち、緩和のたびに `parent[to[e]] = from[e]` を書く。元の後処理の周（負閉路の印付け）は、元が `dist` に印の値を足して桁あふれするので、印は `-inf`（どの有限の距離よりも小さい値）に置き換えた。印のついた頂点の `parent` は `-1` にする。元の `neg` 引数は廃止した。
- `&&` による短絡評価と、添字の中の vector の読み出し（`dist[to[e]]`）は検証器が扱えないので、`int u = from[e]; int v = to[e];` と入れ子の `if` に書き下した。ループの上限は `int` の局所変数（`m = from.size()`、`rounds = n - 1`）にした。

前提:
- `n ≥ 1`、`n < 2^31 - 1`、`dist.size() == n`、`from.size() == to.size() == cost.size() < 2^31 - 1`、すべての `from[e]`・`to[e]` が `[0, n)`。
- 桁あふれしないこと: `dist` の全要素が `[lo, inf]`、`|cost[e]| ≤ C`、`0 ≤ C ≤ 2^61`、`inf ≤ 2^62`、`lo - (n - 1) * m * C ≥ -2^62`（`m` は辺の数）。このとき途中のどの和も `long long` に収まる。

結果（`Proofs/BellmanFordCall.lean`、一般の入力について証明）: 前半の `n - 1` 周のあとの `dist` は、辺を添字の順に 1 周ずつ緩和する操作を `n - 1` 回行った結果 `roundsL`（`Proofs/BellmanFordExec.lean`）に、`parent` は同じ緩和のうち更新した辺の始点を書いた結果 `roundsPL`（`Proofs/BellmanFordPExec.lean`）に等しい。後半の `n` 周は `markRounds`（`Proofs/BellmanFordPExec.lean`）で、辺ごとに `dist[from] == -inf` か、`dist[from] + cost < dist[to]` のとき `dist[to] = -inf; parent[to] = -1` とする（`dist[from] == inf` の辺は何もしない）。出力は `markRounds` の結果に等しい。その上で、`Proofs/BellmanFordMath.lean`、`Proofs/BellmanFordBridge.lean`、`Proofs/BellmanFordParent.lean` により次を証明している。
- 健全性: 前半のあとの `dist[v] != inf` なら、最初に有限だった頂点 `w` から `v` へのウォーク（辺をたどる列）があり、`dist[v]` は `最初の dist[w]` にそのウォークのコストを足した値に等しい。
- 完全性: `inf` が、長さ `n - 1` 辺以下のすべてのウォークの「最初の `dist[w]` ＋コスト」より大きいとき、長さ `k ≤ n - 1` 辺の任意のウォーク `w → v` について（前半のあとの）`dist[v] ≤ 最初の dist[w] + コスト`。
- 親: 前半のあと、各頂点 `v` で `parent[v] = -1` か、`from[e] = parent[v]`、`to[e] = v` の辺 `e` があって `dist[parent[v]] < inf` かつ `dist[parent[v]] + cost[e] ≤ dist[v]`（`ParInvE`）。
- 印付け: 前半のあとの `dist` が安定（`dist[from] != inf` の辺すべてで `dist[to] ≤ dist[from] + cost`）なら、後半は何も変えず、出力は前半のあとの `dist` と `parent` に等しい。

時間と領域: 前半 `n - 1` 周、後半 `n` 周、内側 `m` 辺で、モデル上の仕事量は呼び出し側の引数評価を除いて高々 `(970 * m + 50) * (n - 1) + (970 * m + 50) * n + 300`、vector への書き込みは `2 * m * (n - 1) + 2 * m * n` 回以下。追加領域は局所変数 9 個。

定理に含めていないこと: 「負閉路から届く頂点は必ず `-inf` になる」ことと、負閉路が無いとき前半のあとの `dist` が安定になること（上の安定の仮定を、負閉路が無いことから導く部分）、`n = 0`、上の前提を破る入力（未定義動作）。前提の追加: `0 ≤ inf`、`-inf < lo - (n - 1) * m * C`（有限の距離が `-inf` と等しくならない）、`parent` の初期値がすべて `-1`。C++ のテストは `tests/bellman_ford.cpp`（フロイド–ワーシャルを基準に、始点から届いて負閉路からも届く頂点は `-inf`、それ以外は最短距離と親になることを、ランダムなグラフ（負の辺、負閉路を含む）で確認する）。


費用の型 `Cost` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化はヘッダー末尾の明示的な具体化 `bellman_ford<long long>`。
